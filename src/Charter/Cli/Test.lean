import Charter.Cli.Run

/-!
# Charter.Cli.Test — `charter test <files or directories>`

Runs every `.eflint` file under the given paths in test mode: a file passes when
it produces no error diagnostic and every query holds (`test/eflint-corpus/README.md`).
Prints one line per file and a summary; exit status is non-zero when any file
fails.

**Fixture directives** (plan §5.4, With's style) are comment lines `//! …`
anywhere in the file:

- `//! expect-error: CHR020` — the file passes only if that error is reported
  (several directives, several codes; other outcomes are not checked);
- `//! expect-warning: CHR019` — likewise for a warning;
- `//! known-issue: <why>` — the file is expected to fail; it fails the run if it
  unexpectedly passes (so a fixed issue is noticed and the directive deleted).

With `--expect <file>`, each file's outcome is compared with the outcome recorded
there (lines `ok   <path>` / `FAIL <path>`, the format this command prints, which
`tools/corpus-baseline` produces by running eFLINT itself). With
`--tolerate <file>`, the paths quoted in backticks in that file (the
`tolerances.md` of the corpus) are expected to *differ* from the recorded
outcome, under a ruled decision; a tolerated file that agrees with eFLINT fails
the run, because its tolerance is no longer needed and must be deleted (D2).
`--out json` prints one object per file and a summary object.
-/

namespace Charter.Cli

open Lean (Json)

def walkEflint (p : System.FilePath) : Nat → IO (List System.FilePath)
  | 0 => return []
  | depth + 1 => do
    if ← p.isDir then
      let entries ← p.readDir
      let sorted := entries.qsort (fun a b => a.path.toString < b.path.toString)
      let mut acc := []
      for e in sorted do acc := acc ++ (← walkEflint e.path depth)
      return acc
    else if p.extension == some "eflint" then return [p]
    else return []

structure TestOpts where
  paths    : List String := []
  expect   : Option String := none
  tolerate : Option String := none

def parseTestArgs : List String → TestOpts → Except String TestOpts
  | [], o => .ok { o with paths := o.paths.reverse }
  | "--expect" :: f :: rest, o => parseTestArgs rest { o with expect := some f }
  | ["--expect"], _ => .error "--expect needs a file"
  | "--tolerate" :: f :: rest, o => parseTestArgs rest { o with tolerate := some f }
  | ["--tolerate"], _ => .error "--tolerate needs a file"
  | p :: rest, o => parseTestArgs rest { o with paths := p :: o.paths }

/-- `ok   path` / `FAIL path` lines → (path, passed). Anything after the path is ignored. -/
def readExpected (file : System.FilePath) : IO (List (String × Bool)) := do
  let txt ← IO.FS.readFile file
  return txt.splitOn "\n" |>.filterMap fun line =>
    let ws := line.trim.splitOn " " |>.filter (· != "")
    match ws with
    | "ok" :: p :: _ => some (p, true)
    | "FAIL" :: p :: _ => some (p.takeWhile (· != ':'), false)
    | _ => none

/-- Every backticked token ending in `.eflint`. -/
def readTolerated (file : System.FilePath) : IO (List String) := do
  let txt ← IO.FS.readFile file
  let parts := txt.splitOn "`"
  let rec pick : List String → Bool → List String
    | [], _ => []
    | s :: rest, inside => (if inside && s.endsWith ".eflint" then [s] else []) ++ pick rest (!inside)
  return pick parts false

def endsWithPath (full : String) (suffix : String) : Bool :=
  full == suffix || full.endsWith ("/" ++ suffix) || suffix.endsWith ("/" ++ full)

/-- The `//!` directives of a source text. -/
structure Directives where
  expectErrors   : List String := []
  expectWarnings : List String := []
  knownIssue     : Option String := none

def readDirectives (src : String) : Directives :=
  src.splitOn "\n" |>.foldl (fun d line =>
    let l := line.trim
    if l.startsWith "//!" then
      let body := (l.drop 3).trim
      if body.startsWith "expect-error:" then { d with expectErrors := d.expectErrors ++ [(body.drop 13).trim] }
      else if body.startsWith "expect-warning:" then { d with expectWarnings := d.expectWarnings ++ [(body.drop 15).trim] }
      else if body.startsWith "known-issue:" then { d with knownIssue := some (body.drop 12).trim }
      else d
    else d) {}

/-- The verdict on a file: passed, and why in one phrase. -/
def verdict (d : Directives) (stats : RunStats) : Bool × String :=
  if !d.expectErrors.isEmpty || !d.expectWarnings.isEmpty then
    let missing := (d.expectErrors ++ d.expectWarnings).filter (fun c => !stats.codes.contains c)
    if missing.isEmpty then (true, s!"expected diagnostics reported: {", ".intercalate (d.expectErrors ++ d.expectWarnings)}")
    else (false, s!"expected diagnostics missing: {", ".intercalate missing}; reported: {", ".intercalate stats.codes}")
  else match d.knownIssue with
    | some why => if stats.ok then (false, s!"known issue unexpectedly passes ({why}); delete the directive") else (true, s!"known issue, still failing ({why})")
    | none => (stats.ok, s!"{stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"}")

/-- `charter test <paths…> [--expect file] [--tolerate file] [--out json]` -/
def testCommand (args : List String) : IO UInt32 := do
  let (json, args) ← match takeOutFlag args with
    | .error e => IO.eprintln s!"charter test: {e}"; return 2
    | .ok r => pure r
  let opts ← match parseTestArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter test: {e}"; return 2
  if opts.paths.isEmpty then
    IO.eprintln "usage: charter test <file.eflint | directory> ... [--expect <outcomes>] [--tolerate <tolerances.md>] [--out json]"
    return 2
  let expected ← match opts.expect with
    | some f => readExpected f
    | none => pure []
  let tolerated ← match opts.tolerate with
    | some f => readTolerated f
    | none => pure []
  let mut files : List System.FilePath := []
  for a in opts.paths do files := files ++ (← walkEflint a 32)
  let mut passed := 0
  let mut agreed := 0
  let mut toleratedCount := 0
  let mut failed : List String := []
  let report (f : System.FilePath) (ok : Bool) (why : String) (extra : List (String × Json)) : IO Unit :=
    if json then IO.println (Json.mkObj (([("kind", Json.str "file"), ("file", Json.str f.toString), ("ok", Json.bool ok), ("why", Json.str why)] : List (String × Json)) ++ extra)).compress
    else IO.println s!"{if ok then "ok  " else "FAIL"} {f}{if ok then " (" ++ why ++ ")" else ": " ++ why}"
  for f in files do
    let src ← IO.FS.readFile f
    let d := readDirectives src
    let stats ← runProgram { testMode := true, json } f
    let (outcome, why) := verdict d stats
    let fS := f.toString
    let isTolerated := tolerated.any (endsWithPath fS)
    match expected.find? (fun (p, _) => endsWithPath fS p) with
    | some (_, eflintOk) =>
      let agrees := outcome == eflintOk
      let ok := if isTolerated then !agrees else agrees
      let eflintS := if eflintOk then "passes" else "fails"
      let charterS := if outcome then "passes" else "fails"
      let extra := [("eflint", Json.str eflintS), ("charter", Json.str charterS), ("tolerated", Json.bool isTolerated)]
      if ok then
        passed := passed + 1
        if isTolerated then
          toleratedCount := toleratedCount + 1
          report f true s!"tolerated: eFLINT {eflintS}, Charter {charterS}" extra
        else
          agreed := agreed + 1
          report f true s!"{charterS} as in eFLINT; {stats.phrases} phrases" extra
      else
        failed := failed ++ [fS]
        if isTolerated then report f false s!"listed as tolerated but agrees with eFLINT ({charterS}); delete the tolerance" extra
        else report f false s!"eFLINT {eflintS}, Charter {charterS} ({why})" extra
    | none =>
      if opts.expect.isSome && !json then
        IO.println s!"WARN {f}: no eFLINT outcome recorded; judged on its own"
      if outcome then passed := passed + 1 else failed := failed ++ [fS]
      report f outcome why []
  let detail := if opts.expect.isSome then s!" ({agreed} agree with eFLINT, {toleratedCount} tolerated differences)" else ""
  if json then
    IO.println (Json.mkObj [("kind", "summary"), ("passed", Json.num passed), ("failed", Json.num failed.length),
      ("total", Json.num files.length), ("agree", Json.num agreed), ("tolerated", Json.num toleratedCount)]).compress
  else
    IO.println s!"{passed} passed, {failed.length} failed, {files.length} total{detail}"
  return (if failed.isEmpty then 0 else 1)

end Charter.Cli
