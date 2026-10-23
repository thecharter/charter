import Charter.Cli.Run

/-!
# Charter.Cli.Test — `charter test <files or directories>`

Runs every `.eflint` file under the given paths in test mode: a file passes when
it produces no error diagnostic and every query holds (`test/eflint-corpus/README.md`).
Prints one line per file and a summary; exit status is non-zero when any file
fails.

With `--expect <file>`, each file's outcome is compared with the outcome recorded
there (lines `ok   <path>` / `FAIL <path>`, the format this command prints, which
`tools/corpus-baseline` produces by running eFLINT itself). With
`--tolerate <file>`, the paths quoted in backticks in that file (the
`tolerances.md` of the corpus) are expected to *differ* from the recorded
outcome, under a ruled decision; a tolerated file that agrees with eFLINT fails
the run, because its tolerance is no longer needed and must be deleted (D2).
-/

namespace Charter.Cli

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
  -- odd-indexed parts are inside backticks
  let rec pick : List String → Bool → List String
    | [], _ => []
    | s :: rest, inside => (if inside && s.endsWith ".eflint" then [s] else []) ++ pick rest (!inside)
  return pick parts false

def endsWithPath (full : String) (suffix : String) : Bool :=
  full == suffix || full.endsWith ("/" ++ suffix) || suffix.endsWith ("/" ++ full) || suffix == full

/-- `charter test <paths…> [--expect file] [--tolerate file]` -/
def testCommand (args : List String) : IO UInt32 := do
  let opts ← match parseTestArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter test: {e}"; return 2
  if opts.paths.isEmpty then
    IO.eprintln "usage: charter test <file.eflint | directory> ... [--expect <outcomes>] [--tolerate <tolerances.md>]"
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
  for f in files do
    let stats ← runProgram true f
    let fS := f.toString
    let outcome := stats.ok
    let isTolerated := tolerated.any (endsWithPath fS)
    match expected.find? (fun (p, _) => endsWithPath fS p) with
    | some (_, eflintOk) =>
      let agrees := outcome == eflintOk
      let verdict := if isTolerated then !agrees else agrees
      if verdict then
        passed := passed + 1
        if isTolerated then
          toleratedCount := toleratedCount + 1
          IO.println s!"ok   {f} (tolerated: eFLINT {if eflintOk then "passes" else "fails"}, Charter {if outcome then "passes" else "fails"})"
        else
          agreed := agreed + 1
          IO.println s!"ok   {f} ({if outcome then "passes" else "fails"} as in eFLINT; {stats.phrases} phrases)"
      else
        failed := failed ++ [fS]
        if isTolerated then
          IO.println s!"FAIL {f}: listed as tolerated but agrees with eFLINT ({if outcome then "passes" else "fails"}); delete the tolerance"
        else
          IO.println s!"FAIL {f}: eFLINT {if eflintOk then "passes" else "fails"}, Charter {if outcome then "passes" else "fails"} ({stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"})"
    | none =>
      if opts.expect.isSome then
        IO.println s!"WARN {f}: no eFLINT outcome recorded; judged on its own"
      if outcome then
        passed := passed + 1
        IO.println s!"ok   {f} ({stats.phrases} phrases)"
      else
        failed := failed ++ [fS]
        IO.println s!"FAIL {f}: {stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"}"
  let detail := if opts.expect.isSome then s!" ({agreed} agree with eFLINT, {toleratedCount} tolerated differences)" else ""
  IO.println s!"{passed} passed, {failed.length} failed, {files.length} total{detail}"
  return (if failed.isEmpty then 0 else 1)

end Charter.Cli
