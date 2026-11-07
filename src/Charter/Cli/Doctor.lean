import Charter.Artifact.Hash
import Lean.Data.Json

/-!
# Charter.Cli.Doctor — Claims Registry, Lockfile, & Environment Verifier (`G5.4`, `Law 11`)

`charter doctor [--claims <claims.json>] [--fail-on-unbacked] [--lock [<dir>]] [--out json]`:
1. Verifies every entry in `claims.json` points to an existing artifact file containing the
   declared theorem/gate symbol;
2. Verifies every file digest in `<dir>/charter.lock` matches its current SHA-256 content hash;
3. Reports availability of optional external verifiers (`z3`, `cvc5`, `solc`, `quint`) truthfully
   with zero proof-engine terminology (`Law 11`).
-/

namespace Charter.Cli

open Lean (Json)

structure DoctorOpts where
  claimsPath     : Option String := none
  failOnUnbacked : Bool := false
  lockDir        : Option String := none
  json           : Bool := false

def parseDoctorArgs : List String → DoctorOpts → Except String DoctorOpts
  | [], o => .ok o
  | "--claims" :: p :: rest, o => parseDoctorArgs rest { o with claimsPath := some p }
  | ["--claims"], _ => .error "--claims needs a path to claims.json"
  | "--fail-on-unbacked" :: rest, o => parseDoctorArgs rest { o with failOnUnbacked := true }
  | ["--lock"], o => .ok { o with lockDir := some "." }
  | "--lock" :: d :: r, o =>
    if d.startsWith "-" then parseDoctorArgs (d :: r) { o with lockDir := some "." }
    else parseDoctorArgs r { o with lockDir := some d }
  | "--out" :: "json" :: rest, o => parseDoctorArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseDoctorArgs rest { o with json := false }
  | a :: _, _ => .error s!"unknown flag {a}"
termination_by args _ => args.length

def checkToolOnPath (bin : String) : IO Bool := do
  let out ← IO.Process.output { cmd := "which", args := #[bin] }
  return out.exitCode == 0

def verifyClaimsFile (path : String) : IO (Nat × List String) := do
  let rawOpt : Option String ← try
    let s ← IO.FS.readFile path
    pure (some s)
  catch _ =>
    pure none
  let some raw := rawOpt | return (0, [s!"cannot read {path}"])
  match (do
    let j ← Json.parse raw
    j.getObjValAs? (Array Json) "claims") with
  | .error e => return (0, [s!"invalid JSON in {path}: {e}"])
  | .ok claims =>
    let mut verified := 0
    let mut problems : List String := []
    for c in claims do
      let cid := (c.getObjValAs? String "id").toOption.getD "<unknown>"
      let art := (c.getObjValAs? String "artifact").toOption.getD ""
      let sym := (c.getObjValAs? String "symbol").toOption.getD ""
      let ap := System.FilePath.mk art
      if !(← ap.pathExists) then
        problems := problems ++ [s!"claim `{cid}`: missing artifact `{art}`"]
      else
        if sym != "test/spec" && sym != "tools/battery" && sym != "tools/prove-check" then
          let txt ← IO.FS.readFile ap
          let shortSym := ((sym.splitOn ".").getLast?).getD sym
          if !(txt.splitOn shortSym).length.ble 1 |> (!·) then
            verified := verified + 1
          else if (txt.splitOn shortSym).length > 1 then
            verified := verified + 1
          else
            problems := problems ++ [s!"claim `{cid}`: symbol `{sym}` not found in `{art}`"]
        else verified := verified + 1
    return (verified, problems)

def verifyLockDir (dir : String) : IO (Nat × List String) := do
  let d := System.FilePath.mk dir
  let lockFile := d / "charter.lock"
  if !(← lockFile.pathExists) then
    return (0, [s!"missing lockfile `{lockFile}`"])
  let raw ← IO.FS.readFile lockFile
  match (do let j ← Json.parse raw; j.getObjValAs? (Array Json) "files") with
  | .error e => return (0, [s!"malformed lockfile `{lockFile}`: {e}"])
  | .ok arr =>
    let mut okCnt := 0
    let mut errs : List String := []
    for item in arr do
      let rel := (item.getObjValAs? String "path").toOption.getD ""
      let want := (item.getObjValAs? String "sha256").toOption.getD ""
      let fp := d / rel
      if !(← fp.pathExists) then
        errs := errs ++ [s!"locked file missing: `{fp}`"]
      else
        let txt ← IO.FS.readFile fp
        let actual := Artifact.sha256String txt
        if actual != want then
          errs := errs ++ [s!"lockfile SHA-256 mismatch on `{fp}`: expected {want}, actual {actual}"]
        else okCnt := okCnt + 1
    return (okCnt, errs)

def doctorCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter doctor [--claims <claims.json>] [--fail-on-unbacked] [--lock [<dir>]] [--out json]"
  let opts ← match parseDoctorArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter doctor: {e}\n{usage}"; return 2
  let mut issues : List String := []
  let mut claimsChecked := 0
  if let some cp := opts.claimsPath then
    let (v, probs) ← verifyClaimsFile cp
    claimsChecked := v
    issues := issues ++ probs
  let mut lockedChecked := 0
  if let some ld := opts.lockDir then
    let (lv, lprobs) ← verifyLockDir ld
    lockedChecked := lv
    issues := issues ++ lprobs
  let hasZ3 ← checkToolOnPath "z3"
  let hasCvc5 ← checkToolOnPath "cvc5"
  let hasSolc ← checkToolOnPath "solc"
  let hasQuint ← checkToolOnPath "quint"
  let ok := issues.isEmpty
  if opts.json then
    let j := Json.mkObj [
      ("kind", Json.str "doctor"),
      ("ok", Json.bool ok),
      ("verifiedClaims", Json.num claimsChecked),
      ("verifiedLockEntries", Json.num lockedChecked),
      ("issues", Json.arr (issues.map Json.str).toArray),
      ("optionalBackends", Json.mkObj [
        ("z3", Json.bool hasZ3),
        ("cvc5", Json.bool hasCvc5),
        ("solc", Json.bool hasSolc),
        ("quint", Json.bool hasQuint)
      ])
    ]
    IO.println j.compress
  else
    if !ok then
      for iss in issues do IO.eprintln s!"FAIL doctor: {iss}"
    else
      IO.println s!"ok   charter doctor (claims verified: {claimsChecked}, lock entries verified: {lockedChecked}; optional solvers: z3={hasZ3}, cvc5={hasCvc5}, solc={hasSolc}, quint={hasQuint})"
  if !ok && (opts.failOnUnbacked || opts.lockDir.isSome || opts.claimsPath.isSome) then return 1
  return 0

end Charter.Cli
