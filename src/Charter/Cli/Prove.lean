import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Prove.LeanGen

/-!
# Charter.Cli.Prove — `charter prove <file.eflint>`

Writes the project of `Charter.Prove.LeanGen` under `.charter/prove/<program>/`, runs
the checker on it under a memory cap and a time cap, and reports one line per theorem
(*decided* or FAILED) through the diagnostic channel; the author sees theorem labels and
verdicts, never the engine (Law 11), unless `--show-checker` is given.

Phase 2 (plan §6): a maintainer tool run from the Charter repository with its own
toolchain; the managed toolchain fetched by digest (D9) is Phase 4. Every run is
capped (`--memory MB`, default 6144; `--time S`, default 300), after the 128 GB
incident of 2026-10-24 (AGENTS.md, "Kernel experiments run capped"). Law 10: a theorem
counts as decided only if the checker reports that it depends on no axioms.
-/

namespace Charter.Cli

open Lean (Json)

structure ProveOpts where
  json        : Bool := false
  eflint      : Bool := false
  showChecker : Bool := false
  /-- Write the project and stop; the checker is then run by hand (`tools/kernel-probe`). -/
  emitOnly    : Bool := false
  dir         : Option String := none
  memory      : Nat := 6144
  time        : Nat := 300
  /-- Phrases per checkpoint module (013.4); each module is one checker process. -/
  chunk       : Nat := 5
  files       : List String := []

def parseProveArgs : List String → ProveOpts → Except String ProveOpts
  | [], o => .ok { o with files := o.files.reverse }
  | "--out" :: "json" :: rest, o => parseProveArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseProveArgs rest o
  | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
  | ["--out"], _ => .error "--out needs json or text"
  | "--eflint" :: rest, o => parseProveArgs rest { o with eflint := true }
  | "--show-checker" :: rest, o => parseProveArgs rest { o with showChecker := true }
  | "--emit-only" :: rest, o => parseProveArgs rest { o with emitOnly := true }
  | "--dir" :: d :: rest, o => parseProveArgs rest { o with dir := some d }
  | ["--dir"], _ => .error "--dir needs a directory"
  | "--memory" :: n :: rest, o => match n.toNat? with
    | some k => if k > 16384 then .error "--memory above 16384 MB is refused" else parseProveArgs rest { o with memory := k }
    | none => .error s!"--memory needs megabytes, not {n}"
  | ["--memory"], _ => .error "--memory needs megabytes"
  | "--time" :: n :: rest, o => match n.toNat? with
    | some k => parseProveArgs rest { o with time := k }
    | none => .error s!"--time needs seconds, not {n}"
  | ["--time"], _ => .error "--time needs seconds"
  | "--chunk" :: n :: rest, o => match n.toNat? with
    | some k => if k == 0 then .error "--chunk needs a positive number of phrases" else parseProveArgs rest { o with chunk := k }
    | none => .error s!"--chunk needs a number of phrases, not {n}"
  | ["--chunk"], _ => .error "--chunk needs a number of phrases"
  | a :: rest, o => parseProveArgs rest { o with files := a :: o.files }

/-- The repository root: the nearest ancestor of the working directory holding the
build manifest of the Charter package. -/
partial def findRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  let manifest := dir / "lakefile.toml"
  if ← manifest.pathExists then
    let txt ← IO.FS.readFile manifest
    if (txt.splitOn "name = \"charter\"").length > 1 then return some dir
  match dir.parent with
  | some p => if p == dir then return none else findRoot p
  | none => return none

/-- One environment variable as `lake env` sets it, so the checker can be run directly
(its own process, which the watchdog below can measure) with the repository's toolchain. -/
def lakeEnvVar (root : System.FilePath) (name : String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", name], cwd := some root }
  if out.exitCode != 0 then return none
  let v := out.stdout.trimRight
  return if v.isEmpty then none else some v

/-- The resident size of a process in MB, from `ps`; 0 when it cannot be read. -/
def residentMB (pid : UInt32) : IO Nat := do
  let out ← IO.Process.output { cmd := "ps", args := #["-o", "rss=", "-p", toString pid] }
  return (out.stdout.trim.toNat?.getD 0) / 1024

/-- What the checker said: exit status, its combined output, and the peak resident size
seen; `none` on the time cap or the memory cap (the process was killed). Two memory caps:
the checker's own accounting (`--memory`) and a resident-size watchdog polled every quarter
second, since an allocator may hold memory the checker's counter does not see. -/
def runChecker (root dir file : System.FilePath) (olean : Option System.FilePath) (memory time : Nat) : IO (Option (UInt32 × String) × Nat × String) := do
  let some path ← lakeEnvVar root "PATH" | return (none, 0, "the checker's toolchain could not be found")
  let leanPath := dir.toString ++ ":" ++ (← lakeEnvVar root "LEAN_PATH").getD ""
  let memFlag : String := "--memory=" ++ toString memory
  let args : Array String := #[memFlag, file.toString] ++ (olean.map (fun o => #["-o", o.toString])).getD #[]
  let env : Array (String × Option String) := #[("PATH", some path), ("LEAN_PATH", some leanPath)]
  let spawnArgs : IO.Process.SpawnArgs :=
    { cmd := "lean", args := args, cwd := some root, stdout := .piped, stderr := .piped, env := env }
  let child ← IO.Process.spawn spawnArgs
  let outT ← IO.asTask child.stdout.readToEnd
  let errT ← IO.asTask child.stderr.readToEnd
  let pid := child.pid
  let mut status : Option UInt32 := none
  let mut peak := 0
  let mut killedBy := ""
  for _ in [0 : time * 4] do
    match ← child.tryWait with
    | some st => status := some st; break
    | none =>
      let rss ← residentMB pid
      if rss > peak then peak := rss
      if rss > memory then
        killedBy := s!"the memory cap ({rss} MB resident, cap {memory} MB)"
        break
      IO.sleep 250
  match status with
  | none =>
    child.kill
    let _ ← child.wait
    return (none, peak, if killedBy.isEmpty then s!"the time cap ({time} s)" else killedBy)
  | some st =>
    let out ← IO.ofExcept outT.get
    let err ← IO.ofExcept errT.get
    return (some (st, out ++ err), peak, "")

/-- The module and line an error line of the checker's output names, if it is one. -/
def errorLine (l : String) : Option Prove.Loc :=
  match l.splitOn ":" with
  | file :: line :: _ :: kind :: _ =>
    if kind.trim == "error" then
      match line.toNat?, (System.FilePath.mk file).fileStem with
      | some n, some m => some (m, n)
      | _, _ => none
    else none
  | _ => none

/-- The theorem whose `#print axioms` line this is, if it reports a dependence. -/
def axiomUser (l : String) : Option String :=
  if (l.splitOn "depends on axioms").length > 1 then
    match (l.splitOn "'") with
    | _ :: name :: _ => some name
    | _ => none
  else none

/-- The theorem a line of the generated file belongs to: the last one (or checkpoint
block) starting at or before it. -/
def owner (proj : Prove.Project) (loc : Prove.Loc) : Option String :=
  let starts := (proj.decided.1, proj.decided.2) :: proj.steps.map (fun (s, l) => (s.name, l))
    ++ proj.obligations.map (fun (o, l) => (o.name, l))
  (starts.filter fun (_, (m, l)) => m == loc.1 && l ≤ loc.2).foldl (fun acc (n, (_, l)) => match acc with
    | some (_, l') => if l ≥ l' then some (n, l) else acc
    | none => some (n, l)) none |>.map (·.1)

def claimJson (o : Prove.Obligation) (file : String) (result : Bool) (note : String) : Json :=
  Json.mkObj ([("kind", Json.str "claim"), ("tag", Json.str "decided"), ("about", Json.str o.about), ("claim", Json.str o.text),
    ("result", Json.bool result), ("file", Json.str file), ("line", Json.num o.line), ("theorem", Json.str o.name)]
    ++ (if note.isEmpty then [] else [("note", Json.str note)]))

/-- Prove one program: returns `(decided, failed)`. -/
def proveFile (o : ProveOpts) (root : System.FilePath) (path : String) : IO (Nat × Nat) := do
  let (items, loadDiags) ← loadProgram path o.eflint
  let mut errors := 0
  for d in loadDiags do
    if o.json then IO.println (diagJson d).compress else IO.eprintln d.render
    if d.isError then errors := errors + 1
  if errors > 0 then
    IO.eprintln s!"{path}: prove: the program does not load; nothing to decide"
    return (0, 1)
  let stem := (System.FilePath.mk path).fileStem.getD "program"
  let dir := match o.dir with
    | some d => System.FilePath.mk d
    | none => root / ".charter" / "prove" / stem
  IO.FS.createDirAll dir
  let proj := Prove.generate path stem (items.map (·.item)) o.chunk
  for (m, src) in proj.files do
    IO.FS.writeFile (dir / (m ++ ".lean")) src
  if proj.obligations.isEmpty then
    IO.println s!"{path}: prove: the program makes no claim and declares no invariant; nothing to decide"
    return (0, 0)
  if o.emitOnly then
    IO.println s!"{path}: prove: project written ({proj.files.length} module(s), {proj.steps.length} checkpoint(s), {proj.obligations.length} theorem(s) about claims); not run (--emit-only)"
    return (0, 0)
  -- one checker process per module, in order (each imports the one before); the time cap
  -- is the whole run's, the memory cap each process's
  let mut result : Option (UInt32 × String) := some (0, "")
  let mut peak := 0
  let mut stopped := ""
  let mut left := o.time
  let n := proj.files.length
  for ((m, _), i) in proj.files.zipIdx do
    let file := dir / (m ++ ".lean")
    let olean := if i + 1 < n then some (dir / (m ++ ".olean")) else none
    let t0 ← IO.monoMsNow
    let (r, pk, st) ← runChecker root dir file olean o.memory left
    let spent := ((← IO.monoMsNow) - t0) / 1000
    left := if spent + 1 < left then left - spent else 1
    if pk > peak then peak := pk
    match r, result with
    | none, _ => result := none; stopped := st; break
    | some (code, out), some (code0, out0) =>
      result := some (if code != 0 then code else code0, out0 ++ out)
      if code != 0 then break -- a failing module's import would fail every later one
    | _, _ => pure ()
  let mut decided := 0
  let mut failed := 0
  let report (ob : Prove.Obligation) (ok : Bool) (note : String) : IO Unit := do
    let label := if ob.about == "invariant" then s!"invariant {ob.text}" else s!"{path}:{ob.line}  {ob.text}"
    if o.json then IO.println (claimJson ob path ok note).compress
    else IO.println s!"{if ok then "decided" else "FAILED "}  {label}{if note.isEmpty then "" else s!"  ({note})"}"
  match result with
  | none =>
    for (ob, _) in proj.obligations do
      report ob false s!"not decided: stopped by {stopped}"
      failed := failed + 1
  | some (st, out) =>
    if o.showChecker then IO.println out
    let lines := out.splitOn "\n"
    let errLines := lines.filterMap errorLine
    let failing := (errLines.filterMap (owner proj)).eraseDups
    let axiomatic := (lines.filterMap axiomUser).eraseDups
    -- a checkpoint the kernel disagrees with names its phrase (Law 9); the chain, and with it
    -- every claim, then fails
    let failedSteps := proj.steps.filter fun (s, _) => failing.contains s.name
    let disagreement := match failedSteps with
      | [] => ""
      | (s, _) :: _ => match s.about with
        | "phrase" => s!"the kernel's run of the phrase at line {s.line} disagrees with the evaluator's (Law 9); nothing is decided"
        | "scenario" => s!"the kernel's check of the scenario at line {s.line} disagrees with the evaluator's (Law 9); nothing is decided"
        | _ => "the kernel's check of the program's end state disagrees with the evaluator's (Law 9); nothing is decided"
    let decidedFailed := !disagreement.isEmpty || failing.contains proj.decided.1 || axiomatic.contains proj.decided.1
    let unattributed := st != 0 && errLines.isEmpty
    for (ob, _) in proj.obligations do
      let note :=
        if !disagreement.isEmpty then disagreement
        else if decidedFailed then "the chain of checkpoints did not close; --show-checker prints the checker's output"
        else if unattributed then
          if (out.splitOn "memory").length > 1 then s!"not decided within {o.memory} MB"
          else "the checker could not run; --show-checker prints its output"
        else if failing.contains ob.name then
          if ob.expected then "" else "the evaluator reported this claim false and the kernel agrees"
        else if axiomatic.contains ob.name then "depends on axioms (Law 10)"
        else ""
      let ok := !decidedFailed && !unattributed && !failing.contains ob.name && !axiomatic.contains ob.name
      report ob ok note
      if ok then decided := decided + 1 else failed := failed + 1
  if o.showChecker then IO.println s!"checker peak resident size: {peak} MB"
  return (decided, failed)

/-- `charter prove <file.eflint> … [--dir DIR] [--memory MB] [--time S] [--chunk N] [--show-checker] [--out json] [--eflint]` -/
def proveCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter prove <file.eflint> ... [--dir <directory>] [--memory <MB>] [--time <seconds>] [--chunk <phrases>] [--show-checker] [--emit-only] [--out json] [--eflint]"
  match parseProveArgs args {} with
  | .error e => IO.eprintln s!"charter prove: {e}"; IO.eprintln usage; return 2
  | .ok o =>
    if o.files.isEmpty then IO.eprintln usage; return 2
    let cwd ← IO.currentDir
    let some root ← findRoot cwd
      | IO.eprintln "charter prove: run it from inside the Charter repository (a maintainer tool until the managed toolchain lands, plan Phase 4)"
        return 2
    let mut decided := 0
    let mut failed := 0
    for f in o.files do
      let (d, fl) ← proveFile o root f
      decided := decided + d
      failed := failed + fl
    if o.json then
      IO.println (Json.mkObj [("kind", "summary"), ("decided", Json.num decided), ("failed", Json.num failed), ("ok", Json.bool (failed == 0))]).compress
    else IO.println s!"prove: {decided} decided, {failed} failed"
    return (if failed == 0 then 0 else 1)

end Charter.Cli
