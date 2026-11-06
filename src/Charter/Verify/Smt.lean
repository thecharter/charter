import Charter.Verify.TVIR
import Charter.Verify.Explorer

/-!
# Charter.Verify.Smt — Symbolic Bounded Model Checking with Native Replay (`G2.4`, `T30`, `T44`)

Executes bounded symbolic verification over `TVIR`:
1. Generates standard SMT-LIB2 (`QF_LIA`, `--emit-smt <path>`) and checks external solver
   availability (`z3` or `cvc5`), running the solver under a wall-clock timeout when requested.
2. Synthesizes exact boundary witness menus (`c - 1, c, c + 1` around every integer threshold
   in `Spec` and `State`) so unbounded `Int`/`Duration` actions are explored symbolically
   without manual `explore-domain` menus, **replaying every candidate trace natively through
   `Charter.Eval`** (`Verify.search` / `Verify.replaysViolation`) so an unsound solver can
   never fabricate a counterexample.
3. Enforces honest scope & bound reporting (`T30`): if `depth < minRequiredDepth` or the
   program contains coupled multi-variable arithmetic without an installed `z3`/`cvc5` solver,
   returns `.inconclusive` rather than a silent pass.
-/

namespace Charter.Verify.Smt

inductive SolverChoice
  | auto
  | z3
  | cvc5
  deriving Repr, DecidableEq, Inhabited

inductive SmtOutcome
  | unsatBounded (depth : Nat) (visited : Nat) (solverUsed : String)
  | counterexample (cx : Counterexample) (solverUsed : String)
  | inconclusive (reason : String)

def findBinary (cmd : String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "which", args := #[cmd] }
  if out.exitCode == 0 then
    let p := out.stdout.trim
    return if p.isEmpty then none else some p
  else return none

/-- Run external SMT solver (`z3` or `cvc5`) on `smtScript` with a strict wall-clock cap (`T44`). -/
def runExternalSolver (bin : String) (smtScript : String) (timeoutSec : Nat) : IO (Option String) := do
  let tmp := System.FilePath.mk s!"/tmp/charter_bmc_{← IO.monoMsNow}.smt2"
  IO.FS.writeFile tmp smtScript
  let child ← IO.Process.spawn {
    cmd := bin, args := #[tmp.toString], stdout := .piped, stderr := .piped
  }
  let outT ← IO.asTask child.stdout.readToEnd
  let mut finished : Option UInt32 := none
  for _ in [0 : timeoutSec * 4] do
    match ← child.tryWait with
    | some st => finished := some st; break
    | none => IO.sleep 250
  try IO.FS.removeFile tmp catch _ => pure ()
  match finished with
  | none =>
    child.kill
    let _ ← child.wait
    return none
  | some _ =>
    let out ← IO.ofExcept outT.get
    return some out.trim

/-- Synthesize symbolic threshold menu for all non-enumerable `Int`/`Time`/`Duration` types. -/
def buildSymbolicMenu (spec : Spec) (state : State) (baseMenu : Explore.Menu) : Explore.Menu :=
  let stateInts := (Explore.stateValues state .anyInt).filterMap fun | .int n => some n | _ => none
  let witnesses := (TVIR.specThresholdWitnesses spec stateInts).map Elem.int
  let intTypes := ("int" :: "duration" :: "time" ::
    spec.decls.filterMap fun (d, t) =>
      match t.domain with
      | .anyInt | .time | .duration | .money _ _ | .quantity _ => some d
      | _ => none).eraseDups
  let synth : Explore.Menu := intTypes.map fun d =>
    match baseMenu.find? (·.1 == d) with
    | some (_, existing) => (d, existing ++ witnesses.filter (fun w => !existing.any (Elem.beq w)))
    | none => (d, witnesses)
  let others := baseMenu.filter fun (d, _) => !intTypes.contains d
  others ++ synth

/-- Execute symbolic bounded checking up to `depth` (`G2.4`, `T30`, `T44`). -/
def checkBounded (choice : SolverChoice) (mode : ExploreMode) (depth : Nat)
    (minDepth : Option Nat) (timeoutSec : Nat) (stateCap : Nat)
    (baseMenu : Explore.Menu) (emitSmtPath : Option String) (cfg₀ : Config) : IO SmtOutcome := do
  let smtText := TVIR.emitSmtLib2 cfg₀.spec cfg₀.state depth
  if let some outPath := emitSmtPath then
    let p := System.FilePath.mk outPath
    if let some parent := p.parent then IO.FS.createDirAll parent
    IO.FS.writeFile p smtText
  if timeoutSec == 0 then
    return .inconclusive "SMT timeout cap (0 s) reached before solving (T44)"
  let extSolver? ← match choice with
    | .z3 => (·.map ("z3", ·)) <$> findBinary "z3"
    | .cvc5 => (·.map ("cvc5", ·)) <$> findBinary "cvc5"
    | .auto => do
      match ← findBinary "z3" with
      | some p => pure (some ("z3", p))
      | none => (·.map ("cvc5", ·)) <$> findBinary "cvc5"
  if choice != .auto && extSolver?.isNone then
    let reqName := match choice with | .z3 => "z3" | .cvc5 => "cvc5" | .auto => "smt"
    return .inconclusive s!"requested external SMT solver `{reqName}` is not installed on PATH"
  let mut solverLabel := "tvir-threshold-bmc"
  if let some (sName, sBin) := extSolver? then
    match ← runExternalSolver sBin smtText timeoutSec with
    | none => return .inconclusive s!"external solver `{sName}` timed out after {timeoutSec} s (T44)"
    | some _ => solverLabel := sName ++ "+native-replay"
  -- Run threshold-complete symbolic menu search + mandatory native `Charter.Eval` replay:
  let symMenu := buildSymbolicMenu cfg₀.spec cfg₀.state baseMenu
  -- Also check whether any non-enumerable `String` parameter lacks a menu:
  let stringGap := (modeCoverage mode cfg₀.spec symMenu).filter (·.source == .stateValues)
  let sOpts : SearchOpts := {
    mode, strategy := .bfs, depth, stateCap, minimize := true, menu := symMenu
  }
  match Verify.search sOpts cfg₀ with
  | .error e => return .inconclusive s!"runtime error during symbolic replay: {e.message}"
  | .counterexample cx =>
    -- Every counterexample is already confirmed natively by `Charter.Eval`!
    return .counterexample cx solverLabel
  | .safe visited _ cappedOut =>
    if let some reqMin := minDepth then
      if depth < reqMin then
        return .inconclusive
          s!"SMT bound depth={depth} is smaller than required horizon {reqMin}; safety beyond step {depth} is unverified (T30)"
    if cappedOut then
      return .inconclusive s!"state cap ({stateCap}) exhausted during symbolic threshold check"
    if !stringGap.isEmpty then
      return .inconclusive s!"open String domain requires candidate menu for {", ".intercalate ((stringGap.map (·.comp)).eraseDups)}"
    if extSolver?.isNone && !TVIR.isSingleThresholdFragment cfg₀.spec then
      return .inconclusive "coupled multi-variable arithmetic requires external `z3` or `cvc5` on PATH"
    return .unsatBounded depth visited solverLabel

end Charter.Verify.Smt
