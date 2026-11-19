import Charter.Verify.TVIR
import Charter.Verify.Explorer

/-!
# Charter.Verify.Thresholds — Bounded search over threshold witnesses (`G2.4`, `T30`, `D47`)

`charter verify --backend thresholds` checks invariants of a program whose acts take
unbounded `Int`/`Duration`/`Time` arguments without asking the author for an
`explore-domain` menu:

1. It collects every integer constant in the `Spec` and the starting `State` and offers
   `c - 1, c, c + 1` around each as the candidate values of every integer-carried type
   (`TVIR.specThresholdWitnesses`). For guards that compare one variable with a constant
   these are one witness per interval the guards can tell apart.
2. It runs the ordinary bounded search (`Verify.search`) over that menu. Every step is a
   step of `Charter.Eval`, so a counterexample it reports is one the evaluator performs.
3. It says what it did not decide (`T30`): a depth below the required horizon, an exhausted
   state cap, an open `String` domain with no menu, or arithmetic that couples two variables
   (`x + y`, `x * y`, sums), for which threshold witnesses are not a complete set of cases.
   Each of these is `.inconclusive`, never a pass.

No solver is run and nothing is encoded for one. A solver-backed backend is its own work
(`D47`); until it exists `--backend smt` is refused by the CLI.
-/

namespace Charter.Verify.Thresholds

inductive Outcome
  | safeBounded (depth : Nat) (visited : Nat)
  | counterexample (cx : Counterexample)
  | inconclusive (reason : String)

/-- The menu of threshold witnesses for every `Int`-carried type, added to `baseMenu`. -/
def buildMenu (spec : Spec) (state : State) (baseMenu : Explore.Menu) : Explore.Menu :=
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

/-- Bounded search to `depth` over the threshold-witness menu (`G2.4`, `T30`). -/
def checkBounded (mode : ExploreMode) (depth : Nat) (minDepth : Option Nat) (stateCap : Nat)
    (baseMenu : Explore.Menu) (cfg₀ : Config) : Outcome :=
  let menu := buildMenu cfg₀.spec cfg₀.state baseMenu
  let stringGap := (modeCoverage mode cfg₀.spec menu).filter (·.source == .stateValues)
  let sOpts : SearchOpts := { mode, strategy := .bfs, depth, stateCap, minimize := true, menu }
  match Verify.search sOpts cfg₀ with
  | .error e => .inconclusive s!"runtime error during the search: {e.message}"
  | .counterexample cx => .counterexample cx
  | .safe visited _ cappedOut =>
    match minDepth with
    | some reqMin =>
      if depth < reqMin then
        .inconclusive s!"bound depth={depth} is smaller than required horizon {reqMin}; safety beyond step {depth} is unverified (T30)"
      else finish visited cappedOut stringGap
    | none => finish visited cappedOut stringGap
where
  finish (visited : Nat) (cappedOut : Bool) (stringGap : List Explore.Coverage) : Outcome :=
    if cappedOut then
      .inconclusive s!"state cap ({stateCap}) exhausted during the threshold search"
    else if !stringGap.isEmpty then
      .inconclusive s!"open String domain requires candidate menu for {", ".intercalate ((stringGap.map (·.comp)).eraseDups)}"
    else if !TVIR.isSingleThresholdFragment cfg₀.spec then
      .inconclusive "the program couples integer variables (`x + y`, `x * y`, or a sum); threshold witnesses do not cover every case, and no backend decides this fragment yet"
    else .safeBounded depth visited

end Charter.Verify.Thresholds
