import Charter.Eval.Eval
import Charter.Core.Derivation
import Charter.Resolve.Static

/-!
# Charter.Eval.Interpreter — Phrases, saturation, and what a step reports

eFLINT's `Interpreter.hs` and `Saturation.hs`, per D2, with D6 and D12 applied:

- **Saturation is a stratified fixpoint** (D6, `Charter.Core.Derivation`). Each stratum is
  saturated to its least fixpoint with every lower stratum fixed, so the result never
  depends on the order of type names. Assignments beat derivations (`State.derive`), and
  derived facts are recomputed from scratch after every phrase (`State.rebase`).
- **A duty's violation is reported once** (D12), when it begins; whether it is
  violated now is always `isViolated`.

`runPhrase` is the step: resolve the phrase against the current spec, evaluate it
to a store of assignments, apply the store, saturate, and report. A phrase that
fails leaves the configuration unchanged (eFLINT `interpreter`).
-/

namespace Charter

/-! ## Saturation -/

namespace Saturate

open M

def checkFilter {α} (p : α → M Bool) (m : M α) : M α := do
  let a ← m
  if ← p a then pure a else empty

/-- Instances one derivation clause of `d` yields in the current state. -/
def deriveClause (d : DomId) (tspec : TypeSpec) (c : Derivation) : M (List Tagged) :=
  let dyn (xs : List Var) (t : Term) : M (List Tagged) :=
    foreach M.fuel xs (checkFilter (satConditions M.fuel) (whenTagged (eval M.fuel t) pure))
  let checkSat (m : M Tagged) : M Tagged :=
    if tspec.conditions.isEmpty && tspec.domainConstraint.isTrueLit then m
    else checkFilter (satConditions M.fuel) m
  match c with
  | .holdsWhen t =>
    match tspec.domain with
    | .products xs =>
      if tspec.domainConstraint.isTrueLit then
        foreach M.fuel xs do
          checkTrue (eval M.fuel t)
          checkSat (whenTagged (eval M.fuel (.app d (.named []))) pure)
      else dyn xs (.when (.app d (.named [])) t)
    | _ => dyn [⟨d, ""⟩] (.when (.ref ⟨d, ""⟩) t)
  | .dv xs t => dyn xs t

def runM {α} (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) (m : M α) : Except RuntimeError (List α) :=
  m.run (Ctx.ofIdx spec specIdx state) []

/-- One pass over the derivation clauses of one type; the state and whether it grew.
`prev` are the derived facts before rebasing, whose stamps re-derived facts keep (D7). -/
def passType (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    List Derivation → State → Except RuntimeError (State × Bool)
  | [], s => .ok (s, false)
  | c :: cs, s =>
    match runM spec specIdx s (deriveClause d tspec c) with
    | .error e => .error e
    | .ok ress =>
      match State.deriveAll prev s ress.flatten with
      | (s1, ch) =>
        match passType spec specIdx prev d tspec cs s1 with
        | .error e => .error e
        | .ok (s2, ch2) => .ok (s2, ch || ch2)

/-- One pass over the types of a stratum; returns the state and whether it grew. -/
def pass (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) : List DomId → State → Except RuntimeError (State × Bool)
  | [], s => .ok (s, false)
  | d :: ds, s =>
    match (specIdx.lookup d).map (·.1) with
    | none => pass spec specIdx prev ds s
    | some tspec =>
      match passType spec specIdx prev d tspec tspec.derivation s with
      | .error e => .error e
      | .ok (s1, ch) =>
        match pass spec specIdx prev ds s1 with
        | .error e => .error e
        | .ok (s2, ch2) => .ok (s2, ch || ch2)

def saturateStratum (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (types : List DomId) : Nat → State → Except RuntimeError State
  | 0, _ => .error (.fuelExhausted s!"saturating {", ".intercalate types}")
  | fuel + 1, state =>
    match pass spec specIdx prev types state with
    | .error e => .error e
    | .ok (s', changed) => if changed then saturateStratum spec specIdx prev types fuel s' else .ok s'

/-- Remove derived facts and recompute them stratum by stratum (eFLINT `rebase_and_sat`,
D6); a fact derived before and again keeps its stamp (D7). -/
def rebaseAndSatWithIdx (spec : Spec) (specIdx : Spec.SpecIndex) (strata : List (List DomId)) (state : State) : Except RuntimeError State :=
  let prev := state.derivedFacts
  strata.foldlM (fun s layer => saturateStratum spec specIdx prev layer 100000 s) state.rebase

def rebaseAndSat (spec : Spec) (strata : List (List DomId)) (state : State) : Except RuntimeError State :=
  rebaseAndSatWithIdx spec spec.buildIndex strata state

end Saturate

/-! ## Phrases -/

/-- The configuration between phrases: the spec, the state, its strata, and the
duties violated after the last phrase (for D12 reporting). -/
structure Config where
  spec           : Spec := emptySpec
  strata         : List (List DomId) := []
  state          : State := {}
  violatedDuties : List Tagged := []
  deriving Repr, Inhabited

/-- What a phrase reports (eFLINT `Output`). -/
inductive Output where
  | diag (d : Diagnostic)
  | executed (info : TransInfo)
  | violation (v : Violation)
  | queryRes (ok : Bool)
  | instQueryRes (tes : List Tagged)
  /-- Charter: the result of `?lawful`/`?valid`/`?violated`. -/
  | expectRes (what : Expect) (negated : Bool) (ok : Bool)
  /-- Charter (D7): the clock was set (environment input, not an event). -/
  | timeSet (t : Int)
  /-- Charter (Law 6): the answer to `?why e`: one line per instance. -/
  | whyRes (lines : List String)

def Output.isFailure : Output → Bool
  | .diag d => d.isError
  | .queryRes ok => !ok
  | .expectRes _ _ ok => !ok
  | _ => false

namespace Interp

open M

def diagOf (e : RuntimeError) : Output := .diag (Diagnostic.error e.code e.message)

/-- For a derived fact, the rules of its type, as text. -/
def ruleText (spec : Spec) (i : Info) : String :=
  match i.origin with
  | .derived d _ =>
    match spec.findDecl d with
    | some t =>
      let rules := t.derivation.map fun
        | .holdsWhen c => s!"Holds when {c}"
        | .dv xs c => s!"Derived from (Foreach {", ".intercalate (xs.map toString)}: {c})"
      s!"; rules: {"; ".intercalate rules}"
    | none => ""
  | _ => ""


/-- Report the violations a trigger caused (eFLINT `tell_violations`). -/
def triggerViolations (info : TransInfo) (fuel : Nat) : List Output :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if info.isAction then (if info.forced then [.violation (.trigger info)] else [])
    else info.syncs.flatMap (triggerViolations · fuel)

/-- Evaluate a compiled phrase to the store it applies (eFLINT `sem_phrase`).
`none` means the phrase failed and the configuration is unchanged. -/
def semPhrase (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) : Nat → CPhrase → Option Store × List Output
  | 0, _ => (none, [.diag (Diagnostic.error "CHR104" "phrase too deeply nested")])
  | fuel + 1, p =>
    let ctx := Ctx.ofIdx spec specIdx state
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ctx []
    match p with
    | .onlyDecls init => (some init, [])
    | .scenario .. => (some [], [])
    | .why xs t =>
      match run (foreach M.fuel xs (whenTagged (eval M.fuel t) pure)) with
      | .error e => (none, [diagOf e])
      | .ok tess =>
        let lines := tess.flatten.map fun te =>
          match state.lookup te with
          | none =>
            match spec.judgedAct te.2 with
            | some _ =>
              -- D15: judged for this instance, never materialised
              match run (isHolds M.fuel te) with
              | .ok [true] => s!"{te}: holds; judged for this instance by its Holds when (D15: the domain of {te.2} is not enumerable, so no instance is materialised)"
              | _ => s!"{te}: does not hold; its Holds when is false for this instance (D15: the domain of {te.2} is not enumerable, so no instance is materialised)"
            | none => s!"{te}: no assignment and not derived{if spec.closedType te.2 == some false then " (open type: input is missing)" else " (closed type: does not hold)"}"
          | some i =>
            let holds := if i.live state.time then "holds" else if i.value then "expired" else "does not hold"
            let exp := match i.expiry with | some u => s!", until {u}" | none => ""
            s!"{te}: {holds} since {i.since}{exp}; {i.origin.render}{ruleText spec i}"
        (some [], [.whyRes lines])
    | .setTime _ => (some [], [])
    | .tick => (some [], [])
    | .expect w neg xs t =>
      let ask (te : Tagged) : M Bool := match w with
        | .lawful => isEnabled M.fuel te
        | .valid => isValid M.fuel te
        | .violated => isViolated M.fuel te
      match run (foreach M.fuel xs (whenTagged (eval M.fuel t) ask)) with
      | .error e => (none, [diagOf e])
      | .ok bss => (some [], [.expectRes w neg (bss.flatten.all (fun b => b != neg))])
    | .query t =>
      match run (eval M.fuel t) with
      | .error e => (none, [diagOf e])
      | .ok vs => (some [], [.queryRes (vs.all (· == .bool true))])
    | .instQuery b xs t =>
      let t' := if b then Term.when t (.present t) else t
      match run (foreach M.fuel xs (whenTagged (eval M.fuel t') pure)) with
      | .error e => (none, [diagOf e])
      | .ok vss => (some [], [.instQueryRes vss.flatten])
    | .create xs t => effect ctx (.cAll xs t)
    | .terminate xs t => effect ctx (.tAll xs t)
    | .obfuscate xs t => effect ctx (.oAll xs t)
    | .trigger xs t =>
      let m : M (Sum DomId (List TransInfo)) := do
        let tes ← foreach M.fuel xs (whenTagged (eval M.fuel t) pure)
        match tes with
        | te :: _ =>
          if spec.triggerable te.2 then .inr <$> tes.mapM (instantiateTrans M.fuel [])
          else pure (.inl te.2)
        | [] => pure (.inr [])
      match run m with
      | .error e => (none, [diagOf e])
      | .ok [.inl d] => (some [], [.diag (Diagnostic.error "CHR103" s!"{d} is not an act or event and cannot be triggered")])
      | .ok [.inr infos] =>
        let outs := infos.flatMap fun i => Output.executed i :: triggerViolations i 1000
        (some (Store.unions (infos.map (·.assignments))), outs)
      | .ok _ => (none, [.diag (Diagnostic.error "CHR104" "a trigger produced an unexpected number of results")])
    | .par ps =>
      let rs := ps.map (semPhrase spec specIdx state fuel)
      let outs := rs.flatMap (·.2)
      if rs.all (·.1.isSome) then (some (Store.unions (rs.filterMap (·.1))), outs)
      else (none, outs)
where
  effect (ctx : Ctx) (e : Effect) : Option Store × List Output :=
    match (evalEffect M.fuel e).run ctx [] with
    | .error err => (none, [diagOf err])
    | .ok stores => (some (Store.unions stores), [])

/-- Apply a store, saturate, and find the violations (eFLINT `new_context`). `state1`
is the state after the phrase's assignments (and any clock change). -/
def newContext (cfg : Config) (spec : Spec) (specIdx : Spec.SpecIndex) (strata : List (List DomId)) (state1 : State) :
    Option Config × List Output :=
  match Saturate.rebaseAndSatWithIdx spec specIdx strata state1 with
  | .error e => (none, [diagOf e])
  | .ok state' =>
    let duties := state'.holdsList.filter fun te => match specIdx.lookup te.2 with
      | some ({ kind := .duty _, .. }, _, _) => true
      | _ => false
    let ctx' := Ctx.ofIdx spec specIdx state'
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ctx' []
    let violatedNow : Except RuntimeError (List Tagged) :=
      duties.filterMapM fun te => do
        let r ← run (ignoreMissingInput (evalViolationCondition M.fuel te (spec.findViolationCond te.2)))
        pure (if r.any id then some te else none)
    match violatedNow with
    | .error e => (none, [diagOf e])
    | .ok violated =>
      let newDuty := violated.filter (fun te => !cfg.violatedDuties.contains te)
      let invs : Except RuntimeError (List DomId) :=
        spec.invariants.filterMapM fun d => do
          let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
          let r ← run (ignoreMissingInput (checkFalse (eval M.fuel term)))
          pure (if r.isEmpty then none else some d)
      match invs with
      | .error e => (none, [diagOf e])
      | .ok invViol =>
        let outs := newDuty.map (fun te => Output.violation (.duty te)) ++ invViol.map (fun d => Output.violation (.invariant d))
        (some { spec, strata, state := state', violatedDuties := violated }, outs)

end Interp

mutual
/-- Whether a phrase introduces or extends declarations (so `spec` and `strata` change). -/
def Phrase.hasDecls : Phrase → Bool
  | .decls _ => true
  | .par ps => Phrase.listHasDecls ps
  | _ => false
def Phrase.listHasDecls : List Phrase → Bool
  | [] => false
  | p :: ps => p.hasDecls || Phrase.listHasDecls ps
end

/-- Run one phrase: resolve it against the configuration, evaluate, apply, saturate,
report. On failure the configuration is returned unchanged. -/
def runPhrase (cfg : Config) (p : Phrase) : Config × List Output :=
  let declChanged := p.hasDecls
  match resolvePhrase cfg.spec p with
  | .error ds => (cfg, ds.map .diag)
  | .ok (spec', cp, warnings) =>
    let warnOuts := warnings.map Output.diag
    let strataRes : Except (List DomId) (List (List DomId)) :=
      if declChanged then Stratify.strata spec' else .ok cfg.strata
    match strataRes with
    | .error cycle =>
      (cfg, warnOuts ++ [.diag (Diagnostic.error "CHR020"
        s!"derivation is not stratifiable: {", ".intercalate cycle} depend on their own absence (through Not, Forall, or an aggregate)")])
    | .ok strata =>
      let specIdx := spec'.buildIndex
      -- the clock (D7): environment input applied before saturation, never a transition
      let clock : Except RuntimeError (Option Int) := match cp with
        | .tick => .ok (some (cfg.state.time + 1))
        | .setTime t =>
          match (M.eval M.fuel t).run (Ctx.ofIdx spec' specIdx cfg.state) [] with
          | .error e => .error e
          | .ok [.int t] => if t < cfg.state.time then .error (.timeBackwards cfg.state.time t) else .ok (some t)
          | .ok _ => .error (.fuelExhausted "reading the clock")
        | _ => .ok none
      match clock with
      | .error e => (cfg, warnOuts ++ [Interp.diagOf e])
      | .ok newTime =>
      let state0 := match newTime with
        | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
        | none => { cfg.state with step := cfg.state.step + 1 }
      let (store?, outs) := Interp.semPhrase spec' specIdx state0 1000 cp
      let outs := match newTime with
        | some t => Output.timeSet t :: outs
        | none => outs
      match store? with
      | none => (cfg, warnOuts ++ outs)
      | some store =>
        if !declChanged && newTime.isNone && store.isEmpty then
          -- No declaration, clock, or assignment changed: `state0` is already at its
          -- stratified fixpoint and `cfg.violatedDuties` is unchanged; check invariants (013.1).
          let ctx0 := Ctx.ofIdx spec' specIdx state0
          let run {α} (m : M α) : Except RuntimeError (List α) := m.run ctx0 []
          let invs : Except RuntimeError (List DomId) :=
            spec'.invariants.filterMapM fun d => do
              let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
              let r ← run (M.ignoreMissingInput (M.checkFalse (M.eval M.fuel term)))
              pure (if r.isEmpty then none else some d)
          match invs with
          | .error e => (cfg, warnOuts ++ outs ++ [Interp.diagOf e])
          | .ok invViol =>
            let outs2 := invViol.map (fun d => Output.violation (.invariant d))
            ({ cfg with spec := spec', state := state0 }, warnOuts ++ outs ++ outs2)
        else
          let state1 := State.makeAssignments spec' store state0
          let (cfg'?, outs2) := Interp.newContext cfg spec' specIdx strata state1
          match cfg'? with
          | none => (cfg, warnOuts ++ outs ++ outs2)
          | some cfg' => (cfg', warnOuts ++ outs ++ outs2)

/-! ## Exploration (plan §2.2.7): bounded search over acts from a state -/

namespace Explore

open M

/-- D15: where the candidates for a component of a judged act (`Spec.judgedAct`) came
from: the `explore-domain` menu, or the values of that kind found in the state (the
named heuristic `state-values`, reported and never a passing claim on its own). -/
inductive Source where
  | menu
  | stateValues
  deriving Repr, BEq, Inhabited

/-- One component of a judged act whose candidates had to be supplied: the act, the
component's type, and where its candidates came from. -/
structure Coverage where
  act    : DomId
  comp   : DomId
  source : Source
  deriving Repr, Inhabited

/-- The menu for exploration: candidate values per type (D15, `//! explore-domain: t = …`). -/
abbrev Menu := List (DomId × List Elem)

/-- The primitive leaves of an element. -/
partial def Elem.leaves : Elem → List Elem
  | .prod xs => xs.flatMap (fun p => Elem.leaves p.1)
  | e => [e]

/-- The values of a primitive kind that occur anywhere in the instances that hold. -/
def stateValues (s : State) (dom : Domain) : List Elem :=
  let leaves := s.holdsList.flatMap (fun te => Elem.leaves te.1)
  let wanted := leaves.filter fun e => match dom, e with
    | .anyInt, .int _ | .time, .int _ | .duration, .int _ => true
    | .anyString, .str _ => true
    | _, _ => false
  wanted.foldl (fun acc e => if acc.any (Elem.beq e) then acc else acc ++ [e]) []

/-- Whether a component type of a judged act needs a menu: its domain is a primitive
that cannot be listed. A product component with an `Int` inside ranges over what holds. -/
def needsMenu (spec : Spec) (d : DomId) : Option Domain :=
  match spec.findDecl d with
  | some t => match t.domain with
    | .anyInt | .anyString | .time | .duration => some t.domain
    | _ => none
  | none => none

/-- The components of every judged act that need candidates, and where they come from
under `menu`. -/
def coverage (spec : Spec) (menu : Menu) : List Coverage :=
  spec.decls.flatMap fun (p : DomId × TypeSpec) =>
    match spec.judgedAct p.1 with
    | none => []
    | some _ => (spec.components p.1).filterMap fun x =>
      let d := spec.removeDecoration x
      match needsMenu spec d with
      | none => none
      | some _ => some ⟨p.1, d, if menu.any (·.1 == d) then .menu else .stateValues⟩

/-- Bind each component of a judged act: an enumerable or product component as `scope`
does, a primitive non-enumerable one over the menu's values for its type, else over the
values of that kind in the state (D15). -/
def scopeJudged (menu : Menu) : Nat → List Var → M Tagged → M Tagged
  | 0, _, _ => err (.fuelExhausted "binding a judged act's components")
  | _, [], m => m
  | fuel + 1, x :: xs, m => do
    let spec ← getSpec
    let state ← getState
    let d := spec.removeDecoration x
    let te ← match needsMenu spec d with
      | none => everyValidSubs fuel x
      | some dom =>
        let vals := match menu.find? (·.1 == d) with
          | some (_, vs) => vs
          | none => stateValues state dom
        let te ← nd (vals.map fun e => ((e, d) : Tagged))
        if ← isValidInstance fuel te then pure te else empty
    bindVar x te (scopeJudged menu fuel xs m)

/-- Every instance of every act type that is enabled in the configuration: the
candidates for a next step under lawful behaviour. A judged act's candidates come from
the menu or the state (D15). -/
def enabledActs (menu : Menu) (cfg : Config) : Except RuntimeError (List Tagged) := do
  let spec := cfg.spec
  let ctx := Ctx.of spec cfg.state
  let acts := spec.decls.filterMap fun (p : DomId × TypeSpec) => match p.2.kind with
    | .act _ => some p.1
    | _ => none
  acts.foldlM (fun acc d => do
    let xs := spec.components d
    let body : M Tagged := whenTagged (eval M.fuel (.app d (.named []))) pure
    let m : M (List Tagged) := results (match spec.judgedAct d with
      | some _ => scopeJudged menu M.fuel xs body
      | none => scope M.fuel xs body)
    let insts ← (ignoreMissingInput m).run ctx []
    let insts := insts.flatten
    let enabled ← insts.filterMapM fun te => do
      let r ← (ignoreMissingInput (isEnabled M.fuel te)).run ctx []
      pure (if r.any id then some te else none)
    pure (acc ++ enabled)) []

/-- Perform one act instance from a configuration (the `trigger` step without a phrase). -/
def perform (cfg : Config) (te : Tagged) : Except RuntimeError Config := do
  let specIdx := cfg.spec.buildIndex
  let ctx := Ctx.ofIdx cfg.spec specIdx cfg.state
  let infos ← (instantiateTrans M.fuel [] te).run ctx []
  let store := Store.unions (infos.map (·.assignments))
  let state1 := State.makeAssignments cfg.spec store { cfg.state with step := cfg.state.step + 1 }
  let state' ← Saturate.rebaseAndSatWithIdx cfg.spec specIdx cfg.strata state1
  pure { cfg with state := state' }

/-- The invariants that do not hold in a configuration. -/
def violatedInvariants (cfg : Config) : List DomId :=
  let ctx := Ctx.of cfg.spec cfg.state
  cfg.spec.invariants.filter fun d =>
    let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
    match (ignoreMissingInput (checkFalse (eval M.fuel term))).run ctx [] with
    | .ok rs => !rs.isEmpty
    | .error _ => false

/-- A canonical key of a state: the instances that hold, as sorted text. -/
def stateKey (s : State) : String :=
  let names := s.holdsList.map Tagged.pp
  String.intercalate "|" (names.toArray.qsort (· < ·)).toList

/-- The outcome of an exploration. -/
inductive Result where
  /-- No invariant violated within the bound; how many distinct states were visited, and
  which judged acts' components were explored from a menu or from the state (D15). -/
  | safe (visited : Nat) (cov : List Coverage)
  | violated (invariant : DomId) (trace : List Tagged) (visited : Nat)
  | error (e : RuntimeError)

/-- Breadth-first search over enabled acts from `cfg`, up to `depth` steps and `cap`
visited states, returning the shortest violating trace. Deterministic: candidates
are taken in declaration order, so the same program and depth always give the same
answer (the "seed" of plan §2.2.7 is the declaration order). -/
def bfs (menu : Menu) (cfg : Config) (depth cap : Nat) : Result :=
  let cov := coverage cfg.spec menu
  match violatedInvariants cfg with
  | d :: _ => .violated d [] 1
  | [] =>
    let rec go (frontier : List (Config × List Tagged)) (seen : List String) (fuel : Nat) : Result :=
      match fuel with
      | 0 => .safe seen.length cov
      | fuel + 1 =>
        if frontier.isEmpty then .safe seen.length cov else
        -- expand the whole frontier one level
        let step := frontier.foldl (fun (acc : Except RuntimeError (List (Config × List Tagged) × List String × Option (DomId × List Tagged))) (c, trace) =>
          match acc with
          | .error e => .error e
          | .ok (next, seen, some v) => .ok (next, seen, some v)
          | .ok (next, seen, none) =>
            match enabledActs menu c with
            | .error e => .error e
            | .ok cands =>
              cands.foldl (fun acc te =>
                match acc with
                | .error e => .error e
                | .ok (next, seen, some v) => .ok (next, seen, some v)
                | .ok (next, seen, none) =>
                  if seen.length ≥ cap then .ok (next, seen, none) else
                  match perform c te with
                  | .error e => .error e
                  | .ok c' =>
                    let key := stateKey c'.state
                    if seen.contains key then .ok (next, seen, none)
                    else
                      let trace' := trace ++ [te]
                      match violatedInvariants c' with
                      | d :: _ => .ok (next, key :: seen, some (d, trace'))
                      | [] => .ok (next ++ [(c', trace')], key :: seen, none)) (.ok (next, seen, none)))
          (.ok ([], seen, none))
        match step with
        | .error e => .error e
        | .ok (_, seen, some (d, trace)) => .violated d trace seen.length
        | .ok (next, seen, none) => go next seen fuel
    go [(cfg, [])] [stateKey cfg.state] depth

end Explore

end Charter
