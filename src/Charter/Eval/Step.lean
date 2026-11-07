import Charter.Eval.Eval
import Charter.Core.Derivation
import Charter.Core.Diagnostics

/-!
# Charter.Eval.Step — Operator-Blind `CIR` Saturation & Compiled Step Engine (`G4.1`, `Law 9`)

Contains the **single** runtime saturation and compiled-phrase step engine shared identically
by the `charter` compiler (`Charter.Eval.Interpreter`) and the operator-blind `charter-server`
runtime (`src/Server.lean`).

Imports `Charter.Eval.Eval`, `Charter.Core.Derivation`, and `Charter.Core.Diagnostics` **only**
(zero imports from `Charter.Surface.*`, `Charter.Resolve.*`, or `Charter.Prove.*`).
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
  | .defeasibleDAG dag rules =>
    let evalActiveRules : M (List (String × DefeasibleVal)) := do
      let pairs ← rules.mapM fun r => do
        let bs ← results (whenBool (eval M.fuel r.cond) pure)
        if !(bs.any id) then pure none
        else
          match r.conseq with
          | .holdsBool b => pure (some (r.id, DefeasibleVal.boolOut b))
          | .yieldsVal vt =>
            let vs ← results (whenTagged (eval M.fuel vt) pure)
            match vs with
            | vTe :: _ => pure (some (r.id, DefeasibleVal.elemOut vTe))
            | [] => pure none
      pure (pairs.filterMap id)
    let lookupAct (active : List (String × DefeasibleVal)) (id : String) : Option DefeasibleVal :=
      match active.find? (fun (p : String × DefeasibleVal) => p.1 == id) with
      | some p => some p.2
      | none   => none
    let mkConflictTag (targetTe : Tagged) (r1 r2 : String) : Tagged :=
      (.prod [targetTe, (.str d, "string"), (.str r1, "string"), (.str r2, "string")], defConflictDom)
    match tspec.restriction, tspec.domain with
    | some .function, .products [kVar, _] =>
      foreach M.fuel [kVar] do
        let kTe ← substituteVar kVar
        let active ← evalActiveRules
        match Defeasible.evalCompiledDAG dag (lookupAct active) with
        | .determined _ (.elemOut vTe) => checkSat (pure (.prod [kTe, vTe], d))
        | .conflict r1 r2 => pure (mkConflictTag kTe r1 r2)
        | _ => empty
    | some .var, _ =>
      results do
        let active ← evalActiveRules
        match Defeasible.evalCompiledDAG dag (lookupAct active) with
        | .determined _ (.elemOut vTe) => checkSat (pure vTe)
        | .conflict r1 r2 => pure (mkConflictTag (.str d, "string") r1 r2)
        | _ => empty
    | _, .products xs =>
      foreach M.fuel xs do
        let te ← whenTagged (eval M.fuel (.app d (.named []))) pure
        let active ← withSubs (Tagged.bindings tspec.domain te) evalActiveRules
        match Defeasible.evalCompiledDAG dag (lookupAct active) with
        | .determined _ (.boolOut true) => checkSat (pure te)
        | .conflict r1 r2 => pure (mkConflictTag te r1 r2)
        | _ => empty
    | _, _ =>
      let x : Var := ⟨d, ""⟩
      foreach M.fuel [x] do
        let te ← substituteVar x
        let active ← withSubs (Tagged.bindings tspec.domain te) evalActiveRules
        match Defeasible.evalCompiledDAG dag (lookupAct active) with
        | .determined _ (.boolOut true) => checkSat (pure te)
        | .conflict r1 r2 => pure (mkConflictTag te r1 r2)
        | _ => empty

def runM {α} (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) (m : M α) : Except RuntimeError (List α) :=
  m.run (Ctx.ofIdx spec specIdx state) []

/-- One pass over the derivation clauses of one type; the state and whether it grew. -/
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

/-- Remove derived facts and recompute them stratum by stratum (eFLINT `rebase_and_sat`, D6). -/
def rebaseAndSatWithIdx (spec : Spec) (specIdx : Spec.SpecIndex) (strata : List (List DomId)) (state : State) : Except RuntimeError State :=
  let prev := state.derivedFacts
  strata.foldlM (fun s layer => saturateStratum spec specIdx prev layer 100000 s) state.rebase

def rebaseAndSat (spec : Spec) (strata : List (List DomId)) (state : State) : Except RuntimeError State :=
  rebaseAndSatWithIdx spec spec.buildIndex strata state

end Saturate

/-! ## Compiled Phrases & Runtime Configuration -/

structure Config where
  spec           : Spec := emptySpec
  strata         : List (List DomId) := []
  state          : State := {}
  violatedDuties : List Tagged := []
  lawVersion     : Nat := 0
  deriving Repr, Inhabited

/-- What a phrase reports (eFLINT `Output`). -/
inductive Output where
  | diag (d : Diagnostic)
  | executed (info : TransInfo)
  | violation (v : Violation)
  | queryRes (ok : Bool)
  | instQueryRes (tes : List Tagged)
  | expectRes (what : Expect) (negated : Bool) (ok : Bool)
  | timeSet (t : Int)
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
        | .defeasibleDAG _ rs => s!"Defeasible DAG ({", ".intercalate (rs.map (·.id))})"
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

/-- Evaluate a compiled phrase to the store it applies (eFLINT `sem_phrase`). -/
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
          let tspec? : Option TypeSpec := spec.findDecl te.2
          let spanSuffix := match tspec? with
            | some ts =>
              if ts.spans.isEmpty then ""
              else "; from " ++ ", ".intercalate (ts.spans.map fun (p : ClauseId × String) => s!"{p.1} {showString p.2}")
            | none => ""
          if (tspec?.map TypeSpec.isEvidencedFact).getD false then
            let st := state.evidenceStatus te
            let srcs := state.evidenceSources te
            let srcStr := if srcs.isEmpty then "no tendered evidence"
              else ", ".intercalate (srcs.map fun (k, s, n) =>
                if s.isEmpty then s!"{k} at phrase {n}" else s!"{k} by {showString s} at phrase {n}")
            s!"{te}: epistemic status {st.asString} ({srcStr}){spanSuffix}"
          else
            match state.lookup te with
            | none =>
              match spec.judgedAct te.2 with
              | some _ =>
                match run (isHolds M.fuel te) with
                | .ok [true] => s!"{te}: holds; judged for this instance by its Holds when (D15: the domain of {te.2} is not enumerable, so no instance is materialised){spanSuffix}"
                | _ => s!"{te}: does not hold; its Holds when is false for this instance (D15: the domain of {te.2} is not enumerable, so no instance is materialised){spanSuffix}"
              | none => s!"{te}: no assignment and not derived{if spec.closedType te.2 == some false then " (open type: input is missing)" else " (closed type: does not hold)"}{spanSuffix}"
            | some i =>
              let holds := if i.live state.time then "holds" else if i.value then "expired" else "does not hold"
              let exp := match i.expiry with | some u => s!", until {u}" | none => ""
              s!"{te}: {holds} since {i.since}{exp}; {i.origin.render}{ruleText spec i}{spanSuffix}"
        (some [], [.whyRes lines])
    | .setTime _ => (some [], [])
    | .tick => (some [], [])
    | .expect w neg xs t =>
      let ask (te : Tagged) : M Bool := match w with
        | .lawful => isEnabled M.fuel te
        | .valid => isValid M.fuel te
        | .violated => isViolated M.fuel te
        | .undetermined => do
          let (lTri, vTri, _) ← evalActTri M.fuel te
          pure (lTri == .undetermined || vTri == .undetermined)
        | .conflict => do
          let conf? ← lookupNormativeConflict te
          pure conf?.isSome
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
    | .submitEvidence pol xs t src => effect ctx (.evOp (if pol then .support else .rebut) xs t src)
    | .retractEvidence xs t src => effect ctx (.evOp .retract xs t src)
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

/-- Check all declared invariants on `state` (`013.1`). -/
def checkInvariants (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) : Except RuntimeError (List DomId) :=
  let ctx := Ctx.ofIdx spec specIdx state
  spec.invariants.filterMapM fun d => do
    let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
    let r ← (ignoreMissingInput (checkFalse (eval M.fuel term))).run ctx []
    pure (if r.isEmpty then none else some d)

/-- Evaluate an environment clock phrase (`@ t` or `tick`, `009.1`). -/
def evalClockStep (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) (cp : CPhrase) :
    Except RuntimeError (Option Int) :=
  match cp with
  | .tick => .ok (some (state.time + 1))
  | .setTime t =>
    match (eval M.fuel t).run (Ctx.ofIdx spec specIdx state) [] with
    | .error e => .error e
    | .ok [.int t'] => if t' < state.time then .error (.timeBackwards state.time t') else .ok (some t')
    | .ok _ => .error (.fuelExhausted "reading the clock")
  | _ => .ok none

/-- Extract and strip transient `amendCommitDom` markers written by valid `Amend` acts (`D11`, `D25`). -/
def extractAmendCommits (s : State) : List DomId × State :=
  let commits := s.contents.filterMap fun (te, i) =>
    if te.2 == amendCommitDom && i.live s.time then
      match te.1 with | .str actId => some actId | _ => none
    else none
  if commits.isEmpty then ([], s)
  else (commits.reverse, { s with contents := s.contents.filter fun (te, _) => te.2 != amendCommitDom })

def newContextAfterAmend (cfg : Config) (effSpec : Spec) (effSpecIdx : Spec.SpecIndex)
    (effStrata : List (List DomId)) (nextVer : Nat) (state1Clean : State) :
    Option Config × List Output :=
  match Saturate.rebaseAndSatWithIdx effSpec effSpecIdx effStrata state1Clean with
  | .error e => (none, [diagOf e])
  | .ok state' =>
    let duties := state'.holdsList.filter fun te => match effSpecIdx.lookup te.2 with
      | some ({ kind := .duty _, .. }, _, _) => true
      | _ => false
    let ctx' := Ctx.ofIdx effSpec effSpecIdx state'
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ctx' []
    let violatedNow : Except RuntimeError (List Tagged) :=
      duties.filterMapM fun te => do
        let r ← run (ignoreMissingInput (evalViolationCondition M.fuel te (effSpec.findViolationCond te.2)))
        pure (if r.any id then some te else none)
    match violatedNow with
    | .error e => (none, [diagOf e])
    | .ok violated =>
      let newDuty := violated.filter (fun te => !cfg.violatedDuties.contains te)
      match checkInvariants effSpec effSpecIdx state' with
      | .error e => (none, [diagOf e])
      | .ok invViol =>
        let outs := newDuty.map (fun te => Output.violation (.duty te)) ++ invViol.map (fun d => Output.violation (.invariant d))
        (some { spec := effSpec, strata := effStrata, state := state', violatedDuties := violated, lawVersion := nextVer }, outs)

/-- Apply a store, saturate, and find the violations (eFLINT `new_context`). -/
def newContext (cfg : Config) (spec : Spec) (specIdx : Spec.SpecIndex) (strata : List (List DomId)) (state1 : State) :
    Option Config × List Output :=
  let (amCommits, state1Clean) := extractAmendCommits state1
  if amCommits.isEmpty then
    newContextAfterAmend cfg spec specIdx strata cfg.lawVersion state1Clean
  else
    let sUpd := amCommits.foldl Amend.applyTriggeredAmend spec
    let stUpd := match Stratify.strata sUpd with | .ok st => st | .error _ => strata
    newContextAfterAmend cfg sUpd sUpd.buildIndex stUpd (cfg.lawVersion + amCommits.length) state1Clean

end Interp

/-- Execute an already-compiled `CPhrase` against `cfg` (`G4.1` operator-blind server step, `Law 9`). -/
def evalCompiledStep (cfg : Config) (cp : CPhrase) (forceSat : Bool := false) : Config × List Output :=
  let specIdx := cfg.spec.buildIndex
  match Interp.evalClockStep cfg.spec specIdx cfg.state cp with
  | .error e => (cfg, [Interp.diagOf e])
  | .ok newTime =>
    let state0 := match newTime with
      | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
      | none => { cfg.state with step := cfg.state.step + 1 }
    let (store?, outs) := Interp.semPhrase cfg.spec specIdx state0 1000 cp
    let outs := match newTime with
      | some t => Output.timeSet t :: outs
      | none => outs
    match store? with
    | none => (cfg, outs)
    | some store =>
      if !forceSat && newTime.isNone && store.isEmpty then
        match Interp.checkInvariants cfg.spec specIdx state0 with
        | .error e => (cfg, outs ++ [Interp.diagOf e])
        | .ok invViol =>
          let outs2 := invViol.map (fun d => Output.violation (.invariant d))
          ({ cfg with state := state0 }, outs ++ outs2)
      else
        let state1 := State.makeAssignments cfg.spec store state0
        let (cfg'?, outs2) := Interp.newContext cfg cfg.spec specIdx cfg.strata state1
        match cfg'? with
        | none => (cfg, outs ++ outs2)
        | some cfg' => (cfg', outs ++ outs2)

/-- Apply a declared `Regime` parameter overlay onto `cfg` (`014.4`, `D11`, `D25`). -/
def applyRegimeOverlay (cfg : Config) (regimeName : String) : Except String Config :=
  match cfg.spec.regimes.find? (·.name == regimeName) with
  | none =>
    let avail := if cfg.spec.regimes.isEmpty then "(none)" else ", ".intercalate (cfg.spec.regimes.map (·.name))
    .error s!"unknown regime `{regimeName}` (declared regimes: {avail})"
  | some reg =>
    let st : Store := reg.params.map fun (pname, val) => ((.int val, pname), Assignment.holdsTrue none none)
    let state1 := State.makeAssignments cfg.spec st cfg.state
    match Saturate.rebaseAndSat cfg.spec cfg.strata state1 with
    | .ok state' => .ok { cfg with state := state' }
    | .error e => .error e.message

end Charter
