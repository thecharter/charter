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

def splitConjuncts : Term → List Term
  | .and a b => splitConjuncts a ++ splitConjuncts b
  | .boolLit true => []
  | t => [t]
termination_by structural x => x

mutual
/-- Whether every variable read by `tm` is already in `bound` (`#78` conjunct pushdown). -/
def termReadyAt (spec : Spec) (specIdx : Spec.SpecIndex) (bound : List Var) : Term → Bool
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime | .dimLit _ _ => true
  | .ref x => bound.contains x
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .project a _ | .tag a _ | .untag a | .doneAt a | .stampOf a | .overdueOf a
  | .calOp1 _ a | .fnApp _ a => termReadyAt spec specIdx bound a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    termReadyAt spec specIdx bound a && termReadyAt spec specIdx bound b
  | .ite c t e | .mulDivRound c t e _ =>
    termReadyAt spec specIdx bound c && termReadyAt spec specIdx bound t && termReadyAt spec specIdx bound e
  | .exists_ ys u | .forall_ ys u | .count ys u | .sum ys u | .max ys u | .min ys u =>
    termReadyAt spec specIdx (bound ++ ys) u
  | .app _ (.pos ts) => termReadyList spec specIdx bound ts
  | .app f (.named ms) =>
    let realF := spec.chaseAlias f
    match specIdx.lookup realF with
    | some ({ domain := .products fxs, .. }, _, _) =>
      termReadyMods spec specIdx bound ms &&
      fxs.all (fun fx => bound.contains fx || ms.any (·.1 == fx))
    | _ => false
termination_by structural x => x

def termReadyList (spec : Spec) (specIdx : Spec.SpecIndex) (bound : List Var) : List Term → Bool
  | [] => true
  | t :: ts => termReadyAt spec specIdx bound t && termReadyList spec specIdx bound ts
termination_by structural x => x

def termReadyMods (spec : Spec) (specIdx : Spec.SpecIndex) (bound : List Var) : List (Var × Term) → Bool
  | [] => true
  | (_, t) :: ms => termReadyAt spec specIdx bound t && termReadyMods spec specIdx bound ms
termination_by structural x => x
end

/-- Bind `xs` left-to-right while pushing each conjunct of `conjs` to the earliest binder prefix
where all of its free variables are bound (`#78`: avoids materializing Cartesian act domains). -/
def scopeFiltered (spec : Spec) (specIdx : Spec.SpecIndex) :
    List Var → List Var → List Term → M Tagged → M Tagged
  | _, [], remConjs, leaf => do
    remConjs.forM fun cj => checkTrue (eval M.fuel cj)
    leaf
  | bound, x :: xs, remConjs, leaf =>
    let (readyNow, later) := remConjs.partition (termReadyAt spec specIdx bound)
    do
      readyNow.forM fun cj => checkTrue (eval M.fuel cj)
      let te ← everyValidSubs M.fuel x
      bindVar x te (scopeFiltered spec specIdx (x :: bound) xs later leaf)

/-- Peel outer `.exists_ ys body` layers whose binders are all closed in `specIdx` (`#78`:
`compileDerivation` wraps `Holds when` rules mentioning `Param`s or unbound closed facts in
`.exists_ unbound body`, which otherwise hides top-level `&&` conjuncts from `scopeFiltered`). -/
def peelClosedExists (spec : Spec) (specIdx : Spec.SpecIndex) : Term → List Var × Term
  | .exists_ ys body =>
    let ysClosed := ys.all fun y =>
      match specIdx.lookup (spec.removeDecoration y) with
      | some (yt, _, _) => yt.isClosed
      | none => false
    if ysClosed then
      let (more, inner) := peelClosedExists spec specIdx body
      (ys ++ more, inner)
    else ([], .exists_ ys body)
  | other => ([], other)
termination_by structural t => t

mutual
/-- Conservative syntactic check whether `t` mentions `target` or an indirect modal query
(`.enabled`/`.violated`) (`#78`: non-self-recursive singleton strata reach fixpoint in 1 pass). -/
def termMentionsDomOrModal (spec : Spec) (target : DomId) : Term → Bool
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime | .dimLit _ _ => false
  | .enabled _ | .violated _ => true
  | .ref x => spec.removeDecoration x == target
  | .project u x => spec.removeDecoration x == target || termMentionsDomOrModal spec target u
  | .tag u f => spec.chaseAlias f == target || termMentionsDomOrModal spec target u
  | .fnApp f k => spec.chaseAlias f == target || termMentionsDomOrModal spec target k
  | .app f (.pos ts) => spec.chaseAlias f == target || termMentionsList spec target ts
  | .app f (.named ms) => spec.chaseAlias f == target || termMentionsMods spec target ms
  | .exists_ ys u | .forall_ ys u | .count ys u | .sum ys u | .max ys u | .min ys u =>
    ys.any (fun y => spec.removeDecoration y == target) || termMentionsDomOrModal spec target u
  | .not u | .present u | .evStatus _ u | .hasConflict u | .doneAt u | .stampOf u
  | .overdueOf u | .calOp1 _ u | .untag u =>
    termMentionsDomOrModal spec target u
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b | .mult a b | .mod a b
  | .div a b | .sub a b | .add a b | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    termMentionsDomOrModal spec target a || termMentionsDomOrModal spec target b
  | .ite c t e | .mulDivRound c t e _ =>
    termMentionsDomOrModal spec target c || termMentionsDomOrModal spec target t || termMentionsDomOrModal spec target e
termination_by structural x => x

def termMentionsList (spec : Spec) (target : DomId) : List Term → Bool
  | [] => false
  | t :: ts => termMentionsDomOrModal spec target t || termMentionsList spec target ts
termination_by structural x => x

def termMentionsMods (spec : Spec) (target : DomId) : List (Var × Term) → Bool
  | [] => false
  | (_, t) :: ms => termMentionsDomOrModal spec target t || termMentionsMods spec target ms
termination_by structural x => x
end

/-- Whether `layer` may require more than a single saturation pass to reach fixpoint. -/
def layerNeedsLoop (spec : Spec) (specIdx : Spec.SpecIndex) : List DomId → Bool
  | [d] =>
    match (specIdx.lookup d).map (·.1) with
    | none => false
    | some tspec =>
      let canon := spec.chaseAlias d
      termMentionsDomOrModal spec canon tspec.domainConstraint ||
      termMentionsList spec canon tspec.conditions ||
      tspec.derivation.any fun
        | .holdsWhen t => termMentionsDomOrModal spec canon t
        | .dv ys t => ys.any (fun y => spec.removeDecoration y == canon) || termMentionsDomOrModal spec canon t
        | .defeasibleDAG _ _ => true
  | [] => false
  | _ => true

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
      if tspec.domainConstraint.isTrueLit then do
        let ctx ← getCtx
        let allClosed := ctx.indexed && xs.all fun x =>
          match ctx.specIdx.lookup (ctx.spec.removeDecoration x) with
          | some (xt, _, _) => xt.isClosed
          | none => false
        if allClosed then
          let (extraYs, inner) := peelClosedExists ctx.spec ctx.specIdx t
          let conjs := splitConjuncts inner
          if conjs.any (fun | .boolLit false => true | _ => false) then pure []
          else
            results (scopeFiltered ctx.spec ctx.specIdx [] (xs ++ extraYs) conjs
              (checkSat (whenTagged (eval M.fuel (.app d (.named []))) pure)))
        else
          foreach M.fuel xs do
            checkTrue (eval M.fuel t)
            checkSat (whenTagged (eval M.fuel (.app d (.named []))) pure)
      else dyn xs (.when (.app d (.named [])) t)
    | _ =>
      results do
        let (_, isEnum, _) ← getTypeEntry d
        let te ← if isEnum then do
          let e ← instantiateDomain M.fuel d tspec.domain
          let cand : Tagged := (e, d)
          if !tspec.domainConstraint.isTrueLit then
            withSubs (Tagged.bindings tspec.domain cand) (checkTrue (eval M.fuel tspec.domainConstraint))
          pure cand
        else everyValidSubs M.fuel ⟨d, ""⟩
        withSubs [(⟨d, ""⟩, te)] do
          checkTrue (eval M.fuel t)
          checkSat (pure te)
  | .dv xs (.when head cond) => do
    let ctx ← getCtx
    let allClosed := ctx.indexed && xs.all fun x =>
      match ctx.specIdx.lookup (ctx.spec.removeDecoration x) with
      | some (xt, _, _) => xt.isClosed
      | none => false
    if allClosed then
      let (extraYs, inner) := peelClosedExists ctx.spec ctx.specIdx cond
      if extraYs.all (!xs.contains ·) then
        let conjs := splitConjuncts inner
        if conjs.any (fun | .boolLit false => true | _ => false) then pure []
        else
          results (scopeFiltered ctx.spec ctx.specIdx [] (xs ++ extraYs) conjs
            (checkFilter (satConditions M.fuel) (whenTagged (eval M.fuel head) pure)))
      else dyn xs (.when head cond)
    else dyn xs (.when head cond)
  | .dv xs t => dyn xs t
  | .defeasibleDAG dag rules =>
    let evalActiveRules : M (List (String × DefeasibleVal)) := do
      let pairs ← rules.mapM fun r => do
        if r.freeVars.isEmpty then
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
        else
          let outs ← foreach M.fuel r.freeVars do
            checkTrue (eval M.fuel r.cond)
            match r.conseq with
            | .holdsBool b => pure (DefeasibleVal.boolOut b)
            | .yieldsVal vt =>
              let vTe ← whenTagged (eval M.fuel vt) pure
              pure (DefeasibleVal.elemOut vTe)
          match outs with
          | v :: _ => pure (some (r.id, v))
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

def runMWithIdx {α} (spec : Spec) (specIdx : Spec.SpecIndex) (hasEp : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec))
    (state : State) (stateIdx : State.StateIndex) (m : M α) : Except RuntimeError (List α) :=
  m.run (Ctx.ofBothIdx spec specIdx state stateIdx hasEp (some immDecls)) []

/-- Indexed single-type pass keeping `sIdx = s.buildIndex` incrementally (`#78`: zero `buildIndex` rebuilds). -/
def passTypeIdx (spec : Spec) (specIdx : Spec.SpecIndex) (hasEp : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec)) (prevIdx : State.StateIndex)
    (d : DomId) (tspec : TypeSpec) :
    List Derivation → State → State.StateIndex → Except RuntimeError (State × State.StateIndex × Bool)
  | [], s, sIdx => .ok (s, sIdx, false)
  | c :: cs, s, sIdx =>
    match runMWithIdx spec specIdx hasEp immDecls s sIdx (deriveClause d tspec c) with
    | .error e => .error e
    | .ok ress =>
      match State.deriveAllWithIdx prevIdx s sIdx ress.flatten with
      | (s1, sIdx1, ch) =>
        match passTypeIdx spec specIdx hasEp immDecls prevIdx d tspec cs s1 sIdx1 with
        | .error e => .error e
        | .ok (s2, sIdx2, ch2) => .ok (s2, sIdx2, ch || ch2)

def passIdx (spec : Spec) (specIdx : Spec.SpecIndex) (hasEp : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec)) (prevIdx : State.StateIndex) :
    List DomId → State → State.StateIndex → Except RuntimeError (State × State.StateIndex × Bool)
  | [], s, sIdx => .ok (s, sIdx, false)
  | d :: ds, s, sIdx =>
    match (specIdx.lookup d).map (·.1) with
    | none => passIdx spec specIdx hasEp immDecls prevIdx ds s sIdx
    | some tspec =>
      match passTypeIdx spec specIdx hasEp immDecls prevIdx d tspec tspec.derivation s sIdx with
      | .error e => .error e
      | .ok (s1, sIdx1, ch) =>
        match passIdx spec specIdx hasEp immDecls prevIdx ds s1 sIdx1 with
        | .error e => .error e
        | .ok (s2, sIdx2, ch2) => .ok (s2, sIdx2, ch || ch2)

def saturateStratumIdx (spec : Spec) (specIdx : Spec.SpecIndex) (hasEp : Bool) (isRec : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec)) (prevIdx : State.StateIndex)
    (types : List DomId) : Nat → State → State.StateIndex → Except RuntimeError (State × State.StateIndex)
  | 0, _, _ => .error (.fuelExhausted s!"saturating {", ".intercalate types}")
  | fuel + 1, state, sIdx =>
    match passIdx spec specIdx hasEp immDecls prevIdx types state sIdx with
    | .error e => .error e
    | .ok (s', sIdx', changed) =>
      if changed && isRec then saturateStratumIdx spec specIdx hasEp isRec immDecls prevIdx types fuel s' sIdx'
      else .ok (s', sIdx')

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

/-- Infer exact threshold clock timestamps (`D38`, `#16`, `#47`) for newly derived facts
and recurring `Every <period>` duties so `Held(e) For d` and `Due within` do not depend on
which intermediate clock instants a scenario happens to visit. -/
def clockThresholdSeeds (spec : Spec) (specIdx : Spec.SpecIndex) (acc : State) (layer : List DomId) :
    List (Tagged × Info) :=
  let evalConstInt (tm : Term) : Option Int :=
    match runM spec specIdx acc (whenInt (eval M.fuel tm) pure) with
    | .ok (k :: _) => some k
    | _ => none
  let evalConstTag (tm : Term) : Option Tagged :=
    match runM spec specIdx acc (whenTagged (eval M.fuel tm) pure) with
    | .ok (te :: _) => some te
    | _ => none
  let clauseThreshold : Derivation → Option Int
    | .holdsWhen (.geq .currentTime kTm) => evalConstInt kTm
    | .holdsWhen (.ge .currentTime kTm) => (evalConstInt kTm).map (· + 1)
    | .holdsWhen (.geq (.sub .currentTime t0Tm) durTm) =>
      Option.bind (evalConstInt t0Tm) fun t0 => (evalConstInt durTm).map (t0 + ·)
    | .holdsWhen (.ge (.sub .currentTime t0Tm) durTm) =>
      Option.bind (evalConstInt t0Tm) fun t0 => (evalConstInt durTm).map (t0 + · + 1)
    | .holdsWhen (.heldFor innerTm durTm) =>
      Option.bind (evalConstTag innerTm) fun teIn =>
      Option.bind (acc.lookup teIn) fun iIn =>
      (evalConstInt durTm).map (iIn.since + ·)
    | .holdsWhen (.present innerTm) =>
      Option.bind (evalConstTag innerTm) fun teIn =>
      (acc.lookup teIn).map (·.since)
    | _ => none
  layer.flatMap fun d =>
    match (specIdx.lookup d).map (·.1) with
    | none => []
    | some tspec =>
      match tspec.kind with
      | .duty { everyPeriod := some perLen, .. } =>
        tspec.derivation.flatMap fun c =>
          match runM spec specIdx acc (deriveClause d tspec c) with
          | .ok ress =>
            ress.flatten.filterMap fun te =>
              match te.1 with
              | .prod args =>
                match args.getLast? with
                | some (.int k, _) =>
                  let t0 := k * perLen
                  if t0 <= acc.time then some (te, ⟨true, true, t0, none, .derived d acc.step⟩)
                  else none
                | _ => none
              | _ => none
          | .error _ => []
      | _ =>
        match tspec.domain with
        | .products [] =>
          let candTs := tspec.derivation.filterMap clauseThreshold |>.filter (· <= acc.time)
          match candTs with
          | [] => []
          | t0 :: rest =>
            let earliest := rest.foldl min t0
            [((.prod [], d), ⟨true, true, earliest, none, .derived d acc.step⟩)]
        | _ => []

/-- Indexed variant of `clockThresholdSeeds` reusing `accIdx` (`#78`). -/
def clockThresholdSeedsIdx (spec : Spec) (specIdx : Spec.SpecIndex) (hasEp : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec))
    (acc : State) (accIdx : State.StateIndex) (layer : List DomId) : List (Tagged × Info) :=
  let lookupIdx (te : Tagged) : Option Info :=
    (((accIdx.lookup te.2).getD []).find? (·.1 == te)).map (·.2)
  let evalConstInt (tm : Term) : Option Int :=
    match runMWithIdx spec specIdx hasEp immDecls acc accIdx (whenInt (eval M.fuel tm) pure) with
    | .ok (k :: _) => some k
    | _ => none
  let evalConstTag (tm : Term) : Option Tagged :=
    match runMWithIdx spec specIdx hasEp immDecls acc accIdx (whenTagged (eval M.fuel tm) pure) with
    | .ok (te :: _) => some te
    | _ => none
  let clauseThreshold : Derivation → Option Int
    | .holdsWhen (.geq .currentTime kTm) => evalConstInt kTm
    | .holdsWhen (.ge .currentTime kTm) => (evalConstInt kTm).map (· + 1)
    | .holdsWhen (.geq (.sub .currentTime t0Tm) durTm) =>
      Option.bind (evalConstInt t0Tm) fun t0 => (evalConstInt durTm).map (t0 + ·)
    | .holdsWhen (.ge (.sub .currentTime t0Tm) durTm) =>
      Option.bind (evalConstInt t0Tm) fun t0 => (evalConstInt durTm).map (t0 + · + 1)
    | .holdsWhen (.heldFor innerTm durTm) =>
      Option.bind (evalConstTag innerTm) fun teIn =>
      Option.bind (lookupIdx teIn) fun iIn =>
      (evalConstInt durTm).map (iIn.since + ·)
    | .holdsWhen (.present innerTm) =>
      Option.bind (evalConstTag innerTm) fun teIn =>
      (lookupIdx teIn).map (·.since)
    | _ => none
  layer.flatMap fun d =>
    match (specIdx.lookup d).map (·.1) with
    | none => []
    | some tspec =>
      match tspec.kind with
      | .duty { everyPeriod := some perLen, .. } =>
        tspec.derivation.flatMap fun c =>
          match runMWithIdx spec specIdx hasEp immDecls acc accIdx (deriveClause d tspec c) with
          | .ok ress =>
            ress.flatten.filterMap fun te =>
              match te.1 with
              | .prod args =>
                match args.getLast? with
                | some (.int k, _) =>
                  let t0 := k * perLen
                  if t0 <= acc.time then some (te, ⟨true, true, t0, none, .derived d acc.step⟩)
                  else none
                | _ => none
              | _ => none
          | .error _ => []
      | _ =>
        match tspec.domain with
        | .products [] =>
          let candTs := tspec.derivation.filterMap clauseThreshold |>.filter (· <= acc.time)
          match candTs with
          | [] => []
          | t0 :: rest =>
            let earliest := rest.foldl min t0
            [((.prod [], d), ⟨true, true, earliest, none, .derived d acc.step⟩)]
        | _ => []

/-- Remove derived facts and recompute them stratum by stratum (eFLINT `rebase_and_sat`, D6),
maintaining `State.StateIndex` incrementally (`#78`). -/
def rebaseAndSatWithIdx (spec : Spec) (specIdx : Spec.SpecIndex) (strata : List (List DomId)) (state : State) : Except RuntimeError State := do
  let prev := state.derivedFacts
  let basePrevIdx := State.indexList prev
  let hasEp := spec.hasEpistemicOrDefeasible
  let immDecls := spec.allImmunities
  let s0 := state.rebase
  let (sFin, _) ← strata.foldlM (fun (s, sIdx) layer =>
    let seeds := clockThresholdSeedsIdx spec specIdx hasEp immDecls s sIdx layer
    let prevIdx := if seeds.isEmpty then basePrevIdx else State.indexList (prev ++ seeds)
    let isRec := layerNeedsLoop spec specIdx layer
    saturateStratumIdx spec specIdx hasEp isRec immDecls prevIdx layer 100000 s sIdx) (s0, s0.buildIndex)
  return sFin

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

/-- Report any runtime warnings a trigger or its synced transitions raised (005.11, `CHR109`). -/
def triggerWarnings (info : TransInfo) (fuel : Nat) : List Output :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    info.warnings.map Output.diag ++ info.syncs.flatMap (triggerWarnings · fuel)

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
        | .occurred => do
          let now ← getTime
          match ← lookupState (.prod [te], "$occ") with
          | some i => pure (i.live now)
          | none => pure false
        | .lawful => isEnabled M.fuel te
        | .valid => isValid M.fuel te
        | .violated => isViolated M.fuel te
        | .late => isLate M.fuel te
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
    | .create xs t => effect ctx (.cAll xs t none xs)
    | .terminate xs t => effect ctx (.tAll xs t xs)
    | .obfuscate xs t => effect ctx (.oAll xs t xs)
    | .submitEvidence pol xs t src => effect ctx (.evOp (if pol then .support else .rebut) xs t (.named src))
    | .retractEvidence xs t src => effect ctx (.evOp .retract xs t (.named src))
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
        let outs := infos.flatMap fun i => Output.executed i :: triggerViolations i 1000 ++ triggerWarnings i 1000
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
    | .ok pairs =>
      let stores := pairs.map (·.1)
      let warns := (pairs.flatMap (·.2)).map Output.diag
      (some (Store.unions stores), warns)

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
    let ctx' := Ctx.ofBothIdx effSpec effSpecIdx state' state'.buildIndex effSpec.hasEpistemicOrDefeasible (some effSpec.allImmunities)
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ctx' []
    let violatedNow : Except RuntimeError (List Tagged) :=
      duties.filterMapM fun te => do
        let vconds := match effSpecIdx.lookup te.2 with
          | some ({ kind := .duty ds, .. }, _, _) => some ds.violatedWhen
          | _ => none
        let r ← run (ignoreMissingInput (evalViolationCondition M.fuel te vconds))
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
