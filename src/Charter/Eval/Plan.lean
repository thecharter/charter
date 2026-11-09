import Charter.Eval.Step

/-!
# Charter.Eval.Plan — Operator-Blind Input Schema, Missing-Input Inspection (`#68`), & Backward-Chaining Planner (`#70`)

Shared by both the `charter` CLI (`charter inputs`, `charter plan`) and `charter-server`
(`GetInputSchema`, `InspectInputs`, `Plan`) with zero `Charter.Surface`, `Charter.Resolve`,
or `Charter.Prove` imports (`Law 9`, `test/gates/operator-blind.sh`).
-/

namespace Charter.Plan

open M

/-- Schema description of one component parameter of an open or evidenced fact (`#68`). -/
structure ComponentSchema where
  paramName : String
  domName   : DomId
  domKind   : String
  choices   : List String := []
  deriving Repr, Inhabited

/-- Schema description of an open or evidenced fact type for building client input forms (`#68`). -/
structure InputTypeSchema where
  name         : DomId
  inputKind    : String -- "open" | "evidenced"
  components   : List ComponentSchema := []
  confidential : Bool := false
  audiences    : List String := []
  deriving Repr, Inhabited

def describeDomain (spec : Spec) (_domName : DomId) (dom : Domain) : String × List String :=
  match dom with
  | .strings ss => ("enum", ss)
  | .ints ns => ("int-enum", ns.map toString)
  | .anyString => ("string", [])
  | .anyInt => ("int", [])
  | .time => ("time", [])
  | .duration => ("duration", [])
  | .money cur sc => ("money:" ++ cur ++ ":" ++ toString sc, [])
  | .quantity u => ("quantity:" ++ u, [])
  | .rate => ("rate", [])
  | .products xs =>
    ("product", xs.map fun x => spec.removeDecoration x)

/-- Extract the form-ready schema of all open (`Open`/`Input`) and `Evidenced` fact types in `spec` (`#68`).
When `spec.serviceInterfaceDeclared` is `true` (`#67`), restricts to `spec.exposedInputs`. -/
def extractInputSchemas (spec : Spec) : List InputTypeSchema :=
  spec.decls.reverse.filterMap fun (d, ts) =>
    if d == "int" || d == "string" || d == "actor" || (d.toList.head? == some '_') then none
    else if spec.serviceInterfaceDeclared && !spec.exposedInputs.contains d then none
    else
      match ts.kind with
      | .fact fs =>
        let isOpenInput := (!ts.isClosed || fs.isInput) && !fs.evidenced
        if !isOpenInput && !fs.evidenced then none
        else
          let comps : List ComponentSchema := match ts.domain with
            | .products xs =>
              xs.map fun v =>
                let cDom := spec.removeDecoration v
                let baseDom := match spec.findDecl cDom with
                  | some cts => cts.domain
                  | none => .anyString
                let (dk, chs) := describeDomain spec cDom baseDom
                { paramName := toString v, domName := cDom, domKind := dk, choices := chs }
            | otherDom =>
              let (dk, chs) := describeDomain spec d otherDom
              [{ paramName := d, domName := d, domKind := dk, choices := chs }]
          some {
            name := d
            inputKind := if fs.evidenced then "evidenced" else "open"
            components := comps
            confidential := fs.confidential
            audiences := fs.audiences
          }
      | _ => none

/-- Open facts and unresolved evidence an act instance's evaluation depends on (`#68`). -/
structure MissingActInputs where
  subject       : String
  openFacts     : List String := []
  openDomains   : List DomId := []
  unmetEvidence : List (String × EvidenceStatus) := []
  deriving Repr, Inhabited

mutual
def collectTermApps : Term → List (DomId × Args)
  | .app d args => (d, args) :: collectArgsApps args
  | .fnApp d k => (d, .pos [k]) :: collectTermApps k
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .project a _ | .tag a _ | .untag a | .doneAt a | .stampOf a | .overdueOf a | .calOp1 _ a =>
    collectTermApps a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    collectTermApps a ++ collectTermApps b
  | .mulDivRound x n d _ | .ite x n d =>
    collectTermApps x ++ collectTermApps n ++ collectTermApps d
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t =>
    collectTermApps t
  | .boolLit _ | .intLit _ | .stringLit _ | .ref _ | .currentTime | .dimLit _ _ => []

def collectArgsApps : Args → List (DomId × Args)
  | .pos ts => collectListApps ts
  | .named ms => collectModApps ms

def collectListApps : List Term → List (DomId × Args)
  | [] => []
  | t :: ts => collectTermApps t ++ collectListApps ts

def collectModApps : List (Var × Term) → List (DomId × Args)
  | [] => []
  | (_, t) :: ms => collectTermApps t ++ collectModApps ms
end

mutual
def collectRefDoms (spec : Spec) : Term → List DomId
  | .ref v => [spec.removeDecoration v]
  | .exists_ xs u | .forall_ xs u | .count xs u | .sum xs u | .max xs u | .min xs u =>
    xs.map (spec.removeDecoration) ++ collectRefDoms spec u
  | .app d args => spec.chaseAlias d :: collectArgsDoms spec args
  | .fnApp d k => spec.chaseAlias d :: collectRefDoms spec k
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .project a _ | .tag a _ | .untag a | .doneAt a | .stampOf a | .overdueOf a | .calOp1 _ a =>
    collectRefDoms spec a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    collectRefDoms spec a ++ collectRefDoms spec b
  | .mulDivRound x n d _ | .ite x n d =>
    collectRefDoms spec x ++ collectRefDoms spec n ++ collectRefDoms spec d
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime | .dimLit _ _ => []

def collectArgsDoms (spec : Spec) : Args → List DomId
  | .pos ts => collectListDoms spec ts
  | .named ms => collectModDoms spec ms

def collectListDoms (spec : Spec) : List Term → List DomId
  | [] => []
  | t :: ts => collectRefDoms spec t ++ collectListDoms spec ts

def collectModDoms (spec : Spec) : List (Var × Term) → List DomId
  | [] => []
  | (_, t) :: ms => collectRefDoms spec t ++ collectModDoms spec ms
end

/-- Inspect all unassigned open fact instances/domains and unresolved `Evidenced` facts
that `targetTe`'s lawfulness and validity depend on in `cfg` (`#68`). -/
def inspectMissingInputs (cfg : Config) (targetTe : Tagged) : MissingActInputs := Id.run do
  let spec := cfg.spec
  let specIdx := spec.buildIndex
  let ctx := Ctx.ofIdx spec specIdx cfg.state
  let mut openFacts : List String := []
  let mut openDoms : List DomId := []
  let mut unmetEv : List (String × EvidenceStatus) := []

  -- 1. Direct evaluation of `evalActTri` (catches first `missingInput` or returns `unmetEvidence`)
  match (evalActTri M.fuel targetTe).run ctx [] with
  | .error (.missingInput (.assignments unknowns)) =>
    for te in unknowns do
      if !openFacts.contains te.pp then openFacts := openFacts ++ [te.pp]
      if !openDoms.contains te.2 then openDoms := openDoms ++ [te.2]
  | .error (.missingInput (.instances d))
  | .error (.missingInput (.unassignedVar d))
  | .error (.missingInput (.unassignedFunction d _)) =>
    if !openDoms.contains d then openDoms := openDoms ++ [d]
  | .ok ((_, _, us) :: _) =>
    for (uTe, st) in us do
      if !unmetEv.any (·.1 == uTe.pp) then
        unmetEv := unmetEv ++ [(uTe.pp, st)]
  | _ => pure ()

  -- Also run `ignoreMissingInput` when a `missingInput` interrupted `evalActTri` so `unmetEvidence` is still gathered
  if unmetEv.isEmpty then
    match (ignoreMissingInput (evalActTri M.fuel targetTe)).run ctx [] with
    | .ok ((_, _, us) :: _) =>
      for (uTe, st) in us do
        if !unmetEv.any (·.1 == uTe.pp) then
          unmetEv := unmetEv ++ [(uTe.pp, st)]
    | _ => pure ()

  -- 2. Scan all guard terms of `targetTe` (and applicable immunities) for unassigned open facts
  if let some tspec := spec.findDecl targetTe.2 then
    let binds := Tagged.bindings tspec.domain targetTe
    let hwTerms := tspec.derivation.filterMap fun | .holdsWhen c => some c | _ => none
    let valTerms := match tspec.kind with | .act a => a.validWhen | _ => []
    let immTerms := (spec.immunitiesAgainst targetTe.2 ++ spec.protectionsFor targetTe.2).flatMap fun (_, imTs, imS) =>
      (imTs.derivation.filterMap fun | .holdsWhen c => some c | _ => none) ++ imS.unlessConds
    let allGuardTerms := hwTerms ++ tspec.conditions ++ valTerms ++ immTerms
    for (appDom, appArgs) in allGuardTerms.flatMap collectTermApps do
      let realD := spec.chaseAlias appDom
      if let some dTs := spec.findDecl realD then
        if !dTs.isClosed && !dTs.isEvidencedFact then
          if !openDoms.contains realD then openDoms := openDoms ++ [realD]
          match (ignoreMissingInput (whenTagged (eval M.fuel (.app realD appArgs)) pure)).run ctx binds with
          | .ok cands =>
            for candTe in cands do
              if (cfg.state.lookup candTe).isNone && !openFacts.contains candTe.pp then
                openFacts := openFacts ++ [candTe.pp]
          | .error _ => pure ()
        else if dTs.isEvidencedFact then
          match (ignoreMissingInput (whenTagged (eval M.fuel (.app realD appArgs)) pure)).run ctx binds with
          | .ok cands =>
            for candTe in cands do
              let st := cfg.state.evidenceStatus candTe
              if st != .established && st != .refuted && !unmetEv.any (·.1 == candTe.pp) then
                unmetEv := unmetEv ++ [(candTe.pp, st)]
          | .error _ => pure ()
    for refD in allGuardTerms.flatMap (collectRefDoms spec) do
      if let some rTs := spec.findDecl refD then
        if !rTs.isClosed && !rTs.isEvidencedFact && !openDoms.contains refD then
          let trues := cfg.state.contents.filter (fun (te, _) => te.2 == refD && te.1 != .prod [])
          if trues.isEmpty then openDoms := openDoms ++ [refD]

  return {
    subject := targetTe.pp
    openFacts
    openDomains := openDoms
    unmetEvidence := unmetEv
  }

/-! ## Backward-Chaining Goal Planner (`#70`) -/

inductive PlanStep where
  | act (actor : String) (te : Tagged)
  | wait (targetTime : Int) (delta : Int)
  deriving Repr, Inhabited

def PlanStep.render : PlanStep → String
  | .act actor te =>
    if actor.isEmpty then te.pp
    else te.pp ++ "  [actor: " ++ actor ++ "]"
  | .wait targetTime delta =>
    "@ " ++ toString targetTime ++ "  [wait +" ++ toString delta ++ "]"

inductive PlanResult where
  | alreadyEnabled
  | found (steps : List PlanStep) (visited : Nat)
  | unreachable (visited : Nat) (maxDepth : Nat)
  deriving Repr, Inhabited

def extractActorOfTagged : Tagged → String
  | (.prod ((.str s, _) :: _), _) => s
  | (.prod ((.int n, _) :: _), _) => toString n
  | _ => ""

def isGoalLawfulAndValid (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) (te : Tagged) : Bool :=
  let ctx := Ctx.ofIdx spec specIdx state
  match (ignoreMissingInput (evalActTri M.fuel te)).run ctx [] with
  | .ok ((.yes, .yes, _) :: _) => true
  | _ => false

partial def elemLeaves : Elem → List Elem
  | .prod xs => xs.flatMap (fun p => elemLeaves p.1)
  | e => [e]

def stateCandidateElems (s : State) (dom : Domain) : List Elem :=
  let leaves := s.holdsList.flatMap (fun te => elemLeaves te.1)
  let baseInts : List Elem := [.int 0, .int 1, .int 10, .int 50, .int 100]
  let fromState := leaves.filter fun e => match dom, e with
    | .anyInt, .int _ | .time, .int _ | .duration, .int _ | .money _ _, .int _ | .quantity _, .int _ => true
    | .anyString, .str _ => true
    | _, _ => false
  let seed := match dom with
    | .anyInt | .time | .duration | .money _ _ | .quantity _ => fromState ++ baseInts
    | _ => fromState
  seed.foldl (fun acc e => if acc.any (Elem.beq e) then acc else acc ++ [e]) []

def scopePlanBinders (menu : List (DomId × List Elem)) : Nat → List Var → M Tagged → M Tagged
  | 0, _, _ => empty
  | _, [], m => m
  | fuel + 1, x :: xs, m => do
    let spec ← getSpec
    let state ← getState
    let d := spec.removeDecoration x
    let openDom? : Option Domain := match spec.findDecl d with
      | some t => match t.domain with
        | .anyInt | .anyString | .time | .duration | .money _ _ | .quantity _ => some t.domain
        | _ => none
      | none => none
    let te ← match openDom? with
      | none => everyValidSubs fuel x
      | some dom =>
        let vals := match menu.find? (·.1 == d) with
          | some (_, vs) => vs
          | none => stateCandidateElems state dom
        let cand ← nd (vals.map fun e => ((e, d) : Tagged))
        if ← isValidInstance fuel cand then pure cand else empty
    bindVar x te (scopePlanBinders menu fuel xs m)

/-- All currently lawful **and** valid act instances in `cfg` (`#70`). -/
def lawfulValidActs (menu : List (DomId × List Elem)) (cfg : Config) (specIdx : Spec.SpecIndex) : List Tagged :=
  let spec := cfg.spec
  let ctx := Ctx.ofIdx spec specIdx cfg.state
  let actIds := spec.decls.reverse.filterMap fun (d, ts) =>
    match ts.kind with
    | .act _ =>
      if spec.serviceInterfaceDeclared && !spec.exposedActs.contains d then none
      else some d
    | _ => none
  actIds.flatMap fun d =>
    let xs := spec.components d
    let body : M Tagged := whenTagged (eval M.fuel (.app d (.named []))) pure
    let genM : M (List Tagged) := results (scopePlanBinders menu M.fuel xs body)
    match (ignoreMissingInput genM).run ctx [] with
    | .error _ => []
    | .ok lists =>
      lists.flatten.filter fun te =>
        isGoalLawfulAndValid spec specIdx cfg.state te

mutual
def collectIntConsts : Term → List Int
  | .intLit n => if n > 0 then [n] else []
  | .dimLit _ n => if n > 0 then [n] else []
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .project a _ | .tag a _ | .untag a | .doneAt a | .stampOf a | .overdueOf a | .calOp1 _ a =>
    collectIntConsts a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    collectIntConsts a ++ collectIntConsts b
  | .mulDivRound x n d _ | .ite x n d =>
    collectIntConsts x ++ collectIntConsts n ++ collectIntConsts d
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t =>
    collectIntConsts t
  | .app _ (.pos ts) => collectIntConstsList ts
  | .app _ (.named ms) => collectIntConstsMods ms
  | .fnApp _ k => collectIntConsts k
  | .boolLit _ | .stringLit _ | .ref _ | .currentTime => []

def collectIntConstsList : List Term → List Int
  | [] => []
  | t :: ts => collectIntConsts t ++ collectIntConstsList ts

def collectIntConstsMods : List (Var × Term) → List Int
  | [] => []
  | (_, t) :: ms => collectIntConsts t ++ collectIntConstsMods ms
end

/-- Extract exact candidate future timestamps where a timelock, holding window, or expiry flips (`#70`). -/
def candidateWaitTargets (cfg : Config) : List Int :=
  let now := cfg.state.time
  let paramDurs : List Int := cfg.state.holdsList.filterMap fun te =>
    match cfg.spec.findDecl te.2, te.1 with
    | some { restriction := some .var, .. }, .int k => if k > 0 && k <= 100000 then some k else none
    | _, _ => none
  let specConsts : List Int := cfg.spec.decls.flatMap fun (_, ts) =>
    let dC := ts.derivation.flatMap fun
      | .holdsWhen tm | .dv _ tm => collectIntConsts tm
      | .defeasibleDAG _ rs => rs.flatMap (fun r => collectIntConsts r.cond)
    let cC := ts.conditions.flatMap collectIntConsts
    let vC := match ts.kind with | .act a => a.validWhen.flatMap collectIntConsts | _ => []
    dC ++ cC ++ vC
  let durs := (1 :: (paramDurs ++ specConsts)).eraseDups
  let liveStamps := (now :: cfg.state.contents.filterMap fun (_, i) =>
    if i.live now then some i.since else none).eraseDups
  let expiries := cfg.state.contents.filterMap fun (_, i) =>
    match i.expiry with
    | some exp => if exp > now then some exp else none
    | none => none
  let rawTargets :=
    (liveStamps.flatMap fun st => durs.filterMap fun d =>
      let t := st + d
      if t > now then some t else none) ++
    (specConsts.filter (· > now)) ++
    expiries
  let dedup := rawTargets.eraseDups
  let sorted := (dedup.toArray.qsort (· < ·)).toList
  sorted.take 6

def planStateKey (c : Config) : String :=
  let names := c.state.holdsList.map Tagged.pp
  let sorted := (names.toArray.qsort (· < ·)).toList
  toString c.lawVersion ++ "@" ++ toString c.state.time ++ "|" ++ String.intercalate "|" sorted

def stepAct (c : Config) (specIdx : Spec.SpecIndex) (te : Tagged) : Option (Config × Spec.SpecIndex) :=
  let (c', outs) := evalCompiledStep c (.trigger [] (.tag (.boolLit true) te.2)) false
  let _ := (c', outs)
  let ctx := Ctx.ofIdx c.spec specIdx c.state
  match (instantiateTrans M.fuel [] te).run ctx [] with
  | .error _ => none
  | .ok infos =>
    let store := Store.unions (infos.map (·.assignments))
    let state1 := State.makeAssignments c.spec store { c.state with step := c.state.step + 1 }
    let (cfg'?, _) := Interp.newContext c c.spec specIdx c.strata state1
    match cfg'? with
    | none => none
    | some cfg' =>
      let nextIdx := if cfg'.lawVersion != c.lawVersion then cfg'.spec.buildIndex else specIdx
      some (cfg', nextIdx)

def stepWait (c : Config) (specIdx : Spec.SpecIndex) (newTime : Int) : Option Config :=
  if newTime <= c.state.time then none
  else
    let state0 := { c.state with time := newTime, step := c.state.step + 1 }
    let (cfg'?, _) := Interp.newContext c c.spec specIdx c.strata state0
    cfg'?

/-- Breadth-first search for a shortest sequence of lawful+valid acts and clock waits
after which `targetTe` is both lawful and valid (`#70`). -/
def findShortestPlan (cfg : Config) (targetTe : Tagged)
    (maxDepth : Nat := 5) (maxStates : Nat := 600)
    (menu : List (DomId × List Elem) := []) : PlanResult := Id.run do
  let initIdx := cfg.spec.buildIndex
  if isGoalLawfulAndValid cfg.spec initIdx cfg.state targetTe then
    return .alreadyEnabled
  if maxDepth == 0 then
    return .unreachable 1 0

  let mut seen : List String := [planStateKey cfg]
  let mut frontier : List (Config × Spec.SpecIndex × List PlanStep) := [(cfg, initIdx, [])]

  for _ in [0 : maxDepth] do
    if frontier.isEmpty || seen.length >= maxStates then
      return .unreachable seen.length maxDepth
    let mut nextFrontier : List (Config × Spec.SpecIndex × List PlanStep) := []
    for (curCfg, curIdx, trace) in frontier do
      if seen.length < maxStates then
        -- 1. Try every currently lawful and valid act
        for candTe in lawfulValidActs menu curCfg curIdx do
          if seen.length < maxStates then
            if let some (c', idx') := stepAct curCfg curIdx candTe then
              let stepRec := PlanStep.act (extractActorOfTagged candTe) candTe
              let trace' := trace ++ [stepRec]
              if isGoalLawfulAndValid c'.spec idx' c'.state targetTe then
                return .found trace' (seen.length + 1)
              let k := planStateKey c'
              if !seen.contains k then
                seen := k :: seen
                nextFrontier := nextFrontier ++ [(c', idx', trace')]
        -- 2. Try exact clock threshold advances
        for targetT in candidateWaitTargets curCfg do
          if seen.length < maxStates then
            if let some c' := stepWait curCfg curIdx targetT then
              let stepRec := PlanStep.wait targetT (targetT - curCfg.state.time)
              let trace' := trace ++ [stepRec]
              if isGoalLawfulAndValid c'.spec curIdx c'.state targetTe then
                return .found trace' (seen.length + 1)
              let k := planStateKey c'
              if !seen.contains k then
                seen := k :: seen
                nextFrontier := nextFrontier ++ [(c', curIdx, trace')]
    frontier := nextFrontier

  return .unreachable seen.length maxDepth

end Charter.Plan
