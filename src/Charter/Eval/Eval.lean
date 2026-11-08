import Charter.Core.State
import Charter.Core.Amend

/-!
# Charter.Eval.Eval — The evaluator of terms, instances, and triggers

eFLINT's `Eval.hs`, per D2, as one set of mutually recursive definitions with
explicit fuel (no `partial`). Evaluation is nondeterministic: a term with free
variables denotes every value it takes under every binding of those variables
to instances, so the monad `M` returns a list of results or a `RuntimeError`.

Eval owns the state and the three answers (AGENTS.md, "One owner per fact"):
what holds (`isHolds`), what is enabled (`isEnabled`, eFLINT's lawfulness),
what is violated (`isViolated`), and what a trigger does (`instantiateTrans`).
Nothing here reconstructs a fact from text; every term it runs is in the checked
form `Charter.Resolve` produces.
-/

namespace Charter

/-- Variable bindings, right-biased (`bindVar` overrides an earlier binding). -/
abbrev Subs := List (Var × Tagged)

structure Ctx where
  spec     : Spec
  state    : State
  specIdx  : Spec.SpecIndex := .empty
  stateIdx : State.StateIndex := .empty
  indexed  : Bool := false

namespace Ctx

def ofIdx (spec : Spec) (specIdx : Spec.SpecIndex) (state : State) : Ctx :=
  { spec, state, specIdx, stateIdx := state.buildIndex, indexed := true }

def of (spec : Spec) (state : State) : Ctx :=
  ofIdx spec spec.buildIndex state

end Ctx

/-- The evaluation monad: a context and bindings in, a list of results or an error out. -/
structure M (α : Type) where
  run : Ctx → Subs → Except RuntimeError (List α)

namespace M

instance : Monad M where
  pure a := ⟨fun _ _ => .ok [a]⟩
  bind m f := ⟨fun c s => do
    let as ← m.run c s
    let bss ← as.mapM (fun a => (f a).run c s)
    pure bss.flatten⟩

def err {α} (e : RuntimeError) : M α := ⟨fun _ _ => .error e⟩

def nd {α} (xs : List α) : M α := ⟨fun _ _ => .ok xs⟩

def empty {α} : M α := nd []

/-- Collect every result of `m` as one list. -/
def results {α} (m : M α) : M (List α) := ⟨fun c s => (m.run c s).map (fun xs => [xs])⟩

def alt {α} (m1 m2 : M α) : M α := ⟨fun c s => do let xs ← m1.run c s; let ys ← m2.run c s; pure (xs ++ ys)⟩

def ignoreMissingInput {α} (m : M α) : M α := ⟨fun c s => match m.run c s with
  | .error (.missingInput _) => .ok []
  | r => r⟩

def getCtx : M Ctx := ⟨fun c _ => .ok [c]⟩
def getSpec : M Spec := ⟨fun c _ => .ok [c.spec]⟩
def getState : M State := ⟨fun c _ => .ok [c.state]⟩
def getSubs : M Subs := ⟨fun _ s => .ok [s]⟩
def getTime : M Int := ⟨fun c _ => .ok [c.state.time]⟩

def bindVar {α} (x : Var) (te : Tagged) (m : M α) : M α :=
  ⟨fun c s => m.run c ((x, te) :: s.filter (fun p => p.1 != x))⟩

/-- Extend the bindings with `extra`, which override (eFLINT `subsUnion`, right-biased). -/
def withSubs {α} (extra : List (Var × Tagged)) (m : M α) : M α :=
  ⟨fun c s => m.run c (extra ++ s.filter (fun p => !(extra.any (fun q => q.1 == p.1))))⟩

def whenBool {α} (m : M Value) (f : Bool → M α) : M α := do
  match ← m with
  | .bool b => f b
  | _ => empty

def whenInt {α} (m : M Value) (f : Int → M α) : M α := do
  match ← m with
  | .int i => f i
  | _ => empty

def whenTagged {α} (m : M Value) (f : Tagged → M α) : M α := do
  match ← m with
  | .tagged te => f te
  | _ => empty

def checkTrue (m : M Value) : M Unit := do
  match ← m with
  | .bool true => pure ()
  | _ => empty

def checkFalse (m : M Value) : M Unit := do
  match ← m with
  | .bool false => pure ()
  | _ => empty

def getTypeEntry (d : DomId) : M (TypeSpec × Bool × Option (List Term)) := ⟨fun c _ =>
  if c.indexed then
    match c.specIdx.lookup d with
    | some entry => .ok [entry]
    | none => .error (.undeclaredType d)
  else
    match c.spec.findDecl d with
    | some t => .ok [(t, c.spec.enumerable t.domain, c.spec.judgedRule d)]
    | none => .error (.undeclaredType d)⟩

def getTypeSpec (d : DomId) : M TypeSpec := (·.1) <$> getTypeEntry d

def getDom (d : DomId) : M (Domain × Term) :=
  (fun (t, _, _) => (t.domain, t.domainConstraint)) <$> getTypeEntry d

def lookupState (te : Tagged) : M (Option Info) := ⟨fun c _ =>
  if c.indexed then
    let bucket := (c.stateIdx.lookup te.2).getD []
    .ok [(bucket.find? (·.1 == te)).map (·.2)]
  else .ok [c.state.lookup te]⟩

def trueInstancesOf (d : DomId) : M (List Tagged) := ⟨fun c _ =>
  if c.indexed then
    let now := c.state.time
    let bucket := (c.stateIdx.lookup d).getD []
    .ok [bucket.filterMap fun (te, i) => if i.value && i.live now then some te else none]
  else .ok [c.state.trueInstances d]⟩

def assignedInstancesOf (d : DomId) : M (List Tagged × List Tagged) := ⟨fun c _ =>
  if c.indexed then
    let now := c.state.time
    let bucket := (c.stateIdx.lookup d).getD []
    .ok [(bucket.filterMap fun (te, i) => if i.live now then some te else none,
          bucket.filterMap fun (te, i) => if !(i.live now) then some te else none)]
  else .ok [c.state.assignedInstances d]⟩

def lookupEvidenceStatus (te : Tagged) : M EvidenceStatus := ⟨fun c _ =>
  if c.indexed then
    let direct? := ((c.stateIdx.lookup te.2).getD []).find? (·.1 == te) |>.map (·.2)
    let posB := (c.stateIdx.lookup evFindingPosDom).getD []
    let negB := (c.stateIdx.lookup evFindingNegDom).getD []
    let supB := (c.stateIdx.lookup evSupportDom).getD []
    let rebB := (c.stateIdx.lookup evRebutDom).getD []
    .ok [State.evidenceStatusFromBuckets c.state.time te direct? posB negB supB rebB]
  else .ok [c.state.evidenceStatus te]⟩

def lookupNormativeConflict (te : Tagged) : M (Option (String × String)) := ⟨fun c _ =>
  if c.indexed then
    let bucket := (c.stateIdx.lookup defConflictDom).getD []
    .ok [State.conflictFromBucket c.state.time te bucket]
  else .ok [c.state.conflictOf te]⟩

def candidatesFromEvidenceOf (d : DomId) : M (List Tagged) := ⟨fun c _ =>
  let now := c.state.time
  let extract (bucket : List (Tagged × Info)) : List Tagged :=
    bucket.filterMap fun (entryTe, i) =>
      if i.live now then
        match entryTe.1 with
        | .prod [targetTe, _] => if targetTe.2 == d then some targetTe else none
        | _ => none
      else none
  let posB := if c.indexed then (c.stateIdx.lookup evFindingPosDom).getD [] else c.state.contents.filter (·.1.2 == evFindingPosDom)
  let supB := if c.indexed then (c.stateIdx.lookup evSupportDom).getD [] else c.state.contents.filter (·.1.2 == evSupportDom)
  let direct := if c.indexed then
    ((c.stateIdx.lookup d).getD []).filterMap fun (te, i) => if i.live now then some te else none
  else c.state.trueInstances d
  let raw := direct ++ extract posB ++ extract supB
  let dedup := raw.foldl (fun acc te => if acc.any (· == te) then acc else acc ++ [te]) []
  .ok [dedup]⟩

def dedupUnmet (xs : List (Tagged × EvidenceStatus)) : List (Tagged × EvidenceStatus) :=
  xs.foldl (fun acc p => if acc.any (fun q => q.1 == p.1 && q.2 == p.2) then acc else acc ++ [p]) []

def substituteVar (x : Var) : M Tagged := do
  let spec ← getSpec
  match (← getSubs).find? (fun p => p.1 == x) with
  | some (_, (v, _)) => pure (v, spec.removeDecoration x)
  | none => err (.missingSubstitution x)

def tagValue (v : Value) (d : DomId) : M Value :=
  match v with
  | .int i => pure (.tagged (.int i, d))
  | .str s => pure (.tagged (.str s, d))
  | .tagged (e, _) => pure (.tagged (e, d))
  | .bool _ => empty

def untagValue (v : Value) : M Value :=
  match v with
  | .tagged (.int i, _) => pure (.int i)
  | .tagged (.str s, _) => pure (.str s)
  | _ => empty

/-- The merged store and whether any synced transition was forced (eFLINT `syncTransInfos`). -/
def syncTransInfos (infos : List TransInfo) : Store × Bool :=
  infos.foldr (fun i (st, f) => (Store.union i.assignments st, i.forced || f)) ([], false)

def indexOf (x : Var) (rs : List Var) : Option Nat :=
  let rec go : List Var → Nat → Option Nat
    | [], _ => none
    | r :: rs, k => if r == x then some k else go rs (k + 1)
  go rs 0

/-- Bind each variable in turn with `bind` and run `m` (eFLINT `foreach`). Outside the
evaluator's mutual block so that the block stays polymorphism-free and structurally
recursive on its fuel: the kernel can then unfold it (`prove`, 013.4). -/
def scopeWith {α} (bind : Var → M Tagged) : List Var → M α → M α
  | [], m => m
  | x :: xs, m => do
    let te ← bind x
    bindVar x te (scopeWith bind xs m)

def foreachWith {α} (bind : Var → M Tagged) (xs : List Var) (m : M α) : M (List α) :=
  results (scopeWith bind xs m)

/-- Whether `t` is a bare mention of `d` (`Terminates v` / `Obfuscates v` clearing `v` itself). -/
def isBareClearTerm (spec : Spec) (d : DomId) : Term → Bool
  | .ref y => spec.removeDecoration y == d
  | .app d' (.named []) => spec.chaseAlias d' == d
  | .app d' (.pos []) => spec.chaseAlias d' == d
  | _ => false

/-- Extract `(v, k)` when `t` is `v.k` (possibly wrapped in `.untag`). -/
def matchProjectRef : Term → Option (Var × Var)
  | .project (.ref v) k => some (v, k)
  | .untag (.project (.ref v) k) => some (v, k)
  | _ => none

/-- Find `fVar.kVar == keyTerm` or `keyTerm == fVar.kVar` in an effect's `When` guards (`D32`). -/
def findFnKeyTerm (fVar kVar : Var) : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, t =>
    match t with
    | .when body cond =>
      (findFnKeyTerm fVar kVar fuel cond).orElse (fun _ => findFnKeyTerm fVar kVar fuel body)
    | .and a b =>
      (findFnKeyTerm fVar kVar fuel a).orElse (fun _ => findFnKeyTerm fVar kVar fuel b)
    | .eq lhs rhs =>
      match matchProjectRef lhs with
      | some (v, k) => if v == fVar && k == kVar then some rhs else none
      | none =>
        match matchProjectRef rhs with
        | some (v, k) => if v == fVar && k == kVar then some lhs else none
        | none => none
    | _ => none

mutual

/-- Every element of a domain (eFLINT `instantiate_domain`). -/
def instantiateDomain : Nat → DomId → Domain → M Elem
  | 0, _, _ => err (.fuelExhausted "enumerating a domain")
  | fuel + 1, d, dom => do
    match dom with
    | .time => let t ← getTime; nd ((List.range (t.toNat + 1)).map (fun (k : Nat) => Elem.int (k : Int)))
    | .anyString => err (.enumerateInfiniteDomain d)
    | .anyInt => err (.enumerateInfiniteDomain d)
    | .duration => err (.enumerateInfiniteDomain d)
    | .money _ _ => err (.enumerateInfiniteDomain d)
    | .quantity _ => err (.enumerateInfiniteDomain d)
    | .strings ss => nd (ss.map .str)
    | .ints is => nd (is.map .int)
    | .products xs => do
      let args ← xs.mapM (everyValidSubs fuel)
      pure (.prod args)
termination_by structural n => n

/-- Every instance a variable may be bound to: all elements of an enumerable
domain that pass the domain constraint, or the instances known to hold of a
non-enumerable one (eFLINT `every_valid_subs`). -/
def everyValidSubs : Nat → Var → M Tagged
  | 0, _ => err (.fuelExhausted "binding a variable")
  | fuel + 1, x => do
    let spec ← getSpec
    let d := spec.removeDecoration x
    let (tspec, isEnum, _) ← getTypeEntry d
    let dom := tspec.domain
    let filter := tspec.domainConstraint
    if isEnum then
      let e ← instantiateDomain fuel d dom
      let te : Tagged := (e, d)
      if filter.isTrueLit then pure te
      else do
        withSubs (Tagged.bindings dom te) (checkTrue (eval fuel filter))
        pure te
    else
      if tspec.isEvidencedFact then
        let cands ← candidatesFromEvidenceOf d
        let est ← cands.filterM fun te => do
          let st ← lookupEvidenceStatus te
          pure (st == .established)
        nd est
      else if !tspec.isClosed then
        let (trues, falses) ← assignedInstancesOf d
        if trues.isEmpty && falses.isEmpty then err (.missingInput (.instances d)) else nd trues
      else
        let trues ← trueInstancesOf d
        nd trues
termination_by structural n => n

/-- Whether an instance is well-formed: in its domain and passing the constraint. -/
def isValidInstance : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "checking an instance")
  | fuel + 1, te => do
    let (dom, filter) ← getDom te.2
    let check : M Bool :=
      if filter.isTrueLit then pure true
      else withSubs (Tagged.bindings dom te) (whenBool (eval fuel filter) pure)
    match te.1, dom with
    | .int i, .ints is => if is.contains i then check else pure false
    | .int _, .anyInt => check
    | .int _, .time => check
    | .int _, .duration => check
    | .int _, .money _ _ => check
    | .int _, .quantity _ => check
    | .str s, .strings ss => if ss.contains s then check else pure false
    | .str _, .anyString => check
    | .prod args, .products params =>
      if args.length == params.length then
        let oks ← args.mapM (isValidInstance fuel)
        if oks.all id then check else pure false
      else pure false
    | _, _ => pure false
termination_by structural n => n

/-- Whether the `Conditioned by` conditions of an instance's type hold for it. -/
def satConditions : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "checking conditions")
  | fuel + 1, te => do
    if !(← isValidInstance fuel te) then pure false
    else
      let tspec ← getTypeSpec te.2
      if tspec.conditions.isEmpty then pure true
      else
        withSubs (Tagged.bindings tspec.domain te) do
          let bs ← tspec.conditions.mapM (fun c => whenBool (eval fuel c) pure)
          pure (bs.all id)
termination_by structural n => n

/-- Whether an instance holds (eFLINT `is_holds`): its assignment, or false for a
closed type, or missing input for an open one. -/
def isHolds : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an instance holds")
  | fuel + 1, te => do
    if !(← isValidInstance fuel te) then pure false
    else
      let (tspec, _, judged) ← getTypeEntry te.2
      if tspec.isEvidencedFact then
        let st ← lookupEvidenceStatus te
        match st, tspec.factPresumed with
        | .established, _ => pure true
        | .unresolved, some b => pure b
        | _, _ => pure false
      else
        let now ← getTime
        match ← lookupState te with
        | some i => pure (i.live now)
        | none =>
          match judged with
          | some clauses =>
            -- D15 (brief B11): an act or immunity whose domain is not enumerable is judged
            -- for the instance asked about; its `Holds when` is read with the components bound,
            -- as saturation would have read it had the domain been finite (004.1, 005.5).
            withSubs (Tagged.bindings tspec.domain te) do
              let rs ← results (do let c ← nd clauses; whenBool (eval fuel c) pure)
              if rs.any id then satConditions fuel te else pure false
          | none =>
            if !tspec.isClosed then err (.missingInput (.assignments [te]))
            else pure false
termination_by structural n => n

/-- Whether an act or event instance is enabled: it holds, its conditions hold,
and no transition it syncs with is forced (eFLINT `is_enabled`). Charter's
`Except under a₁, a₂` (plan §2.2.4) replaces this: the act is lawful iff some
instance of a named act sharing its bound components is enabled and valid. -/
def isEnabled : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an act is enabled")
  | fuel + 1, te => do
    let spec ← getSpec
    let tspec ← getTypeSpec te.2
    match tspec.kind with
    | .act a =>
      if !a.exceptUnder.isEmpty then
        withSubs (Tagged.bindings tspec.domain te) do
          let subs ← getSubs
          let rs ← a.exceptUnder.mapM fun d' => do
            let free := (spec.components d').filter (fun x => !(subs.any (fun p => p.1 == x)))
            let insts ← results (scopeWith (everyValidSubs fuel) free (whenTagged (eval fuel (.app d' (.named []))) pure))
            let oks ← insts.mapM fun inst => do
              if ← isEnabled fuel inst then isValid fuel inst else pure false
            pure (oks.any id)
          pure (rs.any id)
      else if spec.hasEpistemicOrDefeasible then
        let (lTri, _, _) ← evalActTri fuel te
        pure (lTri == .yes)
      else if !(← isHolds fuel te) then pure false
      else if !(← satConditions fuel te) then pure false
      else
        withSubs (Tagged.bindings tspec.domain te) do
          let infos ← a.syncs.mapM (evalSync fuel [])
          pure (infos.flatten.all (fun i => !i.forced))
    | _ =>
      if !(← isHolds fuel te) then pure false
      else satConditions fuel te
termination_by structural n => n

/-- Charter (D5, plan §2.2.1–2): whether performing an act instance has institutional
effect: every `Valid when` condition holds and no immunity protects its recipient. An
event or an act without `Valid when` is valid unless an immunity applies. -/
def isValid : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an act is valid")
  | fuel + 1, te => do
    let spec ← getSpec
    let tspec ← getTypeSpec te.2
    match tspec.kind with
    | .act a =>
      -- 003.8: an element outside the act's domain is not an instance of it, so performing it
      -- has no institutional effect (it still occurs, and is not lawful)
      if !(← isValidInstance fuel te) then pure false
      else if spec.hasEpistemicOrDefeasible then
        let (_, vTri, _) ← evalActTri fuel te
        pure (vTri == .yes)
      else
        let amBlocked ← amendImmunityBlocks fuel te.2 a
        if amBlocked then pure false
        else
          let (blocked, protSaved) ← match tspec.domain, te.1, a.hasRecipient with
            | .products (_ :: _ :: actRelVars), .prod (_ :: recipient :: restArgs), true => do
              let b ← immunityBlocks fuel false te.2 recipient (actRelVars.zip restArgs)
              let p ← immunityBlocks fuel true te.2 recipient (actRelVars.zip restArgs)
              pure (b, p)
            | _, .prod (_ :: recipient :: _), true => do
              let b ← immunityBlocks fuel false te.2 recipient []
              let p ← immunityBlocks fuel true te.2 recipient []
              pure (b, p)
            | _, _, _ => pure (false, false)
          if blocked then pure false
          else
            let conds ← withSubs (Tagged.bindings tspec.domain te) (a.validWhen.mapM (fun c => whenBool (eval fuel c) pure))
            pure (conds.all id || protSaved)
    | _ => pure true
termination_by structural n => n

/-- Whether some immunity (`wantProt = false`) or protection (`wantProt = true`, `D35`, `#52`)
instance that holds applies to `party` on the act `act`: its holder is `party`, `act` is in its
target list, any shared `Related to` components match `actRel`, and none of its `Unless`
conditions hold. -/
def immunityBlocks : Nat → Bool → DomId → Tagged → List (Var × Tagged) → M Bool
  | 0, _, _, _, _ => err (.fuelExhausted "checking immunities")
  | fuel + 1, wantProt, act, party, actRel => do
    let spec ← getSpec
    let state ← getState
    let same (a b : Tagged) : Bool := spec.chaseAlias a.2 == spec.chaseAlias b.2 && Elem.beq a.1 b.1
    let candidates := if wantProt then spec.protectionsFor act else spec.immunitiesAgainst act
    let rs ← candidates.mapM fun entry => do
      let d := entry.1
      let tspec := entry.2.1
      let i := entry.2.2
      match tspec.domain with
      | .products (holderVar :: imRelVars) =>
        if spec.chaseAlias holderVar.dom != spec.chaseAlias party.2 then pure false
        else
          let shared := actRel.filter (fun p => imRelVars.contains p.1)
          let initSubs := (holderVar, party) :: shared
          let free := imRelVars.filter (fun x => !(initSubs.any (fun p => p.1 == x)))
          let activeUnlessFalse (im : Tagged) : M Bool := do
            let us ← withSubs (Tagged.bindings tspec.domain im) (i.unlessConds.mapM (fun c => whenBool (eval fuel c) pure))
            pure (!(us.any id))
          if free.isEmpty then
            withSubs initSubs do
              let insts ← results (whenTagged (eval fuel (.app d (.named []))) pure)
              let bs ← insts.mapM fun im => do
                if ← isHolds fuel im then activeUnlessFalse im else pure false
              pure (bs.any id)
          else
            let held := state.holdsList.filter (fun im => im.2 == d)
            let fromHeld ← held.mapM fun im => do
              let ibinds := Tagged.bindings tspec.domain im
              let matchesInit := initSubs.all fun (v, target) =>
                match ibinds.find? (·.1 == v) with
                | some (_, actual) => same actual target
                | none => false
              if matchesInit then activeUnlessFalse im else pure false
            if fromHeld.any id then pure true
            else if spec.enumerable (.products free) then
              withSubs initSubs do
                let insts ← results (scopeWith (everyValidSubs fuel) free (whenTagged (eval fuel (.app d (.named []))) pure))
                let bs ← insts.mapM fun im => do
                  if ← isHolds fuel im then activeUnlessFalse im else pure false
                pure (bs.any id)
            else pure false
      | _ => pure false
    pure (rs.any id)
termination_by structural n => n

/-- Charter (D11, D25, 014.5): whether an active entrenchment immunity blocks an `Amend` act
`actId` (`Against` names `actId` or `"Amend"`, and the amendment's touched rules intersect the
immunity's reflexively protected rule set, with at least one holding un-lifted instance). -/
def amendImmunityBlocks : Nat → DomId → ActSpec → M Bool
  | 0, _, _ => err (.fuelExhausted "checking amendment entrenchment")
  | fuel + 1, actId, a => do
    if !a.isAmend then pure false
    else
      let spec ← getSpec
      let state ← getState
      let installs := (spec.amendBodies.find? (·.1 == actId)).map (·.2) |>.getD []
      let effTargets := a.effects.filterMap fun
        | .cAll _ tm _ _ | .tAll _ tm _ | .oAll _ tm _ => Stratify.typeOf spec tm
        | _ => none
      let touched := actId :: (Amend.touchedIds a.repeals installs ++ effTargets)
      let rs ← (spec.immunitiesAgainstAmend actId).mapM fun entry => do
        let imId := entry.1
        let imTs := entry.2.1
        let imSpec := entry.2.2
        let extraDeps := Amend.governingDeps spec imId imTs imSpec actId
        let protectedIds := Amend.reflexiveProtectedIds spec imId imSpec extraDeps
        if !(touched.any protectedIds.contains) then pure false
        else
          let activeUnlessFalse (im : Tagged) : M Bool := do
            let us ← withSubs (Tagged.bindings imTs.domain im) (imSpec.unlessConds.mapM (fun c => whenBool (eval fuel c) pure))
            pure (!(us.any id))
          let held := state.holdsList.filter (fun im => im.2 == imId)
          let fromHeld ← held.mapM activeUnlessFalse
          if fromHeld.any id then pure true
          else if spec.enumerable imTs.domain then
            let imVars := spec.components imId
            let insts ← results (scopeWith (everyValidSubs fuel) imVars (whenTagged (eval fuel (.app imId (.named []))) pure))
            let bs ← insts.mapM fun im => do
              if ← isHolds fuel im then activeUnlessFalse im else pure false
            pure (bs.any id)
          else pure false
      pure (rs.any id)
termination_by structural n => n

/-- Whether a duty instance's violation condition holds. Charter (007.3): a duty
`Overridden by d₁, d₂` is not violated while an instance of a named duty holds that shares
the components the two duties have in common (by name, as `Except under` shares them,
005.5); its other components range over every instance. Precedence is declared and one
level deep: the overriding duty's own precedence is not consulted. -/
def evalViolationCondition : Nat → Tagged → Option (List Term) → M Bool
  | 0, _, _ => err (.fuelExhausted "checking a violation condition")
  | fuel + 1, te, mconds => do
    let tspec ← getTypeSpec te.2
    let cond := (mconds.getD []).foldr Term.or (.boolLit false)
    withSubs (Tagged.bindings tspec.domain te) do
      let v ← whenBool (eval fuel cond) pure
      if !v then pure false
      else
        match tspec.kind with
        | .duty ds =>
          let exc ← ds.excusedWhen.mapM (fun c => whenBool (eval fuel c) pure)
          if exc.any id then pure false
          else if ds.overriddenBy.isEmpty then pure true
          else
            let spec ← getSpec
            let subs ← getSubs
            let rs ← ds.overriddenBy.mapM fun d' => do
              let free := (spec.components d').filter (fun x => !(subs.any (fun p => p.1 == x)))
              let insts ← results (scopeWith (everyValidSubs fuel) free (whenTagged (eval fuel (.app d' (.named []))) pure))
              let held ← insts.mapM (isHolds fuel)
              pure (held.any id)
            pure (!(rs.any id))
        | _ => pure true
termination_by structural n => n

def isViolated : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether a duty is violated")
  | fuel + 1, te => do
    if !(← isHolds fuel te) then pure false
    else evalViolationCondition fuel te ((← getSpec).findViolationCond te.2)
termination_by structural n => n

/-- Three-valued Kleene guard evaluation (`D22`, `G3.2`): propagates `undetermined` and
collects `unmetEvidence` whenever an `Unresolved` or `Conflicted` `Evidenced` premise can
influence the guard outcome (`T06`, `T07`). -/
def evalTermTri : Nat → Term → M (TriBool × List (Tagged × EvidenceStatus))
  | 0, _ => err (.fuelExhausted "evaluating three-valued guard")
  | fuel + 1, t0 => do
    match t0 with
    | .boolLit b => pure (TriBool.ofBool b, [])
    | .not a => do
      let (va, ua) ← evalTermTri fuel a
      pure (va.not, ua)
    | .and a b => do
      let (va, ua) ← evalTermTri fuel a
      if va == .no then pure (.no, [])
      else
        let (vb, ub) ← evalTermTri fuel b
        if vb == .no then pure (.no, [])
        else if va == .yes && vb == .yes then pure (.yes, [])
        else pure (.undetermined, dedupUnmet (ua ++ ub))
    | .or a b => do
      let (va, ua) ← evalTermTri fuel a
      if va == .yes then pure (.yes, [])
      else
        let (vb, ub) ← evalTermTri fuel b
        if vb == .yes then pure (.yes, [])
        else if va == .no && vb == .no then pure (.no, [])
        else pure (.undetermined, dedupUnmet (ua ++ ub))
    | .present inner =>
      whenTagged (eval fuel inner) fun te => do
        let conf? ← lookupNormativeConflict te
        if conf?.isSome then
          pure (.undetermined, [(te, .conflicted)])
        else
          let tspec ← getTypeSpec te.2
          if tspec.isEvidencedFact then
            if !(← isValidInstance fuel te) then pure (.no, [])
            else
              let st ← lookupEvidenceStatus te
              match st, tspec.factPresumed with
              | .unresolved, some b => pure (TriBool.ofBool b, [])
              | _, _ =>
                match TriBool.ofEvidenceStatus st with
                | .undetermined => pure (.undetermined, [(te, st)])
                | v => pure (v, [])
          else
            let b ← isHolds fuel te
            pure (TriBool.ofBool b, [])
    | .exists_ xs body => do
      let pairs ← results (scopeWith (everyValidSubs fuel) xs (evalTermTri fuel body))
      if pairs.any (fun p => p.1 == .yes) then pure (.yes, [])
      else if pairs.all (fun p => p.1 == .no) then pure (.no, [])
      else pure (.undetermined, dedupUnmet (pairs.flatMap fun p => if p.1 == .undetermined then p.2 else []))
    | .forall_ xs body => do
      let pairs ← results (scopeWith (everyValidSubs fuel) xs (evalTermTri fuel body))
      if pairs.any (fun p => p.1 == .no) then pure (.no, [])
      else if pairs.all (fun p => p.1 == .yes) then pure (.yes, [])
      else pure (.undetermined, dedupUnmet (pairs.flatMap fun p => if p.1 == .undetermined then p.2 else []))
    | other =>
      whenBool (eval fuel other) fun b => pure (TriBool.ofBool b, [])
termination_by structural n => n

/-- Three-valued `(lawfulTri, validTri, unmetEvidence)` judgment for an act instance (`D22`). -/
def evalActTri : Nat → Tagged → M (TriBool × TriBool × List (Tagged × EvidenceStatus))
  | 0, _ => err (.fuelExhausted "evaluating epistemic act judgment")
  | fuel + 1, te => do
    let tspec ← getTypeSpec te.2
    match tspec.kind with
    | .act a =>
      -- 003.8: not an instance of the act, so neither lawful nor valid, whatever the evidence
      if !(← isValidInstance fuel te) then pure (.no, .no, []) else
      let (vTri, vUnmet) ← withSubs (Tagged.bindings tspec.domain te) do
        let ps ← a.validWhen.mapM (evalTermTri fuel)
        let folded := ps.foldl (fun (accV, accU) (v, u) =>
          let nv := TriBool.and accV v
          (nv, if nv == .no then [] else accU ++ u)) (TriBool.yes, ([] : List (Tagged × EvidenceStatus)))
        let (immBlocked, protSaved) ← match tspec.domain, te.1, a.hasRecipient with
          | .products (_ :: _ :: actRelVars), .prod (_ :: recipient :: restArgs), true => do
            let b ← immunityBlocks fuel false te.2 recipient (actRelVars.zip restArgs)
            let p ← immunityBlocks fuel true te.2 recipient (actRelVars.zip restArgs)
            pure (b, p)
          | _, .prod (_ :: recipient :: _), true => do
            let b ← immunityBlocks fuel false te.2 recipient []
            let p ← immunityBlocks fuel true te.2 recipient []
            pure (b, p)
          | _, _, _ => pure (false, false)
        let amBlocked ← amendImmunityBlocks fuel te.2 a
        if immBlocked || amBlocked then pure (TriBool.no, [])
        else if protSaved then pure (TriBool.yes, [])
        else pure folded
      let (lTri, lUnmet) ← (do
        if !a.exceptUnder.isEmpty then
          let b ← isEnabled fuel te
          pure (TriBool.ofBool b, [])
        else
          let now ← getTime
          match ← lookupState te with
          | some i =>
            if !(i.live now) then pure (TriBool.no, [])
            else
              let sc ← satConditions fuel te
              pure (TriBool.ofBool sc, [])
          | none =>
            let hwTerms : List Term := tspec.derivation.filterMap fun
              | .holdsWhen c => some c
              | _ => none
            if hwTerms.isEmpty then
              let h ← isHolds fuel te
              let sc ← if h then satConditions fuel te else pure false
              pure (TriBool.ofBool (h && sc), [])
            else
              withSubs (Tagged.bindings tspec.domain te) do
                let hps ← hwTerms.mapM (evalTermTri fuel)
                let (hV, hU) := hps.foldl (fun (accV, accU) (v, u) =>
                  let nv := TriBool.or accV v
                  (nv, if nv == .yes then [] else accU ++ u)) (TriBool.no, ([] : List (Tagged × EvidenceStatus)))
                if hV == .no then pure (TriBool.no, [])
                else
                  let cps ← tspec.conditions.mapM (evalTermTri fuel)
                  let (cV, cU) := cps.foldl (fun (accV, accU) (v, u) =>
                    let nv := TriBool.and accV v
                    (nv, if nv == .no then [] else accU ++ u)) (hV, hU)
                  let infos ← a.syncs.mapM (evalSync fuel [])
                  if infos.flatten.any (·.forced) then pure (TriBool.no, [])
                  else pure (cV, cU))
      pure (lTri, vTri, dedupUnmet (lUnmet ++ vUnmet))
    | _ =>
      let en ← isEnabled fuel te
      let vl ← isValid fuel te
      pure (TriBool.ofBool en, TriBool.ofBool vl, [])
termination_by structural n => n

/-- What triggering an act or event instance does (eFLINT `instantiate_trans'`),
with `done` guarding sync cycles. -/
def instantiateTrans : Nat → List Tagged → Tagged → M TransInfo
  | 0, _, _ => err (.fuelExhausted "triggering an act")
  | fuel + 1, done, te => do
    if done.contains te then empty
    else
      let spec ← getSpec
      let tspec ← getTypeSpec te.2
      let actor : Option Tagged := match te.1 with
        | .prod (a :: _) => some a
        | _ => none
      let doTransition (mActor : Option Tagged) (enabled valid : Bool)
          (lTri vTri : TriBool) (unmet : List (Tagged × EvidenceStatus))
          (effects : List Effect) (ss : List Sync) (physical : Bool) : M TransInfo :=
        withSubs (Tagged.bindings tspec.domain te) do
          let syncInfos ← ss.mapM (evalSync fuel (te :: done))
          let syncInfos := syncInfos.flatten
          let (ssAss, anyF) := syncTransInfos syncInfos
          -- D5: the act's own effects apply iff it is valid; synced transitions are judged on their own
          let pairs ← if valid then effects.mapM (evalEffect fuel) else pure []
          let stores := pairs.map (·.1)
          let warns := pairs.flatMap (·.2)
          -- Law 6: the act is the origin of what its effects assign
          let own : Store := (Store.unions stores).map fun (x, a) => (x, a.byAct te)
          let ass := Store.union own ssAss
          let disabled := anyF || !enabled
          let forced := anyF || (lTri == .no && !physical)
          let finalLTri := if anyF then .no else lTri
          pure (.mk te ass forced disabled valid mActor syncInfos finalLTri vTri unmet warns)
      match tspec.kind with
      | .fact _ => empty
      | .duty _ => empty
      | .immunity _ => empty
      | .act a => do
        if spec.hasEpistemicOrDefeasible then
          let (lTri, vTri, unmet) ← evalActTri fuel te
          let enabled := lTri == .yes
          let valid := vTri == .yes
          doTransition actor enabled valid lTri vTri unmet a.effects a.syncs a.physical
        else
          let enabled ← isEnabled fuel te
          let valid ← isValid fuel te
          let lTri := TriBool.ofBool enabled
          let vTri := TriBool.ofBool valid
          doTransition actor enabled valid lTri vTri [] a.effects a.syncs a.physical
      | .event e => do
        let enabled ← isEnabled fuel te
        doTransition none enabled true (TriBool.ofBool enabled) .yes [] e.effects e.syncs true
termination_by structural n => n

def evalSync : Nat → List Tagged → Sync → M (List TransInfo)
  | 0, _, _ => err (.fuelExhausted "evaluating a sync")
  | fuel + 1, done, s => foreachWith (everyValidSubs fuel) s.xs (whenTagged (eval fuel s.t) (instantiateTrans fuel done))
termination_by structural n => n

def evalEffect : Nat → Effect → M (Store × List Diagnostic)
  | 0, _ => err (.fuelExhausted "evaluating an effect")
  | fuel + 1, e => do
    let elemSource : Elem → String := fun el =>
      let rec go : Nat → Elem → String
        | 0, _ => ""
        | _ + 1, .str s => s
        | _ + 1, .int i => toString i
        | k + 1, .prod args => "(" ++ ", ".intercalate (args.map fun (e', _) => go k e') ++ ")"
      go 16 el
    let resolveSource : EvSource → M String
      | .named s => pure s
      | .component x => do
        let (el, _) ← substituteVar x
        pure (elemSource el)
    let bindEffVar (allowClear : Bool) (imp : List Var) (t : Term) (x : Var) : M Tagged := do
      let spec ← getSpec
      let d := spec.removeDecoration x
      let (tspec, _, _) ← getTypeEntry d
      if tspec.restriction == some .var then
        let trues ← trueInstancesOf d
        if trues.isEmpty then
          if allowClear && isBareClearTerm spec d t then empty
          else err (.missingInput (.unassignedVar d))
        else nd trues
      else if tspec.restriction == some .function && imp.contains x then
        let trues ← trueInstancesOf d
        match tspec.domain with
        | .products [kVar, _] =>
          match findFnKeyTerm x kVar 32 t with
          | some keyExpr =>
            let kVals ← results (whenTagged (eval fuel keyExpr) pure)
            match kVals with
            | [kVal] =>
              let matching := trues.filter fun (el, _) =>
                match el with
                | .prod [k, _] => k == kVal
                | _ => false
              if matching.isEmpty then err (.missingInput (.unassignedFunction d (some kVal)))
              else nd matching
            | _ =>
              if trues.isEmpty then err (.missingInput (.unassignedFunction d none))
              else nd trues
          | none =>
            if trues.isEmpty then err (.missingInput (.unassignedFunction d none))
            else nd trues
        | _ =>
          if trues.isEmpty then err (.missingInput (.unassignedFunction d none))
          else nd trues
      else everyValidSubs fuel x
    match e with
    | .cAll xs t none imp =>
      let tes ← foreachWith (bindEffVar false imp t) xs (whenTagged (eval fuel t) pure)
      pure (tes.map (·, .holdsTrue none none), [])
    | .cAll xs t (some d) imp =>
      -- D7: `Creates e For d` stamps the instances with the expiry now + d
      let now ← getTime
      let pairs ← foreachWith (bindEffVar false imp t) xs (whenTagged (eval fuel t) (fun te => whenInt (eval fuel d) (fun dur => pure (te, now + dur))))
      pure (pairs.map (fun (te, u) => (te, .holdsTrue (some u) none)), [])
    | .tAll xs t imp =>
      let tes ← foreachWith (bindEffVar true imp t) xs (whenTagged (eval fuel t) pure)
      pure (tes.map (·, .holdsFalse none), [])
    | .oAll xs t imp =>
      let tes ← foreachWith (bindEffVar true imp t) xs (whenTagged (eval fuel t) pure)
      pure (tes.map (·, .unknown), [])
    | .evOp .support xs t src => do
      let srcStr ← resolveSource src
      let tes ← foreachWith (bindEffVar false xs t) xs (whenTagged (eval fuel t) pure)
      pure (tes.map (fun te => ((.prod [te, (.str srcStr, "string")], evSupportDom), .holdsTrue none none)), [])
    | .evOp .rebut xs t src => do
      let srcStr ← resolveSource src
      let tes ← foreachWith (bindEffVar false xs t) xs (whenTagged (eval fuel t) pure)
      pure (tes.map (fun te => ((.prod [te, (.str srcStr, "string")], evRebutDom), .holdsTrue none none)), [])
    | .evOp op xs t src => do
      let srcStr ← resolveSource src
      let tes ← foreachWith (bindEffVar false xs t) xs (whenTagged (eval fuel t) pure)
      let state ← getState
      let doms : List DomId := match op with
        | .retractSupport => [evSupportDom]
        | .retractRebut   => [evRebutDom]
        | _               => [evSupportDom, evRebutDom]
      let polLabel : String := match op with
        | .retractSupport => "supporting "
        | .retractRebut   => "contrary "
        | _               => ""
      let perTarget := tes.map fun te =>
        let found := state.contents.filterMap fun (entryTe, i) =>
          if doms.contains entryTe.2 && i.live state.time then
            match entryTe.1 with
            | .prod [targetTe, (.str entrySrc, _)] =>
              if targetTe == te && (srcStr.isEmpty || entrySrc == srcStr) then
                some (entryTe, Assignment.holdsFalse none)
              else none
            | _ => none
          else none
        let ws := if found.isEmpty then
          [Diagnostic.warning "CHR109"
            s!"retraction on {Tagged.pp te}{if srcStr.isEmpty then "" else s!" by {srcStr}"} found no active {polLabel}evidence to withdraw (005.11)"]
        else []
        (found, ws)
      pure (perTarget.flatMap (·.1), perTarget.flatMap (·.2))
    | .findingOp pol xs t std => do
      let tes ← foreachWith (everyValidSubs fuel) xs (whenTagged (eval fuel t) pure)
      let state ← getState
      let posDom := if pol then evFindingPosDom else evFindingNegDom
      let oppDom := if pol then evFindingNegDom else evFindingPosDom
      let entries := tes.flatMap fun te =>
        let clearOpp := state.contents.filterMap fun (entryTe, i) =>
          if entryTe.2 == oppDom && i.live state.time then
            match entryTe.1 with
            | .prod [targetTe, _] => if targetTe == te then some (entryTe, Assignment.holdsFalse none) else none
            | _ => none
          else none
        ((.prod [te, (.str std, "string")], posDom), Assignment.holdsTrue none none) :: clearOpp
      pure (entries, [])
    | .amendOp actId =>
      pure ([((.str actId, amendCommitDom), Assignment.holdsTrue none none)], [])
termination_by structural n => n

/-- Evaluate a checked term to its values (eFLINT `eval`). -/
def eval : Nat → Term → M Value
  | 0, _ => err (.fuelExhausted "evaluating an expression")
  | fuel + 1, t0 => do
    match t0 with
    | .currentTime => .int <$> getTime
    | .stringLit s => pure (.str s)
    | .boolLit b => pure (.bool b)
    | .intLit i => pure (.int i)
    | .ref x => .tagged <$> substituteVar x
    | .app d args => do
      let (dom, filter) ← getDom d
      -- an instance built through a placeholder is an instance of the aliased type
      let d := (← getSpec).chaseAlias d
      match dom with
      | .products xs =>
        let argsV ← match args with
          | .named [] => xs.mapM substituteVar
          | _ =>
            let repl := args.substitutions xs
            let tes ← repl.mapM (fun (x, t) => whenTagged (eval fuel t) (fun te => pure (x, te)))
            withSubs tes (xs.mapM substituteVar)
        if filter.isTrueLit then
          pure (.tagged (.prod argsV, d))
        else
          withSubs (xs.zip argsV) do
            checkTrue (eval fuel filter)
            pure (.tagged (.prod argsV, d))
      | _ => err (.primitiveApplication d)
    | .tag t d => do let v ← eval fuel t; tagValue v d
    | .untag t => do let v ← eval fuel t; untagValue v
    | .not t => whenBool (eval fuel t) (fun b => pure (.bool !b))
    | .and a b => whenBool (eval fuel a) (fun
        | false => pure (.bool false)
        | true => whenBool (eval fuel b) (fun b => pure (.bool b)))
    | .or a b => whenBool (eval fuel a) (fun
        | true => pure (.bool true)
        | false => whenBool (eval fuel b) (fun b => pure (.bool b)))
    | .leq a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.bool (x ≤ y))))
    | .le a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.bool (x < y))))
    | .geq a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.bool (x ≥ y))))
    | .ge a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.bool (x > y))))
    | .mult a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.int (x * y))))
    | .mod a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.int (Int.fmod x y))))
    | .div a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.int (Int.fdiv x y))))
    | .sub a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.int (x - y))))
    | .add a b => whenInt (eval fuel a) (fun x => whenInt (eval fuel b) (fun y => pure (.int (x + y))))
    | .eq a b => do let x ← eval fuel a; let y ← eval fuel b; pure (.bool (x == y))
    | .neq a b => do let x ← eval fuel a; let y ← eval fuel b; pure (.bool (!(x == y)))
    | .sum xs t => do let is ← foreachWith (everyValidSubs fuel) xs (whenInt (eval fuel t) pure); pure (.int (is.foldl (· + ·) 0))
    | .count xs t => do let vs ← foreachWith (everyValidSubs fuel) xs (eval fuel t); pure (.int vs.length)
    | .max xs t => do
      let is ← foreachWith (everyValidSubs fuel) xs (whenInt (eval fuel t) pure)
      pure (.int (match is with | [] => 0 | i :: rest => rest.foldl max i))
    | .min xs t => do
      let is ← foreachWith (everyValidSubs fuel) xs (whenInt (eval fuel t) pure)
      pure (.int (match is with | [] => 0 | i :: rest => rest.foldl min i))
    | .when t c => do
      let v ← eval fuel t
      whenBool (eval fuel c) (fun | true => pure v | false => empty)
    | .present t => whenTagged (eval fuel t) (fun te => .bool <$> isHolds fuel te)
    | .heldFor t d => whenTagged (eval fuel t) (fun te => whenInt (eval fuel d) (fun dur => do
        -- D7, Law 7: a condition over the stamp, never an event
        if !(← isHolds fuel te) then pure (.bool false)
        else
          let now ← getTime
          match ← lookupState te with
          | some i => pure (.bool (now - i.since ≥ dur))
          | none => pure (.bool false)))
    | .violated t => whenTagged (eval fuel t) (fun te => .bool <$> isViolated fuel te)
    | .enabled t => whenTagged (eval fuel t) (fun te => .bool <$> isEnabled fuel te)
    | .evStatus want t => whenTagged (eval fuel t) (fun te => do
        let st ← lookupEvidenceStatus te
        pure (.bool (st == want)))
    | .hasConflict t => whenTagged (eval fuel t) (fun te => do
        let conf? ← lookupNormativeConflict te
        pure (.bool conf?.isSome))
    | .mulDivRound x num den mode =>
      whenInt (eval fuel x) fun vx =>
      whenInt (eval fuel num) fun vnum =>
      whenInt (eval fuel den) fun vden =>
        match mulDivRound vx vnum vden mode with
        | .ok res => pure (.int res)
        | .error msg => err (.arithmeticError msg)
    | .exists_ xs t => do
      let rs ← results (scopeWith (everyValidSubs fuel) xs (checkTrue (eval fuel t)))
      pure (.bool !rs.isEmpty)
    | .forall_ xs t => do
      let bs ← results (scopeWith (everyValidSubs fuel) xs (whenBool (eval fuel t) pure))
      pure (.bool (bs.all id))
    | .project t x => whenTagged (eval fuel t) (fun te => do
        match te.1 with
        | .prod tes =>
          let (dom, _) ← getDom te.2
          match dom with
          | .products rs =>
            if tes.length == rs.length then
              match indexOf x rs with
              | some j => match tes[j]? with
                | some te' => pure (.tagged te')
                | none => empty
              | none => empty
            else empty
          | _ => empty
        | _ => empty)

end

/-- Bind each variable in turn to every valid instance and run `m` (eFLINT `foreach`). -/
def foreach {α} (fuel : Nat) (xs : List Var) (m : M α) : M (List α) := foreachWith (everyValidSubs fuel) xs m

def scope {α} (fuel : Nat) (xs : List Var) (m : M α) : M α := scopeWith (everyValidSubs fuel) xs m

/-- Fuel for one evaluation: bounds nesting depth, not total work. -/
def fuel : Nat := 100000

end M

end Charter
