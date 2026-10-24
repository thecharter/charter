import Charter.Core.State

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
  spec  : Spec
  state : State

/-- The evaluation monad: a context and bindings in, a list of results or an error out. -/
structure M (α : Type) where
  run : Ctx → Subs → Except RuntimeError (List α)

namespace M

instance : Monad M where
  pure a := ⟨fun _ _ => .ok [a]⟩
  bind m f := ⟨fun c s => do
    let as ← m.run c s
    as.foldlM (fun acc a => do let bs ← (f a).run c s; pure (acc ++ bs)) []⟩

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

def getTypeSpec (d : DomId) : M TypeSpec := do
  match (← getSpec).findDecl d with
  | some t => pure t
  | none => err (.undeclaredType d)

def getDom (d : DomId) : M (Domain × Term) := do
  let t ← getTypeSpec d
  pure (t.domain, t.domainConstraint)

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
    | .strings ss => nd (ss.map .str)
    | .ints is => nd (is.map .int)
    | .products xs => do
      let args ← xs.mapM (everyValidSubs fuel)
      pure (.prod args)

/-- Every instance a variable may be bound to: all elements of an enumerable
domain that pass the domain constraint, or the instances known to hold of a
non-enumerable one (eFLINT `every_valid_subs`). -/
def everyValidSubs : Nat → Var → M Tagged
  | 0, _ => err (.fuelExhausted "binding a variable")
  | fuel + 1, x => do
    let spec ← getSpec
    let state ← getState
    let d := spec.removeDecoration x
    let (dom, filter) ← getDom d
    if spec.enumerable dom then
      let e ← instantiateDomain fuel d dom
      let te : Tagged := (e, d)
      withSubs (Tagged.bindings dom te) (checkTrue (eval fuel filter))
      pure te
    else
      let (trues, falses) := state.assignedInstances d
      match spec.closedType d with
      | some false => if trues.isEmpty && falses.isEmpty then err (.missingInput (.instances d)) else nd trues
      | _ => nd trues

/-- Whether an instance is well-formed: in its domain and passing the constraint. -/
def isValidInstance : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "checking an instance")
  | fuel + 1, te => do
    let (dom, filter) ← getDom te.2
    let check : M Bool := withSubs (Tagged.bindings dom te) (whenBool (eval fuel filter) pure)
    match te.1, dom with
    | .int i, .ints is => if is.contains i then check else pure false
    | .int _, .anyInt => check
    | .int _, .time => check
    | .int _, .duration => check
    | .str s, .strings ss => if ss.contains s then check else pure false
    | .str _, .anyString => check
    | .prod args, .products params =>
      if args.length == params.length then
        let oks ← args.mapM (isValidInstance fuel)
        if oks.all id then check else pure false
      else pure false
    | _, _ => pure false

/-- Whether the `Conditioned by` conditions of an instance's type hold for it. -/
def satConditions : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "checking conditions")
  | fuel + 1, te => do
    if !(← isValidInstance fuel te) then pure false
    else
      let tspec ← getTypeSpec te.2
      withSubs (Tagged.bindings tspec.domain te) do
        let bs ← tspec.conditions.mapM (fun c => whenBool (eval fuel c) pure)
        pure (bs.all id)

/-- Whether an instance holds (eFLINT `is_holds`): its assignment, or false for a
closed type, or missing input for an open one. -/
def isHolds : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an instance holds")
  | fuel + 1, te => do
    if !(← isValidInstance fuel te) then pure false
    else
      let state ← getState
      let spec ← getSpec
      match state.lookup te with
      | some i => pure (i.live state.time)
      | none =>
        match spec.judgedAct te.2 with
        | some clauses =>
          -- D15 (brief B11): an act whose domain is not enumerable is judged for the
          -- instance asked about; its `Holds when` is read with the components bound,
          -- as saturation would have read it had the domain been finite (004.1, 005.5).
          let tspec ← getTypeSpec te.2
          withSubs (Tagged.bindings tspec.domain te) do
            let rs ← results (do let c ← nd clauses; whenBool (eval fuel c) pure)
            if rs.any id then satConditions fuel te else pure false
        | none =>
          match spec.closedType te.2 with
          | some false => err (.missingInput (.assignments [te]))
          | _ => pure false

/-- Whether an act or event instance is enabled: it holds, its conditions hold,
and no transition it syncs with is forced (eFLINT `is_enabled`). Charter's
`Except under a₁, a₂` (plan §2.2.4) replaces this: the act is lawful iff some
instance of a named act sharing its bound components is enabled and valid. -/
def isEnabled : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an act is enabled")
  | fuel + 1, te => do
    let tspec ← getTypeSpec te.2
    match tspec.kind with
    | .act a =>
      if !a.exceptUnder.isEmpty then
        let spec ← getSpec
        withSubs (Tagged.bindings tspec.domain te) do
          let subs ← getSubs
          let rs ← a.exceptUnder.mapM fun d' => do
            let free := (spec.components d').filter (fun x => !(subs.any (fun p => p.1 == x)))
            let insts ← results (scope fuel free (whenTagged (eval fuel (.app d' (.named []))) pure))
            let oks ← insts.mapM fun inst => do
              if ← isEnabled fuel inst then isValid fuel inst else pure false
            pure (oks.any id)
          pure (rs.any id)
      else if !(← isHolds fuel te) then pure false
      else if !(← satConditions fuel te) then pure false
      else
        withSubs (Tagged.bindings tspec.domain te) do
          let infos ← a.syncs.mapM (evalSync fuel [])
          pure (infos.flatten.all (fun i => !i.forced))
    | _ =>
      if !(← isHolds fuel te) then pure false
      else satConditions fuel te

/-- Charter (D5, plan §2.2.1–2): whether performing an act instance has institutional
effect: every `Valid when` condition holds and no immunity protects its recipient. An
event or an act without `Valid when` is valid unless an immunity applies. -/
def isValid : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether an act is valid")
  | fuel + 1, te => do
    let tspec ← getTypeSpec te.2
    match tspec.kind with
    | .act a =>
      let conds ← withSubs (Tagged.bindings tspec.domain te) (a.validWhen.mapM (fun c => whenBool (eval fuel c) pure))
      if !(conds.all id) then pure false
      else
        match te.1, a.hasRecipient with
        | .prod (_ :: recipient :: _), true => do
          let blocked ← immunityBlocks fuel te.2 recipient
          pure (!blocked)
        | _, _ => pure true
    | _ => pure true

/-- Whether some immunity instance that holds protects `party` against the act `act`:
its holder is `party`, `act` is in its `Against`, and none of its `Unless` conditions hold. -/
def immunityBlocks : Nat → DomId → Tagged → M Bool
  | 0, _, _ => err (.fuelExhausted "checking immunities")
  | fuel + 1, act, party => do
    let spec ← getSpec
    let state ← getState
    let same (a b : Tagged) : Bool := spec.chaseAlias a.2 == spec.chaseAlias b.2 && Elem.beq a.1 b.1
    let rs ← (spec.immunitiesAgainst act).mapM fun entry => do
      let d := entry.1
      let tspec := entry.2.1
      let i := entry.2.2
      let held := state.holdsList.filter (fun im => im.2 == d)
      let bs ← held.mapM fun im => do
        match im.1 with
        | .prod (holder :: _) =>
          if same holder party then
            let us ← withSubs (Tagged.bindings tspec.domain im) (i.unlessConds.mapM (fun c => whenBool (eval fuel c) pure))
            pure (!(us.any id))
          else pure false
        | _ => pure false
      pure (bs.any id)
    pure (rs.any id)

def evalViolationCondition : Nat → Tagged → Option (List Term) → M Bool
  | 0, _, _ => err (.fuelExhausted "checking a violation condition")
  | fuel + 1, te, mconds => do
    let (dom, _) ← getDom te.2
    let cond := (mconds.getD []).foldr Term.or (.boolLit false)
    withSubs (Tagged.bindings dom te) (whenBool (eval fuel cond) pure)

def isViolated : Nat → Tagged → M Bool
  | 0, _ => err (.fuelExhausted "deciding whether a duty is violated")
  | fuel + 1, te => do
    if !(← isHolds fuel te) then pure false
    else evalViolationCondition fuel te ((← getSpec).findViolationCond te.2)

/-- Bind each variable in turn to every valid instance and run `m` (eFLINT `foreach`). -/
def foreach {α} : Nat → List Var → M α → M (List α)
  | 0, _, _ => err (.fuelExhausted "iterating a Foreach")
  | fuel + 1, xs, m => results (scope fuel xs m)

def scope {α} : Nat → List Var → M α → M α
  | 0, _, _ => err (.fuelExhausted "iterating a Foreach")
  | _, [], m => m
  | fuel + 1, x :: xs, m => do
    let te ← everyValidSubs fuel x
    bindVar x te (scope fuel xs m)

/-- What triggering an act or event instance does (eFLINT `instantiate_trans'`),
with `done` guarding sync cycles. -/
def instantiateTrans : Nat → List Tagged → Tagged → M TransInfo
  | 0, _, _ => err (.fuelExhausted "triggering an act")
  | fuel + 1, done, te => do
    if done.contains te then empty
    else
      let tspec ← getTypeSpec te.2
      let enabled ← isEnabled fuel te
      let actor : Option Tagged := match te.1 with
        | .prod (a :: _) => some a
        | _ => none
      let doTransition (mActor : Option Tagged) (valid : Bool) (effects : List Effect) (ss : List Sync) (physical : Bool) : M TransInfo :=
        withSubs (Tagged.bindings tspec.domain te) do
          let syncInfos ← ss.mapM (evalSync fuel (te :: done))
          let syncInfos := syncInfos.flatten
          let (ssAss, anyF) := syncTransInfos syncInfos
          -- D5: the act's own effects apply iff it is valid; synced transitions are judged on their own
          let stores ← if valid then effects.mapM (evalEffect fuel) else pure []
          -- Law 6: the act is the origin of what its effects assign
          let own : Store := (Store.unions stores).map fun (x, a) => (x, a.byAct te)
          let ass := Store.union own ssAss
          let disabled := anyF || !enabled
          let forced := anyF || (!enabled && !physical)
          pure (.mk te ass forced disabled valid mActor syncInfos)
      match tspec.kind with
      | .fact _ => empty
      | .duty _ => empty
      | .immunity _ => empty
      | .act a => do
        let valid ← isValid fuel te
        doTransition actor valid a.effects a.syncs a.physical
      | .event e => doTransition none true e.effects e.syncs true

def evalSync : Nat → List Tagged → Sync → M (List TransInfo)
  | 0, _, _ => err (.fuelExhausted "evaluating a sync")
  | fuel + 1, done, s => foreach fuel s.xs (whenTagged (eval fuel s.t) (instantiateTrans fuel done))

def evalEffect : Nat → Effect → M Store
  | 0, _ => err (.fuelExhausted "evaluating an effect")
  | fuel + 1, e => do
    match e with
    | .cAll xs t none => let tes ← foreach fuel xs (whenTagged (eval fuel t) pure); pure (tes.map (·, .holdsTrue none none))
    | .cAll xs t (some d) =>
      -- D7: `Creates e For d` stamps the instances with the expiry now + d
      let now ← getTime
      let pairs ← foreach fuel xs (whenTagged (eval fuel t) (fun te => whenInt (eval fuel d) (fun dur => pure (te, now + dur))))
      pure (pairs.map fun (te, u) => (te, .holdsTrue (some u) none))
    | .tAll xs t => let tes ← foreach fuel xs (whenTagged (eval fuel t) pure); pure (tes.map (·, .holdsFalse none))
    | .oAll xs t => let tes ← foreach fuel xs (whenTagged (eval fuel t) pure); pure (tes.map (·, .unknown))

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
        let repl := args.substitutions xs
        let tes ← repl.mapM (fun (x, t) => whenTagged (eval fuel t) (fun te => pure (x, te)))
        let argsV ← withSubs tes (xs.mapM substituteVar)
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
    | .sum xs t => do let is ← foreach fuel xs (whenInt (eval fuel t) pure); pure (.int (is.foldl (· + ·) 0))
    | .count xs t => do let vs ← foreach fuel xs (eval fuel t); pure (.int vs.length)
    | .max xs t => do
      let is ← foreach fuel xs (whenInt (eval fuel t) pure)
      pure (.int (match is with | [] => 0 | i :: rest => rest.foldl max i))
    | .min xs t => do
      let is ← foreach fuel xs (whenInt (eval fuel t) pure)
      pure (.int (match is with | [] => 0 | i :: rest => rest.foldl min i))
    | .when t c => do
      let v ← eval fuel t
      whenBool (eval fuel c) (fun | true => pure v | false => empty)
    | .present t => whenTagged (eval fuel t) (fun te => .bool <$> isHolds fuel te)
    | .heldFor t d => whenTagged (eval fuel t) (fun te => whenInt (eval fuel d) (fun dur => do
        -- D7, Law 7: a condition over the stamp, never an event
        if !(← isHolds fuel te) then pure (.bool false)
        else
          let state ← getState
          match state.lookup te with
          | some i => pure (.bool (state.time - i.since ≥ dur))
          | none => pure (.bool false)))
    | .violated t => whenTagged (eval fuel t) (fun te => .bool <$> isViolated fuel te)
    | .enabled t => whenTagged (eval fuel t) (fun te => .bool <$> isEnabled fuel te)
    | .exists_ xs t => do
      let rs ← results (scope fuel xs (checkTrue (eval fuel t)))
      pure (.bool !rs.isEmpty)
    | .forall_ xs t => do
      let bs ← results (scope fuel xs (whenBool (eval fuel t) pure))
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

/-- Fuel for one evaluation: bounds nesting depth, not total work. -/
def fuel : Nat := 100000

end M

end Charter
