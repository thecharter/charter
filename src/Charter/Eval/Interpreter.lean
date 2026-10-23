import Charter.Eval.Eval
import Charter.Resolve.Static

/-!
# Charter.Eval.Interpreter — Phrases, saturation, and what a step reports

eFLINT's `Interpreter.hs` and `Saturation.hs`, per D2, with D6 and D12 applied:

- **Saturation is a stratified fixpoint** (D6). The derived types are ordered by
  their dependencies; a dependency through a non-monotone operator (`Not`,
  `Forall`, `Count`, `Sum`, `Max`, `Min`) is negative, and a negative dependency
  inside a cycle is rejected with CHR020 before anything runs. Each stratum is
  then saturated to its least fixpoint with every lower stratum fixed, so the
  result never depends on the order of type names. Assignments beat derivations
  (`State.derive`), and derived facts are recomputed from scratch after every
  phrase (`State.rebase`), as in eFLINT.
- **A duty's violation is reported once** (D12), when it begins; whether it is
  violated now is always `isViolated`.

`runPhrase` is the step: resolve the phrase against the current spec, evaluate it
to a store of assignments, apply the store, saturate, and report. A phrase that
fails leaves the configuration unchanged (eFLINT `interpreter`).
-/

namespace Charter

/-! ## Stratification (D6) -/

namespace Stratify

inductive Pol | pos | neg
  deriving DecidableEq, Repr

def Pol.under : Pol → Pol → Pol
  | .pos, p => p
  | .neg, _ => .neg

/-- The type an instance-valued checked term denotes, if it is syntactically clear. -/
def typeOf (spec : Spec) : Term → Option DomId
  | .app d _ => some d
  | .ref x => some (spec.removeDecoration x)
  | .project _ x => some (spec.removeDecoration x)
  | .tag _ d => some d
  | .when t _ => typeOf spec t
  | _ => none

abbrev Dep := DomId × Pol

/-- Binding a variable enumerates its type, which reads the type's holding instances
when the domain is not enumerable (and its domain constraint always); every bound
variable is therefore a read of its type. -/
def binderDeps (spec : Spec) (xs : List Var) (p : Pol) : List Dep :=
  xs.map fun x => (spec.removeDecoration x, p)

mutual
/-- The types a checked term reads, with the polarity of each read. `bound` are the
variables bound by enclosing binders (their mention is a binding, not a read). -/
def deps (spec : Spec) : Nat → List Var → Pol → Term → List Dep
  | 0, _, _, _ => []
  | fuel + 1, bound, p, t =>
    match t with
    | .boolLit _ | .intLit _ | .stringLit _ | .currentTime => []
    | .ref x => if bound.contains x then [] else [(spec.removeDecoration x, p)]
    | .app _ args => depsArgs spec fuel bound p args
    | .present t => (typeOf spec t).toList.map (·, p) ++ deps spec fuel bound p t
    | .violated t =>
      let own := (typeOf spec t).toList.map (·, p)
      let conds := match typeOf spec t with
        | some d => match spec.findViolationCond d with
          | some cs => depsList spec fuel (spec.components d) p cs
          | none => []
        | none => []
      own ++ conds ++ deps spec fuel bound p t
    | .enabled t =>
      let own := (typeOf spec t).toList.map (·, p)
      let more := match typeOf spec t with
        | some d => enabledDeps spec fuel [] p d
        | none => []
      own ++ more ++ deps spec fuel bound p t
    | .not t => deps spec fuel bound .neg t
    | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b | .mult a b | .mod a b
    | .div a b | .sub a b | .add a b | .eq a b | .neq a b | .when a b =>
      deps spec fuel bound p a ++ deps spec fuel bound p b
    | .heldFor t d => deps spec fuel bound p t ++ deps spec fuel bound p d
    | .exists_ xs t => binderDeps spec xs p ++ deps spec fuel (bound ++ xs) p t
    | .forall_ xs t | .count xs t | .sum xs t | .max xs t | .min xs t =>
      binderDeps spec xs .neg ++ deps spec fuel (bound ++ xs) .neg t
    | .project t _ | .tag t _ | .untag t => deps spec fuel bound p t
def depsArgs (spec : Spec) : Nat → List Var → Pol → Args → List Dep
  | 0, _, _, _ => []
  | fuel + 1, bound, p, args =>
    match args with
    | .pos ts => depsList spec fuel bound p ts
    | .named ms => depsMods spec fuel bound p ms
def depsList (spec : Spec) : Nat → List Var → Pol → List Term → List Dep
  | 0, _, _, _ => []
  | _, _, _, [] => []
  | fuel + 1, bound, p, t :: ts => deps spec fuel bound p t ++ depsList spec fuel bound p ts
def depsMods (spec : Spec) : Nat → List Var → Pol → List (Var × Term) → List Dep
  | 0, _, _, _ => []
  | _, _, _, [] => []
  | fuel + 1, bound, p, (_, t) :: ms => deps spec fuel bound p t ++ depsMods spec fuel bound p ms
/-- What `Enabled(d(...))` reads beyond `d` itself: `d`'s conditions and the
enabledness of every act it syncs with. -/
def enabledDeps (spec : Spec) : Nat → List DomId → Pol → DomId → List Dep
  | 0, _, _, _ => []
  | fuel + 1, seen, p, d =>
    if seen.contains d then [] else
    match spec.findDecl d with
    | none => []
    | some tspec =>
      let xs := spec.components d
      let conds := depsList spec fuel xs p tspec.conditions
      let more := match tspec.kind with
        | .act a =>
          -- syncs, Valid when (consulted through Except under), and the Except under acts themselves
          a.syncs.flatMap (fun s =>
            binderDeps spec s.xs p ++ deps spec fuel (xs ++ s.xs) p s.t ++
            (match typeOf spec s.t with
              | some d' => [(d', p)] ++ enabledDeps spec fuel (d :: seen) p d'
              | none => [])) ++
          depsList spec fuel xs p a.validWhen ++
          a.exceptUnder.flatMap (fun d' => [(d', p)] ++ enabledDeps spec fuel (d :: seen) p d')
        | _ => []
      conds ++ more
end

/-- The dependencies of a derived type: its derivation rules, its own conditions
(derived instances must satisfy them), and its domain constraint. -/
def typeDeps (spec : Spec) (d : DomId) (tspec : TypeSpec) : List Dep :=
  let xs := spec.components d
  let fuel := 1000
  let fromDerivations := tspec.derivation.flatMap fun
    | .dv ys t => binderDeps spec ys .pos ++ deps spec fuel ys .pos t
    | .holdsWhen t => binderDeps spec xs .pos ++ deps spec fuel xs .pos t
  let fromConds := depsList spec fuel xs .pos tspec.conditions
  let fromFilter := deps spec fuel xs .pos tspec.domainConstraint
  fromDerivations ++ fromConds ++ fromFilter

/-- Strata of the derived types, lowest first, or the types on a negative cycle. -/
def strata (spec : Spec) : Except (List DomId) (List (List DomId)) :=
  let derived := spec.derivedTypes
  let edges : List (DomId × Dep) := derived.flatMap fun d =>
    match spec.findDecl d with
    | some t => (typeDeps spec d t).filter (fun e => derived.contains e.1) |>.map (d, ·)
    | none => []
  -- reachability by repeated relaxation
  let direct (a b : DomId) : Bool := edges.any fun (x, (y, _)) => x == a && y == b
  let rec closure (fuel : Nat) (reach : List (DomId × DomId)) : List (DomId × DomId) :=
    match fuel with
    | 0 => reach
    | fuel + 1 =>
      let more := reach.flatMap fun (a, b) => reach.filterMap fun (b', c) =>
        if b == b' && !reach.contains (a, c) then some (a, c) else none
      let more := more.eraseDups
      if more.isEmpty then reach else closure fuel (reach ++ more)
  let reach := closure (derived.length * derived.length + 1) (edges.map fun (a, (b, _)) => (a, b))
  let reaches (a b : DomId) : Bool := a == b || reach.contains (a, b)
  let bad := edges.filter fun (a, (b, p)) => p == .neg && reaches b a
  if !bad.isEmpty then .error (bad.map (·.1) |>.eraseDups)
  else
    -- order: a type comes after everything it reaches that does not reach it back
    let rec layers (fuel : Nat) (pending done : List DomId) (acc : List (List DomId)) : List (List DomId) :=
      match fuel with
      | 0 => acc ++ [pending]
      | fuel + 1 =>
        if pending.isEmpty then acc else
        let ready := pending.filter fun d => pending.all fun e =>
          e == d || !(direct d e || reach.contains (d, e)) || reaches e d
        if ready.isEmpty then acc ++ [pending]
        else
          -- group mutually reachable ready types into one stratum each
          let groups := ready.foldl (fun (gs : List (List DomId)) d =>
            match gs.findIdx? (fun g => g.any fun e => reaches d e && reaches e d) with
            | some i => gs.set i (gs[i]! ++ [d])
            | none => gs ++ [[d]]) []
          layers fuel (pending.filter (fun d => !ready.contains d)) (done ++ ready) (acc ++ groups)
    .ok (layers (derived.length + 1) derived [] [])

end Stratify

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
  match c with
  | .holdsWhen t =>
    match tspec.domain with
    | .products xs => dyn xs (.when (.app d (.named [])) t)
    | _ => dyn [⟨d, ""⟩] (.when (.ref ⟨d, ""⟩) t)
  | .dv xs t => dyn xs t

def runM {α} (spec : Spec) (state : State) (m : M α) : Except RuntimeError (List α) :=
  m.run ⟨spec, state⟩ []

/-- One pass over the derivation clauses of one type; the state and whether it grew.
`prev` are the derived facts before rebasing, whose stamps re-derived facts keep (D7). -/
def passType (spec : Spec) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    List Derivation → State → Except RuntimeError (State × Bool)
  | [], s => .ok (s, false)
  | c :: cs, s =>
    match runM spec s (deriveClause d tspec c) with
    | .error e => .error e
    | .ok ress =>
      match State.deriveAll prev s ress.flatten with
      | (s1, ch) =>
        match passType spec prev d tspec cs s1 with
        | .error e => .error e
        | .ok (s2, ch2) => .ok (s2, ch || ch2)

/-- One pass over the types of a stratum; returns the state and whether it grew. -/
def pass (spec : Spec) (prev : List (Tagged × Info)) : List DomId → State → Except RuntimeError (State × Bool)
  | [], s => .ok (s, false)
  | d :: ds, s =>
    match spec.findDecl d with
    | none => pass spec prev ds s
    | some tspec =>
      match passType spec prev d tspec tspec.derivation s with
      | .error e => .error e
      | .ok (s1, ch) =>
        match pass spec prev ds s1 with
        | .error e => .error e
        | .ok (s2, ch2) => .ok (s2, ch || ch2)

def saturateStratum (spec : Spec) (prev : List (Tagged × Info)) (types : List DomId) : Nat → State → Except RuntimeError State
  | 0, _ => .error (.fuelExhausted s!"saturating {", ".intercalate types}")
  | fuel + 1, state =>
    match pass spec prev types state with
    | .error e => .error e
    | .ok (s', changed) => if changed then saturateStratum spec prev types fuel s' else .ok s'

/-- Remove derived facts and recompute them stratum by stratum (eFLINT `rebase_and_sat`,
D6); a fact derived before and again keeps its stamp (D7). -/
def rebaseAndSat (spec : Spec) (strata : List (List DomId)) (state : State) : Except RuntimeError State :=
  let prev := state.derivedFacts
  strata.foldlM (fun s layer => saturateStratum spec prev layer 100000 s) state.rebase

end Saturate

/-! ## Phrases -/

/-- The configuration between phrases: the spec, the state, its strata, and the
duties violated after the last phrase (for D12 reporting). -/
structure Config where
  spec           : Spec := emptySpec
  strata         : List (List DomId) := []
  state          : State := {}
  violatedDuties : List Tagged := []

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
def semPhrase (spec : Spec) (state : State) : Nat → CPhrase → Option Store × List Output
  | 0, _ => (none, [.diag (Diagnostic.error "CHR104" "phrase too deeply nested")])
  | fuel + 1, p =>
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ⟨spec, state⟩ []
    match p with
    | .onlyDecls init => (some init, [])
    | .scenario _ _ => (some [], [])
    | .why xs t =>
      match run (foreach M.fuel xs (whenTagged (eval M.fuel t) pure)) with
      | .error e => (none, [diagOf e])
      | .ok tess =>
        let lines := tess.flatten.map fun te =>
          match state.lookup te with
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
    | .create xs t => effect (.cAll xs t)
    | .terminate xs t => effect (.tAll xs t)
    | .obfuscate xs t => effect (.oAll xs t)
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
      let rs := ps.map (semPhrase spec state fuel)
      let outs := rs.flatMap (·.2)
      if rs.all (·.1.isSome) then (some (Store.unions (rs.filterMap (·.1))), outs)
      else (none, outs)
where
  effect (e : Effect) : Option Store × List Output :=
    match (evalEffect M.fuel e).run ⟨spec, state⟩ [] with
    | .error err => (none, [diagOf err])
    | .ok stores => (some (Store.unions stores), [])

/-- Apply a store, saturate, and find the violations (eFLINT `new_context`). `state1`
is the state after the phrase's assignments (and any clock change). -/
def newContext (cfg : Config) (spec : Spec) (strata : List (List DomId)) (state1 : State) :
    Option Config × List Output :=
  match Saturate.rebaseAndSat spec strata state1 with
  | .error e => (none, [diagOf e])
  | .ok state' =>
    let duties := state'.holdsList.filter fun te => match spec.kindOf te.2 with
      | some (.duty _) => true
      | _ => false
    let run {α} (m : M α) : Except RuntimeError (List α) := m.run ⟨spec, state'⟩ []
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

/-- Run one phrase: resolve it against the configuration, evaluate, apply, saturate,
report. On failure the configuration is returned unchanged. -/
def runPhrase (cfg : Config) (p : Phrase) : Config × List Output :=
  match resolvePhrase cfg.spec p with
  | .error ds => (cfg, ds.map .diag)
  | .ok (spec', cp, warnings) =>
    let warnOuts := warnings.map Output.diag
    match Stratify.strata spec' with
    | .error cycle =>
      (cfg, warnOuts ++ [.diag (Diagnostic.error "CHR020"
        s!"derivation is not stratifiable: {", ".intercalate cycle} depend on their own absence (through Not, Forall, or an aggregate)")])
    | .ok strata =>
      -- the clock (D7): environment input applied before saturation, never a transition
      let clock : Except RuntimeError (Option Int) := match cp with
        | .tick => .ok (some (cfg.state.time + 1))
        | .setTime t =>
          match (M.eval M.fuel t).run ⟨spec', cfg.state⟩ [] with
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
      let (store?, outs) := Interp.semPhrase spec' state0 1000 cp
      let outs := match newTime with
        | some t => Output.timeSet t :: outs
        | none => outs
      match store? with
      | none => (cfg, warnOuts ++ outs)
      | some store =>
        let state1 := State.makeAssignments spec' store state0
        let (cfg'?, outs2) := Interp.newContext cfg spec' strata state1
        match cfg'? with
        | none => (cfg, warnOuts ++ outs ++ outs2)
        | some cfg' => (cfg', warnOuts ++ outs ++ outs2)

/-! ## Exploration (plan §2.2.7): bounded search over acts from a state -/

namespace Explore

open M

/-- Every instance of every act type that is enabled in the configuration: the
candidates for a next step under lawful behaviour. -/
def enabledActs (cfg : Config) : Except RuntimeError (List Tagged) := do
  let spec := cfg.spec
  let acts := spec.decls.filterMap fun (p : DomId × TypeSpec) => match p.2.kind with
    | .act _ => some p.1
    | _ => none
  acts.foldlM (fun acc d => do
    let xs := spec.components d
    let m : M (List Tagged) := results (scope M.fuel xs (whenTagged (eval M.fuel (.app d (.named []))) pure))
    let insts ← (ignoreMissingInput m).run ⟨spec, cfg.state⟩ []
    let insts := insts.flatten
    let enabled ← insts.filterMapM fun te => do
      let r ← (ignoreMissingInput (isEnabled M.fuel te)).run ⟨spec, cfg.state⟩ []
      pure (if r.any id then some te else none)
    pure (acc ++ enabled)) []

/-- Perform one act instance from a configuration (the `trigger` step without a phrase). -/
def perform (cfg : Config) (te : Tagged) : Except RuntimeError Config := do
  let infos ← (instantiateTrans M.fuel [] te).run ⟨cfg.spec, cfg.state⟩ []
  let store := Store.unions (infos.map (·.assignments))
  let state1 := State.makeAssignments cfg.spec store { cfg.state with step := cfg.state.step + 1 }
  let state' ← Saturate.rebaseAndSat cfg.spec cfg.strata state1
  pure { cfg with state := state' }

/-- The invariants that do not hold in a configuration. -/
def violatedInvariants (cfg : Config) : List DomId :=
  cfg.spec.invariants.filter fun d =>
    let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
    match (ignoreMissingInput (checkFalse (eval M.fuel term))).run ⟨cfg.spec, cfg.state⟩ [] with
    | .ok rs => !rs.isEmpty
    | .error _ => false

/-- A canonical key of a state: the instances that hold, as sorted text. -/
def stateKey (s : State) : String :=
  let names := s.holdsList.map Tagged.pp
  String.intercalate "|" (names.toArray.qsort (· < ·)).toList

/-- The outcome of an exploration. -/
inductive Result where
  /-- No invariant violated within the bound; how many distinct states were visited. -/
  | safe (visited : Nat)
  | violated (invariant : DomId) (trace : List Tagged) (visited : Nat)
  | error (e : RuntimeError)

/-- Breadth-first search over enabled acts from `cfg`, up to `depth` steps and `cap`
visited states, returning the shortest violating trace. Deterministic: candidates
are taken in declaration order, so the same program and depth always give the same
answer (the "seed" of plan §2.2.7 is the declaration order). -/
def bfs (cfg : Config) (depth cap : Nat) : Result :=
  match violatedInvariants cfg with
  | d :: _ => .violated d [] 1
  | [] =>
    let rec go (frontier : List (Config × List Tagged)) (seen : List String) (fuel : Nat) : Result :=
      match fuel with
      | 0 => .safe seen.length
      | fuel + 1 =>
        if frontier.isEmpty then .safe seen.length else
        -- expand the whole frontier one level
        let step := frontier.foldl (fun (acc : Except RuntimeError (List (Config × List Tagged) × List String × Option (DomId × List Tagged))) (c, trace) =>
          match acc with
          | .error e => .error e
          | .ok (next, seen, some v) => .ok (next, seen, some v)
          | .ok (next, seen, none) =>
            match enabledActs c with
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
