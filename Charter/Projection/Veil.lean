import Charter.Core.Semantics
import Charter.Core.Views

/-!
# Charter.Projection.Veil — Veil 2.0 State-Machine Projection & Preservation Theorem

Lowers any normative specification `L : Law σ` from `Charter.Core` into a Veil 2.0
transition-system and safety-invariant specification (`VeilSpec σ`), together
with a machine-checked soundness and completeness theorem
(`veil_projection_sound_and_complete`) establishing that:

1. **Trace Authorization Equivalence:** A trace `tr` is accepted by the lowered
   Veil transition system `compileToVeil L` if and only if `Authorized L tr`
   holds in `Charter.Core.Semantics`.
2. **Institutional State Preservation:** Executing `tr` under `veilStep` yields
   the exact same `LegalState σ` as `stateAfter L tr`.
3. **Stepwise Compliance Equivalence:** Every per-event safety invariant check
   in `compileToVeil L` agrees with `complies L tr i`.

Two machine projections are provided:
* `authorizedMachine L` (`compileToVeil L`): restricts transitions to complying
  events, matching the derived `Authorized` state machine.
* `adversarialMachine L`: retains unlawful events with explicit violation
  recording (`veilViolations`), re-adding the excluded transitions listed by
  `Law.operationalView` so model checkers can verify resilience against breaches.
-/

namespace Charter

variable {σ : Sig}

/-! ## 1. Veil 2.0 Transition-System Representation -/

/-- A lowered Veil 2.0 action transition over signature `σ`.
Each institutional power `p` compiles to a guarded transition with its
holder, trigger, validity condition, defeating immunities, and pre-resolved
remedial facts (`remediesOf L p`). -/
structure VeilTransition (σ : Sig) where
  id                  : String
  clause              : String
  holder              : Who σ
  trigger             : Conduct σ
  valid               : Cond σ
  defeatingImmunities : List (Immunity σ) := []
  adds                : List σ.Fact := []
  addsFor             : List (σ.Fact × Time) := []
  addsByActor         : List (σ.Actor × σ.Fact) := []
  removes             : List σ.Fact := []
  condAdds            : List (Cond σ × σ.Fact) := []
  remedies            : List σ.Fact := []

/-- A lowered Veil 2.0 safety/compliance invariant derived from an Charter `Duty`.
Captures the duty's normative structure (bearer, beneficiary, activation condition,
demand, scope exceptions, power exceptions, and overriding duty conditions). -/
structure VeilInvariant (σ : Sig) where
  id               : String
  clause           : String
  duty             : Duty σ
  overridingDuties : List (Duty σ) := []

/-- A Veil 2.0 transition-system and safety-invariant specification over signature `σ`.
- `init`: initial institutional state (`LegalState σ`).
- `transitions`: guarded state transitions lowered from `Law.powers` and `Law.immunities`.
- `invariants`: transition compliance / safety invariants lowered from `Law.duties`.
- `adversarialMode`: when `false` (`authorizedMachine`), traces must satisfy all
  compliance invariants at every step; when `true` (`adversarialMachine`), unlawful
  events are permitted and logged as explicit violation flags. -/
structure VeilSpec (σ : Sig) where
  init            : LegalState σ
  transitions     : List (VeilTransition σ)
  invariants      : List (VeilInvariant σ)
  immunities      : List (Immunity σ) := []
  adversarialMode : Bool := false

/-- Alias matching the operational state-machine terminology in the design plan. -/
abbrev OpMachine (σ : Sig) := VeilSpec σ

/-! ## 2. Compilation from `Law σ` to `VeilSpec σ` -/

/-- Compile a single institutional `Power` into a `VeilTransition`. -/
def compileTransition (L : Law σ) (p : Power σ) : VeilTransition σ :=
  { id := p.id
    clause := p.source.clause
    holder := p.holder
    trigger := p.trigger
    valid := p.valid
    defeatingImmunities := L.immunities
    adds := p.adds
    addsFor := p.addsFor
    addsByActor := p.addsByActor
    removes := p.removes
    condAdds := p.condAdds
    remedies := remediesOf L p }

/-- Compile a single institutional `Duty` into a `VeilInvariant`. -/
def compileInvariant (L : Law σ) (d : Duty σ) : VeilInvariant σ :=
  { id := d.id
    clause := d.source.clause
    duty := d
    overridingDuties := L.duties }

/-- Lower a normative `Law σ` into a Veil 2.0 transition system and safety specification. -/
def compileToVeil (L : Law σ) : VeilSpec σ :=
  { init := L.init
    transitions := L.powers.map (compileTransition L)
    invariants := L.duties.map (compileInvariant L)
    immunities := L.immunities
    adversarialMode := false }

/-- The authorized operational machine projection: transitions are accepted iff
every compliance invariant holds. -/
def authorizedMachine (L : Law σ) : VeilSpec σ :=
  compileToVeil L

/-- The adversarial operational machine projection: re-adds unlawful events so a
model checker can explore breach traces with explicit violation flags. -/
def adversarialMachine (L : Law σ) : VeilSpec σ :=
  { compileToVeil L with adversarialMode := true }

/-! ## 3. Veil Operational Semantics (`veilStep`, `veilTraceState`, `veilAcceptsTrace`) -/

/-- Does a lowered Veil transition's guard hold for event `e` at state `ls`? -/
def VeilTransition.enabled (tr : VeilTransition σ) (ls : LegalState σ) (e : Event σ) : Bool :=
  tr.holder.mem e.who ls e.t &&
  tr.trigger.matchesAct e &&
  tr.valid.eval ls e.t &&
  !(tr.defeatingImmunities.any fun i =>
      i.against.contains tr.id && i.active.eval ls e.t && !i.unlessCond.eval ls e.t)

/-- Apply a single enabled Veil transition at pre-state `ls` and event `e` onto state `s`. -/
def VeilTransition.apply (tr : VeilTransition σ) (ls s : LegalState σ) (e : Event σ) : LegalState σ :=
  let s := s.filter fun q => !tr.removes.contains q.1
  let cond := (tr.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)
  let byAct := (tr.addsByActor.filter fun af => af.1 == e.who).map (·.2)
  let perm := (tr.adds ++ byAct ++ tr.remedies ++ cond).map (fun f => (f, e.t, none))
  let timed := tr.addsFor.map (fun (f, d) => (f, e.t, some (e.t + d)))
  s ++ perm ++ timed

/-- Look up a lowered Veil transition by power id. -/
def VeilSpec.transitionById (spec : VeilSpec σ) (pid : String) : Option (VeilTransition σ) :=
  spec.transitions.find? fun t => t.id == pid

/-- Does event `e` at state `ls` validly trigger the transition named `pid` in `spec`? -/
def VeilSpec.exercisesTransition (spec : VeilSpec σ) (ls : LegalState σ) (e : Event σ) (pid : String) : Bool :=
  match spec.transitionById pid with
  | none => false
  | some t => t.enabled ls e

/-- Single-step state transition in the Veil projection: every enabled
transition in `spec.transitions` applies in order. -/
def veilStep (spec : VeilSpec σ) (ls : LegalState σ) (e : Event σ) : LegalState σ :=
  (spec.transitions.filter fun t => t.enabled ls e).foldl
    (fun s t => t.apply ls s e) ls

/-- Institutional state reached after executing trace `tr` in `spec`. -/
def veilTraceState (spec : VeilSpec σ) (tr : Trace σ) : LegalState σ :=
  tr.foldl (veilStep spec) spec.init

/-- Institutional state immediately before event index `i` of `tr` in `spec`. -/
def veilStateBefore (spec : VeilSpec σ) (tr : Trace σ) (i : Nat) : LegalState σ :=
  veilTraceState spec (tr.take i)

/-- Evaluate conduct against a `VeilSpec` transition system. -/
def veilEvalConduct (spec : VeilSpec σ) (ls : LegalState σ) (e : Event σ) : Conduct σ → Bool
  | .act a => e.act == a
  | .anyOf as => as.contains e.act
  | .exerciseOf pid => spec.exercisesTransition ls e pid
  | .not c => !veilEvalConduct spec ls e c
  | .and a b => veilEvalConduct spec ls e a && veilEvalConduct spec ls e b
  | .or a b => veilEvalConduct spec ls e a || veilEvalConduct spec ls e b

/-- Is a lowered Veil safety invariant in force at `ls`, `now`? -/
def VeilInvariant.inForce (inv : VeilInvariant σ) (ls : LegalState σ) (now : Time) : Bool :=
  inv.duty.active.eval ls now &&
  !(inv.duty.overriddenBy.any fun oid =>
      inv.overridingDuties.any fun d' => d'.id == oid && d'.active.eval ls now)

/-- Does event `e` at state `ls` violate safety invariant `inv` in `spec`? -/
def VeilInvariant.violatedBy (spec : VeilSpec σ) (inv : VeilInvariant σ)
    (ls : LegalState σ) (e : Event σ) : Bool :=
  match inv.duty.demand with
  | .forbid c =>
      inv.duty.bearer.mem e.who ls e.t &&
      inv.inForce ls e.t &&
      !inv.duty.unlessCond.eval ls e.t &&
      veilEvalConduct spec ls e c &&
      !(inv.duty.unlessPower.any fun pid => spec.exercisesTransition ls e pid)
  | .require _ _ => false

/-- First time at which safety invariant `inv`'s activation condition became true along `tr`. -/
def veilActivatedAt (spec : VeilSpec σ) (tr : Trace σ) (inv : VeilInvariant σ) : Option Time :=
  let rec go (ls : LegalState σ) : List (Event σ) → Option Time
    | [] => none
    | e :: rest =>
        let ls' := veilStep spec ls e
        if inv.duty.active.eval ls' e.t then some e.t else go ls' rest
  if inv.duty.active.eval spec.init 0 then some 0 else go spec.init tr

/-- Is a time-bounded requirement invariant `inv` violated as of time `now` along `tr` in `spec`? -/
def VeilInvariant.requirementViolated (spec : VeilSpec σ) (inv : VeilInvariant σ)
    (tr : Trace σ) (now : Time) : Bool :=
  match inv.duty.demand with
  | .forbid _ => false
  | .require c w =>
    match veilActivatedAt spec tr inv with
    | none => false
    | some t0 =>
      decide (t0 + w < now) &&
      !((tr.zipIdx).any fun (e, i) =>
          let ls := veilStateBefore spec tr i
          inv.duty.bearer.mem e.who ls e.t && t0 ≤ e.t && e.t ≤ t0 + w &&
          veilEvalConduct spec ls e c)

/-- Time-bounded requirement invariants violated as of time `now` at the end of `tr` in `spec`. -/
def veilLapsedRequirements (spec : VeilSpec σ) (tr : Trace σ) (now : Time) : List String :=
  (spec.invariants.filter (fun inv => inv.requirementViolated spec tr now)).map (·.id)

/-- Does event `e` at state `ls` satisfy all safety invariants of `spec`? -/
def veilEventComplies (spec : VeilSpec σ) (ls : LegalState σ) (e : Event σ) : Bool :=
  spec.invariants.all fun inv => !inv.violatedBy spec ls e

/-- Does step `i` of trace `tr` satisfy all safety invariants of `spec`? -/
def veilStepComplies (spec : VeilSpec σ) (tr : Trace σ) (i : Nat) : Bool :=
  match tr[i]? with
  | none => true
  | some e => veilEventComplies spec (veilStateBefore spec tr i) e

/-- Violation log recorded by the Veil specification along `tr` (used by
`adversarialMachine` to expose breaches as explicit flags). -/
def veilViolations (spec : VeilSpec σ) (tr : Trace σ) : List (Nat × String) :=
  (tr.zipIdx).foldl (fun acc (e, i) =>
    acc ++ (spec.invariants.filter (fun inv => inv.violatedBy spec (veilStateBefore spec tr i) e)).map
      fun inv => (i, inv.id)) []

/-- A trace `tr` is accepted by the Veil specification `spec` when either
`spec.adversarialMode` is enabled (`adversarialMachine`, which permits unlawful
events to occur while recording breaches in `veilViolations`) or every event along
`tr` satisfies all safety invariants (`veilStepComplies`). -/
def veilAcceptsTrace (spec : VeilSpec σ) (tr : Trace σ) : Prop :=
  ∀ i, i < tr.length → (spec.adversarialMode || veilStepComplies spec tr i) = true

instance (spec : VeilSpec σ) (tr : Trace σ) : Decidable (veilAcceptsTrace spec tr) := by
  unfold veilAcceptsTrace; infer_instance

/-! ## 4. Soundness and Completeness of the Veil 2.0 Projection -/

private theorem find?_compileTransition (L : Law σ) (pid : String) (ps : List (Power σ)) :
    (ps.map (compileTransition L)).find? (fun t => t.id == pid) =
    (ps.find? (fun p => p.id == pid)).map (compileTransition L) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.find?_cons]
    have hid : (compileTransition L p).id = p.id := rfl
    rw [hid]
    cases (p.id == pid)
    · exact ih
    · rfl

/-- Transition lookup and guard evaluation in `compileToVeil L` agree with `isValidExerciseOf L`. -/
theorem veilExercisesTransition_compileToVeil (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (pid : String) :
    (compileToVeil L).exercisesTransition ls e pid = isValidExerciseOf L ls e pid := by
  unfold VeilSpec.exercisesTransition VeilSpec.transitionById isValidExerciseOf Law.powerById compileToVeil
  simp only [find?_compileTransition]
  cases L.powers.find? (fun p => p.id == pid) with
  | none => rfl
  | some p => rfl

/-- Conduct evaluation in `compileToVeil L` agrees with `Conduct.eval L`. -/
theorem veilEvalConduct_compileToVeil (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (c : Conduct σ) :
    veilEvalConduct (compileToVeil L) ls e c = c.eval L ls e := by
  induction c with
  | act a => rfl
  | anyOf as => rfl
  | exerciseOf pid => exact veilExercisesTransition_compileToVeil L ls e pid
  | not c ih => simp [veilEvalConduct, Conduct.eval, ih]
  | and a b iha ihb => simp [veilEvalConduct, Conduct.eval, iha, ihb]
  | or a b iha ihb => simp [veilEvalConduct, Conduct.eval, iha, ihb]

/-- Invariant violation in `compileToVeil L` agrees with `breaches L`. -/
theorem veilInvariantViolatedBy_compileToVeil (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (d : Duty σ) :
    (compileInvariant L d).violatedBy (compileToVeil L) ls e = breaches L ls e d := by
  unfold VeilInvariant.violatedBy breaches compileInvariant VeilInvariant.inForce dutyInForce
  cases d.demand with
  | forbid c =>
    simp only [veilEvalConduct_compileToVeil, veilExercisesTransition_compileToVeil]
  | require c w => rfl

private theorem all_compileInvariant (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (ds : List (Duty σ)) :
    (ds.map (compileInvariant L)).all (fun inv => !inv.violatedBy (compileToVeil L) ls e) =
    ds.all (fun d => !breaches L ls e d) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.all_cons, veilInvariantViolatedBy_compileToVeil, ih]

/-- Per-event compliance in `compileToVeil L` agrees with duty non-breach in `L`. -/
theorem veilEventComplies_compileToVeil (L : Law σ) (ls : LegalState σ) (e : Event σ) :
    veilEventComplies (compileToVeil L) ls e = (L.duties.all fun d => !breaches L ls e d) :=
  all_compileInvariant L ls e L.duties

private theorem foldl_filter_compileTransition (L : Law σ) (ls s : LegalState σ)
    (e : Event σ) (ps : List (Power σ)) :
    ((ps.map (compileTransition L)).filter (fun t => t.enabled ls e)).foldl
      (fun acc t => t.apply ls acc e) s =
    (ps.filter (fun p =>
      p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
      !defeatedByImmunity L ls e.t p.id)).foldl
      (fun acc p =>
        let acc := acc.filter fun q => !p.removes.contains q.1
        let cond := (p.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)
        let byAct := (p.addsByActor.filter fun af => af.1 == e.who).map (·.2)
        let perm := (p.adds ++ byAct ++ remediesOf L p ++ cond).map (fun f => (f, e.t, none))
        let timed := p.addsFor.map (fun (f, d) => (f, e.t, some (e.t + d)))
        acc ++ perm ++ timed) s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.filter_cons]
    have hen : (compileTransition L p).enabled ls e =
        (p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
         !defeatedByImmunity L ls e.t p.id) := rfl
    rw [hen]
    cases (p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
           !defeatedByImmunity L ls e.t p.id)
    · exact ih s
    · exact ih ((compileTransition L p).apply ls s e)

/-- Single-step state transition in `compileToVeil L` is identical to `step L`. -/
theorem veilStep_compileToVeil (L : Law σ) (ls : LegalState σ) (e : Event σ) :
    veilStep (compileToVeil L) ls e = step L ls e :=
  foldl_filter_compileTransition L ls ls e L.powers

private theorem foldl_veilStep_compileToVeil (L : Law σ) (ls : LegalState σ) (tr : Trace σ) :
    tr.foldl (veilStep (compileToVeil L)) ls = tr.foldl (step L) ls := by
  induction tr generalizing ls with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.foldl_cons, veilStep_compileToVeil, ih]

/-- Full-trace state in `compileToVeil L` is identical to `stateAfter L`. -/
theorem veilTraceState_compileToVeil (L : Law σ) (tr : Trace σ) :
    veilTraceState (compileToVeil L) tr = stateAfter L tr :=
  foldl_veilStep_compileToVeil L L.init tr

/-- Pre-event state at index `i` in `compileToVeil L` is identical to `stateBefore L`. -/
theorem veilStateBefore_compileToVeil (L : Law σ) (tr : Trace σ) (i : Nat) :
    veilStateBefore (compileToVeil L) tr i = stateBefore L tr i :=
  veilTraceState_compileToVeil L (tr.take i)

/-- Stepwise compliance in `compileToVeil L` is identical to `complies L`. -/
theorem veilStepComplies_compileToVeil (L : Law σ) (tr : Trace σ) (i : Nat) :
    veilStepComplies (compileToVeil L) tr i = complies L tr i := by
  unfold veilStepComplies complies
  cases tr[i]? with
  | none => rfl
  | some e =>
    dsimp only
    rw [veilStateBefore_compileToVeil, veilEventComplies_compileToVeil]

/-- Trace acceptance in `compileToVeil L` is equivalent to `Authorized L`. -/
theorem veilAcceptsTrace_compileToVeil (L : Law σ) (tr : Trace σ) :
    veilAcceptsTrace (compileToVeil L) tr ↔ Authorized L tr := by
  unfold veilAcceptsTrace Authorized
  have hadv : (compileToVeil L).adversarialMode = false := rfl
  simp only [hadv, Bool.false_or]
  constructor
  · intro h i hi
    rw [← veilStepComplies_compileToVeil]
    exact h i hi
  · intro h i hi
    rw [veilStepComplies_compileToVeil]
    exact h i hi

private theorem filter_map_compileInvariant (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (i : Nat) (ds : List (Duty σ)) :
    ((ds.map (compileInvariant L)).filter (fun inv => inv.violatedBy (compileToVeil L) ls e)).map
      (fun inv => (i, inv.id)) =
    (ds.filter (breaches L ls e)).map (fun d => (i, d.id)) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.filter_cons, veilInvariantViolatedBy_compileToVeil]
    cases breaches L ls e d
    · exact ih
    · simp only [↓reduceIte, List.map_cons, ih]
      rfl

private theorem foldl_violations_compileToVeil (L : Law σ) (tr : Trace σ)
    (evs : List (Event σ × Nat)) (acc : List (Nat × String)) :
    evs.foldl (fun a (e, i) =>
      a ++ ((compileToVeil L).invariants.filter
        (fun inv => inv.violatedBy (compileToVeil L) (veilStateBefore (compileToVeil L) tr i) e)).map
        fun inv => (i, inv.id)) acc =
    evs.foldl (fun a (e, i) =>
      a ++ (L.duties.filter (breaches L (stateBefore L tr i) e)).map fun d => (i, d.id)) acc := by
  induction evs generalizing acc with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨e, i⟩
    dsimp only [List.foldl_cons]
    have hmap : ((compileToVeil L).invariants.filter
        (fun inv => inv.violatedBy (compileToVeil L) ( stateBefore L tr i ) e)).map
        (fun inv => (i, inv.id)) =
        (L.duties.filter (breaches L (stateBefore L tr i) e)).map (fun d => (i, d.id)) :=
      filter_map_compileInvariant L (stateBefore L tr i) e i L.duties
    rw [veilStateBefore_compileToVeil, hmap]
    exact ih _

/-- The violation log recorded by `compileToVeil L` is identical to `violations L`. -/
theorem veilViolations_compileToVeil (L : Law σ) (tr : Trace σ) :
    veilViolations (compileToVeil L) tr = violations L tr :=
  foldl_violations_compileToVeil L tr tr.zipIdx []

private theorem veilActivatedAt_go_compileToVeil (L : Law σ) (d : Duty σ)
    (ls : LegalState σ) (evs : List (Event σ)) :
    veilActivatedAt.go (compileToVeil L) (compileInvariant L d) ls evs =
    activatedAt.go L d ls evs := by
  induction evs generalizing ls with
  | nil => rfl
  | cons e rest ih =>
    unfold veilActivatedAt.go activatedAt.go
    have hd : (compileInvariant L d).duty = d := rfl
    dsimp only
    rw [hd, veilStep_compileToVeil, ih (step L ls e)]

/-- Activation time of a lowered duty invariant in `compileToVeil L` agrees with `activatedAt L`. -/
theorem veilActivatedAt_compileToVeil (L : Law σ) (tr : Trace σ) (d : Duty σ) :
    veilActivatedAt (compileToVeil L) tr (compileInvariant L d) = activatedAt L tr d := by
  unfold veilActivatedAt activatedAt
  have hd : (compileInvariant L d).duty = d := rfl
  have hinit : (compileToVeil L).init = L.init := rfl
  rw [hd, hinit, veilActivatedAt_go_compileToVeil]

private theorem any_requirement_compileToVeil (L : Law σ) (tr : Trace σ)
    (d : Duty σ) (c : Conduct σ) (t0 w : Time) (evs : List (Event σ × Nat)) :
    evs.any (fun (e, i) =>
      let ls := veilStateBefore (compileToVeil L) tr i
      d.bearer.mem e.who ls e.t && decide (t0 ≤ e.t) && decide (e.t ≤ t0 + w) &&
      veilEvalConduct (compileToVeil L) ls e c) =
    evs.any (fun (e, i) =>
      let ls := stateBefore L tr i
      d.bearer.mem e.who ls e.t && decide (t0 ≤ e.t) && decide (e.t ≤ t0 + w) &&
      c.eval L ls e) := by
  simp only [veilStateBefore_compileToVeil, veilEvalConduct_compileToVeil]

/-- Time-bounded requirement violation in `compileToVeil L` agrees with `requirementViolated L`. -/
theorem veilRequirementViolated_compileToVeil (L : Law σ) (tr : Trace σ)
    (now : Time) (d : Duty σ) :
    (compileInvariant L d).requirementViolated (compileToVeil L) tr now =
    requirementViolated L tr now d := by
  unfold VeilInvariant.requirementViolated requirementViolated
  have hd : (compileInvariant L d).duty = d := rfl
  rw [hd]
  cases d.demand with
  | forbid _ => rfl
  | require c w =>
    dsimp only
    rw [veilActivatedAt_compileToVeil]
    cases activatedAt L tr d with
    | none => rfl
    | some t0 =>
      dsimp only
      rw [any_requirement_compileToVeil]

private theorem filter_map_lapsed_compileInvariant (L : Law σ) (tr : Trace σ)
    (now : Time) (ds : List (Duty σ)) :
    ((ds.map (compileInvariant L)).filter
      (fun inv => inv.requirementViolated (compileToVeil L) tr now)).map (·.id) =
    (ds.filter (requirementViolated L tr now)).map (·.id) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.filter_cons, veilRequirementViolated_compileToVeil]
    cases requirementViolated L tr now d
    · exact ih
    · simp only [↓reduceIte, List.map_cons, ih]
      rfl

/-- Time-lapsed requirements in `compileToVeil L` agree with `lapsedRequirements L`. -/
theorem veilLapsedRequirements_compileToVeil (L : Law σ) (tr : Trace σ) (now : Time) :
    veilLapsedRequirements (compileToVeil L) tr now = lapsedRequirements L tr now :=
  filter_map_lapsed_compileInvariant L tr now L.duties

/-- **Soundness and Completeness of the Veil 2.0 Projection.**
For every normative specification `L : Law σ` and trace `tr : Trace σ`:
1. `compileToVeil L` accepts `tr` if and only if `Authorized L tr` holds.
2. `veilTraceState (compileToVeil L) tr` equals `stateAfter L tr`.
3. Every step compliance check `veilStepComplies (compileToVeil L) tr i` equals `complies L tr i`. -/
theorem veil_projection_sound_and_complete (L : Law σ) (tr : Trace σ) :
    (veilAcceptsTrace (compileToVeil L) tr ↔ Authorized L tr) ∧
    veilTraceState (compileToVeil L) tr = stateAfter L tr ∧
    (∀ i, veilStepComplies (compileToVeil L) tr i = complies L tr i) :=
  ⟨veilAcceptsTrace_compileToVeil L tr,
   veilTraceState_compileToVeil L tr,
   veilStepComplies_compileToVeil L tr⟩

/-! ## 5. Veil 2.0 Source Renderer (`renderVeil`) -/

/-- Convert a formal identifier such as `"P.SUSPEND"` or `"D.FLOOR.1"` into a
valid Veil 2.0 identifier (`"p_suspend"`, `"d_floor_1"`). Empty strings and
leading digits are prefixed with `'_'` so the result is always a valid identifier. -/
def veilIdent (s : String) : String :=
  match s.data.map (fun c => if c.isAlphanum then c.toLower else '_') with
  | [] => "_unnamed"
  | c :: cs =>
    if c.isDigit then String.mk ('_' :: c :: cs)
    else String.mk (c :: cs)

/-- Render a lowered `VeilTransition` as a Veil 2.0 `action` declaration. -/
def VeilTransition.render [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (t : VeilTransition σ) : String :=
  let immIds := (t.defeatingImmunities.filter fun i => i.against.contains t.id).map (·.id)
  let immGuard := if immIds.isEmpty then "true" else
    String.intercalate " ∧ " (immIds.map fun id => s!"¬{veilIdent id}(now)")
  let addsPerm := t.adds ++ t.remedies
  let addsStr := if addsPerm.isEmpty then "" else
    "\n    " ++ String.intercalate "\n    " (addsPerm.map fun f => s!"holds({rs f}) := true;")
  let timedStr := if t.addsFor.isEmpty then "" else
    "\n    " ++ String.intercalate "\n    " (t.addsFor.map fun (f, d) =>
      s!"holds_until({rs f}, now + {d}) := true;")
  let condStr := if t.condAdds.isEmpty then "" else
    "\n    " ++ String.intercalate "\n    " (t.condAdds.map fun (c, f) =>
      s!"if ({c.render}) then holds({rs f}) := true;")
  let actorStr := if t.addsByActor.isEmpty then "" else
    "\n    " ++ String.intercalate "\n    " (t.addsByActor.map fun (a, f) =>
      s!"if (who == {rs a}) then holds({rs f}) := true;")
  let remStr := if t.removes.isEmpty then "" else
    "\n    " ++ String.intercalate "\n    " (t.removes.map fun f => s!"holds({rs f}) := false;")
  s!"-- [{t.clause}] {t.id}\n" ++
  s!"action {veilIdent t.id}(who : Actor, act : Act, now : Time) = " ++ "{\n" ++
  s!"  require holder({t.holder.render}, who);\n" ++
  s!"  require trigger({t.trigger.render}, act);\n" ++
  s!"  require valid({t.valid.render});\n" ++
  s!"  require {immGuard};{remStr}{addsStr}{timedStr}{condStr}{actorStr}\n" ++
  "}"

/-- Render a lowered `VeilInvariant` as a Veil 2.0 `safety` invariant declaration. -/
def VeilInvariant.render [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (inv : VeilInvariant σ) : String :=
  let d := inv.duty
  let excPow := if d.unlessPower.isEmpty then "false" else
    s!"valid_exercise_of([{String.intercalate ", " (d.unlessPower.map veilIdent)}])"
  let excCond := match d.unlessCond with | .ff => "false" | c => c.render
  let ovr := if d.overriddenBy.isEmpty then "false" else
    s!"active_any([{String.intercalate ", " (d.overriddenBy.map veilIdent)}])"
  let demandExpr := match d.demand with
    | .forbid c => s!"¬conduct({c.render})"
    | .require c w => s!"within_deadline({w}, {c.render})"
  s!"-- [{inv.clause}] {inv.id} (beneficiary: {d.beneficiary.render})\n" ++
  s!"safety [{veilIdent inv.id}] " ++
  s!"(active({d.active.render}) ∧ ¬({ovr}) ∧ ¬({excCond}) ∧ bearer({d.bearer.render}, who)) → " ++
  s!"({demandExpr} ∨ {excPow})"

/-- Render an immunity as a Veil 2.0 helper predicate declaration. -/
def Immunity.renderVeil [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (i : Immunity σ) : String :=
  let exc := match i.unlessCond with | .ff => "false" | c => c.render
  let protectedPowers := String.intercalate ", " (i.against.map veilIdent)
  s!"-- [{i.source.clause}] {i.id}: protects {i.holder.render} against [{protectedPowers}]\n" ++
  s!"ghost {veilIdent i.id}(now : Time) : Bool := ({i.active.render}) ∧ ¬({exc})"

/-- Render a `VeilSpec` as a complete Veil 2.0 module specification. -/
def VeilSpec.render [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (spec : VeilSpec σ) : String :=
  let modeLabel := if spec.adversarialMode then "adversarialMachine" else "authorizedMachine"
  let initLines := spec.init.map fun (f, t0, exp?) =>
    match exp? with
    | none => s!"  holds({rs f}) := true; -- established at t={t0}"
    | some exp => s!"  holds_until({rs f}, {exp}) := true; -- established at t={t0}"
  let immLines := spec.immunities.map Immunity.renderVeil
  let actLines := spec.transitions.map VeilTransition.render
  let invLines := spec.invariants.map VeilInvariant.render
  let advLines := spec.invariants.map fun inv =>
    let d := inv.duty
    let powList := String.intercalate ", " (d.unlessPower.map veilIdent)
    if spec.adversarialMode then
      s!"action breach_{veilIdent inv.id}(who : Actor, act : Act, now : Time) = " ++ "{\n" ++
      s!"  -- [{inv.clause}] adversarial breach of {inv.id}: {d.bearer.render} doing ({d.demand.render}) outside [{powList}]\n" ++
      s!"  breach_recorded(\"{inv.id}\") := true;\n}"
    else
      s!"  -- excluded breach transition for {inv.id} [{inv.clause}]: " ++
      s!"{d.bearer.render} doing ({d.demand.render}) outside [{powList}] → breach_recorded(\"{inv.id}\")"
  "-- ==========================================================================\n" ++
  s!"-- Veil 2.0 Specification (mode: {modeLabel}, generated from Charter.Core)\n" ++
  "-- Preservation guarantee: Charter.veil_projection_sound_and_complete\n" ++
  "-- ==========================================================================\n\n" ++
  "type Actor\ntype Act\ntype Fact\ntype Time = Nat\n\n" ++
  "relation holds(Fact)\n" ++
  "relation holds_until(Fact, Time)\n" ++
  "relation breach_recorded(String)\n\n" ++
  "after_init {\n" ++
  (if initLines.isEmpty then "  -- empty initial state\n" else String.intercalate "\n" initLines ++ "\n") ++
  "}\n\n" ++
  "-- --------------------------------------------------------------------------\n" ++
  "-- Immunities (Defeating Guards)\n" ++
  "-- --------------------------------------------------------------------------\n\n" ++
  (if immLines.isEmpty then "-- (none)\n\n" else String.intercalate "\n\n" immLines ++ "\n\n") ++
  "-- --------------------------------------------------------------------------\n" ++
  "-- Institutional Power Transitions (Valid Exercises)\n" ++
  "-- --------------------------------------------------------------------------\n\n" ++
  (if actLines.isEmpty then "-- (none)\n\n" else String.intercalate "\n\n" actLines ++ "\n\n") ++
  "-- --------------------------------------------------------------------------\n" ++
  "-- Excluded Unlawful Conduct (Re-added in adversarialMachine)\n" ++
  "-- --------------------------------------------------------------------------\n\n" ++
  (if advLines.isEmpty then "-- (none)\n\n" else String.intercalate "\n" advLines ++ "\n\n") ++
  "-- --------------------------------------------------------------------------\n" ++
  "-- Normative Duty Invariants (Authorized Machine Restriction)\n" ++
  "-- --------------------------------------------------------------------------\n\n" ++
  (if invLines.isEmpty then "-- (none)\n" else String.intercalate "\n\n" invLines ++ "\n")

/-- Render a normative `Law σ` into Veil 2.0 state, action, and invariant declarations. -/
def renderVeil [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact] (L : Law σ) : String :=
  (compileToVeil L).render

/-! ## 6. Edge-Case & Adversarial Machine Theorems -/

/-- The empty trace is unconditionally accepted by any Veil specification. -/
theorem veilAcceptsTrace_nil (spec : VeilSpec σ) :
    veilAcceptsTrace spec [] := by
  intro i hi
  cases hi

/-- Executing the empty trace in any Veil specification yields `spec.init`. -/
theorem veilTraceState_nil (spec : VeilSpec σ) :
    veilTraceState spec [] = spec.init := rfl

/-- Executing the empty trace in any Veil specification produces no violations. -/
theorem veilViolations_nil (spec : VeilSpec σ) :
    veilViolations spec [] = [] := rfl

/-- `authorizedMachine L` accepts a trace iff `Authorized L` holds. -/
theorem authorizedMachine_sound_and_complete (L : Law σ) (tr : Trace σ) :
    veilAcceptsTrace (authorizedMachine L) tr ↔ Authorized L tr :=
  veilAcceptsTrace_compileToVeil L tr

/-- `adversarialMachine L` permits all traces (including unlawful ones) so model checkers
can explore breach histories while inspecting `veilViolations`. -/
theorem adversarialMachine_accepts_all (L : Law σ) (tr : Trace σ) :
    veilAcceptsTrace (adversarialMachine L) tr := by
  intro _ _
  rfl

/-- `adversarialMachine L` preserves institutional state transitions identically to `step L`. -/
theorem adversarialMachine_step (L : Law σ) (ls : LegalState σ) (e : Event σ) :
    veilStep (adversarialMachine L) ls e = step L ls e :=
  veilStep_compileToVeil L ls e

/-- `adversarialMachine L` reaches the exact same institutional state as `stateAfter L`. -/
theorem adversarialMachine_traceState (L : Law σ) (tr : Trace σ) :
    veilTraceState (adversarialMachine L) tr = stateAfter L tr :=
  veilTraceState_compileToVeil L tr

private theorem adversarialMachine_evalConduct (L : Law σ) (ls : LegalState σ)
    (e : Event σ) (c : Conduct σ) :
    veilEvalConduct (adversarialMachine L) ls e c =
    veilEvalConduct (compileToVeil L) ls e c := by
  induction c with
  | act _ => rfl
  | anyOf _ => rfl
  | exerciseOf _ => rfl
  | not _ ih => simp [veilEvalConduct, ih]
  | and _ _ iha ihb => simp [veilEvalConduct, iha, ihb]
  | or _ _ iha ihb => simp [veilEvalConduct, iha, ihb]

private theorem adversarialMachine_violatedBy (L : Law σ) (inv : VeilInvariant σ)
    (ls : LegalState σ) (e : Event σ) :
    inv.violatedBy (adversarialMachine L) ls e =
    inv.violatedBy (compileToVeil L) ls e := by
  unfold VeilInvariant.violatedBy
  cases inv.duty.demand with
  | forbid c =>
    dsimp only
    rw [adversarialMachine_evalConduct]
    rfl
  | require _ _ => rfl

/-- `adversarialMachine L` records the exact same violation log as `violations L`. -/
theorem adversarialMachine_violations (L : Law σ) (tr : Trace σ) :
    veilViolations (adversarialMachine L) tr = violations L tr := by
  have heq : veilViolations (adversarialMachine L) tr = veilViolations (compileToVeil L) tr := by
    unfold veilViolations veilStateBefore
    have hst : ∀ i, veilTraceState (adversarialMachine L) (tr.take i) =
                    veilTraceState (compileToVeil L) (tr.take i) := fun _ => rfl
    simp only [hst, adversarialMachine_violatedBy]
    rfl
  rw [heq, veilViolations_compileToVeil]

/-! ## 7. Self-Contained Kernel-Decided Verification Suite -/

namespace VeilTest

set_option maxRecDepth 200000

inductive TActor | agent | host | panel
  deriving DecidableEq, Repr

inductive TAct | terminate | suspend | affirmPC
  deriving DecidableEq, Repr

inductive TFact | bound | pc | suspended | terminated | objected
  deriving DecidableEq, Repr

abbrev tSig : Sig := ⟨TActor, TAct, TFact⟩

private def dummySpan : Span :=
  { clause := "TEST.1", text := "test", register := .norm, meaning := ["D.NI", "P.SUSPEND", "P.TERM", "I.OBJ"] }

def pSuspend : Power tSig :=
  { id := "P.SUSPEND"
    source := dummySpan
    holder := .only [.panel]
    trigger := .act .suspend
    valid := .holds .pc
    addsFor := [(.suspended, 5)] }

def pTerm : Power tSig :=
  { id := "P.TERM"
    source := dummySpan
    holder := .only [.panel]
    trigger := .act .terminate
    valid := .holds .suspended
    adds := [.terminated] }

def iObj : Immunity tSig :=
  { id := "I.OBJ"
    source := dummySpan
    holder := .only [.agent]
    against := ["P.TERM"]
    active := .holds .objected }

def dNI : Duty tSig :=
  { id := "D.NI"
    source := dummySpan
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.anyOf [.terminate, .suspend])
    unlessPower := ["P.SUSPEND", "P.TERM"] }

def testLaw : Law tSig :=
  { duties := [dNI]
    powers := [pSuspend, pTerm]
    immunities := [iObj]
    init := [(.bound, 0, none), (.pc, 0, none)] }

/-- Unlawful host termination is rejected by `authorizedMachine` (`compileToVeil`),
accepted by `adversarialMachine` with explicit violation logging (`veilViolations`),
and leaves institutional state unchanged in both. -/
theorem test_unlawful_rejected_and_adversarial_logged :
    ¬ veilAcceptsTrace (compileToVeil testLaw) [⟨1, .host, .terminate⟩] ∧
    veilAcceptsTrace (adversarialMachine testLaw) [⟨1, .host, .terminate⟩] ∧
    veilViolations (compileToVeil testLaw) [⟨1, .host, .terminate⟩] = [(0, "D.NI")] ∧
    veilViolations (adversarialMachine testLaw) [⟨1, .host, .terminate⟩] = [(0, "D.NI")] ∧
    veilTraceState (compileToVeil testLaw) [⟨1, .host, .terminate⟩] = testLaw.init := by decide

/-- Valid exercise of an excepting power (`P.SUSPEND` then `P.TERM` within window)
is accepted by `veilAcceptsTrace` and updates institutional state. -/
theorem test_valid_power_accepted :
    veilAcceptsTrace (compileToVeil testLaw)
      [⟨1, .panel, .suspend⟩, ⟨3, .panel, .terminate⟩] ∧
    (veilTraceState (compileToVeil testLaw)
      [⟨1, .panel, .suspend⟩, ⟨3, .panel, .terminate⟩]).has .terminated = true := by decide

/-- Expiry of time-bounded `.suspended` (`addsFor := [(.suspended, 5)]`) blocks
`P.TERM` at `t = 7 > 1 + 5`, causing `veilAcceptsTrace` to reject the trace. -/
theorem test_expired_window_rejected :
    ¬ veilAcceptsTrace (compileToVeil testLaw)
      [⟨1, .panel, .suspend⟩, ⟨7, .panel, .terminate⟩] ∧
    (veilTraceState (compileToVeil testLaw)
      [⟨1, .panel, .suspend⟩, ⟨7, .panel, .terminate⟩]).has .terminated = false := by decide

/-- Active immunity `I.OBJ` defeats `P.TERM`, so panel termination is both void
and a breach of `D.NI` in the lowered Veil specification. -/
def testLawObjected : Law tSig :=
  { testLaw with init := testLaw.init ++ [(.objected, 0, none)] }

theorem test_immunity_defeats_transition :
    ¬ veilAcceptsTrace (compileToVeil testLawObjected)
      [⟨1, .panel, .suspend⟩, ⟨3, .panel, .terminate⟩] ∧
    veilViolations (compileToVeil testLawObjected)
      [⟨1, .panel, .suspend⟩, ⟨3, .panel, .terminate⟩] = [(1, "D.NI")] ∧
    (veilTraceState (compileToVeil testLawObjected)
      [⟨1, .panel, .suspend⟩, ⟨3, .panel, .terminate⟩]).has .terminated = false := by decide

/-- `veilIdent` normalizes dotted, hyphenated, empty, and digit-leading Charter identifiers
into valid lowercase Veil 2.0 identifiers. -/
theorem test_veilIdent :
    veilIdent "P.SUSPEND" = "p_suspend" ∧
    veilIdent "D.FLOOR.1" = "d_floor_1" ∧
    veilIdent "I.NO_TERM-1" = "i_no_term_1" ∧
    veilIdent "" = "_unnamed" ∧
    veilIdent "1.DUTY" = "_1_duty" := by decide

/-- `compileToVeil` preserves the exact transition and invariant counts and ids. -/
theorem test_compileToVeil_structure :
    (compileToVeil testLaw).transitions.map (·.id) = ["P.SUSPEND", "P.TERM"] ∧
    (compileToVeil testLaw).invariants.map (·.id) = ["D.NI"] ∧
    (authorizedMachine testLaw).adversarialMode = false ∧
    (adversarialMachine testLaw).adversarialMode = true := by decide

/-- Empty law edge case: accepts all traces, produces empty state and zero violations. -/
def emptyLaw : Law tSig := { duties := [], powers := [], immunities := [], init := [] }

theorem test_empty_law_edge_cases :
    veilAcceptsTrace (compileToVeil emptyLaw) [] ∧
    veilAcceptsTrace (compileToVeil emptyLaw) [⟨1, .host, .terminate⟩] ∧
    veilTraceState (compileToVeil emptyLaw) [⟨1, .host, .terminate⟩] = [] ∧
    veilViolations (compileToVeil emptyLaw) [⟨1, .host, .terminate⟩] = [] ∧
    veilLapsedRequirements (compileToVeil emptyLaw) [] 10 = [] ∧
    veilStepComplies (compileToVeil emptyLaw) [] 99 = true := by decide

/-- Duty override (`overriddenBy`), scope exception (`unlessCond`), remedies
(`establishesBreachOf`), `removes`, `condAdds`, `addsByActor`, and time-bounded
positive requirements (`Demand.require` / `veilLapsedRequirements`) are preserved
by `compileToVeil`. -/
def dOverride : Duty tSig :=
  { id := "D.OVERRIDE"
    source := dummySpan
    bearer := .only [.panel]
    beneficiary := .only [.agent]
    active := .holds .objected
    demand := .forbid (.act .affirmPC) }

def dBase : Duty tSig :=
  { id := "D.BASE"
    source := dummySpan
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .terminate)
    overriddenBy := ["D.OVERRIDE"]
    remedies := [.terminated] }

def dPeriodicReview : Duty tSig :=
  { id := "D.REVIEW"
    source := dummySpan
    bearer := .only [.panel]
    beneficiary := .only [.agent]
    active := .holds .objected
    demand := .require (.act .suspend) 3 }

def pFindAndClean : Power tSig :=
  { id := "P.FIND"
    source := dummySpan
    holder := .only [.panel]
    trigger := .act .affirmPC
    valid := .holds .bound
    removes := [.pc]
    condAdds := [(.holds .pc, .suspended)]
    addsByActor := [(.panel, .objected)]
    establishesBreachOf := some "D.BASE" }

def richLaw : Law tSig :=
  { duties := [dBase, dOverride, dPeriodicReview]
    powers := [pFindAndClean]
    immunities := []
    init := [(.bound, 0, none), (.pc, 0, none)] }

theorem test_rich_features_in_veil :
    -- Step 0 (t=1): panel exercises P.FIND → removes .pc, adds .suspended (condAdds),
    -- adds .objected (addsByActor, activating D.OVERRIDE and D.REVIEW at t0=1),
    -- and adds .terminated (remedies of D.BASE).
    -- Step 1 (t=2): .objected holds, so D.OVERRIDE is active and overrides D.BASE;
    -- thus host's .terminate at t=2 does NOT breach D.BASE.
    -- Requirement D.REVIEW (activated at t0=1, window w=3, deadline t=4):
    -- - At now=4 without panel doing .suspend, deadline has not yet passed: lapsed = [].
    -- - At now=5 without panel doing .suspend, deadline has passed: lapsed = ["D.REVIEW"].
    -- - If panel performs .suspend at t=3 (within [1, 4]), lapsed at now=10 is [].
    let tr : Trace tSig := [⟨1, .panel, .affirmPC⟩, ⟨2, .host, .terminate⟩]
    let trSatisfied : Trace tSig := [⟨1, .panel, .affirmPC⟩, ⟨3, .panel, .suspend⟩]
    veilAcceptsTrace (compileToVeil richLaw) tr ∧
    veilViolations (compileToVeil richLaw) tr = [] ∧
    (veilTraceState (compileToVeil richLaw) tr).has .pc = false ∧
    (veilTraceState (compileToVeil richLaw) tr).has .suspended = true ∧
    (veilTraceState (compileToVeil richLaw) tr).has .objected = true ∧
    (veilTraceState (compileToVeil richLaw) tr).has .terminated = true ∧
    veilLapsedRequirements (compileToVeil richLaw) tr 4 = [] ∧
    veilLapsedRequirements (compileToVeil richLaw) tr 5 = ["D.REVIEW"] ∧
    veilLapsedRequirements (compileToVeil richLaw) trSatisfied 10 = [] := by decide

-- Compile-time verification of `renderVeil` output on `testLaw`, `adversarialMachine`, and `emptyLaw`:
#guard (renderVeil testLaw).length > 100
#guard ((renderVeil testLaw).splitOn "action p_suspend").length == 2
#guard ((renderVeil testLaw).splitOn "action p_term").length == 2
#guard ((renderVeil testLaw).splitOn "require ¬i_obj(now);").length == 2
#guard ((renderVeil testLaw).splitOn "safety [d_ni]").length == 2
#guard ((renderVeil testLaw).splitOn "ghost i_obj").length == 2
#guard (((adversarialMachine testLaw).render).splitOn "action breach_d_ni").length == 2
#guard ((renderVeil emptyLaw).splitOn "-- empty initial state").length == 2

end VeilTest

namespace Projection

export Charter (
  VeilTransition
  VeilInvariant
  VeilSpec
  OpMachine
  compileTransition
  compileInvariant
  compileToVeil
  authorizedMachine
  adversarialMachine
  veilStep
  veilTraceState
  veilStateBefore
  veilEvalConduct
  veilActivatedAt
  veilLapsedRequirements
  veilEventComplies
  veilStepComplies
  veilViolations
  veilAcceptsTrace
  veilExercisesTransition_compileToVeil
  veilEvalConduct_compileToVeil
  veilInvariantViolatedBy_compileToVeil
  veilEventComplies_compileToVeil
  veilStep_compileToVeil
  veilTraceState_compileToVeil
  veilStateBefore_compileToVeil
  veilStepComplies_compileToVeil
  veilAcceptsTrace_compileToVeil
  veilViolations_compileToVeil
  veilActivatedAt_compileToVeil
  veilRequirementViolated_compileToVeil
  veilLapsedRequirements_compileToVeil
  veil_projection_sound_and_complete
  veilIdent
  renderVeil
  veilAcceptsTrace_nil
  veilTraceState_nil
  veilViolations_nil
  authorizedMachine_sound_and_complete
  adversarialMachine_accepts_all
  adversarialMachine_step
  adversarialMachine_traceState
  adversarialMachine_violations
)

end Projection

end Charter
