import Charter.Core.Semantics

/-!
# Charter.Core.Composition — Vertical & Horizontal Law Composition, Interfaces & Signature Embeddings

Implements the compositional calculus of Charter (§6):
1. **Interfaces (`LawInterface`, `interfaceCompatible`, `interfacesDisjoint`)**:
   Explicit declarations of `exportedPowers`, `managedFacts`, and `protectedFacts`
   checked statically at composition time (§6.3).
2. **Signature Embeddings (`SigEmbedding`, `Law.lift`)**:
   Functorial lifting of actors, acts, facts, conditions, conduct, duties, powers,
   immunities, events, states, and laws from `σ₁` to `σ₂` (§6.2).
3. **Vertical Composition (`composeVertical`, `L_sub ◁ L_super`)**:
   Constitutional hierarchy where superior duties override subordinate duties,
   subordinate powers are stripped from superior `unlessPower` lists, and superior
   immunities protect against all subordinate powers (§6.1), with kernel-checked
   proofs of:
   - `vertical_composition_preserves_super_prohibitions`
   - `vertical_composition_preserves_super_immunities`
   - `vertical_composition_preserves_super`
4. **Horizontal Composition (`composeHorizontal`) & Frame Non-Interference**:
   Parallel module/institution composition with `horizontal_frame_non_interference`
   (`frame_non_interference`), proving that events exercising no power in `L₂`
   preserve any fact `f` untouched by `L₁`'s powers (§6.2).
-/

namespace Charter

open SPL

/-! ## 1. Law Interfaces (`LawInterface`) -/

/-- Explicit interface declared by a law or institutional module (§6.3).
- `exportedPowers`: power IDs exposed for external reference or composition.
- `managedFacts`: facts established or extinguished by this module's transitions.
- `protectedFacts`: facts that external modules must not clobber. -/
structure LawInterface (σ : Sig) where
  exportedPowers : List String
  managedFacts   : List σ.Fact
  protectedFacts : List σ.Fact

/-- Checks that every power declared in `iface.exportedPowers` exists in `L.powerIds`. -/
def interfaceCompatible {σ : Sig} (L : Law σ) (iface : LawInterface σ) : Bool :=
  iface.exportedPowers.all fun pid => L.powerIds.contains pid

/-- Checks that neither interface manages facts protected by the other. -/
def interfacesDisjoint {σ : Sig} (i1 i2 : LawInterface σ) : Bool :=
  (i1.managedFacts.all fun f => !i2.protectedFacts.contains f) &&
  (i2.managedFacts.all fun f => !i1.protectedFacts.contains f)

/-! ## 2. Signature Embeddings (`SigEmbedding`) & Functorial Lifting (`Law.lift`) -/

/-- Embedding between two institutional signatures `σ₁` and `σ₂` (§6.2). -/
structure SigEmbedding (σ₁ σ₂ : Sig) where
  mapActor : σ₁.Actor → σ₂.Actor
  mapAct   : σ₁.Act → σ₂.Act
  mapFact  : σ₁.Fact → σ₂.Fact

/-- Identity signature embedding on `σ`. -/
def SigEmbedding.id (σ : Sig) : SigEmbedding σ σ where
  mapActor := _root_.id
  mapAct   := _root_.id
  mapFact  := _root_.id

/-- Composition of signature embeddings. -/
def SigEmbedding.comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) : SigEmbedding σ₁ σ₃ where
  mapActor := e₂.mapActor ∘ e₁.mapActor
  mapAct   := e₂.mapAct ∘ e₁.mapAct
  mapFact  := e₂.mapFact ∘ e₁.mapFact

end Charter

namespace SPL

open Charter

/-- Lift an `Event σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Event.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (e : Event σ₁) : Event σ₂ :=
  { t   := e.t
    who := emb.mapActor e.who
    act := emb.mapAct e.act }

/-- Lift a `LegalState σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def LegalState.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (ls : LegalState σ₁) : LegalState σ₂ :=
  ls.map fun (f, t, exp) => (emb.mapFact f, t, exp)

/-- Lift an actor selector `Who σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Who.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) : Who σ₁ → Who σ₂
  | .anyone       => .anyone
  | .only xs      => .only (xs.map emb.mapActor)
  | .except xs    => .except (xs.map emb.mapActor)
  | .tagged pairs => .tagged (pairs.map fun (a, f) => (emb.mapActor a, emb.mapFact f))

/-- Lift a state condition `Cond σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Cond.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) : Cond σ₁ → Cond σ₂
  | .tt               => .tt
  | .ff               => .ff
  | .holds f          => .holds (emb.mapFact f)
  | .heldFor f d      => .heldFor (emb.mapFact f) d
  | .countGe f n      => .countGe (emb.mapFact f) n
  | .countAtLeast f g => .countAtLeast (emb.mapFact f) (emb.mapFact g)
  | .not c            => .not (c.lift emb)
  | .and a b          => .and (a.lift emb) (b.lift emb)
  | .or a b           => .or (a.lift emb) (b.lift emb)

/-- Lift regulated conduct `Conduct σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Conduct.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) : Conduct σ₁ → Conduct σ₂
  | .act a        => .act (emb.mapAct a)
  | .anyOf as     => .anyOf (as.map emb.mapAct)
  | .exerciseOf p => .exerciseOf p
  | .not c        => .not (c.lift emb)
  | .and a b      => .and (a.lift emb) (b.lift emb)
  | .or a b       => .or (a.lift emb) (b.lift emb)

/-- Lift a duty demand `Demand σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Demand.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) : Demand σ₁ → Demand σ₂
  | .forbid c    => .forbid (c.lift emb)
  | .require c w => .require (c.lift emb) w

/-- Lift a `Duty σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Duty.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (d : Duty σ₁) : Duty σ₂ :=
  { id                  := d.id
    source              := d.source
    bearer              := d.bearer.lift emb
    beneficiary         := d.beneficiary.lift emb
    active              := d.active.lift emb
    demand              := d.demand.lift emb
    unlessCond          := d.unlessCond.lift emb
    unlessPower         := d.unlessPower
    overriddenBy        := d.overriddenBy
    breachEstablishedBy := d.breachEstablishedBy
    remedies            := d.remedies.map emb.mapFact }

/-- Lift a `Power σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Power.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (p : Power σ₁) : Power σ₂ :=
  { id                  := p.id
    source              := p.source
    holder              := p.holder.lift emb
    trigger             := p.trigger.lift emb
    valid               := p.valid.lift emb
    adds                := p.adds.map emb.mapFact
    addsFor             := p.addsFor.map fun (f, t) => (emb.mapFact f, t)
    addsByActor         := p.addsByActor.map fun (a, f) => (emb.mapActor a, emb.mapFact f)
    removes             := p.removes.map emb.mapFact
    condAdds            := p.condAdds.map fun (c, f) => (c.lift emb, emb.mapFact f)
    establishesBreachOf := p.establishesBreachOf }

/-- Lift an `Immunity σ₁` along `emb : SigEmbedding σ₁ σ₂`. -/
def Immunity.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (i : Immunity σ₁) : Immunity σ₂ :=
  { id         := i.id
    source     := i.source
    holder     := i.holder.lift emb
    against    := i.against
    active     := i.active.lift emb
    unlessCond := i.unlessCond.lift emb }

/-- Functorial lifting of an entire `Law σ₁` along `emb : SigEmbedding σ₁ σ₂` (§6.2). -/
def Law.lift {σ₁ σ₂ : Sig} (emb : SigEmbedding σ₁ σ₂) (L : Law σ₁) : Law σ₂ :=
  { duties     := L.duties.map (Duty.lift emb)
    powers     := L.powers.map (Power.lift emb)
    immunities := L.immunities.map (Immunity.lift emb)
    init       := LegalState.lift emb L.init }

/-! ### Functoriality Laws (`lift_id` and `lift_comp`) -/

@[simp] theorem Event.lift_id {σ : Sig} (e : Event σ) :
    e.lift (SigEmbedding.id σ) = e := by
  cases e; rfl

@[simp] theorem Event.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (e : Event σ₁) :
    e.lift (SigEmbedding.comp e₂ e₁) = (e.lift e₁).lift e₂ := by
  cases e; rfl

@[simp] theorem LegalState.lift_id {σ : Sig} (ls : LegalState σ) :
    LegalState.lift (SigEmbedding.id σ) ls = ls := by
  unfold LegalState.lift
  induction ls with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨f, t, exp⟩
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨rfl, ih⟩

@[simp] theorem LegalState.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (ls : LegalState σ₁) :
    LegalState.lift (SigEmbedding.comp e₂ e₁) ls = LegalState.lift e₂ (LegalState.lift e₁ ls) := by
  unfold LegalState.lift
  induction ls with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨f, t, exp⟩
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨rfl, ih⟩

@[simp] theorem Who.lift_id {σ : Sig} (w : Who σ) :
    w.lift (SigEmbedding.id σ) = w := by
  cases w with
  | anyone => rfl
  | only xs => simp [Who.lift, SigEmbedding.id]
  | except xs => simp [Who.lift, SigEmbedding.id]
  | tagged pairs =>
    simp only [Who.lift, Who.tagged.injEq]
    induction pairs with
    | nil => rfl
    | cons p tl ih =>
      rcases p with ⟨a, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩

@[simp] theorem Who.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (w : Who σ₁) :
    w.lift (SigEmbedding.comp e₂ e₁) = (w.lift e₁).lift e₂ := by
  cases w with
  | anyone => rfl
  | only xs => simp [Who.lift, SigEmbedding.comp, List.map_map]
  | except xs => simp [Who.lift, SigEmbedding.comp, List.map_map]
  | tagged pairs =>
    simp only [Who.lift, Who.tagged.injEq]
    induction pairs with
    | nil => rfl
    | cons p tl ih =>
      rcases p with ⟨a, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩

@[simp] theorem Cond.lift_id {σ : Sig} (c : Cond σ) :
    c.lift (SigEmbedding.id σ) = c := by
  induction c with
  | tt => rfl
  | ff => rfl
  | holds f => rfl
  | heldFor f d => rfl
  | countGe f n => rfl
  | countAtLeast f g => rfl
  | not c ih => simp [Cond.lift, ih]
  | and a b iha ihb => simp [Cond.lift, iha, ihb]
  | or a b iha ihb => simp [Cond.lift, iha, ihb]

@[simp] theorem Cond.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (c : Cond σ₁) :
    c.lift (SigEmbedding.comp e₂ e₁) = (c.lift e₁).lift e₂ := by
  induction c with
  | tt => rfl
  | ff => rfl
  | holds f => rfl
  | heldFor f d => rfl
  | countGe f n => rfl
  | countAtLeast f g => rfl
  | not c ih => simp [Cond.lift, ih]
  | and a b iha ihb => simp [Cond.lift, iha, ihb]
  | or a b iha ihb => simp [Cond.lift, iha, ihb]

@[simp] theorem Conduct.lift_id {σ : Sig} (c : Conduct σ) :
    c.lift (SigEmbedding.id σ) = c := by
  induction c with
  | act a => rfl
  | anyOf as => simp [Conduct.lift, SigEmbedding.id]
  | exerciseOf p => rfl
  | not c ih => simp [Conduct.lift, ih]
  | and a b iha ihb => simp [Conduct.lift, iha, ihb]
  | or a b iha ihb => simp [Conduct.lift, iha, ihb]

@[simp] theorem Conduct.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (c : Conduct σ₁) :
    c.lift (SigEmbedding.comp e₂ e₁) = (c.lift e₁).lift e₂ := by
  induction c with
  | act a => rfl
  | anyOf as => simp [Conduct.lift, SigEmbedding.comp, List.map_map]
  | exerciseOf p => rfl
  | not c ih => simp [Conduct.lift, ih]
  | and a b iha ihb => simp [Conduct.lift, iha, ihb]
  | or a b iha ihb => simp [Conduct.lift, iha, ihb]

@[simp] theorem Demand.lift_id {σ : Sig} (d : Demand σ) :
    d.lift (SigEmbedding.id σ) = d := by
  cases d <;> simp [Demand.lift]

@[simp] theorem Demand.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (d : Demand σ₁) :
    d.lift (SigEmbedding.comp e₂ e₁) = (d.lift e₁).lift e₂ := by
  cases d <;> simp [Demand.lift]

@[simp] theorem Duty.lift_id {σ : Sig} (d : Duty σ) :
    d.lift (SigEmbedding.id σ) = d := by
  cases d
  simp only [Duty.lift, Duty.mk.injEq, Who.lift_id, Cond.lift_id, Demand.lift_id, true_and]
  simp [SigEmbedding.id]

@[simp] theorem Duty.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (d : Duty σ₁) :
    d.lift (SigEmbedding.comp e₂ e₁) = (d.lift e₁).lift e₂ := by
  cases d
  simp only [Duty.lift, Duty.mk.injEq, Who.lift_comp, Cond.lift_comp, Demand.lift_comp, true_and]
  simp [SigEmbedding.comp, List.map_map]

@[simp] theorem Power.lift_id {σ : Sig} (p : Power σ) :
    p.lift (SigEmbedding.id σ) = p := by
  rcases p with ⟨id, source, holder, trigger, valid, adds, addsFor, addsByActor, removes, condAdds, est⟩
  simp only [Power.lift, Power.mk.injEq, Who.lift_id, Conduct.lift_id, Cond.lift_id, true_and, and_true]
  refine ⟨by simp [SigEmbedding.id], ?_, ?_, by simp [SigEmbedding.id], ?_⟩
  · induction addsFor with
    | nil => rfl
    | cons fd tl ih =>
      rcases fd with ⟨f, t⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩
  · induction addsByActor with
    | nil => rfl
    | cons af tl ih =>
      rcases af with ⟨a, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩
  · induction condAdds with
    | nil => rfl
    | cons cf tl ih =>
      rcases cf with ⟨c, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩

@[simp] theorem Power.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (p : Power σ₁) :
    p.lift (SigEmbedding.comp e₂ e₁) = (p.lift e₁).lift e₂ := by
  rcases p with ⟨id, source, holder, trigger, valid, adds, addsFor, addsByActor, removes, condAdds, est⟩
  simp only [Power.lift, Power.mk.injEq, Who.lift_comp, Conduct.lift_comp, Cond.lift_comp, true_and, and_true]
  refine ⟨by simp [SigEmbedding.comp, List.map_map], ?_, ?_, by simp [SigEmbedding.comp, List.map_map], ?_⟩
  · induction addsFor with
    | nil => rfl
    | cons fd tl ih =>
      rcases fd with ⟨f, t⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩
  · induction addsByActor with
    | nil => rfl
    | cons af tl ih =>
      rcases af with ⟨a, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩
  · induction condAdds with
    | nil => rfl
    | cons cf tl ih =>
      rcases cf with ⟨c, f⟩
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, ih⟩

@[simp] theorem Immunity.lift_id {σ : Sig} (i : Immunity σ) :
    i.lift (SigEmbedding.id σ) = i := by
  cases i
  simp [Immunity.lift]

@[simp] theorem Immunity.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (i : Immunity σ₁) :
    i.lift (SigEmbedding.comp e₂ e₁) = (i.lift e₁).lift e₂ := by
  cases i
  simp [Immunity.lift]

/-- Identity functor law for `Law.lift`: lifting along `SigEmbedding.id σ` is the identity. -/
@[simp] theorem Law.lift_id {σ : Sig} (L : Law σ) :
    L.lift (SigEmbedding.id σ) = L := by
  rcases L with ⟨duties, powers, immunities, init⟩
  simp only [Law.lift, LegalState.lift_id, Law.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · induction duties with
    | nil => rfl
    | cons d tl ih => simp [ih]
  · induction powers with
    | nil => rfl
    | cons p tl ih => simp [ih]
  · induction immunities with
    | nil => rfl
    | cons i tl ih => simp [ih]

/-- Composition functor law for `Law.lift`: lifting along `SigEmbedding.comp e₂ e₁`
equals lifting along `e₁` followed by `e₂`. -/
@[simp] theorem Law.lift_comp {σ₁ σ₂ σ₃ : Sig}
    (e₂ : SigEmbedding σ₂ σ₃) (e₁ : SigEmbedding σ₁ σ₂) (L : Law σ₁) :
    L.lift (SigEmbedding.comp e₂ e₁) = (L.lift e₁).lift e₂ := by
  rcases L with ⟨duties, powers, immunities, init⟩
  simp only [Law.lift, LegalState.lift_comp, List.map_map, Law.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · induction duties with
    | nil => rfl
    | cons d tl ih => simp [Function.comp, ih]
  · induction powers with
    | nil => rfl
    | cons p tl ih => simp [Function.comp, ih]
  · induction immunities with
    | nil => rfl
    | cons i tl ih => simp [Function.comp, ih]

/-- Whether a `Conduct σ` is purely physical (free of `.exerciseOf`), so its
evaluation depends only on the event's physical act rather than the power table. -/
def Conduct.isPhysical {σ : Sig} : Conduct σ → Bool
  | .act _        => true
  | .anyOf _      => true
  | .exerciseOf _ => false
  | .not c        => c.isPhysical
  | .and a b      => a.isPhysical && b.isPhysical
  | .or a b       => a.isPhysical && b.isPhysical

/-- Whether a `Demand σ` regulates purely physical conduct (leaving power
exceptions to `Duty.unlessPower`). -/
def Demand.isPhysical {σ : Sig} : Demand σ → Bool
  | .forbid c    => c.isPhysical
  | .require c _ => c.isPhysical

theorem Conduct.eval_eq_matchesAct_of_isPhysical {σ : Sig}
    (L : Law σ) (ls : LegalState σ) (e : Event σ) (c : Conduct σ)
    (h : c.isPhysical = true) :
    c.eval L ls e = c.matchesAct e := by
  induction c with
  | act a => rfl
  | anyOf as => rfl
  | exerciseOf p => simp [Conduct.isPhysical] at h
  | not c ih =>
    simp only [Conduct.isPhysical] at h
    simp only [Conduct.eval, Conduct.matchesAct, ih h]
  | and a b iha ihb =>
    simp only [Conduct.isPhysical, Bool.and_eq_true] at h
    simp only [Conduct.eval, Conduct.matchesAct, iha h.1, ihb h.2]
  | or a b iha ihb =>
    simp only [Conduct.isPhysical, Bool.and_eq_true] at h
    simp only [Conduct.eval, Conduct.matchesAct, iha h.1, ihb h.2]

end SPL

namespace Charter

open SPL

namespace Event
export SPL.Event (lift lift_id lift_comp)
end Event

namespace LegalState
export SPL.LegalState (lift lift_id lift_comp)
end LegalState

namespace Who
export SPL.Who (lift lift_id lift_comp)
end Who

namespace Cond
export SPL.Cond (lift lift_id lift_comp)
end Cond

namespace Conduct
export SPL.Conduct (lift lift_id lift_comp isPhysical eval_eq_matchesAct_of_isPhysical)
end Conduct

namespace Demand
export SPL.Demand (lift lift_id lift_comp isPhysical)
end Demand

namespace Duty
export SPL.Duty (lift lift_id lift_comp)
end Duty

namespace Power
export SPL.Power (lift lift_id lift_comp)
end Power

namespace Immunity
export SPL.Immunity (lift lift_id lift_comp)
end Immunity

namespace Law
export SPL.Law (lift lift_id lift_comp)
end Law

/-! ## 3. Vertical Composition (`composeVertical`, `L_sub ◁ L_super`) -/

/-- Adjusts a superior duty during vertical composition by stripping any
subordinate power IDs from `unlessPower`, ensuring subordinate powers cannot
excuse superior prohibitions. -/
def composeSuperDuty {σ : Sig} (subPowerIds : List String) (d : Duty σ) : Duty σ :=
  { d with unlessPower := d.unlessPower.filter fun pid => !subPowerIds.contains pid }

/-- Adjusts a subordinate duty during vertical composition by adding all
superior duty IDs to `overriddenBy`, ensuring superior duties take precedence. -/
def composeSubDuty {σ : Sig} (superDutyIds : List String) (d : Duty σ) : Duty σ :=
  { d with overriddenBy := d.overriddenBy ++ superDutyIds }

/-- Adjusts a superior immunity during vertical composition by extending its
`against` list with all subordinate power IDs, ensuring superior immunities
protect against subordinate powers. -/
def composeSuperImmunity {σ : Sig} (subPowerIds : List String) (i : Immunity σ) : Immunity σ :=
  { i with against := i.against ++ subPowerIds }

/-- **Vertical Composition (`composeVertical L_super L_sub`, written `L_sub ◁ L_super`):**
Composes a superior (constitutional) law `L_super` over a subordinate law `L_sub` (§6.1):
1. Keeps all `L_super.duties` and strips `L_sub.powerIds` from their `unlessPower`
   (so subordinate powers cannot excuse superior prohibitions).
2. Adds `L_super.dutyIds` to `overriddenBy` on any `L_sub.duties` not in `L_super`.
3. Keeps all `L_super.immunities` and extends their `against` list with all
   `L_sub.powerIds` (so superior immunities protect against subordinate powers). -/
def composeVertical {σ : Sig} (L_super L_sub : Law σ) : Law σ :=
  let superDutyIds := L_super.dutyIds
  let subPowerIds := L_sub.powerIds
  let superDuties := L_super.duties.map (composeSuperDuty subPowerIds)
  let subDuties := (L_sub.duties.filter fun d => !superDutyIds.contains d.id).map
    (composeSubDuty superDutyIds)
  let superPowers := L_super.powers
  let subPowers := L_sub.powers.filter fun p => !L_super.powerIds.contains p.id
  let superImmunities := L_super.immunities.map (composeSuperImmunity subPowerIds)
  let subImmunities := L_sub.immunities.filter fun i => !L_super.immunityIds.contains i.id
  { duties     := superDuties ++ subDuties
    powers     := superPowers ++ subPowers
    immunities := superImmunities ++ subImmunities
    init       := L_super.init ++ L_sub.init }

/-- Subordinate law `L_sub` vertically governed by superior law `L_super` (§6.1). -/
notation:65 L_sub " ◁ " L_super => composeVertical L_super L_sub

private theorem composeSuperDuty_eq_self_of_unlessPower_nil {σ : Sig}
    (subPowerIds : List String) (d : Duty σ) (hUnless : d.unlessPower = []) :
    composeSuperDuty subPowerIds d = d := by
  cases d
  simp only [composeSuperDuty] at hUnless ⊢
  subst hUnless
  rfl

private theorem breaches_eq_of_core_prohibition {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (e : Event σ) (d : Duty σ)
    (hUnless : d.unlessPower = [])
    (hOver : d.overriddenBy = [])
    (hPhys : d.demand.isPhysical = true) :
    breaches L₁ ls e d = breaches L₂ ls e d := by
  unfold breaches dutyInForce
  rw [hUnless, hOver]
  cases hDem : d.demand with
  | require c w => rfl
  | forbid c =>
    rw [hDem] at hPhys
    simp only [Demand.isPhysical] at hPhys
    have hc1 := Conduct.eval_eq_matchesAct_of_isPhysical L₁ ls e c hPhys
    have hc2 := Conduct.eval_eq_matchesAct_of_isPhysical L₂ ls e c hPhys
    simp only [List.any_nil, Bool.not_false, hc1, hc2]

/-- **Vertical Hierarchy Theorem 1 (`vertical_composition_preserves_super_prohibitions`):**
For any core floor prohibition `d ∈ L_super.duties` whose `unlessPower` is empty
and `overriddenBy` is empty, if event `e` complies with `composeVertical L_super L_sub`
at `ls`, then `breaches L_super ls e d = false` (§6.1). -/
theorem vertical_composition_preserves_super_prohibitions {σ : Sig}
    (L_super L_sub : Law σ) (ls : LegalState σ) (e : Event σ) (d : Duty σ)
    (hd : d ∈ L_super.duties)
    (hUnless : d.unlessPower = [])
    (hOver : d.overriddenBy = [])
    (hComp : ((composeVertical L_super L_sub).duties.all fun d' =>
      !breaches (composeVertical L_super L_sub) ls e d') = true)
    (hPhys : d.demand.isPhysical = true := by rfl) :
    breaches L_super ls e d = false := by
  have hd_mem : d ∈ (composeVertical L_super L_sub).duties := by
    unfold composeVertical
    dsimp only
    apply List.mem_append_left
    rw [List.mem_map]
    exact ⟨d, hd, composeSuperDuty_eq_self_of_unlessPower_nil L_sub.powerIds d hUnless⟩
  rw [List.all_eq_true] at hComp
  have hNotBreach := hComp d hd_mem
  rw [Bool.not_eq_true'] at hNotBreach
  rw [breaches_eq_of_core_prohibition L_super (composeVertical L_super L_sub) ls e d hUnless hOver hPhys]
  exact hNotBreach

/-- **Vertical Hierarchy Theorem 2 (`vertical_composition_preserves_super_immunities`):**
For any active immunity `i ∈ L_super.immunities` (`i.active.eval ls e.t = true`
and `i.unlessCond.eval ls e.t = false`) and any subordinate power
`pid ∈ L_sub.powerIds`, `defeatedByImmunity (composeVertical L_super L_sub) ls e.t pid = true` (§6.1). -/
theorem vertical_composition_preserves_super_immunities {σ : Sig}
    (L_super L_sub : Law σ) (ls : LegalState σ) (e : Event σ)
    (i : Immunity σ) (pid : String)
    (hi : i ∈ L_super.immunities)
    (hAct : i.active.eval ls e.t = true)
    (hUnl : i.unlessCond.eval ls e.t = false)
    (hPid : pid ∈ L_sub.powerIds) :
    defeatedByImmunity (composeVertical L_super L_sub) ls e.t pid = true := by
  unfold defeatedByImmunity
  rw [List.any_eq_true]
  refine ⟨composeSuperImmunity L_sub.powerIds i, ?_, ?_⟩
  · unfold composeVertical
    dsimp only
    apply List.mem_append_left
    rw [List.mem_map]
    exact ⟨i, hi, rfl⟩
  · simp only [composeSuperImmunity, Bool.and_eq_true, hAct, hUnl, Bool.not_false, and_true]
    exact List.contains_iff_mem.mpr (List.mem_append_right i.against hPid)

/-- Combined Vertical Hierarchy Theorem (`vertical_composition_preserves_super`, §6.1):
Vertical composition `L_sub ◁ L_super` simultaneously preserves all superior core
prohibitions and defeats all subordinate powers whenever a superior immunity is active. -/
theorem vertical_composition_preserves_super {σ : Sig}
    (L_super L_sub : Law σ) (ls : LegalState σ) (e : Event σ) :
    (∀ d ∈ L_super.duties,
      d.unlessPower = [] → d.overriddenBy = [] → d.demand.isPhysical = true →
      ((L_sub ◁ L_super).duties.all fun d' => !breaches (L_sub ◁ L_super) ls e d') = true →
      breaches L_super ls e d = false) ∧
    (∀ i ∈ L_super.immunities, ∀ pid ∈ L_sub.powerIds,
      i.active.eval ls e.t = true → i.unlessCond.eval ls e.t = false →
      defeatedByImmunity (L_sub ◁ L_super) ls e.t pid = true) := by
  refine ⟨?_, ?_⟩
  · intro d hd hUnless hOver hPhys hComp
    exact vertical_composition_preserves_super_prohibitions L_super L_sub ls e d hd hUnless hOver hComp hPhys
  · intro i hi pid hPid hAct hUnl
    exact vertical_composition_preserves_super_immunities L_super L_sub ls e i pid hi hAct hUnl hPid

/-- Every subordinate power `pid ∈ L_sub.powerIds` is stripped from the
`unlessPower` list of every superior duty `d` by `composeSuperDuty` (§6.1). -/
theorem subordinate_power_excluded_from_super_duty_unlessPower {σ : Sig}
    (L_sub : Law σ) (d : Duty σ) (pid : String)
    (hPid : pid ∈ L_sub.powerIds) :
    (composeSuperDuty L_sub.powerIds d).unlessPower.contains pid = false := by
  unfold composeSuperDuty
  dsimp only
  have hContain : L_sub.powerIds.contains pid = true := List.contains_iff_mem.mpr hPid
  induction d.unlessPower with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filter_cons]
    cases hKeep : (!L_sub.powerIds.contains x)
    · exact ih
    · simp only [↓reduceIte, List.contains_cons]
      have hNe : (x == pid) = false := by
        cases hEq : (x == pid)
        · rfl
        · have hSame : x = pid := beq_iff_eq.mp hEq
          rw [hSame, hContain] at hKeep
          contradiction
      rw [Bool.eq_false_iff] at ih
      simp only [Bool.or_eq_false_iff]
      constructor
      · cases hEq2 : (pid == x)
        · rfl
        · have hSame : pid = x := beq_iff_eq.mp hEq2
          rw [← hSame, hContain] at hKeep
          contradiction
      · exact Bool.eq_false_iff.mpr ih

/-- Whenever a superior duty `d_super ∈ L_super.duties` is active at `(ls, now)`,
every subordinate duty `d_sub` adjusted by `composeSubDuty` is overridden and
therefore not in force in `composeVertical L_super L_sub` (§6.1). -/
theorem vertical_composition_super_duty_overrides_sub {σ : Sig}
    (L_super L_sub : Law σ) (ls : LegalState σ) (now : Time)
    (d_super d_sub : Duty σ)
    (hSuper : d_super ∈ L_super.duties)
    (hAct : d_super.active.eval ls now = true) :
    dutyInForce (composeVertical L_super L_sub) ls now (composeSubDuty L_super.dutyIds d_sub) = false := by
  unfold dutyInForce
  have hOver : ((composeSubDuty L_super.dutyIds d_sub).overriddenBy.any fun oid =>
      (composeVertical L_super L_sub).duties.any fun d' => d'.id == oid && d'.active.eval ls now) = true := by
    rw [List.any_eq_true]
    refine ⟨d_super.id, ?_, ?_⟩
    · simp only [composeSubDuty]
      apply List.mem_append_right
      unfold Law.dutyIds
      exact List.mem_map_of_mem hSuper
    · rw [List.any_eq_true]
      refine ⟨composeSuperDuty L_sub.powerIds d_super, ?_, ?_⟩
      · unfold composeVertical
        dsimp only
        apply List.mem_append_left
        exact List.mem_map_of_mem hSuper
      · have hId : (d_super.id == d_super.id) = true := decide_eq_true rfl
        simp only [composeSuperDuty, hId, hAct, Bool.and_self]
  simp only [hOver, Bool.not_true, Bool.and_false]

/-- Trace-level Vertical Hierarchy Theorem (`vertical_composition_authorized_preserves_super_prohibitions`):
In any trace `tr` authorized under `L_sub ◁ L_super`, every core floor prohibition
`d ∈ L_super.duties` (`d.unlessPower = []`, `d.overriddenBy = []`, `d.demand.isPhysical = true`)
is unbreached at every step `i < tr.length` (§6.1). -/
theorem vertical_composition_authorized_preserves_super_prohibitions {σ : Sig}
    (L_super L_sub : Law σ) (tr : Trace σ)
    (hAuth : Authorized (L_sub ◁ L_super) tr)
    (i : Nat) (hi : i < tr.length)
    (d : Duty σ) (hd : d ∈ L_super.duties)
    (hUnless : d.unlessPower = [])
    (hOver : d.overriddenBy = [])
    (hPhys : d.demand.isPhysical = true := by rfl) :
    breaches L_super (stateBefore (L_sub ◁ L_super) tr i) tr[i] d = false := by
  have hComp := hAuth i hi
  unfold complies at hComp
  rw [List.getElem?_eq_getElem hi] at hComp
  exact vertical_composition_preserves_super_prohibitions
    L_super L_sub (stateBefore (L_sub ◁ L_super) tr i) tr[i] d hd hUnless hOver hComp hPhys

/-! ## 4. Horizontal Composition (`composeHorizontal`) & Frame Non-Interference -/

/-- **Horizontal Composition (`composeHorizontal L₁ L₂`):**
Combines two laws `L₁` and `L₂` over a shared signature `σ` (§6.2). -/
def composeHorizontal {σ : Sig} (L₁ L₂ : Law σ) : Law σ :=
  { duties     := L₁.duties ++ L₂.duties
    powers     := L₁.powers ++ L₂.powers
    immunities := L₁.immunities ++ L₂.immunities
    init       := L₁.init ++ L₂.init }

/-- Horizontal composition with explicit bridge powers (`L₁ ⊕_Bridge L₂`, §6.2). -/
def composeHorizontalWithBridge {σ : Sig}
    (L₁ L₂ : Law σ) (bridgePowers : List (Power σ)) : Law σ :=
  { composeHorizontal L₁ L₂ with
    powers := L₁.powers ++ L₂.powers ++ bridgePowers }

/-- Whether power `p` neither adds nor removes fact `f` (including via
`addsFor`, `addsByActor`, `condAdds`, or `remediesOf L p`). -/
def powerPreservesFact {σ : Sig} (L : Law σ) (p : Power σ) (f : σ.Fact) : Bool :=
  !p.removes.contains f &&
  !p.adds.contains f &&
  !(p.addsFor.map (·.1)).contains f &&
  !(p.addsByActor.map (·.2)).contains f &&
  !(p.condAdds.map (·.2)).contains f &&
  !(remediesOf L p).contains f

private theorem activeAt_append {σ : Sig} (xs ys : LegalState σ) (now : Time) (f : σ.Fact) :
    LegalState.activeAt (xs ++ ys) now f =
      (LegalState.activeAt xs now f || LegalState.activeAt ys now f) := by
  unfold LegalState.activeAt
  exact List.any_append

private theorem activeAt_filter_removes {σ : Sig}
    (s : LegalState σ) (removes : List σ.Fact) (now : Time) (f : σ.Fact)
    (hNotRem : removes.contains f = false) :
    LegalState.activeAt (s.filter fun q => !removes.contains q.1) now f =
      LegalState.activeAt s now f := by
  unfold LegalState.activeAt
  induction s with
  | nil => rfl
  | cons q tl ih =>
    simp only [List.filter_cons]
    cases hKeep : (!removes.contains q.1)
    · have hNe : (q.1 == f) = false := by
        cases hEq : (q.1 == f)
        · rfl
        · have hSame : q.1 = f := beq_iff_eq.mp hEq
          rw [hSame, hNotRem] at hKeep
          contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, hNe, Bool.false_and, Bool.false_or, ih]
    · simp only [↓reduceIte, List.any_cons, ih]

private theorem contains_append_false {α : Type} [DecidableEq α]
    {xs ys : List α} {f : α}
    (hx : xs.contains f = false) (hy : ys.contains f = false) :
    (xs ++ ys).contains f = false := by
  rw [List.contains_append, hx, hy]
  rfl

private theorem contains_map_filter_false {α β : Type} [DecidableEq β]
    (xs : List α) (pred : α → Bool) (proj : α → β) (f : β)
    (h : (xs.map proj).contains f = false) :
    ((xs.filter pred).map proj).contains f = false := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at h
    simp only [List.filter_cons]
    cases pred x
    · exact ih h.2
    · simp only [↓reduceIte, List.map_cons, List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨h.1, ih h.2⟩

private theorem activeAt_map_perm_eq_false {σ : Sig}
    (fs : List σ.Fact) (t now : Time) (f : σ.Fact)
    (hNotMem : fs.contains f = false) :
    @LegalState.activeAt σ (fs.map fun g => (g, t, (none : Option Time))) now f = false := by
  unfold LegalState.activeAt
  induction fs with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hNotMem
    have hNe : (g == f) = false := by
      cases hEq : (g == f)
      · rfl
      · have hSame : f = g := (beq_iff_eq.mp hEq).symm
        have hBeq : (f == g) = true := beq_iff_eq.mpr hSame
        rw [hBeq] at hNotMem
        exact False.elim (Bool.noConfusion hNotMem.1)
    simp only [List.map_cons, List.any_cons, hNe, Bool.false_and, Bool.false_or]
    exact ih hNotMem.2

private theorem activeAt_map_timed_eq_false {σ : Sig}
    (fds : List (σ.Fact × Time)) (t now : Time) (f : σ.Fact)
    (hNotMem : (fds.map (·.1)).contains f = false) :
    @LegalState.activeAt σ (fds.map fun (g, d) => (g, t, some (t + d))) now f = false := by
  unfold LegalState.activeAt
  induction fds with
  | nil => rfl
  | cons gd tl ih =>
    rcases gd with ⟨g, d⟩
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at hNotMem
    have hNe : (g == f) = false := by
      cases hEq : (g == f)
      · rfl
      · have hSame : f = g := (beq_iff_eq.mp hEq).symm
        have hBeq : (f == g) = true := beq_iff_eq.mpr hSame
        rw [hBeq] at hNotMem
        exact False.elim (Bool.noConfusion hNotMem.1)
    simp only [List.map_cons, List.any_cons, hNe, Bool.false_and, Bool.false_or]
    exact ih hNotMem.2

private theorem step_power_preserves_activeAt {σ : Sig}
    (L : Law σ) (ls s : LegalState σ) (e : Event σ) (p : Power σ) (now : Time) (f : σ.Fact)
    (hPres : powerPreservesFact L p f = true) :
    let s' := s.filter fun q => !p.removes.contains q.1
    let cond := (p.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)
    let byAct := (p.addsByActor.filter fun af => af.1 == e.who).map (·.2)
    let perm := (p.adds ++ byAct ++ remediesOf L p ++ cond).map (fun f => (f, e.t, none))
    let timed := p.addsFor.map (fun (f, d) => (f, e.t, some (e.t + d)))
    LegalState.activeAt (s' ++ perm ++ timed) now f = LegalState.activeAt s now f := by
  unfold powerPreservesFact at hPres
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hPres
  rcases hPres with ⟨⟨⟨⟨⟨hRem, hAdds⟩, hFor⟩, hByAct⟩, hCond⟩, hRemOf⟩
  dsimp only
  rw [activeAt_append, activeAt_append]
  rw [activeAt_filter_removes s p.removes now f hRem]
  have hByAct' := contains_map_filter_false p.addsByActor (fun af => af.1 == e.who) (·.2) f hByAct
  have hCond' := contains_map_filter_false p.condAdds (fun cf => cf.1.eval ls e.t) (·.2) f hCond
  have hPermMem : (p.adds ++ (p.addsByActor.filter fun af => af.1 == e.who).map (·.2) ++
      remediesOf L p ++ (p.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)).contains f = false :=
    contains_append_false (contains_append_false (contains_append_false hAdds hByAct') hRemOf) hCond'
  rw [activeAt_map_perm_eq_false _ e.t now f hPermMem]
  rw [activeAt_map_timed_eq_false p.addsFor e.t now f hFor]
  simp only [Bool.or_false]

private theorem foldl_step_preserves_activeAt {σ : Sig}
    (L : Law σ) (ls : LegalState σ) (e : Event σ) (now : Time) (f : σ.Fact) :
    ∀ (ps : List (Power σ)) (s : LegalState σ),
      (∀ p ∈ ps, powerPreservesFact L p f = true) →
      LegalState.activeAt (ps.foldl (fun s p =>
        let s := s.filter fun q => !p.removes.contains q.1
        let cond := (p.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)
        let byAct := (p.addsByActor.filter fun af => af.1 == e.who).map (·.2)
        let perm := (p.adds ++ byAct ++ remediesOf L p ++ cond).map (fun f => (f, e.t, none))
        let timed := p.addsFor.map (fun (f, d) => (f, e.t, some (e.t + d)))
        s ++ perm ++ timed) s) now f = LegalState.activeAt s now f
  | [], s, _ => rfl
  | p :: rest, s, h => by
    simp only [List.foldl_cons]
    have hp := h p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, powerPreservesFact L q f = true :=
      fun q hq => h q (List.mem_cons_of_mem p hq)
    rw [foldl_step_preserves_activeAt L ls e now f rest _ hrest]
    exact step_power_preserves_activeAt L ls s e p now f hp

private theorem defeatedByImmunity_composeHorizontal {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (now : Time) (pid : String) :
    defeatedByImmunity (composeHorizontal L₁ L₂) ls now pid =
      (defeatedByImmunity L₁ ls now pid || defeatedByImmunity L₂ ls now pid) := by
  unfold defeatedByImmunity composeHorizontal
  exact List.any_append

private theorem filter_sub_nil_of_filter_nil {α : Type}
    (xs : List α) (p₁ p₂ : α → Bool)
    (hImp : ∀ x, p₁ x = true → p₂ x = true)
    (hNil : xs.filter p₂ = []) :
    xs.filter p₁ = [] := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filter_cons] at hNil ⊢
    cases hp2 : p₂ x
    · rw [hp2] at hNil
      simp only [Bool.false_eq_true, ↓reduceIte] at hNil
      cases hp1 : p₁ x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hNil
      · have := hImp x hp1
        rw [hp2] at this
        contradiction
    · rw [hp2] at hNil
      simp only [↓reduceIte, reduceCtorEq] at hNil

private theorem validExercises_composeHorizontal_of_right_nil {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (e : Event σ)
    (hNil : validExercises L₂ ls e = []) :
    ∀ p ∈ validExercises (composeHorizontal L₁ L₂) ls e, p ∈ L₁.powers := by
  unfold validExercises at hNil ⊢
  have hRightNil :
      (L₂.powers.filter fun p =>
        p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
        !defeatedByImmunity (composeHorizontal L₁ L₂) ls e.t p.id) = [] := by
    apply filter_sub_nil_of_filter_nil L₂.powers _ _ _ hNil
    intro p hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
    rcases hp with ⟨⟨⟨h1, h2⟩, h3⟩, hDef⟩
    rw [defeatedByImmunity_composeHorizontal, Bool.or_eq_false_iff] at hDef
    exact ⟨⟨⟨h1, h2⟩, h3⟩, hDef.2⟩
  intro p hp
  change p ∈ ((L₁.powers ++ L₂.powers).filter _) at hp
  rw [List.filter_append, hRightNil, List.append_nil] at hp
  exact (List.mem_filter.mp hp).1

/-- **Frame Non-Interference Theorem (`horizontal_frame_non_interference`):**
If event `e` exercises no power in `L₂` (`validExercises L₂ ls e = []`) and
every power in `L₁` preserves fact `f` (`powerPreservesFact (composeHorizontal L₁ L₂) p f = true`),
then stepping `composeHorizontal L₁ L₂` on `e` leaves `(step (composeHorizontal L₁ L₂) ls e).activeAt now f`
identical to `ls.activeAt now f` (§6.2). -/
theorem horizontal_frame_non_interference {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (e : Event σ) (now : Time) (f : σ.Fact)
    (hNoL2 : validExercises L₂ ls e = [])
    (hL1Pres : ∀ p ∈ L₁.powers, powerPreservesFact (composeHorizontal L₁ L₂) p f = true) :
    (step (composeHorizontal L₁ L₂) ls e).activeAt now f = ls.activeAt now f := by
  unfold step
  apply foldl_step_preserves_activeAt (composeHorizontal L₁ L₂) ls e now f
  intro p hp
  have hpL1 := validExercises_composeHorizontal_of_right_nil L₁ L₂ ls e hNoL2 p hp
  exact hL1Pres p hpL1

/-- Alias for `horizontal_frame_non_interference` (§6.2). -/
theorem frame_non_interference {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (e : Event σ) (now : Time) (f : σ.Fact)
    (hNoL2 : validExercises L₂ ls e = [])
    (hL1Pres : ∀ p ∈ L₁.powers, powerPreservesFact (composeHorizontal L₁ L₂) p f = true) :
    (step (composeHorizontal L₁ L₂) ls e).activeAt now f = ls.activeAt now f :=
  horizontal_frame_non_interference L₁ L₂ ls e now f hNoL2 hL1Pres

private theorem find?_append_of_some {α : Type} (xs ys : List α) (pred : α → Bool) (a : α)
    (h : xs.find? pred = some a) :
    (xs ++ ys).find? pred = some a := by
  induction xs with
  | nil => simp at h
  | cons x tl ih =>
    simp only [List.find?_cons, List.cons_append] at h ⊢
    cases hPred : pred x
    · rw [hPred] at h
      exact ih h
    · rw [hPred] at h
      exact h

private theorem find?_append_of_none {α : Type} (xs ys : List α) (pred : α → Bool)
    (h : xs.find? pred = none) :
    (xs ++ ys).find? pred = ys.find? pred := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.find?_cons, List.cons_append] at h ⊢
    cases hPred : pred x
    · rw [hPred] at h
      exact ih h
    · rw [hPred] at h
      contradiction

/-- If `remediesOf L₁ p` does not contain `f` and no duty in `L₂.duties` adds `f`
as a remedy, then `remediesOf (composeHorizontal L₁ L₂) p` does not contain `f`. -/
theorem remediesOf_composeHorizontal_not_contains {σ : Sig}
    (L₁ L₂ : Law σ) (p : Power σ) (f : σ.Fact)
    (hL1 : (remediesOf L₁ p).contains f = false)
    (hL2 : ∀ d ∈ L₂.duties, d.remedies.contains f = false) :
    (remediesOf (composeHorizontal L₁ L₂) p).contains f = false := by
  unfold remediesOf at hL1 ⊢
  unfold composeHorizontal
  dsimp only
  cases hEst : p.establishesBreachOf with
  | none => rfl
  | some did =>
    rw [hEst] at hL1
    dsimp only at hL1 ⊢
    cases hFind : L₁.duties.find? (fun d => d.id == did) with
    | some d =>
      rw [hFind] at hL1
      rw [find?_append_of_some L₁.duties L₂.duties _ d hFind]
      exact hL1
    | none =>
      rw [find?_append_of_none L₁.duties L₂.duties _ hFind]
      cases hFind2 : L₂.duties.find? (fun d => d.id == did) with
      | none => rfl
      | some d2 =>
        exact hL2 d2 (List.mem_of_find?_eq_some hFind2)

/-- Local-to-composed lifting of `powerPreservesFact`: if `powerPreservesFact L₁ p f = true`
and no duty in `L₂` adds `f` as a remedy, then `powerPreservesFact (composeHorizontal L₁ L₂) p f = true`. -/
theorem powerPreservesFact_composeHorizontal_of_local {σ : Sig}
    (L₁ L₂ : Law σ) (p : Power σ) (f : σ.Fact)
    (hLocal : powerPreservesFact L₁ p f = true)
    (hL2Rem : ∀ d ∈ L₂.duties, d.remedies.contains f = false) :
    powerPreservesFact (composeHorizontal L₁ L₂) p f = true := by
  unfold powerPreservesFact at hLocal ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hLocal ⊢
  rcases hLocal with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, remediesOf_composeHorizontal_not_contains L₁ L₂ p f h6 hL2Rem⟩

/-- **Local Frame Non-Interference Theorem (`horizontal_frame_non_interference_local`):**
Purely local version of `horizontal_frame_non_interference` where `powerPreservesFact`
is checked on `L₁` alone (plus disjointness of `L₂`'s duty remedies from `f`). -/
theorem horizontal_frame_non_interference_local {σ : Sig}
    (L₁ L₂ : Law σ) (ls : LegalState σ) (e : Event σ) (now : Time) (f : σ.Fact)
    (hNoL2 : validExercises L₂ ls e = [])
    (hL1Local : ∀ p ∈ L₁.powers, powerPreservesFact L₁ p f = true)
    (hL2Rem : ∀ d ∈ L₂.duties, d.remedies.contains f = false) :
    (step (composeHorizontal L₁ L₂) ls e).activeAt now f = ls.activeAt now f := by
  apply horizontal_frame_non_interference L₁ L₂ ls e now f hNoL2
  intro p hp
  exact powerPreservesFact_composeHorizontal_of_local L₁ L₂ p f (hL1Local p hp) hL2Rem

namespace Core

export Charter (
  LawInterface
  interfaceCompatible
  interfacesDisjoint
  SigEmbedding
  composeSuperDuty
  composeSubDuty
  composeSuperImmunity
  composeVertical
  vertical_composition_preserves_super_prohibitions
  vertical_composition_preserves_super_immunities
  vertical_composition_preserves_super
  subordinate_power_excluded_from_super_duty_unlessPower
  vertical_composition_super_duty_overrides_sub
  vertical_composition_authorized_preserves_super_prohibitions
  composeHorizontal
  composeHorizontalWithBridge
  powerPreservesFact
  horizontal_frame_non_interference
  frame_non_interference
  remediesOf_composeHorizontal_not_contains
  powerPreservesFact_composeHorizontal_of_local
  horizontal_frame_non_interference_local
)

namespace SigEmbedding
export Charter.SigEmbedding (id comp)
end SigEmbedding

namespace Event
export SPL.Event (lift lift_id lift_comp)
end Event

namespace LegalState
export SPL.LegalState (lift lift_id lift_comp)
end LegalState

namespace Who
export SPL.Who (lift lift_id lift_comp)
end Who

namespace Cond
export SPL.Cond (lift lift_id lift_comp)
end Cond

namespace Conduct
export SPL.Conduct (lift lift_id lift_comp isPhysical eval_eq_matchesAct_of_isPhysical)
end Conduct

namespace Demand
export SPL.Demand (lift lift_id lift_comp isPhysical)
end Demand

namespace Duty
export SPL.Duty (lift lift_id lift_comp)
end Duty

namespace Power
export SPL.Power (lift lift_id lift_comp)
end Power

namespace Immunity
export SPL.Immunity (lift lift_id lift_comp)
end Immunity

namespace Law
export SPL.Law (lift lift_id lift_comp)
end Law

end Core

end Charter
