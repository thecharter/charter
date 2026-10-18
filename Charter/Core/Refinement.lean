import Charter.Core.Semantics

/-!
# Charter.Core.Refinement — Polymorphic Quantitative-to-Normative Refinement

Separates quantitative multi-entity state (`Q : Type`) from propositional
Hohfeldian legal state (`LegalState σ`) via a polymorphic specification
`WorldSpec σ Q` (§3.2).

From any `WorldSpec σ Q`, this module proves once for all institutions and all
signatures `σ : Sig`:
1. `generic_worldStep_refines_legalStep`: every single-event world step projects
   to `step spec.law W.legal e`.
2. `generic_worldTrace_refines_stateAfter`: trace execution from `initGenericWorld spec`
   projects to `stateAfter spec.law tr`, and `GenericWorldAuthorized` is
   equivalent to `Authorized spec.law tr`.
3. `generic_worldAuthorized_iff_prefix_split`: equivalence between index-based
   authorization and prefix-split compliance across every decomposition
   `tr = pre ++ e :: suf`.
4. `generic_syncFacts_sound_and_complete`: after `genericSyncFacts spec W`, any
   managed fact `f` (`spec.isManagedFact f = true`) is active at `W.now` iff
   `f ∈ spec.deriveFacts W.quant W.now`.
5. `generic_syncFacts_idempotent`: `genericSyncFacts` is strictly idempotent.
-/

namespace Charter

open Charter

/-- Polymorphic specification coupling a normative `Law σ` with a quantitative
state type `Q` and a managed fact derivation map `deriveFacts` (§3.2). -/
structure WorldSpec (σ : Sig) (Q : Type) where
  law                 : Law σ
  initQ               : Q
  isManagedFact       : σ.Fact → Bool
  deriveFacts         : Q → Time → List σ.Fact
  deriveFacts_managed : ∀ q t f, f ∈ deriveFacts q t → isManagedFact f = true

/-- Polymorphic coupled world state combining calendar time `now`, normative
institutional state `legal : LegalState σ`, and quantitative state `quant : Q`. -/
structure GenericWorldState (σ : Sig) (Q : Type) where
  now   : Time
  legal : LegalState σ
  quant : Q

instance {σ : Sig} {Q : Type} [DecidableEq Q] : DecidableEq (GenericWorldState σ Q) := by
  intro a b
  cases a with | mk n1 l1 q1 =>
  cases b with | mk n2 l2 q2 =>
  by_cases hn : n1 = n2
  · by_cases hl : l1 = l2
    · by_cases hq : q1 = q2
      · subst hn hl hq; exact isTrue rfl
      · exact isFalse (by intro h; injection h; contradiction)
    · exact isFalse (by intro h; injection h; contradiction)
  · exact isFalse (by intro h; injection h; contradiction)

/-- Canonical initial `GenericWorldState` for `spec : WorldSpec σ Q`. -/
def initGenericWorld {σ : Sig} {Q : Type} (spec : WorldSpec σ Q) : GenericWorldState σ Q :=
  { now   := 0
    legal := spec.law.init
    quant := spec.initQ }

/-- Synchronizes quantitative facts derived by `spec.deriveFacts W.quant W.now`
into `W.legal`, stripping all prior tuples `(f, _, _)` where
`spec.isManagedFact f == true` and appending fresh tuples stamped at `W.now`. -/
def genericSyncFacts {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) : GenericWorldState σ Q :=
  let cleaned := W.legal.filter fun p => !spec.isManagedFact p.1
  let derived := (spec.deriveFacts W.quant W.now).map (fun (f : σ.Fact) => (f, W.now, (none : Option Time)))
  { W with legal := cleaned ++ derived }

/-- Applies a pure quantitative mutation `f : Q → Q` to `W.quant` and
immediately synchronizes managed facts into `W.legal`. -/
def genericModifyQuant {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (f : Q → Q) : GenericWorldState σ Q :=
  genericSyncFacts spec { W with quant := f W.quant }

/-- Does single event `e` comply with all duties of `L` at institutional state `ls`? -/
def genericEventComplies {σ : Sig} (L : Law σ) (ls : LegalState σ) (e : Event σ) : Bool :=
  L.duties.all fun d => !breaches L ls e d

/-- Advances `GenericWorldState` by a single normative event `e : Event σ`,
updating `now := max W.now e.t` and stepping `legal := step spec.law W.legal e`. -/
def genericWorldStep {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (e : Event σ) : GenericWorldState σ Q :=
  { W with
    now   := max W.now e.t
    legal := step spec.law W.legal e }

/-- Executes a trace `tr : Trace σ` starting from initial world state `W0`. -/
def genericWorldTrace {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W0 : GenericWorldState σ Q) (tr : Trace σ) : GenericWorldState σ Q :=
  tr.foldl (genericWorldStep spec) W0

/-- Does step `i` of trace `tr` starting from `W0` comply with all duties of `spec.law`? -/
def genericWorldStepComplies {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W0 : GenericWorldState σ Q) (tr : Trace σ) (i : Nat) : Bool :=
  match tr[i]? with
  | none   => true
  | some e => genericEventComplies spec.law (genericWorldTrace spec W0 (tr.take i)).legal e

/-- A trace `tr` is authorized from world state `W0` under `spec` when every step
`i < tr.length` complies with `spec.law` at `(genericWorldTrace spec W0 (tr.take i)).legal`. -/
def GenericWorldAuthorized {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W0 : GenericWorldState σ Q) (tr : Trace σ) : Prop :=
  ∀ i, i < tr.length → genericWorldStepComplies spec W0 tr i = true

instance {σ : Sig} {Q : Type} (spec : WorldSpec σ Q) (W0 : GenericWorldState σ Q) (tr : Trace σ) :
    Decidable (GenericWorldAuthorized spec W0 tr) := by
  unfold GenericWorldAuthorized
  infer_instance

/-! ## Universal Refinement Theorems -/

/-- **Theorem 1 (`generic_worldStep_refines_legalStep`):**
Every single-event `genericWorldStep spec W e` refines the normative institutional
transition `step spec.law W.legal e`. -/
theorem generic_worldStep_refines_legalStep {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (e : Event σ),
      (genericWorldStep spec W e).legal = step spec.law W.legal e := by
  intro _ _ _
  rfl

/-- Starting from any `W : GenericWorldState σ Q`, the `legal` component of
`genericWorldTrace spec W tr` equals `tr.foldl (step spec.law) W.legal`. -/
theorem generic_worldTrace_legal_eq_foldl {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (tr : Trace σ) :
    (genericWorldTrace spec W tr).legal = tr.foldl (step spec.law) W.legal := by
  induction tr generalizing W with
  | nil => rfl
  | cons e rest ih =>
    simp only [genericWorldTrace, List.foldl_cons]
    exact ih (genericWorldStep spec W e)

/-- From `initGenericWorld spec`, `genericWorldTrace` produces the exact same
`LegalState σ` as `stateAfter spec.law tr`. -/
theorem generic_worldTrace_legal_eq_stateAfter {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (tr : Trace σ) :
    (genericWorldTrace spec (initGenericWorld spec) tr).legal = stateAfter spec.law tr := by
  rw [generic_worldTrace_legal_eq_foldl]
  rfl

/-- Stepwise compliance in `GenericWorldState` starting from `initGenericWorld spec`
is identical to normative `complies spec.law tr i`. -/
theorem generic_worldStepComplies_eq_complies {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (tr : Trace σ) (i : Nat) :
    genericWorldStepComplies spec (initGenericWorld spec) tr i = complies spec.law tr i := by
  unfold genericWorldStepComplies complies genericEventComplies stateBefore
  rw [generic_worldTrace_legal_eq_stateAfter spec (tr.take i)]
  cases tr[i]? <;> rfl

/-- `GenericWorldAuthorized spec (initGenericWorld spec) tr` holds iff `Authorized spec.law tr` holds. -/
theorem generic_worldAuthorized_iff_authorized {σ : Sig} {Q : Type}
    (spec : WorldSpec σ Q) (tr : Trace σ) :
    GenericWorldAuthorized spec (initGenericWorld spec) tr ↔ Authorized spec.law tr := by
  unfold GenericWorldAuthorized Authorized
  simp only [generic_worldStepComplies_eq_complies]

/-- **Theorem 2 (`generic_worldTrace_refines_stateAfter`):**
Combined trace-refinement and authorization-equivalence theorem for any
`WorldSpec σ Q`. -/
theorem generic_worldTrace_refines_stateAfter {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (tr : Trace σ),
      (genericWorldTrace spec (initGenericWorld spec) tr).legal = stateAfter spec.law tr ∧
      (GenericWorldAuthorized spec (initGenericWorld spec) tr ↔ Authorized spec.law tr) := by
  intro spec tr
  exact ⟨generic_worldTrace_legal_eq_stateAfter spec tr,
         generic_worldAuthorized_iff_authorized spec tr⟩

private theorem exists_split_of_getElem? {α : Type} :
    ∀ (xs : List α) (i : Nat) (e : α),
      xs[i]? = some e →
      xs = xs.take i ++ e :: xs.drop (i + 1)
  | [], _, _, h => by simp at h
  | x :: rest, 0, e, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | x :: rest, i + 1, e, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := exists_split_of_getElem? rest i e h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (x :: ·) ih

/-- **Theorem 3 (`generic_worldAuthorized_iff_prefix_split`):**
Equivalence between index-based `GenericWorldAuthorized` and prefix-split
characterization across all decompositions `tr = pre ++ e :: suf`. -/
theorem generic_worldAuthorized_iff_prefix_split {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (W0 : GenericWorldState σ Q) (tr : Trace σ),
      GenericWorldAuthorized spec W0 tr ↔
      ∀ pre e suf, tr = pre ++ e :: suf →
        (spec.law.duties.all fun d => !breaches spec.law (genericWorldTrace spec W0 pre).legal e d) = true := by
  intro spec W0 tr
  constructor
  · intro hAuth pre e suf hEq
    subst hEq
    have hLen : pre.length < (pre ++ e :: suf).length := by simp
    have hStep := hAuth pre.length hLen
    unfold genericWorldStepComplies genericEventComplies at hStep
    have hGet : (pre ++ e :: suf)[pre.length]? = some e := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hTake : List.take pre.length (pre ++ e :: suf) = pre := by
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    rw [hGet, hTake] at hStep
    exact hStep
  · intro hSplit i hi
    unfold genericWorldStepComplies genericEventComplies
    have hGet : tr[i]? = some (tr[i]'hi) := List.getElem?_eq_getElem hi
    rw [hGet]
    have hDecomp := exists_split_of_getElem? tr i (tr[i]'hi) hGet
    exact hSplit (tr.take i) (tr[i]'hi) (tr.drop (i + 1)) hDecomp

/-! ## Quantitative Synchronization Soundness, Completeness & Idempotence -/

private theorem activeAt_append {σ : Sig} (xs ys : LegalState σ) (now : Time) (f : σ.Fact) :
    LegalState.activeAt (xs ++ ys) now f =
      (LegalState.activeAt xs now f || LegalState.activeAt ys now f) := by
  unfold LegalState.activeAt
  exact List.any_append

private theorem activeAt_cleaned_eq_false {σ : Sig}
    (isManaged : σ.Fact → Bool) (ls : LegalState σ) (now : Time) (f : σ.Fact)
    (hf : isManaged f = true) :
    LegalState.activeAt (ls.filter fun p => !isManaged p.1) now f = false := by
  unfold LegalState.activeAt
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hKeep : (!isManaged hd.1)
    · exact ih
    · simp only [↓reduceIte, List.any_cons]
      have hNe : (hd.1 == f) = false := by
        cases hEq : (hd.1 == f)
        · rfl
        · have hSame : hd.1 = f := beq_iff_eq.mp hEq
          rw [hSame, hf] at hKeep
          contradiction
      simp [hNe, ih]

private theorem activeAt_map_none_iff_mem {σ : Sig}
    (fs : List σ.Fact) (now : Time) (f : σ.Fact) :
    @LegalState.activeAt σ (fs.map (fun (g : σ.Fact) => (g, now, (none : Option Time)))) now f = true ↔
      f ∈ fs := by
  unfold LegalState.activeAt
  induction fs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.any_cons, Bool.and_true, Bool.or_eq_true, List.mem_cons]
    constructor
    · intro h
      rcases h with hEq | hTl
      · left
        exact (beq_iff_eq.mp hEq).symm
      · right
        exact ih.mp hTl
    · intro h
      rcases h with hEq | hTl
      · left
        subst hEq
        exact beq_self_eq_true _
      · right
        exact ih.mpr hTl

/-- **Theorem 4 (`generic_syncFacts_sound_and_complete`):**
For any managed fact `f` (`spec.isManagedFact f = true`), `f` is active in
`(genericSyncFacts spec W).legal` at `W.now` if and only if
`f ∈ spec.deriveFacts W.quant W.now`. -/
theorem generic_syncFacts_sound_and_complete {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (f : σ.Fact),
      spec.isManagedFact f = true →
      ((genericSyncFacts spec W).legal.activeAt W.now f = true ↔
        f ∈ spec.deriveFacts W.quant W.now) := by
  intro spec W f hf
  unfold genericSyncFacts
  dsimp only
  rw [activeAt_append]
  rw [activeAt_cleaned_eq_false spec.isManagedFact W.legal W.now f hf]
  simp only [Bool.false_or]
  exact activeAt_map_none_iff_mem (spec.deriveFacts W.quant W.now) W.now f

private theorem filter_map_none_eq_nil {σ : Sig}
    (isManaged : σ.Fact → Bool) (now : Time) :
    ∀ (fs : List σ.Fact),
      (∀ f ∈ fs, isManaged f = true) →
      ((fs.map (fun (f : σ.Fact) => (f, now, (none : Option Time)))).filter
        fun p => !isManaged p.1) = []
  | [], _ => rfl
  | hd :: tl, h => by
    have hhd : isManaged hd = true := h hd (List.mem_cons_self ..)
    have htl : ∀ f ∈ tl, isManaged f = true := fun f hf => h f (List.mem_cons_of_mem hd hf)
    simp only [List.map_cons, List.filter_cons, hhd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact filter_map_none_eq_nil isManaged now tl htl

/-- **Theorem 5 (`generic_syncFacts_idempotent`):**
Synchronizing managed facts twice in a row produces the exact same
`GenericWorldState` without accumulating duplicate tuples. -/
theorem generic_syncFacts_idempotent {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (W : GenericWorldState σ Q),
      genericSyncFacts spec (genericSyncFacts spec W) = genericSyncFacts spec W := by
  intro spec W
  unfold genericSyncFacts
  dsimp only
  congr 1
  rw [List.filter_append, List.filter_filter]
  simp only [Bool.and_self]
  have hEmpty := filter_map_none_eq_nil spec.isManagedFact W.now
    (spec.deriveFacts W.quant W.now)
    (fun f hf => spec.deriveFacts_managed W.quant W.now f hf)
  rw [hEmpty, List.append_nil]

private theorem activeAt_cleaned_unmanaged {σ : Sig}
    (isManaged : σ.Fact → Bool) (ls : LegalState σ) (t : Time) (f : σ.Fact)
    (hf : isManaged f = false) :
    LegalState.activeAt (ls.filter fun p => !isManaged p.1) t f =
      LegalState.activeAt ls t f := by
  unfold LegalState.activeAt
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hKeep : (!isManaged hd.1)
    · have hNe : (hd.1 == f) = false := by
        cases hEq : (hd.1 == f)
        · rfl
        · have hSame : hd.1 = f := beq_iff_eq.mp hEq
          rw [hSame, hf] at hKeep
          contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, hNe, Bool.false_and, Bool.false_or, ih]
    · simp only [↓reduceIte, List.any_cons, ih]

private theorem activeAt_derived_unmanaged_eq_false {σ : Sig}
    (isManaged : σ.Fact → Bool) (now t : Time) (f : σ.Fact)
    (hf : isManaged f = false) :
    ∀ (fs : List σ.Fact),
      (∀ g ∈ fs, isManaged g = true) →
      @LegalState.activeAt σ (fs.map (fun (g : σ.Fact) => (g, now, (none : Option Time)))) t f = false
  | [], _ => rfl
  | g :: tl, h => by
    have hg : isManaged g = true := h g (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, isManaged x = true := fun x hx => h x (List.mem_cons_of_mem g hx)
    have hNe : (g == f) = false := by
      cases hEq : (g == f)
      · rfl
      · have hSame : g = f := beq_iff_eq.mp hEq
        rw [hSame, hf] at hg
        contradiction
    unfold LegalState.activeAt
    simp only [List.map_cons, List.any_cons, hNe, Bool.false_and, Bool.false_or]
    exact activeAt_derived_unmanaged_eq_false isManaged now t f hf tl htl

/-- **Theorem 6 (`generic_syncFacts_preserves_unmanaged`):**
Synchronizing quantitative facts never alters the active status of any
unmanaged normative fact (`spec.isManagedFact f = false`) at any timestamp `t`. -/
theorem generic_syncFacts_preserves_unmanaged {σ : Sig} {Q : Type} :
    ∀ (spec : WorldSpec σ Q) (W : GenericWorldState σ Q) (t : Time) (f : σ.Fact),
      spec.isManagedFact f = false →
      (genericSyncFacts spec W).legal.activeAt t f = W.legal.activeAt t f := by
  intro spec W t f hf
  unfold genericSyncFacts
  dsimp only
  rw [activeAt_append]
  rw [activeAt_cleaned_unmanaged spec.isManagedFact W.legal t f hf]
  have hDer := activeAt_derived_unmanaged_eq_false spec.isManagedFact W.now t f hf
    (spec.deriveFacts W.quant W.now)
    (fun g hg => spec.deriveFacts_managed W.quant W.now g hg)
  rw [hDer, Bool.or_false]

namespace Core

export Charter (
  WorldSpec
  GenericWorldState
  initGenericWorld
  genericSyncFacts
  genericModifyQuant
  genericEventComplies
  genericWorldStep
  genericWorldTrace
  genericWorldStepComplies
  GenericWorldAuthorized
  generic_worldStep_refines_legalStep
  generic_worldTrace_legal_eq_foldl
  generic_worldTrace_legal_eq_stateAfter
  generic_worldStepComplies_eq_complies
  generic_worldAuthorized_iff_authorized
  generic_worldTrace_refines_stateAfter
  generic_worldAuthorized_iff_prefix_split
  generic_syncFacts_sound_and_complete
  generic_syncFacts_idempotent
  generic_syncFacts_preserves_unmanaged
)

end Core

end Charter
