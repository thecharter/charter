import Charter.Core.Spec
import Charter.Core.Derivation

/-!
# Charter.Core.Amend — Rule-Level `Amend`, Reflexive Entrenchment, & `CIR` Ratchet Proof (`D11`, `D25`, `G3.5`)

Implements live `CIR` rule-level `Amend` transitions (`014.3`) and reflexive `Immunity`
entrenchment (`014.5`, `T23`, `T24`):
1. `neutralizeTypeSpec`: repeals normative authority/effects of a repealed rule while keeping
   its declaration performable (`Mission Law 1`: occurrence is never blocked; a repealed power
   occurs and is void).
2. `reflexiveProtectedIds`: computes the reflexively closed set of rule IDs protected by an
   entrenchment `Immunity` (`imId` itself, `im.protects`, all `Entrenched Invariant`s, and
   validity-governing dependencies — `D11` clause 3).
3. `cir_ratchet_trajectory_preserves_entrenched`: kernel-checked theorem over `Core.Spec`
   proving that across any finite trajectory of valid `Amend` steps, the entrenchment
   immunity itself, every rule in `im.protects`, and every `Entrenched Invariant` retain
   their exact `TypeSpec` records (`T24`).
-/

namespace Charter

/-- Transient internal store domain signaling a valid `Amend` transition inside `newContext`. -/
def amendCommitDom : String := "$amend_commit"

namespace Amend

/-- Neutralize a repealed rule's normative effect while keeping acts performable (`Mission Law 1`). -/
def neutralizeTypeSpec (t : TypeSpec) : TypeSpec :=
  match t.kind with
  | .act a =>
    { t with
      derivation := []
      defeasibleRules := []
      kind := .act { a with effects := [], syncs := [], validWhen := [.boolLit false], exceptUnder := [] } }
  | .immunity im =>
    { t with
      derivation := []
      defeasibleRules := []
      kind := .immunity { im with against := [], protects := [] } }
  | .duty du =>
    { t with
      derivation := []
      defeasibleRules := []
      kind := .duty { du with creatingActs := [], violatedWhen := [] } }
  | .event ev =>
    { t with
      derivation := []
      kind := .event { ev with effects := [], syncs := [] } }
  | .fact _ =>
    { t with derivation := [], defeasibleRules := [] }

def applyRepeals : Spec → List DomId → Spec
  | s, [] => s
  | s, r :: rs => applyRepeals (s.adjustDecl r neutralizeTypeSpec) rs

def applyInstallDecl : Spec → Decl → Spec
  | s, .typeDecl d t => s.insertDecl d t
  | s, .typeExt d cs _ => s.adjustDecl d (TypeSpec.applyExt cs)
  | s, _ => s

def applyInstallDecls : Spec → List Decl → Spec
  | s, [] => s
  | s, d :: ds => applyInstallDecls (applyInstallDecl s d) ds

/-- Apply an `Amend` act's `repeals` and `installs` rule changes to `Spec`. -/
def applyAmendChange (s : Spec) (repeals : List DomId) (installs : List Decl) : Spec :=
  applyInstallDecls (applyRepeals s repeals) installs

def touchedByDecls : List Decl → List DomId
  | [] => []
  | .typeDecl d _ :: ds => d :: touchedByDecls ds
  | .typeExt d _ _ :: ds => d :: touchedByDecls ds
  | _ :: ds => touchedByDecls ds

/-- All rule IDs modified by `(repeals, installs)`. -/
def touchedIds (repeals : List DomId) (installs : List Decl) : List DomId :=
  repeals ++ touchedByDecls installs

/--Dependencies governing `im`'s activation/lifting and `amendAct`'s `Valid when` (`D11` clause 3). -/
def governingDeps (s : Spec) (imId : DomId) (imTs : TypeSpec) (im : ImmunitySpec)
    (amendActId : DomId) : List DomId :=
  let imVars := s.components imId
  let imDerivDeps := imTs.derivation.flatMap fun
    | .dv ys tm => (Stratify.deps s 200 ys .pos tm).map (·.1)
    | .holdsWhen tm => (Stratify.deps s 200 imVars .pos tm).map (·.1)
    | .defeasibleDAG _ rs => rs.flatMap fun r => (Stratify.deps s 200 imVars .pos r.cond).map (·.1)
  let unlessDeps := (Stratify.depsList s 200 imVars .pos im.unlessConds).map (·.1)
  let actValidDeps := match s.findDecl amendActId with
    | some { kind := .act a, .. } =>
      let av := s.components amendActId
      (Stratify.depsList s 200 av .pos a.validWhen).map (·.1)
    | _ => []
  (imDerivDeps ++ unlessDeps ++ actValidDeps).eraseDups

/-- Reflexively closed rule-ID set protected by entrenchment immunity `imId` (`D11` clause 3):
includes `imId` itself, `im.protects`, all `Entrenched Invariant`s, and `extraDeps`. -/
def reflexiveProtectedIds (s : Spec) (imId : DomId) (im : ImmunitySpec)
    (extraDeps : List DomId := []) : List DomId :=
  imId :: (im.protects ++ s.entrenchedInvariants ++ extraDeps)

/-- Apply a triggered `Amend` act `actId` to `s`. -/
def applyTriggeredAmend (s : Spec) (actId : DomId) : Spec :=
  match s.findDecl actId with
  | some { kind := .act a, .. } =>
    if !a.isAmend then s
    else
      let installs := (s.amendBodies.find? (·.1 == actId)).map (·.2) |>.getD []
      applyAmendChange s a.repeals installs
  | _ => s

/-! ## Universal `CIR` Ratchet Preservation Proof (`D11`, `D25`, `G3.5`, `T24`) -/

theorem find?_filter_ne_dom (d r : DomId) (hne : d ≠ r) :
    ∀ (xs : List (DomId × TypeSpec)),
      (xs.filter (fun p => p.1 != d)).find? (fun p => p.1 == r) =
      xs.find? (fun p => p.1 == r)
  | [] => rfl
  | (k, t) :: rest => by
    simp only [List.filter_cons]
    by_cases hkd : (k != d) = true
    · rw [if_pos hkd]
      simp only [List.find?_cons]
      cases k == r
      · exact find?_filter_ne_dom d r hne rest
      · rfl
    · rw [if_neg hkd]
      have hkeq : k = d := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hkd
        exact hkd
      subst hkeq
      have hdrF : (k == r) = false := beq_false_of_ne hne
      simp only [List.find?_cons, hdrF]
      exact find?_filter_ne_dom k r hne rest

theorem insertDecl_lookupDecl_ne (s : Spec) (d r : DomId) (t : TypeSpec) (hne : d ≠ r) :
    (s.insertDecl d t).lookupDecl r = s.lookupDecl r := by
  unfold Spec.insertDecl Spec.lookupDecl
  have hdrF : (d == r) = false := beq_false_of_ne hne
  simp only [List.find?_cons, hdrF, find?_filter_ne_dom d r hne]

theorem find?_map_adjust_ne (d r : DomId) (f : TypeSpec → TypeSpec) (hne : d ≠ r) :
    ∀ (xs : List (DomId × TypeSpec)),
      (xs.map fun (d', t) => if d' == d then (d', f t) else (d', t)).find? (fun p => p.1 == r) =
      xs.find? (fun p => p.1 == r)
  | [] => rfl
  | (k, t) :: rest => by
    simp only [List.map_cons, List.find?_cons]
    by_cases hkd : (k == d) = true
    · have hkeq : k = d := eq_of_beq hkd
      subst hkeq
      have hdrF : (k == r) = false := beq_false_of_ne hne
      simp only [hkd, ↓reduceIte, hdrF]
      exact find?_map_adjust_ne k r f hne rest
    · have hkdF : (k == d) = false := Bool.eq_false_iff.mpr hkd
      simp only [hkdF, Bool.false_eq_true, ↓reduceIte]
      cases k == r
      · exact find?_map_adjust_ne d r f hne rest
      · rfl

theorem adjustDecl_lookupDecl_ne (s : Spec) (d r : DomId) (f : TypeSpec → TypeSpec) (hne : d ≠ r) :
    (s.adjustDecl d f).lookupDecl r = s.lookupDecl r := by
  unfold Spec.adjustDecl Spec.lookupDecl
  simp only [find?_map_adjust_ne d r f hne]

theorem applyRepeals_lookupDecl_not_mem (r : DomId) :
    ∀ (rs : List DomId) (s : Spec), r ∉ rs → (applyRepeals s rs).lookupDecl r = s.lookupDecl r
  | [], s, _ => rfl
  | x :: xs, s, hnm => by
    have hxr : x ≠ r := fun h => hnm (h ▸ List.mem_cons_self)
    have hxs : r ∉ xs := fun hm => hnm (List.mem_cons_of_mem x hm)
    simp only [applyRepeals]
    rw [applyRepeals_lookupDecl_not_mem r xs _ hxs, adjustDecl_lookupDecl_ne s x r _ hxr]

theorem applyInstallDecls_lookupDecl_not_mem (r : DomId) :
    ∀ (ds : List Decl) (s : Spec), r ∉ touchedByDecls ds → (applyInstallDecls s ds).lookupDecl r = s.lookupDecl r
  | [], s, _ => rfl
  | d :: ds, s, hnm => by
    cases d with
    | typeDecl k t =>
      simp only [touchedByDecls, List.mem_cons, not_or] at hnm
      have hkr : k ≠ r := fun h => hnm.1 h.symm
      simp only [applyInstallDecls, applyInstallDecl]
      rw [applyInstallDecls_lookupDecl_not_mem r ds _ hnm.2, insertDecl_lookupDecl_ne s k r t hkr]
    | typeExt k cs extK =>
      simp only [touchedByDecls, List.mem_cons, not_or] at hnm
      have hkr : k ≠ r := fun h => hnm.1 h.symm
      simp only [applyInstallDecls, applyInstallDecl]
      rw [applyInstallDecls_lookupDecl_not_mem r ds _ hnm.2, adjustDecl_lookupDecl_ne s k r _ hkr]
    | placeholder _ _ | clause _ | document _ _ _ _ | param _ _ _
    | module _ _ _ | use _ _ _ | property _ | amendInstall _ _ | regime _ =>
      simp only [touchedByDecls] at hnm
      simp only [applyInstallDecls, applyInstallDecl]
      exact applyInstallDecls_lookupDecl_not_mem r ds s hnm

/-- Any rule `r ∉ touchedIds repeals installs` is preserved identically across `applyAmendChange`. -/
theorem applyAmendChange_lookupDecl_untouched (s : Spec) (repeals : List DomId) (installs : List Decl)
    (r : DomId) (hUntouched : r ∉ touchedIds repeals installs) :
    (applyAmendChange s repeals installs).lookupDecl r = s.lookupDecl r := by
  unfold touchedIds at hUntouched
  rw [List.mem_append, not_or] at hUntouched
  unfold applyAmendChange
  rw [applyInstallDecls_lookupDecl_not_mem r installs _ hUntouched.2,
      applyRepeals_lookupDecl_not_mem r repeals s hUntouched.1]

/-- Reflexivity (`D11` clause 3): an entrenchment immunity is always a member of its own protected set. -/
theorem reflexive_self_protected (s : Spec) (imId : DomId) (im : ImmunitySpec) (deps : List DomId) :
    imId ∈ reflexiveProtectedIds s imId im deps :=
  List.mem_cons_self

/-- A valid `Amend` step under active entrenchment set `protectedSet` touches none of `protectedSet`. -/
def ValidCIRAmendStep (protectedSet : List DomId) (s : Spec)
    (repeals : List DomId) (installs : List Decl) (s' : Spec) : Prop :=
  (∀ r ∈ protectedSet, r ∉ touchedIds repeals installs) ∧
  s' = applyAmendChange s repeals installs

/-- Arbitrary-length finite trajectory of valid `CIR` `Amend` steps. -/
inductive ValidCIRAmendTrace (protectedSet : List DomId) : Spec → Spec → Prop where
  | refl (s : Spec) : ValidCIRAmendTrace protectedSet s s
  | step {s₁ s₂ s₃ : Spec} (repeals : List DomId) (installs : List Decl) :
      ValidCIRAmendStep protectedSet s₁ repeals installs s₂ →
      ValidCIRAmendTrace protectedSet s₂ s₃ →
      ValidCIRAmendTrace protectedSet s₁ s₃

theorem valid_trace_preserves_set {protectedSet : List DomId} {s₀ sₙ : Spec}
    (hTrace : ValidCIRAmendTrace protectedSet s₀ sₙ) :
    ∀ r ∈ protectedSet, sₙ.lookupDecl r = s₀.lookupDecl r := by
  induction hTrace with
  | refl _ => intros; rfl
  | step repeals installs hStep _ ih =>
    intro r hr
    rcases hStep with ⟨hDisj, rfl⟩
    rw [ih r hr]
    exact applyAmendChange_lookupDecl_untouched _ repeals installs r (hDisj r hr)

/-- **Universal `CIR` Ratchet Preservation Theorem (`D11`, `D25`, `G3.5`, `T24`):**
Across any valid `Amend` trajectory under active reflexive entrenchment `imId`,
(1) `imId` itself is preserved intact (preventing two-step ratchet repeal),
(2) every rule named in `im.protects` is preserved intact, and
(3) every `Entrenched Invariant` of `s₀` is preserved intact. -/
theorem cir_ratchet_trajectory_preserves_entrenched
    (s₀ sₙ : Spec) (imId : DomId) (im : ImmunitySpec) (deps : List DomId)
    (hTrace : ValidCIRAmendTrace (reflexiveProtectedIds s₀ imId im deps) s₀ sₙ) :
    sₙ.lookupDecl imId = s₀.lookupDecl imId ∧
    (∀ r ∈ im.protects, sₙ.lookupDecl r = s₀.lookupDecl r) ∧
    (∀ inv ∈ s₀.entrenchedInvariants, sₙ.lookupDecl inv = s₀.lookupDecl inv) := by
  have hAll := valid_trace_preserves_set hTrace
  refine ⟨hAll imId List.mem_cons_self, ?_, ?_⟩
  · intro r hr
    apply hAll r
    exact List.mem_cons_of_mem imId (List.mem_append_left _ (List.mem_append_left _ hr))
  · intro inv hinv
    apply hAll inv
    exact List.mem_cons_of_mem imId (List.mem_append_left _ (List.mem_append_right _ hinv))

end Amend

end Charter
