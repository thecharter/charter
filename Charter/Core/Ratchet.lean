import Charter.Core.Semantics

/-!
# Charter.Core.Ratchet — Universal Parameter Exploration & Bilateral Ratchets

Formalizes the law-agnostic theory of constitutional amendments, parameter
calibration bounds, bilateral ratchets, and entrenched core preservation (§8):
1. **`RatchetSpec P σ`**:
   Specifies `wellCalibrated : P → Bool`, `bilateralRatchet : P → P → Bool`,
   and `entrenchedCore : Law σ → Law σ → Bool`.
2. **`ValidAmendmentStep` & `ValidAmendmentTrajectory`**:
   Single-step and multi-step amendment validity predicates (with `Decidable`
   instances for kernel-checked trajectory verification).
3. **`universal_ratchet_preserves_entrenched_core` & `universal_ratchet_trajectory_safe`**:
   Universal meta-theorems proving that any valid amendment step or finite
   amendment trajectory from `p₀` to `pₙ` preserves calibration bounds,
   bilateral parameter ratchets, and the entrenched Hohfeldian core.
4. **`sweepParameterGrid` & `renderSweepTable`**:
   Evaluates candidate parameter regimes against a baseline regime for CLI
   exploration (`charter explore`).
-/

namespace Charter

open SPL

/-- Universal specification of parameter calibration, bilateral parameter
ratchets, and entrenched normative core preservation over parameter space `P`
and signature `σ` (§8). -/
structure RatchetSpec (P : Type) (σ : Sig) where
  wellCalibrated   : P → Bool
  bilateralRatchet : P → P → Bool
  entrenchedCore   : Law σ → Law σ → Bool

/-- Canonical structural entrenchment check verifying that `L₂` retains all
duty IDs, immunity IDs, and power IDs of `L₁`. -/
def defaultEntrenchedCore {σ : Sig} (L₁ L₂ : Law σ) : Bool :=
  (L₁.dutyIds.all fun did => L₂.dutyIds.contains did) &&
  (L₁.immunityIds.all fun iid => L₂.immunityIds.contains iid) &&
  (L₁.powerIds.all fun pid => L₂.powerIds.contains pid)

private theorem all_contains_refl {α : Type} [DecidableEq α] (xs : List α) :
    (xs.all fun x => xs.contains x) = true := by
  rw [List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr hx

private theorem all_contains_trans {α : Type} [DecidableEq α] {xs ys zs : List α}
    (h1 : (xs.all fun x => ys.contains x) = true)
    (h2 : (ys.all fun y => zs.contains y) = true) :
    (xs.all fun x => zs.contains x) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro x hx
  have hy : x ∈ ys := List.contains_iff_mem.mp (h1 x hx)
  exact h2 x hy

/-- `defaultEntrenchedCore` is reflexive for every `L : Law σ`. -/
theorem defaultEntrenchedCore_refl {σ : Sig} (L : Law σ) :
    defaultEntrenchedCore L L = true := by
  unfold defaultEntrenchedCore
  simp only [all_contains_refl, Bool.and_self]

/-- `defaultEntrenchedCore` is transitive across arbitrary laws `L₁, L₂, L₃ : Law σ`. -/
theorem defaultEntrenchedCore_trans {σ : Sig} (L₁ L₂ L₃ : Law σ)
    (h12 : defaultEntrenchedCore L₁ L₂ = true)
    (h23 : defaultEntrenchedCore L₂ L₃ = true) :
    defaultEntrenchedCore L₁ L₃ = true := by
  unfold defaultEntrenchedCore at h12 h23 ⊢
  simp only [Bool.and_eq_true] at h12 h23 ⊢
  exact ⟨⟨all_contains_trans h12.1.1 h23.1.1,
          all_contains_trans h12.1.2 h23.1.2⟩,
         all_contains_trans h12.2 h23.2⟩

/-- A single amendment step `p₁ → p₂` is valid under `R : RatchetSpec P σ` and
`lawOf : P → Law σ` when both regimes are well-calibrated, the bilateral
parameter ratchet holds from `p₁` to `p₂`, and the entrenched normative core
is preserved from `lawOf p₁` to `lawOf p₂` (§8). -/
def ValidAmendmentStep {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ) (p₁ p₂ : P) : Prop :=
  R.wellCalibrated p₁ = true ∧
  R.wellCalibrated p₂ = true ∧
  R.bilateralRatchet p₁ p₂ = true ∧
  R.entrenchedCore (lawOf p₁) (lawOf p₂) = true

instance {P : Type} {σ : Sig} (R : RatchetSpec P σ) (lawOf : P → Law σ) (p₁ p₂ : P) :
    Decidable (ValidAmendmentStep R lawOf p₁ p₂) := by
  unfold ValidAmendmentStep
  infer_instance

/-- Multi-step amendment trajectory predicate for chains `p₀ :: p₁ :: ... :: pₙ` (§8). -/
def ValidAmendmentTrajectory {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ) : List P → Prop
  | [] => True
  | [p] =>
      R.wellCalibrated p = true ∧
      R.bilateralRatchet p p = true ∧
      R.entrenchedCore (lawOf p) (lawOf p) = true
  | [p₁, p₂] =>
      ValidAmendmentStep R lawOf p₁ p₂
  | p₁ :: p₂ :: p₃ :: rest =>
      ValidAmendmentStep R lawOf p₁ p₂ ∧
      ValidAmendmentTrajectory R lawOf (p₂ :: p₃ :: rest)

instance {P : Type} {σ : Sig} (R : RatchetSpec P σ) (lawOf : P → Law σ) :
    ∀ (tr : List P), Decidable (ValidAmendmentTrajectory R lawOf tr)
  | [] => isTrue trivial
  | [p] => by
    unfold ValidAmendmentTrajectory
    infer_instance
  | [p₁, p₂] => by
    unfold ValidAmendmentTrajectory
    infer_instance
  | p₁ :: p₂ :: p₃ :: rest => by
    unfold ValidAmendmentTrajectory
    have := instDecidableValidAmendmentTrajectory R lawOf (p₂ :: p₃ :: rest)
    infer_instance

/-- **Universal Single-Step Ratchet Theorem (`universal_ratchet_preserves_entrenched_core`):**
Any valid amendment step `ValidAmendmentStep R lawOf p₁ p₂` guarantees that `p₂`
remains well-calibrated, satisfies `R.bilateralRatchet p₁ p₂ = true`, and
preserves the entrenched core `R.entrenchedCore (lawOf p₁) (lawOf p₂) = true` (§8). -/
theorem universal_ratchet_preserves_entrenched_core {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ) (p₁ p₂ : P)
    (hStep : ValidAmendmentStep R lawOf p₁ p₂) :
    R.wellCalibrated p₁ = true ∧
    R.wellCalibrated p₂ = true ∧
    R.bilateralRatchet p₁ p₂ = true ∧
    R.entrenchedCore (lawOf p₁) (lawOf p₂) = true :=
  hStep

/-- **Universal Multi-Step Ratchet Meta-Theorem (`universal_ratchet_trajectory_safe`):**
If `R.bilateralRatchet` and `R.entrenchedCore` are transitive, then any
non-empty `ValidAmendmentTrajectory` from `p₀` to `pₙ = (p₀ :: rest).getLast _`
satisfies `R.wellCalibrated pₙ = true ∧ R.bilateralRatchet p₀ pₙ = true ∧
R.entrenchedCore (lawOf p₀) (lawOf pₙ) = true` (§8). -/
theorem universal_ratchet_trajectory_safe {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ)
    (hRatTrans : ∀ a b c,
      R.bilateralRatchet a b = true →
      R.bilateralRatchet b c = true →
      R.bilateralRatchet a c = true)
    (hCoreTrans : ∀ L₁ L₂ L₃,
      R.entrenchedCore L₁ L₂ = true →
      R.entrenchedCore L₂ L₃ = true →
      R.entrenchedCore L₁ L₃ = true) :
    ∀ (p₀ : P) (rest : List P),
      ValidAmendmentTrajectory R lawOf (p₀ :: rest) →
      let pₙ := (p₀ :: rest).getLast (List.cons_ne_nil p₀ rest)
      R.wellCalibrated pₙ = true ∧
      R.bilateralRatchet p₀ pₙ = true ∧
      R.entrenchedCore (lawOf p₀) (lawOf pₙ) = true
  | p₀, [], hTraj => by
    simp only [ValidAmendmentTrajectory] at hTraj
    exact hTraj
  | p₀, [p₁], hTraj => by
    simp only [ValidAmendmentTrajectory, ValidAmendmentStep] at hTraj
    exact ⟨hTraj.2.1, hTraj.2.2.1, hTraj.2.2.2⟩
  | p₀, p₁ :: p₂ :: tail, hTraj => by
    simp only [ValidAmendmentTrajectory] at hTraj
    rcases hTraj with ⟨hStep, hRest⟩
    have ih := universal_ratchet_trajectory_safe R lawOf hRatTrans hCoreTrans p₁ (p₂ :: tail) hRest
    dsimp only at ih ⊢
    have hLast : (p₀ :: p₁ :: p₂ :: tail).getLast (List.cons_ne_nil p₀ _) =
                 (p₁ :: p₂ :: tail).getLast (List.cons_ne_nil p₁ _) := rfl
    rw [hLast]
    refine ⟨ih.1, ?_, ?_⟩
    · exact hRatTrans p₀ p₁ _ hStep.2.2.1 ih.2.1
    · exact hCoreTrans (lawOf p₀) (lawOf p₁) _ hStep.2.2.2 ih.2.2

/-- Evaluates a grid of candidate parameter regimes `(label, p)` against a
`baseline` regime under `R : RatchetSpec P σ` and `lawOf : P → Law σ`,
returning `(label, wellCalibrated p, bilateralRatchet baseline p, entrenchedCore (lawOf baseline) (lawOf p))`
for each candidate (§8). -/
def sweepParameterGrid {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ)
    (baseline : P) (candidates : List (String × P)) :
    List (String × Bool × Bool × Bool) :=
  candidates.map fun (label, p) =>
    (label,
     R.wellCalibrated p,
     R.bilateralRatchet baseline p,
     R.entrenchedCore (lawOf baseline) (lawOf p))

/-- Every candidate `(label, p)` whose row in `sweepParameterGrid` has all three
booleans `true` forms a `ValidAmendmentStep R lawOf baseline p` whenever
`R.wellCalibrated baseline = true`. -/
theorem sweepParameterGrid_sound {P : Type} {σ : Sig}
    (R : RatchetSpec P σ) (lawOf : P → Law σ) (baseline p : P)
    (hBase : R.wellCalibrated baseline = true)
    (hCal : R.wellCalibrated p = true)
    (hRat : R.bilateralRatchet baseline p = true)
    (hCore : R.entrenchedCore (lawOf baseline) (lawOf p) = true) :
    ValidAmendmentStep R lawOf baseline p :=
  ⟨hBase, hCal, hRat, hCore⟩

/-- Renders the output of `sweepParameterGrid` as a human-readable Markdown table. -/
def renderSweepTable (rows : List (String × Bool × Bool × Bool)) : String :=
  let header :=
    "| Candidate Regime | Well-Calibrated | Bilateral Ratchet | Entrenched Core | Verdict |\n" ++
    "| :--- | :---: | :---: | :---: | :---: |"
  let body := rows.map fun (label, cal, rat, core) =>
    let bStr (b : Bool) : String := if b then "PASS" else "FAIL"
    let verdict := if cal && rat && core then "ADMISSIBLE" else "REJECTED"
    s!"| {label} | {bStr cal} | {bStr rat} | {bStr core} | {verdict} |"
  String.intercalate "\n" (header :: body)

namespace Core

export Charter (
  RatchetSpec
  defaultEntrenchedCore
  defaultEntrenchedCore_refl
  defaultEntrenchedCore_trans
  ValidAmendmentStep
  ValidAmendmentTrajectory
  universal_ratchet_preserves_entrenched_core
  universal_ratchet_trajectory_safe
  sweepParameterGrid
  sweepParameterGrid_sound
  renderSweepTable
)

end Core

end Charter
