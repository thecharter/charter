import Charter.Core.Scale

/-!
# Charter.Verify.ArithLemmas — Kernel-Proved Scaled Integer Division Lemmas (`#75`)

General all-parameter lemmas over `Charter.mulDivRound` (`Floor` and `Ceil`) used by
`Charter.Verify.InductiveArith` to discharge inductive conservation, floor/ceiling
non-negativity, and atomic zero-crossing base-split obligations in the proof kernel.
-/

namespace Charter.Verify.ArithLemmas

def mdrFloor (x num den : Int) : Int :=
  if den ≤ 0 then 0 else Int.fdiv (x * num) den

def mdrCeil (x num den : Int) : Int :=
  if den ≤ 0 then 0
  else
    let q := Int.fdiv (x * num) den
    let r := Int.fmod (x * num) den
    if r == 0 then q else q + 1

theorem mdrFloor_matches_mulDivRound (x num den : Int) (hd : 0 < den) :
    Charter.mulDivRound x num den .floor = .ok (mdrFloor x num den) := by
  unfold Charter.mulDivRound mdrFloor
  have hne : (den == 0) = false := beq_false_of_ne (by omega)
  have hle : ¬(den ≤ 0) := by omega
  rw [if_neg (by simp [hne]), if_pos hd, if_neg hle]

theorem mdrCeil_matches_mulDivRound (x num den : Int) (hd : 0 < den) :
    Charter.mulDivRound x num den .ceil = .ok (mdrCeil x num den) := by
  unfold Charter.mulDivRound mdrCeil
  have hne : (den == 0) = false := beq_false_of_ne (by omega)
  have hle : ¬(den ≤ 0) := by omega
  rw [if_neg (by simp [hne]), if_pos hd, if_neg hle]

private theorem fdiv_nonneg_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ Int.fdiv a b := by
  cases a with
  | negSucc _ => omega
  | ofNat m =>
    cases b with
    | negSucc _ => omega
    | ofNat n =>
      cases m with
      | zero => exact Int.le_refl 0
      | succ m' => exact Int.ofNat_le.mpr (Nat.zero_le _)

private theorem fmod_bounds_of_pos (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ Int.fmod a b ∧ Int.fmod a b < b ∧ b * Int.fdiv a b + Int.fmod a b = a := by
  cases a with
  | negSucc _ => omega
  | ofNat m =>
    cases b with
    | negSucc _ => omega
    | ofNat n =>
      have hn : 0 < n := Int.ofNat_lt.mp hb
      cases m with
      | zero =>
        refine ⟨Int.le_refl 0, hb, ?_⟩
        change (n : Int) * 0 + 0 = 0
        omega
      | succ m' =>
        have hmod : (m' + 1) % n < n := Nat.mod_lt (m' + 1) hn
        have hdiv : n * ((m' + 1) / n) + (m' + 1) % n = m' + 1 := Nat.div_add_mod (m' + 1) n
        show 0 ≤ (((m' + 1) % n : Nat) : Int) ∧
             (((m' + 1) % n : Nat) : Int) < (n : Int) ∧
             (n : Int) * (((m' + 1) / n : Nat) : Int) + (((m' + 1) % n : Nat) : Int) = ((m' + 1 : Nat) : Int)
        exact ⟨Int.ofNat_le.mpr (Nat.zero_le _), Int.ofNat_lt.mpr hmod, by exact_mod_cast hdiv⟩

private theorem fdiv_neg_le_zero (a b : Int) (ha : a < 0) (hb : 0 < b) :
    Int.fdiv a b ≤ 0 := by
  cases a with
  | ofNat m =>
    have : (0 : Int) ≤ Int.ofNat m := Int.ofNat_le.mpr (Nat.zero_le m)
    omega
  | negSucc m =>
    cases b with
    | negSucc _ => omega
    | ofNat n =>
      cases n with
      | zero => cases Int.lt_irrefl 0 hb
      | succ k =>
        show Int.negSucc (m / (k + 1)) ≤ 0
        exact Int.le_of_lt (Int.negSucc_lt_zero _)

theorem mdrFloor_nonneg {x num den : Int} (hx : 0 ≤ x) (hn : 0 ≤ num) (hd : 0 < den) :
    0 ≤ mdrFloor x num den := by
  unfold mdrFloor
  rw [if_neg (by omega)]
  exact fdiv_nonneg_of_nonneg (x * num) den (Int.mul_nonneg hx hn) hd

theorem mdrCeil_nonneg {x num den : Int} (hx : 0 ≤ x) (hn : 0 ≤ num) (hd : 0 < den) :
    0 ≤ mdrCeil x num den := by
  unfold mdrCeil
  rw [if_neg (by omega)]
  have hq := fdiv_nonneg_of_nonneg (x * num) den (Int.mul_nonneg hx hn) hd
  dsimp only
  split <;> omega

/-- **Atomic Zero-Crossing Split Bound (`#75`):**
Whenever `0 < bal`, `0 < bps`, `0 < scale`, and `mdrFloor va bps scale > bal`,
the ceiling retirement base `mdrCeil bal scale bps` satisfies `0 ≤ mdrCeil bal scale bps ≤ va`,
so the unretired residual `va - mdrCeil bal scale bps` lies in `[0, va]` for all integers. -/
theorem mdrCeil_split_bounds {va bps bal scale : Int}
    (hbal : 0 < bal) (hbps : 0 < bps) (hscale : 0 < scale)
    (hgt : bal < mdrFloor va bps scale) :
    0 ≤ va - mdrCeil bal scale bps ∧ va - mdrCeil bal scale bps ≤ va := by
  unfold mdrFloor at hgt
  rw [if_neg (by omega)] at hgt
  have hvabps_nn : 0 ≤ va * bps := by
    by_cases hneg : va * bps < 0
    · have hle0 := fdiv_neg_le_zero (va * bps) scale hneg hscale
      omega
    · omega
  have ⟨hr1_nn, hr1_lt, hdiv1⟩ := fmod_bounds_of_pos (va * bps) scale hvabps_nn hscale
  have h_prod_gt : bal * scale < va * bps := by
    have hge1 : bal + 1 ≤ Int.fdiv (va * bps) scale := by omega
    have hmul : scale * (bal + 1) ≤ scale * Int.fdiv (va * bps) scale :=
      Int.mul_le_mul_of_nonneg_left hge1 (by omega)
    have hlin : scale * (bal + 1) = bal * scale + scale := by
      rw [Int.mul_add, Int.mul_one, Int.mul_comm scale bal]
    omega
  unfold mdrCeil
  rw [if_neg (by omega)]
  dsimp only
  have hbalscale_nn : 0 ≤ bal * scale := Int.mul_nonneg (by omega) (by omega)
  have hq2_nn : 0 ≤ Int.fdiv (bal * scale) bps := fdiv_nonneg_of_nonneg (bal * scale) bps hbalscale_nn hbps
  have ⟨hr2_nn, hr2_lt, hdiv2⟩ := fmod_bounds_of_pos (bal * scale) bps hbalscale_nn hbps
  by_cases hr0 : (Int.fmod (bal * scale) bps == 0) = true
  · rw [if_pos hr0]
    have hr_eq : Int.fmod (bal * scale) bps = 0 := beq_iff_eq.mp hr0
    have h_q_lt : Int.fdiv (bal * scale) bps < va := by
      by_cases hcontra : va ≤ Int.fdiv (bal * scale) bps
      · have hm : va * bps ≤ Int.fdiv (bal * scale) bps * bps :=
          Int.mul_le_mul_of_nonneg_right hcontra (by omega)
        rw [Int.mul_comm (Int.fdiv (bal * scale) bps) bps] at hm
        omega
      · omega
    omega
  · rw [if_neg hr0]
    have hr_ne : Int.fmod (bal * scale) bps ≠ 0 := by
      intro h; exact hr0 (beq_iff_eq.mpr h)
    have h_q1_le : Int.fdiv (bal * scale) bps + 1 ≤ va := by
      by_cases hcontra : va ≤ Int.fdiv (bal * scale) bps
      · have hm : va * bps ≤ Int.fdiv (bal * scale) bps * bps :=
          Int.mul_le_mul_of_nonneg_right hcontra (by omega)
        rw [Int.mul_comm (Int.fdiv (bal * scale) bps) bps] at hm
        omega
      · omega
    omega

theorem mdrCeil_split_bounds_ge {va bps bal scale : Int}
    (hbal : bal > 0) (hbps : bps > 0) (hscale : scale > 0)
    (hgt : mdrFloor va bps scale > bal) :
    (va - mdrCeil bal scale bps ≥ 0) ∧ (va - mdrCeil bal scale bps ≤ va) :=
  mdrCeil_split_bounds hbal hbps hscale hgt

end Charter.Verify.ArithLemmas
