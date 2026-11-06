/-!
# Charter.Core.Scale — Exact Minor-Unit `Money`/`Quantity` Scaling & Rounding (`D24`, `G3.4`)

Defines Charter's explicit rounding modes (`Floor`, `Ceil`, `NearestEven`, `ExactOrReject`)
and exact arbitrary-precision integer `mulDivRound` (`(x * num) / den` without intermediate
overflow, binary floating point, or unreduced rational heap wrappers in `Core.State`,
`docs/rfc.md` §6.3, `T10`, `T11`).
-/

namespace Charter

/-- Explicit rounding policy for scaled integer division (`010.12`, `D24`). -/
inductive RoundingMode where
  | floor
  | ceil
  | nearestEven
  | exactOrReject
  deriving Repr, DecidableEq, Inhabited

def RoundingMode.beq : RoundingMode → RoundingMode → Bool
  | .floor, .floor => true
  | .ceil, .ceil => true
  | .nearestEven, .nearestEven => true
  | .exactOrReject, .exactOrReject => true
  | _, _ => false

instance : BEq RoundingMode := ⟨RoundingMode.beq⟩

def RoundingMode.kwName : RoundingMode → String
  | .floor         => "Floor"
  | .ceil          => "Ceil"
  | .nearestEven   => "NearestEven"
  | .exactOrReject => "ExactOrReject"

/-- Compute `(x * num) / den` in exact `Int` arithmetic and round according to `mode` (`010.12`). -/
def mulDivRound (x num den : Int) (mode : RoundingMode) : Except String Int :=
  if den == 0 then
    .error "MulDivRound: division by zero"
  else
    let (p, d) := if 0 < den then (x * num, den) else (-(x * num), -den)
    let q := Int.fdiv p d
    let r := Int.fmod p d
    match mode with
    | .floor => .ok q
    | .ceil => .ok (if r == 0 then q else q + 1)
    | .exactOrReject =>
      if r == 0 then .ok q
      else .error s!"MulDivRound: inexact rational {p}/{d} rejected under ExactOrReject"
    | .nearestEven =>
      let twoR := 2 * r
      if twoR < d then .ok q
      else if d < twoR then .ok (q + 1)
      else
        if Int.fmod q 2 == 0 then .ok q else .ok (q + 1)

/-- `T10` (`docs/rfc.md` §6.3, §14): `allowance=20`, `used=0`, `purchase=300`, `feeA=2%`, `feeB=5%`
yields exact `40 + 1400 = 1440` minor units (`$14.40` at scale 2), rounds to `14` (`Floor`) and
`15` (`Ceil`) at scale 0, and rejects inexact `144 / 10` under `ExactOrReject`. -/
theorem mulDivRound_t10_tiered_allowance :
    (do
      let tierA ← mulDivRound (20 * 100) 2 100 .exactOrReject
      let tierB ← mulDivRound (280 * 100) 5 100 .exactOrReject
      pure (tierA + tierB)) = .ok 1440 ∧
    mulDivRound 144 1 10 .floor = .ok 14 ∧
    mulDivRound 144 1 10 .ceil = .ok 15 ∧
    (mulDivRound 144 1 10 .exactOrReject).isOk = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Banker's `NearestEven` rounding resolves exact `.5` midpoints to even integers (`±14.5 -> ±14`, `±15.5 -> ±16`). -/
theorem mulDivRound_nearestEven_ties_even :
    mulDivRound 145 1 10 .nearestEven = .ok 14 ∧
    mulDivRound 155 1 10 .nearestEven = .ok 16 ∧
    mulDivRound (-145) 1 10 .nearestEven = .ok (-14) ∧
    mulDivRound (-155) 1 10 .nearestEven = .ok (-16) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `Floor` never exceeds `Ceil` for any inputs where `den ≠ 0`. -/
theorem mulDivRound_floor_le_ceil (x num den qf qc : Int)
    (hf : mulDivRound x num den .floor = .ok qf)
    (hc : mulDivRound x num den .ceil = .ok qc) :
    qf ≤ qc := by
  unfold mulDivRound at hf hc
  by_cases h0 : (den == 0) = true
  · rw [if_pos h0] at hf; cases hf
  · rw [if_neg h0] at hf hc
    dsimp only at hf hc
    injection hf with hqf
    injection hc with hqc
    rw [← hqf, ← hqc]
    split <;> omega

end Charter
