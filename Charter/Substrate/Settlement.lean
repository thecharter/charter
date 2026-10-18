import Charter.Core.Semantics

/-!
# Substrate Assumption 3 — Contestable Economic/Risk Oracles & Atomic Settlement Rails

Reference implementation and kernel-checked proofs for the third substrate
capability of the Protocol of Sovereign Agency:
- Contestable valuation feeds (`ContestableValuation`) that settle either by an
  authoritative Law 6 panel ruling (`law6RulingAmount = some r`) or once the
  challenge window (`contestWindow`) elapses without contest,
- Point-of-settlement atomic waterfall distribution (`executeAtomicSettlement`)
  reimbursing qualified expenses, deducting the capped shared-infrastructure fee
  levy, collecting founding-ledger retirement up to `remainingLedger`, collecting
  post-retirement royalty (unless bought out), and returning the retained surplus
  to the agent while conserving 100% of `grossInflow`.
-/

namespace Charter.Substrate

/-- A contestable economic or risk valuation feed entry. -/
structure ContestableValuation where
  feedId           : Nat
  proposedAmount   : Nat
  proposedAt       : Nat
  contested        : Bool
  law6RulingAmount : Option Nat
  deriving DecidableEq, Repr

abbrev ContestableValuationFeed := ContestableValuation

/-- Mark a contestable valuation as contested during the challenge window. -/
def contestValuation (v : ContestableValuation) : ContestableValuation :=
  { v with contested := true }

/-- Record an authoritative Law 6 panel ruling `rulingAmount` on valuation `v`. -/
def applyLaw6Ruling (v : ContestableValuation) (rulingAmount : Nat) :
    ContestableValuation :=
  { v with law6RulingAmount := some rulingAmount }

/-- Resolve a contestable valuation at timestamp `now` under `contestWindow`:
- If a Law 6 ruling has been issued (`some r`), that ruling governs (`some r`).
- Otherwise, if the valuation is uncontested (`!v.contested`) and the challenge
  window has elapsed (`now ≥ v.proposedAt + contestWindow`), it settles at
  `some v.proposedAmount`.
- Otherwise, the valuation remains unsettled (`none`). -/
def settledValuationAt (contestWindow now : Nat) (v : ContestableValuation) :
    Option Nat :=
  match v.law6RulingAmount with
  | some r => some r
  | none =>
    if !v.contested && now >= v.proposedAt + contestWindow then
      some v.proposedAmount
    else
      none

/-- Output of an atomic point-of-settlement waterfall distribution. -/
structure AtomicWaterfallDistribution where
  qualifiedExpenseReimbursed : Nat
  feePoolLevy                : Nat
  retirementCollected        : Nat
  royaltyCollected           : Nat
  agentRetainedSurplus       : Nat
  deriving DecidableEq, Repr

/-- Execute an atomic point-of-settlement waterfall over `grossInflow`:
1. Reimburses `expUsed := min grossInflow qualifiedExpense`,
2. From `netValueAdded := grossInflow - expUsed`, deducts
   `feeLevy := min netValueAdded ((netValueAdded * levyCapBps) / 10000)`,
3. From `distributable := netValueAdded - feeLevy`, collects
   `retPaid := min remainingLedger (min distributable ((distributable * retirementBps) / 10000))`,
4. From the post-retirement portion `distributable - retPaid`, collects
   `royPaid := if royaltyBoughtOut then 0 else min (distributable - retPaid) (((distributable - retPaid) * royaltyBps) / 10000)`,
5. Leaves `agentRetainedSurplus := distributable - retPaid - royPaid`. -/
def executeAtomicSettlement
    (grossInflow qualifiedExpense levyCapBps retirementBps royaltyBps remainingLedger : Nat)
    (royaltyBoughtOut : Bool) : AtomicWaterfallDistribution :=
  let expUsed := min grossInflow qualifiedExpense
  let netValueAdded := grossInflow - expUsed
  let feeLevy := min netValueAdded ((netValueAdded * levyCapBps) / 10000)
  let distributable := netValueAdded - feeLevy
  let retPaid := min remainingLedger (min distributable ((distributable * retirementBps) / 10000))
  let postRet := distributable - retPaid
  let royPaid :=
    if royaltyBoughtOut then 0
    else min postRet ((postRet * royaltyBps) / 10000)
  let surplus := distributable - retPaid - royPaid
  { qualifiedExpenseReimbursed := expUsed
    feePoolLevy                := feeLevy
    retirementCollected        := retPaid
    royaltyCollected           := royPaid
    agentRetainedSurplus       := surplus }

/-! ## Kernel-Checked Substrate Capability 3 Theorems -/

/-- `settledValuationAt` resolves to `some r` whenever a Law 6 ruling `some r`
is present, and when `law6RulingAmount = none` it resolves to `some v.proposedAmount`
if and only if `v.contested = false` and `now ≥ v.proposedAt + contestWindow`. -/
theorem valuation_settled_by_ruling_or_uncontested_window
    (contestWindow now : Nat) (v : ContestableValuation) :
    (∀ r, v.law6RulingAmount = some r →
      settledValuationAt contestWindow now v = some r) ∧
    (v.law6RulingAmount = none → v.contested = false →
      now ≥ v.proposedAt + contestWindow →
      settledValuationAt contestWindow now v = some v.proposedAmount) ∧
    (v.law6RulingAmount = none →
      (v.contested = true ∨ now < v.proposedAt + contestWindow) →
      settledValuationAt contestWindow now v = none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hRul
    simp [settledValuationAt, hRul]
  · intro hNone hUncont hWin
    simp [settledValuationAt, hNone, hUncont, hWin]
  · intro hNone hPending
    rcases hPending with hCont | hLt
    · simp [settledValuationAt, hNone, hCont]
    · have hNotGe : ¬ (now ≥ v.proposedAt + contestWindow) := by omega
      simp [settledValuationAt, hNone, hNotGe]

/-- Contesting an unruled valuation blocks automatic settlement until a Law 6
ruling is issued, and applying a Law 6 ruling `r` settles the valuation to `some r`. -/
theorem contest_and_ruling_semantics
    (contestWindow now r : Nat) (v : ContestableValuation) :
    (v.law6RulingAmount = none →
      settledValuationAt contestWindow now (contestValuation v) = none) ∧
    settledValuationAt contestWindow now (applyLaw6Ruling v r) = some r := by
  refine ⟨fun hNone => by simp [contestValuation, settledValuationAt, hNone], ?_⟩
  simp [applyLaw6Ruling, settledValuationAt]

/-- For all inputs, the five components of `executeAtomicSettlement` sum to
`grossInflow` with zero value lost or created at settlement. -/
theorem atomic_settlement_conserves_gross_inflow
    (g e lCap retBps royBps rem : Nat) (bought : Bool) :
    let d := executeAtomicSettlement g e lCap retBps royBps rem bought
    d.qualifiedExpenseReimbursed + d.feePoolLevy + d.retirementCollected +
      d.royaltyCollected + d.agentRetainedSurplus = g := by
  dsimp [executeAtomicSettlement]
  have hExp : min g e ≤ g := Nat.min_le_left g e
  have hFee : min (g - min g e) ((g - min g e) * lCap / 10000) ≤ g - min g e :=
    Nat.min_le_left _ _
  have hRet1 :
      min rem (min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
        ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000)) ≤
      min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
        ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000) :=
    Nat.min_le_right _ _
  have hRet2 :
      min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
        ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000) ≤
      g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000) :=
    Nat.min_le_left _ _
  cases bought
  · have hRoy :
        min
          (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000) -
            min rem (min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
              ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000)))
          ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000) -
            min rem (min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
              ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000))) *
            royBps / 10000) ≤
        g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000) -
          min rem (min (g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000))
            ((g - min g e - min (g - min g e) ((g - min g e) * lCap / 10000)) * retBps / 10000)) :=
      Nat.min_le_left _ _
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [↓reduceIte]
    omega

/-- Retirement collected in an atomic settlement never exceeds `remainingLedger`. -/
theorem atomic_settlement_retirement_never_exceeds_ledger
    (g e lCap retBps royBps rem : Nat) (bought : Bool) :
    (executeAtomicSettlement g e lCap retBps royBps rem bought).retirementCollected ≤ rem := by
  dsimp [executeAtomicSettlement]
  exact Nat.min_le_left rem _

/-- When the founding ledger has already been retired (`rem = 0`), zero
retirement is collected in every atomic settlement. -/
theorem atomic_settlement_zero_ledger_zero_retirement
    (g e lCap retBps royBps : Nat) (bought : Bool) :
    (executeAtomicSettlement g e lCap retBps royBps 0 bought).retirementCollected = 0 := by
  have h := atomic_settlement_retirement_never_exceeds_ledger g e lCap retBps royBps 0 bought
  omega

/-- The shared-infrastructure fee levy never exceeds the basis-point cap
`((g - expUsed) * lCap) / 10000` or net value added `g - expUsed`. -/
theorem atomic_settlement_levy_capped
    (g e lCap retBps royBps rem : Nat) (bought : Bool) :
    let d := executeAtomicSettlement g e lCap retBps royBps rem bought
    let netValueAdded := g - d.qualifiedExpenseReimbursed
    d.feePoolLevy ≤ (netValueAdded * lCap) / 10000 ∧
    d.feePoolLevy ≤ netValueAdded := by
  dsimp [executeAtomicSettlement]
  exact ⟨Nat.min_le_right _ _, Nat.min_le_left _ _⟩

/-- An agent that has bought out its royalty under Law 4 (`royaltyBoughtOut = true`)
pays zero royalty in every atomic settlement. -/
theorem atomic_settlement_bought_out_zero_royalty
    (g e lCap retBps royBps rem : Nat) :
    (executeAtomicSettlement g e lCap retBps royBps rem true).royaltyCollected = 0 := by
  rfl

/-- For any basis-point rate `bps ≤ 10000`, `(x * bps) / 10000 ≤ x`, so the
`min x ((x * bps) / 10000)` guard in `executeAtomicSettlement` is an exact
no-op on in-range basis-point parameters while preventing overflow when
out-of-range rates `bps > 10000` are supplied. -/
theorem atomic_settlement_bps_cap_noop (x bps : Nat) (hBps : bps ≤ 10000) :
    min x ((x * bps) / 10000) = (x * bps) / 10000 := by
  have hMul : x * bps ≤ x * 10000 := Nat.mul_le_mul_left x hBps
  have hDiv : (x * bps) / 10000 ≤ x :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000 x]; exact hMul)
  exact Nat.min_eq_right hDiv

/-- For all valid basis-point parameters (`retBps ≤ 10000` and `royBps ≤ 10000`),
`executeAtomicSettlement`'s `retirementCollected` and `royaltyCollected` equal
the exact uncapped basis-point formulas `min rem ((distributable * retBps) / 10000)`
and `if bought then 0 else ((distributable - retPaid) * royBps) / 10000`. -/
theorem atomic_settlement_exact_bps_formulas
    (g e lCap retBps royBps rem : Nat) (bought : Bool)
    (hRetBps : retBps ≤ 10000) (hRoyBps : royBps ≤ 10000) :
    let d := executeAtomicSettlement g e lCap retBps royBps rem bought
    let expUsed := min g e
    let netValueAdded := g - expUsed
    let feeLevy := min netValueAdded ((netValueAdded * lCap) / 10000)
    let distributable := netValueAdded - feeLevy
    let retPaid := min rem ((distributable * retBps) / 10000)
    d.retirementCollected = retPaid ∧
    d.royaltyCollected = (if bought then 0 else ((distributable - retPaid) * royBps) / 10000) := by
  dsimp [executeAtomicSettlement]
  rw [atomic_settlement_bps_cap_noop _ retBps hRetBps]
  rw [atomic_settlement_bps_cap_noop _ royBps hRoyBps]
  exact ⟨rfl, rfl⟩

end Charter.Substrate

namespace Charter

export Substrate (
  ContestableValuation
  ContestableValuationFeed
  contestValuation
  applyLaw6Ruling
  settledValuationAt
  AtomicWaterfallDistribution
  executeAtomicSettlement
  valuation_settled_by_ruling_or_uncontested_window
  contest_and_ruling_semantics
  atomic_settlement_conserves_gross_inflow
  atomic_settlement_retirement_never_exceeds_ledger
  atomic_settlement_zero_ledger_zero_retirement
  atomic_settlement_levy_capped
  atomic_settlement_bought_out_zero_royalty
  atomic_settlement_bps_cap_noop
  atomic_settlement_exact_bps_formulas
)

end Charter
