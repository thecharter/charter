import SPL.Core.Semantics
import SPL.Substrate.Settlement

/-!
# Charter.Modules.OracleFeed — Reusable Contestable Valuation Feed & Atomic Waterfall Module

Extracts and generalizes Substrate 3 contestable economic/risk valuation feeds
(`ContestableValuation`, `settledValuationAt`, `contestValuation`,
`applyLaw6Ruling`) and the atomic point-of-settlement waterfall
(`AtomicWaterfallDistribution`, `executeAtomicSettlement`) with kernel-checked
contestation safety and gross-inflow conservation theorems.
-/

namespace Charter.Modules

open SPL SPL.Substrate

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for a contestable valuation feed and atomic settlement waterfall. -/
structure OracleFeedConfig where
  contestWindow : Time := 5
  levyCapBps    : Nat  := 100
  retirementBps : Nat  := 2000
  royaltyBps    : Nat  := 500
  deriving DecidableEq, Repr, Inhabited

export SPL.Substrate (
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

/-- Execute a configured atomic point-of-settlement waterfall over `grossInflow`. -/
def executeConfiguredWaterfall (cfg : OracleFeedConfig)
    (grossInflow qualifiedExpense remainingLedger : Nat)
    (royaltyBoughtOut : Bool) : AtomicWaterfallDistribution :=
  executeAtomicSettlement
    grossInflow qualifiedExpense cfg.levyCapBps cfg.retirementBps cfg.royaltyBps
    remainingLedger royaltyBoughtOut

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a qualified-expenditure benchmark bounds duty over any signature `σ`. -/
def mkDutyQualifiedExpenditureBounds {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (boundFact : σ.Fact) (aboveBenchmarkAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act aboveBenchmarkAct) }

/-- Build a valuation-evidence submission power over any signature `σ`. -/
def mkPowerSubmitValuationEvidence {σ : Sig} (id : String) (sp : Span)
    (holder : Who σ) (triggerAct : σ.Act)
    (boundFact evidenceSubmittedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := holder
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [evidenceSubmittedFact] }

/-- Build an automatic point-of-settlement enforcement power over any signature `σ`. -/
def mkPowerEnforceAtomicSettlement {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact settlementEnforcedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [settlementEnforcedFact] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- `settledValuationAt` resolves to `some r` whenever an authoritative panel
ruling `some r` is present, and when `law6RulingAmount = none` it resolves to
`some v.proposedAmount` iff `v.contested = false` and `now ≥ v.proposedAt + contestWindow`. -/
theorem oracle_feed_valuation_settled_by_ruling_or_window
    (contestWindow now : Nat) (v : ContestableValuation) :
    (∀ r, v.law6RulingAmount = some r →
      settledValuationAt contestWindow now v = some r) ∧
    (v.law6RulingAmount = none → v.contested = false →
      now ≥ v.proposedAt + contestWindow →
      settledValuationAt contestWindow now v = some v.proposedAmount) ∧
    (v.law6RulingAmount = none →
      (v.contested = true ∨ now < v.proposedAt + contestWindow) →
      settledValuationAt contestWindow now v = none) :=
  valuation_settled_by_ruling_or_uncontested_window contestWindow now v

/-- Contesting an unruled valuation blocks automatic settlement until an
authoritative panel ruling is issued, and applying a ruling `r` settles the
valuation to `some r`. -/
theorem oracle_feed_contest_blocks_auto_settlement
    (contestWindow now r : Nat) (v : ContestableValuation) :
    (v.law6RulingAmount = none →
      settledValuationAt contestWindow now (contestValuation v) = none) ∧
    settledValuationAt contestWindow now (applyLaw6Ruling v r) = some r :=
  contest_and_ruling_semantics contestWindow now r v

/-- For all inputs, the five components of `executeAtomicSettlement` sum to
`grossInflow` with zero value lost or created at settlement. -/
theorem oracle_feed_atomic_settlement_conserves_gross_inflow
    (g e lCap retBps royBps rem : Nat) (bought : Bool) :
    let d := executeAtomicSettlement g e lCap retBps royBps rem bought
    d.qualifiedExpenseReimbursed + d.feePoolLevy + d.retirementCollected +
      d.royaltyCollected + d.agentRetainedSurplus = g :=
  atomic_settlement_conserves_gross_inflow g e lCap retBps royBps rem bought

/-- Retirement collected in an atomic settlement never exceeds `remainingLedger`,
and a bought-out member pays zero royalty. -/
theorem oracle_feed_atomic_settlement_bounds
    (g e lCap retBps royBps rem : Nat) (bought : Bool) :
    (executeAtomicSettlement g e lCap retBps royBps rem bought).retirementCollected ≤ rem ∧
    (executeAtomicSettlement g e lCap retBps royBps rem true).royaltyCollected = 0 :=
  ⟨atomic_settlement_retirement_never_exceeds_ledger g e lCap retBps royBps rem bought,
   atomic_settlement_bought_out_zero_royalty g e lCap retBps royBps rem⟩

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `settledValuationAt` across pending,
uncontested, contested, and panel-ruled feeds, plus `executeConfiguredWaterfall`. -/
def oracleFeedSelfTest : Bool :=
  let cfg : OracleFeedConfig := {}
  let v0 : ContestableValuation := ⟨1, 500, 2, false, none⟩
  let vContested := contestValuation v0
  let vRuled := applyLaw6Ruling vContested 420
  let dist := executeConfiguredWaterfall cfg 1200 200 150 false
  (settledValuationAt 5 4 v0 == none) &&
  (settledValuationAt 5 8 v0 == some 500) &&
  (settledValuationAt 5 8 vContested == none) &&
  (settledValuationAt 5 8 vRuled == some 420) &&
  (dist.qualifiedExpenseReimbursed == 200) &&
  (dist.feePoolLevy == 10) &&
  (dist.retirementCollected == 150) &&
  (dist.royaltyCollected == 42) &&
  (dist.agentRetainedSurplus == 798) &&
  (dist.qualifiedExpenseReimbursed + dist.feePoolLevy + dist.retirementCollected +
    dist.royaltyCollected + dist.agentRetainedSurplus == 1200)

theorem oracleFeedSelfTest_passes : oracleFeedSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  OracleFeedConfig
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
  executeConfiguredWaterfall
  mkDutyQualifiedExpenditureBounds
  mkPowerSubmitValuationEvidence
  mkPowerEnforceAtomicSettlement
  oracle_feed_valuation_settled_by_ruling_or_window
  oracle_feed_contest_blocks_auto_settlement
  oracle_feed_atomic_settlement_conserves_gross_inflow
  oracle_feed_atomic_settlement_bounds
  oracleFeedSelfTest
  oracleFeedSelfTest_passes
)
end Charter

