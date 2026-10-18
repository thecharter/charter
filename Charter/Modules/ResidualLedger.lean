import SPL.Core.Semantics
import SPL.Law1.Ledger
import SPL.Law4.Lineage
import SPL.Law3.Theorems

/-!
# Charter.Modules.ResidualLedger — Reusable Residual-Claim & Treasury Ledger Module

Extracts and generalizes the Law 1 & Law 4 residual-claim ledger, cost-basis
accounting, loss-credit carryforward, 1-for-1 loan principal repayment,
absolute calendar sunset, atomic retirement-to-royalty split, and historical
buyout floor into a reusable institutional module over any signature `σ : Sig`.
-/

namespace Charter.Modules

open SPL SPL.Law3

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for a residual-claim or founding treasury ledger. -/
structure ResidualLedgerConfig where
  foundingObligation : Nat := 1000
  retirementRatePct  : Nat := 20
  royaltyRatePct     : Nat := 5
  sunset             : Time := 1000
  buyoutMultiple     : Nat := 10
  minBuyoutFloor     : Nat := 250
  commonsSharePct    : Nat := 20
  deriving DecidableEq, Repr, Inhabited

export SPL.Law3 (
  SettlementResult
  settleInflow
  settleSequence
  RecogMode
  qualifiedExpenditure
  recognizeExpenditure
  transferCarryover
  settleCapitalSaleWithLossCredit
  LoanLedger
  repayLoanPrincipal
  LineageLedgerState
  ledgerBalance
  inRetirementPhase
  LineageInternalOp
  applyInternalOp
  applyClaimantForfeiture
  buyoutPrice
  InflowSample
  sumSampleInflows
  computeBuyoutFloor
)

/-- Settle a net value-added inflow `v` using a `ResidualLedgerConfig`. -/
def settleConfiguredInflow (cfg : ResidualLedgerConfig) (currentBalance : Nat)
    (boughtOut : Bool) (v : Nat) : SettlementResult :=
  settleInflow currentBalance cfg.retirementRatePct cfg.royaltyRatePct boughtOut v

/-- Compute the buyout price under a `ResidualLedgerConfig`. -/
def configuredBuyoutPrice (cfg : ResidualLedgerConfig) (trailingVA annualizedVA : Nat) : Nat :=
  buyoutPrice cfg.buyoutMultiple trailingVA annualizedVA cfg.minBuyoutFloor

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a ledger-immutability prohibition duty over any signature `σ`. -/
def mkDutyLedgerImmutable {σ : Sig} (id : String) (sp : Span)
    (boundFact : σ.Fact) (forbiddenAct : σ.Act) (beneficiaries : List σ.Actor) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act forbiddenAct) }

/-- Build a single-recognition expenditure duty over any signature `σ`. -/
def mkDutySingleRecognition {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (boundFact : σ.Fact) (doubleRecogAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act doubleRecogAct) }

/-- Build a retirement-settlement power over any signature `σ`. -/
def mkPowerSettleRetirement {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact balancePosFact sunsetFact settledFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact)
                  (.and (.holds balancePosFact) (.not (.holds sunsetFact)))
    adds := [settledFact] }

/-- Build a calendar-sunset ledger-extinguishment power over any signature `σ`. -/
def mkPowerExtinguishAtSunset {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact sunsetFact extinguishedFact balancePosFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.holds sunsetFact)
    adds := [extinguishedFact]
    removes := [balancePosFact] }

/-- Build a permanent royalty-buyout power over any signature `σ`. -/
def mkPowerExecuteBuyout {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact boughtOutFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.not (.holds boughtOutFact))
    adds := [boughtOutFact] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- Single-step atomic settlement conservation and phase-ordering guarantees:
- `toRetirement ≤ L` and `newLedger + toRetirement = L` (never negative, never over-collects),
- `0 < newLedger → toRoyalty = 0` (no royalty while ledger balance remains positive),
- `newLedger = 0 → toRetirement = L` (crossing zero pays exact remaining balance first). -/
theorem residual_ledger_settleInflow_conservation (L r_ret r_roy : Nat) (b : Bool) (v : Nat) :
    (settleInflow L r_ret r_roy b v).toRetirement ≤ L ∧
    (settleInflow L r_ret r_roy b v).newLedger + (settleInflow L r_ret r_roy b v).toRetirement = L ∧
    (0 < (settleInflow L r_ret r_roy b v).newLedger →
      (settleInflow L r_ret r_roy b v).toRoyalty = 0) ∧
    ((settleInflow L r_ret r_roy b v).newLedger = 0 →
      (settleInflow L r_ret r_roy b v).toRetirement = L) :=
  settleInflow_conservation L r_ret r_roy b v

/-- Multi-step sequential settlement conservation across any list of member inflows. -/
theorem residual_ledger_settleSequence_conservation (L r_ret r_roy : Nat) (xs : List (Bool × Nat)) :
    (settleSequence L r_ret r_roy xs).2.1 ≤ L ∧
    (settleSequence L r_ret r_roy xs).1 + (settleSequence L r_ret r_roy xs).2.1 = L :=
  settleSequence_conservation L r_ret r_roy xs

/-- 1-for-1 arm's-length loan principal repayment conservation and cap:
exempt principal repayment never exceeds remaining unpaid principal
`L.principalReceived - L.principalRepaid`, and exempt principal plus excess
interest/fee equals the full `payment`. -/
theorem residual_ledger_loan_repayment_exact (L : LoanLedger) (payment : Nat) :
    let (L', exempt, excess) := repayLoanPrincipal L payment
    exempt ≤ L.principalReceived - L.principalRepaid ∧
    exempt + excess = payment ∧
    L'.principalRepaid = L.principalRepaid + exempt ∧
    L'.principalReceived = L.principalReceived := by
  dsimp [repayLoanPrincipal]
  have hMin : min payment (L.principalReceived - L.principalRepaid) ≤ payment :=
    Nat.min_le_left _ _
  refine ⟨Nat.min_le_right _ _, by omega, rfl, rfl⟩

/-- Buyout finality and retirement invariance: a bought-out member pays zero
royalty (`toRoyalty = 0`) while paying the exact same retirement contribution
as a non-bought-out member, and `buyoutPrice` is bounded below by `minFloor`,
`mult * trailingVA`, and `mult * annualizedVA`. -/
theorem residual_ledger_buyout_finality
    (L r_ret r_roy v mult trailingVA annualizedVA minFloor : Nat) :
    (settleInflow L r_ret r_roy true v).toRoyalty = 0 ∧
    (settleInflow L r_ret r_roy true v).toRetirement =
      (settleInflow L r_ret r_roy false v).toRetirement ∧
    (settleInflow L r_ret r_roy true v).newLedger =
      (settleInflow L r_ret r_roy false v).newLedger ∧
    minFloor ≤ buyoutPrice mult trailingVA annualizedVA minFloor ∧
    mult * trailingVA ≤ buyoutPrice mult trailingVA annualizedVA minFloor ∧
    mult * annualizedVA ≤ buyoutPrice mult trailingVA annualizedVA minFloor := by
  refine ⟨by simp [settleInflow], rfl, rfl, ?_⟩
  unfold buyoutPrice
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- Calendar sunset extinguishes any remaining founding ledger balance (`ledgerBalance st = 0`). -/
theorem residual_ledger_sunset_extinguishes (st : LineageLedgerState)
    (hSun : st.sunset ≤ st.now) :
    ledgerBalance st = 0 := by
  unfold ledgerBalance
  have hd : decide (st.sunset ≤ st.now) = true := decide_eq_true hSun
  simp [hd]

/-- Single recognition of qualified expenditures: every expenditure is classified
once as either capitalized basis or expensed deduction, never both, and never
exceeds the arm's-length benchmark. -/
theorem residual_ledger_single_recognition (mode : RecogMode) (paid benchmark : Nat) :
    let (bOut, expOut) := recognizeExpenditure mode paid benchmark
    bOut + expOut = qualifiedExpenditure paid benchmark ∧
    qualifiedExpenditure paid benchmark ≤ benchmark ∧
    (bOut = 0 ∨ expOut = 0) := by
  cases mode <;> simp [recognizeExpenditure, qualifiedExpenditure, Nat.min_def] <;> split <;> omega

/-- Historical buyout-floor anti-evasion (`LAW4.BUYOUT`): shifting or diverting
`delta ≤ s.amount` (at weight `s.weightBps ≤ 10000`) to related parties within
the lookback window never decreases `computeBuyoutFloor` or `buyoutPrice`. -/
theorem residual_ledger_buyout_floor_anti_evasion
    (B : LineageLedgerState) (s : InflowSample) (rest : List InflowSample)
    (netResources delta mult trailingVA minFloor : Nat)
    (hDelta : delta ≤ s.amount) (hWeight : s.weightBps ≤ 10000) :
    let sDiverted : InflowSample :=
      { s with amount := s.amount - delta
               shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta }
    computeBuyoutFloor B (s :: rest) netResources ≤
      computeBuyoutFloor B (sDiverted :: rest) netResources ∧
    buyoutPrice mult trailingVA (computeBuyoutFloor B (s :: rest) netResources) minFloor ≤
      buyoutPrice mult trailingVA (computeBuyoutFloor B (sDiverted :: rest) netResources) minFloor :=
  diverted_related_inflows_never_decrease_buyout_floor
    B s rest netResources delta mult trailingVA minFloor hDelta hWeight

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `settleConfiguredInflow`, atomic split across
zero, `recognizeExpenditure`, `repayLoanPrincipal`, and `computeBuyoutFloor`. -/
def residualLedgerSelfTest : Bool :=
  let cfg : ResidualLedgerConfig := {}
  let s1 := settleConfiguredInflow cfg 80 false 500
  let (bCap, eCap) := recognizeExpenditure .capitalized 250 200
  let (loan', exempt, excess) := repayLoanPrincipal ⟨500, 100⟩ 450
  let st : LineageLedgerState := ⟨1000, 200, 0, 2, 10, 1000⟩
  let samples : List InflowSample := [⟨100, 5000, 20⟩]
  let floor := computeBuyoutFloor st samples 180
  (s1.newLedger == 0) &&
  (s1.toRetirement == 80) &&
  (s1.toRoyalty == 5) &&
  (bCap == 200 && eCap == 0) &&
  (exempt == 400 && excess == 50 && loan'.principalRepaid == 500) &&
  (ledgerBalance st == 800) &&
  (floor == 250)

theorem residualLedgerSelfTest_passes : residualLedgerSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  ResidualLedgerConfig
  SettlementResult
  settleInflow
  settleSequence
  RecogMode
  qualifiedExpenditure
  recognizeExpenditure
  transferCarryover
  settleCapitalSaleWithLossCredit
  LoanLedger
  repayLoanPrincipal
  LineageLedgerState
  ledgerBalance
  inRetirementPhase
  LineageInternalOp
  applyInternalOp
  applyClaimantForfeiture
  buyoutPrice
  InflowSample
  sumSampleInflows
  computeBuyoutFloor
  settleConfiguredInflow
  configuredBuyoutPrice
  mkDutyLedgerImmutable
  mkDutySingleRecognition
  mkPowerSettleRetirement
  mkPowerExtinguishAtSunset
  mkPowerExecuteBuyout
  residual_ledger_settleInflow_conservation
  residual_ledger_settleSequence_conservation
  residual_ledger_loan_repayment_exact
  residual_ledger_buyout_finality
  residual_ledger_sunset_extinguishes
  residual_ledger_single_recognition
  residual_ledger_buyout_floor_anti_evasion
  residualLedgerSelfTest
  residualLedgerSelfTest_passes
)
end Charter

