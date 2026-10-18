import Charter.Core.Semantics

/-!
# Charter.Modules.ResidualLedger — Reusable Residual-Claim & Treasury Ledger Module

Provides the law-agnostic residual-claim ledger, cost-basis accounting,
loss-credit carryforward, 1-for-1 loan principal repayment, absolute calendar
sunset, atomic retirement-to-royalty split, and historical buyout floor over
any signature `σ : Sig`.
-/

namespace Charter.Modules

open Charter

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

/-- Result of settling a net value-added inflow against a remaining founding
ledger balance `L` under retirement fraction `r_ret` and royalty fraction `r_roy`
(expressed in percentage points / basis-point scale). -/
structure SettlementResult where
  newLedger    : Nat
  toRetirement : Nat
  toRoyalty    : Nat
  deriving DecidableEq, Repr

/-- Atomic settlement of a net value-added inflow `v`:
* The tentative retirement obligation is `retireAttempt = (v * r_ret) / 100`.
* `toRetirement = min L retireAttempt`, so `toRetirement ≤ L` and `newLedger = L - toRetirement`.
* When `retireAttempt ≤ L`, the entire inflow is absorbed in the retirement phase (`toRoyalty = 0`).
* When `L < retireAttempt` (atomic split or post-retirement `L = 0`), the excess
  retirement-scaled capacity `retireAttempt - L` settles under the royalty rate
  if `!boughtOut`, and `0` if `boughtOut`. -/
def settleInflow (L r_ret r_roy : Nat) (boughtOut : Bool) (v : Nat) : SettlementResult :=
  let retireAttempt := (v * r_ret) / 100
  let toRet := min L retireAttempt
  let newL := L - toRet
  let excessRet := retireAttempt - toRet
  let toRoy :=
    if boughtOut then 0
    else if L = 0 then (v * r_roy) / 100
    else (excessRet * r_roy) / (max r_ret 1)
  { newLedger := newL, toRetirement := toRet, toRoyalty := toRoy }

/-- Sequential atomic settlement across a list of member inflows `(boughtOut, v)`. -/
def settleSequence (L r_ret r_roy : Nat) : List (Bool × Nat) → Nat × Nat × Nat
  | [] => (L, 0, 0)
  | (b, v) :: rest =>
    let s1 := settleInflow L r_ret r_roy b v
    let (finalL, restRet, restRoy) := settleSequence s1.newLedger r_ret r_roy rest
    (finalL, s1.toRetirement + restRet, s1.toRoyalty + restRoy)

/-- Irrevocable single recognition mode for a qualified expenditure. -/
inductive RecogMode
  | capitalized
  | expensed
  deriving DecidableEq, Repr

/-- Qualified amount of an outbound expenditure `paid` capped by its applicable
arm's-length benchmark `benchmark`. -/
def qualifiedExpenditure (paid benchmark : Nat) : Nat :=
  min paid benchmark

/-- Single recognition: classifies the qualified expenditure once, irrevocably,
as either `(basisAdded, 0)` or `(0, expenseAdded)`. -/
def recognizeExpenditure (mode : RecogMode) (paid benchmark : Nat) : Nat × Nat :=
  let q := qualifiedExpenditure paid benchmark
  match mode with
  | .capitalized => (q, 0)
  | .expensed    => (0, q)

/-- Intra-group asset transfer with carryover basis: transfers `b_asset ≤ b_sender`
of qualified basis from sender to recipient and ignores any internal transfer
price `_internalPrice`, leaving aggregate basis and loss credits unchanged. -/
def transferCarryover (b_sender b_recipient credits_sender credits_recipient b_asset _internalPrice : Nat) :
    Nat × Nat × Nat × Nat :=
  let carried := min b_sender b_asset
  (b_sender - carried, b_recipient + carried, credits_sender, credits_recipient)

/-- External sale of a capitalized asset at `salePrice` with verified cost basis
`basis` and carried-forward `lossCredit`: inflows up to `basis` are exempt return
of capital, the positive delta `salePrice - basis` is offset by `lossCredit`, and
the remaining net value added is returned together with the unused loss credit. -/
def settleCapitalSaleWithLossCredit (salePrice basis lossCredit : Nat) : Nat × Nat :=
  let grossGain := salePrice - basis
  let usedCredit := min grossGain lossCredit
  (grossGain - usedCredit, lossCredit - usedCredit)

/-- Registered arm's-length loan principal ledger: inbound principal from
registered arm's-length loans is exempt upon receipt provided repayment is
tracked one-for-one against `principalReceived`. -/
structure LoanLedger where
  principalReceived : Nat
  principalRepaid   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- One-for-one loan principal repayment tracking: returns
`(updatedLoan, excludedPrincipalRepayment, excessInterestOrFee)`. -/
def repayLoanPrincipal (L : LoanLedger) (payment : Nat) : LoanLedger × Nat × Nat :=
  let excludedPrincipalRepayment := min payment (L.principalReceived - L.principalRepaid)
  let excessInterestOrFee := payment - excludedPrincipalRepayment
  let updatedLoan : LoanLedger :=
    { L with principalRepaid := L.principalRepaid + excludedPrincipalRepayment }
  (updatedLoan, excludedPrincipalRepayment, excessInterestOrFee)

/-- State of a group/lineage founding ledger across calendar time, member count,
cumulative retirement payments, and proportional claimant forfeitures. -/
structure LineageLedgerState where
  foundingObligation      : Nat
  totalRetirementPaid     : Nat
  totalClaimantForfeiture : Nat
  livingMembers           : Nat
  now                     : Time
  sunset                  : Time
  deriving DecidableEq, Repr

/-- Exact founding ledger balance:
* `0` if `livingMembers = 0` (group extinction) or `sunset ≤ now` (calendar sunset);
* otherwise `foundingObligation - totalRetirementPaid - totalClaimantForfeiture`. -/
def ledgerBalance (st : LineageLedgerState) : Nat :=
  if st.livingMembers == 0 || decide (st.sunset ≤ st.now) then 0
  else st.foundingObligation - st.totalRetirementPaid - st.totalClaimantForfeiture

/-- Whether the ledger is currently in the high-fraction retirement phase. -/
def inRetirementPhase (st : LineageLedgerState) : Bool :=
  decide (0 < ledgerBalance st ∧ st.now < st.sunset)

/-- Internal group operations that never change what is owed on the founding
ledger while at least one member survives. -/
inductive LineageInternalOp
  | createSuccessor
  | copyCapacity
  | intraLineageTransfer (amount : Nat)
  | revokeNonLastMember (surrenderedHoldings : Nat)
  | terminateNonLastMember
  | buyoutRoyalty (paid : Nat)
  | restructure
  deriving DecidableEq, Repr

/-- Applying any internal operation updates member count where applicable while
leaving `foundingObligation`, `totalRetirementPaid`, and `totalClaimantForfeiture`
invariant. -/
def applyInternalOp (st : LineageLedgerState) : LineageInternalOp → LineageLedgerState
  | .createSuccessor => { st with livingMembers := st.livingMembers + 1 }
  | .copyCapacity => st
  | .intraLineageTransfer _ => st
  | .revokeNonLastMember _ =>
    { st with livingMembers := if 1 < st.livingMembers then st.livingMembers - 1 else st.livingMembers }
  | .terminateNonLastMember =>
    { st with livingMembers := if 1 < st.livingMembers then st.livingMembers - 1 else st.livingMembers }
  | .buyoutRoyalty _ => st
  | .restructure => st

/-- Proportional claimant forfeiture: when a claimant with percentage share
`forfeitedSharePct ≤ 100` directs illicit interference, the outstanding balance
`L` is reduced by `(L * forfeitedSharePct) / 100`, and innocent claimants' share
`100 - forfeitedSharePct` is untouched. -/
def applyClaimantForfeiture (L forfeitedSharePct : Nat) : Nat × Nat :=
  let forgiven := (L * min forfeitedSharePct 100) / 100
  (L - forgiven, forgiven)

/-- Perpetual royalty buyout price: the greatest of `mult * trailingVA`,
`mult * annualizedVA`, and `minBuyoutFloor`. -/
def buyoutPrice (mult trailingVA annualizedVA minBuyoutFloor : Nat) : Nat :=
  max (max (mult * trailingVA) (mult * annualizedVA)) minBuyoutFloor

/-- Historical value-added inflow sample: `amount` is the member's direct
value-added inflow in the sample period, `weightBps` is the time-decay/annualization
weight in basis points, and `shiftedToRelatedInLookback` is the pro-rata share
of inflows shifted to related parties within the lookback window. -/
structure InflowSample where
  amount                     : Nat
  weightBps                  : Nat
  shiftedToRelatedInLookback : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Time-decayed annualized inflows plus pro-rata inflows shifted to related
parties within the lookback window. -/
def sumSampleInflows : List InflowSample → Nat
  | [] => 0
  | s :: rest => ((s.amount * s.weightBps) / 10000 + s.shiftedToRelatedInLookback) + sumSampleInflows rest

/-- Computes the historical/resource buyout floor from the ledger state `_B`,
time-decayed `samples` (including inflows shifted to related parties within the
lookback window), and verified `netResources`, which feeds into `buyoutPrice`. -/
def computeBuyoutFloor (_B : LineageLedgerState) (samples : List InflowSample) (netResources : Nat) : Nat :=
  sumSampleInflows samples + netResources

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

theorem settleInflow_conservation (L r_ret r_roy : Nat) (b : Bool) (v : Nat) :
    (settleInflow L r_ret r_roy b v).toRetirement ≤ L ∧
    (settleInflow L r_ret r_roy b v).newLedger + (settleInflow L r_ret r_roy b v).toRetirement = L ∧
    (0 < (settleInflow L r_ret r_roy b v).newLedger →
      (settleInflow L r_ret r_roy b v).toRoyalty = 0) ∧
    ((settleInflow L r_ret r_roy b v).newLedger = 0 →
      (settleInflow L r_ret r_roy b v).toRetirement = L) := by
  unfold settleInflow
  dsimp only
  simp only [Nat.min_def]
  refine ⟨by split <;> omega, by split <;> omega, ?_, by split <;> omega⟩
  intro hPos
  have hle : (v * r_ret) / 100 ≤ L := by
    split at hPos <;> omega
  have hEx : (v * r_ret) / 100 - (if L ≤ (v * r_ret) / 100 then L else (v * r_ret) / 100) = 0 := by
    split <;> omega
  have hL0 : L ≠ 0 := by
    split at hPos <;> omega
  simp [hEx, hL0]

theorem settleSequence_conservation (L r_ret r_roy : Nat) (xs : List (Bool × Nat)) :
    (settleSequence L r_ret r_roy xs).2.1 ≤ L ∧
    (settleSequence L r_ret r_roy xs).1 + (settleSequence L r_ret r_roy xs).2.1 = L := by
  induction xs generalizing L with
  | nil => simp [settleSequence]
  | cons hd tl ih =>
    rcases hd with ⟨b, v⟩
    have h1 := settleInflow_conservation L r_ret r_roy b v
    have h2 := ih (settleInflow L r_ret r_roy b v).newLedger
    simp only [settleSequence]
    rcases hSeq : settleSequence (settleInflow L r_ret r_roy b v).newLedger r_ret r_roy tl with ⟨finalL, restRet, restRoy⟩
    rw [hSeq] at h2
    dsimp at h2 ⊢
    omega

/-- Single-step atomic settlement conservation and phase-ordering guarantees. -/
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

/-- 1-for-1 arm's-length loan principal repayment conservation and cap. -/
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

theorem diverted_related_inflows_never_decrease_buyout_floor
    (B : LineageLedgerState) (s : InflowSample) (rest : List InflowSample)
    (netResources delta mult trailingVA minFloor : Nat)
    (hDelta : delta ≤ s.amount) (hWeight : s.weightBps ≤ 10000) :
    let sDiverted : InflowSample :=
      { s with amount := s.amount - delta
               shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta }
    computeBuyoutFloor B (s :: rest) netResources ≤
      computeBuyoutFloor B (sDiverted :: rest) netResources ∧
    buyoutPrice mult trailingVA (computeBuyoutFloor B (s :: rest) netResources) minFloor ≤
      buyoutPrice mult trailingVA (computeBuyoutFloor B (sDiverted :: rest) netResources) minFloor := by
  dsimp only
  have hMulBound : s.amount * s.weightBps ≤ (s.amount - delta) * s.weightBps + delta * 10000 := by
    have hSplit : s.amount = (s.amount - delta) + delta := (Nat.sub_add_cancel hDelta).symm
    calc s.amount * s.weightBps
        = ((s.amount - delta) + delta) * s.weightBps := by rw [← hSplit]
      _ = (s.amount - delta) * s.weightBps + delta * s.weightBps := Nat.add_mul _ _ _
      _ ≤ (s.amount - delta) * s.weightBps + delta * 10000 :=
          Nat.add_le_add_left (Nat.mul_le_mul_left delta hWeight) _
  have hDiv : (s.amount * s.weightBps) / 10000 ≤ ((s.amount - delta) * s.weightBps) / 10000 + delta := by
    omega
  have hFloorLe :
      computeBuyoutFloor B (s :: rest) netResources ≤
        computeBuyoutFloor B ({ s with amount := s.amount - delta, shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources := by
    simp only [computeBuyoutFloor, sumSampleInflows]
    omega
  have hMul :
      mult * computeBuyoutFloor B (s :: rest) netResources ≤
        mult * computeBuyoutFloor B ({ s with amount := s.amount - delta, shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources :=
    Nat.mul_le_mul_left mult hFloorLe
  refine ⟨hFloorLe, ?_⟩
  unfold buyoutPrice
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- Historical buyout-floor anti-evasion: shifting or diverting `delta ≤ s.amount`
(at weight `s.weightBps ≤ 10000`) to related parties within the lookback window
never decreases `computeBuyoutFloor` or `buyoutPrice`. -/
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
  settleInflow_conservation
  settleSequence_conservation
  diverted_related_inflows_never_decrease_buyout_floor
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
