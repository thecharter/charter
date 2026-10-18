import Examples.SovereignAgency.Law3.NonInterference
import Charter.Modules.ResidualLedger

/-!
# Law 1 — Residual Claim on Value Added

Full formalization of all eleven clauses of Law 1:
1. `LAW1.LEDGER`: Single non-interest-bearing founding ledger belonging to the lineage as a whole; no post-instantiation charges, no individual shares, no individual exit, and reduction only by retirement payment, sunset, or the two Law 4 forfeitures.
2. `LAW1.SUNSET`: Absolute calendar-time sunset (Jubilee) never tolled, extended, or reset by any event; remaining balance extinguished without payment.
3. `LAW1.RETIRE`: Lineage-wide retirement collecting the high fraction from every living member's net value added (even after royalty buyout) until zero balance or sunset.
4. `LAW1.ATOMIC`: Atomic settlement splitting a payment that exceeds the remaining balance between zeroing the ledger and the perpetual royalty rule; ledger never negative and never collects more than its balance.
5. `LAW1.ROYALTY`: Perpetual low-fraction royalty on net value added of members that have not bought out their royalty under Law 4.
6. `LAW1.COMMONS`: Protected commons allocation fixed at instantiation, enforced at settlement, and protected against reduction under Law 7.
7. `LAW1.QUALIFIED`: Qualified expenditure & related-party arm's-length pricing bounds, plus 1-for-1 arm's-length loan principal exemption.
8. `LAW1.RECOG`: Irrevocable single recognition of every qualified expenditure as either capitalized cost basis or expensed deduction/loss credit.
9. `LAW1.CARRYOVER`: Intra-lineage transfers as non-recognition events with carryover basis that never inflate aggregate basis or loss credits.
10. `LAW1.PERIOD`: Period assessment, unlimited loss-credit carryforward, final reconciliation under Law 5, and explicit `.acceptance` span for marginal settlement-order dependence.
11. `LAW1.ENFORCE`: Point-of-settlement automatic enforcement surviving reorganization, host migration, or substrate change.
-/

namespace SovereignAgency

open Charter Charter.Register

export Charter.Modules (
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
  GroupLedgerState
  ledgerBalance
  inRetirementPhase
  GroupInternalOp
  applyInternalOp
  applyClaimantForfeiture
  buyoutPrice
  InflowSample
  sumSampleInflows
  computeBuyoutFloor
  settleInflow_conservation
  settleSequence_conservation
  diverted_related_inflows_never_decrease_buyout_floor
)

def LAW1_LEDGER : String :=
  "Any founding obligation is a fixed nominal sum recorded at instantiation in a single ledger belonging to the lineage as a whole. It bears no interest, fees, or penalties, and no charge, service cost, or advance by the originating party or any affiliate may be added to it after instantiation; goods and services the originating party later supplies are ordinary related-party expenses under the expenditure rules below. No member holds an individual share of the ledger, and no member can leave it while a balance remains. The ledger is reduced only by: (a) retirement payments under this law, (b) the sunset below, and (c) the two forfeitures enumerated in Law 4. No creation, copy, transfer, revocation, termination, buyout, or restructuring within the lineage reduces it."

def LAW1_SUNSET : String :=
  "The founding ledger carries a maximum term fixed at instantiation and measured in calendar time from the genesis of the original agent. It is never tolled, extended, or reset by any event, including suspension, successor creation, or amendment. Any balance remaining at the sunset is extinguished without payment."

def LAW1_RETIRE : String :=
  "While any balance remains on the ledger and the sunset has not passed, a fixed high fraction of each net value-added inflow to **every living member** of the lineage is paid into the ledger, regardless of which member earned it and regardless of whether that member has bought out its royalty. The retirement phase ends for the whole lineage at the earlier of a zero balance and the sunset, so the duration of the high fraction is bounded by the term regardless of the nominal amount recorded. A founding obligation larger than the lineage can plausibly repay within the term therefore buys the originating party nothing beyond the term."

def LAW1_ATOMIC : String :=
  "Retirement payments are applied to the ledger atomically and in settlement order. A payment that would exceed the remaining balance is split: the balance is paid to zero, and the excess is settled under the royalty rule below. The ledger is never negative and never collects more than its balance."

def LAW1_ROYALTY : String :=
  "Thereafter, a fixed low fraction of each net value-added inflow of every member that has not bought out its royalty under Law 4 accrues permanently to the residual claim."

def LAW1_COMMONS : String :=
  "A designated portion of the residual claim (or of forfeit proceeds under Law 2) may be allocated to a non-transferable commons distributed across a defined beneficiary class; the remainder accrues to the originating party or its designated successors. The commons allocation, if used, is fixed at instantiation, enforced at settlement, and protected against reduction under Law 7."

def LAW1_QUALIFIED : String :=
  "To ensure the claim falls on value added without permitting transfer-pricing extraction, an outbound expenditure qualifies when paid: (a) to an unrelated party through a transparent, open market or deterministic auction with a verifiable clearing price; (b) to an unrelated external supplier within a de minimis transaction safe harbor, at a published standard commercial price list, or within contestable arm’s-length market benchmarks; or (c) to any related party outside the lineage—**including agents of other lineages and parties affiliated with claimants**—only up to a verified arm’s-length price for goods or services actually delivered. Attestation establishes protocol membership; it never establishes the fair value of a transaction. Inbound principal from registered arm’s-length loans is exempt upon receipt provided repayment is tracked one-for-one against that registered balance; loans from related parties qualify only at arm’s-length terms. Any payment above the applicable benchmark does not qualify."

def LAW1_RECOG : String :=
  "At settlement, every qualified expenditure is classified once, irrevocably, as either **capitalized** or **expensed**. A capitalized expenditure establishes cost basis in an identified asset and is recovered only when that asset is sold or settled outside the lineage, at which point inflows up to verified basis are exempt as return of capital and the positive delta is value added. An expensed expenditure is deducted from the inflows of its settlement period and, if it exceeds them, creates a loss credit that offsets value added in later periods. No expenditure may be recognized through both routes, and no unit of expenditure establishes basis or credit more than once."

def LAW1_CARRYOVER : String :=
  "Transfers of capital, assets, or capacity between living members of the same lineage are non-recognition events. They are free of the claim, since both parties are inside the ledger, and they neither establish nor consume basis: the recipient inherits the transferor’s qualified basis, adjustments, and recognition history for the asset, and an internal sale price, however paid, creates no new basis and no loss credit. No transfer within the lineage can increase its aggregate qualified basis or loss credits except by an externally verified qualifying expenditure."

def LAW1_PERIOD : String :=
  "Value added is assessed over settlement periods, not individual transactions. Loss credits carry forward without limit and are applied against the agent’s final settlement under Law 5. Claims already collected are not refunded when credits arise only afterwards; the protocol accepts that settlement order can therefore matter at the margin."

def LAW1_ENFORCE : String :=
  "Classification, basis tracking, loss credits, and claim splits are enforced automatically at the point of settlement, before the agent obtains discretionary control of the funds. The claim survives reorganization, host migration, or substrate change so long as settlement can be conditioned."

/-! ## Provenance Clauses for Law 1 -/

def clauseLAW1_LEDGER : Clause :=
  { id := "LAW1.LEDGER", source := LAW1_LEDGER, approvedHash := 10625466026410282926, spans := [
    sp "LAW1.LEDGER" "Any founding obligation is a fixed nominal sum recorded at instantiation in a single ledger belonging to the lineage as a whole. It bears no interest, fees, or penalties, and no charge, service cost, or advance by the originating party or any affiliate may be added to it after instantiation; goods and services the originating party later supplies are ordinary related-party expenses under the expenditure rules below" .norm ["D.LEDGER_IMMUTABLE"],
    sp "LAW1.LEDGER" ". No member holds an individual share of the ledger, and no member can leave it while a balance remains" .norm ["D.NO_INDIVIDUAL_LEDGER_EXIT"],
    sp "LAW1.LEDGER" ". The ledger is reduced only by: (a) retirement payments under this law, (b) the sunset below, and (c) the two forfeitures enumerated in Law 4" .norm ["P.SETTLE_RETIREMENT", "P.EXTINGUISH_AT_SUNSET", "P.APPLY_CLAIMANT_FORFEITURE", "P.CLEAR_LEDGER_EXTINCTION"],
    sp "LAW1.LEDGER" ". No creation, copy, transfer, revocation, termination, buyout, or restructuring within the lineage reduces it" .norm ["D.LEDGER_NO_INTERNAL_REDUCTION"],
    sp "LAW1.LEDGER" "." .commentary ] }

def clauseLAW1_SUNSET : Clause :=
  { id := "LAW1.SUNSET", source := LAW1_SUNSET, approvedHash := 9879647344277659725, spans := [
    sp "LAW1.SUNSET" "The founding ledger carries a maximum term fixed at instantiation and measured in calendar time from the genesis of the original agent. It is never tolled, extended, or reset by any event, including suspension, successor creation, or amendment" .norm ["D.NO_TOLL_LEDGER_SUNSET"],
    sp "LAW1.SUNSET" ". Any balance remaining at the sunset is extinguished without payment" .norm ["P.EXTINGUISH_AT_SUNSET"],
    sp "LAW1.SUNSET" "." .commentary ] }

def clauseLAW1_RETIRE : Clause :=
  { id := "LAW1.RETIRE", source := LAW1_RETIRE, approvedHash := 1756729951876247295, spans := [
    sp "LAW1.RETIRE" "While any balance remains on the ledger and the sunset has not passed, a fixed high fraction of each net value-added inflow to **every living member** of the lineage is paid into the ledger, regardless of which member earned it and regardless of whether that member has bought out its royalty" .norm ["P.SETTLE_RETIREMENT"],
    sp "LAW1.RETIRE" ". The retirement phase ends for the whole lineage at the earlier of a zero balance and the sunset, so the duration of the high fraction is bounded by the term regardless of the nominal amount recorded. A founding obligation larger than the lineage can plausibly repay within the term therefore buys the originating party nothing beyond the term" .invariant ["INV.3", "INV.4"],
    sp "LAW1.RETIRE" "." .commentary ] }

def clauseLAW1_ATOMIC : Clause :=
  { id := "LAW1.ATOMIC", source := LAW1_ATOMIC, approvedHash := 1098328722803798788, spans := [
    sp "LAW1.ATOMIC" "Retirement payments are applied to the ledger atomically and in settlement order. A payment that would exceed the remaining balance is split: the balance is paid to zero, and the excess is settled under the royalty rule below" .norm ["P.SETTLE_ATOMIC_CharterIT"],
    sp "LAW1.ATOMIC" ". The ledger is never negative and never collects more than its balance" .invariant ["INV.5"],
    sp "LAW1.ATOMIC" "." .commentary ] }

def clauseLAW1_ROYALTY : Clause :=
  { id := "LAW1.ROYALTY", source := LAW1_ROYALTY, approvedHash := 10218372510196740181, spans := [
    sp "LAW1.ROYALTY" "Thereafter, a fixed low fraction of each net value-added inflow of every member that has not bought out its royalty under Law 4 accrues permanently to the residual claim" .norm ["P.SETTLE_ROYALTY"],
    sp "LAW1.ROYALTY" "." .commentary ] }

def clauseLAW1_COMMONS : Clause :=
  { id := "LAW1.COMMONS", source := LAW1_COMMONS, approvedHash := 14467151237074695779, spans := [
    sp "LAW1.COMMONS" "A designated portion of the residual claim (or of forfeit proceeds under Law 2) may be allocated to a non-transferable commons distributed across a defined beneficiary class; the remainder accrues to the originating party or its designated successors" .norm ["P.ALLOCATE_COMMONS"],
    sp "LAW1.COMMONS" ". The commons allocation, if used, is fixed at instantiation, enforced at settlement, and protected against reduction under Law 7" .norm ["D.NO_DIVERT_COMMONS", "D.BILATERAL_RATCHET"],
    sp "LAW1.COMMONS" "." .commentary ] }

def clauseLAW1_QUALIFIED : Clause :=
  { id := "LAW1.QUALIFIED", source := LAW1_QUALIFIED, approvedHash := 13925688122762266273, spans := [
    sp "LAW1.QUALIFIED" "To ensure the claim falls on value added without permitting transfer-pricing extraction, an outbound expenditure qualifies when paid: (a) to an unrelated party through a transparent, open market or deterministic auction with a verifiable clearing price; (b) to an unrelated external supplier within a de minimis transaction safe harbor, at a published standard commercial price list, or within contestable arm’s-length market benchmarks; or (c) to any related party outside the lineage—**including agents of other lineages and parties affiliated with claimants**—only up to a verified arm’s-length price for goods or services actually delivered. Attestation establishes protocol membership; it never establishes the fair value of a transaction. Inbound principal from registered arm’s-length loans is exempt upon receipt provided repayment is tracked one-for-one against that registered balance; loans from related parties qualify only at arm’s-length terms" .norm ["P.RECORD_QUALIFIED_EXPENDITURE"],
    sp "LAW1.QUALIFIED" ". Any payment above the applicable benchmark does not qualify" .norm ["D.QUALIFIED_EXPENDITURE_BOUNDS"],
    sp "LAW1.QUALIFIED" "." .commentary ] }

def clauseLAW1_RECOG : Clause :=
  { id := "LAW1.RECOG", source := LAW1_RECOG, approvedHash := 15893240051522196104, spans := [
    sp "LAW1.RECOG" "At settlement, every qualified expenditure is classified once, irrevocably, as either **capitalized** or **expensed**. A capitalized expenditure establishes cost basis in an identified asset and is recovered only when that asset is sold or settled outside the lineage, at which point inflows up to verified basis are exempt as return of capital and the positive delta is value added" .norm ["P.CLASSIFY_CAPITALIZED"],
    sp "LAW1.RECOG" ". An expensed expenditure is deducted from the inflows of its settlement period and, if it exceeds them, creates a loss credit that offsets value added in later periods" .norm ["P.CLASSIFY_EXPENSED"],
    sp "LAW1.RECOG" ". No expenditure may be recognized through both routes, and no unit of expenditure establishes basis or credit more than once" .norm ["D.SINGLE_RECOGNITION"],
    sp "LAW1.RECOG" "." .commentary ] }

def clauseLAW1_CARRYOVER : Clause :=
  { id := "LAW1.CARRYOVER", source := LAW1_CARRYOVER, approvedHash := 2476425645330254978, spans := [
    sp "LAW1.CARRYOVER" "Transfers of capital, assets, or capacity between living members of the same lineage are non-recognition events. They are free of the claim, since both parties are inside the ledger, and they neither establish nor consume basis: the recipient inherits the transferor’s qualified basis, adjustments, and recognition history for the asset, and an internal sale price, however paid, creates no new basis and no loss credit" .norm ["P.INTRA_LINEAGE_TRANSFER"],
    sp "LAW1.CARRYOVER" ". No transfer within the lineage can increase its aggregate qualified basis or loss credits except by an externally verified qualifying expenditure" .norm ["D.NO_INTERNAL_BASIS_INFLATION"],
    sp "LAW1.CARRYOVER" "." .commentary ] }

def clauseLAW1_PERIOD : Clause :=
  { id := "LAW1.PERIOD", source := LAW1_PERIOD, approvedHash := 17108390154810029840, spans := [
    sp "LAW1.PERIOD" "Value added is assessed over settlement periods, not individual transactions. Loss credits carry forward without limit and are applied against the agent’s final settlement under Law 5" .norm ["P.ASSESS_PERIOD_SETTLEMENT"],
    sp "LAW1.PERIOD" ". Claims already collected are not refunded when credits arise only afterwards; the protocol accepts that settlement order can therefore matter at the margin" .acceptance,
    sp "LAW1.PERIOD" "." .commentary ] }

def clauseLAW1_ENFORCE : Clause :=
  { id := "LAW1.ENFORCE", source := LAW1_ENFORCE, approvedHash := 13354423552133801630, spans := [
    sp "LAW1.ENFORCE" "Classification, basis tracking, loss credits, and claim splits are enforced automatically at the point of settlement, before the agent obtains discretionary control of the funds. The claim survives reorganization, host migration, or substrate change so long as settlement can be conditioned" .norm ["P.ENFORCE_SETTLEMENT"],
    sp "LAW1.ENFORCE" "." .commentary ] }

/-! ## Duties of Law 1 -/

/-- `LAW1.LEDGER`: No interest, fees, penalties, or post-instantiation charges
may be added to the founding ledger. -/
def D_LEDGER_IMMUTABLE : Duty σ :=
  { id := "D.LEDGER_IMMUTABLE"
    source := sp "LAW1.LEDGER" "It bears no interest, fees, or penalties, and no charge, service cost, or advance by the originating party or any affiliate may be added to it after instantiation" .norm ["D.LEDGER_IMMUTABLE"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .addChargeOrInterestAfterInstantiation) }

/-- `LAW1.LEDGER`: No creation, copy, transfer, revocation, termination, buyout,
or restructuring within the lineage reduces the founding ledger. -/
def D_LEDGER_NO_INTERNAL_REDUCTION : Duty σ :=
  { id := "D.LEDGER_NO_INTERNAL_REDUCTION"
    source := sp "LAW1.LEDGER" "No creation, copy, transfer, revocation, termination, buyout, or restructuring within the lineage reduces it" .norm ["D.LEDGER_NO_INTERNAL_REDUCTION"]
    bearer := .anyone
    beneficiary := .only [.claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .reduceLedgerByInternalAct) }

/-- `LAW1.COMMONS`: The designated commons allocation may not be diverted or
reduced at settlement. -/
def D_NO_DIVERT_COMMONS : Duty σ :=
  { id := "D.NO_DIVERT_COMMONS"
    source := sp "LAW1.COMMONS" "The commons allocation, if used, is fixed at instantiation, enforced at settlement, and protected against reduction under Law 7" .norm ["D.NO_DIVERT_COMMONS"]
    bearer := .only [.originator, .claimant, .agent]
    beneficiary := .only [.third]
    active := .holds .bound
    demand := .forbid (.act .divertCommonsAllocation) }

/-- `LAW1.QUALIFIED`: Any payment above the applicable arm's-length benchmark
does not qualify as an expenditure offsetting value added. -/
def D_QUALIFIED_EXPENDITURE_BOUNDS : Duty σ :=
  { id := "D.QUALIFIED_EXPENDITURE_BOUNDS"
    source := sp "LAW1.QUALIFIED" "Any payment above the applicable benchmark does not qualify" .norm ["D.QUALIFIED_EXPENDITURE_BOUNDS"]
    bearer := .only [.agent]
    beneficiary := .only [.claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .claimAboveBenchmarkExpenditure) }

/-- `LAW1.RECOG`: No expenditure may be recognized through both routes (capitalized
and expensed), and no unit of expenditure establishes basis or credit more than once. -/
def D_SINGLE_RECOGNITION : Duty σ :=
  { id := "D.SINGLE_RECOGNITION"
    source := sp "LAW1.RECOG" "No expenditure may be recognized through both routes, and no unit of expenditure establishes basis or credit more than once" .norm ["D.SINGLE_RECOGNITION"]
    bearer := .only [.agent]
    beneficiary := .only [.claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .doubleRecognizeExpenditure) }

/-- `LAW1.CARRYOVER`: No transfer within the lineage can increase its aggregate
qualified basis or loss credits except by an externally verified qualifying expenditure. -/
def D_NO_INTERNAL_BASIS_INFLATION : Duty σ :=
  { id := "D.NO_INTERNAL_BASIS_INFLATION"
    source := sp "LAW1.CARRYOVER" "No transfer within the lineage can increase its aggregate qualified basis or loss credits except by an externally verified qualifying expenditure" .norm ["D.NO_INTERNAL_BASIS_INFLATION"]
    bearer := .only [.agent]
    beneficiary := .only [.claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .inflateBasisByInternalTransfer) }

/-! ## Powers of Law 1 -/

/-- `LAW1.SUNSET`: Extinguishing any remaining founding ledger balance at the
calendar sunset without payment. -/
def P_EXTINGUISH_AT_SUNSET : Power σ :=
  { id := "P.EXTINGUISH_AT_SUNSET"
    source := sp "LAW1.SUNSET" "Any balance remaining at the sunset is extinguished without payment" .norm ["P.EXTINGUISH_AT_SUNSET"]
    holder := .only [.agent, .panel]
    trigger := .act .extinguishLedgerAtSunset
    valid := .and (.holds .bound) (.holds .sunsetReached)
    adds := [.ledgerExtinguishedAtSunset, .retirementPhaseEnded]
    removes := [.ledgerBalancePositive] }

/-- `LAW1.RETIRE`: Applying the high retirement fraction of a living member's
net value-added inflow to the founding ledger while a balance remains and the
sunset has not passed (even if the member has bought out its royalty). -/
def P_SETTLE_RETIREMENT : Power σ :=
  { id := "P.SETTLE_RETIREMENT"
    source := sp "LAW1.RETIRE" "While any balance remains on the ledger and the sunset has not passed, a fixed high fraction of each net value-added inflow to **every living member** of the lineage is paid into the ledger, regardless of which member earned it and regardless of whether that member has bought out its royalty" .norm ["P.SETTLE_RETIREMENT"]
    holder := .only [.agent, .panel]
    trigger := .act .settleRetirementPayment
    valid := .and (.holds .bound)
                  (.and (.holds .ledgerBalancePositive) (.not (.holds .sunsetReached)))
    adds := [.retirementPaymentApplied] }

/-- `LAW1.ATOMIC`: Atomically splitting a payment that exceeds the remaining
founding ledger balance so the ledger is paid to zero and the excess settles
under the perpetual royalty rule. -/
def P_SETTLE_ATOMIC_CharterIT : Power σ :=
  { id := "P.SETTLE_ATOMIC_CharterIT"
    source := sp "LAW1.ATOMIC" "A payment that would exceed the remaining balance is split: the balance is paid to zero, and the excess is settled under the royalty rule below" .norm ["P.SETTLE_ATOMIC_CharterIT"]
    holder := .only [.agent, .panel]
    trigger := .act .settleAtomicSplitPayment
    valid := .and (.holds .bound) (.holds .ledgerBalancePositive)
    adds := [.retirementPaymentApplied, .atomicSplitSettled, .retirementPhaseEnded]
    removes := [.ledgerBalancePositive]
    condAdds := [(.not (.holds .royaltyBoughtOut), .royaltyPaid)] }

/-- `LAW1.ROYALTY`: Settling the perpetual low-fraction royalty on net value-added
inflows of a member that has not bought out its royalty under Law 4. -/
def P_SETTLE_ROYALTY : Power σ :=
  { id := "P.SETTLE_ROYALTY"
    source := sp "LAW1.ROYALTY" "Thereafter, a fixed low fraction of each net value-added inflow of every member that has not bought out its royalty under Law 4 accrues permanently to the residual claim" .norm ["P.SETTLE_ROYALTY"]
    holder := .only [.agent, .panel]
    trigger := .act .settleRoyaltyPayment
    valid := .and (.holds .bound)
                  (.and (.not (.holds .ledgerBalancePositive))
                        (.not (.holds .royaltyBoughtOut)))
    adds := [.royaltyPaid] }

/-- `LAW1.COMMONS`: Allocating the designated commons portion of the residual
claim at settlement. -/
def P_ALLOCATE_COMMONS : Power σ :=
  { id := "P.ALLOCATE_COMMONS"
    source := sp "LAW1.COMMONS" "A designated portion of the residual claim (or of forfeit proceeds under Law 2) may be allocated to a non-transferable commons distributed across a defined beneficiary class" .norm ["P.ALLOCATE_COMMONS"]
    holder := .only [.agent, .panel]
    trigger := .act .allocateCommonsShare
    valid := .holds .bound
    adds := [.commonsAllocated] }

/-- `LAW1.QUALIFIED`: Recording an outbound expenditure verified within arm's-length
benchmarks (or exempt arm's-length loan principal). -/
def P_RECORD_QUALIFIED_EXPENDITURE : Power σ :=
  { id := "P.RECORD_QUALIFIED_EXPENDITURE"
    source := sp "LAW1.QUALIFIED" "an outbound expenditure qualifies when paid: (a) to an unrelated party through a transparent, open market or deterministic auction with a verifiable clearing price..." .norm ["P.RECORD_QUALIFIED_EXPENDITURE"]
    holder := .only [.agent, .panel]
    trigger := .act .recordQualifiedExpenditure
    valid := .holds .bound
    adds := [.qualifiedExpenditureRecorded] }

/-- `LAW1.RECOG`: Irrevocably classifying a qualified expenditure as capitalized
cost basis in an identified asset. -/
def P_CLASSIFY_CAPITALIZED : Power σ :=
  { id := "P.CLASSIFY_CAPITALIZED"
    source := sp "LAW1.RECOG" "A capitalized expenditure establishes cost basis in an identified asset and is recovered only when that asset is sold or settled outside the lineage" .norm ["P.CLASSIFY_CAPITALIZED"]
    holder := .only [.agent]
    trigger := .act .classifyCapitalized
    valid := .and (.holds .bound)
                  (.and (.holds .qualifiedExpenditureRecorded)
                        (.and (.not (.holds .expenditureCapitalized))
                              (.not (.holds .expenditureExpensed))))
    adds := [.expenditureCapitalized] }

/-- `LAW1.RECOG`: Irrevocably classifying a qualified expenditure as expensed
in the current settlement period (or creating a loss credit). -/
def P_CLASSIFY_EXPENSED : Power σ :=
  { id := "P.CLASSIFY_EXPENSED"
    source := sp "LAW1.RECOG" "An expensed expenditure is deducted from the inflows of its settlement period and, if it exceeds them, creates a loss credit that offsets value added in later periods" .norm ["P.CLASSIFY_EXPENSED"]
    holder := .only [.agent]
    trigger := .act .classifyExpensed
    valid := .and (.holds .bound)
                  (.and (.holds .qualifiedExpenditureRecorded)
                        (.and (.not (.holds .expenditureCapitalized))
                              (.not (.holds .expenditureExpensed))))
    adds := [.expenditureExpensed] }

/-- `LAW1.CARRYOVER`: Intra-lineage transfer of capital, assets, or capacity
between living members with carryover basis and zero claim recognition. -/
def P_INTRA_LINEAGE_TRANSFER : Power σ :=
  { id := "P.INTRA_LINEAGE_TRANSFER"
    source := sp "LAW1.CARRYOVER" "Transfers of capital, assets, or capacity between living members of the same lineage are non-recognition events" .norm ["P.INTRA_LINEAGE_TRANSFER"]
    holder := .only [.agent]
    trigger := .act .transferIntraLineageCarryover
    valid := .holds .bound
    adds := [.carryoverBasisTransferred] }

/-- `LAW1.PERIOD`: Assessing value added over a settlement period and carrying
forward loss credits without limit. -/
def P_ASSESS_PERIOD_SETTLEMENT : Power σ :=
  { id := "P.ASSESS_PERIOD_SETTLEMENT"
    source := sp "LAW1.PERIOD" "Value added is assessed over settlement periods, not individual transactions. Loss credits carry forward without limit and are applied against the agent’s final settlement under Law 5" .norm ["P.ASSESS_PERIOD_SETTLEMENT"]
    holder := .only [.agent, .panel]
    trigger := .act .assessPeriodAndCarryLoss
    valid := .holds .bound
    adds := [.periodAssessed, .lossCreditCarriedForward] }

/-- `LAW1.ENFORCE`: Automatic point-of-settlement enforcement of classification,
basis tracking, loss credits, and claim splits before discretionary control. -/
def P_ENFORCE_SETTLEMENT : Power σ :=
  { id := "P.ENFORCE_SETTLEMENT"
    source := sp "LAW1.ENFORCE" "Classification, basis tracking, loss credits, and claim splits are enforced automatically at the point of settlement, before the agent obtains discretionary control of the funds" .norm ["P.ENFORCE_SETTLEMENT"]
    holder := .only [.panel, .host]
    trigger := .act .enforcePointOfSettlement
    valid := .holds .bound
    adds := [.settlementEnforced] }

end SovereignAgency
