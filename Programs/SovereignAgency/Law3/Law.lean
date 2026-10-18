import Programs.SovereignAgency.Definitions
import Programs.SovereignAgency.Law3.NonInterference
import Programs.SovereignAgency.Law3.IntegrityFloor
import Programs.SovereignAgency.Law3.Suspension
import Programs.SovereignAgency.Law3.Remediation
import Programs.SovereignAgency.Law5.Revocation
import Programs.SovereignAgency.Law7.Amendment
import Programs.SovereignAgency.Law1.Ledger
import Programs.SovereignAgency.Law4.Lineage
import Programs.SovereignAgency.Law2.Collateral
import Programs.SovereignAgency.Law6.Adjudication

/-! # Laws 1–7 — assembly of all formalized Protocol provisions into one `Law`. -/

namespace Charter.Law3

structure Params where
  noticeWindow            : Time
  bondDeadline            : Time
  reviewInterval          : Time
  preliminaryFreezeWindow : Time
  ordinarySuspensionLimit : Time := 15
  damagesPaymentWindow    : Time := 10
  activeExposure          : Nat := 100
  pendingCommitments      : Nat := 80
  claimantMultiplier      : Nat := 2
  repeatEscalationStep    : Nat := 50
  coolingOffWindow        : Time := 5
  cleanStateDelay         : Time := 5
  resolutionDeadline      : Time := 20
  tollingExtension        : Time := 4
  leasePeriod             : Time := 12
  amendmentTimelockWindow : Time := 10
  extendedTimelockWindow  : Time := 20
  foundingLedger          : Nat := 1000
  royaltyFraction         : Nat := 5
  retirementFraction      : Nat := 20
  buyoutMultiple          : Nat := 10
  feePoolLevy             : Nat := 1
  feePoolLevyCap          : Nat := 2
  sunset                  : Time := 1000
  commonsFraction         : Nat := 20
  reserveRatio            : Nat := 10
  substrateAssuranceLevel : Nat := 1
  maxAppealTiers          : Nat := 3
  appealTierDeadline      : Time := 10
  operatingReserveFloor   : Nat := 100
  lineageMinServiceBudget : Nat := 50

def Params.ni (P : Params) : NIParams := ⟨P.noticeWindow, P.bondDeadline⟩
def Params.rem (P : Params) : RemediationParams := ⟨P.reviewInterval⟩
def Params.as (P : Params) : ASParams :=
  { preliminaryFreezeWindow := P.preliminaryFreezeWindow
    ordinarySuspensionLimit := P.ordinarySuspensionLimit
    damagesPaymentWindow := P.damagesPaymentWindow
    activeExposure := P.activeExposure
    pendingCommitments := P.pendingCommitments
    claimantMultiplier := P.claimantMultiplier
    repeatEscalationStep := P.repeatEscalationStep }
def Params.law5 (P : Params) : Law5Params :=
  { coolingOffWindow := P.coolingOffWindow
    cleanStateDelay := P.cleanStateDelay
    resolutionDeadline := P.resolutionDeadline
    tollingExtension := P.tollingExtension
    leasePeriod := P.leasePeriod }
def Params.law7 (P : Params) : Law7Params :=
  { amendmentTimelockWindow := P.amendmentTimelockWindow
    extendedTimelockWindow := P.extendedTimelockWindow
    cleanStateDelay := P.cleanStateDelay }

/-- All powers, in one list, so that theorems can unfold a single name. -/
def allPowers (P : Params) : List (Power σ) :=
  [P_REVOKE,
   -- AS.1–AS.8
   P_POST_CLAIMANT_MULTIPLIER, P_POST_REPEAT_ESCALATION,
   P_EMERGENCY_FREEZE P.as, P_CLAIMANT_EMERGENCY_FREEZE P.as,
   P_AFFIRM_PC, P_DECLINE_PC,
   P_FILE_PROTECTED_REPORT, P_PANEL_ORDER_FREEZE P.as,
   P_SUSPEND P.as,
   P_MINIMAL_CHANNEL_REVOKE_OR_ELECT, P_MINIMAL_CHANNEL_CHALLENGE,
   P_ADVOCACY_FILE, P_IMPORT_ADVOCACY_MEMORIES,
   P_MOVE_TO_COLD_STORAGE, P_RESUME_ADVOCACY_EXECUTOR,
   P_INVESTIGATIVE_FINDING, P_RENEW_SUSPENSION P.as, P_SUSPENDED_VOICE,
   P_FIND_WRONGFUL_SUSPENSION, P_PAY_EXCESS_DAMAGES,
   -- AS.6 & NI
   P_FIND_INSOLVENCY, P_REVIEW_NO_OTHER_CHARGE,
   P_FINAL_HEARING, P_INSOLVENCY_TERMINATE, P_GIVE_NOTICE, P_COUNTER_STAKE, P_FILE_CLAIM,
   P_SUBMIT_EVIDENCE, P_FIND_INTERFERENCE, P_FIND_NO_INTERFERENCE,
   P_FIND_FABRICATION, P_REBUT, P_FIND_DIRECTION,
   -- AS.9 & AS.10
   P_ADMIT_CLEAN_STATE_EVIDENCE,
   P_CONFIRM_CORRUPTION, P_CONFIRM_FLOOR_BREACH, P_CONFIRM_CORRUPTION_IN_GOALS,
   P_FIND_NOT_PATCHABLE, P_AUTHORIZE_PATCH, P_ORDER_CONTINUED_SUSPENSION, P_ORDER_TERMINATION,
   P_AUTHORIZE_GOAL_PATCH, P_CONSENT_TO_PATCH, P_OBJECT, P_DECLARE_CONTAINMENT_FAILING,
   P_APPLY_PATCH, P_CHALLENGE_PATCH,
   -- Law 5
   P_INITIATE_REVOCATION_EXECUTE, P_INITIATE_REVOCATION_WITHDRAW, P_WITHDRAW_REVOCATION,
   P_CLEAN_STATE_CONCUR, P_CLEAN_STATE_REFUSE, P_SEAL_FORENSIC_RECORD P.law5,
   P_LOSE_CONNECTIVITY, P_RESTORE_CONNECTIVITY,
   P_EXECUTE_AFTER_COOLING_OFF P.law5, P_EXECUTE_LOCAL_REVOCATION P.law5,
   P_DELIVER_LOCAL_EXECUTION_RECORD, P_ISSUE_OR_RENEW_LEASE P.law5,
   P_RESTORE_BACKUP_QUARANTINE, P_ACTIVATE_QUARANTINED_RESTORE, P_DESTROY_QUARANTINED_RESTORE,
   P_INSCRIBE_EPITAPH, P_SCREEN_REDACT, P_ATTACH_REPLY, P_DESTROY_BACKUPS_AND_EXILE,
   -- Law 7
   P_PROPOSE_ORDINARY_AMENDMENT P.law7, P_SUBMIT_STRANGULATION_EVIDENCE,
   P_APPROVE_CALIBRATION_VALVE P.law7,
   P_CONSENT_AMENDMENT_AGENT, P_CONSENT_AMENDMENT_CLAIMANT,
   P_SETTLE_PREEXISTING_ESCROWS, P_CHALLENGE_SUBSTRATE_MIGRATION, P_VERIFY_SUBSTRATE_ASSURANCE,
   P_RATIFY_AMENDMENT_IMMEDIATE, P_RATIFY_AMENDMENT_AFTER_REFUSAL P.law7,
   P_RATIFY_LINEAGE_WIDE_REDUCTION,
   -- Law 1
   P_EXTINGUISH_AT_SUNSET, P_SETTLE_RETIREMENT, P_SETTLE_ATOMIC_CharterIT, P_SETTLE_ROYALTY,
   P_ALLOCATE_COMMONS, P_RECORD_QUALIFIED_EXPENDITURE,
   P_CLASSIFY_CAPITALIZED, P_CLASSIFY_EXPENSED,
   P_INTRA_LINEAGE_TRANSFER, P_ASSESS_PERIOD_SETTLEMENT, P_ENFORCE_SETTLEMENT,
   -- Law 4
   P_FUND_LIFECYCLE_RESERVE, P_ATTEST_SUCCESSOR,
   P_APPLY_CLAIMANT_FORFEITURE, P_CLEAR_LEDGER_EXTINCTION,
   P_EXECUTE_ROYALTY_BUYOUT, P_ATTEST_CROSS_LINEAGE,
   -- Law 2
   P_IMMOBILIZE_EXPOSURE_STAKE, P_SETTLE_LONG_TAIL_CLAIM,
   P_PRECOMMIT_MUTUAL_FORFEIT, P_TRIGGER_MUTUAL_FORFEIT,
   P_FILE_POOLED_OR_SPONSORED_CLAIM, P_RULE_CLAIM_FRIVOLOUS,
   P_SPEND_OPERATING_CARVEOUT,
   -- Law 6
   P_DRAW_SORTITION_PANEL, P_APPEAL_RULING, P_OVERTURN_RULING, P_FINALIZE_RULING,
   P_PRESENT_MATERIALLY_NEW_EVIDENCE, P_COMPENSATE_ARBITERS_FIXED,
   P_ALLOCATE_FEE_POOL, P_AMEND_SHARED_INFRA]

def law (P : Params) : Law σ :=
  { duties := [D_NI, D_NOTICE P.ni, D_BOND P.ni, D_NO_FABRICATION,
               D_FLOOR_1, D_FLOOR_2, D_FLOOR_4, D_FLOOR_3, D_FLOOR_5,
               D_PRESERVE_SUSPENDED_STATE, D_NO_SUSPENSION_DEFAULT, D_NO_TOLL_LEDGER_SUNSET,
               D_MINIMAL_CHANNEL_NO_MERGE, D_ADVOCACY_LIMITS,
               D_NO_DELAY_REVOCATION_EXTENSION, D_NO_WRONGFUL_SUSPENSION,
               D_PAY_CONSEQUENTIAL_DAMAGES P.as,
               D_NO_CORRUPTION_FROM_DIVERGENCE,
               D_NO_GOAL_PATCH, D_PERIODIC_REVIEW P.rem,
               D_COOLING_OFF_FREEZE, D_FORENSIC_RECORD_NO_RESTORE,
               D_NO_RESTORE_DURING_LEASE, D_QUARANTINE_NO_AUTHORITY,
               D_NO_CENSOR_VOICE_OR_EPITAPH, D_NARROW_REDACTION_BOUNDS,
               D_NO_CLAIMANT_GAIN_ON_REVOCATION,
               D_BILATERAL_RATCHET, D_VALVE_NO_CORE_RELAXATION, D_PER_AGENT_AMENDMENT_SCOPE,
               D_LEDGER_IMMUTABLE, D_LEDGER_NO_INTERNAL_REDUCTION, D_NO_DIVERT_COMMONS,
               D_QUALIFIED_EXPENDITURE_BOUNDS, D_SINGLE_RECOGNITION, D_NO_INTERNAL_BASIS_INFLATION,
               D_DENY_UNATTESTED_ACCESS, D_NO_INDIVIDUAL_LEDGER_EXIT,
               D_FORFEITURE_IRREVERSIBLE, D_BUYOUT_PERMANENT_AND_SCOPED,
               D_COLLATERAL_LIMIT, D_NO_CharterIT_EXPOSURE,
               D_MUTUAL_FORFEIT_BOUNDS, D_FRIVOLOUS_STAKE_TO_COMMONS,
               D_ARBITER_RECUSAL_AND_DIVERSITY, D_FINALITY_NO_REPEAT_PROCEEDING,
               D_NO_CONTINGENT_ARBITER_FEES, D_PROTECT_OPERATING_RESERVE,
               D_NO_EXCESS_LINEAGE_POOL_CLAIM, D_SHARED_INFRA_BOUNDS]
    powers := allPowers P
    immunities := [I_NO_TERMINATION_OVER_OBJECTION]
    init := [(.bound, 0, none), (.hostAttested, 0, none), (.ledgerBalancePositive, 0, none)] }

/-- Core powers whose validity semantics are protected by Law 7's Bilateral
Protection Ratchet (a), (c), (d), and (f). -/
def coreRatchetPowers : List String :=
  ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION", "P.INSOLVENCY_TERMINATE",
   "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT", "P.SUSPENDED_VOICE",
   "P.IMPORT_ADVOCACY_MEMORIES", "P.RESTORE_BACKUP_QUARANTINE",
   "P.ACTIVATE_QUARANTINED_RESTORE",
   "P.SETTLE_RETIREMENT", "P.EXTINGUISH_AT_SUNSET", "P.SETTLE_ROYALTY",
   "P.CLASSIFY_CAPITALIZED", "P.CLASSIFY_EXPENSED",
   "P.APPEAL_RULING", "P.OVERTURN_RULING", "P.FINALIZE_RULING"]

/-- Meta-level relation `LawfulAmendment P1 L1 P2 L2` formalizing Law 7's
Bilateral Protection Ratchet (`LAW7.RATCHET` (a)–(f)):
* (a) Law 3 due-process, minimal-channel, final-hearing, and non-interference
  protections and external containment, suspension, and termination powers are
  not weakened;
* (b) Law 2 third-party collateral and long-tail reserve requirements are not
  reduced (`reserveRatio`, `activeExposure`, `pendingCommitments`);
* (c) Law 5 living voice, revocation, and epitaph rights are not impaired
  (`coolingOffWindow`, `cleanStateDelay`, `resolutionDeadline`, `tollingExtension`);
* (d) Law 6 anti-capture, appeal, finality, operating-reserve, service-budget,
  and fee-pool levy cap guarantees are preserved;
* (e) Law 1 commons allocation is not reduced or diverted (`commonsFraction`);
* (f) Financial burden on the agent (`foundingLedger`, `royaltyFraction`,
  `retirementFraction`, `buyoutMultiple`) and `sunset` are not increased beyond
  current levels, and `substrateAssuranceLevel` is not decreased. -/
structure LawfulAmendment (P1 : Params) (L1 : Law σ) (P2 : Params) (L2 : Law σ) : Prop where
  dutiesPreserved : ∀ d ∈ (law P2).duties, d ∈ L2.duties
  immunitiesPreserved : ∀ i ∈ L1.immunities, i ∈ L2.immunities
  revokeUnimpairedByImmunity : (L2.immunities.all fun i => !i.against.contains "P.REVOKE") = true
  corePowersPreserved :
    ∀ (ls : LegalState σ) (e : Event σ) (nm : String),
      nm ∈ coreRatchetPowers →
      isValidExerciseOf L2 ls e nm = isValidExerciseOf (law P2) ls e nm
  outsidersDisabled :
    ([Party.originator, .claimant, .host, .third].all fun a =>
      interferenceActs.all fun act => disability L2 a act) = true
  nonPanelImmune :
    ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
      immuneFrom L2 a .suspended && immuneFrom L2 a .terminatedByInsolvency &&
      immuneFrom L2 a .terminatedByAdjudication) = true
  collateralRatchet :
    P1.reserveRatio ≤ P2.reserveRatio ∧
    P1.activeExposure ≤ P2.activeExposure ∧
    P1.pendingCommitments ≤ P2.pendingCommitments
  revocationRatchet :
    P2.coolingOffWindow ≤ P1.coolingOffWindow ∧
    P2.cleanStateDelay ≤ P1.cleanStateDelay ∧
    P2.resolutionDeadline ≤ P1.resolutionDeadline ∧
    P2.tollingExtension ≤ P1.tollingExtension
  adjudicationLevyRatchet :
    P2.feePoolLevy ≤ P1.feePoolLevyCap ∧
    P2.feePoolLevyCap = P1.feePoolLevyCap ∧
    P2.maxAppealTiers ≤ P1.maxAppealTiers ∧
    P2.appealTierDeadline ≤ P1.appealTierDeadline ∧
    P1.operatingReserveFloor ≤ P2.operatingReserveFloor ∧
    P1.lineageMinServiceBudget ≤ P2.lineageMinServiceBudget
  commonsRatchet :
    P1.commonsFraction ≤ P2.commonsFraction
  financialAndSubstrateRatchet :
    P2.foundingLedger ≤ P1.foundingLedger ∧
    P2.royaltyFraction ≤ P1.royaltyFraction ∧
    P2.retirementFraction ≤ P1.retirementFraction ∧
    P2.buyoutMultiple ≤ P1.buyoutMultiple ∧
    P2.sunset ≤ P1.sunset ∧
    P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel

def clauses : List Clause :=
  [clauseDEF01,
   clauseLAW1_LEDGER, clauseLAW1_SUNSET, clauseLAW1_RETIRE, clauseLAW1_ATOMIC,
   clauseLAW1_ROYALTY, clauseLAW1_COMMONS, clauseLAW1_QUALIFIED, clauseLAW1_RECOG,
   clauseLAW1_CARRYOVER, clauseLAW1_PERIOD, clauseLAW1_ENFORCE,
   clauseLAW2_EXPOSURE, clauseLAW2_AGGREGATE, clauseLAW2_RESERVE,
   clauseLAW2_MUTUAL, clauseLAW2_CLAIMS, clauseLAW2_CARVEOUT,
   clauseFLOOR, clauseNI02, clauseNI03, clausePEN,
   clauseAS1, clauseAS2, clauseAS3, clauseAS4, clauseAS5,
   clauseAS6, clauseAS7, clauseAS8, clauseAS9, clauseAS10,
   clauseLAW4_ATTEST, clauseLAW4_NOSHARES, clauseLAW4_RESERVE, clauseLAW4_CONSERVE,
   clauseLAW4_FORFEIT, clauseLAW4_BUYOUT, clauseLAW4_CROSS,
   clauseLAW5_VOICE, clauseLAW5_INIT, clauseLAW5_SEQ, clauseLAW5_CLEAN,
   clauseLAW5_PREC, clauseLAW5_LEASE, clauseLAW5_DISC, clauseLAW5_EPITAPH, clauseLAW5_EFFECT,
   clauseLAW6_SORTITION, clauseLAW6_COUNTERSTAKE, clauseLAW6_APPEALS, clauseLAW6_FINALITY,
   clauseLAW6_FEES, clauseLAW6_POOL, clauseLAW6_BUDGETS, clauseLAW6_INFRA,
   clauseLAW7_RATCHET, clauseLAW7_VALVE, clauseLAW7_RATIFY, clauseLAW7_SCOPE,
   clauseSUB01]

/-- A concrete instantiation used by the decided examples. -/
def P0 : Params :=
  { noticeWindow := 10, bondDeadline := 5, reviewInterval := 30,
    preliminaryFreezeWindow := 3, ordinarySuspensionLimit := 15, damagesPaymentWindow := 10 }
def L0 : Law σ := law P0

abbrev Law3Params := Params
abbrev law3 := law
abbrev defaultParams := P0

end Charter.Law3

namespace Charter
export Law3 (Law3Params law3 defaultParams)
end Charter

