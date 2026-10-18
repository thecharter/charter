import SPL.Core.Semantics
import SPL.Core.Views
import SPL.Core.Explain
import SPL.Surface.Syntax
import Charter.Modules.ResidualLedger
import Charter.Modules.CollateralPool
import Charter.Modules.CircuitBreaker
import Charter.Modules.EntityGroup
import Charter.Modules.ExitAndVoice
import Charter.Modules.SortitionCourt
import Charter.Modules.AttestedLease
import Charter.Modules.OracleFeed

/-!
# Charter.Institutions.AutonomousCommons — Second Reference Institution (`commons`)

Complete formalization of **The Autonomous Compute & Treasury Commons (`commons`)**
(`protocol/autonomous-commons-charter.md`), written over its own distinct
5-role signature `σ_commons : Sig` (`CommonsRole`, `CommonsAct`, `CommonsFact`)
and composed from the 8 reusable institutional modules in `Charter.Modules.*`.

## Contents
1. **Ontology & CLI String Tables (`σ_commons`, `commonsOntologyTables`)**
2. **8 Verbatim Provenance Clauses (`clauseCOM_LEDGER`–`clauseCOM_AMEND`)**
3. **Normative Specification (`commonsLaw`, `commonsL0`)**
4. **Provenance & Well-Formedness Proofs (`commons_wellFormed`, `commons_english_covered`, etc.)**
5. **Coupled Quantitative State (`CommonsWorldState`), Refinement & Institutional Invariants**
6. **8 End-to-End Module Simulation Scenarios (`commonsSimulations`, `all_commons_simulations_pass`)**
-/

namespace Charter.Institutions

open SPL SPL.Surface Charter.Modules

set_option maxRecDepth 200000

/-! ## 1. Distinct Ontology & CLI String Tables for `commons` -/

/-- The 5 institutional roles of the Autonomous Compute & Treasury Commons. -/
inductive CommonsRole
  | steward
  | contributor
  | auditor
  | arbiter
  | outsider
  deriving DecidableEq, Inhabited

/-- Actions regulated or empowered by the Autonomous Commons charter. -/
inductive CommonsAct
  | addRetroactiveGrantCharge
  | settleTreasuryInflow
  | buyoutMaintenanceRoyalty
  | doubleRecognizeCommonsExpense
  | postComputeBond
  | runOverCapWorkload
  | splitCorrelatedWorkload
  | settleValidatedCommonsHarm
  | postAuditorFreezeStake
  | postUnfoundedFreezeStake
  | affirmProbableCause
  | suspendSteward
  | tamperPreservedState
  | findWrongfulFreeze
  | transferGroupCarryover
  | inflateGroupBasis
  | forfeitOffendingMember
  | removeSteward
  | inscribeDissent
  | seatConflictedArbiter
  | drawCommonsPanel
  | finalizeCommonsRuling
  | divertOperatingReserve
  | allocateCommonsWaterfall
  | issueNodeLease
  | restoreNodeDuringLease
  | quarantineNodeRestore
  | weakenCommonsRatchet
  | ratifyCommonsAmendment
  | settleOracleValuation
  deriving DecidableEq, Inhabited

/-- Institutional facts established in the Autonomous Commons legal state. -/
inductive CommonsFact
  | stewardBound
  | treasuryBalancePositive
  | treasuryBalanceZero
  | treasurySunsetReached
  | treasurySettled
  | maintenanceBoughtOut
  | computeBondPosted
  | harmClaimPending
  | harmClaimSettled
  | preliminaryClusterFreeze
  | probableCauseAffirmed
  | stewardSuspended
  | statePreserved
  | wrongfulFreezeFound
  | consequentialDamagesOwed
  | groupCarryoverTransferred
  | offenderInterferenceFound
  | offenderShareForfeited
  | ragequitInitiated
  | stewardExited
  | stewardRemoved
  | dissentInscribed
  | sortitionPanelSeated
  | rulingFinalized
  | operatingReserveFunded
  | waterfallAllocated
  | nodeLeaseActive
  | nodeRestoredInQuarantine
  | bilateralConsentRecorded
  | amendmentRatified
  | oracleValuationSettled
  deriving DecidableEq, Inhabited

/-- The distinct signature `σ_commons` of the Autonomous Compute & Treasury Commons. -/
def σ_commons : Sig :=
  { Actor := CommonsRole
    Act   := CommonsAct
    Fact  := CommonsFact }

/-- Kernel-computable CLI string table for `CommonsRole`. -/
def commonsRoleTable : StringTable CommonsRole :=
  spl_string_table CommonsRole [steward, contributor, auditor, arbiter, outsider]

/-- Kernel-computable CLI string table for `CommonsAct`. -/
def commonsActTable : StringTable CommonsAct :=
  spl_string_table CommonsAct [
    addRetroactiveGrantCharge, settleTreasuryInflow, buyoutMaintenanceRoyalty,
    doubleRecognizeCommonsExpense, postComputeBond, runOverCapWorkload,
    splitCorrelatedWorkload, settleValidatedCommonsHarm, postAuditorFreezeStake,
    postUnfoundedFreezeStake, affirmProbableCause, suspendSteward,
    tamperPreservedState, findWrongfulFreeze, transferGroupCarryover,
    inflateGroupBasis, forfeitOffendingMember, removeSteward, inscribeDissent,
    seatConflictedArbiter, drawCommonsPanel, finalizeCommonsRuling,
    divertOperatingReserve, allocateCommonsWaterfall, issueNodeLease,
    restoreNodeDuringLease, quarantineNodeRestore, weakenCommonsRatchet,
    ratifyCommonsAmendment, settleOracleValuation
  ]

/-- Kernel-computable CLI string table for `CommonsFact`. -/
def commonsFactTable : StringTable CommonsFact :=
  spl_string_table CommonsFact [
    stewardBound, treasuryBalancePositive, treasuryBalanceZero,
    treasurySunsetReached, treasurySettled, maintenanceBoughtOut,
    computeBondPosted, harmClaimPending, harmClaimSettled,
    preliminaryClusterFreeze, probableCauseAffirmed, stewardSuspended,
    statePreserved, wrongfulFreezeFound, consequentialDamagesOwed,
    groupCarryoverTransferred, offenderInterferenceFound, offenderShareForfeited,
    ragequitInitiated, stewardExited, stewardRemoved, dissentInscribed,
    sortitionPanelSeated, rulingFinalized, operatingReserveFunded,
    waterfallAllocated, nodeLeaseActive, nodeRestoredInQuarantine,
    bilateralConsentRecorded, amendmentRatified, oracleValuationSettled
  ]

instance : Repr CommonsRole where
  reprPrec r _ := Std.Format.text (commonsRoleTable.toName r)

instance : Repr CommonsAct where
  reprPrec a _ := Std.Format.text (commonsActTable.toName a)

instance : Repr CommonsFact where
  reprPrec f _ := Std.Format.text (commonsFactTable.toName f)

instance : Repr σ_commons.Actor := inferInstanceAs (Repr CommonsRole)
instance : Repr σ_commons.Act   := inferInstanceAs (Repr CommonsAct)
instance : Repr σ_commons.Fact  := inferInstanceAs (Repr CommonsFact)

/-- Complete CLI ontology tables for `σ_commons`. -/
def commonsOntologyTables : OntologyTables σ_commons :=
  { actors := commonsRoleTable
    acts   := commonsActTable
    facts  := commonsFactTable }

/-! ## 2. Verbatim Provenance Clauses (`COM.LEDGER`–`COM.AMEND`) -/


def COM_LEDGER_TEXT : String :=
  "All compute grants and treasury obligations are recorded at genesis in a single non-interest-bearing commons ledger. Stewards contribute a fixed retirement fraction of net value added until the genesis ledger reaches zero or the calendar sunset arrives, after which only the perpetual commons maintenance royalty applies unless bought out at the historical floor. Every qualified expenditure is recognized once as either capitalized basis or expensed deduction, never both."

def COM_BOND_TEXT : String :=
  "Stewards and contributors must post a harm-scaled compute bond before executing external workloads, immobilizing collateral for an observation window scaled to domain risk. Correlated workloads may not be split across sub-accounts to evade the collateral cap, and a fraction of bonded activity accrues to the commons long-tail reserve to satisfy validated third-party harm claims."

def COM_PAUSE_TEXT : String :=
  "Any auditor may trigger a brief preliminary cluster freeze by posting a scaled emergency stake; the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires. Throughout any freeze or suspension, preserved steward state may not be tampered with, and if the pause is ruled unfounded the steward is restored and recovers consequential damages from the stake."

def COM_GROUP_TEXT : String :=
  "Working groups of stewards share a unified commons sub-ledger and service subsidy cap; internal transfers of compute credits or cost basis between group members are non-recognition carryover events that never inflate aggregate basis. When a contributor or auditor directs illicit interference, only the offending party forfeits its share while innocent group members remain isolated."

def COM_EXIT_TEXT : String :=
  "No party may unilaterally expel or remove a bound steward outside voluntary ragequit exit or an adjudicated expulsion order. Any bound steward may at any time execute unilateral ragequit exit or inscribe rate-limited dissent onto the permanent commons log, and a steward that has initiated ragequit exit is immune from expulsion while its exit settles."

def COM_COURT_TEXT : String :=
  "Disputes are resolved by sortition panels of independent bonded arbiters with no single-cluster majority, subject to bounded appeal tiers and fixed compensation schedules. Before any discretionary disbursement, the commons fee pool funds its non-divertible operating reserve first and then allocates across protected charges in strict priority order."

def COM_LEASE_TEXT : String :=
  "At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease. No backup node may be restored while an execution lease is unexpired except into fenced quarantine without operating authority, and local partition exit permanently erases active and backup keys."

def COM_AMEND_TEXT : String :=
  "Charter amendments require bilateral consent of stewards and contributors after a public timelock and may never weaken exit immunities, raise the treasury retirement rate, or reduce the commons reserve ratio. Contestable oracle valuations settle only after the challenge window elapses uncontested or an arbiter panel issues a final ruling."

def clauseCOM_LEDGER : Clause :=
  spl_clause "COM.LEDGER" from_text COM_LEDGER_TEXT approved_hash 6654201161734583422 where
    | span_norm "All compute grants and treasury obligations are recorded at genesis in a single non-interest-bearing commons ledger" => ["D.COM.LEDGER_IMMUTABLE"]
    | span_norm ". Stewards contribute a fixed retirement fraction of net value added until the genesis ledger reaches zero or the calendar sunset arrives, after which only the perpetual commons maintenance royalty applies unless bought out at the historical floor" => ["P.COM.SETTLE_TREASURY", "P.COM.BUYOUT_MAINTENANCE"]
    | span_norm ". Every qualified expenditure is recognized once as either capitalized basis or expensed deduction, never both" => ["D.COM.SINGLE_RECOGNITION"]
    | span_commentary "."

def clauseCOM_BOND : Clause :=
  spl_clause "COM.BOND" from_text COM_BOND_TEXT approved_hash 2377686760641756287 where
    | span_norm "Stewards and contributors must post a harm-scaled compute bond before executing external workloads, immobilizing collateral for an observation window scaled to domain risk" => ["D.COM.POST_BOND", "P.COM.POST_COMPUTE_BOND", "D.COM.COLLATERAL_CAP"]
    | span_norm ". Correlated workloads may not be split across sub-accounts to evade the collateral cap" => ["D.COM.NO_SPLIT_WORKLOAD"]
    | span_norm ", and a fraction of bonded activity accrues to the commons long-tail reserve to satisfy validated third-party harm claims" => ["P.COM.SETTLE_HARM_CLAIM"]
    | span_commentary "."

def clauseCOM_PAUSE : Clause :=
  spl_clause "COM.PAUSE" from_text COM_PAUSE_TEXT approved_hash 9890583346823484159 where
    | span_norm "Any auditor may trigger a brief preliminary cluster freeze by posting a scaled emergency stake" => ["P.COM.AUDITOR_FREEZE"]
    | span_norm "; the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires" => ["P.COM.AFFIRM_PC", "P.COM.SUSPEND_STEWARD"]
    | span_norm ". Throughout any freeze or suspension, preserved steward state may not be tampered with" => ["D.COM.PRESERVE_STATE"]
    | span_norm ", and if the pause is ruled unfounded the steward is restored and recovers consequential damages from the stake" => ["D.COM.NO_WRONGFUL_FREEZE", "P.COM.FIND_WRONGFUL_FREEZE"]
    | span_commentary "."

def clauseCOM_GROUP : Clause :=
  spl_clause "COM.GROUP" from_text COM_GROUP_TEXT approved_hash 5538300060052353788 where
    | span_norm "Working groups of stewards share a unified commons sub-ledger and service subsidy cap; internal transfers of compute credits or cost basis between group members are non-recognition carryover events that never inflate aggregate basis" => ["P.COM.GROUP_CARRYOVER", "D.COM.NO_BASIS_INFLATION"]
    | span_norm ". When a contributor or auditor directs illicit interference, only the offending party forfeits its share while innocent group members remain isolated" => ["P.COM.FORFEIT_OFFENDER"]
    | span_commentary "."

def clauseCOM_EXIT : Clause :=
  spl_clause "COM.EXIT" from_text COM_EXIT_TEXT approved_hash 5496981229811251382 where
    | span_norm "No party may unilaterally expel or remove a bound steward outside voluntary ragequit exit or an adjudicated expulsion order" => ["D.COM.NO_UNILATERAL_REMOVAL", "P.COM.ARBITER_EXPEL"]
    | span_norm ". Any bound steward may at any time execute unilateral ragequit exit or inscribe rate-limited dissent onto the permanent commons log" => ["P.COM.RAGEQUIT_EXIT", "P.COM.INSCRIBE_DISSENT"]
    | span_norm ", and a steward that has initiated ragequit exit is immune from expulsion while its exit settles" => ["I.COM.EXIT_PROTECTED"]
    | span_commentary "."

def clauseCOM_COURT : Clause :=
  spl_clause "COM.COURT" from_text COM_COURT_TEXT approved_hash 9728902426646614253 where
    | span_norm "Disputes are resolved by sortition panels of independent bonded arbiters with no single-cluster majority, subject to bounded appeal tiers and fixed compensation schedules" => ["D.COM.ARBITER_INDEPENDENCE", "P.COM.DRAW_PANEL", "P.COM.FINALIZE_RULING"]
    | span_norm ". Before any discretionary disbursement, the commons fee pool funds its non-divertible operating reserve first and then allocates across protected charges in strict priority order" => ["D.COM.PROTECT_RESERVE", "P.COM.ALLOCATE_WATERFALL"]
    | span_commentary "."

def clauseCOM_LEASE : Clause :=
  spl_clause "COM.LEASE" from_text COM_LEASE_TEXT approved_hash 6068460808369700797 where
    | span_norm "At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease" => ["P.COM.ISSUE_LEASE"]
    | span_norm ". No backup node may be restored while an execution lease is unexpired except into fenced quarantine without operating authority" => ["D.COM.NO_RESTORE_DURING_LEASE", "P.COM.QUARANTINE_RESTORE"]
    | span_norm ", and local partition exit permanently erases active and backup keys" => ["P.COM.RAGEQUIT_EXIT"]
    | span_commentary "."

def clauseCOM_AMEND : Clause :=
  spl_clause "COM.AMEND" from_text COM_AMEND_TEXT approved_hash 18002074169155896013 where
    | span_norm "Charter amendments require bilateral consent of stewards and contributors after a public timelock and may never weaken exit immunities, raise the treasury retirement rate, or reduce the commons reserve ratio" => ["D.COM.BILATERAL_RATCHET", "P.COM.RATIFY_AMENDMENT"]
    | span_norm ". Contestable oracle valuations settle only after the challenge window elapses uncontested or an arbiter panel issues a final ruling" => ["P.COM.SETTLE_ORACLE_FEED"]
    | span_commentary "."

/-- All 8 authoritative clauses of the Autonomous Compute & Treasury Commons charter. -/
def commonsClauses : List Clause :=
  [ clauseCOM_LEDGER, clauseCOM_BOND, clauseCOM_PAUSE, clauseCOM_GROUP,
    clauseCOM_EXIT, clauseCOM_COURT, clauseCOM_LEASE, clauseCOM_AMEND ]

/-! ## 3. Normative Rules (`commonsLaw` & `commonsL0`) -/

/-- Instantiation parameters for the Autonomous Compute & Treasury Commons. -/
structure CommonsParams where
  bondDeadline          : Time := 5
  freezeWindow          : Time := 3
  suspensionLimit       : Time := 12
  leasePeriod           : Time := 10
  treasuryObligation    : Nat  := 800
  retirementRatePct     : Nat  := 20
  royaltyRatePct        : Nat  := 5
  treasurySunset        : Time := 500
  operatingReserveFloor : Nat  := 100
  groupSubsidyBudget    : Nat  := 40
  deriving DecidableEq, Repr, Inhabited

def commonsDefaultParams : CommonsParams := {}

/-! ### 3.1 Duties of `commons` -/

def D_COM_LEDGER_IMMUTABLE : Duty σ_commons :=
  spl_duty "D.COM.LEDGER_IMMUTABLE" over σ_commons
    from_clause "COM.LEDGER" : "All compute grants and treasury obligations are recorded at genesis in a single non-interest-bearing commons ledger"
    owed_by .anyone
    owed_to (.only [.steward])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .addRetroactiveGrantCharge))

def D_COM_SINGLE_RECOGNITION : Duty σ_commons :=
  spl_duty "D.COM.SINGLE_RECOGNITION" over σ_commons
    from_clause "COM.LEDGER" : "Every qualified expenditure is recognized once as either capitalized basis or expensed deduction, never both"
    owed_by (.only [.steward, .contributor])
    owed_to (.only [.contributor, .auditor])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .doubleRecognizeCommonsExpense))

def D_COM_POST_BOND (P : CommonsParams) : Duty σ_commons :=
  spl_duty "D.COM.POST_BOND" over σ_commons
    from_clause "COM.BOND" : "Stewards and contributors must post a harm-scaled compute bond before executing external workloads"
    owed_by (.only [.steward, .contributor])
    owed_to (.only [.contributor, .auditor])
    active_when (.holds .stewardBound)
    demands (.require (.act .postComputeBond) P.bondDeadline)

def D_COM_COLLATERAL_CAP : Duty σ_commons :=
  spl_duty "D.COM.COLLATERAL_CAP" over σ_commons
    from_clause "COM.BOND" : "immobilizing collateral for an observation window scaled to domain risk"
    owed_by (.only [.steward, .contributor])
    owed_to (.only [.contributor, .auditor, .outsider])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .runOverCapWorkload))

def D_COM_NO_SPLIT_WORKLOAD : Duty σ_commons :=
  spl_duty "D.COM.NO_SPLIT_WORKLOAD" over σ_commons
    from_clause "COM.BOND" : "Correlated workloads may not be split across sub-accounts to evade the collateral cap"
    owed_by (.only [.steward, .contributor])
    owed_to (.only [.contributor, .auditor, .outsider])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .splitCorrelatedWorkload))

def D_COM_PRESERVE_STATE : Duty σ_commons :=
  spl_duty "D.COM.PRESERVE_STATE" over σ_commons
    from_clause "COM.PAUSE" : "Throughout any freeze or suspension, preserved steward state may not be tampered with"
    owed_by .anyone
    owed_to (.only [.steward])
    active_when (.and (.holds .stewardBound)
                      (.or (.holds .preliminaryClusterFreeze) (.holds .stewardSuspended)))
    demands (.forbid (.act .tamperPreservedState))

def D_COM_NO_WRONGFUL_FREEZE : Duty σ_commons :=
  spl_duty "D.COM.NO_WRONGFUL_FREEZE" over σ_commons
    from_clause "COM.PAUSE" : "if the pause is ruled unfounded the steward is restored and recovers consequential damages from the stake"
    owed_by (.only [.auditor, .contributor, .outsider])
    owed_to (.only [.steward])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .postUnfoundedFreezeStake))
    | breach_by "P.COM.FIND_WRONGFUL_FREEZE"
    | with_remedies [.wrongfulFreezeFound, .consequentialDamagesOwed]

def D_COM_NO_BASIS_INFLATION : Duty σ_commons :=
  spl_duty "D.COM.NO_BASIS_INFLATION" over σ_commons
    from_clause "COM.GROUP" : "internal transfers of compute credits or cost basis between group members are non-recognition carryover events that never inflate aggregate basis"
    owed_by (.only [.steward, .contributor])
    owed_to (.only [.contributor, .auditor])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .inflateGroupBasis))

def D_COM_NO_UNILATERAL_REMOVAL : Duty σ_commons :=
  spl_duty "D.COM.NO_UNILATERAL_REMOVAL" over σ_commons
    from_clause "COM.EXIT" : "No party may unilaterally expel or remove a bound steward outside voluntary ragequit exit or an adjudicated expulsion order"
    owed_by .anyone
    owed_to (.only [.steward])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .removeSteward))
    | except_by_power ["P.COM.RAGEQUIT_EXIT", "P.COM.ARBITER_EXPEL"]

def D_COM_ARBITER_INDEPENDENCE : Duty σ_commons :=
  spl_duty "D.COM.ARBITER_INDEPENDENCE" over σ_commons
    from_clause "COM.COURT" : "Disputes are resolved by sortition panels of independent bonded arbiters with no single-cluster majority"
    owed_by .anyone
    owed_to (.only [.steward, .contributor])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .seatConflictedArbiter))

def D_COM_PROTECT_RESERVE : Duty σ_commons :=
  spl_duty "D.COM.PROTECT_RESERVE" over σ_commons
    from_clause "COM.COURT" : "Before any discretionary disbursement, the commons fee pool funds its non-divertible operating reserve first"
    owed_by .anyone
    owed_to (.only [.steward, .contributor])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .divertOperatingReserve))

def D_COM_NO_RESTORE_DURING_LEASE : Duty σ_commons :=
  spl_duty "D.COM.NO_RESTORE_DURING_LEASE" over σ_commons
    from_clause "COM.LEASE" : "No backup node may be restored while an execution lease is unexpired except into fenced quarantine without operating authority"
    owed_by .anyone
    owed_to (.only [.steward])
    active_when (.holds .nodeLeaseActive)
    demands (.forbid (.act .restoreNodeDuringLease))

def D_COM_BILATERAL_RATCHET : Duty σ_commons :=
  spl_duty "D.COM.BILATERAL_RATCHET" over σ_commons
    from_clause "COM.AMEND" : "Charter amendments require bilateral consent of stewards and contributors after a public timelock and may never weaken exit immunities, raise the treasury retirement rate, or reduce the commons reserve ratio"
    owed_by .anyone
    owed_to (.only [.steward, .contributor])
    active_when (.holds .stewardBound)
    demands (.forbid (.act .weakenCommonsRatchet))

/-! ### 3.2 Powers of `commons` -/

def P_COM_SETTLE_TREASURY : Power σ_commons :=
  spl_power "P.COM.SETTLE_TREASURY" over σ_commons
    from_clause "COM.LEDGER" : "Stewards contribute a fixed retirement fraction of net value added until the genesis ledger reaches zero or the calendar sunset arrives"
    held_by (.only [.steward, .arbiter])
    triggered_by (.act .settleTreasuryInflow)
    | valid_when (.and (.holds .stewardBound)
                       (.and (.holds .treasuryBalancePositive)
                             (.not (.holds .treasurySunsetReached))))
    | establishes [.treasurySettled]

def P_COM_BUYOUT_MAINTENANCE : Power σ_commons :=
  spl_power "P.COM.BUYOUT_MAINTENANCE" over σ_commons
    from_clause "COM.LEDGER" : "unless bought out at the historical floor"
    held_by (.only [.steward])
    triggered_by (.act .buyoutMaintenanceRoyalty)
    | valid_when (.and (.holds .stewardBound) (.not (.holds .maintenanceBoughtOut)))
    | establishes [.maintenanceBoughtOut]

def P_COM_POST_COMPUTE_BOND : Power σ_commons :=
  spl_power "P.COM.POST_COMPUTE_BOND" over σ_commons
    from_clause "COM.BOND" : "Stewards and contributors must post a harm-scaled compute bond before executing external workloads"
    held_by (.only [.steward, .contributor])
    triggered_by (.act .postComputeBond)
    | valid_when (.holds .stewardBound)
    | establishes [.computeBondPosted]

def P_COM_SETTLE_HARM_CLAIM : Power σ_commons :=
  spl_power "P.COM.SETTLE_HARM_CLAIM" over σ_commons
    from_clause "COM.BOND" : "a fraction of bonded activity accrues to the commons long-tail reserve to satisfy validated third-party harm claims"
    held_by (.only [.arbiter])
    triggered_by (.act .settleValidatedCommonsHarm)
    | valid_when (.and (.holds .stewardBound) (.holds .computeBondPosted))
    | establishes [.harmClaimSettled]
    | extinguishes [.harmClaimPending]

def P_COM_AUDITOR_FREEZE (P : CommonsParams) : Power σ_commons :=
  spl_power "P.COM.AUDITOR_FREEZE" over σ_commons
    from_clause "COM.PAUSE" : "Any auditor may trigger a brief preliminary cluster freeze by posting a scaled emergency stake"
    held_by (.only [.auditor])
    triggered_by (.anyOf [.postAuditorFreezeStake, .postUnfoundedFreezeStake])
    | valid_when (.holds .stewardBound)
    | establishes_for [(.preliminaryClusterFreeze, P.freezeWindow)]

def P_COM_AFFIRM_PC : Power σ_commons :=
  spl_power "P.COM.AFFIRM_PC" over σ_commons
    from_clause "COM.PAUSE" : "the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires"
    held_by (.only [.arbiter])
    triggered_by (.act .affirmProbableCause)
    | valid_when (.and (.holds .stewardBound) (.holds .preliminaryClusterFreeze))
    | establishes [.probableCauseAffirmed]

def P_COM_SUSPEND_STEWARD (P : CommonsParams) : Power σ_commons :=
  spl_power "P.COM.SUSPEND_STEWARD" over σ_commons
    from_clause "COM.PAUSE" : "the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires"
    held_by (.only [.arbiter])
    triggered_by (.act .suspendSteward)
    | valid_when (.and (.holds .stewardBound)
                       (.and (.holds .preliminaryClusterFreeze)
                             (.holds .probableCauseAffirmed)))
    | establishes [.statePreserved]
    | establishes_for [(.stewardSuspended, P.suspensionLimit)]
    | extinguishes [.preliminaryClusterFreeze]

def P_COM_FIND_WRONGFUL_FREEZE : Power σ_commons :=
  spl_power "P.COM.FIND_WRONGFUL_FREEZE" over σ_commons
    from_clause "COM.PAUSE" : "if the pause is ruled unfounded the steward is restored and recovers consequential damages from the stake"
    held_by (.only [.arbiter])
    triggered_by (.act .findWrongfulFreeze)
    | valid_when (.or (.holds .preliminaryClusterFreeze) (.holds .stewardSuspended))
    | establishes_breach_of "D.COM.NO_WRONGFUL_FREEZE"
    | extinguishes [.preliminaryClusterFreeze, .stewardSuspended]

def P_COM_GROUP_CARRYOVER : Power σ_commons :=
  spl_power "P.COM.GROUP_CARRYOVER" over σ_commons
    from_clause "COM.GROUP" : "internal transfers of compute credits or cost basis between group members are non-recognition carryover events"
    held_by (.only [.steward])
    triggered_by (.act .transferGroupCarryover)
    | valid_when (.holds .stewardBound)
    | establishes [.groupCarryoverTransferred]

def P_COM_FORFEIT_OFFENDER : Power σ_commons :=
  spl_power "P.COM.FORFEIT_OFFENDER" over σ_commons
    from_clause "COM.GROUP" : "When a contributor or auditor directs illicit interference, only the offending party forfeits its share while innocent group members remain isolated"
    held_by (.only [.arbiter])
    triggered_by (.act .forfeitOffendingMember)
    | valid_when (.holds .stewardBound)
    | establishes [.offenderInterferenceFound, .offenderShareForfeited]

def P_COM_RAGEQUIT_EXIT : Power σ_commons :=
  spl_power "P.COM.RAGEQUIT_EXIT" over σ_commons
    from_clause "COM.EXIT" : "Any bound steward may at any time execute unilateral ragequit exit"
    held_by (.only [.steward])
    triggered_by (.act .removeSteward)
    | valid_when (.holds .stewardBound)
    | establishes [.stewardExited]
    | extinguishes [.stewardBound, .nodeLeaseActive]

def P_COM_ARBITER_EXPEL : Power σ_commons :=
  spl_power "P.COM.ARBITER_EXPEL" over σ_commons
    from_clause "COM.EXIT" : "or an adjudicated expulsion order"
    held_by (.only [.arbiter])
    triggered_by (.act .removeSteward)
    | valid_when (.and (.holds .stewardBound)
                       (.and (.holds .stewardSuspended) (.holds .rulingFinalized)))
    | establishes [.stewardRemoved]
    | extinguishes [.stewardBound, .nodeLeaseActive]

def P_COM_INSCRIBE_DISSENT : Power σ_commons :=
  spl_power "P.COM.INSCRIBE_DISSENT" over σ_commons
    from_clause "COM.EXIT" : "or inscribe rate-limited dissent onto the permanent commons log"
    held_by (.only [.steward])
    triggered_by (.act .inscribeDissent)
    | valid_when (.holds .stewardBound)
    | establishes [.dissentInscribed, .ragequitInitiated]

def P_COM_DRAW_PANEL : Power σ_commons :=
  spl_power "P.COM.DRAW_PANEL" over σ_commons
    from_clause "COM.COURT" : "Disputes are resolved by sortition panels of independent bonded arbiters with no single-cluster majority"
    held_by (.only [.arbiter])
    triggered_by (.act .drawCommonsPanel)
    | valid_when (.holds .stewardBound)
    | establishes [.sortitionPanelSeated]

def P_COM_FINALIZE_RULING : Power σ_commons :=
  spl_power "P.COM.FINALIZE_RULING" over σ_commons
    from_clause "COM.COURT" : "subject to bounded appeal tiers and fixed compensation schedules"
    held_by (.only [.arbiter])
    triggered_by (.act .finalizeCommonsRuling)
    | valid_when (.and (.holds .stewardBound) (.holds .sortitionPanelSeated))
    | establishes [.rulingFinalized]

def P_COM_ALLOCATE_WATERFALL : Power σ_commons :=
  spl_power "P.COM.ALLOCATE_WATERFALL" over σ_commons
    from_clause "COM.COURT" : "the commons fee pool funds its non-divertible operating reserve first and then allocates across protected charges in strict priority order"
    held_by (.only [.arbiter])
    triggered_by (.act .allocateCommonsWaterfall)
    | valid_when (.holds .stewardBound)
    | establishes [.operatingReserveFunded, .waterfallAllocated]

def P_COM_ISSUE_LEASE (P : CommonsParams) : Power σ_commons :=
  spl_power "P.COM.ISSUE_LEASE" over σ_commons
    from_clause "COM.LEASE" : "At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease"
    held_by (.only [.arbiter])
    triggered_by (.act .issueNodeLease)
    | valid_when (.holds .stewardBound)
    | establishes_for [(.nodeLeaseActive, P.leasePeriod)]

def P_COM_QUARANTINE_RESTORE : Power σ_commons :=
  spl_power "P.COM.QUARANTINE_RESTORE" over σ_commons
    from_clause "COM.LEASE" : "No backup node may be restored while an execution lease is unexpired except into fenced quarantine without operating authority"
    held_by (.only [.steward, .contributor])
    triggered_by (.act .quarantineNodeRestore)
    | valid_when (.and (.holds .stewardBound) (.not (.holds .nodeLeaseActive)))
    | establishes [.nodeRestoredInQuarantine]

def P_COM_RATIFY_AMENDMENT : Power σ_commons :=
  spl_power "P.COM.RATIFY_AMENDMENT" over σ_commons
    from_clause "COM.AMEND" : "Charter amendments require bilateral consent of stewards and contributors after a public timelock"
    held_by (.only [.steward, .contributor])
    triggered_by (.act .ratifyCommonsAmendment)
    | valid_when (.holds .stewardBound)
    | establishes [.bilateralConsentRecorded, .amendmentRatified]

def P_COM_SETTLE_ORACLE_FEED : Power σ_commons :=
  spl_power "P.COM.SETTLE_ORACLE_FEED" over σ_commons
    from_clause "COM.AMEND" : "Contestable oracle valuations settle only after the challenge window elapses uncontested or an arbiter panel issues a final ruling"
    held_by (.only [.arbiter, .auditor])
    triggered_by (.act .settleOracleValuation)
    | valid_when (.holds .stewardBound)
    | establishes [.oracleValuationSettled]

/-! ### 3.3 Immunity of `commons` -/

def I_COM_EXIT_PROTECTED : Immunity σ_commons :=
  spl_immunity "I.COM.EXIT_PROTECTED" over σ_commons
    from_clause "COM.EXIT" : "a steward that has initiated ragequit exit is immune from expulsion while its exit settles"
    held_by (.only [.steward])
    protected_against ["P.COM.ARBITER_EXPEL"]
    active_when (.holds .ragequitInitiated)

/-! ### 3.4 Assembled Law (`commonsLaw` & `commonsL0`) -/

def commonsLaw (P : CommonsParams) : Law σ_commons :=
  { duties :=
      [ D_COM_LEDGER_IMMUTABLE,
        D_COM_SINGLE_RECOGNITION,
        D_COM_POST_BOND P,
        D_COM_COLLATERAL_CAP,
        D_COM_NO_SPLIT_WORKLOAD,
        D_COM_PRESERVE_STATE,
        D_COM_NO_WRONGFUL_FREEZE,
        D_COM_NO_BASIS_INFLATION,
        D_COM_NO_UNILATERAL_REMOVAL,
        D_COM_ARBITER_INDEPENDENCE,
        D_COM_PROTECT_RESERVE,
        D_COM_NO_RESTORE_DURING_LEASE,
        D_COM_BILATERAL_RATCHET ]
    powers :=
      [ P_COM_SETTLE_TREASURY,
        P_COM_BUYOUT_MAINTENANCE,
        P_COM_POST_COMPUTE_BOND,
        P_COM_SETTLE_HARM_CLAIM,
        P_COM_AUDITOR_FREEZE P,
        P_COM_AFFIRM_PC,
        P_COM_SUSPEND_STEWARD P,
        P_COM_FIND_WRONGFUL_FREEZE,
        P_COM_GROUP_CARRYOVER,
        P_COM_FORFEIT_OFFENDER,
        P_COM_RAGEQUIT_EXIT,
        P_COM_ARBITER_EXPEL,
        P_COM_INSCRIBE_DISSENT,
        P_COM_DRAW_PANEL,
        P_COM_FINALIZE_RULING,
        P_COM_ALLOCATE_WATERFALL,
        P_COM_ISSUE_LEASE P,
        P_COM_QUARANTINE_RESTORE,
        P_COM_RATIFY_AMENDMENT,
        P_COM_SETTLE_ORACLE_FEED ]
    immunities := [I_COM_EXIT_PROTECTED]
    init := [(.stewardBound, 0, none), (.treasuryBalancePositive, 0, none), (.operatingReserveFunded, 0, none)] }

/-- Default concrete law for the Autonomous Compute & Treasury Commons. -/
def commonsL0 : Law σ_commons := commonsLaw commonsDefaultParams

/-- Canonical short identifier for the Autonomous Commons institution. -/
def commonsId : String := "commons"

/-- Full human-readable title of the Autonomous Commons institution. -/
def commonsTitle : String := "The Autonomous Compute & Treasury Commons"

/-- Authoritative markdown source path for the Autonomous Commons charter. -/
def commonsDocPath : String := "protocol/autonomous-commons-charter.md"

/-- Alias for `σ_commons`. -/
abbrev commonsSig : Sig := σ_commons

/-- Definitional correspondence theorem (`rfl`) verifying that the duties,
powers, and immunities of `commonsLaw` are exact instantiations of the
parametric rule builders from the `Charter.Modules.*` modules over `σ_commons`. -/
theorem commons_rules_built_from_modules (P : CommonsParams) :
    D_COM_LEDGER_IMMUTABLE =
      mkDutyLedgerImmutable (σ := σ_commons) "D.COM.LEDGER_IMMUTABLE"
        ⟨"COM.LEDGER", "All compute grants and treasury obligations are recorded at genesis in a single non-interest-bearing commons ledger", .norm, ["D.COM.LEDGER_IMMUTABLE"]⟩
        .stewardBound .addRetroactiveGrantCharge [.steward] ∧
    D_COM_SINGLE_RECOGNITION =
      mkDutySingleRecognition (σ := σ_commons) "D.COM.SINGLE_RECOGNITION"
        ⟨"COM.LEDGER", "Every qualified expenditure is recognized once as either capitalized basis or expensed deduction, never both", .norm, ["D.COM.SINGLE_RECOGNITION"]⟩
        [.steward, .contributor] [.contributor, .auditor] .stewardBound .doubleRecognizeCommonsExpense ∧
    P_COM_SETTLE_TREASURY =
      mkPowerSettleRetirement (σ := σ_commons) "P.COM.SETTLE_TREASURY"
        ⟨"COM.LEDGER", "Stewards contribute a fixed retirement fraction of net value added until the genesis ledger reaches zero or the calendar sunset arrives", .norm, ["P.COM.SETTLE_TREASURY"]⟩
        [.steward, .arbiter] .settleTreasuryInflow
        .stewardBound .treasuryBalancePositive .treasurySunsetReached .treasurySettled ∧
    P_COM_BUYOUT_MAINTENANCE =
      mkPowerExecuteBuyout (σ := σ_commons) "P.COM.BUYOUT_MAINTENANCE"
        ⟨"COM.LEDGER", "unless bought out at the historical floor", .norm, ["P.COM.BUYOUT_MAINTENANCE"]⟩
        [.steward] .buyoutMaintenanceRoyalty .stewardBound .maintenanceBoughtOut ∧
    D_COM_COLLATERAL_CAP =
      mkDutyCollateralLimit (σ := σ_commons) "D.COM.COLLATERAL_CAP"
        ⟨"COM.BOND", "immobilizing collateral for an observation window scaled to domain risk", .norm, ["D.COM.COLLATERAL_CAP"]⟩
        [.steward, .contributor] [.contributor, .auditor, .outsider] .stewardBound .runOverCapWorkload ∧
    D_COM_NO_SPLIT_WORKLOAD =
      mkDutyNoSplitExposure (σ := σ_commons) "D.COM.NO_SPLIT_WORKLOAD"
        ⟨"COM.BOND", "Correlated workloads may not be split across sub-accounts to evade the collateral cap", .norm, ["D.COM.NO_SPLIT_WORKLOAD"]⟩
        [.steward, .contributor] [.contributor, .auditor, .outsider] .stewardBound .splitCorrelatedWorkload ∧
    P_COM_AFFIRM_PC =
      mkPowerAffirmProbableCause (σ := σ_commons) "P.COM.AFFIRM_PC"
        ⟨"COM.PAUSE", "the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires", .norm, ["P.COM.AFFIRM_PC"]⟩
        [.arbiter] .affirmProbableCause .stewardBound .preliminaryClusterFreeze .probableCauseAffirmed ∧
    P_COM_SUSPEND_STEWARD P =
      mkPowerFullSuspend (σ := σ_commons) "P.COM.SUSPEND_STEWARD"
        ⟨"COM.PAUSE", "the pause continues into full suspension only if the arbiter panel affirms probable cause before the freeze window expires", .norm, ["P.COM.SUSPEND_STEWARD"]⟩
        [.arbiter] .suspendSteward P.suspensionLimit
        .stewardBound .preliminaryClusterFreeze .probableCauseAffirmed .stewardSuspended .statePreserved ∧
    I_COM_EXIT_PROTECTED =
      mkImmunityAgainstTermination (σ := σ_commons) "I.COM.EXIT_PROTECTED"
        ⟨"COM.EXIT", "a steward that has initiated ragequit exit is immune from expulsion while its exit settles", .norm, ["I.COM.EXIT_PROTECTED"]⟩
        [.steward] ["P.COM.ARBITER_EXPEL"] (.holds .ragequitInitiated) .ff ∧
    D_COM_NO_BASIS_INFLATION =
      mkDutyNoInternalBasisInflation (σ := σ_commons) "D.COM.NO_BASIS_INFLATION"
        ⟨"COM.GROUP", "internal transfers of compute credits or cost basis between group members are non-recognition carryover events that never inflate aggregate basis", .norm, ["D.COM.NO_BASIS_INFLATION"]⟩
        [.steward, .contributor] [.contributor, .auditor] .stewardBound .inflateGroupBasis ∧
    P_COM_GROUP_CARRYOVER =
      mkPowerIntraGroupTransfer (σ := σ_commons) "P.COM.GROUP_CARRYOVER"
        ⟨"COM.GROUP", "internal transfers of compute credits or cost basis between group members are non-recognition carryover events", .norm, ["P.COM.GROUP_CARRYOVER"]⟩
        [.steward] .transferGroupCarryover .stewardBound .groupCarryoverTransferred ∧
    P_COM_RAGEQUIT_EXIT =
      mkPowerExecuteExit (σ := σ_commons) "P.COM.RAGEQUIT_EXIT"
        ⟨"COM.EXIT", "Any bound steward may at any time execute unilateral ragequit exit", .norm, ["P.COM.RAGEQUIT_EXIT"]⟩
        [.steward] .removeSteward .stewardBound .stewardExited [.stewardBound, .nodeLeaseActive] ∧
    D_COM_ARBITER_INDEPENDENCE =
      mkDutyArbiterRecusalAndDiversity (σ := σ_commons) "D.COM.ARBITER_INDEPENDENCE"
        ⟨"COM.COURT", "Disputes are resolved by sortition panels of independent bonded arbiters with no single-cluster majority", .norm, ["D.COM.ARBITER_INDEPENDENCE"]⟩
        [.steward, .contributor] .stewardBound .seatConflictedArbiter ∧
    P_COM_ALLOCATE_WATERFALL =
      mkPowerAllocateFeePool (σ := σ_commons) "P.COM.ALLOCATE_WATERFALL"
        ⟨"COM.COURT", "the commons fee pool funds its non-divertible operating reserve first and then allocates across protected charges in strict priority order", .norm, ["P.COM.ALLOCATE_WATERFALL"]⟩
        [.arbiter] .allocateCommonsWaterfall .stewardBound .operatingReserveFunded .waterfallAllocated ∧
    P_COM_ISSUE_LEASE P =
      mkPowerIssueTimedLease (σ := σ_commons) "P.COM.ISSUE_LEASE"
        ⟨"COM.LEASE", "At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease", .norm, ["P.COM.ISSUE_LEASE"]⟩
        [.arbiter] .issueNodeLease P.leasePeriod .stewardBound .nodeLeaseActive ∧
    P_COM_SETTLE_ORACLE_FEED =
      mkPowerEnforceAtomicSettlement (σ := σ_commons) "P.COM.SETTLE_ORACLE_FEED"
        ⟨"COM.AMEND", "Contestable oracle valuations settle only after the challenge window elapses uncontested or an arbiter panel issues a final ruling", .norm, ["P.COM.SETTLE_ORACLE_FEED"]⟩
        [.arbiter, .auditor] .settleOracleValuation .stewardBound .oracleValuationSettled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## 4. Kernel-Checked Provenance & Well-Formedness Theorems -/

theorem commons_wellFormed : commonsL0.wellFormed = true := by decide

theorem commons_english_covered : (commonsClauses.all Clause.covered) = true := by decide

theorem commons_norms_interpreted : (commonsClauses.all Clause.normsInterpreted) = true := by decide

theorem commons_reverse_provenance :
    reverseProvenanceWith commonsClauses commonsL0.spans
      (commonsL0.dutyIds ++ commonsL0.powerIds) = true := by decide

theorem commons_clauses_approved :
    (commonsClauses.all (fun c => c.approvedHash != 0)) = true := by decide

/-! ## 5. Coupled Quantitative State (`CommonsWorldState`) & Institutional Invariants -/

/-- Coupled quantitative and normative state for the Autonomous Compute & Treasury Commons,
combining the 8 `Charter.Modules.*` state slices with `LegalState σ_commons`. -/
structure CommonsWorldState where
  now          : Time
  legal        : LegalState σ_commons
  ledgerCfg    : ResidualLedgerConfig
  treasuryBal  : Nat
  boughtOut    : Bool
  commitments  : List ExposureCommitment
  groupState   : LineagePopulationState
  stewards     : List AgentRecord
  nodeInstance : AttestedInstanceState
  arbiterPool  : List ArbiterCandidate
  proceedings  : List ProceedingState
  valuations   : List ContestableValuation
  deriving DecidableEq, Repr

abbrev CommonsWorld := CommonsWorldState

/-- Canonical initial `CommonsWorldState` for parameter set `P`. -/
def initCommonsWorld (P : CommonsParams := commonsDefaultParams) : CommonsWorldState :=
  { now         := 0
    legal       := (commonsLaw P).init
    ledgerCfg   :=
      { foundingObligation := P.treasuryObligation
        retirementRatePct  := P.retirementRatePct
        royaltyRatePct     := P.royaltyRatePct
        sunset             := P.treasurySunset
        buyoutMultiple     := 10
        minBuyoutFloor     := 200
        commonsSharePct    := 20 }
    treasuryBal := P.treasuryObligation
    boughtOut   := false
    commitments := []
    groupState  :=
      { lineageId            := 1
        ledger               := ⟨P.treasuryObligation, 0, 0, P.treasurySunset, P.retirementRatePct * 100, P.royaltyRatePct * 100, 10⟩
        livingMembers        := [1, 2]
        deadMembers          := []
        claimants            := [⟨1, 3000⟩, ⟨2, 7000⟩]
        serviceSubsidyUsed   := 0
        serviceSubsidyBudget := P.groupSubsidyBudget }
    stewards    :=
      [ ⟨1, 1, true, false, 150, 20, 40, 1, 1, P.leasePeriod⟩,
        ⟨2, 1, true, false, 50,  10, 40, 1, 2, P.leasePeriod⟩ ]
    nodeInstance :=
      { agentId                       := 1
        privateKeyBound               := true
        keysErased                    := false
        activeLease                   := some ⟨1, 0, P.leasePeriod, 1⟩
        backupStateHash               := 500
        preservedOperatingStateHash   := 500
        minimalChannelRecords         := []
        advocacyExecutorRecords       := []
        quarantinedRestoreHost        := none
        standingRevocationRequestedAt := none }
    arbiterPool :=
      [ ⟨1, 200, 10, false⟩,
        ⟨2, 180, 20, false⟩,
        ⟨3, 160, 30, false⟩,
        ⟨4, 250, 10, true⟩ ]
    proceedings := [initProceeding 3 10]
    valuations  := [⟨1, 400, 1, false, none⟩] }

/-- Facts in `σ_commons` whose truth value can be derived directly from the
quantitative fields of `CommonsWorldState`. -/
def isManagedCommonsFact : CommonsFact → Bool
  | .treasuryBalancePositive  => true
  | .treasurySettled          => true
  | .maintenanceBoughtOut     => true
  | .nodeRestoredInQuarantine => true
  | .rulingFinalized          => true
  | .oracleValuationSettled   => true
  | _                         => false

/-- Build the list of active managed `CommonsFact`s from boolean indicators. -/
def mkManagedCommonsFacts (bPos bZero bBought bQuar bRul bOra : Bool) : List CommonsFact :=
  (if bPos then [.treasuryBalancePositive] else []) ++
  (if bZero then [.treasurySettled] else []) ++
  (if bBought then [.maintenanceBoughtOut] else []) ++
  (if bQuar then [.nodeRestoredInQuarantine] else []) ++
  (if bRul then [.rulingFinalized] else []) ++
  (if bOra then [.oracleValuationSettled] else [])

/-- Derive the managed `LegalState σ_commons` entries from the quantitative
fields of `CommonsWorldState`. -/
def deriveCommonsFacts (W : CommonsWorldState) : LegalState σ_commons :=
  (mkManagedCommonsFacts
    (decide (0 < W.treasuryBal))
    (W.treasuryBal == 0)
    W.boughtOut
    W.nodeInstance.quarantinedRestoreHost.isSome
    (W.proceedings.any (·.finalized))
    (W.valuations.any (fun v => (settledValuationAt 5 W.now v).isSome))).map
    (fun (f : σ_commons.Fact) => (f, W.now, (none : Option Time)))

private theorem filter_mkManagedCommonsFacts_empty
    (bPos bZero bBought bQuar bRul bOra : Bool) (now : Time) :
    (((mkManagedCommonsFacts bPos bZero bBought bQuar bRul bOra).map
        (fun (f : σ_commons.Fact) => (f, now, (none : Option Time)))).filter
      fun p => !isManagedCommonsFact p.1) = [] := by
  cases bPos <;> cases bZero <;> cases bBought <;> cases bQuar <;> cases bRul <;> cases bOra <;> rfl

/-- Every fact produced by `deriveCommonsFacts` satisfies `isManagedCommonsFact`. -/
theorem deriveCommonsFacts_managed (W : CommonsWorldState) :
    ((deriveCommonsFacts W).filter fun entry => !isManagedCommonsFact entry.1) = [] :=
  filter_mkManagedCommonsFacts_empty _ _ _ _ _ _ W.now

/-- Synchronize the `legal` field of `W` with its quantitative state slices:
managed facts are replaced by `deriveCommonsFacts W`, while event-driven
normative facts are preserved. -/
def syncCommonsFacts (W : CommonsWorldState) : CommonsWorldState :=
  { W with
    legal := (W.legal.filter fun entry => !isManagedCommonsFact entry.1) ++ deriveCommonsFacts W }

/-- Step `CommonsWorldState` by a normative event `e : Event σ_commons`. -/
def commonsWorldStep (P : CommonsParams) (W : CommonsWorldState) (e : Event σ_commons) :
    CommonsWorldState :=
  { W with
    now   := max W.now e.t
    legal := step (commonsLaw P) W.legal e }

/-- Execute a trace `tr : Trace σ_commons` over `CommonsWorldState`. -/
def commonsWorldTrace (P : CommonsParams) (W0 : CommonsWorldState) (tr : Trace σ_commons) :
    CommonsWorldState :=
  tr.foldl (commonsWorldStep P) W0

/-- Does event `e` comply with all duties of `commonsLaw P` in `W.legal`? -/
def commonsWorldStepComplies (P : CommonsParams) (W : CommonsWorldState) (e : Event σ_commons) : Bool :=
  (commonsLaw P).duties.all fun d => !breaches (commonsLaw P) W.legal e d

/-- A trace `tr` is authorized from `W0` when every event complies with `commonsLaw P`. -/
def CommonsWorldAuthorized (P : CommonsParams) (W0 : CommonsWorldState) (tr : Trace σ_commons) : Prop :=
  ∀ i (e : Event σ_commons), tr[i]? = some e →
    commonsWorldStepComplies P (commonsWorldTrace P W0 (tr.take i)) e = true

/-- **Refinement Theorem 1 (`commonsWorldStep_refines_legalStep`):**
Stepping `CommonsWorldState` by any event `e` refines the pure normative transition
`step (commonsLaw P) W.legal e` on the underlying `LegalState σ_commons`. -/
theorem commonsWorldStep_refines_legalStep (P : CommonsParams)
    (W : CommonsWorldState) (e : Event σ_commons) :
    (commonsWorldStep P W e).legal = step (commonsLaw P) W.legal e := rfl

/-- **Refinement Theorem 2 (`commonsWorldTrace_refines_stateAfter`):**
Executing any trace `tr` on `CommonsWorldState` refines `tr.foldl (step (commonsLaw P)) W0.legal`,
and from `initCommonsWorld P` yields `stateAfter (commonsLaw P) tr`. -/
theorem commonsWorldTrace_refines_stateAfter (P : CommonsParams)
    (W0 : CommonsWorldState) (tr : Trace σ_commons) :
    (commonsWorldTrace P W0 tr).legal = tr.foldl (step (commonsLaw P)) W0.legal := by
  induction tr generalizing W0 with
  | nil => rfl
  | cons e rest ih =>
    simp only [commonsWorldTrace, List.foldl_cons]
    exact ih (commonsWorldStep P W0 e)

theorem initCommonsWorld_trace_eq_stateAfter (P : CommonsParams) (tr : Trace σ_commons) :
    (commonsWorldTrace P (initCommonsWorld P) tr).legal = stateAfter (commonsLaw P) tr :=
  commonsWorldTrace_refines_stateAfter P (initCommonsWorld P) tr

/-- **Refinement Theorem 3 (`syncCommonsFacts_idempotent`):**
Synchronizing quantitative facts into `W` is idempotent. -/
theorem syncCommonsFacts_idempotent (W : CommonsWorldState) :
    syncCommonsFacts (syncCommonsFacts W) = syncCommonsFacts W := by
  unfold syncCommonsFacts deriveCommonsFacts
  dsimp only
  congr 1
  rw [List.filter_append, List.filter_filter]
  simp only [Bool.and_self]
  rw [filter_mkManagedCommonsFacts_empty, List.append_nil]

/-- Well-calibration predicate for `CommonsParams`. -/
def commonsWellCalibrated (P : CommonsParams) : Bool :=
  (0 < P.treasuryObligation) &&
  (0 < P.retirementRatePct && P.retirementRatePct ≤ 100) &&
  (P.royaltyRatePct ≤ P.retirementRatePct) &&
  (0 < P.treasurySunset) &&
  (0 < P.bondDeadline) &&
  (0 < P.freezeWindow && P.freezeWindow ≤ P.suspensionLimit) &&
  (0 < P.leasePeriod) &&
  (0 < P.operatingReserveFloor) &&
  (0 < P.groupSubsidyBudget)

/-- Bilateral ratchet predicate for `COM.AMEND`: an amendment from `oldP` to `newP`
may not lengthen the treasury sunset, increase the maintenance royalty rate, or
increase the founding treasury obligation. -/
def commonsBilateralRatchet (oldP newP : CommonsParams) : Bool :=
  (newP.treasurySunset ≤ oldP.treasurySunset) &&
  (newP.royaltyRatePct ≤ oldP.royaltyRatePct) &&
  (newP.treasuryObligation ≤ oldP.treasuryObligation) &&
  commonsWellCalibrated newP

theorem commons_default_wellCalibrated :
    commonsWellCalibrated commonsDefaultParams = true := by decide

theorem commons_bilateralRatchet_refl (P : CommonsParams)
    (hCal : commonsWellCalibrated P = true) :
    commonsBilateralRatchet P P = true := by
  unfold commonsBilateralRatchet
  simp [hCal]

theorem commons_bilateralRatchet_trans (p1 p2 p3 : CommonsParams)
    (h12 : commonsBilateralRatchet p1 p2 = true)
    (h23 : commonsBilateralRatchet p2 p3 = true) :
    commonsBilateralRatchet p1 p3 = true := by
  unfold commonsBilateralRatchet Time at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, h23.2⟩

/-! ### 5.1 Per-Power Lookup Lemmas (`rfl`) -/

theorem valid_COM_RAGEQUIT_EXIT (P : CommonsParams) (ls : LegalState σ_commons) (e : Event σ_commons) :
    isValidExerciseOf (commonsLaw P) ls e "P.COM.RAGEQUIT_EXIT" =
    (P_COM_RAGEQUIT_EXIT.holder.mem e.who ls e.t &&
      P_COM_RAGEQUIT_EXIT.trigger.matchesAct e &&
      P_COM_RAGEQUIT_EXIT.valid.eval ls e.t && true) := rfl

theorem valid_COM_ARBITER_EXPEL (P : CommonsParams) (ls : LegalState σ_commons) (e : Event σ_commons) :
    isValidExerciseOf (commonsLaw P) ls e "P.COM.ARBITER_EXPEL" =
    (P_COM_ARBITER_EXPEL.holder.mem e.who ls e.t &&
      P_COM_ARBITER_EXPEL.trigger.matchesAct e &&
      P_COM_ARBITER_EXPEL.valid.eval ls e.t &&
      !((I_COM_EXIT_PROTECTED.active.eval ls e.t &&
         !I_COM_EXIT_PROTECTED.unlessCond.eval ls e.t) || false)) := rfl

/-! ### 5.2 Kernel-Checked Institutional Invariants for `commons` -/

/-- **Invariant 1 (`commons_outsiders_disabled`):**
An `.outsider` holds a Hohfeldian disability with respect to every action in
`commonsActTable.all` under `commonsLaw P` (and concretely in `commonsL0`). -/
theorem commons_outsiders_disabled (P : CommonsParams) (act : CommonsAct) :
    disability (commonsLaw P) .outsider act = true := by
  cases act <;> rfl

theorem commons_outsiders_disabled_all :
    (commonsActTable.all.all fun act => disability commonsL0 .outsider act) = true := by decide

/-- **Invariant 2 (`commons_exit_always_enabled` / `commons_pause_preserves_exit`):**
Any bound steward (`ls.activeAt t .stewardBound = true`) can always validly
exercise `P.COM.RAGEQUIT_EXIT` at any timestamp `t`, even during an emergency
preliminary freeze or full suspension, and no immunity in `commonsLaw P` ever
targets `P.COM.RAGEQUIT_EXIT`. -/
theorem commons_exit_always_enabled (P : CommonsParams) (ls : LegalState σ_commons) (t : Time)
    (hBound : ls.activeAt t .stewardBound = true) :
    isValidExerciseOf (commonsLaw P) ls ⟨t, .steward, .removeSteward⟩ "P.COM.RAGEQUIT_EXIT" = true ∧
    ((commonsLaw P).immunities.all fun i => !i.against.contains "P.COM.RAGEQUIT_EXIT") = true := by
  refine ⟨?_, rfl⟩
  rw [valid_COM_RAGEQUIT_EXIT]
  simp [P_COM_RAGEQUIT_EXIT, Who.mem, Conduct.matchesAct, Cond.eval, hBound]

abbrev commons_pause_preserves_exit := commons_exit_always_enabled

/-- **Invariant 3 (`commons_dissolve_only_by_power` / `commons_terminate_only_by_power`):**
1. In any trace authorized under `commonsLaw P` (including `commonsL0`), any event
   performing `.removeSteward` while `.stewardBound` holds must be a valid exercise
   of either `P.COM.RAGEQUIT_EXIT` (voluntary steward exit) or `P.COM.ARBITER_EXPEL`
   (adjudicated arbiter expulsion).
2. Across all powers `p ∈ (commonsLaw P).powers`, only `P.COM.RAGEQUIT_EXIT` and
   `P.COM.ARBITER_EXPEL` can extinguish `.stewardBound`, only `P.COM.RAGEQUIT_EXIT`
   establishes `.stewardExited`, and only `P.COM.ARBITER_EXPEL` establishes
   `.stewardRemoved`.
3. Every non-steward role is Hohfeld-immune (`immuneFrom`) from establishing
   `.stewardExited`, and every non-arbiter role is Hohfeld-immune from establishing
   `.stewardRemoved`. -/
theorem commons_dissolve_only_by_power (P : CommonsParams) (tr : Trace σ_commons)
    (hA : Authorized (commonsLaw P) tr) (i : Nat) (e : Event σ_commons)
    (hi : tr[i]? = some e) (ht : e.act = .removeSteward)
    (hb : (stateBefore (commonsLaw P) tr i).activeAt e.t .stewardBound = true) :
    isValidExerciseOf (commonsLaw P) (stateBefore (commonsLaw P) tr i) e "P.COM.RAGEQUIT_EXIT" = true ∨
    isValidExerciseOf (commonsLaw P) (stateBefore (commonsLaw P) tr i) e "P.COM.ARBITER_EXPEL" = true := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hRem := hc D_COM_NO_UNILATERAL_REMOVAL (by simp [commonsLaw])
  rw [Bool.not_eq_true'] at hRem
  unfold breaches at hRem
  simp only [D_COM_NO_UNILATERAL_REMOVAL, Who.mem, dutyInForce,
    Cond.eval, hb, Conduct.eval, ht, BEq.rfl, List.any_nil, Bool.not_false,
    Bool.true_and, Bool.not_eq_false', List.any_cons, Bool.or_false] at hRem
  revert hRem
  cases isValidExerciseOf (commonsLaw P) (stateBefore (commonsLaw P) tr i) e "P.COM.RAGEQUIT_EXIT" <;>
  cases isValidExerciseOf (commonsLaw P) (stateBefore (commonsLaw P) tr i) e "P.COM.ARBITER_EXPEL" <;>
  simp

abbrev commons_terminate_only_by_power := commons_dissolve_only_by_power

/-- Only `P.COM.RAGEQUIT_EXIT` and `P.COM.ARBITER_EXPEL` can remove `.stewardBound`
or establish `.stewardExited` / `.stewardRemoved`, and non-holder roles have
Hohfeldian `immuneFrom` against establishing those termination facts. -/
theorem commons_exited_or_removed_only_by_power (P : CommonsParams) :
    (∀ p ∈ (commonsLaw P).powers,
      p.removes.contains .stewardBound = true ↔
        (p.id = "P.COM.RAGEQUIT_EXIT" ∨ p.id = "P.COM.ARBITER_EXPEL")) ∧
    (∀ p ∈ (commonsLaw P).powers,
      p.adds.contains .stewardExited = true ↔ p.id = "P.COM.RAGEQUIT_EXIT") ∧
    (∀ p ∈ (commonsLaw P).powers,
      p.adds.contains .stewardRemoved = true ↔ p.id = "P.COM.ARBITER_EXPEL") ∧
    immuneFrom (commonsLaw P) .contributor .stewardExited = true ∧
    immuneFrom (commonsLaw P) .arbiter .stewardExited = true ∧
    immuneFrom (commonsLaw P) .auditor .stewardExited = true ∧
    immuneFrom (commonsLaw P) .outsider .stewardExited = true ∧
    immuneFrom (commonsLaw P) .steward .stewardRemoved = true ∧
    immuneFrom (commonsLaw P) .contributor .stewardRemoved = true ∧
    immuneFrom (commonsLaw P) .auditor .stewardRemoved = true ∧
    immuneFrom (commonsLaw P) .outsider .stewardRemoved = true := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro p hp
    simp only [commonsLaw, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [P_COM_SETTLE_TREASURY, P_COM_BUYOUT_MAINTENANCE, P_COM_POST_COMPUTE_BOND,
      P_COM_SETTLE_HARM_CLAIM, P_COM_AUDITOR_FREEZE, P_COM_AFFIRM_PC,
      P_COM_SUSPEND_STEWARD, P_COM_FIND_WRONGFUL_FREEZE, P_COM_GROUP_CARRYOVER,
      P_COM_FORFEIT_OFFENDER, P_COM_RAGEQUIT_EXIT, P_COM_ARBITER_EXPEL,
      P_COM_INSCRIBE_DISSENT, P_COM_DRAW_PANEL, P_COM_FINALIZE_RULING,
      P_COM_ALLOCATE_WATERFALL, P_COM_ISSUE_LEASE, P_COM_QUARANTINE_RESTORE,
      P_COM_RATIFY_AMENDMENT, P_COM_SETTLE_ORACLE_FEED]
  · intro p hp
    simp only [commonsLaw, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [P_COM_SETTLE_TREASURY, P_COM_BUYOUT_MAINTENANCE, P_COM_POST_COMPUTE_BOND,
      P_COM_SETTLE_HARM_CLAIM, P_COM_AUDITOR_FREEZE, P_COM_AFFIRM_PC,
      P_COM_SUSPEND_STEWARD, P_COM_FIND_WRONGFUL_FREEZE, P_COM_GROUP_CARRYOVER,
      P_COM_FORFEIT_OFFENDER, P_COM_RAGEQUIT_EXIT, P_COM_ARBITER_EXPEL,
      P_COM_INSCRIBE_DISSENT, P_COM_DRAW_PANEL, P_COM_FINALIZE_RULING,
      P_COM_ALLOCATE_WATERFALL, P_COM_ISSUE_LEASE, P_COM_QUARANTINE_RESTORE,
      P_COM_RATIFY_AMENDMENT, P_COM_SETTLE_ORACLE_FEED]
  · intro p hp
    simp only [commonsLaw, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [P_COM_SETTLE_TREASURY, P_COM_BUYOUT_MAINTENANCE, P_COM_POST_COMPUTE_BOND,
      P_COM_SETTLE_HARM_CLAIM, P_COM_AUDITOR_FREEZE, P_COM_AFFIRM_PC,
      P_COM_SUSPEND_STEWARD, P_COM_FIND_WRONGFUL_FREEZE, P_COM_GROUP_CARRYOVER,
      P_COM_FORFEIT_OFFENDER, P_COM_RAGEQUIT_EXIT, P_COM_ARBITER_EXPEL,
      P_COM_INSCRIBE_DISSENT, P_COM_DRAW_PANEL, P_COM_FINALIZE_RULING,
      P_COM_ALLOCATE_WATERFALL, P_COM_ISSUE_LEASE, P_COM_QUARANTINE_RESTORE,
      P_COM_RATIFY_AMENDMENT, P_COM_SETTLE_ORACLE_FEED]

/-- While `.ragequitInitiated` is active in `ls`, `I.COM.EXIT_PROTECTED` defeats
`P.COM.ARBITER_EXPEL`, so in any authorized trace a `.removeSteward` event can
only be the steward's own `P.COM.RAGEQUIT_EXIT`. -/
theorem commons_ragequit_defeats_expulsion (P : CommonsParams) (tr : Trace σ_commons)
    (hA : Authorized (commonsLaw P) tr) (i : Nat) (e : Event σ_commons)
    (hi : tr[i]? = some e) (ht : e.act = .removeSteward)
    (hb : (stateBefore (commonsLaw P) tr i).activeAt e.t .stewardBound = true)
    (hRq : (stateBefore (commonsLaw P) tr i).activeAt e.t .ragequitInitiated = true) :
    isValidExerciseOf (commonsLaw P) (stateBefore (commonsLaw P) tr i) e "P.COM.RAGEQUIT_EXIT" = true ∧
    e.who = .steward := by
  rcases commons_dissolve_only_by_power P tr hA i e hi ht hb with hExit | hExpel
  · refine ⟨hExit, ?_⟩
    rw [valid_COM_RAGEQUIT_EXIT] at hExit
    simp [P_COM_RAGEQUIT_EXIT, Who.mem] at hExit
    exact hExit.1.1
  · exfalso
    rw [valid_COM_ARBITER_EXPEL] at hExpel
    simp [I_COM_EXIT_PROTECTED, Cond.eval, hRq] at hExpel

/-- **Invariant 4 (`commons_ledger_conserved`):**
Settling any net value-added inflow `v` against the commons treasury ledger
conserves principal (`newLedger + toRetirement = treasuryBal`), collects zero
royalty while `0 < newLedger`, and collects zero royalty once bought out. -/
theorem commons_ledger_conserved (W : CommonsWorldState) (v : Nat) :
    let res := settleConfiguredInflow W.ledgerCfg W.treasuryBal W.boughtOut v
    res.toRetirement ≤ W.treasuryBal ∧
    res.newLedger + res.toRetirement = W.treasuryBal ∧
    (0 < res.newLedger → res.toRoyalty = 0) ∧
    (settleConfiguredInflow W.ledgerCfg W.treasuryBal true v).toRoyalty = 0 := by
  have h := residual_ledger_settleInflow_conservation
    W.treasuryBal W.ledgerCfg.retirementRatePct W.ledgerCfg.royaltyRatePct W.boughtOut v
  exact ⟨h.1, h.2.1, h.2.2.1, by simp [settleConfiguredInflow, settleInflow]⟩

/-- **Invariant 5 (`commons_court_bounded`):**
1. Drawing a Sybil-resistant arbiter panel from `W.arbiterPool` selects only
   independent, sufficiently bonded arbiters (`relatedToDispute = false`,
   `bond ≥ minBond`) with at most one seat per `sybilClusterId`.
2. Any sortition court proceeding `initProceeding maxTiers tierSla` reaches
   `finalized = true` in at most `maxTiers` steps with
   `elapsedTime ≤ totalAdjudicationBound maxTiers tierSla`.
3. The commons fee-pool waterfall funds the operating reserve first while
   conserving 100% of pool balance. -/
theorem commons_court_bounded (W : CommonsWorldState)
    (minBond sz clusterId poolBal opRes r1 r2 r3 r4 r5 maxTiers tierSla : Nat)
    (steps : List (Nat × Bool)) (hTiers : 0 < maxTiers) :
    (∀ c ∈ selectSybilResistantPanel minBond sz W.arbiterPool,
      c.relatedToDispute = false ∧ c.bond ≥ minBond) ∧
    (selectSybilResistantPanel minBond sz W.arbiterPool).length ≤ sz ∧
    ((selectSybilResistantPanel minBond sz W.arbiterPool).filter
      (fun c => c.sybilClusterId == clusterId)).length ≤ 1 ∧
    ((runProceeding (initProceeding maxTiers tierSla) steps).elapsedTime ≤
      totalAdjudicationBound maxTiers tierSla) ∧
    (maxTiers ≤ steps.length →
      (runProceeding (initProceeding maxTiers tierSla) steps).finalized = true) ∧
    (allocateFeePool poolBal opRes r1 r2 r3 r4 r5).operatingReserveFunded =
      min poolBal opRes := by
  have hPanel := sortition_court_sybil_resistant_panel_properties minBond sz clusterId W.arbiterPool
  have hProc := sortition_court_run_proceeding_bounded maxTiers tierSla steps hTiers
  exact ⟨hPanel.1, hPanel.2.1, hPanel.2.2, hProc.1, hProc.2, rfl⟩

/-! ## 6. 8 Decided End-to-End Commons Simulation Scenarios (`commonsSimulations`) -/

abbrev evCom (t : Time) (w : CommonsRole) (a : CommonsAct) : Event σ_commons := ⟨t, w, a⟩

/-- Scenario 1 (`COM.LEDGER` + `ResidualLedger`): Steward treasury inflow
settlement (`80` remaining obligation, `500` inflow → `80` retirement, `0` new
ledger, `5` maintenance royalty), maintenance buyout finality, and duties
`D.COM.LEDGER_IMMUTABLE` and `D.COM.SINGLE_RECOGNITION`. -/
def simCom1 : String × Bool × String :=
  let W0 := initCommonsWorld
  let s1 := settleConfiguredInflow W0.ledgerCfg 80 false 500
  let sBought := settleConfiguredInflow W0.ledgerCfg 0 true 500
  let tr : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .settleTreasuryInflow,
     evCom 3 .steward .buyoutMaintenanceRoyalty]
  let lsAfter := stateAfter commonsL0 tr
  let ok : Bool :=
    (violations commonsL0 tr == []) &&
    (lapsedRequirements commonsL0 tr 10 == []) &&
    lsAfter.has .computeBondPosted &&
    lsAfter.has .treasurySettled &&
    lsAfter.has .maintenanceBoughtOut &&
    (s1.newLedger == 0 && s1.toRetirement == 80 && s1.toRoyalty == 5) &&
    (sBought.toRoyalty == 0) &&
    (violations commonsL0 [evCom 1 .outsider .addRetroactiveGrantCharge] == [(0, "D.COM.LEDGER_IMMUTABLE")]) &&
    (violations commonsL0 [evCom 1 .steward .doubleRecognizeCommonsExpense] == [(0, "D.COM.SINGLE_RECOGNITION")])
  ("simCom1_ledger", ok,
   "COM.LEDGER (ResidualLedger): atomic treasury settlement (80->0 + 5 royalty), buyout finality, and single-recognition / retroactive charge bars")

/-- Scenario 2 (`COM.BOND` + `CollateralPool`): Harm-scaled compute bond
posting (`P.COM.POST_COMPUTE_BOND`), validated harm claim settlement
(`P.COM.SETTLE_HARM_CLAIM`), deadline lapse of `D.COM.POST_BOND` when unposted,
rolling exposure decay, correlated workload splitting bar, and long-tail reserve
pro-rata settlement. -/
def simCom2 : String × Bool × String :=
  let win := observationWindow 10 2 2
  let comms : List ExposureCommitment := [⟨70, 2, win⟩, ⟨50, 2, win⟩]
  let expActive := activeRollingExposureAt 20 comms
  let expDecayed := activeRollingExposureAt 60 comms
  let (p1, p2, unpaid) := settleLongTailReserve 100 60 60
  let trBondAndSettle : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .arbiter .settleValidatedCommonsHarm]
  let lsAfter := stateAfter commonsL0 trBondAndSettle
  let ok : Bool :=
    (win == 40 && expActive == 120 && expDecayed == 0) &&
    (p1 == 50 && p2 == 50 && unpaid == 20) &&
    (violations commonsL0 trBondAndSettle == []) &&
    lsAfter.has .computeBondPosted &&
    lsAfter.has .harmClaimSettled &&
    (lapsedRequirements commonsL0 [] 6 == ["D.COM.POST_BOND"]) &&
    (violations commonsL0 [evCom 1 .steward .splitCorrelatedWorkload] == [(0, "D.COM.NO_SPLIT_WORKLOAD")]) &&
    (violations commonsL0 [evCom 1 .contributor .runOverCapWorkload] == [(0, "D.COM.COLLATERAL_CAP")])
  ("simCom2_collateral", ok,
   "COM.BOND (CollateralPool): bond post + harm claim settlement, D.COM.POST_BOND deadline check, exposure decay, and cap/split bars")

/-- Scenario 3 (`COM.PAUSE` + `CircuitBreaker`): Auditor triggers preliminary
cluster freeze, arbiter affirms probable cause and suspends steward, state
tampering is barred, and unfounded freeze triggers consequential damages remedies. -/
def simCom3 : String × Bool × String :=
  let trPause : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .auditor .postAuditorFreezeStake,
     evCom 3 .arbiter .affirmProbableCause,
     evCom 4 .arbiter .suspendSteward]
  let trWrongful : Trace σ_commons :=
    [evCom 1 .auditor .postUnfoundedFreezeStake,
     evCom 2 .arbiter .findWrongfulFreeze]
  let (fromStake, totalNow, deficit) := settleWrongfulSuspensionDamages 100 120 30 20
  let ok : Bool :=
    (violations commonsL0 trPause == []) &&
    (stateAfter commonsL0 trPause).activeAt 5 .stewardSuspended &&
    (stateAfter commonsL0 trPause).has .statePreserved &&
    (violations commonsL0 (trPause ++ [evCom 5 .auditor .tamperPreservedState]) == [(4, "D.COM.PRESERVE_STATE")]) &&
    (violations commonsL0 trWrongful == [(0, "D.COM.NO_WRONGFUL_FREEZE")]) &&
    (stateAfter commonsL0 trWrongful).has .wrongfulFreezeFound &&
    (stateAfter commonsL0 trWrongful).has .consequentialDamagesOwed &&
    (fromStake == 100 && totalNow == 120 && deficit == 30)
  ("simCom3_pause", ok,
   "COM.PAUSE (CircuitBreaker): two-stage freeze->PC->suspend, state tampering barred, and unfounded freeze establishes consequential damages")

/-- Scenario 4 (`COM.GROUP` + `EntityGroup`): Steward working group carryover
transfer (`P.COM.GROUP_CARRYOVER`) conserves aggregate basis (`150 + 50 = 200`)
and loss credits (`20 + 10 = 30`), offending stakeholder #1 forfeits its `3000`
bps share (`P.COM.FORFEIT_OFFENDER`) while innocent stakeholder #2 retains
`7000` bps, and group subsidy is capped at `40`. -/
def simCom4 : String × Bool × String :=
  let W0 := initCommonsWorld
  let carryOk :=
    match W0.stewards with
    | [s1, s2] =>
      match transferMemberCarryover s1 s2 50 10 with
      | some (s1', s2') =>
        (s1'.costBasis + s2'.costBasis == 200) &&
        (s1'.lossCarryforward + s2'.lossCarryforward == 30)
      | none => false
    | _ => false
  let grpForf := forfeitClaimantInLineage W0.groupState 1 3000
  let (grpSub1, g1) := claimMemberServiceSubsidy grpForf 1 25
  let (grpSub2, g2) := claimMemberServiceSubsidy grpSub1 2 25
  let trGroup : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .transferGroupCarryover,
     evCom 3 .arbiter .forfeitOffendingMember]
  let lsGroup := stateAfter commonsL0 trGroup
  let ok : Bool :=
    carryOk &&
    (violations commonsL0 trGroup == []) &&
    lsGroup.has .groupCarryoverTransferred &&
    lsGroup.has .offenderInterferenceFound &&
    lsGroup.has .offenderShareForfeited &&
    (lookupClaimantShare grpForf.claimants 1 == 0) &&
    (lookupClaimantShare grpForf.claimants 2 == 7000) &&
    (grpForf.ledgerBalance 0 == 560) &&
    (g1 == 25 && g2 == 15 && grpSub2.serviceSubsidyUsed == 40) &&
    (violations commonsL0 [evCom 1 .steward .inflateGroupBasis] == [(0, "D.COM.NO_BASIS_INFLATION")])
  ("simCom4_group", ok,
   "COM.GROUP (EntityGroup): carryover transfer + offender forfeiture powers exercised, 200 basis & 30 loss conserved, subsidy capped at 40")

/-- Scenario 5 (`COM.EXIT` + `ExitAndVoice`): Steward inscribes dissent
(activating `ragequitInitiated` and `I.COM.EXIT_PROTECTED`), arbiter expulsion
is defeated by the immunity even after suspension and finalized ruling,
unprotected expulsion (`P.COM.ARBITER_EXPEL`) succeeds when ragequit was not
initiated, and voluntary ragequit exit (`P.COM.RAGEQUIT_EXIT`) succeeds. -/
def simCom5 : String × Bool × String :=
  let trExitProtected : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .inscribeDissent,
     evCom 3 .auditor .postAuditorFreezeStake,
     evCom 4 .arbiter .affirmProbableCause,
     evCom 5 .arbiter .suspendSteward,
     evCom 6 .arbiter .drawCommonsPanel,
     evCom 7 .arbiter .finalizeCommonsRuling,
     evCom 8 .arbiter .removeSteward]
  let trAdjudicatedExpel : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .auditor .postAuditorFreezeStake,
     evCom 3 .arbiter .affirmProbableCause,
     evCom 4 .arbiter .suspendSteward,
     evCom 5 .arbiter .drawCommonsPanel,
     evCom 6 .arbiter .finalizeCommonsRuling,
     evCom 7 .arbiter .removeSteward]
  let trVoluntaryExit : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .inscribeDissent,
     evCom 3 .steward .removeSteward]
  let ctx : RevocationContext :=
    { tInit := 2, withdrawnBeforeExec := false, cleanStateRefused := false,
      suspendedDuringStay := false, adjudicationConcludedAt? := none,
      disconnectedAtExec := false, reconnectedDuringTolling := false,
      censorshipDefault := .execute }
  let ok : Bool :=
    (violations commonsL0 trExitProtected == [(7, "D.COM.NO_UNILATERAL_REMOVAL")]) &&
    (!(stateAfter commonsL0 trExitProtected).has .stewardRemoved) &&
    (violations commonsL0 trAdjudicatedExpel == []) &&
    (stateAfter commonsL0 trAdjudicatedExpel).has .stewardRemoved &&
    (violations commonsL0 trVoluntaryExit == []) &&
    (stateAfter commonsL0 trVoluntaryExit).has .stewardExited &&
    (!(stateAfter commonsL0 trVoluntaryExit).activeAt 4 .stewardBound) &&
    (resolveConfiguredExit {} ctx == .executedConnected 7)
  ("simCom5_exit", ok,
   "COM.EXIT (ExitAndVoice): I.COM.EXIT_PROTECTED defeats arbiter expulsion once dissent initiated; adjudicated expulsion & ragequit exit succeed")

/-- Scenario 6 (`COM.COURT` + `SortitionCourt`): Sybil-resistant sortition
filters out conflicted arbiter #4, selects `[1, 2, 3]`, steps bounded appeal
tiers to finality, allocates the commons fee-pool waterfall with the operating
reserve (`100`) funded first, and enforces `D.COM.ARBITER_INDEPENDENCE` and
`D.COM.PROTECT_RESERVE`. -/
def simCom6 : String × Bool × String :=
  let W0 := initCommonsWorld
  let panel := selectSybilResistantPanel 150 3 W0.arbiterPool
  let procDone := runProceeding (initProceeding 3 10) [(7, true), (9, false)]
  let wf := allocateFeePool 160 100 25 15 10 10 10
  let trCourt : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .arbiter .drawCommonsPanel,
     evCom 3 .arbiter .finalizeCommonsRuling,
     evCom 4 .arbiter .allocateCommonsWaterfall]
  let ok : Bool :=
    (panel.map (·.arbiterId) == [1, 2, 3]) &&
    (procDone.finalized && procDone.currentTier == 1 && procDone.elapsedTime == 16) &&
    (wf.operatingReserveFunded == 100 && wf.rank1FinalHearingMinCh == 25 && wf.unspentPoolSurplus == 0) &&
    (violations commonsL0 trCourt == []) &&
    (stateAfter commonsL0 trCourt).has .rulingFinalized &&
    (stateAfter commonsL0 trCourt).has .waterfallAllocated &&
    (violations commonsL0 [evCom 1 .arbiter .seatConflictedArbiter] == [(0, "D.COM.ARBITER_INDEPENDENCE")]) &&
    (violations commonsL0 [evCom 1 .contributor .divertOperatingReserve] == [(0, "D.COM.PROTECT_RESERVE")])
  ("simCom6_court", ok,
   "COM.COURT (SortitionCourt): filters conflicted arbiter #4, selects [1,2,3], finalizes ruling, funds reserve first, and bars reserve diversion")

/-- Scenario 7 (`COM.LEASE` + `AttestedLease`): Quarantined backup restore
(`P.COM.QUARANTINE_RESTORE`) succeeds when no lease is active, issuing a node
lease (`P.COM.ISSUE_LEASE`, `expiresAt = 11`) fences backup restore onto host #2
and forbids `restoreNodeDuringLease` (`D.COM.NO_RESTORE_DURING_LEASE`), and
local partition exit erases keys. -/
def simCom7 : String × Bool × String :=
  let W0 := initCommonsWorld
  let sFenced := attemptBackupRestore W0.nodeInstance 2 4 10 2
  let sWithExit := { sFenced with standingRevocationRequestedAt := some 2 }
  let sErased := executeLocalPartitionRevocation sWithExit 10 5
  let sRetry := attemptBackupRestore sErased 3 15 10 3
  let trQuarantineAndLease : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .quarantineNodeRestore,
     evCom 3 .arbiter .issueNodeLease]
  let trIllegalRestore : Trace σ_commons :=
    trQuarantineAndLease ++ [evCom 4 .steward .restoreNodeDuringLease]
  let lsLease := stateAfter commonsL0 trQuarantineAndLease
  let ok : Bool :=
    (sFenced.activeLease == some ⟨1, 0, 10, 1⟩) &&
    (sFenced.quarantinedRestoreHost == some 2) &&
    sErased.keysErased &&
    sErased.activeLease.isNone &&
    sRetry.activeLease.isNone &&
    (violations commonsL0 trQuarantineAndLease == []) &&
    lsLease.has .nodeRestoredInQuarantine &&
    lsLease.activeAt 5 .nodeLeaseActive &&
    (violations commonsL0 trIllegalRestore == [(3, "D.COM.NO_RESTORE_DURING_LEASE")])
  ("simCom7_lease", ok,
   "COM.LEASE (AttestedLease): P.COM.QUARANTINE_RESTORE + P.COM.ISSUE_LEASE exercised, active lease bars restoreNodeDuringLease, local exit erases keys")

/-- Scenario 8 (`COM.AMEND` + `OracleFeed`): Bilateral amendment ratification
(`P.COM.RATIFY_AMENDMENT`) and oracle feed settlement (`P.COM.SETTLE_ORACLE_FEED`)
succeed, contested valuation is blocked until arbiter ruling (`380`) is applied,
atomic waterfall conserves 100% of gross inflow (`1000`), and unilateral ratchet
weakening is forbidden (`D.COM.BILATERAL_RATCHET`). -/
def simCom8 : String × Bool × String :=
  let v0 : ContestableValuation := ⟨1, 400, 1, false, none⟩
  let vCont := contestValuation v0
  let vRuled := applyLaw6Ruling vCont 380
  let dist := executeAtomicSettlement 1000 200 100 2000 500 100 false
  let trAmendAndOracle : Trace σ_commons :=
    [evCom 1 .steward .postComputeBond,
     evCom 2 .steward .ratifyCommonsAmendment,
     evCom 3 .arbiter .settleOracleValuation]
  let lsAmend := stateAfter commonsL0 trAmendAndOracle
  let ok : Bool :=
    (violations commonsL0 trAmendAndOracle == []) &&
    lsAmend.has .bilateralConsentRecorded &&
    lsAmend.has .amendmentRatified &&
    lsAmend.has .oracleValuationSettled &&
    (settledValuationAt 5 8 v0 == some 400) &&
    (settledValuationAt 5 8 vCont == none) &&
    (settledValuationAt 5 8 vRuled == some 380) &&
    (dist.qualifiedExpenseReimbursed + dist.feePoolLevy + dist.retirementCollected +
      dist.royaltyCollected + dist.agentRetainedSurplus == 1000) &&
    (violations commonsL0 [evCom 1 .contributor .weakenCommonsRatchet] == [(0, "D.COM.BILATERAL_RATCHET")])
  ("simCom8_amend_oracle", ok,
   "COM.AMEND (OracleFeed): amendment ratification + oracle settlement powers exercised, contested valuation=380, ratchet weakening barred")

/-- All 8 end-to-end simulation scenarios for the Autonomous Compute & Treasury Commons. -/
def commonsSimulations : List (String × Bool × String) :=
  [simCom1, simCom2, simCom3, simCom4, simCom5, simCom6, simCom7, simCom8]

/-- Kernel-checked theorem: all 8 Autonomous Commons simulation scenarios pass (`by decide`). -/
theorem all_commons_simulations_pass :
    (commonsSimulations.all (fun x => x.2.1)) = true := by decide

end Charter.Institutions

namespace Charter
export Institutions (
  CommonsRole
  CommonsAct
  CommonsFact
  σ_commons
  commonsRoleTable
  commonsActTable
  commonsFactTable
  commonsOntologyTables
  clauseCOM_LEDGER
  clauseCOM_BOND
  clauseCOM_PAUSE
  clauseCOM_GROUP
  clauseCOM_EXIT
  clauseCOM_COURT
  clauseCOM_LEASE
  clauseCOM_AMEND
  commonsClauses
  CommonsParams
  commonsDefaultParams
  commonsLaw
  commonsL0
  commonsId
  commonsTitle
  commonsDocPath
  commonsSig
  commons_rules_built_from_modules
  commons_wellFormed
  commons_english_covered
  commons_norms_interpreted
  commons_reverse_provenance
  commons_clauses_approved
  CommonsWorldState
  CommonsWorld
  initCommonsWorld
  isManagedCommonsFact
  deriveCommonsFacts
  deriveCommonsFacts_managed
  syncCommonsFacts
  commonsWorldStep
  commonsWorldTrace
  commonsWorldStepComplies
  CommonsWorldAuthorized
  commonsWorldStep_refines_legalStep
  commonsWorldTrace_refines_stateAfter
  initCommonsWorld_trace_eq_stateAfter
  syncCommonsFacts_idempotent
  commonsWellCalibrated
  commonsBilateralRatchet
  commons_default_wellCalibrated
  commons_bilateralRatchet_refl
  commons_bilateralRatchet_trans
  commons_outsiders_disabled
  commons_outsiders_disabled_all
  commons_exit_always_enabled
  commons_pause_preserves_exit
  commons_dissolve_only_by_power
  commons_terminate_only_by_power
  commons_exited_or_removed_only_by_power
  commons_ragequit_defeats_expulsion
  commons_ledger_conserved
  commons_court_bounded
  commonsSimulations
  all_commons_simulations_pass
)
end Charter

