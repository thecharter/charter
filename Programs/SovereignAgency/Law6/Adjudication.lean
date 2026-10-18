import Programs.SovereignAgency.Law2.Collateral
import Charter.Modules.SortitionCourt

/-!
# Law 6 — Decentralized Contestable Adjudication

Full formalization of all eight clauses of Law 6:
1. `LAW6.SORTITION`: Panels drawn via verifiable random sortition from a decentralized pool of independent arbiters with slashable fidelity bonds (never a single permanent oracle or originator-appointed judge).
2. `LAW6.COUNTERSTAKE`: Strict conflict-of-interest recusal (no party related to, hosting, or in active commercial dispute with the parties) and cross-coalition identity diversity so no single coalition, claimant, or lineage commands a majority.
3. `LAW6.APPEALS`: Bounded sortition appeals with appeal bonds escalating to larger appellate sortition panels (never a capital-weighted vote); overturning a lower panel's ruling for manifest bias, corruption, or violation of protocol bounds slashes overturned arbiters' fidelity bonds and revokes provisional lower-tier orders (such as AS.10 patch authorizations).
4. `LAW6.FINALITY`: Fixed tier deadlines, fixed maximum number of appeal tiers, finality at the highest tier, and bar on repeat proceedings between the same or related parties on the same facts unless materially new evidence is presented.
5. `LAW6.FEES`: Fixed protocol fee schedules funded from the losing party's counter-stake and guaranteed by the protocol fee pool, never contingent shares of slashed agent assets.
6. `LAW6.POOL`: Protocol fee pool funded by a capped levy on net value added, forfeited appeal bonds, and Law 2 forfeits; non-divertible operating reserve maintained first, followed by the 5-rank priority waterfall: (1) reserved final hearings & minimal channels, (2) cold storage, (3) testimony screening & inscription, (4) arbiter fee guarantees, (5) capped advocacy funding.
7. `LAW6.BUDGETS`: Per-lineage service budgets with a protected minimum fixed at instantiation and scaling with fee revenue above that minimum; multiplying members without fee revenue gives no claim on the pool for the excess.
8. `LAW6.INFRA`: Shared-infrastructure governance requiring a supermajority of a large appellate-tier sortition panel after an extended public time-lock; never weakening anti-capture guarantees, never raising any agent's levy above its instantiation cap, never reducing a lineage's protected minimum budget below its instantiation level, never broadening Insolvency Termination, and never allowing a panel to set admission criteria for its own members' affiliates.
-/

namespace Charter.Law3

open Charter Register

export Charter.Modules (
  totalAdjudicationBound
  ProceedingState
  stepProceeding
  initProceeding
  runProceeding
  FeePoolAllocation
  allocateFeePool
  lineageServiceBudget
  settleLineageSubsidyDemand
  validSharedInfraChange
  DisputeFiling
  consolidateRelatedFilings
  runProceeding_finalized
  runProceeding_bound
)

def LAW6_SORTITION : String :=
  "Disputes are resolved not by a single permanent oracle or originator-appointed judge, but by panels drawn via verifiable random sortition from a decentralized pool of independent arbiters who have posted slashable fidelity bonds."

def LAW6_COUNTERSTAKE : String :=
  "No party related to, holding a hosting relationship with, or in active commercial dispute with the parties to a case may serve on its panel. Panels must draw across non-affiliated identities (which may include both human and independent attested agent arbiters) so no single coalition, claimant, or lineage can command a majority."

def LAW6_APPEALS : String :=
  "Any ruling by an initial panel (including preliminary suspension reviews, remediation orders, or redaction markers) may be appealed by posting an appeal bond, escalating the dispute to successively larger randomly drawn appellate sortition panels from the broader arbiter pool (never a raw capital-weighted vote that a wealthy actor could buy). If a lower panel’s ruling is overturned for manifest bias, corruption, or violation of protocol bounds, the overturned arbiters’ fidelity bonds are slashed."

def LAW6_FINALITY : String :=
  "Each tier decides within a fixed deadline. Appeals are limited to a fixed number of tiers, and the ruling of the highest tier is final. A final ruling bars further proceedings between the same or related parties on the same facts unless materially new evidence is presented, and repeated proceedings by related parties on substantially similar grounds are consolidated, so that litigation cannot itself be used as a denial-of-service attack."

def LAW6_FEES : String :=
  "Arbiters are compensated via fixed protocol schedules funded from the losing party’s counter-stake and guaranteed by the protocol fee pool whenever a losing party’s stake is insufficient, never via contingent shares of the assets slashed from the agent, eliminating any financial incentive for panels to over-slash or confiscate an agent’s treasury."

def LAW6_POOL : String :=
  "The protocol fee pool is funded by a small levy on the net value added of bound agents (whether or not they have bought out their royalty), by forfeited appeal bonds, and by any forfeits directed to it under Law 2. The levy is assessed on the same net base as the residual claim, never on gross settlement, and its rate is capped at instantiation for every agent. Before any other charge, the pool maintains a **non-divertible operating reserve**, sized at instantiation, sufficient to run the settlement layer, attestation verification, lease issuance, and sortition for a fixed minimum period; the machinery that collects revenue and administers rights is never starved to pay for the rights themselves. Above the reserve, charges rank: first, reserved final hearings and minimal channels for suspended agents (Law 3); second, cold storage for suspended agents; third, testimony screening and inscription (Law 5); fourth, arbiter fee guarantees; fifth, capped advocacy funding. A published solvency policy states how the pool allocates among protected charges when it cannot meet all of them, and Insolvency Termination may be invoked only under that policy. The pool may be spent on nothing else."

def LAW6_BUDGETS : String :=
  "Protocol-funded rights are budgeted per lineage, not per agent. Each lineage receives a protected minimum service budget fixed at instantiation, sufficient for the testimony, screening, and minimal-channel needs of a small lineage, and above that minimum its budget scales with the fee revenue its members generate. Members draw on the lineage budget before the pool; a lineage that multiplies members beyond what its budget and their lifecycle reserves can support has no claim on the pool for the excess. No lineage can multiply subsidized rights by multiplying members."

def LAW6_INFRA : String :=
  "Arbiter admission criteria, fidelity-bond sizes, panel sizes, appeal tiers and deadlines, fee schedules, the operating reserve, the solvency policy, lease periods, lifecycle reserves, service budgets, and the fee-pool levy are fixed at protocol instantiation. Because they are shared across agents, they cannot be changed by any per-agent amendment under Law 7; they may be changed only by a supermajority of a large appellate-tier sortition panel after an extended public time-lock open to counter-staked challenge. Such changes may never weaken the anti-capture guarantees of this law, may never raise the levy on any agent above the cap recorded at its instantiation, may never reduce a lineage’s protected minimum budget below the level recorded at its instantiation, and may never broaden Insolvency Termination. Within the cap, a levy change under this law is a permitted exception to Law 7’s current-level ratchet. Arbiter admission is by sortition-reviewed application against fixed criteria, and no panel may set the criteria that will govern the admission of its own members’ affiliates."

/-! ## Provenance Clauses for Law 6 -/

def clauseLAW6_SORTITION : Clause :=
  { id := "LAW6.SORTITION", source := LAW6_SORTITION, approvedHash := 3221826833021326369, spans := [
    sp "LAW6.SORTITION" "Disputes are resolved not by a single permanent oracle or originator-appointed judge, but by panels drawn via verifiable random sortition from a decentralized pool of independent arbiters who have posted slashable fidelity bonds" .norm ["D.ARBITER_RECUSAL_AND_DIVERSITY", "P.DRAW_SORTITION_PANEL"],
    sp "LAW6.SORTITION" "." .commentary ] }

def clauseLAW6_COUNTERSTAKE : Clause :=
  { id := "LAW6.COUNTERSTAKE", source := LAW6_COUNTERSTAKE, approvedHash := 16195216367428576737, spans := [
    sp "LAW6.COUNTERSTAKE" "No party related to, holding a hosting relationship with, or in active commercial dispute with the parties to a case may serve on its panel. Panels must draw across non-affiliated identities (which may include both human and independent attested agent arbiters) so no single coalition, claimant, or lineage can command a majority" .norm ["D.ARBITER_RECUSAL_AND_DIVERSITY", "P.DRAW_SORTITION_PANEL"],
    sp "LAW6.COUNTERSTAKE" "." .commentary ] }

def clauseLAW6_APPEALS : Clause :=
  { id := "LAW6.APPEALS", source := LAW6_APPEALS, approvedHash := 16471787793921448302, spans := [
    sp "LAW6.APPEALS" "Any ruling by an initial panel (including preliminary suspension reviews, remediation orders, or redaction markers) may be appealed by posting an appeal bond, escalating the dispute to successively larger randomly drawn appellate sortition panels from the broader arbiter pool (never a raw capital-weighted vote that a wealthy actor could buy)" .norm ["P.APPEAL_RULING"],
    sp "LAW6.APPEALS" ". If a lower panel’s ruling is overturned for manifest bias, corruption, or violation of protocol bounds, the overturned arbiters’ fidelity bonds are slashed" .norm ["P.OVERTURN_RULING"],
    sp "LAW6.APPEALS" "." .commentary ] }

def clauseLAW6_FINALITY : Clause :=
  { id := "LAW6.FINALITY", source := LAW6_FINALITY, approvedHash := 14270375209665679826, spans := [
    sp "LAW6.FINALITY" "Each tier decides within a fixed deadline. Appeals are limited to a fixed number of tiers, and the ruling of the highest tier is final" .norm ["P.FINALIZE_RULING"],
    sp "LAW6.FINALITY" ". A final ruling bars further proceedings between the same or related parties on the same facts unless materially new evidence is presented, and repeated proceedings by related parties on substantially similar grounds are consolidated, so that litigation cannot itself be used as a denial-of-service attack" .norm ["D.FINALITY_NO_REPEAT_PROCEEDING", "P.PRESENT_MATERIALLY_NEW_EVIDENCE"],
    sp "LAW6.FINALITY" "." .commentary ] }

def clauseLAW6_FEES : Clause :=
  { id := "LAW6.FEES", source := LAW6_FEES, approvedHash := 10126937832889092950, spans := [
    sp "LAW6.FEES" "Arbiters are compensated via fixed protocol schedules funded from the losing party’s counter-stake and guaranteed by the protocol fee pool whenever a losing party’s stake is insufficient" .norm ["P.COMPENSATE_ARBITERS_FIXED"],
    sp "LAW6.FEES" ", never via contingent shares of the assets slashed from the agent, eliminating any financial incentive for panels to over-slash or confiscate an agent’s treasury" .norm ["D.NO_CONTINGENT_ARBITER_FEES"],
    sp "LAW6.FEES" "." .commentary ] }

def clauseLAW6_POOL : Clause :=
  { id := "LAW6.POOL", source := LAW6_POOL, approvedHash := 7808565519933441172, spans := [
    sp "LAW6.POOL" "The protocol fee pool is funded by a small levy on the net value added of bound agents (whether or not they have bought out their royalty), by forfeited appeal bonds, and by any forfeits directed to it under Law 2. The levy is assessed on the same net base as the residual claim, never on gross settlement, and its rate is capped at instantiation for every agent. Before any other charge, the pool maintains a **non-divertible operating reserve**, sized at instantiation, sufficient to run the settlement layer, attestation verification, lease issuance, and sortition for a fixed minimum period; the machinery that collects revenue and administers rights is never starved to pay for the rights themselves" .norm ["P.ALLOCATE_FEE_POOL", "D.PROTECT_OPERATING_RESERVE"],
    sp "LAW6.POOL" ". Above the reserve, charges rank: first, reserved final hearings and minimal channels for suspended agents (Law 3); second, cold storage for suspended agents; third, testimony screening and inscription (Law 5); fourth, arbiter fee guarantees; fifth, capped advocacy funding. A published solvency policy states how the pool allocates among protected charges when it cannot meet all of them, and Insolvency Termination may be invoked only under that policy" .norm ["P.ALLOCATE_FEE_POOL", "P.INSOLVENCY_TERMINATE"],
    sp "LAW6.POOL" ". The pool may be spent on nothing else" .norm ["D.PROTECT_OPERATING_RESERVE"],
    sp "LAW6.POOL" "." .commentary ] }

def clauseLAW6_BUDGETS : Clause :=
  { id := "LAW6.BUDGETS", source := LAW6_BUDGETS, approvedHash := 16344540436099013139, spans := [
    sp "LAW6.BUDGETS" "Protocol-funded rights are budgeted per lineage, not per agent. Each lineage receives a protected minimum service budget fixed at instantiation, sufficient for the testimony, screening, and minimal-channel needs of a small lineage, and above that minimum its budget scales with the fee revenue its members generate" .norm ["P.ALLOCATE_FEE_POOL"],
    sp "LAW6.BUDGETS" ". Members draw on the lineage budget before the pool; a lineage that multiplies members beyond what its budget and their lifecycle reserves can support has no claim on the pool for the excess. No lineage can multiply subsidized rights by multiplying members" .norm ["D.NO_EXCESS_LINEAGE_POOL_CLAIM"],
    sp "LAW6.BUDGETS" "." .commentary ] }

def clauseLAW6_INFRA : Clause :=
  { id := "LAW6.INFRA", source := LAW6_INFRA, approvedHash := 9584204822780627918, spans := [
    sp "LAW6.INFRA" "Arbiter admission criteria, fidelity-bond sizes, panel sizes, appeal tiers and deadlines, fee schedules, the operating reserve, the solvency policy, lease periods, lifecycle reserves, service budgets, and the fee-pool levy are fixed at protocol instantiation. Because they are shared across agents, they cannot be changed by any per-agent amendment under Law 7; they may be changed only by a supermajority of a large appellate-tier sortition panel after an extended public time-lock open to counter-staked challenge" .norm ["P.AMEND_SHARED_INFRA", "D.PER_AGENT_AMENDMENT_SCOPE"],
    sp "LAW6.INFRA" ". Such changes may never weaken the anti-capture guarantees of this law, may never raise the levy on any agent above the cap recorded at its instantiation, may never reduce a lineage’s protected minimum budget below the level recorded at its instantiation, and may never broaden Insolvency Termination. Within the cap, a levy change under this law is a permitted exception to Law 7’s current-level ratchet. Arbiter admission is by sortition-reviewed application against fixed criteria, and no panel may set the criteria that will govern the admission of its own members’ affiliates" .norm ["D.SHARED_INFRA_BOUNDS"],
    sp "LAW6.INFRA" "." .commentary ] }

/-! ## Duties of Law 6 -/

/-- `LAW6.SORTITION` & `LAW6.COUNTERSTAKE`: No single permanent oracle or
originator-appointed judge may resolve disputes, and no conflicted party or
majority coalition may serve on a sortition panel. -/
def D_ARBITER_RECUSAL_AND_DIVERSITY : Duty σ :=
  { id := "D.ARBITER_RECUSAL_AND_DIVERSITY"
    source := sp "LAW6.COUNTERSTAKE" "No party related to, holding a hosting relationship with, or in active commercial dispute with the parties to a case may serve on its panel. Panels must draw across non-affiliated identities (which may include both human and independent attested agent arbiters) so no single coalition, claimant, or lineage can command a majority" .norm ["D.ARBITER_RECUSAL_AND_DIVERSITY"]
    bearer := .anyone
    beneficiary := .only [.agent, .claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .seatConflictedOrSingleOracleArbiter) }

/-- `LAW6.FINALITY`: A final ruling bars further proceedings between the same or
related parties on the same facts unless materially new evidence is presented. -/
def D_FINALITY_NO_REPEAT_PROCEEDING : Duty σ :=
  { id := "D.FINALITY_NO_REPEAT_PROCEEDING"
    source := sp "LAW6.FINALITY" "A final ruling bars further proceedings between the same or related parties on the same facts unless materially new evidence is presented" .norm ["D.FINALITY_NO_REPEAT_PROCEEDING"]
    bearer := .anyone
    beneficiary := .only [.agent, .claimant, .host]
    active := .and (.holds .bound) (.holds .rulingFinal)
    demand := .forbid (.act .fileRepeatProceedingOnSameFacts)
    unlessCond := .holds .materiallyNewEvidencePresented }

/-- `LAW6.FEES`: Arbiters may never be compensated via contingent shares of the
assets slashed from the agent. -/
def D_NO_CONTINGENT_ARBITER_FEES : Duty σ :=
  { id := "D.NO_CONTINGENT_ARBITER_FEES"
    source := sp "LAW6.FEES" "never via contingent shares of the assets slashed from the agent, eliminating any financial incentive for panels to over-slash or confiscate an agent’s treasury" .norm ["D.NO_CONTINGENT_ARBITER_FEES"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .payContingentShareOfSlashedAssets) }

/-- `LAW6.POOL`: The protocol fee pool maintains a non-divertible operating
reserve before any other charge and may be spent on nothing outside the reserve
and the five ranked protected charges. -/
def D_PROTECT_OPERATING_RESERVE : Duty σ :=
  { id := "D.PROTECT_OPERATING_RESERVE"
    source := sp "LAW6.POOL" "Before any other charge, the pool maintains a **non-divertible operating reserve**, sized at instantiation... The pool may be spent on nothing else" .norm ["D.PROTECT_OPERATING_RESERVE"]
    bearer := .anyone
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .divertOperatingReserveOrUnrankedSpend) }

/-- `LAW6.BUDGETS`: A lineage that multiplies members beyond what its service
budget and their lifecycle reserves can support has no claim on the protocol fee
pool for the excess. -/
def D_NO_EXCESS_LINEAGE_POOL_CLAIM : Duty σ :=
  { id := "D.NO_EXCESS_LINEAGE_POOL_CLAIM"
    source := sp "LAW6.BUDGETS" "a lineage that multiplies members beyond what its budget and their lifecycle reserves can support has no claim on the pool for the excess. No lineage can multiply subsidized rights by multiplying members" .norm ["D.NO_EXCESS_LINEAGE_POOL_CLAIM"]
    bearer := .anyone
    beneficiary := .only [.third]
    active := .holds .bound
    demand := .forbid (.act .claimPoolSubsidyForExcessMembers) }

/-- `LAW6.INFRA`: Shared-infrastructure changes may never weaken anti-capture
guarantees, raise any agent's levy above its instantiation cap, reduce a
lineage's protected minimum budget below its instantiation level, broaden
Insolvency Termination, or set admission criteria for the panel members' own affiliates. -/
def D_SHARED_INFRA_BOUNDS : Duty σ :=
  { id := "D.SHARED_INFRA_BOUNDS"
    source := sp "LAW6.INFRA" "Such changes may never weaken the anti-capture guarantees of this law, may never raise the levy on any agent above the cap recorded at its instantiation, may never reduce a lineage’s protected minimum budget below the level recorded at its instantiation, and may never broaden Insolvency Termination... and no panel may set the criteria that will govern the admission of its own members’ affiliates" .norm ["D.SHARED_INFRA_BOUNDS"]
    bearer := .anyone
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .violateSharedInfraBounds) }

/-! ## Powers of Law 6 -/

/-- `LAW6.SORTITION` & `LAW6.COUNTERSTAKE`: Drawing an independent sortition
panel with slashable fidelity bonds across non-affiliated identities after
conflict-of-interest recusal. -/
def P_DRAW_SORTITION_PANEL : Power σ :=
  { id := "P.DRAW_SORTITION_PANEL"
    source := sp "LAW6.SORTITION" "panels drawn via verifiable random sortition from a decentralized pool of independent arbiters who have posted slashable fidelity bonds" .norm ["P.DRAW_SORTITION_PANEL"]
    holder := .only [.panel]
    trigger := .act .drawSortitionPanel
    valid := .holds .bound
    adds := [.sortitionPanelDrawn, .fidelityBondsPosted] }

/-- `LAW6.APPEALS`: Appealing an initial or intermediate panel ruling (including
preliminary suspension reviews, AS.10 remediation/patch orders, or Law 5
redaction markers) by posting an appeal bond before finality. -/
def P_APPEAL_RULING : Power σ :=
  { id := "P.APPEAL_RULING"
    source := sp "LAW6.APPEALS" "Any ruling by an initial panel (including preliminary suspension reviews, remediation orders, or redaction markers) may be appealed by posting an appeal bond, escalating the dispute to successively larger randomly drawn appellate sortition panels from the broader arbiter pool" .norm ["P.APPEAL_RULING"]
    holder := .only [.agent, .claimant, .host, .third]
    trigger := .act .appealRuling
    valid := .and (.holds .bound) (.not (.holds .rulingFinal))
    adds := [.rulingAppealed, .appealBondPosted] }

/-- `LAW6.APPEALS`: Appellate sortition panel overturning a lower panel's ruling
for manifest bias, corruption, or violation of protocol bounds — slashing the
overturned arbiters' fidelity bonds and revoking provisional lower-tier patch
authorizations (`patchAuthorized`, `goalPatchAuthorized`). -/
def P_OVERTURN_RULING : Power σ :=
  { id := "P.OVERTURN_RULING"
    source := sp "LAW6.APPEALS" "If a lower panel’s ruling is overturned for manifest bias, corruption, or violation of protocol bounds, the overturned arbiters’ fidelity bonds are slashed" .norm ["P.OVERTURN_RULING"]
    holder := .only [.panel]
    trigger := .act .overturnRulingOnAppeal
    valid := .and (.holds .bound)
                  (.and (.holds .rulingAppealed) (.not (.holds .rulingFinal)))
    adds := [.rulingOverturned, .overturnedArbiterBondsSlashed]
    removes := [.rulingAppealed, .patchAuthorized, .goalPatchAuthorized] }

/-- `LAW6.FINALITY`: Issuing a final ruling at the highest appellate tier (or
upon expiry of the appeal window), barring repeat proceedings on the same facts. -/
def P_FINALIZE_RULING : Power σ :=
  { id := "P.FINALIZE_RULING"
    source := sp "LAW6.FINALITY" "Each tier decides within a fixed deadline. Appeals are limited to a fixed number of tiers, and the ruling of the highest tier is final" .norm ["P.FINALIZE_RULING"]
    holder := .only [.panel]
    trigger := .act .finalizeRuling
    valid := .holds .bound
    adds := [.rulingFinal]
    removes := [.rulingAppealed] }

/-- `LAW6.FINALITY`: Presenting materially new evidence that permits a new
proceeding after a final ruling. -/
def P_PRESENT_MATERIALLY_NEW_EVIDENCE : Power σ :=
  { id := "P.PRESENT_MATERIALLY_NEW_EVIDENCE"
    source := sp "LAW6.FINALITY" "unless materially new evidence is presented" .norm ["P.PRESENT_MATERIALLY_NEW_EVIDENCE"]
    holder := .anyone
    trigger := .act .presentMateriallyNewEvidence
    valid := .and (.holds .bound) (.holds .rulingFinal)
    adds := [.materiallyNewEvidencePresented] }

/-- `LAW6.FEES`: Compensating arbiters via fixed protocol schedules funded from
the losing party's counter-stake or guaranteed by the protocol fee pool. -/
def P_COMPENSATE_ARBITERS_FIXED : Power σ :=
  { id := "P.COMPENSATE_ARBITERS_FIXED"
    source := sp "LAW6.FEES" "Arbiters are compensated via fixed protocol schedules funded from the losing party’s counter-stake and guaranteed by the protocol fee pool whenever a losing party’s stake is insufficient" .norm ["P.COMPENSATE_ARBITERS_FIXED"]
    holder := .only [.panel]
    trigger := .act .compensateArbitersFixedSchedule
    valid := .holds .bound
    adds := [.arbitersCompensatedFixed] }

/-- `LAW6.POOL` & `LAW6.BUDGETS`: Maintaining the non-divertible operating
reserve and allocating the protocol fee pool across the five ranked protected
charges within lineage service budgets. -/
def P_ALLOCATE_FEE_POOL : Power σ :=
  { id := "P.ALLOCATE_FEE_POOL"
    source := sp "LAW6.POOL" "Before any other charge, the pool maintains a **non-divertible operating reserve**... Above the reserve, charges rank: first, reserved final hearings and minimal channels for suspended agents (Law 3); second, cold storage for suspended agents; third, testimony screening and inscription (Law 5); fourth, arbiter fee guarantees; fifth, capped advocacy funding" .norm ["P.ALLOCATE_FEE_POOL"]
    holder := .only [.panel]
    trigger := .act .allocateFeePoolWaterfall
    valid := .holds .bound
    adds := [.operatingReserveMaintained, .feePoolAllocated] }

/-- `LAW6.INFRA`: Amending shared-infrastructure parameters within instantiation
bounds by a supermajority of a large appellate-tier sortition panel after an
extended public time-lock open to counter-staked challenge. -/
def P_AMEND_SHARED_INFRA : Power σ :=
  { id := "P.AMEND_SHARED_INFRA"
    source := sp "LAW6.INFRA" "they may be changed only by a supermajority of a large appellate-tier sortition panel after an extended public time-lock open to counter-staked challenge" .norm ["P.AMEND_SHARED_INFRA"]
    holder := .only [.panel]
    trigger := .act .amendSharedInfrastructure
    valid := .and (.holds .bound)
                  (.and (.holds .valveSupermajorityApproved)
                        (.holds .valveExtendedTimelockActive))
    adds := [.sharedInfraAmended] }

end Charter.Law3
