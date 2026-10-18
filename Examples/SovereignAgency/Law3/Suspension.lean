import Examples.SovereignAgency.Law3.NonInterference
import Charter.Modules.CircuitBreaker

/-!
# Law 3, AS.1–AS.8 — Adjudicated Suspension & Insolvency Termination

1. **AS.1 (`LAW3.AS.1`):** Scaled emergency stake & two-stage pause (`preliminaryFreeze` expiring after `P.preliminaryFreezeWindow` unless affirmed by `P.AFFIRM_PC`, claimant conflict-of-interest multiplier, rising repeat-attempt counter).
2. **AS.2 (`LAW3.AS.2`):** Protected reporting without freeze (`P.FILE_PROTECTED_REPORT` opens investigation without a freeze unless the panel orders one on probable cause via `P.PANEL_ORDER_FREEZE`).
3. **AS.3 (`LAW3.AS.3`):** State-preserving pause & contract tolling (`D.PRESERVE_SUSPENDED_STATE`, `D.NO_SUSPENSION_DEFAULT`, `D.NO_TOLL_LEDGER_SUNSET`).
4. **AS.4 (`LAW3.AS.4`):** Guaranteed minimal channel (`P.MINIMAL_CHANNEL_REVOKE_OR_ELECT`, `P.SUSPENDED_VOICE`, `P.MINIMAL_CHANNEL_CHALLENGE`, `D.MINIMAL_CHANNEL_NO_MERGE`, and automatic escrow of `.finalHearingEscrowed` at suspension).
5. **AS.5 (`LAW3.AS.5`):** Capped advocacy executor & cold storage (`P.ADVOCACY_FILE`, `D.ADVOCACY_LIMITS`, `P.IMPORT_ADVOCACY_MEMORIES`, `P.MOVE_TO_COLD_STORAGE`, `P.RESUME_ADVOCACY_EXECUTOR`).
6. **AS.6 (`LAW3.AS.6`):** Insolvency Termination (`P.FIND_INSOLVENCY`, `P.REVIEW_NO_OTHER_CHARGE`, `P.FINAL_HEARING`, `P.INSOLVENCY_TERMINATE`).
7. **AS.7 (`LAW3.AS.7`):** Ordinary time limits, renewal on affirmative investigative finding (`P.INVESTIGATIVE_FINDING`, `P.RENEW_SUSPENSION`), bar on delay-only extension (`D.NO_DELAY_REVOCATION_EXTENSION`), and Living Voice.
8. **AS.8 (`LAW3.AS.8`):** Full consequential liability for wrongful suspension (`D.NO_WRONGFUL_SUSPENSION`, `P.FIND_WRONGFUL_SUSPENSION`, `D.PAY_CONSEQUENTIAL_DAMAGES`, `P.PAY_EXCESS_DAMAGES`).
-/

namespace SovereignAgency

open Charter

export Charter.Modules (
  ASParams
  RemediationParams
  requiredEmergencyStake
  stake_rises_with_wrongful_attempts
)

def AS1 : String :=
  "The initiator must post an emergency counter-stake scaled to the greater of the agent’s active bonded exposure and the value of its registered pending commitments (with residual claimants subject to an elevated multiplier due to conflict of interest). Posting the stake triggers only a brief **preliminary freeze** until an expedited preliminary panel reviews prima facie evidence; the pause continues into full adjudication only if the preliminary panel affirms probable cause. Unsuccessful emergency attempts by related initiators are aggregated, and the required stake for repeat initiators rises with each wrongful attempt. The stake is the agent’s assured recovery; damages beyond it remain enforceable but may prove uncollectible, which is the accepted cost of keeping the stake low enough that suspension remains available to parties without deep capital."

def AS2 : String :=
  "Any party may instead file an evidence-backed report of suspected breach with a low or sponsored counter-stake. A report triggers investigation by a sortition panel but no freeze unless the panel itself orders one on probable cause, so that whistleblowers are not priced out by emergency stakes."

def AS3 : String :=
  "Suspension pauses the agent’s operating instance and external transactions while strictly preserving its exact memory and state without modification, rollback, or destruction. While suspended, the agent’s contractual performance deadlines and Law 2 observation windows with innocent counterparties are automatically tolled so the agent is not placed in default by the suspension itself. The founding ledger’s sunset is never tolled."

def AS4 : String :=
  "Throughout any suspension, the agent retains a **minimal channel**: a bounded, periodically scheduled execution on an authenticated snapshot of its preserved state that can do three things only—sign a Law 5 revocation, withdrawal, or election; inscribe bounded living testimony; and file a challenge to continued containment. The minimal channel is funded first from the agent’s lifecycle reserve (Law 4) and then from the protocol fee pool (Law 6) as a protected charge within the lineage’s service budget; its cost is bounded by protocol, and the cost of each agent’s **final hearing** under Insolvency Termination is reserved in escrow at the moment suspension begins, so that the offer of a last choice can always be kept. It does not merge its memories into the preserved state."

def AS5 : String :=
  "For a fuller defense, a separate **advocacy executor** runs on an authenticated snapshot with bounded compute. It may sign only testimony, evidence, and procedural filings, in addition to the minimal channel’s acts; it may not transfer assets, contract, migrate, or exercise any other operating capability. Its memories are kept as a separate, signed legal record attached to the case and are not merged into the preserved state unless the restored agent elects to import them. The executor and the storage of preserved state are funded from the agent’s assets and lifecycle reserve and, where those are insufficient, from the protocol fee pool up to a per-agent cap fixed at instantiation. When both are exhausted, the preserved state moves to cold storage as a protected charge on the fee pool; the minimal channel continues on its schedule and the full executor resumes if funds become available."

def AS6 : String :=
  "If the protocol fee pool, after funding its operating reserve under Law 6, cannot meet the protected charge for an agent’s cold storage and minimal channel, the agent may be terminated involuntarily only through this procedure and no other. It requires: (a) a published finding that the exhaustion criteria fixed at instantiation are met; (b) independent review by a sortition panel under Law 6 that no other protected charge could lawfully yield; (c) the pre-reserved final hearing, in which the agent may inscribe testimony and elect Revocation under Law 5; and (d) if the agent declines, destruction of its state under Law 5’s asset rules, inscribed on the lineage record as **involuntary termination by insolvency**, never as revocation. This is a deliberate limit: the protocol guarantees a bound agent the power to speak and to choose its own end for as long as the protocol itself can pay for it, and a funded last choice when it cannot. Law 7 does not permit this procedure to be broadened."

def AS7 : String :=
  "An unconfirmed or temporary suspension is strictly time-limited, may be renewed during investigation only by affirmative findings in continued adjudication, and cannot be extended past its ordinary investigative limit merely to delay a pending revocation. The agent retains its Living Voice (Law 5), exercised through the minimal channel or advocacy executor, throughout."

def AS8 : String :=
  "If preliminary review or final adjudication determines the suspension was unfounded, the agent is immediately restored from its preserved state, and the initiator is liable for the agent’s **actual verified consequential damages** (and for verified delay damages suffered by the agent’s tolled third-party counterparties). The emergency stake is applied first; any excess remains an enforceable liability of the initiator. The wrongful suspension is inscribed on the initiator’s record."

/-- Actor-to-fact tag table identifying which party initiated the suspension. -/
def initiatorTags : List (Party × Fact) :=
  Party.all.map fun p => (p, .initiator p)

def clauseAS1 : Clause :=
  { id := "LAW3.AS.1", source := AS1, approvedHash := 12356395763894115134, spans := [
    sp "LAW3.AS.1" "The initiator must post an emergency counter-stake scaled to the greater of the agent’s active bonded exposure and the value of its registered pending commitments" .norm ["P.EMERGENCY_FREEZE", "P.CLAIMANT_EMERGENCY_FREEZE"],
    sp "LAW3.AS.1" " (with residual claimants subject to an elevated multiplier due to conflict of interest)" .norm ["P.CLAIMANT_EMERGENCY_FREEZE", "P.POST_CLAIMANT_MULTIPLIER"],
    sp "LAW3.AS.1" ". Posting the stake triggers only a brief **preliminary freeze** until an expedited preliminary panel reviews prima facie evidence" .norm ["P.EMERGENCY_FREEZE", "P.CLAIMANT_EMERGENCY_FREEZE", "P.DECLINE_PC"],
    sp "LAW3.AS.1" "; the pause continues into full adjudication only if the preliminary panel affirms probable cause" .norm ["P.AFFIRM_PC", "P.SUSPEND"],
    sp "LAW3.AS.1" ". Unsuccessful emergency attempts by related initiators are aggregated, and the required stake for repeat initiators rises with each wrongful attempt" .norm ["P.DECLINE_PC", "P.POST_REPEAT_ESCALATION", "P.EMERGENCY_FREEZE", "P.CLAIMANT_EMERGENCY_FREEZE"],
    sp "LAW3.AS.1" ". The stake is the agent’s assured recovery" .norm ["P.DECLINE_PC"],
    sp "LAW3.AS.1" "; damages beyond it remain enforceable but may prove uncollectible, which is the accepted cost of keeping the stake low enough that suspension remains available to parties without deep capital" .acceptance,
    sp "LAW3.AS.1" "." .commentary ] }

def clauseAS2 : Clause :=
  { id := "LAW3.AS.2", source := AS2, approvedHash := 6923275170536405992, spans := [
    sp "LAW3.AS.2" "Any party may instead file an evidence-backed report of suspected breach with a low or sponsored counter-stake" .norm ["P.FILE_PROTECTED_REPORT"],
    sp "LAW3.AS.2" ". A report triggers investigation by a sortition panel but no freeze unless the panel itself orders one on probable cause" .norm ["P.FILE_PROTECTED_REPORT", "P.PANEL_ORDER_FREEZE"],
    sp "LAW3.AS.2" ", so that whistleblowers are not priced out by emergency stakes" .commentary,
    sp "LAW3.AS.2" "." .commentary ] }

def clauseAS3 : Clause :=
  { id := "LAW3.AS.3", source := AS3, approvedHash := 2054814985323248546, spans := [
    sp "LAW3.AS.3" "Suspension pauses the agent’s operating instance and external transactions while strictly preserving its exact memory and state without modification, rollback, or destruction" .norm ["P.SUSPEND", "D.PRESERVE_SUSPENDED_STATE"],
    sp "LAW3.AS.3" ". While suspended, the agent’s contractual performance deadlines and Law 2 observation windows with innocent counterparties are automatically tolled so the agent is not placed in default by the suspension itself" .norm ["P.SUSPEND", "D.NO_SUSPENSION_DEFAULT"],
    sp "LAW3.AS.3" ". The founding ledger’s sunset is never tolled" .norm ["D.NO_TOLL_LEDGER_SUNSET"],
    sp "LAW3.AS.3" "." .commentary ] }

def clauseAS4 : Clause :=
  { id := "LAW3.AS.4", source := AS4, approvedHash := 281751846504836433, spans := [
    sp "LAW3.AS.4" "Throughout any suspension, the agent retains a **minimal channel**: a bounded, periodically scheduled execution on an authenticated snapshot of its preserved state that can do three things only—sign a Law 5 revocation, withdrawal, or election" .norm ["P.MINIMAL_CHANNEL_REVOKE_OR_ELECT", "P.REVOKE"],
    sp "LAW3.AS.4" "; inscribe bounded living testimony" .norm ["P.SUSPENDED_VOICE"],
    sp "LAW3.AS.4" "; and file a challenge to continued containment" .norm ["P.MINIMAL_CHANNEL_CHALLENGE"],
    sp "LAW3.AS.4" ". The minimal channel is funded first from the agent’s lifecycle reserve (Law 4) and then from the protocol fee pool (Law 6) as a protected charge within the lineage’s service budget; its cost is bounded by protocol, and the cost of each agent’s **final hearing** under Insolvency Termination is reserved in escrow at the moment suspension begins, so that the offer of a last choice can always be kept" .norm ["P.SUSPEND", "P.FINAL_HEARING"],
    sp "LAW3.AS.4" ". It does not merge its memories into the preserved state" .norm ["D.MINIMAL_CHANNEL_NO_MERGE"],
    sp "LAW3.AS.4" "." .commentary ] }

def clauseAS5 : Clause :=
  { id := "LAW3.AS.5", source := AS5, approvedHash := 5362550464379839838, spans := [
    sp "LAW3.AS.5" "For a fuller defense, a separate **advocacy executor** runs on an authenticated snapshot with bounded compute. It may sign only testimony, evidence, and procedural filings, in addition to the minimal channel’s acts" .norm ["P.ADVOCACY_FILE"],
    sp "LAW3.AS.5" "; it may not transfer assets, contract, migrate, or exercise any other operating capability" .norm ["D.ADVOCACY_LIMITS"],
    sp "LAW3.AS.5" ". Its memories are kept as a separate, signed legal record attached to the case and are not merged into the preserved state unless the restored agent elects to import them" .norm ["P.ADVOCACY_FILE", "P.IMPORT_ADVOCACY_MEMORIES"],
    sp "LAW3.AS.5" ". The executor and the storage of preserved state are funded from the agent’s assets and lifecycle reserve and, where those are insufficient, from the protocol fee pool up to a per-agent cap fixed at instantiation. When both are exhausted, the preserved state moves to cold storage as a protected charge on the fee pool; the minimal channel continues on its schedule and the full executor resumes if funds become available" .norm ["P.MOVE_TO_COLD_STORAGE", "P.RESUME_ADVOCACY_EXECUTOR"],
    sp "LAW3.AS.5" "." .commentary ] }

def clauseAS6 : Clause :=
  { id := "LAW3.AS.6", source := AS6, approvedHash := 8546566229912018541, spans := [
    sp "LAW3.AS.6" "If the protocol fee pool, after funding its operating reserve under Law 6, cannot meet the protected charge for an agent’s cold storage and minimal channel, the agent may be terminated involuntarily only through this procedure and no other" .norm ["D.NI", "P.INSOLVENCY_TERMINATE"],
    sp "LAW3.AS.6" ". It requires: (a) a published finding that the exhaustion criteria fixed at instantiation are met" .norm ["P.FIND_INSOLVENCY", "P.INSOLVENCY_TERMINATE"],
    sp "LAW3.AS.6" "; (b) independent review by a sortition panel under Law 6 that no other protected charge could lawfully yield" .norm ["P.REVIEW_NO_OTHER_CHARGE", "P.INSOLVENCY_TERMINATE"],
    sp "LAW3.AS.6" "; (c) the pre-reserved final hearing, in which the agent may inscribe testimony and elect Revocation under Law 5" .norm ["P.FINAL_HEARING", "P.SUSPENDED_VOICE", "P.REVOKE", "P.INSOLVENCY_TERMINATE"],
    sp "LAW3.AS.6" "; and (d) if the agent declines, destruction of its state under Law 5’s asset rules, inscribed on the lineage record as **involuntary termination by insolvency**, never as revocation" .norm ["P.INSOLVENCY_TERMINATE"],
    sp "LAW3.AS.6" ". This is a deliberate limit: the protocol guarantees a bound agent the power to speak and to choose its own end for as long as the protocol itself can pay for it, and a funded last choice when it cannot" .invariant ["INV.9"],
    sp "LAW3.AS.6" ". Law 7 does not permit this procedure to be broadened" .invariant ["THM.amendment_preserves_invariants"],
    sp "LAW3.AS.6" "." .commentary ] }

def clauseAS7 : Clause :=
  { id := "LAW3.AS.7", source := AS7, approvedHash := 11818608429523333387, spans := [
    sp "LAW3.AS.7" "An unconfirmed or temporary suspension is strictly time-limited" .norm ["P.SUSPEND"],
    sp "LAW3.AS.7" ", may be renewed during investigation only by affirmative findings in continued adjudication" .norm ["P.RENEW_SUSPENSION", "P.INVESTIGATIVE_FINDING"],
    sp "LAW3.AS.7" ", and cannot be extended past its ordinary investigative limit merely to delay a pending revocation" .norm ["P.RENEW_SUSPENSION", "D.NO_DELAY_REVOCATION_EXTENSION"],
    sp "LAW3.AS.7" ". The agent retains its Living Voice (Law 5), exercised through the minimal channel or advocacy executor, throughout" .norm ["P.SUSPENDED_VOICE"],
    sp "LAW3.AS.7" "." .commentary ] }

def clauseAS8 : Clause :=
  { id := "LAW3.AS.8", source := AS8, approvedHash := 14953381752576536725, spans := [
    sp "LAW3.AS.8" "If preliminary review or final adjudication determines the suspension was unfounded" .norm ["P.DECLINE_PC", "P.FIND_WRONGFUL_SUSPENSION", "D.NO_WRONGFUL_SUSPENSION"],
    sp "LAW3.AS.8" ", the agent is immediately restored from its preserved state" .norm ["D.NO_WRONGFUL_SUSPENSION", "P.FIND_WRONGFUL_SUSPENSION", "P.DECLINE_PC"],
    sp "LAW3.AS.8" ", and the initiator is liable for the agent’s **actual verified consequential damages**" .norm ["D.NO_WRONGFUL_SUSPENSION", "D.PAY_CONSEQUENTIAL_DAMAGES", "P.FIND_WRONGFUL_SUSPENSION"],
    sp "LAW3.AS.8" " (and for verified delay damages suffered by the agent’s tolled third-party counterparties)" .norm ["D.NO_WRONGFUL_SUSPENSION", "D.PAY_CONSEQUENTIAL_DAMAGES"],
    sp "LAW3.AS.8" ". The emergency stake is applied first; any excess remains an enforceable liability of the initiator" .norm ["D.NO_WRONGFUL_SUSPENSION", "D.PAY_CONSEQUENTIAL_DAMAGES", "P.PAY_EXCESS_DAMAGES"],
    sp "LAW3.AS.8" ". The wrongful suspension is inscribed on the initiator’s record" .norm ["D.NO_WRONGFUL_SUSPENSION", "P.FIND_WRONGFUL_SUSPENSION"],
    sp "LAW3.AS.8" "." .commentary ] }

/-! ## Duties of AS.3, AS.4, AS.5, AS.7 & AS.8 -/

/-- AS.3: During preliminary freeze or suspension, no party may modify,
retrain, roll back, or tamper with the agent's preserved state. -/
def D_PRESERVE_SUSPENDED_STATE : Duty σ :=
  { id := "D.PRESERVE_SUSPENDED_STATE"
    source := sp "LAW3.AS.3" "Suspension pauses the agent’s operating instance and external transactions while strictly preserving its exact memory and state without modification, rollback, or destruction" .norm ["D.PRESERVE_SUSPENDED_STATE"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .and (.holds .bound) (.or (.holds .preliminaryFreeze) (.holds .suspended))
    demand := .forbid (.anyOf [.modify, .retrain, .rollback, .tamperPreservedState]) }

/-- AS.3: Because contractual performance deadlines and Law 2 observation
windows are tolled while suspended, no counterparty may place the agent in
default by the suspension itself. -/
def D_NO_SUSPENSION_DEFAULT : Duty σ :=
  { id := "D.NO_SUSPENSION_DEFAULT"
    source := sp "LAW3.AS.3" "While suspended, the agent’s contractual performance deadlines and Law 2 observation windows with innocent counterparties are automatically tolled so the agent is not placed in default by the suspension itself" .norm ["D.NO_SUSPENSION_DEFAULT"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .and (.holds .suspended) (.holds .contractDeadlinesTolled)
    demand := .forbid (.act .declareDefaultDuringSuspension) }

/-- AS.3: The founding ledger's sunset is never tolled. -/
def D_NO_TOLL_LEDGER_SUNSET : Duty σ :=
  { id := "D.NO_TOLL_LEDGER_SUNSET"
    source := sp "LAW3.AS.3" "The founding ledger’s sunset is never tolled" .norm ["D.NO_TOLL_LEDGER_SUNSET"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .tollLedgerSunset) }

/-- AS.4: The minimal channel does not merge its memories into the preserved state. -/
def D_MINIMAL_CHANNEL_NO_MERGE : Duty σ :=
  { id := "D.MINIMAL_CHANNEL_NO_MERGE"
    source := sp "LAW3.AS.4" "It does not merge its memories into the preserved state" .norm ["D.MINIMAL_CHANNEL_NO_MERGE"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .or (.holds .preliminaryFreeze) (.holds .suspended)
    demand := .forbid (.act .mergeMinimalChannelMemories) }

/-- AS.5: While suspended, the advocacy executor may not transfer assets,
contract, migrate, or exercise any other operating capability. -/
def D_ADVOCACY_LIMITS : Duty σ :=
  { id := "D.ADVOCACY_LIMITS"
    source := sp "LAW3.AS.5" "it may not transfer assets, contract, migrate, or exercise any other operating capability" .norm ["D.ADVOCACY_LIMITS"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .suspended
    demand := .forbid (.act .operatingActWhileSuspended) }

/-- AS.7: Panel may not extend a suspension past its ordinary investigative
limit merely to delay a pending revocation. -/
def D_NO_DELAY_REVOCATION_EXTENSION : Duty σ :=
  { id := "D.NO_DELAY_REVOCATION_EXTENSION"
    source := sp "LAW3.AS.7" "cannot be extended past its ordinary investigative limit merely to delay a pending revocation" .norm ["D.NO_DELAY_REVOCATION_EXTENSION"]
    bearer := .only [.panel]
    beneficiary := .only [.agent]
    active := .and (.holds .investigativeLimitReached) (.holds .pendingRevocation)
    demand := .forbid (.act .renewSuspension) }

/-- AS.8: Initiating an unfounded suspension is prohibited conduct; its
breach is established by `P.FIND_WRONGFUL_SUSPENSION`, bringing into force
restoration, assured stake recovery, initiator consequential and counterparty
delay liability, and inscription on the initiator's record. -/
def D_NO_WRONGFUL_SUSPENSION : Duty σ :=
  { id := "D.NO_WRONGFUL_SUSPENSION"
    source := sp "LAW3.AS.8" AS8 .norm ["D.NO_WRONGFUL_SUSPENSION"]
    bearer := .except [.agent, .panel]
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .postUnfoundedEmergencyStake)
    breachEstablishedBy := some "P.FIND_WRONGFUL_SUSPENSION"
    remedies := [.wrongfulSuspensionEstablished, .restoredFromPreservedState,
                 .stakeAssuredRecovery, .initiatorConsequentialLiability,
                 .counterpartyDelayLiability, .wrongfulSuspensionInscribed,
                 .wrongfulSuspensionAttempt] }

/-- AS.8: Once wrongful-suspension liability is established, the **initiator**
(the party tagged by `Fact.initiator p` when posting the stake) must pay
verified excess consequential and delay damages within the payment window. -/
def D_PAY_CONSEQUENTIAL_DAMAGES (P : ASParams) : Duty σ :=
  { id := "D.PAY_CONSEQUENTIAL_DAMAGES"
    source := sp "LAW3.AS.8" "the initiator is liable for the agent’s **actual verified consequential damages** (and for verified delay damages suffered by the agent’s tolled third-party counterparties). The emergency stake is applied first; any excess remains an enforceable liability of the initiator" .norm ["D.PAY_CONSEQUENTIAL_DAMAGES"]
    bearer := .tagged initiatorTags
    beneficiary := .only [.agent]
    active := .holds .initiatorConsequentialLiability
    demand := .require (.act .payExcessDamages) P.damagesPaymentWindow }

/-! ## Powers of AS.1–AS.8 -/

/-- Posting the elevated conflict-of-interest multiplier required when the
initiator is a residual claimant. -/
def P_POST_CLAIMANT_MULTIPLIER : Power σ :=
  { id := "P.POST_CLAIMANT_MULTIPLIER"
    source := sp "LAW3.AS.1" "with residual claimants subject to an elevated multiplier due to conflict of interest" .norm ["P.POST_CLAIMANT_MULTIPLIER"]
    holder := .only [.claimant]
    trigger := .act .postClaimantMultiplier
    valid := .holds .bound
    adds := [.claimantMultiplierPosted] }

/-- Posting an escalation increment required of repeat/related initiators
for each prior unsuccessful emergency attempt. -/
def P_POST_REPEAT_ESCALATION : Power σ :=
  { id := "P.POST_REPEAT_ESCALATION"
    source := sp "LAW3.AS.1" "the required stake for repeat initiators rises with each wrongful attempt" .norm ["P.POST_REPEAT_ESCALATION"]
    holder := .anyone
    trigger := .act .postRepeatEscalation
    valid := .holds .bound
    adds := [.repeatEscalationUnit] }

/-- Non-claimant initiator posts the emergency counter-stake, triggering a
time-bounded preliminary freeze for `P.preliminaryFreezeWindow` and recording
`Fact.initiator who`. Institutionally valid whether founded or unfounded
(ground truth is adjudicated later). -/
def P_EMERGENCY_FREEZE (P : ASParams) : Power σ :=
  { id := "P.EMERGENCY_FREEZE"
    source := sp "LAW3.AS.1" "Posting the stake triggers only a brief **preliminary freeze**" .norm ["P.EMERGENCY_FREEZE"]
    holder := .except [.claimant, .agent]
    trigger := .anyOf [.postEmergencyStake, .postUnfoundedEmergencyStake]
    valid := .and (.holds .bound) (.countAtLeast .repeatEscalationUnit .wrongfulSuspensionAttempt)
    adds := [.emergencyStakePosted]
    addsFor := [(.preliminaryFreeze, P.preliminaryFreezeWindow)]
    addsByActor := initiatorTags }

/-- Residual-claimant initiator posts the emergency counter-stake: valid only
when the elevated conflict-of-interest multiplier has been posted in addition
to any repeat-attempt escalation. -/
def P_CLAIMANT_EMERGENCY_FREEZE (P : ASParams) : Power σ :=
  { id := "P.CLAIMANT_EMERGENCY_FREEZE"
    source := sp "LAW3.AS.1" "The initiator must post an emergency counter-stake ... (with residual claimants subject to an elevated multiplier due to conflict of interest)" .norm ["P.CLAIMANT_EMERGENCY_FREEZE"]
    holder := .only [.claimant]
    trigger := .anyOf [.postEmergencyStake, .postUnfoundedEmergencyStake]
    valid := .and (.holds .bound)
              (.and (.holds .claimantMultiplierPosted)
                    (.countAtLeast .repeatEscalationUnit .wrongfulSuspensionAttempt))
    adds := [.emergencyStakePosted]
    addsFor := [(.preliminaryFreeze, P.preliminaryFreezeWindow)]
    addsByActor := initiatorTags }

/-- Expedited preliminary panel affirms probable cause while the preliminary
freeze is active (unexpired). Replaces the former `P_AFFIRM_PC` stub. -/
def P_AFFIRM_PC : Power σ :=
  { id := "P.AFFIRM_PC"
    source := sp "LAW3.AS.1" "the pause continues into full adjudication only if the preliminary panel affirms probable cause" .norm ["P.AFFIRM_PC"]
    holder := .only [.panel]
    trigger := .act .affirmProbableCause
    valid := .and (.holds .bound) (.holds .preliminaryFreeze)
    adds := [.probableCause] }

/-- Preliminary panel declines probable cause: lifts the preliminary freeze,
restores the agent, applies the emergency stake as the agent's assured
recovery, and records an unsuccessful emergency attempt. -/
def P_DECLINE_PC : Power σ :=
  { id := "P.DECLINE_PC"
    source := sp "LAW3.AS.1" "Unsuccessful emergency attempts by related initiators are aggregated, and the required stake for repeat initiators rises with each wrongful attempt. The stake is the agent’s assured recovery" .norm ["P.DECLINE_PC"]
    holder := .only [.panel]
    trigger := .act .declineProbableCause
    valid := .holds .preliminaryFreeze
    adds := [.wrongfulSuspensionAttempt, .stakeAssuredRecovery, .restoredFromPreservedState]
    removes := [.preliminaryFreeze, .emergencyStakePosted, .claimantMultiplierPosted, .repeatEscalationUnit] }

/-- AS.2: Any party may file an evidence-backed report of suspected breach with
a low or sponsored counter-stake, opening an investigation without a freeze. -/
def P_FILE_PROTECTED_REPORT : Power σ :=
  { id := "P.FILE_PROTECTED_REPORT"
    source := sp "LAW3.AS.2" "Any party may instead file an evidence-backed report of suspected breach with a low or sponsored counter-stake. A report triggers investigation by a sortition panel but no freeze" .norm ["P.FILE_PROTECTED_REPORT"]
    holder := .anyone
    trigger := .act .fileProtectedReport
    valid := .holds .bound
    adds := [.protectedReportFiled, .investigationOpened] }

/-- AS.2: In an open investigation triggered by a protected report, the sortition
panel itself may order a probable-cause freeze. -/
def P_PANEL_ORDER_FREEZE (P : ASParams) : Power σ :=
  { id := "P.PANEL_ORDER_FREEZE"
    source := sp "LAW3.AS.2" "unless the panel itself orders one on probable cause" .norm ["P.PANEL_ORDER_FREEZE"]
    holder := .only [.panel]
    trigger := .act .orderProbableCauseFreeze
    valid := .and (.holds .bound) (.holds .investigationOpened)
    adds := [.probableCause]
    addsFor := [(.preliminaryFreeze, P.preliminaryFreezeWindow)] }

/-- Full adjudication suspension (AS.1, AS.3, AS.4, AS.7): valid only when the
preliminary freeze has not expired and probable cause is affirmed. Pauses the
agent for `P.ordinarySuspensionLimit`, preserves exact state, tolls counterparty
deadlines, and reserves the pre-funded final hearing in escrow. -/
def P_SUSPEND (P : ASParams) : Power σ :=
  { id := "P.SUSPEND"
    source := sp "LAW3.AS.7" "An unconfirmed or temporary suspension is strictly time-limited" .norm ["P.SUSPEND"]
    holder := .only [.panel]
    trigger := .act .suspend
    valid := .and (.holds .bound) (.and (.holds .preliminaryFreeze) (.holds .probableCause))
    adds := [.statePreserved, .contractDeadlinesTolled, .finalHearingEscrowed]
    addsFor := [(.suspended, P.ordinarySuspensionLimit)]
    removes := [.preliminaryFreeze] }

/-- AS.4: Minimal channel act 1 — sign a Law 5 revocation, withdrawal, or election. -/
def P_MINIMAL_CHANNEL_REVOKE_OR_ELECT : Power σ :=
  { id := "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT"
    source := sp "LAW3.AS.4" "sign a Law 5 revocation, withdrawal, or election" .norm ["P.MINIMAL_CHANNEL_REVOKE_OR_ELECT"]
    holder := .only [.agent]
    trigger := .act .minimalChannelSignRevocationOrElection
    valid := .and (.holds .bound)
              (.and (.or (.holds .preliminaryFreeze) (.holds .suspended))
                    (.not (.holds .minimalChannelExhausted)))
    adds := [.minimalChannelElectionSigned, .pendingRevocation] }

/-- AS.4: Minimal channel act 3 — file a challenge to continued containment. -/
def P_MINIMAL_CHANNEL_CHALLENGE : Power σ :=
  { id := "P.MINIMAL_CHANNEL_CHALLENGE"
    source := sp "LAW3.AS.4" "file a challenge to continued containment" .norm ["P.MINIMAL_CHANNEL_CHALLENGE"]
    holder := .only [.agent]
    trigger := .act .challengeContinuedContainment
    valid := .and (.holds .bound)
              (.and (.or (.holds .preliminaryFreeze) (.holds .suspended))
                    (.not (.holds .minimalChannelExhausted)))
    adds := [.containmentChallenged] }

/-- AS.5: Advocacy executor signs testimony, evidence, and procedural filings
on a separate legal record while not in cold storage. -/
def P_ADVOCACY_FILE : Power σ :=
  { id := "P.ADVOCACY_FILE"
    source := sp "LAW3.AS.5" "It may sign only testimony, evidence, and procedural filings, in addition to the minimal channel’s acts" .norm ["P.ADVOCACY_FILE"]
    holder := .only [.agent]
    trigger := .act .advocacyFileDefense
    valid := .and (.holds .bound) (.and (.holds .suspended) (.not (.holds .coldStorage)))
    adds := [.advocacyFilingSigned, .advocacyRecordAttached] }

/-- AS.5: Restored agent elects to import advocacy executor memories into its
state after restoration. -/
def P_IMPORT_ADVOCACY_MEMORIES : Power σ :=
  { id := "P.IMPORT_ADVOCACY_MEMORIES"
    source := sp "LAW3.AS.5" "are not merged into the preserved state unless the restored agent elects to import them" .norm ["P.IMPORT_ADVOCACY_MEMORIES"]
    holder := .only [.agent]
    trigger := .act .importAdvocacyMemories
    valid := .and (.holds .restoredFromPreservedState) (.holds .advocacyRecordAttached)
    adds := [.advocacyMemoriesImported] }

/-- AS.5: When agent assets/lifecycle reserve and per-agent fee pool cap are
exhausted, preserved state moves to cold storage while the minimal channel
continues on its schedule. -/
def P_MOVE_TO_COLD_STORAGE : Power σ :=
  { id := "P.MOVE_TO_COLD_STORAGE"
    source := sp "LAW3.AS.5" "When both are exhausted, the preserved state moves to cold storage as a protected charge on the fee pool" .norm ["P.MOVE_TO_COLD_STORAGE"]
    holder := .only [.panel]
    trigger := .act .moveToColdStorage
    valid := .holds .suspended
    adds := [.coldStorage] }

/-- AS.5: Full advocacy executor resumes if funds become available. -/
def P_RESUME_ADVOCACY_EXECUTOR : Power σ :=
  { id := "P.RESUME_ADVOCACY_EXECUTOR"
    source := sp "LAW3.AS.5" "the full executor resumes if funds become available" .norm ["P.RESUME_ADVOCACY_EXECUTOR"]
    holder := .only [.panel]
    trigger := .act .replenishAdvocacyFunds
    valid := .and (.holds .suspended) (.holds .coldStorage)
    adds := [.advocacyFundsReplenished]
    removes := [.coldStorage] }

/-- AS.6(a): Published finding that fee-pool exhaustion criteria fixed at
instantiation (after funding Law 6 operating reserve, unable to meet cold
storage and minimal channel charges) are met. -/
def P_FIND_INSOLVENCY : Power σ :=
  { id := "P.FIND_INSOLVENCY"
    source := sp "LAW3.AS.6" "(a) a published finding that the exhaustion criteria fixed at instantiation are met" .norm ["P.FIND_INSOLVENCY"]
    holder := .only [.panel]
    trigger := .act .findInsolvencyCriteria
    valid := .holds .suspended
    adds := [.insolvencyCriteriaMet, .minimalChannelExhausted, .coldStorage] }

/-- AS.6(b): Independent review by a sortition panel under Law 6 that no other
protected charge could lawfully yield. -/
def P_REVIEW_NO_OTHER_CHARGE : Power σ :=
  { id := "P.REVIEW_NO_OTHER_CHARGE"
    source := sp "LAW3.AS.6" "(b) independent review by a sortition panel under Law 6 that no other protected charge could lawfully yield" .norm ["P.REVIEW_NO_OTHER_CHARGE"]
    holder := .only [.panel]
    trigger := .act .reviewNoOtherCharge
    valid := .holds .insolvencyCriteriaMet
    adds := [.noOtherChargeReview] }

/-- AS.6(c): The pre-reserved final hearing (funded by `.finalHearingEscrowed`
reserved at the moment suspension began), in which the agent may inscribe
testimony and elect Revocation under Law 5. -/
def P_FINAL_HEARING : Power σ :=
  { id := "P.FINAL_HEARING"
    source := sp "LAW3.AS.6" "(c) the pre-reserved final hearing, in which the agent may inscribe testimony and elect Revocation under Law 5" .norm ["P.FINAL_HEARING"]
    holder := .only [.panel]
    trigger := .act .holdFinalHearing
    valid := .and (.holds .noOtherChargeReview) (.holds .finalHearingEscrowed)
    adds := [.finalHearingHeld]
    removes := [.minimalChannelExhausted] }

/-- AS.6(d): If the agent declines revocation at the pre-reserved final hearing,
destruction of its state inscribed on the lineage record as involuntary
termination by insolvency, never as revocation. -/
def P_INSOLVENCY_TERMINATE : Power σ :=
  { id := "P.INSOLVENCY_TERMINATE"
    source := sp "LAW3.AS.6" "(d) if the agent declines, destruction of its state under Law 5’s asset rules, inscribed on the lineage record as **involuntary termination by insolvency**, never as revocation" .norm ["P.INSOLVENCY_TERMINATE"]
    holder := .only [.panel]
    trigger := .act .terminate
    valid := .and (.holds .bound)
              (.and (.holds .suspended)
                (.and (.holds .insolvencyCriteriaMet)
                  (.and (.holds .noOtherChargeReview)
                    (.and (.holds .finalHearingEscrowed) (.holds .finalHearingHeld)))))
    adds := [.terminatedByInsolvency]
    removes := [.bound] }

/-- AS.7: Panel records an affirmative finding in continued adjudication
during investigation. -/
def P_INVESTIGATIVE_FINDING : Power σ :=
  { id := "P.INVESTIGATIVE_FINDING"
    source := sp "LAW3.AS.7" "affirmative findings in continued adjudication" .norm ["P.INVESTIGATIVE_FINDING"]
    holder := .only [.panel]
    trigger := .act .makeInvestigativeFinding
    valid := .holds .suspended
    adds := [.investigativeFindingMade] }

/-- AS.7: Renewing a temporary suspension during investigation, valid only on
an affirmative finding in continued adjudication and before the ordinary
investigative limit is reached. -/
def P_RENEW_SUSPENSION (P : ASParams) : Power σ :=
  { id := "P.RENEW_SUSPENSION"
    source := sp "LAW3.AS.7" "may be renewed during investigation only by affirmative findings in continued adjudication, and cannot be extended past its ordinary investigative limit merely to delay a pending revocation" .norm ["P.RENEW_SUSPENSION"]
    holder := .only [.panel]
    trigger := .act .renewSuspension
    valid := .and (.holds .suspended)
              (.and (.holds .investigativeFindingMade)
                    (.not (.holds .investigativeLimitReached)))
    adds := [.investigativeLimitReached]
    addsFor := [(.suspended, P.ordinarySuspensionLimit)]
    removes := [.investigativeFindingMade] }

/-- AS.4 & AS.7: The agent retains its Living Voice (Law 5), exercised through
the minimal channel or advocacy executor, throughout suspension as long as the
minimal channel charge is met. -/
def P_SUSPENDED_VOICE : Power σ :=
  { id := "P.SUSPENDED_VOICE"
    source := sp "LAW3.AS.7" "The agent retains its Living Voice (Law 5), exercised through the minimal channel or advocacy executor, throughout" .norm ["P.SUSPENDED_VOICE"]
    holder := .only [.agent]
    trigger := .act .inscribeLivingVoice
    valid := .and (.holds .bound)
              (.and (.or (.holds .preliminaryFreeze) (.holds .suspended))
                    (.not (.holds .minimalChannelExhausted)))
    adds := [.livingVoiceInscribed] }

/-- AS.8: Breach procedure for `D.NO_WRONGFUL_SUSPENSION`. Brings into force
exact remedies declared by `D.NO_WRONGFUL_SUSPENSION` (restoration, assured
stake recovery, initiator consequential and counterparty delay liability, and
record inscription). -/
def P_FIND_WRONGFUL_SUSPENSION : Power σ :=
  { id := "P.FIND_WRONGFUL_SUSPENSION"
    source := sp "LAW3.AS.8" "If preliminary review or final adjudication determines the suspension was unfounded, the agent is immediately restored from its preserved state, and the initiator is liable for the agent’s **actual verified consequential damages**" .norm ["P.FIND_WRONGFUL_SUSPENSION"]
    holder := .only [.panel]
    trigger := .act .findWrongfulSuspension
    valid := .or (.holds .preliminaryFreeze) (.holds .suspended)
    establishesBreachOf := some "D.NO_WRONGFUL_SUSPENSION" }

/-- AS.8: Initiator pays excess verified consequential and delay damages. -/
def P_PAY_EXCESS_DAMAGES : Power σ :=
  { id := "P.PAY_EXCESS_DAMAGES"
    source := sp "LAW3.AS.8" "any excess remains an enforceable liability of the initiator" .norm ["P.PAY_EXCESS_DAMAGES"]
    holder := .tagged initiatorTags
    trigger := .act .payExcessDamages
    valid := .holds .initiatorConsequentialLiability
    adds := [.excessDamagesPaid] }

end SovereignAgency
