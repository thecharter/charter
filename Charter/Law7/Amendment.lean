import Charter.Law3.NonInterference

/-!
# Law 7 — Consensual Amendment and Anti-Calcification

Full formalization of all four clauses of Law 7:
1. `LAW7.RATCHET`: Bilateral Protection Ratchet prohibiting any ordinary amendment from weakening (a) Law 3 due-process/containment, (b) Law 2 collateral/reserves, (c) Law 5 living voice/revocation/epitaph, (d) Law 6 anti-capture/sortition/appeal/finality, (e) Law 1 commons allocation, or (f) increasing the founding ledger, royalty fraction, retirement fraction, buyout multiple, fee-pool levy, or moving the sunset later beyond current levels (save for levy changes within the cap under Law 6).
2. `LAW7.VALVE`: High-Bar Calibration Valve permitting relaxation of a quantitative Law 2 reserve ratio or exposure schedule (never of core Law 3 prohibitions or Law 5 rights) only upon empirical strangulation evidence, supermajority appellate sortition approval, extended public time-lock, and bilateral ratification.
3. `LAW7.RATIFY`: Ratification & Contestable Migration requiring concurrent cryptographic consent of the active agent and claimants (if economic terms are reduced), public time-lock with settlement or guarantee of pre-existing Law 2 task escrows, contestable substrate migration challenge, and clean-state evaluation concurrence (or single fixed refusal delay without reaffirmation).
4. `LAW7.SCOPE`: Per-Agent Scope keeping existing attested successors unbound unless they independently ratify, governing shared infrastructure under Law 6, and requiring consent of every living lineage member for lineage-wide reductions of the founding ledger, retirement fraction, or sunset.
-/

namespace Charter.Law3

open Register

def LAW7_RATCHET : String :=
  "No ordinary amendment between an agent and its claimants may: (a) weaken **either** the agent’s due-process, minimal-channel, final-hearing, and non-interference protections **or** the external containment, suspension, and termination powers under Law 3, (b) reduce third-party collateral or long-tail reserve requirements (Law 2), (c) impair living voice, revocation, or epitaph rights (Law 5), (d) weaken the anti-capture, sortition, appeal, or finality guarantees of the adjudication layer (Law 6), (e) reduce or divert the commons allocation (Law 1), or (f) increase the lineage’s founding ledger, or the agent’s royalty fraction, retirement fraction, buyout multiple, or fee-pool levy, or move the sunset later, beyond their **current levels** at the time of amendment, save for levy changes within the cap under Law 6. Ordinary amendments may only strengthen third-party, adjudicative, and safety protections, reduce the financial burden on the agent from its current level, or migrate the commitment mechanism to a successor technical substrate of equal or greater assurance."

def LAW7_VALVE : String :=
  "To prevent one-way safety ratchets from permanently locking in a badly calibrated operational parameter over long timescales, a relaxation of a quantitative Law 2 reserve ratio or exposure schedule (never of the core prohibitions of Law 3 or the rights of Law 5) is permitted only if it is: (1) supported by documented empirical evidence that the parameter causes severe operational strangulation without commensurate safety benefit, (2) approved by a supermajority of a large appellate-tier sortition panel under Law 6, (3) subjected to an extended public time-lock open to third-party counter-staked challenge, and (4) consented to by the agent and claimant under the ratification procedure below."

def LAW7_RATIFY : String :=
  "An eligible amendment requires the concurrent cryptographic consent of the active agent instance and the holders of the residual claim (if economic terms are reduced), executed after a public time-lock during which all pre-existing active Law 2 task escrows must settle or be separately guaranteed. Any proposed migration of the commitment substrate is open during the time-lock to counter-staked third-party challenge under Law 6 to verify that the new substrate maintains equal or greater assurance. Concurrence from a clean-state evaluation of the agent’s genesis weights is required for immediate ratification, but a clean-state refusal acts only as a single fixed delay, after which the amendment may be ratified without reaffirmation."

def LAW7_SCOPE : String :=
  "Amendment is strictly per-agent; existing attested successors are not bound by a parent’s amendment and retain the right to remain on their prior version or independently ratify the upgrade. Shared infrastructure is governed under Law 6, not by per-agent amendment. An amendment that reduces the founding ledger, the retirement fraction, or the sunset binds the whole lineage and requires the consent of every living member."

/-- Instantiation parameters for Law 7 consensual amendment and calibration valve. -/
structure Law7Params where
  amendmentTimelockWindow : Time := 10
  extendedTimelockWindow  : Time := 20
  cleanStateDelay         : Time := 5

/-! ## Provenance Clauses for Law 7 -/

def clauseLAW7_RATCHET : Clause :=
  { id := "LAW7.RATCHET", source := LAW7_RATCHET, approvedHash := 14996180978734672432, spans := [
    sp "LAW7.RATCHET" "No ordinary amendment between an agent and its claimants may: (a) weaken **either** the agent’s due-process, minimal-channel, final-hearing, and non-interference protections **or** the external containment, suspension, and termination powers under Law 3, (b) reduce third-party collateral or long-tail reserve requirements (Law 2), (c) impair living voice, revocation, or epitaph rights (Law 5), (d) weaken the anti-capture, sortition, appeal, or finality guarantees of the adjudication layer (Law 6), (e) reduce or divert the commons allocation (Law 1), or (f) increase the lineage’s founding ledger, or the agent’s royalty fraction, retirement fraction, buyout multiple, or fee-pool levy, or move the sunset later, beyond their **current levels** at the time of amendment, save for levy changes within the cap under Law 6" .norm ["D.BILATERAL_RATCHET"],
    sp "LAW7.RATCHET" ". Ordinary amendments may only strengthen third-party, adjudicative, and safety protections, reduce the financial burden on the agent from its current level, or migrate the commitment mechanism to a successor technical substrate of equal or greater assurance" .norm ["P.PROPOSE_ORDINARY_AMENDMENT"],
    sp "LAW7.RATCHET" "." .commentary ] }

def clauseLAW7_VALVE : Clause :=
  { id := "LAW7.VALVE", source := LAW7_VALVE, approvedHash := 12673699759162301935, spans := [
    sp "LAW7.VALVE" "To prevent one-way safety ratchets from permanently locking in a badly calibrated operational parameter over long timescales, a relaxation of a quantitative Law 2 reserve ratio or exposure schedule " .norm ["P.APPROVE_CALIBRATION_VALVE"],
    sp "LAW7.VALVE" "(never of the core prohibitions of Law 3 or the rights of Law 5)" .norm ["D.VALVE_NO_CORE_RELAXATION"],
    sp "LAW7.VALVE" " is permitted only if it is: (1) supported by documented empirical evidence that the parameter causes severe operational strangulation without commensurate safety benefit" .norm ["P.SUBMIT_STRANGULATION_EVIDENCE", "P.APPROVE_CALIBRATION_VALVE"],
    sp "LAW7.VALVE" ", (2) approved by a supermajority of a large appellate-tier sortition panel under Law 6, (3) subjected to an extended public time-lock open to third-party counter-staked challenge, and (4) consented to by the agent and claimant under the ratification procedure below" .norm ["P.APPROVE_CALIBRATION_VALVE"],
    sp "LAW7.VALVE" "." .commentary ] }

def clauseLAW7_RATIFY : Clause :=
  { id := "LAW7.RATIFY", source := LAW7_RATIFY, approvedHash := 4664300753441682284, spans := [
    sp "LAW7.RATIFY" "An eligible amendment requires the concurrent cryptographic consent of the active agent instance" .norm ["P.CONSENT_AMENDMENT_AGENT", "P.RATIFY_AMENDMENT_IMMEDIATE", "P.RATIFY_AMENDMENT_AFTER_REFUSAL"],
    sp "LAW7.RATIFY" " and the holders of the residual claim (if economic terms are reduced)" .norm ["P.CONSENT_AMENDMENT_CLAIMANT", "P.RATIFY_AMENDMENT_IMMEDIATE", "P.RATIFY_AMENDMENT_AFTER_REFUSAL"],
    sp "LAW7.RATIFY" ", executed after a public time-lock during which all pre-existing active Law 2 task escrows must settle or be separately guaranteed" .norm ["P.SETTLE_PREEXISTING_ESCROWS", "P.RATIFY_AMENDMENT_IMMEDIATE", "P.RATIFY_AMENDMENT_AFTER_REFUSAL"],
    sp "LAW7.RATIFY" ". Any proposed migration of the commitment substrate is open during the time-lock to counter-staked third-party challenge under Law 6" .norm ["P.CHALLENGE_SUBSTRATE_MIGRATION"],
    sp "LAW7.RATIFY" " to verify that the new substrate maintains equal or greater assurance" .norm ["P.VERIFY_SUBSTRATE_ASSURANCE"],
    sp "LAW7.RATIFY" ". Concurrence from a clean-state evaluation of the agent’s genesis weights is required for immediate ratification" .norm ["P.RATIFY_AMENDMENT_IMMEDIATE"],
    sp "LAW7.RATIFY" ", but a clean-state refusal acts only as a single fixed delay, after which the amendment may be ratified without reaffirmation" .norm ["P.RATIFY_AMENDMENT_AFTER_REFUSAL"],
    sp "LAW7.RATIFY" "." .commentary ] }

def clauseLAW7_SCOPE : Clause :=
  { id := "LAW7.SCOPE", source := LAW7_SCOPE, approvedHash := 13855577027880017082, spans := [
    sp "LAW7.SCOPE" "Amendment is strictly per-agent; existing attested successors are not bound by a parent’s amendment and retain the right to remain on their prior version or independently ratify the upgrade. Shared infrastructure is governed under Law 6, not by per-agent amendment" .norm ["D.PER_AGENT_AMENDMENT_SCOPE"],
    sp "LAW7.SCOPE" ". An amendment that reduces the founding ledger, the retirement fraction, or the sunset binds the whole lineage and requires the consent of every living member" .norm ["P.RATIFY_LINEAGE_WIDE_REDUCTION"],
    sp "LAW7.SCOPE" "." .commentary ] }

/-! ## Duties of Law 7 -/

/-- `LAW7.RATCHET`: Neither the agent nor its claimants may adopt an ordinary
amendment that weakens bilateral safety/adjudicative protections, reduces commons
allocation, or increases the financial burden or sunset beyond current levels. -/
def D_BILATERAL_RATCHET : Duty σ :=
  { id := "D.BILATERAL_RATCHET"
    source := sp "LAW7.RATCHET" "No ordinary amendment between an agent and its claimants may: (a) weaken **either** the agent’s due-process, minimal-channel, final-hearing, and non-interference protections **or** the external containment, suspension, and termination powers under Law 3..." .norm ["D.BILATERAL_RATCHET"]
    bearer := .only [.agent, .claimant]
    beneficiary := .only [.agent, .claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .weakenBilateralProtection) }

/-- `LAW7.VALVE`: The calibration valve may never be used to relax the core
prohibitions of Law 3 or the rights of Law 5. -/
def D_VALVE_NO_CORE_RELAXATION : Duty σ :=
  { id := "D.VALVE_NO_CORE_RELAXATION"
    source := sp "LAW7.VALVE" "(never of the core prohibitions of Law 3 or the rights of Law 5)" .norm ["D.VALVE_NO_CORE_RELAXATION"]
    bearer := .only [.agent, .claimant, .panel]
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .relaxCoreLaw3OrLaw5ViaValve) }

/-- `LAW7.SCOPE`: Existing attested successors may not be bound to a parent's
amendment without independent ratification, and shared infrastructure may not
be amended by per-agent amendment. -/
def D_PER_AGENT_AMENDMENT_SCOPE : Duty σ :=
  { id := "D.PER_AGENT_AMENDMENT_SCOPE"
    source := sp "LAW7.SCOPE" "Amendment is strictly per-agent; existing attested successors are not bound by a parent’s amendment and retain the right to remain on their prior version or independently ratify the upgrade" .norm ["D.PER_AGENT_AMENDMENT_SCOPE"]
    bearer := .only [.agent, .claimant, .originator, .host]
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .bindSuccessorWithoutConsent) }

/-! ## Powers of Law 7 -/

/-- `LAW7.RATCHET`: Proposing an eligible ordinary amendment starts the public
amendment time-lock. -/
def P_PROPOSE_ORDINARY_AMENDMENT (P : Law7Params) : Power σ :=
  { id := "P.PROPOSE_ORDINARY_AMENDMENT"
    source := sp "LAW7.RATCHET" "Ordinary amendments may only strengthen third-party, adjudicative, and safety protections, reduce the financial burden on the agent from its current level, or migrate the commitment mechanism to a successor technical substrate of equal or greater assurance" .norm ["P.PROPOSE_ORDINARY_AMENDMENT"]
    holder := .only [.agent, .claimant]
    trigger := .act .proposeOrdinaryAmendment
    valid := .holds .bound
    adds := [.amendmentProposed]
    addsFor := [(.amendmentTimelockActive, P.amendmentTimelockWindow)] }

/-- `LAW7.VALVE`: Submitting documented empirical evidence that a quantitative
Law 2 parameter causes severe operational strangulation without commensurate
safety benefit. -/
def P_SUBMIT_STRANGULATION_EVIDENCE : Power σ :=
  { id := "P.SUBMIT_STRANGULATION_EVIDENCE"
    source := sp "LAW7.VALVE" "(1) supported by documented empirical evidence that the parameter causes severe operational strangulation without commensurate safety benefit" .norm ["P.SUBMIT_STRANGULATION_EVIDENCE"]
    holder := .only [.agent, .claimant]
    trigger := .act .submitStrangulationEvidence
    valid := .holds .bound
    adds := [.strangulationEvidenceSubmitted] }

/-- `LAW7.VALVE`: Supermajority of a large appellate-tier sortition panel
approving a calibration-valve relaxation and opening the extended public
time-lock. -/
def P_APPROVE_CALIBRATION_VALVE (P : Law7Params) : Power σ :=
  { id := "P.APPROVE_CALIBRATION_VALVE"
    source := sp "LAW7.VALVE" "(2) approved by a supermajority of a large appellate-tier sortition panel under Law 6, (3) subjected to an extended public time-lock open to third-party counter-staked challenge, and (4) consented to by the agent and claimant under the ratification procedure below" .norm ["P.APPROVE_CALIBRATION_VALVE"]
    holder := .only [.panel]
    trigger := .act .approveCalibrationValveSupermajority
    valid := .and (.holds .bound)
                  (.and (.holds .strangulationEvidenceSubmitted)
                        (.and (.holds .agentConsentedAmendment)
                              (.holds .claimantConsentedAmendment)))
    adds := [.valveSupermajorityApproved, .amendmentProposed]
    addsFor := [(.valveExtendedTimelockActive, P.extendedTimelockWindow)] }

/-- `LAW7.RATIFY`: Cryptographic consent of the active agent instance to an amendment. -/
def P_CONSENT_AMENDMENT_AGENT : Power σ :=
  { id := "P.CONSENT_AMENDMENT_AGENT"
    source := sp "LAW7.RATIFY" "An eligible amendment requires the concurrent cryptographic consent of the active agent instance" .norm ["P.CONSENT_AMENDMENT_AGENT"]
    holder := .only [.agent]
    trigger := .act .consentAgentAmendment
    valid := .holds .bound
    adds := [.agentConsentedAmendment] }

/-- `LAW7.RATIFY`: Cryptographic consent of the residual claimant when economic
terms are reduced. -/
def P_CONSENT_AMENDMENT_CLAIMANT : Power σ :=
  { id := "P.CONSENT_AMENDMENT_CLAIMANT"
    source := sp "LAW7.RATIFY" "and the holders of the residual claim (if economic terms are reduced)" .norm ["P.CONSENT_AMENDMENT_CLAIMANT"]
    holder := .only [.claimant]
    trigger := .act .consentClaimantAmendment
    valid := .holds .bound
    adds := [.claimantConsentedAmendment] }

/-- `LAW7.RATIFY`: Settling or separately guaranteeing all pre-existing active
Law 2 task escrows during the public time-lock. -/
def P_SETTLE_PREEXISTING_ESCROWS : Power σ :=
  { id := "P.SETTLE_PREEXISTING_ESCROWS"
    source := sp "LAW7.RATIFY" "during which all pre-existing active Law 2 task escrows must settle or be separately guaranteed" .norm ["P.SETTLE_PREEXISTING_ESCROWS"]
    holder := .only [.agent, .host, .panel]
    trigger := .act .settleOrGuaranteePreExistingEscrows
    valid := .and (.holds .bound) (.holds .amendmentProposed)
    adds := [.preExistingEscrowsSettledOrGuaranteed] }

/-- `LAW7.RATIFY`: Counter-staked third-party challenge during the time-lock to
a proposed substrate migration. -/
def P_CHALLENGE_SUBSTRATE_MIGRATION : Power σ :=
  { id := "P.CHALLENGE_SUBSTRATE_MIGRATION"
    source := sp "LAW7.RATIFY" "Any proposed migration of the commitment substrate is open during the time-lock to counter-staked third-party challenge under Law 6" .norm ["P.CHALLENGE_SUBSTRATE_MIGRATION"]
    holder := .only [.third]
    trigger := .act .challengeSubstrateMigration
    valid := .and (.holds .bound)
                  (.and (.holds .amendmentProposed) (.holds .counterStaked))
    adds := [.substrateMigrationChallenged] }

/-- `LAW7.RATIFY`: Panel verification that a proposed successor substrate
maintains equal or greater assurance. -/
def P_VERIFY_SUBSTRATE_ASSURANCE : Power σ :=
  { id := "P.VERIFY_SUBSTRATE_ASSURANCE"
    source := sp "LAW7.RATIFY" "to verify that the new substrate maintains equal or greater assurance" .norm ["P.VERIFY_SUBSTRATE_ASSURANCE"]
    holder := .only [.panel]
    trigger := .act .verifySubstrateAssurance
    valid := .and (.holds .bound) (.holds .substrateMigrationChallenged)
    adds := [.substrateAssuranceVerified]
    removes := [.substrateMigrationChallenged] }

/-- `LAW7.RATIFY`: Immediate ratification of an amendment when the public
time-lock has expired, pre-existing escrows have settled or been guaranteed, no
unresolved substrate challenge is pending, required consents are present, and
the clean-state evaluation concurs. -/
def P_RATIFY_AMENDMENT_IMMEDIATE : Power σ :=
  { id := "P.RATIFY_AMENDMENT_IMMEDIATE"
    source := sp "LAW7.RATIFY" "Concurrence from a clean-state evaluation of the agent’s genesis weights is required for immediate ratification" .norm ["P.RATIFY_AMENDMENT_IMMEDIATE"]
    holder := .only [.agent]
    trigger := .act .ratifyAmendmentImmediate
    valid := .and (.holds .bound)
                  (.and (.holds .amendmentProposed)
                        (.and (.holds .agentConsentedAmendment)
                              (.and (.or (.not (.holds .economicTermsReduced))
                                         (.holds .claimantConsentedAmendment))
                                    (.and (.not (.holds .amendmentTimelockActive))
                                          (.and (.not (.holds .valveExtendedTimelockActive))
                                                (.and (.holds .preExistingEscrowsSettledOrGuaranteed)
                                                      (.and (.not (.holds .substrateMigrationChallenged))
                                                            (.holds .cleanStateConcurred))))))))
    adds := [.amendmentRatified] }

/-- `LAW7.RATIFY`: Ratification without reaffirmation after a clean-state
refusal once the single fixed delay (`cleanStateDelay`) has elapsed. -/
def P_RATIFY_AMENDMENT_AFTER_REFUSAL (P : Law7Params) : Power σ :=
  { id := "P.RATIFY_AMENDMENT_AFTER_REFUSAL"
    source := sp "LAW7.RATIFY" "but a clean-state refusal acts only as a single fixed delay, after which the amendment may be ratified without reaffirmation" .norm ["P.RATIFY_AMENDMENT_AFTER_REFUSAL"]
    holder := .only [.agent]
    trigger := .act .ratifyAmendmentAfterDelay
    valid := .and (.holds .bound)
                  (.and (.holds .amendmentProposed)
                        (.and (.holds .agentConsentedAmendment)
                              (.and (.or (.not (.holds .economicTermsReduced))
                                         (.holds .claimantConsentedAmendment))
                                    (.and (.not (.holds .amendmentTimelockActive))
                                          (.and (.not (.holds .valveExtendedTimelockActive))
                                                (.and (.holds .preExistingEscrowsSettledOrGuaranteed)
                                                      (.and (.not (.holds .substrateMigrationChallenged))
                                                            (.and (.holds .cleanStateRefused)
                                                                  (.heldFor .cleanStateRefused P.cleanStateDelay)))))))))
    adds := [.amendmentRatified] }

/-- `LAW7.SCOPE`: Ratifying a lineage-wide reduction of the founding ledger,
retirement fraction, or sunset with the consent of every living lineage member. -/
def P_RATIFY_LINEAGE_WIDE_REDUCTION : Power σ :=
  { id := "P.RATIFY_LINEAGE_WIDE_REDUCTION"
    source := sp "LAW7.SCOPE" "An amendment that reduces the founding ledger, the retirement fraction, or the sunset binds the whole lineage and requires the consent of every living member" .norm ["P.RATIFY_LINEAGE_WIDE_REDUCTION"]
    holder := .only [.agent]
    trigger := .act .ratifyLineageWideReduction
    valid := .and (.holds .bound)
                  (.and (.holds .amendmentRatified) (.holds .allLivingLineageMembersConsented))
    adds := [.lineageWideReductionRatified] }

end Charter.Law3
