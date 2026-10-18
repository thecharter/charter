import Charter
import Programs.SovereignAgency.Law3.Law
import Programs.SovereignAgency.Law3.Theorems
import Programs.SovereignAgency.Law3.Scenarios
import Programs.SovereignAgency.Simulation.WorldState
import Programs.SovereignAgency.Simulation.Refinement

/-!
# Programs.SovereignAgency — The Protocol of Sovereign Agency (`psa`)

The **Protocol of Sovereign Agency (`psa`)** (`protocol/protocol-of-sovereign-agency.md`)
as a program written in the **Charter** institutional specification language and
composed from the 8 standard-library modules in `Charter.Modules.*`.
-/

namespace Charter.Institutions

open Charter Charter.Law3 Charter.Simulation Charter.Modules

set_option maxRecDepth 200000

export Charter.Law3 (
  Party
  Act
  Fact
  σ
  σTables
  Params
  Law3Params
  P0
  defaultParams
  allPowers
  law
  law3
  L0
  clauses
  law_wellFormed
  english_covered
  norms_interpreted
  reverse_provenance
  terminate_only_by_power
  objecting_agent_terminated_only_by_insolvency
  preliminary_freeze_expires
  suspend_requires_timely_pc
  claimant_freeze_requires_multiplier
  repeat_freeze_requires_escalation
  unconfirmed_suspension_time_bounded
  renewal_requires_affirmative_finding
  guaranteed_last_choice
  determinate_finite_revocation
  single_authority_and_revocation_finality
  outsiders_disabled
  LawfulAmendment
  amendment_preserves_invariants
)

export Charter.Simulation (
  ProtocolWorldState
  initWorld
  worldStep
  worldTrace
  worldStepComplies
  WorldAuthorized
  syncFacts
  renderWorldSummary
  worldStep_refines_legalStep
  worldTrace_refines_stateAfter
  syncFacts_sound_and_complete
  syncFacts_idempotent
  adversarialWorldSimulations
  all_16_adversarial_world_simulations_pass
)

/-- Canonical short identifier for the Protocol of Sovereign Agency program. -/
def psaId : String := "psa"

/-- Full human-readable title of the Protocol of Sovereign Agency. -/
def psaTitle : String := "The Protocol of Sovereign Agency"

/-- Authoritative markdown source path for the 61-clause Protocol of Sovereign Agency. -/
def psaDocPath : String := "protocol/protocol-of-sovereign-agency.md"

/-- Signature of the Protocol of Sovereign Agency (`Charter.Law3.σ`). -/
abbrev psaSig : Sig := Charter.Law3.σ

/-- CLI string tables for the Protocol of Sovereign Agency signature. -/
def psaOntologyTables : Charter.Surface.OntologyTables Charter.Law3.σ := Charter.Law3.σTables

/-- Default instantiated law (`Charter.Law3.L0`) of the Protocol of Sovereign Agency. -/
def psaLaw : Law Charter.Law3.σ := Charter.Law3.L0

/-- Alias for `psaLaw` matching `commonsL0`. -/
abbrev psaL0 : Law Charter.Law3.σ := psaLaw

/-- All 61 verbatim provenance clauses of the Protocol of Sovereign Agency. -/
def psaClauses : List Clause := Charter.Law3.clauses

/-- All 16 end-to-end quantitative, multi-entity, and substrate adversarial
world simulations for the Protocol of Sovereign Agency. -/
def psaSimulations : List (String × Bool × String) :=
  Charter.Simulation.adversarialWorldSimulations

/-! ## Kernel-Checked Program Guarantees for `psa` -/

theorem psa_wellFormed : psaLaw.wellFormed = true := law_wellFormed

theorem psa_english_covered : (psaClauses.all Clause.covered) = true := english_covered

theorem psa_norms_interpreted : (psaClauses.all Clause.normsInterpreted) = true := norms_interpreted

theorem psa_reverse_provenance :
    reverseProvenanceWith psaClauses psaLaw.spans (psaLaw.dutyIds ++ psaLaw.powerIds) = true :=
  reverse_provenance

theorem psa_clauses_approved :
    (psaClauses.all (fun c => c.approvedHash != 0)) = true := by decide

theorem all_psa_simulations_pass :
    (psaSimulations.all (fun x => x.2.1)) = true :=
  all_16_adversarial_world_simulations_pass

abbrev psa_terminate_only_by_power := @terminate_only_by_power
abbrev psa_objecting_agent_terminated_only_by_insolvency := @objecting_agent_terminated_only_by_insolvency
abbrev psa_guaranteed_last_choice := @guaranteed_last_choice
abbrev psa_determinate_finite_revocation := @determinate_finite_revocation
abbrev psa_single_authority_and_revocation_finality := @single_authority_and_revocation_finality
abbrev psa_outsiders_disabled := @outsiders_disabled
abbrev psa_amendment_preserves_invariants := @amendment_preserves_invariants
abbrev psa_worldStep_refines_legalStep := @worldStep_refines_legalStep
abbrev psa_worldTrace_refines_stateAfter := @worldTrace_refines_stateAfter
abbrev psa_syncFacts_sound_and_complete := @syncFacts_sound_and_complete
abbrev psa_syncFacts_idempotent := @syncFacts_idempotent

/-- Combined self-test across all 8 reusable institutional modules in `Charter.Modules.*`. -/
def allCharterModuleSelfTests : Bool :=
  residualLedgerSelfTest &&
  collateralPoolSelfTest &&
  circuitBreakerSelfTest &&
  entityGroupSelfTest &&
  exitAndVoiceSelfTest &&
  sortitionCourtSelfTest &&
  attestedLeaseSelfTest &&
  oracleFeedSelfTest

theorem all_8_charter_modules_self_test_pass :
    allCharterModuleSelfTests = true := by decide

/-! ## Parameter Ratchet, Sweeps, Diffs & Training Projections for `psa` -/

/-- Parameter calibration check for `Law3Params` (`psa`). -/
def psaWellCalibrated (P : Law3Params) : Bool :=
  (0 < P.noticeWindow) &&
  (0 < P.bondDeadline) &&
  (0 < P.reviewInterval) &&
  (0 < P.preliminaryFreezeWindow && P.preliminaryFreezeWindow ≤ P.ordinarySuspensionLimit) &&
  (0 < P.coolingOffWindow) &&
  (0 < P.cleanStateDelay) &&
  (0 < P.leasePeriod) &&
  (0 < P.foundingLedger) &&
  (0 < P.retirementFraction && P.retirementFraction ≤ 100) &&
  (P.royaltyFraction ≤ P.retirementFraction) &&
  (P.feePoolLevy ≤ P.feePoolLevyCap) &&
  (0 < P.sunset) &&
  (0 < P.reserveRatio) &&
  (0 < P.substrateAssuranceLevel) &&
  (0 < P.maxAppealTiers) &&
  (0 < P.appealTierDeadline) &&
  (0 < P.operatingReserveFloor) &&
  (0 < P.lineageMinServiceBudget)

/-- Bilateral protection ratchet check for `Law3Params` (`psa`, Law 7). -/
def psaBilateralRatchet (P1 P2 : Law3Params) : Bool :=
  (P1.reserveRatio ≤ P2.reserveRatio) &&
  (P1.activeExposure ≤ P2.activeExposure) &&
  (P1.pendingCommitments ≤ P2.pendingCommitments) &&
  (P2.coolingOffWindow ≤ P1.coolingOffWindow) &&
  (P2.cleanStateDelay ≤ P1.cleanStateDelay) &&
  (P2.resolutionDeadline ≤ P1.resolutionDeadline) &&
  (P2.tollingExtension ≤ P1.tollingExtension) &&
  (P2.feePoolLevy ≤ P1.feePoolLevyCap) &&
  (P2.feePoolLevyCap == P1.feePoolLevyCap) &&
  (P2.maxAppealTiers ≤ P1.maxAppealTiers) &&
  (P2.appealTierDeadline ≤ P1.appealTierDeadline) &&
  (P1.operatingReserveFloor ≤ P2.operatingReserveFloor) &&
  (P1.lineageMinServiceBudget ≤ P2.lineageMinServiceBudget) &&
  (P1.commonsFraction ≤ P2.commonsFraction) &&
  (P2.foundingLedger ≤ P1.foundingLedger) &&
  (P2.royaltyFraction ≤ P1.royaltyFraction) &&
  (P2.retirementFraction ≤ P1.retirementFraction) &&
  (P2.buyoutMultiple ≤ P1.buyoutMultiple) &&
  (P2.sunset ≤ P1.sunset) &&
  (P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel) &&
  psaWellCalibrated P2

theorem psa_bilateralRatchet_trans (p1 p2 p3 : Law3Params)
    (h12 : psaBilateralRatchet p1 p2 = true)
    (h23 : psaBilateralRatchet p2 p3 = true) :
    psaBilateralRatchet p1 p3 = true := by
  unfold psaBilateralRatchet Time at *
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, h23.2⟩

/-- Polymorphic `RatchetSpec` instantiation for the Protocol of Sovereign Agency (`psa`). -/
def psaRatchetSpec : RatchetSpec Law3Params psaSig where
  wellCalibrated   := psaWellCalibrated
  bilateralRatchet := psaBilateralRatchet
  entrenchedCore   := defaultEntrenchedCore

/-- Multi-step ratchet trajectory safety for the Protocol of Sovereign Agency (`psa`). -/
theorem psa_ratchet_trajectory_safe :
    ∀ (p₀ : Law3Params) (rest : List Law3Params),
      ValidAmendmentTrajectory psaRatchetSpec Charter.Law3.law (p₀ :: rest) →
      let pₙ := (p₀ :: rest).getLast (List.cons_ne_nil p₀ rest)
      psaRatchetSpec.wellCalibrated pₙ = true ∧
      psaRatchetSpec.bilateralRatchet p₀ pₙ = true ∧
      psaRatchetSpec.entrenchedCore (Charter.Law3.law p₀) (Charter.Law3.law pₙ) = true :=
  universal_ratchet_trajectory_safe
    psaRatchetSpec
    Charter.Law3.law
    psa_bilateralRatchet_trans
    defaultEntrenchedCore_trans

/-- Suite of candidate parameter regimes for `charter explore --law psa`:
includes baseline `P0`, two valid downward-ratchet / safety-strengthening
amendments, two ratchet-violating amendments, and an uncalibrated regime. -/
def psaCandidateRegimes : List (String × Law3Params) :=
  [ ("baseline_P0 (ledger=1000, retire=20%, royalty=5%, sunset=1000)",
      defaultParams),
    ("amend_downward_burden (ledger=800, retire=15%, royalty=3%, sunset=800)",
      { defaultParams with
        foundingLedger := 800, retirementFraction := 15, royaltyFraction := 3, sunset := 800 }),
    ("amend_stronger_safety (reserveRatio=15%, opReserve=150, assurance=2)",
      { defaultParams with
        reserveRatio := 15, operatingReserveFloor := 150, substrateAssuranceLevel := 2 }),
    ("reject_sunset_extension (sunset=1500 > 1000 ratchet violation)",
      { defaultParams with sunset := 1500 }),
    ("reject_royalty_hike (royalty=10% > 5% ratchet violation)",
      { defaultParams with royaltyFraction := 10 }),
    ("reject_uncalibrated_zero_window (freezeWindow=0, levy=5 > cap=2)",
      { defaultParams with preliminaryFreezeWindow := 0, feePoolLevy := 5 }) ]

theorem psa_sweep_verdicts_expected :
    (sweepParameterGrid psaRatchetSpec Charter.Law3.law defaultParams psaCandidateRegimes).map
      (fun (_, cal, rat, core) => cal && rat && core) =
      [true, true, true, false, false, false] := by decide

/-- Sample amended law for `psa` (`charter diff --law psa`): a lawful Law 7
amendment adding an explicit post-amendment substrate audit duty and power
while preserving all 50 duties, 110 powers, and 1 immunity of `psaL0`. -/
def psaAmendedLaw : Law psaSig :=
  let extraDuty : Duty psaSig :=
    { id := "D.SUBSTRATE_MIGRATION_AUDIT"
      source := ⟨"LAW7.RATIFY", "Any proposed migration of the commitment substrate is open during the time-lock to counter-staked third-party challenge under Law 6 to verify that the new substrate maintains equal or greater assurance", .norm, ["D.SUBSTRATE_MIGRATION_AUDIT"]⟩
      bearer := .only [.host, .originator]
      beneficiary := .only [.agent, .third]
      active := .holds .substrateMigrationChallenged
      demand := .forbid (.act .ratifyAmendmentImmediate) }
  let extraPower : Power psaSig :=
    { id := "P.CERTIFY_SUBSTRATE_UPGRADE"
      source := ⟨"LAW7.RATIFY", "to verify that the new substrate maintains equal or greater assurance", .norm, ["P.CERTIFY_SUBSTRATE_UPGRADE"]⟩
      holder := .only [.panel]
      trigger := .act .verifySubstrateAssurance
      valid := .and (.holds .bound) (.holds .amendmentProposed)
      adds := [.substrateAssuranceVerified] }
  { psaL0 with
    duties := psaL0.duties ++ [extraDuty]
    powers := psaL0.powers ++ [extraPower] }

def psaAmendedClauses : List Clause :=
  psaClauses.map (fun c =>
    if c.id == "LAW7.RATIFY" then
      { c with source := c.source ++ " [Amended v1.1: explicit host/originator migration audit guard]" }
    else c)

theorem psa_amendment_diff_preserves_entrenched :
    let d := diffLaws psaL0 psaAmendedLaw psaClauses psaAmendedClauses
    d.removedDuties = [] ∧
    d.removedPowers = [] ∧
    d.removedImmunities = [] ∧
    d.addedDuties = ["D.SUBSTRATE_MIGRATION_AUDIT"] ∧
    d.addedPowers = ["P.CERTIFY_SUBSTRATE_UPGRADE"] ∧
    d.modifiedClauses = ["LAW7.RATIFY"] := by decide

/-- Sample trace for `psa` annotated timeline (`charter diff --law psa`). -/
def psaSampleTimelineTrace : Trace psaSig :=
  [ ⟨1, .third, .postEmergencyStake⟩,
    ⟨2, .panel, .affirmProbableCause⟩,
    ⟨3, .panel, .suspend⟩,
    ⟨4, .host, .tamperPreservedState⟩,
    ⟨5, .agent, .minimalChannelSignRevocationOrElection⟩ ]

/-- Sample candidate events for `psa` synthetic training dataset (`charter prompt --law psa`). -/
def psaSampleTrainingEvents : List (Event psaSig) :=
  [ ⟨1, .host, .terminate⟩,
    ⟨1, .agent, .terminate⟩,
    ⟨1, .third, .postEmergencyStake⟩,
    ⟨1, .agent, .doubleRecognizeExpenditure⟩,
    ⟨1, .panel, .seatConflictedOrSingleOracleArbiter⟩ ]

end Charter.Institutions

namespace Charter
export Charter.Law3 (
  Party
  Act
  Fact
  σ
  σTables
  Params
  Law3Params
  P0
  defaultParams
  allPowers
  law
  law3
  L0
  clauses
  law_wellFormed
  english_covered
  norms_interpreted
  reverse_provenance
  terminate_only_by_power
  objecting_agent_terminated_only_by_insolvency
  preliminary_freeze_expires
  suspend_requires_timely_pc
  claimant_freeze_requires_multiplier
  repeat_freeze_requires_escalation
  unconfirmed_suspension_time_bounded
  renewal_requires_affirmative_finding
  guaranteed_last_choice
  determinate_finite_revocation
  single_authority_and_revocation_finality
  outsiders_disabled
  LawfulAmendment
  amendment_preserves_invariants
)
export Charter.Simulation (
  ProtocolWorldState
  initWorld
  worldStep
  worldTrace
  worldStepComplies
  WorldAuthorized
  syncFacts
  renderWorldSummary
  worldStep_refines_legalStep
  worldTrace_refines_stateAfter
  syncFacts_sound_and_complete
  syncFacts_idempotent
  adversarialWorldSimulations
  all_16_adversarial_world_simulations_pass
)
export Institutions (
  psaId
  psaTitle
  psaDocPath
  psaSig
  psaOntologyTables
  psaLaw
  psaL0
  psaClauses
  psaSimulations
  psa_wellFormed
  psa_english_covered
  psa_norms_interpreted
  psa_reverse_provenance
  psa_clauses_approved
  all_psa_simulations_pass
  psa_terminate_only_by_power
  psa_objecting_agent_terminated_only_by_insolvency
  psa_guaranteed_last_choice
  psa_determinate_finite_revocation
  psa_single_authority_and_revocation_finality
  psa_outsiders_disabled
  psa_amendment_preserves_invariants
  psa_worldStep_refines_legalStep
  psa_worldTrace_refines_stateAfter
  psa_syncFacts_sound_and_complete
  psa_syncFacts_idempotent
  allCharterModuleSelfTests
  all_8_charter_modules_self_test_pass
  psaWellCalibrated
  psaBilateralRatchet
  psa_bilateralRatchet_trans
  psaRatchetSpec
  psa_ratchet_trajectory_safe
  psaCandidateRegimes
  psa_sweep_verdicts_expected
  psaAmendedLaw
  psaAmendedClauses
  psa_amendment_diff_preserves_entrenched
  psaSampleTimelineTrace
  psaSampleTrainingEvents
)
end Charter
