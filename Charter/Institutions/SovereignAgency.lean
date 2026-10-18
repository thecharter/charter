import Charter.Modules.ResidualLedger
import Charter.Modules.CollateralPool
import Charter.Modules.CircuitBreaker
import Charter.Modules.EntityGroup
import Charter.Modules.ExitAndVoice
import Charter.Modules.SortitionCourt
import Charter.Modules.AttestedLease
import Charter.Modules.OracleFeed
import SPL.Core.Views
import SPL.Core.Explain
import SPL.Law3.Law
import SPL.Law3.Theorems
import SPL.Law3.Scenarios
import SPL.Simulation.WorldState
import SPL.Simulation.Refinement


/-!
# Charter.Institutions.SovereignAgency — Flagship Reference Institution (`psa`)

Packages the 61-clause **Protocol of Sovereign Agency (`psa`)** as the flagship
reference institution of the Charter framework, composed from all 8 reusable
institutional modules in `Charter.Modules.*`.
-/

namespace Charter.Institutions

open SPL SPL.Law3 SPL.Simulation Charter.Modules

set_option maxRecDepth 200000

export SPL.Law3 (
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

export SPL.Simulation (
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

/-- Canonical short identifier for the Protocol of Sovereign Agency institution. -/
def psaId : String := "psa"

/-- Full human-readable title of the Protocol of Sovereign Agency. -/
def psaTitle : String := "The Protocol of Sovereign Agency"

/-- Authoritative markdown source path for the 61-clause Protocol of Sovereign Agency. -/
def psaDocPath : String := "protocol/protocol-of-sovereign-agency.md"

/-- Signature of the Protocol of Sovereign Agency (`SPL.Law3.σ`). -/
abbrev psaSig : Sig := SPL.Law3.σ

/-- CLI string tables for the Protocol of Sovereign Agency signature. -/
def psaOntologyTables : SPL.Surface.OntologyTables SPL.Law3.σ := SPL.Law3.σTables

/-- Default instantiated law (`SPL.Law3.L0`) of the Protocol of Sovereign Agency. -/
def psaLaw : Law SPL.Law3.σ := SPL.Law3.L0

/-- Alias for `psaLaw` matching `commonsL0`. -/
abbrev psaL0 : Law SPL.Law3.σ := psaLaw

/-- All 61 verbatim provenance clauses of the Protocol of Sovereign Agency. -/
def psaClauses : List Clause := SPL.Law3.clauses

/-- All 16 end-to-end quantitative, multi-entity, and substrate adversarial
world simulations for the Protocol of Sovereign Agency. -/
def psaSimulations : List (String × Bool × String) :=
  SPL.Simulation.adversarialWorldSimulations

/-! ## Kernel-Checked Institution Guarantees for `psa` -/

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

end Charter.Institutions

namespace Charter
export SPL.Law3 (
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
export SPL.Simulation (
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
)
end Charter

