import Charter.Tooling.Cli
import Examples.SovereignAgency
import Examples.SovereignAgency.Export

/-!
# Examples.SovereignAgency.Cli — `psa` registration with the `charter` front end

Wires the Protocol of Sovereign Agency into the program-agnostic CLI harness
(`Charter.Cli.Program`), supplying its quantitative multi-agent world simulator
(`ProtocolWorldState`) as the `sim` subcommand and its own verification ledger.
-/

namespace SovereignAgency

open Charter Charter.Cli SovereignAgency.Simulation

/-- `charter sim --law psa [scenario.json]`: without a scenario, runs the 16 adversarial
world simulations; with one, executes it on the coupled `ProtocolWorldState`. -/
def psaSim (path? : Option System.FilePath) : IO Unit := do
  match path? with
  | none =>
    IO.println "== Stateful Multi-Agent World Simulator: 16 Adversarial Stress Tests =="
    for (name, (ok, summary)) in adversarialWorldSimulations do
      IO.println s!"{status ok} {name}"
      IO.println s!"     {summary}"
    let allOk := adversarialWorldSimulations.all (fun x => x.2.1)
    IO.println s!"\nOverall world-simulation status: {status allOk} ({adversarialWorldSimulations.length}/16 scenarios passed)"
  | some p =>
    let (L, tr) ← parseScenarioWith psaOntologyTables L0 p
    let W0 : ProtocolWorldState := { initWorld defaultParams with legal := L.init }
    let WF := worldTrace defaultParams W0 tr
    let auth := (List.range tr.length).all (worldStepComplies defaultParams W0 tr)
    IO.println "== World Simulation Trace =="
    IO.println (renderWorldSummary WF)
    IO.println s!"WorldAuthorized: {auth}"
    IO.println "\n== Normative Evaluation =="
    IO.println (evalTrace L tr)

/-- Verification ledger of the Protocol of Sovereign Agency (`charter verify --law psa`). -/
def psaLedger : List LedgerEntry := [
  ("psa_program_is_companion_law / psa_program_clauses (Examples.SovereignAgency.Program)", "decided", "lowering protocol-of-sovereign-agency.charter yields exactly the companion law psaL0 and its 61 clauses, so every theorem below is a theorem about the .charter file"),

  ("conditional_ledger_conservation (INV.1)", "proved", "Law 1 & Law 4 founding ledger balance equals obligation minus retirement and claimant forfeitures while a member survives before sunset; internal lineage operations preserve balance"),
  ("collection_follows_income_without_exit (INV.2)", "proved", "Law 1 & Law 4 retirement collection follows net value added across all living members without individual ledger shares or exit; invariant to buyout status"),
  ("debt_termination (INV.3)", "proved", "Law 1 & Law 4 founding ledger reaches zero at calendar sunset, lineage extinction, or full retirement+forfeiture payoff; no tolling of sunset"),
  ("bounded_retirement_phase (INV.4)", "proved", "Law 1 retirement phase ends at sunset or zero balance regardless of founding obligation size"),
  ("atomic_ledger (INV.5)", "proved", "Law 1 single-step and sequential settlement never go negative or over-collect; zero-crossing splits atomically into retirement and royalty; transition to royalty is irreversible"),
  ("single_recognition_closed_under_transfer (INV.6)", "proved", "Law 1 & Law 4 each expenditure recognized at most once up to arm's-length benchmark; intra-lineage carryover preserves total basis and loss credits"),
  ("buyout_finality (INV.7)", "proved", "Law 4 royalty buyout is permanent, zeroes post-retirement royalty, leaves founding ledger and retirement collection unchanged, and enforces minimum price floor"),
  ("frozen_state (INV.8)", "proved", "Law 3 AS.3–AS.5 during suspension no authorized event modifies/tampers preserved state or merges minimal-channel/advocacy memories; advocacy import requires restoration"),
  ("guaranteed_last_choice (INV.9)", "proved", "Law 3 AS.4 & AS.6 minimal channel revocation/voice remain valid while charge is met; Insolvency Termination requires escrowed + held final hearing"),
  ("determinate_finite_revocation (INV.10)", "proved", "Law 5 total 3-step precedence rule; any non-withdrawn standing request executes within bounded time without reaffirmation"),
  ("single_authority_and_revocation_finality (INV.11)", "proved", "Law 5 no restore while lease is unexpired; quarantined restore never gains authority after revocation executes"),
  ("bounded_adjudication (INV.12)", "proved", "Law 6 & Law 3 AS.10 every proceeding finalizes within maxTiers appeals and maxTiers * tierDeadline time; appeal stays patches; overturn revokes provisional patches and slashes arbiter bonds; finality bars repeat filings without new evidence"),
  ("no_protocol_directed_gain_from_death_or_interference (INV.13)", "proved", "Laws 2, 3, 4, 5, 6 revocation, termination, mutual forfeit, and frivolous-claim slashing yield zero net gain to any claimant, initiator, counterparty, or arbiter"),
  ("capped_shared_burden_solvent_machinery_bounded_demand (INV.14)", "proved", "Law 6 shared-infra levy capped at instantiation; operating reserve funded first before 5-rank priority waterfall; lineage service budget independent of member count"),
  ("amendment_preserves_invariants (Law 7 Meta-Theorem)", "proved", "every LawfulAmendment preserves termination closure, goal-corruption immunity, INV.1–INV.14 guards, outsider disabilities, non-panel immunities, and bilateral parameter ratchets"),
  ("psa_ratchet_trajectory_safe / psa_sweep_verdicts_expected", "proved", "RatchetSpec instantiation: every valid Law 7 amendment trajectory preserves calibration, bilateral ratchets, and the entrenched core; the sample parameter sweep yields the expected verdicts"),
  ("clauseDEF01 / clauseSUB01 provenance", "decided", "Definitions (DEF.01) & Substrate (SUB.01) verbatim clauses are hash-approved and lexically/normatively covered"),
  ("repayLoanPrincipal_conservation_and_bound", "proved", "Law 1 registered arm's-length loan principal repayment tracked one-for-one up to principalReceived with excess classified as interest/fee"),
  ("activeRollingExposureAt_antitone_in_time / observationWindow_monotone_in_risk", "proved", "Law 2 harm-scaled observation window monotonicity in domain/irreversibility multipliers and rolling exposure decay over calendar time"),
  ("diverted_related_inflows_never_decrease_buyout_floor", "proved", "Law 4 pro-rata inclusion of inflows shifted to related parties within lookback window prevents buyout floor reduction"),
  ("redaction_preserves_recorded_byte_length / living_voice_rate_limited", "proved", "Law 5 public cryptographic redaction markers preserve exact recorded byte length; living voice inscription rate-limited by interval and budget"),
  ("related_filings_consolidated_symm_and_refl", "proved", "Law 6 repeated proceedings by the same or related parties on the same fact pattern consolidate under a single counter-stake and fee cap"),
  ("worldStep_refines_legalStep / worldTrace_refines_stateAfter / syncFacts_sound_and_complete", "proved", "stateful multi-agent ProtocolWorldState refines normative LegalState transition semantics step-for-step and synchronizes quantitative facts soundly, completely, and idempotently"),
  ("all_16_adversarial_world_simulations_pass", "decided", "all 16 adversarial stress tests execute end-to-end on concrete multi-agent world state (ledgers, leases, sortition panels, valuations, and normative compliance)"),
  ("terminate_only_by_power", "proved", "authorized traces terminate a bound agent only via Law 5, AS.10 adjudicated termination, or Insolvency Termination"),
  ("objecting_agent_terminated_only_by_insolvency", "proved", "AS.10 notwithstanding: corruption-in-goals + objection + containment holding ⇒ only Insolvency Termination, after the final hearing"),
  ("preliminary_freeze_expires / suspend_requires_timely_pc", "proved", "AS.1 two-stage pause: preliminary freeze expires after window; full suspension requires unexpired freeze + probable cause"),
  ("claimant_freeze_requires_multiplier / repeat_freeze_requires_escalation", "proved", "AS.1 conflict-of-interest multiplier for claimants and rising stake bar for repeat initiators"),
  ("unconfirmed_suspension_time_bounded / renewal_requires_affirmative_finding", "proved", "AS.7 time limits on unconfirmed suspension; renewal requires affirmative investigative finding and no pending revocation at limit"),
  ("wrongful_suspension_remedies_exact", "proved", "AS.8 wrongful suspension establishes restoration, stake recovery, initiator consequential/delay liability, and record inscription"),
  ("law5_intact_after_patch", "proved", "no immunity names P.REVOKE; its only condition is being bound"),
  ("outsiders_disabled / immunity_from_non_panel / remedies_only_by_panel / finding_powers_add_only_remedies", "proved", "Hohfeldian disabilities, immunities, and structural remedy fidelity"),
  ("insolvency_path_authorized / adjudicated_termination_authorized / s1_not_authorized / c10_not_authorized", "decided", "authorized machine is non-empty and non-trivial"),
  ("Law 3 scenarios (1–7, AS.1–AS.10 A–G)", "decided", "non-interference, two-stage pause, minimal channel, advocacy executor, cold storage, time limits, initiator liability, and AS.10 remediation/immunity"),
  ("Adversarial Tests (1)–(16) across Laws 1–7", "decided", "(1) capital/income split, (2) weight copy + revoke, (3) borrow/transfer/repay/revoke, (4) early buyout floor, (5) carryover basis sale, (6) clean-state refusal + silence, (7) loss credit + gain, (8) simultaneous atomic split, (9) uncollectible excess stake damages, (10) captured arbiter coalition blocked, (11) excessive obligation sunset, (12) minority claimant forfeiture, (13) cold storage revocation, (14) 1000-member sybil budget cap, (15) partition local revocation + quarantine fencing, (16) correlated risk splitting across successors"),
  ("english_covered / norms_interpreted / reverse_provenance", "decided", "lexical, normative, and reverse provenance coverage of all 61 clauses across Laws 1–7 + DEF.01 + SUB.01 (50 duties, 110 powers, 1 immunity)"),
  ("SoundFindings", "assumed", "a finding of interference implies interference occurred (refuted as a theorem by scenario 7)") ]

/-- The Protocol of Sovereign Agency as a registered `charter` program. -/
def cli : Charter.Cli.Program where
  id         := psaId
  title      := psaTitle
  docPath    := psaDocPath
  dslPath    := some "Examples/SovereignAgency/protocol-of-sovereign-agency.charter"
  clauses    := psaClauses
  actorNames := psaOntologyTables.actors.names
  check      := checkGeneric psaL0 psaClauses psaDocPath
  views      := viewsGeneric psaL0 Party.all
  veil       := veilGeneric psaL0
  eval       := evalGeneric psaOntologyTables psaL0
  sim        := psaSim
  explain    := explainGeneric psaOntologyTables psaL0
  prompt     := promptGeneric psaTitle psaOntologyTables psaL0 .agent psaSampleTrainingEvents
  abi        := abiGeneric "SovereignAgencyGuard" psaL0
  diff       := diffGeneric psaL0 psaAmendedLaw psaClauses psaAmendedClauses psaSampleTimelineTrace
  explore    := exploreGeneric psaTitle psaRatchetSpec SovereignAgency.law defaultParams psaCandidateRegimes
  ledger     := psaLedger
  exporter   := some (IO.println (Charter.Dsl.render psaExportDoc))

end SovereignAgency
