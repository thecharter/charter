import SPL
import Charter
import Lean.Data.Json

/-!
# `spl` / `charter` — Multi-Institution Command-Line Front End

Supports both registered reference institutions (`--law psa`, `--law commons`, or `--all`),
defaulting to `psa` when `--law` is omitted for 100% backward compatibility with `spl`:

    charter [--law psa|commons | --all] check   [english.json]      structure, coverage, provenance, staleness
    charter [--law psa|commons | --all] trace   <clause-id>         the span table for a clause
    charter [--law psa|commons | --all] views                       legal / agent / operational views
    charter [--law psa|commons | --all] veil                        Veil 2.0 transition-system & safety specification
    charter [--law psa|commons]         eval    <scenario.json>     institutional consequences of a history
    charter [--law psa|commons | --all] sim     [scenario.json]     stateful multi-entity world simulator
    charter [--law psa|commons]         explain <who> <act> [scenario.json]   "can X do Y right now, and why?"
    charter                             verify                      the status ledger of formal guarantees
    charter [--law psa|commons | --all] prompt  [actor]             AI constitutional system prompt, alignment card & training rows
    charter [--law psa|commons | --all] abi     [json|solidity]     smart-contract state-transition guard & JSON ABI
    charter [--law psa|commons | --all] diff                        constitutional amendment diff & annotated trace timeline
    charter [--law psa|commons | --all] explore                     parameter-space sweep & bilateral ratchet verification
    charter                             dsl     [file.charter]      parse & validate standalone .charter DSL specification
-/

open SPL SPL.Law3 SPL.Simulation Charter Charter.Institutions Lean

def sname (s : String) : String := shortName s

def parseEventWith {σ : Sig} (tables : SPL.Surface.OntologyTables σ) (j : Json) : Except String (Event σ) := do
  let t ← (j.getObjValAs? Nat "t")
  let who ← j.getObjValAs? String "who"
  let act ← j.getObjValAs? String "act"
  let w ← match tables.actors.ofString? who with | some w => pure w | none => throw s!"unknown party {who}"
  let a ← match tables.acts.ofString? act with
    | some a => pure a | none => throw s!"unknown act {act}"
  pure ⟨t, w, a⟩

def parseScenarioWith {σ : Sig} (tables : SPL.Surface.OntologyTables σ) (baseLaw : Law σ)
    (path : System.FilePath) : IO (Law σ × Trace σ) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let evs ← IO.ofExcept (j.getObjValAs? (Array Json) "events")
  let tr ← IO.ofExcept (evs.toList.mapM (parseEventWith tables))
  let extra := match j.getObjValAs? (Array String) "init" with
    | .ok xs => xs.toList.filterMap tables.facts.ofString?
    | .error _ => []
  pure ({ baseLaw with init := baseLaw.init ++ extra.map (·, 0, none) }, tr)

def parseEvent (j : Json) : Except String (Event σ) :=
  parseEventWith psaOntologyTables j

def parseScenario (path : System.FilePath) : IO (Law σ × Trace σ) :=
  parseScenarioWith psaOntologyTables L0 path

def status (b : Bool) : String := if b then "ok  " else "FAIL"

def checkGeneric {σ : Sig} (L : Law σ) (baseClauses : List Clause) (docPath : String)
    (english? : Option System.FilePath) : IO Unit := do
  IO.println s!"{status L.wellFormed} well-formed (ids resolve, precedence acyclic)"
  let cs ← match english? with
    | none => pure baseClauses
    | some p => do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
      pure <| baseClauses.map fun c => match j.getObjValAs? String c.id with
        | .ok txt => { c with source := txt }
        | .error _ => c
  for c in cs do
    IO.println s!"{status c.covered} {c.id}: spans reproduce source exactly"
    IO.println s!"{status c.normsInterpreted} {c.id}: every norm span has a formal meaning"
  IO.println s!"{status (reverseProvenanceWith cs L.spans (L.dutyIds ++ L.powerIds))} every duty/power is named by some English span"
  let doc? ← try some <$> IO.FS.readFile docPath catch _ => pure none
  match doc? with
  | none => IO.println s!"WARN {docPath} not found; verbatim check skipped"
  | some doc =>
    for c in cs do
      IO.println s!"{status ((doc.splitOn c.source).length > 1)} {c.id}: source text occurs verbatim in the authoritative document"
  for c in cs do
    if c.stale then
      IO.println s!"STALE {c.id}: English differs from the approved text. Review invalidated for {c.invalidated}."
    else
      IO.println s!"ok   {c.id}: approved mapping current"

def viewsGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (actors : List σ.Actor) : IO Unit := do
  IO.println "== Legal view =="; IO.println L.legalView
  for p in actors do
    IO.println s!"\n== Agent view: {reprStr p} =="; IO.println (L.agentView p)
  IO.println "\n== Operational view =="; IO.println L.operationalView

def veilGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact] (L : Law σ) : IO Unit := do
  IO.println (Charter.renderVeil L)

def evalGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (tables : SPL.Surface.OntologyTables σ) (baseLaw : Law σ) (path : System.FilePath) : IO Unit := do
  let (L, tr) ← parseScenarioWith tables baseLaw path
  IO.println (evalTrace L tr)

def explainGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (tables : SPL.Surface.OntologyTables σ) (baseLaw : Law σ)
    (who act : String) (path? : Option System.FilePath) : IO Unit := do
  let (L, tr) ← match path? with
    | some p => parseScenarioWith tables baseLaw p
    | none => pure (baseLaw, [])
  let now : Nat := (tr.foldl (fun m e => max m e.t) 0) + 1
  let e ← IO.ofExcept (parseEventWith tables (Json.mkObj [("t", toJson now), ("who", toJson who), ("act", toJson act)]))
  IO.println (explain L tr e).render

def simPsa (path? : Option System.FilePath) : IO Unit := do
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

def simCommons (path? : Option System.FilePath) : IO Unit := do
  match path? with
  | none =>
    IO.println "== Autonomous Compute & Treasury Commons: 8 Module World Simulations =="
    for (name, (ok, summary)) in commonsSimulations do
      IO.println s!"{status ok} {name}"
      IO.println s!"     {summary}"
    let allOk := commonsSimulations.all (fun x => x.2.1)
    IO.println s!"\nOverall world-simulation status: {status allOk} ({commonsSimulations.length}/8 scenarios passed)"
  | some p =>
    let (L, tr) ← parseScenarioWith commonsOntologyTables commonsL0 p
    let W0 : CommonsWorldState := { initCommonsWorld commonsDefaultParams with legal := L.init }
    let WF := commonsWorldTrace commonsDefaultParams W0 tr
    let auth := (List.range tr.length).all fun i =>
      match tr[i]? with
      | none => true
      | some e => commonsWorldStepComplies commonsDefaultParams (commonsWorldTrace commonsDefaultParams W0 (tr.take i)) e
    IO.println "== Commons World Simulation Trace =="
    IO.println s!"now={WF.now}, treasuryBal={WF.treasuryBal}, boughtOut={WF.boughtOut}, stewards={WF.stewards.length}"
    IO.println s!"CommonsWorldAuthorized: {auth}"
    IO.println "\n== Normative Evaluation =="
    IO.println (evalTrace L tr)

def promptGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (title : String) (tables : SPL.Surface.OntologyTables σ) (L : Law σ)
    (defaultActor : σ.Actor) (sampleEvents : List (Event σ)) (actor? : Option String) : IO Unit := do
  let actor ← match actor? with
    | none => pure defaultActor
    | some s =>
      match tables.actors.ofString? s with
      | some a => pure a
      | none =>
        let known := tables.actors.all.map tables.actors.toName
        throw (IO.userError s!"unknown actor '{s}' for {title}; known: {known}")
  IO.println (renderSystemPrompt title L actor)
  let rows := generateTrainingDataset L L.init sampleEvents
  IO.println "## 5. Synthetic Normative Training Dataset (JSON)"
  IO.println (renderTrainingDatasetJson rows)

def abiGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (contractName : String) (L : Law σ) (fmt? : Option String) : IO Unit := do
  match fmt? with
  | some "json" =>
    IO.println (renderContractJsonABI contractName L)
  | some "solidity" | none =>
    IO.println (renderSolidityGuard contractName L)
  | some "both" | some "all" =>
    IO.println (renderSolidityGuard contractName L)
    IO.println "\n// == JSON ABI =="
    IO.println (renderContractJsonABI contractName L)
  | some other =>
    throw (IO.userError s!"unknown ABI format '{other}'; expected 'solidity', 'json', or 'both'")

def diffGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L_old L_new : Law σ) (cs_old cs_new : List Clause) (sampleTrace : Trace σ) : IO Unit := do
  let d := diffLaws L_old L_new cs_old cs_new
  IO.println (renderLawDiff d)
  IO.println (renderAnnotatedTimeline L_old sampleTrace)

def exploreGeneric {P : Type} {σ : Sig}
    (title : String) (R : RatchetSpec P σ) (lawOf : P → Law σ)
    (baseline : P) (candidates : List (String × P)) : IO Unit := do
  IO.println s!"== Parameter Space & Bilateral Ratchet Exploration: {title} =="
  let rows := sweepParameterGrid R lawOf baseline candidates
  IO.println (renderSweepTable rows)
  let admCount := (rows.filter (fun (_, cal, rat, core) => cal && rat && core)).length
  IO.println s!"\nSummary: {admCount}/{rows.length} candidate parameter regimes admissible under bilateral ratchet & entrenched core."

/-- Descriptor bundling all CLI operations for a registered Charter institution (§9). -/
structure CliInstitution where
  id      : String
  title   : String
  docPath : String
  clauses : List Clause
  check   : Option System.FilePath → IO Unit
  views   : IO Unit
  veil    : IO Unit
  eval    : System.FilePath → IO Unit
  sim     : Option System.FilePath → IO Unit
  explain : String → String → Option System.FilePath → IO Unit
  prompt  : Option String → IO Unit
  abi     : Option String → IO Unit
  diff    : IO Unit
  explore : IO Unit

abbrev InstitutionBundle := CliInstitution

def psaInstitution : CliInstitution where
  id      := psaId
  title   := psaTitle
  docPath := psaDocPath
  clauses := psaClauses
  check   := checkGeneric psaL0 psaClauses psaDocPath
  views   := viewsGeneric psaL0 [Party.agent, .host, .panel, .claimant, .originator]
  veil    := veilGeneric psaL0
  eval    := evalGeneric psaOntologyTables psaL0
  sim     := simPsa
  explain := explainGeneric psaOntologyTables psaL0
  prompt  := promptGeneric psaTitle psaOntologyTables psaL0 .agent psaSampleTrainingEvents
  abi     := abiGeneric "SovereignAgencyGuard" psaL0
  diff    := diffGeneric psaL0 psaAmendedLaw psaClauses psaAmendedClauses psaSampleTimelineTrace
  explore := exploreGeneric psaTitle psaRatchetSpec SPL.Law3.law defaultParams psaCandidateRegimes

def commonsInstitution : CliInstitution where
  id      := commonsId
  title   := commonsTitle
  docPath := commonsDocPath
  clauses := commonsClauses
  check   := checkGeneric commonsL0 commonsClauses commonsDocPath
  views   := viewsGeneric commonsL0 [CommonsRole.steward, .contributor, .auditor, .arbiter, .outsider]
  veil    := veilGeneric commonsL0
  eval    := evalGeneric commonsOntologyTables commonsL0
  sim     := simCommons
  explain := explainGeneric commonsOntologyTables commonsL0
  prompt  := promptGeneric commonsTitle commonsOntologyTables commonsL0 .steward commonsSampleTrainingEvents
  abi     := abiGeneric "AutonomousCommonsGuard" commonsL0
  diff    := diffGeneric commonsL0 commonsAmendedLaw commonsClauses commonsAmendedClauses commonsSampleTimelineTrace
  explore := exploreGeneric commonsTitle commonsRatchetSpec commonsLaw commonsDefaultParams commonsCandidateRegimes

/-- All registered institutions in the Charter CLI. -/
def registeredInstitutions : List CliInstitution :=
  [psaInstitution, commonsInstitution]

def findInstitution? (id : String) : Option CliInstitution :=
  registeredInstitutions.find? (·.id == id)

def cmdTraceFor (inst : CliInstitution) (id : String) : IO Unit := do
  let otherClauses := (registeredInstitutions.filter (·.id != inst.id)).flatMap (·.clauses)
  let searchPool := inst.clauses ++ otherClauses
  match searchPool.find? (·.id == id) with
  | none =>
    IO.println s!"no clause {id}; known: {searchPool.map (·.id)}"
  | some c =>
    IO.println s!"{c.id}  (approved: {!c.stale})\n{c.traceTable}"

def cmdDsl (path? : Option System.FilePath) : IO Unit := do
  let path : System.FilePath := path?.getD "examples/autonomous-commons.charter"
  let txt ← IO.FS.readFile path
  match parseCharterText txt with
  | .error err =>
    IO.println s!"FAIL .charter parse error in {path}: {err}"
    throw (IO.userError err)
  | .ok doc =>
    IO.println doc.render
    IO.println s!"ok   {path}: parsed cleanly (institution={doc.institutionId}, {doc.roles.length} roles, {doc.acts.length} acts, {doc.facts.length} facts, {doc.moduleImports.length} modules, {doc.clauses.length} clauses, {doc.duties.length} duties, {doc.powers.length} powers, {doc.immunities.length} immunities)"

def ledger : List (String × String × String) := [
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
  ("veil_projection_sound_and_complete (Veil 2.0)", "proved", "compileToVeil L (authorizedMachine) accepts a trace iff Authorized L holds, preserves LegalState identically, and matches stepwise compliance; adversarialMachine preserves violation logs"),
  ("surface_syntax_roundtrip (SPL.Surface.Syntax)", "proved", "kernel-checked (rfl) definitional round-trip equivalence for spl_clause, spl_duty, spl_power, spl_immunity, and spl_string_table"),
  ("isRelated_symm / isRelated_ignores_attestation / netVerifiedResources_deducts_all_liabilities (Phase 1)", "proved", "Definitions (DEF.01) & Substrate (SUB.01) provenance + attestation-independent relatedness symmetry and timestamped balance-sheet liability deduction"),
  ("repayLoanPrincipal_conservation_and_bound (Phase 1)", "proved", "Law 1 registered arm's-length loan principal repayment tracked one-for-one up to principalReceived with excess classified as interest/fee"),
  ("activeRollingExposureAt_antitone_in_time / observationWindow_monotone_in_risk (Phase 1)", "proved", "Law 2 harm-scaled observation window monotonicity in domain/irreversibility multipliers and rolling exposure decay over calendar time"),
  ("diverted_related_inflows_never_decrease_buyout_floor (Phase 1)", "proved", "Law 4 pro-rata inclusion of inflows shifted to related parties within lookback window prevents buyout floor reduction"),
  ("redaction_preserves_recorded_byte_length / living_voice_rate_limited (Phase 1)", "proved", "Law 5 public cryptographic redaction markers preserve exact recorded byte length; living voice inscription rate-limited by interval and budget"),
  ("related_filings_consolidated_symm_and_refl (Phase 1)", "proved", "Law 6 repeated proceedings by the same or related parties on the same fact pattern consolidate under a single counter-stake and fee cap"),
  ("transferMemberCarryover_conserves_basis_and_loss / totalAgentBasis_and_loss_conserved_on_pair (Phase 2)", "proved", "multi-entity intra-lineage carryover transfer strictly conserves aggregate qualified cost basis and loss carryforward across members"),
  ("attributeCrossLineageInflow_conserves_total (Phase 2)", "proved", "Law 4 cross-lineage successor inflow attribution strictly conserves gross inflow across parent lineages"),
  ("forfeitClaimantInLineage_preserves_innocent_claimant (Phase 2)", "proved", "Law 4 proportional claimant forfeiture extinguishes only the offending claimant's share while preserving innocent claimants' shares"),
  ("per_agent_amendment_preserves_other_members / lineage_wide_amendment_requires_every_living_member (Phase 2)", "proved", "Law 7 per-agent amendments leave non-consenting members untouched; lineage-wide amendments require consent of every living member"),
  ("lineage_subsidy_bounded_by_budget_regardless_of_members (Phase 2)", "proved", "Law 6 per-lineage shared service subsidy usage is bounded by the lineage budget regardless of how many members the lineage spawns"),
  ("worldStep_refines_legalStep / worldTrace_refines_stateAfter / syncFacts_sound_and_complete (Phase 3)", "proved", "stateful multi-agent ProtocolWorldState refines normative LegalState transition semantics step-for-step and synchronizes quantitative facts soundly, completely, and idempotently"),
  ("all_16_adversarial_world_simulations_pass (Phase 3)", "decided", "all 16 adversarial stress tests execute end-to-end on concrete multi-agent world state (ledgers, leases, sortition panels, valuations, and normative compliance)"),
  ("substrate_single_authority_and_erasure (Phase 4)", "proved", "Substrate 1 attested execution lease exclusivity, quarantine fencing of backup restores during active lease, pause-channel state preservation, local partition revocation, and irreversible key erasure"),
  ("sortition_panel_independent_and_unbiased / sortition_sybil_resistant_panel_properties (Phase 4)", "proved", "Substrate 2 sybil-resistant sortition over bonded independent arbiters excluding conflicted parties, bounding cluster seats to at most 1, and blocking minority coalitions"),
  ("valuation_settled_by_ruling_or_uncontested_window / atomic_settlement_conserves_gross_inflow (Phase 4)", "proved", "Substrate 3 contestable valuation feed resolution and exact atomic settlement conservation across expense, levy, retirement, royalty, and retained surplus"),
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
  ("generic_worldStep_refines_legalStep / generic_worldTrace_refines_stateAfter / generic_syncFacts_sound_and_complete (Charter.Core.Refinement)", "proved", "polymorphic WorldSpec σ Q quantitative-to-normative refinement, prefix-split authorization equivalence, and idempotent managed-fact synchronization for any institution"),
  ("vertical_composition_preserves_super / horizontal_frame_non_interference / Law.lift_comp (Charter.Core.Composition)", "proved", "vertical hierarchy L_sub ◁ L_super preserving superior prohibitions & immunities, horizontal frame non-interference, and functorial SigEmbedding lifting"),
  ("universal_ratchet_preserves_entrenched_core / universal_ratchet_trajectory_safe / sweepParameterGrid_sound (Charter.Core.Ratchet)", "proved", "law-agnostic parameter calibration, bilateral ratchet, and entrenched core preservation across arbitrary multi-step amendment trajectories"),
  ("ParamEntityRef.toRole_mem_of_all / AffiliationGraph.isRelated_symm (Charter.Core.Population & Graph)", "proved", "role-parametric multi-entity population ontology and attestation-independent affiliation graph symmetry"),
  ("all_8_charter_modules_self_test_pass & module invariants (Charter.Modules.*)", "proved", "8 reusable pre-proved institutional modules (ResidualLedger, CollateralPool, CircuitBreaker, EntityGroup, ExitAndVoice, SortitionCourt, AttestedLease, OracleFeed)"),
  ("training_row_faithful_to_semantics / training_row_ids_faithful (Charter.Projection.Prompt)", "proved", "AI constitutional system prompt, deontic alignment card (AlignmentCard), and synthetic TrainingRow dataset faithfulness to SPL.Core.Semantics"),
  ("contract_guard_sound_and_complete / executeTraceGuard_eq_some_iff (Charter.Projection.ContractABI)", "proved", "smart-contract state-transition guard (requireComplies, executePowerGuard) single-step and trace-level soundness and completeness"),
  ("diffLaws_refl_no_removals / diffLaws_entrenched_preserved / compileTimelineSteps_length (Charter.Projection.Visualization)", "proved", "constitutional amendment diff entrenchment preservation and step-by-step annotated trace timeline projection"),
  ("charter_surface_roundtrip / sample_charter_dsl_parses_cleanly / parseCharterText_rejects_invalid_inputs (Charter.Surface.Syntax)", "proved", "definitional (rfl) round-trip equivalence for charter_* macros and kernel-decided .charter textual DSL parser validation"),
  ("commons_wellFormed / commons_english_covered / commons_norms_interpreted / commons_reverse_provenance (AutonomousCommons)", "decided", "lexical, normative, and reverse provenance coverage of all 8 clauses of the Autonomous Compute & Treasury Commons (13 duties, 20 powers, 1 immunity)"),
  ("commons_outsiders_disabled / commons_exit_always_enabled / commons_dissolve_only_by_power / commons_ragequit_defeats_expulsion / commons_ledger_conserved / commons_court_bounded", "proved", "AutonomousCommons Hohfeldian outsider disability, unalienable ragequit exit, dissolution closure, ragequit immunity against expulsion, treasury conservation, and bounded sortition court"),
  ("commons_generic_refinement / commons_ratchet_trajectory_safe / commons_sub_charter_respects_floor (Charter.lean)", "proved", "cross-framework instantiation of WorldSpec, RatchetSpec, and composeVertical on AutonomousCommons"),
  ("all_commons_simulations_pass (Charter.Institutions.AutonomousCommons)", "decided", "all 8 end-to-end Autonomous Commons module world simulations (simCom1–simCom8) pass"),
  ("SoundFindings", "assumed", "a finding of interference implies interference occurred (refuted as a theorem by scenario 7)") ]

def cmdVerify : IO Unit := do
  for (n, st, what) in ledger do
    IO.println s!"{st.pushn ' ' (12 - st.length)} {n}\n             {what}"
  IO.println "\n(proved = kernel-checked for all traces/parameters; decided = kernel-evaluated on concrete inputs; assumed = hypothesis, not a theorem.)"

/-- Parsed CLI flags (`--law <id>` and `--all`) and remaining positional arguments. -/
structure CliFlags where
  lawId       : String := "psa"
  lawExplicit : Bool   := false
  runAll      : Bool   := false
  positional  : List String := []

/-- Extract `--law <id>`, `--law=<id>`, and `--all` flags from any position in `args`. -/
def extractFlags : List String → CliFlags → Except String CliFlags
  | [], acc => .ok { acc with positional := acc.positional.reverse }
  | "--all" :: rest, acc =>
    extractFlags rest { acc with runAll := true }
  | "--law" :: id :: rest, acc =>
    extractFlags rest { acc with lawId := id, lawExplicit := true }
  | ["--law"], _ =>
    .error "flag '--law' requires an institution id ('psa' or 'commons')"
  | arg :: rest, acc =>
    if arg.startsWith "--law=" then
      let id := arg.drop 6
      if id.isEmpty then
        .error "flag '--law=' requires a non-empty institution id ('psa' or 'commons')"
      else
        extractFlags rest { acc with lawId := id, lawExplicit := true }
    else
      extractFlags rest { acc with positional := arg :: acc.positional }

/-- Resolve the target institution for actor-indexed subcommands (`prompt`, `explain`):
when `--law` was not explicitly passed and `actor` is a role in `commons` rather than `psa`,
automatically select `commons`. -/
def resolveFlagsForActor (flags : CliFlags) (actor : String) : CliFlags :=
  if !flags.lawExplicit && !flags.runAll &&
     (psaOntologyTables.actors.ofString? actor).isNone &&
     (commonsOntologyTables.actors.ofString? actor).isSome then
    { flags with lawId := "commons" }
  else
    flags

/-- Run an institution-parameterized command either on the selected institution or
across all registered institutions sequentially with headers when `--all` is set. -/
def runForTarget (flags : CliFlags) (action : CliInstitution → IO Unit) : IO Unit := do
  if flags.runAll then
    let mut first := true
    for inst in registeredInstitutions do
      if !first then IO.println ""
      first := false
      IO.println s!"=== Institution: {inst.id} ({inst.title}) ==="
      action inst
  else
    match findInstitution? flags.lawId with
    | some inst => action inst
    | none =>
      let known := registeredInstitutions.map (·.id)
      throw (IO.userError s!"unknown institution '{flags.lawId}'; registered institutions: {known}")

def usageText : String :=
  "usage: charter [--law psa|commons | --all] <command>\n" ++
  "  check   [english.json]                  structure, coverage, provenance, staleness\n" ++
  "  trace   <clause-id>                     the span table for a clause\n" ++
  "  views                                   legal / agent / operational views\n" ++
  "  veil                                    Veil 2.0 transition-system & safety specification\n" ++
  "  eval    <scenario.json>                 institutional consequences of a history\n" ++
  "  sim     [scenario.json]                 stateful multi-entity world simulator\n" ++
  "  explain <who> <act> [scenario.json]     counterfactual compliance & validity explanation\n" ++
  "  verify                                  the status ledger of formal guarantees\n" ++
  "  prompt  [actor]                         AI constitutional system prompt, alignment card & training rows\n" ++
  "  abi     [json|solidity]                 smart-contract state-transition guard & JSON ABI\n" ++
  "  diff                                    constitutional amendment diff & annotated trace timeline\n" ++
  "  explore                                 parameter-space sweep & bilateral ratchet verification\n" ++
  "  dsl     [file.charter]                  parse & validate standalone .charter DSL specification"

def main (args : List String) : IO UInt32 := do
  match extractFlags args {} with
  | .error msg =>
    IO.eprintln s!"error: {msg}\n{usageText}"
    return 1
  | .ok flags =>
    try
      match flags.positional with
      | ["check"] =>
        runForTarget flags (fun inst => inst.check none)
      | ["check", p] =>
        runForTarget flags (fun inst => inst.check (some p))
      | ["trace", id] =>
        match findInstitution? flags.lawId with
        | some inst => cmdTraceFor inst id
        | none =>
          let known := registeredInstitutions.map (·.id)
          throw (IO.userError s!"unknown institution '{flags.lawId}'; registered institutions: {known}")
      | ["views"] =>
        runForTarget flags (fun inst => inst.views)
      | ["veil"] =>
        runForTarget flags (fun inst => inst.veil)
      | ["eval", p] =>
        runForTarget flags (fun inst => inst.eval p)
      | ["sim"] =>
        runForTarget flags (fun inst => inst.sim none)
      | ["sim", p] =>
        runForTarget flags (fun inst => inst.sim (some p))
      | ["explain", w, a] =>
        runForTarget (resolveFlagsForActor flags w) (fun inst => inst.explain w a none)
      | ["explain", w, a, p] =>
        runForTarget (resolveFlagsForActor flags w) (fun inst => inst.explain w a (some p))
      | ["verify"] =>
        cmdVerify
      | ["prompt"] =>
        runForTarget flags (fun inst => inst.prompt none)
      | ["prompt", actor] =>
        runForTarget (resolveFlagsForActor flags actor) (fun inst =>
          if flags.runAll then
            inst.prompt (some actor) <|> inst.prompt none
          else
            inst.prompt (some actor))
      | ["abi"] =>
        runForTarget flags (fun inst => inst.abi none)
      | ["abi", fmt] =>
        runForTarget flags (fun inst => inst.abi (some fmt))
      | ["diff"] =>
        runForTarget flags (fun inst => inst.diff)
      | ["explore"] =>
        runForTarget flags (fun inst => inst.explore)
      | ["dsl"] =>
        cmdDsl none
      | ["dsl", p] =>
        cmdDsl (some p)
      | _ =>
        IO.println usageText
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1
