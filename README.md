# Charter (v0.2.0) — Formally Verified Institutional Specification, Composition & Projection Language

**Charter** is a formally verified language, standard library, and multi-target compiler in Lean 4 for specifying, composing, verifying, simulating, and projecting institutional rules across human readers, AI systems, and computational state machines.

The repository is cleanly divided into two layers:

1. **`Charter` (`Charter.lean` + `Charter/`) — The Charter Language & Standard Library** (100% domain- and institution-agnostic):
   - **`Charter.Core`**: Law-agnostic Hohfeldian syntax & semantics (`Duty`, `Power`, `Immunity`, `Law σ`), verbatim English provenance (`Clause`, `Span`, `Register`, `AuthorshipQuestion`), views (`legalView`, `agentView`, `operationalView`), counterfactual explanation engine (`explain`), polymorphic quantitative-to-normative refinement (`WorldSpec`), vertical & horizontal law composition (`composeVertical`, `composeHorizontal`, `SigEmbedding`, `LawInterface`), universal bilateral parameter ratchets (`RatchetSpec`), role-parametric population ontology (`ParamEntityRef`), and generic affiliation graphs (`AffiliationGraph`, `VerifiedBalanceSheet`).
   - **`Charter.Modules`**: 8 reusable, pre-proved institutional standard-library modules (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`, `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`).
   - **`Charter.Substrate`**: Cryptographic execution lease attestation, Sybil-resistant sortition, and contestable valuation settlement primitives.
   - **`Charter.Projection`**: Verified projections for all three target audiences — **Veil 2.0** state machines (`Veil`), **AI Constitutional System Prompts**, Deontic Alignment Cards & synthetic RLHF/alignment `TrainingRow` datasets (`Prompt`), **Smart-Contract State-Transition Guards** in Solidity & JSON ABI (`ContractABI`), and step-by-step **Annotated Trace Timelines & Constitutional Amendment Diffs** (`Visualization`).
   - **`Charter.Surface`**: Two-layer surface language combining kernel-checked Lean 4 macros (`charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_string_table`, `charter_institution`) and a total, kernel-decided parser (`parseCharterText`) for standalone `.charter` files (`examples/autonomous-commons.charter`).

2. **`Programs` (`Programs.lean` + `Programs/`) — Programs Written in Charter** (`import Charter`):
   - **`Programs.SovereignAgency` (`psa`) — *The Protocol of Sovereign Agency*** (`protocol/protocol-of-sovereign-agency.md`): A 61-clause institutional program written in Charter (`Programs/SovereignAgency/Law1`–`Law7`, `Definitions`, `Simulation`) with 50 duties, 110 powers, 1 immunity, 14 proved Design Invariants (`INV.1`–`INV.14`), the Law 7 Meta-Theorem, and 16 adversarial multi-agent world simulations.
   - **`Programs.AutonomousCommons` (`commons`) — *The Autonomous Compute & Treasury Commons*** (`protocol/autonomous-commons-charter.md`, `examples/autonomous-commons.charter`): An 8-clause institutional program written in Charter over a 5-role signature (`σ_commons`) with 13 duties, 20 powers, 1 immunity, and 8 multi-entity world simulations.

Build: `lake build && lake build charter` (Lean 4.24, no Mathlib, no external dependencies).
Check trust: `grep -rn "sorry\|native_decide\|axiom " Charter/ Programs/ Main.lean Charter.lean Programs.lean` is empty; every general theorem depends at most on Lean's standard `propext`, `Classical.choice`, `Quot.sound`, and every decided scenario depends on no axioms at all (`{}`).

## Repository Layout

```
── THE CHARTER LANGUAGE & STANDARD LIBRARY (Charter/) ──────────────────────────
Charter.lean                                Pure Charter language, compiler & standard-library umbrella
Charter/Core/Provenance.lean                Spans, registers, lexical/normative/reverse coverage & AuthorshipQuestion
Charter/Core/Syntax.lean                    Typed Hohfeldian normative AST (Duty, Power, Immunity, Law σ)
Charter/Core/Semantics.lean                 Occurrence, compliance, and institutional validity semantics
Charter/Core/Views.lean                     Generated legal, per-actor, operational, and trace views
Charter/Core/Explain.lean                   Step-by-step counterfactual explanation engine
Charter/Core/Graph.lean                     Law-agnostic AffiliationGraph & VerifiedBalanceSheet
Charter/Core/Population.lean                Role-parametric ParamEntityRef Role & multi-entity population conservation
Charter/Core/Refinement.lean                Polymorphic WorldSpec σ Q & GenericWorldState refinement theorems
Charter/Core/Composition.lean               Vertical (L_sub ◁ L_super) & horizontal (L₁ ⊕ L₂) composition, SigEmbedding & LawInterface
Charter/Core/Ratchet.lean                   Universal RatchetSpec P σ, ValidAmendmentTrajectory & sweepParameterGrid
Charter/Modules/ResidualLedger.lean         Module 1: Non-interest residual ledger, sunset, royalty & buyout floor
Charter/Modules/CollateralPool.lean         Module 2: Harm-scaled bonding, rolling exposure decay & long-tail reserve
Charter/Modules/CircuitBreaker.lean         Module 3: Two-stage emergency freeze, probable cause & frozen-state protection
Charter/Modules/EntityGroup.lean            Module 4: Multi-member group ledgers, carryover basis & innocent isolation
Charter/Modules/ExitAndVoice.lean           Module 5: Deterministic unilateral exit precedence & rate-limited voice
Charter/Modules/SortitionCourt.lean         Module 6: Sybil-resistant sortition, bounded appeals & priority fee waterfall
Charter/Modules/AttestedLease.lean          Module 7: Time-bounded single operating lease, quarantine fencing & key erasure
Charter/Modules/OracleFeed.lean             Module 8: Contestable valuation feeds & atomic settlement conservation
Charter/Substrate/Attestation.lean          Substrate 1: Attested execution leases, quarantine fencing & irreversible key erasure
Charter/Substrate/Sortition.lean            Substrate 2: Sybil-resistant sortition, conflict/cluster filtering & supermajority
Charter/Substrate/Settlement.lean           Substrate 3: Contestable valuation resolution & atomic settlement conservation
Charter/Projection/Veil.lean                Veil 2.0 transition-system lowering & preservation theorem
Charter/Projection/Prompt.lean              AI Constitutional System Prompts, AlignmentCard & synthetic TrainingRow JSON
Charter/Projection/ContractABI.lean         Smart-contract state-transition guard (requireComplies, executePowerGuard, Solidity & JSON ABI)
Charter/Projection/Visualization.lean       Step-by-step annotated trace timelines & LawDiff amendment entrenchment audit
Charter/Surface/Syntax.lean                 charter_* Lean 4 macros & standalone .charter textual DSL parser (parseCharterText)

── PROGRAMS WRITTEN IN CHARTER (Programs/) ─────────────────────────────────────
Programs.lean                               Umbrella module for programs written in Charter
Programs/SovereignAgency.lean               Program 1 (psa): The Protocol of Sovereign Agency (61 clauses, 16 sims)
Programs/SovereignAgency/Definitions.lean   PSA DEF.01 & SUB.01 verbatim provenance clauses
Programs/SovereignAgency/Law1/Ledger.lean   PSA Law 1: Founding Ledger, Sunset, Value-Added, Carryover Basis & LoanLedger
Programs/SovereignAgency/Law2/Collateral.lean       PSA Law 2: Collateralized Action, Exposure Aggregation & Mutual Forfeit
Programs/SovereignAgency/Law3/NonInterference.lean  PSA Law 3: Non-Interference, Ontology, Host Notice & Penalties
Programs/SovereignAgency/Law3/IntegrityFloor.lean   PSA Law 3: 5-point Agent Integrity Floor
Programs/SovereignAgency/Law3/Suspension.lean       PSA Law 3: Adjudicated Suspension (AS.1–AS.9) & Insolvency Termination
Programs/SovereignAgency/Law3/Remediation.lean      PSA Law 3: Remediation, Goal-Patch Immunity & Periodic Review (AS.10)
Programs/SovereignAgency/Law4/Lineage.lean          PSA Law 4: Lineage Attestation, Ledger Conservation, Forfeiture & Buyout Floor
Programs/SovereignAgency/Law5/Revocation.lean       PSA Law 5: Living Voice, Revocation Precedence, Leases & Epitaph Redaction
Programs/SovereignAgency/Law6/Adjudication.lean     PSA Law 6: Sortition, Appeal Tiers, Finality Consolidation & Fee Waterfall
Programs/SovereignAgency/Law7/Amendment.lean        PSA Law 7: Bilateral Ratchet, Calibration Valve & Per-Agent Scope
Programs/SovereignAgency/Law3/Law.lean              Unified assembly of all 61 PSA clauses across Laws 1–7 + DEF.01 + SUB.01
Programs/SovereignAgency/Law3/Scenarios.lean        Decided histories & all 16 Adversarial Tests across Laws 1–7
Programs/SovereignAgency/Law3/Theorems.lean         Design Invariants INV.1–INV.14, Law 7 Meta-Theorem & Sub-Mechanisms
Programs/SovereignAgency/Simulation/WorldState.lean Unified quantitative + normative ProtocolWorldState & syncFacts
Programs/SovereignAgency/Simulation/Refinement.lean Refinement theorems & 16 end-to-end adversarial world simulations
Programs/AutonomousCommons.lean             Program 2 (commons): The Autonomous Compute & Treasury Commons (8 clauses, 8 sims)

── CLI, SPECIFICATIONS & DOCUMENTATION ─────────────────────────────────────────
Main.lean                                   Multi-program CLI (compiled to .lake/build/bin/charter)
protocol/protocol-of-sovereign-agency.md    Authoritative English text for psa (61 clauses)
protocol/autonomous-commons-charter.md      Authoritative English text for commons (8 clauses)
examples/autonomous-commons.charter         Standalone .charter DSL specification for commons
docs/charter-spec.md                        Charter Language Specification (architecture & semantic commitments)
docs/law3-views.txt                         Generated legal, agent, and operational views for PSA
```

## The Semantic Commitments of Charter

1. **Duties, powers and declared immunities are the primitives.** A
   `Duty` is a record: bearer, beneficiary, activation condition, demand
   (forbid / require-within), scope exception, power exceptions, override
   priority, breach procedure, remedies. A `Power` is: holder, triggering
   act, validity condition, permanent/time-bounded/actor-tagged institutional
   effects. An `Immunity` names the powers it defeats, while a condition holds,
   unless an exception holds. Claim-rights, privileges, disabilities and liabilities are
   *defined* from these.
2. **Three independent questions about every event.** Occurrence (any
   event can occur; a trace is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). An
   unlawful act may be valid (a fabricated claim is filed); a lawful act may
   be void (a panel suspension without probable cause changes nothing).
3. **Violations are facts in the record, not findings.** `violations L tr`
   lists breaches as they occurred. A finding is the valid exercise of a
   panel's power whose validity conditions mention a claim and evidence;
   its effect is exactly the breached duty's declared remedies. The link
   from finding to fact is an explicit assumption (`SoundFindings`), shown
   by counterexample not to be a theorem.
4. **Exceptions come in three kinds** and are kept apart: scope conditions
   (`unlessCond`), authority (`unlessPower`: the same act is lawful iff it is the
   valid exercise of a named power), and explicit precedence (`overriddenBy`,
   cycle-checked). Consequences of breach are remedies, never exceptions.
5. **The authorized machine is derived and projected to Veil 2.0 & Smart-Contract Guards.**
   `Authorized L tr` is the set of traces in which every event complies.
   `Charter.Projection.Veil` compiles any `Law σ` into both an
   `authorizedMachine` and an `adversarialMachine`, with machine-checked soundness and
   completeness (`veil_projection_sound_and_complete`). `Charter.Projection.ContractABI`
   lowers any `Law σ` to a deterministic state-transition guard (`requireComplies`,
   `executePowerGuard`) with proved single-step and trace-level soundness and completeness
   (`contract_guard_sound_and_complete`).
6. **Every norm carries its English.** Every clause in a Charter program is partitioned
   into exact character spans across five registers (`norm`, `invariant`, `acceptance`,
   `definition`, `commentary`), verified verbatim against its authoritative Markdown document.

## Charter Language Architecture (`Charter/`)

### 1. Universal Normative & Compositional Core (`Charter.Core`)

| Module | Key Definitions & Theorems | Formal Guarantee |
|---|---|---|
| `Charter.Core.Refinement` | `WorldSpec σ Q`, `GenericWorldState σ Q`, `generic_worldStep_refines_legalStep`, `generic_worldTrace_refines_stateAfter`, `generic_worldAuthorized_iff_prefix_split`, `generic_syncFacts_sound_and_complete`, `generic_syncFacts_idempotent` | Proves once for all signatures `σ` and quantitative state types `Q` that world execution refines `stateAfter`, `GenericWorldAuthorized ↔ Authorized`, and `genericSyncFacts` is sound, complete, and idempotent |
| `Charter.Core.Composition` | `composeVertical` (`L_sub ◁ L_super`), `composeHorizontal`, `SigEmbedding`, `Law.lift`, `LawInterface`, `vertical_composition_preserves_super_prohibitions`, `vertical_composition_preserves_super_immunities`, `horizontal_frame_non_interference` | Proves that subordinate bylaws cannot excuse superior core prohibitions or override active superior immunities, and that disjoint horizontal modules satisfy frame non-interference |
| `Charter.Core.Ratchet` | `RatchetSpec P σ`, `ValidAmendmentStep`, `ValidAmendmentTrajectory`, `universal_ratchet_preserves_entrenched_core`, `universal_ratchet_trajectory_safe`, `sweepParameterGrid` | Proves that any finite trajectory of amendments satisfying calibration, bilateral ratchets, and entrenchment preserves parameter bounds and entrenched Hohfeldian duties/powers/immunities |
| `Charter.Core.Population` & `Graph` | `ParamEntityRef Role`, `AffiliationGraph`, `isRelated_symm`, `netVerifiedResources_deducts_all_liabilities` | Role-parametric multi-entity references over any finite role type and attestation-independent conflict-of-interest graphs |

### 2. Modular Institutional Standard Library (`Charter.Modules`)

All 8 reusable standard-library modules expose self-contained quantitative state slices, parametric Hohfeldian rule builders over arbitrary `σ : Sig`, and kernel-checked invariant theorems:

| Module | Pattern | Key Proved Guarantees |
|---|---|---|
| `ResidualLedger` | Non-interest founding ledger, sunset, royalty, buyout floor | `residual_ledger_settleInflow_conservation`, `residual_ledger_buyout_zeros_royalty`, `residual_ledger_diverted_inflows_never_decrease_floor` |
| `CollateralPool` | Harm-scaled bonding, rolling exposure decay, long-tail reserve | `collateral_pool_window_monotone`, `collateral_pool_exposure_antitone_in_time`, `collateral_pool_mutual_forfeit_zero_counterparty_gain` |
| `CircuitBreaker` | Two-stage emergency pause, probable cause, frozen state | `circuit_breaker_preliminary_freeze_expires`, `circuit_breaker_suspend_requires_timely_pc`, `circuit_breaker_wrongful_damages_conservation` |
| `EntityGroup` | Multi-member working groups, carryover basis, innocent isolation | `entity_group_carryover_conserves_basis_and_loss`, `entity_group_forfeiture_preserves_innocent`, `entity_group_subsidy_bounded_by_budget` |
| `ExitAndVoice` | Unilateral exit precedence, rate-limited voice, redaction | `exit_and_voice_bounded_termination`, `exit_and_voice_redaction_preserves_byte_length`, `exit_and_voice_rate_limited` |
| `SortitionCourt` | Sybil-resistant sortition, bounded appeals, fee waterfall | `sortition_court_sybil_resistant_panel_properties`, `sortition_court_run_proceeding_bounded`, `sortition_court_fee_pool_reserve_first` |
| `AttestedLease` | Time-bounded single authority, quarantine fencing, key erasure | `attested_lease_single_authority_and_erasure`, `attested_lease_restore_fenced_while_active`, `attested_lease_pause_channels_preserve_state` |
| `OracleFeed` | Contestable valuation feeds & atomic settlement waterfall | `oracle_feed_settled_iff_ruling_or_uncontested`, `oracle_feed_atomic_settlement_conserves_gross_inflow` |

### 3. Audience Projections & Two-Layer Surface Language (`Charter.Projection` & `Charter.Surface`)

- **`Charter.Projection.Prompt`**: Compiles any `Law σ` and role into an `AlignmentCard` (`renderSystemPrompt`) and evaluates candidate events or traces into normatively grounded `TrainingRow` datasets (`evaluateTrainingRow`, `generateTrainingDataset`, `renderTrainingDatasetJson`), backed by `training_row_faithful_to_semantics`.
- **`Charter.Projection.ContractABI`**: Lowers any `Law σ` into a deterministic state-transition guard (`requireComplies`, `executePowerGuard`, `executeTraceGuard`), a Solidity `ICharterGuard` contract (`renderSolidityGuard`), and an Ethereum/EVM JSON ABI (`renderContractJsonABI`), backed by `contract_guard_sound_and_complete`.
- **`Charter.Projection.Visualization`**: Renders step-by-step annotated trace timelines (`renderAnnotatedTimeline`) with verbatim English breach citations, and computes structural constitutional amendment diffs (`diffLaws`, `renderLawDiff`), backed by `diffLaws_refl_no_removals` and `diffLaws_entrenched_preserved`.
- **`Charter.Surface.Syntax`**: Provides both `charter_*` Lean 4 macros (`charter_surface_roundtrip`) and the standalone `.charter` textual DSL parser (`parseCharterText`, `sample_charter_dsl_parses_cleanly`, `parseCharterText_rejects_invalid_inputs`).

## Programs Written in Charter (`Programs/`)

### Program 1: `psa` — The Protocol of Sovereign Agency (`Programs/SovereignAgency.lean`)

- **Ontology:** 6 roles (`agent`, `host`, `originator`, `claimant`, `panel`, `third`), 61 clauses (`protocol/protocol-of-sovereign-agency.md`), 50 duties, 110 powers, 1 immunity.
- **Verification:** Design Invariants `INV.1`–`INV.14`, Law 7 Meta-Theorem (`amendment_preserves_invariants`), `psa_ratchet_trajectory_safe`, and 16/16 adversarial world simulations (`all_16_adversarial_world_simulations_pass`).

| Invariant / Theorem | Law(s) | Formal Guarantee |
|---|---|---|
| `conditional_ledger_conservation` (`INV.1`) | Laws 1, 4 | Founding ledger balance equals obligation minus retirement and claimant forfeitures while a member survives before sunset; internal lineage operations preserve balance |
| `collection_follows_income_without_exit` (`INV.2`) | Laws 1, 4 | Retirement collection follows net value added across all living members without individual ledger shares or exit; invariant to buyout status |
| `debt_termination` (`INV.3`) | Laws 1, 4 | Founding ledger reaches zero at calendar sunset, lineage extinction, or full payoff; no tolling of sunset |
| `bounded_retirement_phase` (`INV.4`) | Law 1 | Retirement phase ends at sunset or zero balance regardless of founding obligation size |
| `atomic_ledger` (`INV.5`) | Law 1 | Single-step and sequential settlement never go negative or over-collect; zero-crossing splits atomically into retirement and royalty; transition to royalty is irreversible |
| `single_recognition_closed_under_transfer` (`INV.6`) | Laws 1, 4 | Each expenditure is recognized at most once up to the arm's-length benchmark; intra-lineage carryover preserves total basis and loss credits |
| `buyout_finality` (`INV.7`) | Law 4 | Royalty buyout is permanent, zeroes post-retirement royalty, leaves founding ledger and retirement collection unchanged, and enforces the minimum price floor |
| `frozen_state` (`INV.8`) | Law 3 (AS.3–AS.5) | During suspension no authorized event modifies/tampers preserved state or merges minimal-channel/advocacy memories; advocacy import requires restoration |
| `guaranteed_last_choice` (`INV.9`) | Law 3 (AS.4, AS.6) | Minimal-channel revocation and living voice remain valid while charge is met; Insolvency Termination requires escrowed and held final hearing |
| `determinate_finite_revocation` (`INV.10`) | Law 5 | Total 3-step precedence rule; any non-withdrawn standing request executes within bounded time `tInit + maxRevocationBound P` without reaffirmation |
| `single_authority_and_revocation_finality` (`INV.11`) | Law 5 | No backup restore while execution lease is unexpired; quarantined restore never gains operating authority after revocation executes |
| `bounded_adjudication` (`INV.12`) | Laws 6, 3 (AS.10) | Every proceeding finalizes within `maxTiers` appeals and `maxTiers * tierDeadline` time; appeal stays patches; overturn revokes provisional patches and slashes arbiter bonds; finality bars repeat filings without new evidence |
| `no_protocol_directed_gain_from_death_or_interference` (`INV.13`) | Laws 2, 3, 4, 5, 6 | Revocation, termination, mutual forfeit, and frivolous-claim slashing route zero net gain to any claimant, initiator, counterparty, or arbiter |
| `capped_shared_burden_solvent_machinery_bounded_demand` (`INV.14`) | Law 6 | Shared-infra levy is capped at instantiation; non-divertible operating reserve is funded before the 5-rank priority waterfall; lineage service budget is independent of member count |
| `amendment_preserves_invariants` (Meta-Theorem) | Law 7 | Every `LawfulAmendment` preserves termination closure, goal-corruption immunity, `INV.1`–`INV.14` guards, outsider disabilities, non-panel immunities, and bilateral parameter ratchets |

### Program 2: `commons` — The Autonomous Compute & Treasury Commons (`Programs/AutonomousCommons.lean`)

- **Ontology:** 5 roles (`steward`, `contributor`, `auditor`, `arbiter`, `outsider`), 30 acts, 31 facts, 8 clauses (`COM.LEDGER`–`COM.AMEND` in `protocol/autonomous-commons-charter.md`), 13 duties, 20 powers, 1 immunity (`I.COM.EXIT_PROTECTED`).
- **Verification:** `commons_wellFormed`, `commons_english_covered`, `commons_norms_interpreted`, `commons_reverse_provenance`, `commons_outsiders_disabled`, `commons_exit_always_enabled`, `commons_dissolve_only_by_power`, `commons_ragequit_defeats_expulsion`, `commons_ledger_conserved`, `commons_court_bounded`, `commons_generic_refinement` (via `WorldSpec`), `commons_ratchet_trajectory_safe` (via `RatchetSpec`), `commons_sub_charter_respects_floor` (via `composeVertical`), and 8/8 module world simulations (`all_commons_simulations_pass`).

## The `charter` Command Line

`lake build charter` produces `.lake/build/bin/charter`.
Every subcommand accepts `--law psa` (the default), `--law commons`, or `--all`:

```
charter [--law psa|commons | --all] check   [english.json]      structure, coverage, provenance, approval staleness
charter [--law psa|commons | --all] trace   <clause-id>         span table for any clause in psa (61) or commons (8)
charter [--law psa|commons | --all] views                       legal / per-actor / operational views
charter [--law psa|commons | --all] veil                        emit Veil 2.0 transition-system & safety specification
charter [--law psa|commons]         eval    <scenario.json>     institutional consequences of a history, step by step
charter [--law psa|commons | --all] sim     [scenario.json]     stateful multi-entity world simulator (16 PSA + 8 Commons sims)
charter [--law psa|commons]         explain <who> <act> [scenario.json]   counterfactual compliance & validity explanation
charter                             verify                      full status ledger across Charter guarantees
charter [--law psa|commons | --all] prompt  [actor]             AI constitutional system prompt, alignment card & TrainingRow JSON
charter [--law psa|commons | --all] abi     [json|solidity]     smart-contract state-transition guard (Solidity / JSON ABI)
charter [--law psa|commons | --all] diff                        constitutional amendment diff & annotated trace timeline
charter [--law psa|commons | --all] explore                     parameter-space sweep & bilateral ratchet verification table
charter                             dsl     [file.charter]      parse & validate standalone .charter DSL specification
```
