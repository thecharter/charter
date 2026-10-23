# Charter (v0.3.0) — Formally Verified Institutional Specification, Composition & Projection Language

**Charter** is a formally verified language for institutional rules (constitutions, protocols, charters, bylaws). A Charter program is a **`.charter` file**: it declares roles, acts, facts, and parameters, quotes its authoritative English clause by clause, and states its duties, powers, and immunities in a small declarative grammar. The `charter` command line runs every analysis on that file directly, with no Lean required of the author: provenance checks, legal and per-role views, scenario evaluation, counterfactual explanations, AI constitutional prompts, smart-contract guards, Veil state machines, amendment diffs, and parameter sweeps. The language, its semantics, and every projection are implemented and proved in Lean 4, and a one-line Lean stub (`charter_program "file.charter"`) embeds a program as a Lean term so that anything about it can be kernel-checked.

The repository has two layers with a strict dependency direction (`Examples → Charter`, never the reverse):

1. **`Charter` (`Charter.lean` + `Charter/`) — the language.** The `.charter` grammar, parser, validator, and printer (`Charter.Surface.Dsl`); its meaning as a Hohfeldian law (`Charter.Surface.Lower`); the normative core, standard library, projections, and CLI harness. Nothing in this layer refers to any particular institution. Its tests use small self-contained toy charters.
2. **`Examples` (`Examples.lean` + `Examples/`) — programs written in Charter.** Two ship today, each a `.charter` file next to its authoritative Markdown and scenario files: *The Protocol of Sovereign Agency* (`psa`, `Examples/SovereignAgency/protocol-of-sovereign-agency.charter`, 61 clauses) and *The Autonomous Compute & Treasury Commons* (`commons`, `Examples/AutonomousCommons/autonomous-commons.charter`, 8 clauses). Each also keeps a Lean companion holding its theorems and quantitative world simulations, together with a kernel-checked proof (`psa_program_is_lean_law`, `commons_program_is_lean_law`) that lowering the `.charter` file yields exactly the law those theorems are about.

Build: `lake build` (Lean 4.24, no Mathlib, no external dependencies). The CLI lands in `.lake/build/bin/charter`.
Check trust: `grep -rn "sorry\|native_decide\|axiom " src/Charter/ Examples/ src/Main.lean src/Charter.lean Examples.lean` is empty; every general theorem depends at most on Lean's standard `propext`, `Classical.choice`, `Quot.sound`, and every decided scenario depends on no axioms at all (`{}`).

## Repository Layout

```
── THE CHARTER LANGUAGE & STANDARD LIBRARY (Charter/) ──────────────────────────
Charter.lean                                Umbrella module for the language, compiler & standard library
src/Charter/Core/Provenance.lean                Spans, registers, lexical/normative/reverse coverage & AuthorshipQuestion
src/Charter/Core/Syntax.lean                    Typed Hohfeldian normative AST (Duty, Power, Immunity, Law σ)
src/Charter/Core/Semantics.lean                 Occurrence, compliance, and institutional validity semantics
src/Charter/Core/Views.lean                     Generated legal, per-actor, operational, and trace views
src/Charter/Core/Explain.lean                   Step-by-step counterfactual explanation engine
src/Charter/Core/Graph.lean                     Law-agnostic AffiliationGraph & VerifiedBalanceSheet
src/Charter/Core/Population.lean                Groups, members, stakeholders, operators: ParamEntityRef Role & population conservation
src/Charter/Core/Refinement.lean                Polymorphic WorldSpec σ Q & GenericWorldState refinement theorems
src/Charter/Core/Composition.lean               Vertical (L_sub ◁ L_super) & horizontal (L₁ ⊕ L₂) composition, SigEmbedding & LawInterface
src/Charter/Core/Ratchet.lean                   Universal RatchetSpec P σ, ValidAmendmentTrajectory & sweepParameterGrid
src/Charter/Modules/ResidualLedger.lean         Module 1: Non-interest residual ledger, sunset, royalty & buyout floor
src/Charter/Modules/CollateralPool.lean         Module 2: Harm-scaled bonding, rolling exposure decay & long-tail reserve
src/Charter/Modules/CircuitBreaker.lean         Module 3: Two-stage emergency freeze, probable cause & frozen-state protection
src/Charter/Modules/EntityGroup.lean            Module 4: Multi-member group ledgers, carryover basis & innocent isolation
src/Charter/Modules/ExitAndVoice.lean           Module 5: Deterministic unilateral exit precedence & rate-limited voice
src/Charter/Modules/SortitionCourt.lean         Module 6: Sybil-resistant sortition, bounded appeals & priority fee waterfall
src/Charter/Modules/AttestedLease.lean          Module 7: Time-bounded single operating lease, quarantine fencing & key erasure
src/Charter/Modules/OracleFeed.lean             Module 8: Contestable valuation feeds & atomic settlement conservation
src/Charter/Substrate/Attestation.lean          Substrate: attested execution leases, quarantine fencing & irreversible key erasure
src/Charter/Substrate/Sortition.lean            Substrate: Sybil-resistant sortition, conflict/cluster filtering & supermajority
src/Charter/Substrate/Settlement.lean           Substrate: contestable valuation resolution & atomic settlement conservation
src/Charter/Projection/Veil.lean                Veil 2.0 transition-system lowering & preservation theorem
src/Charter/Projection/Prompt.lean              AI constitutional system prompts, AlignmentCard & synthetic TrainingRow JSON
src/Charter/Projection/ContractABI.lean         Smart-contract state-transition guard (requireComplies, executePowerGuard, Solidity & JSON ABI)
src/Charter/Projection/Visualization.lean       Step-by-step annotated trace timelines & LawDiff amendment entrenchment audit
src/Charter/Surface/Dsl.lean                    The .charter language: AST (Doc), tokenizer, parser (parseCharterText), validator (validate), printer (render)
src/Charter/Surface/Lower.lean                  Meaning of a Doc: lowering to Law σ_dyn over the dynamic signature, string tables, parameter environments
src/Charter/Surface/Unlower.lean                Exporting a Lean law as a Doc (sentinel-based parameter naming), embeddingOf
src/Charter/Surface/Program.lean                `charter_program "file.charter"`: embeds a validated .charter file as a Lean term
src/Charter/Surface/DslSample.lean              Kernel-decided toy program: parse, validate, print/parse round trip, lower, evaluate scenarios
src/Charter/Surface/Syntax.lean                 charter_* Lean 4 macros for programs written directly in Lean (charter_clause, charter_duty, ...)
src/Charter/Tooling/Cli.lean                    Program-agnostic `charter` CLI harness (Charter.Cli.Program, Charter.Cli.run)

── EXAMPLE PROGRAMS WRITTEN IN CHARTER (Examples/) ─────────────────────────────
Examples.lean                               Umbrella module for the example programs
Examples/SovereignAgency/protocol-of-sovereign-agency.charter   THE PROGRAM: psa written in the Charter language (61 clauses, 50 duties, 110 powers)
Examples/SovereignAgency/protocol-of-sovereign-agency.md        Authoritative English text for psa
Examples/SovereignAgency.lean               Lean companion of psa: signature, theorems, 16 world simulations
Examples/SovereignAgency/Program.lean       charter_program embedding + psa_program_is_lean_law (the .charter file = the Lean law)
Examples/SovereignAgency/Export.lean        `charter export --law psa`: the Lean formalization printed as .charter text
Examples/SovereignAgency/scenarios/*.json   Scenario histories for `charter eval|sim|explain`
Examples/SovereignAgency/views.txt          Generated legal, agent, and operational views for psa
Examples/SovereignAgency/Definitions.lean   DEF.01 & SUB.01 verbatim provenance clauses
Examples/SovereignAgency/Law1/Ledger.lean   Law 1: Founding Ledger, Sunset, Value-Added, Carryover Basis & LoanLedger
Examples/SovereignAgency/Law2/Collateral.lean       Law 2: Collateralized Action, Exposure Aggregation & Mutual Forfeit
Examples/SovereignAgency/Law3/NonInterference.lean  Law 3: Signature, Non-Interference, Host Notice & Penalties
Examples/SovereignAgency/Law3/IntegrityFloor.lean   Law 3: 5-point Agent Integrity Floor
Examples/SovereignAgency/Law3/Suspension.lean       Law 3: Adjudicated Suspension (AS.1–AS.9) & Insolvency Termination
Examples/SovereignAgency/Law3/Remediation.lean      Law 3: Remediation, Goal-Patch Immunity & Periodic Review (AS.10)
Examples/SovereignAgency/Law4/Lineage.lean          Law 4: Lineage Attestation, Ledger Conservation, Forfeiture & Buyout Floor
Examples/SovereignAgency/Law5/Revocation.lean       Law 5: Living Voice, Revocation Precedence, Leases & Epitaph Redaction
Examples/SovereignAgency/Law6/Adjudication.lean     Law 6: Sortition, Appeal Tiers, Finality Consolidation & Fee Waterfall
Examples/SovereignAgency/Law7/Amendment.lean        Law 7: Bilateral Ratchet, Calibration Valve & Per-Agent Scope
Examples/SovereignAgency/Law.lean                   Assembly of all 61 clauses across Laws 1–7 + DEF.01 + SUB.01 into one Law
Examples/SovereignAgency/Scenarios.lean             Decided histories & all 16 Adversarial Tests across Laws 1–7
Examples/SovereignAgency/Theorems.lean              Design Invariants INV.1–INV.14, Law 7 Meta-Theorem & Sub-Mechanisms
Examples/SovereignAgency/Simulation/WorldState.lean Coupled quantitative + normative ProtocolWorldState & syncFacts
Examples/SovereignAgency/Simulation/Refinement.lean Refinement theorems & 16 end-to-end adversarial world simulations
Examples/SovereignAgency/Cli.lean                   Registers psa (and its world simulator) with the charter CLI
Examples/AutonomousCommons/autonomous-commons.charter      THE PROGRAM: commons written in the Charter language (8 clauses, 13 duties, 20 powers)
Examples/AutonomousCommons/autonomous-commons-charter.md   Authoritative English text for commons
Examples/AutonomousCommons.lean             Lean companion of commons: signature, theorems, 8 world simulations
Examples/AutonomousCommons/Program.lean     charter_program embedding + commons_program_is_lean_law
Examples/AutonomousCommons/Export.lean      `charter export --law commons`
Examples/AutonomousCommons/Cli.lean                 Registers commons with the charter CLI

── CLI & DOCUMENTATION ─────────────────────────────────────────────────────────
src/Main.lean                                 `charter` executable: Charter.Cli.run over the registered examples
docs/spec/                                  The Charter language specification (skeleton; replaces docs/charter-spec.md, archived under docs/completed/)
HANDOFF.md                                  Orientation for the next maintainer
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
   from finding to fact is an explicit assumption (`SoundFindings` in the
   `psa` example), shown by counterexample not to be a theorem.
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
| `Charter.Core.Population` & `Graph` | `ParamEntityRef Role`, `GroupState`, `MemberRecord`, `StakeholderShare`, `transferMemberCarryover_conserves_basis_and_loss`, `attributeCrossGroupInflow_conserves_total`, `forfeitStakeholderInGroup_preserves_innocent_stakeholder`, `group_wide_amendment_requires_every_living_member`, `AffiliationGraph`, `isRelated_symm`, `netVerifiedResources_deducts_all_liabilities` | Role-parametric multi-entity references over any finite role type, conservation theorems for group/member/stakeholder accounting, and attestation-independent conflict-of-interest graphs |

### 2. Modular Institutional Standard Library (`Charter.Modules`)

All 8 reusable standard-library modules expose self-contained quantitative state slices, parametric Hohfeldian rule builders over arbitrary `σ : Sig`, and kernel-checked invariant theorems:

| Module | Pattern | Key Proved Guarantees |
|---|---|---|
| `ResidualLedger` | Non-interest founding ledger, sunset, royalty, buyout floor | `residual_ledger_settleInflow_conservation`, `residual_ledger_buyout_zeros_royalty`, `residual_ledger_diverted_inflows_never_decrease_floor` |
| `CollateralPool` | Harm-scaled bonding, rolling exposure decay, long-tail reserve | `collateral_pool_window_monotone`, `collateral_pool_exposure_antitone_in_time`, `collateral_pool_mutual_forfeit_zero_counterparty_gain` |
| `CircuitBreaker` | Two-stage emergency pause, probable cause, frozen state | `circuit_breaker_preliminary_freeze_expires`, `circuit_breaker_suspend_requires_timely_pc`, `circuit_breaker_wrongful_damages_conservation` |
| `EntityGroup` | Multi-member working groups, carryover basis, innocent isolation | `entity_group_carryover_conserves_basis_and_loss`, `entity_group_forfeit_isolates_innocent_stakeholder`, `entity_group_subsidy_bounded_by_budget` |
| `ExitAndVoice` | Unilateral exit precedence, rate-limited voice, redaction | `exit_and_voice_determinate_finite_revocation`, `exit_and_voice_redaction_preserves_bytes`, `exit_and_voice_rate_limit_iff` |
| `SortitionCourt` | Sybil-resistant sortition, bounded appeals, fee waterfall | `sortition_court_sybil_resistant_panel_properties`, `sortition_court_run_proceeding_bounded`, `sortition_court_fee_pool_reserve_first` |
| `AttestedLease` | Time-bounded single authority, quarantine fencing, key erasure | `attested_lease_single_authority_and_erasure`, `attested_lease_restore_fenced_while_active`, `attested_lease_pause_channels_preserve_state` |
| `OracleFeed` | Contestable valuation feeds & atomic settlement waterfall | `oracle_feed_settled_iff_ruling_or_uncontested`, `oracle_feed_atomic_settlement_conserves_gross_inflow` |

### 3. Audience Projections, Surface Language & Tooling (`Charter.Projection`, `Charter.Surface`, `Charter.Tooling`)

- **`Charter.Projection.Prompt`**: Compiles any `Law σ` and role into an `AlignmentCard` (`renderSystemPrompt`) and evaluates candidate events or traces into normatively grounded `TrainingRow` datasets (`evaluateTrainingRow`, `generateTrainingDataset`, `renderTrainingDatasetJson`), backed by `training_row_faithful_to_semantics`.
- **`Charter.Projection.ContractABI`**: Lowers any `Law σ` into a deterministic state-transition guard (`requireComplies`, `executePowerGuard`, `executeTraceGuard`), a Solidity `ICharterGuard` contract (`renderSolidityGuard`), and an Ethereum/EVM JSON ABI (`renderContractJsonABI`), backed by `contract_guard_sound_and_complete`.
- **`Charter.Projection.Visualization`**: Renders step-by-step annotated trace timelines (`renderAnnotatedTimeline`) with verbatim English breach citations, and computes structural amendment diffs (`diffLaws`, `renderLawDiff`), backed by `diffLaws_refl_no_removals` and `diffLaws_entrenched_preserved`.
- **`Charter.Surface.Dsl` / `Lower` / `Unlower` / `Program`**: The `.charter` language. `parseCharterText` reads a file into a `Doc`, `validate` reports every unresolved name or type error, `render` prints it back (`sample_render_roundtrip`), and `lower` gives it meaning as a `Law σ_dyn` over the dynamic signature (actors and acts are declared names, facts are names optionally applied to a role), so every projection and theorem of the language applies to it. `unlower` is the reverse direction used to export a Lean law. `charter_program "file.charter"` embeds a file as a Lean term at elaboration time; the kernel then sees only data (`Charter.Surface.DslSample` decides parsing, validation, round trip, lowering, and scenario outcomes on a toy tenancy program).
- **`Charter.Surface.Syntax`**: `charter_*` Lean 4 macros (`charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_institution`, `charter_string_table`) for programs written directly in Lean, with definitional round-trip proofs (`charter_surface_roundtrip`).
- **`Charter.Tooling.Cli`**: The program-agnostic command-line harness. A program registers by building a `Charter.Cli.Program` (law, clauses, string tables, sample traces, parameter regimes, optional world simulator, verification ledger); `Charter.Cli.run` dispatches every subcommand over the registered programs.

## Example Programs Written in Charter (`Examples/`)

### Example 1: `psa` — The Protocol of Sovereign Agency (`Examples/SovereignAgency.lean`)

- **Ontology:** 6 roles (`agent`, `host`, `originator`, `claimant`, `panel`, `third`), 61 clauses (`Examples/SovereignAgency/protocol-of-sovereign-agency.md`), 50 duties, 110 powers, 1 immunity, all in the `SovereignAgency` namespace.
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

### Example 2: `commons` — The Autonomous Compute & Treasury Commons (`Examples/AutonomousCommons.lean`)

- **Ontology:** 5 roles (`steward`, `contributor`, `auditor`, `arbiter`, `outsider`), 30 acts, 31 facts, 8 clauses (`COM.LEDGER`–`COM.AMEND` in `Examples/AutonomousCommons/autonomous-commons-charter.md`), 13 duties, 20 powers, 1 immunity (`I.COM.EXIT_PROTECTED`), all in the `AutonomousCommons` namespace.
- **Verification:** `commons_wellFormed`, `commons_english_covered`, `commons_norms_interpreted`, `commons_reverse_provenance`, `commons_rules_built_from_modules`, `commons_outsiders_disabled`, `commons_exit_always_enabled`, `commons_dissolve_only_by_power`, `commons_ragequit_defeats_expulsion`, `commons_ledger_conserved`, `commons_court_bounded`, `commons_generic_refinement` (via `WorldSpec`), `commons_ratchet_trajectory_safe` (via `RatchetSpec`), `commons_sub_charter_respects_floor` (via `composeVertical`), and 8/8 module world simulations (`all_commons_simulations_pass`).

## Writing a Charter Program

A program is one `.charter` file. Declarations start at the beginning of a line and continue over indented lines; `--` starts a comment; strings may span lines and use `\"`, `\\`, `\n`, `\t`.

```
charter garden "Allotment Garden Rules"
document "rules.md"                        -- authoritative English, relative to this file
default actor gardener                     -- role used by `prompt` when none is given

roles gardener, committee
acts plant, reassign, giveNotice
facts allotted, noticeGiven, reassigned, initiator(role)   -- facts may take a role argument

params
  noticeWindow = 10

regime "short notice"                      -- alternative parameter sets, swept by `explore`
  noticeWindow = 3

init allotted                              -- facts established at time 0

clause ALT.1 approved 12345678901234567890 -- hash of the clause text, printed by `check`
  norm "The committee may reassign an allotted plot only after giving the gardener notice" => D.NOTICE, P.REASSIGN
  commentary "."

duty D.NOTICE
  from ALT.1 "only after giving the gardener notice"
  bearer only committee
  beneficiary only gardener
  active holds allotted
  forbid act reassign
  except when heldFor noticeGiven noticeWindow

power P.REASSIGN
  from ALT.1 "The committee may reassign an allotted plot"
  holder only committee
  trigger act reassign
  valid heldFor noticeGiven noticeWindow
  adds reassigned
  removes allotted
```

Clause spans come in five registers (`norm`, `definition`, `invariant`, `acceptance`, `commentary`); `check` verifies that the spans reproduce the clause exactly, that every norm span names a rule, that every rule is named by some span, and that each clause occurs verbatim in the `document`. Actor classes are `anyone`, `only r, s`, `except r, s`, `tagged f` (every role `r` carrying `f(r)`), or `tagged r: f(r), s: g(s)`. Conditions are `true`, `false`, `holds f`, `heldFor f n`, `countGe f n`, `countAtLeast f g`, `not`, `and`, `or`, and parentheses; conduct is `act a`, `anyOf a, b`, `exerciseOf P.X`, with the same connectives; numbers are literals, parameter names, or sums. Duty modifiers: `except when <cond>`, `except by power P.A, P.B`, `overridden by D.A`, `breach by P.FIND`, `remedies f, g`. Power effects: `adds f`, `adds f for n` (time-to-live), `adds f to role` (actor-indexed), `adds f if <cond>` (conditional), `removes f`, `establishes breach of D.X`. Immunities take `holder`, `against P.A, P.B`, `active`, and `except when`. `use module Name with a = 1` documents which standard-library pattern a program instantiates. The complete grammar is in the header of `src/Charter/Surface/Dsl.lean`.

Workflow:

1. Write the file and run `charter check my.charter`. Validation errors name the declaration and the unresolved name; once the structure is right, `check` prints the text hash to paste into each clause's `approved` field, so later edits to the English are flagged as `STALE`.
2. Run `charter views`, `explain <who> <act> [scenario.json]`, `eval scenario.json`, `prompt [actor]`, `abi`, `veil`, `diff`, and `explore` with the file as an argument. Scenario files are `{"institution": "<id>", "init": [facts], "events": [{"t", "who", "act"}]}`.
3. Optionally, in a Lean package that requires this repository, write `def myDoc := charter_program "my.charter"` and prove what you care about by `decide` on `(Charter.Dsl.lower myDoc).law`: well-formedness, provenance, scenario outcomes, or equality with a hand-written Lean law. Quantitative world models and theorems quantifying over all traces are written in Lean against that lowered law, exactly as the two shipped examples do.

## The `charter` Command Line

`lake build` produces `.lake/build/bin/charter`. Any `.charter` files on the command line are the programs the command runs on. Without files, the command runs on the programs linked into the binary (the two examples): every subcommand accepts `--law <id>` or `--all`; with neither flag it runs over every registered program, `explain`/`prompt` pick the program that owns the named actor, and `eval`/`sim` read the scenario file's `"institution"` key.

```
charter [--law <id> | --all] check   [english.json]      structure, coverage, provenance, approval staleness
charter [--law <id> | --all] trace   <clause-id>         span table for any clause of the selected programs
charter [--law <id> | --all] views                       legal / per-actor / operational views
charter [--law <id> | --all] veil                        emit Veil 2.0 transition-system & safety specification
charter [--law <id>]         eval    <scenario.json>     institutional consequences of a history, step by step
charter [--law <id> | --all] sim     [scenario.json]     program-specific stateful world simulator (16 psa + 8 commons sims)
charter [--law <id>]         explain <who> <act> [scenario.json]   counterfactual compliance & validity explanation
charter [--law <id> | --all] verify                      language ledger followed by each program's ledger of guarantees
charter [--law <id> | --all] prompt  [actor]             AI constitutional system prompt, alignment card & TrainingRow JSON
charter [--law <id> | --all] abi     [json|solidity]     smart-contract state-transition guard (Solidity / JSON ABI)
charter [--law <id> | --all] diff                        amendment diff & annotated trace timeline
charter [--law <id> | --all] explore                     parameter-space sweep & bilateral ratchet verification table
charter [--law <id> | --all] dsl                         parse, validate & summarize the program's .charter file
charter [--law <id> | --all] export                      print a registered (Lean) program as .charter text
charter <command> [args] <file.charter> ...              run any command above on the given .charter files
```

Examples:

```
.lake/build/bin/charter check Examples/SovereignAgency/protocol-of-sovereign-agency.charter   # 280 ok, 0 FAIL, 0 STALE
.lake/build/bin/charter explain host terminate Examples/SovereignAgency/protocol-of-sovereign-agency.charter
.lake/build/bin/charter eval Examples/SovereignAgency/scenarios/host-shutdown.json Examples/SovereignAgency/protocol-of-sovereign-agency.charter
.lake/build/bin/charter check                      # the linked Lean programs: 0 FAIL, 0 STALE
.lake/build/bin/charter sim --law psa Examples/SovereignAgency/scenarios/host-shutdown.json   # coupled world simulator (Lean companion)
.lake/build/bin/charter prompt steward             # resolves to commons
.lake/build/bin/charter export --law psa           # prints the Lean formalization as .charter (what the shipped file is)
```
