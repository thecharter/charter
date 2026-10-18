# HANDOFF — Charter Language & Example Programs (v0.3.0)

For the agent taking over this repository (`https://github.com/thecharter/charter`). Read this, then `README.md`,
`docs/charter-spec.md`, and the Lean sources in the order listed under
"Repository Layout" in `README.md`.
Build with `lake build` before changing anything; all targets must succeed with zero errors and zero warnings.

## 1. What this project is

**Charter is a language, and a Charter program is a `.charter` file.** The repository is split into two Lake library targets with a strict dependency direction (`Examples → Charter`, never `Charter → Examples`):

1. **`Charter` (`Charter.lean` + `Charter/`) — The Charter Language, Compiler, Standard Library & CLI harness.**
   A domain-agnostic, formally verified institutional specification language in Lean 4 for specifying, composing, verifying, simulating, and projecting institutional rules across arbitrary signatures `σ : Sig`. `Charter` contains zero references to any specific constitution or protocol: its vocabulary is generic (groups, members, stakeholders, operators, arbiters), its substrate and module docstrings describe patterns rather than any one document, and its test suites use small self-contained toy charters (a residential tenancy, a lending library).
2. **`Examples` (`Examples.lean` + `Examples/`) — Programs Written in Charter (`import Charter`).**
   Each example lives in its own namespace and directory together with its authoritative English text, scenario files, generated views, and a `Cli.lean` that registers it with the harness:
   - **`psa` — *The Protocol of Sovereign Agency*** (`Examples/SovereignAgency.lean`, `Examples/SovereignAgency/*`, namespace `SovereignAgency`): a 61-clause constitution for self-owning AI agents across Definitions (`DEF.01`), Substrate (`SUB.01`), and Laws 1–7, with 14 Design Invariants (`INV.1`–`INV.14`), the Law 7 Meta-Theorem, and 16 adversarial multi-agent world simulations. This was the document the project originally set out to formalize; it is now one example among others.
   - **`commons` — *The Autonomous Compute & Treasury Commons*** (`Examples/AutonomousCommons.lean`, `Examples/AutonomousCommons/*`, namespace `AutonomousCommons`): an 8-clause multi-steward compute and treasury commons composed from all 8 reusable standard-library modules in `Charter/Modules/`.

Core architectural decisions (do not relitigate without the owner):

- **Strict dependency direction and namespace separation.** Nothing under `Charter/` may import, name, quote, or special-case an example. Examples never define anything in the `Charter` namespace (they used to re-export into it; that is gone). If a mechanism in an example turns out to be reusable, generalize it into `Charter/Modules/` or `Charter/Core/` under generic vocabulary first, then have the example instantiate it.
- **The semantics lives in Lean 4, as a deep embedding.** Duties, powers,
  and immunities are *data* (`Charter/Core/Syntax.lean`);
  one interpretation function gives them meaning (`Charter/Core/Semantics.lean`);
  views, explanations, AI prompts, smart-contract guards, and Veil 2.0 state machines
  are all pure projections generated from `Law σ`. Lean's kernel is the only trusted checker.
- **Polymorphic quantitative-to-normative refinement (`WorldSpec σ Q`).**
  `Charter/Core/Refinement.lean` separates quantitative multi-entity state (`Q`)
  from propositional Hohfeldian state (`LegalState σ`), proving step refinement,
  trace refinement, prefix-split authorization equivalence, and idempotent fact
  synchronization once for all signatures `σ` and state types `Q`.
- **Modular institutional composition (`Charter.Modules.*` & `Charter.Core.Composition`).**
  Reusable institutional mechanisms live in `Charter/Modules/` and are composed via
  vertical hierarchy (`L_sub ◁ L_super`), horizontal composition (`composeHorizontal`),
  and functorial signature embeddings (`SigEmbedding`, `Law.lift`).
- **The `.charter` language is the program format (`Charter.Surface.Dsl`, `Lower`, `Unlower`, `Program`).**
  `parseCharterText` → `validate` → `lower` turns a file into a `Law σ_dyn` over the dynamic signature (`Atom` actors/acts, `DynFact` facts with an optional role argument); the CLI runs every subcommand on `.charter` files given as arguments (`Program.ofLowered`). `charter_program "file"` embeds a file as a Lean term at elaboration time (the kernel sees data, never text), which is how each example proves `*_program_is_lean_law`: lowering the shipped `.charter` file equals the Lean law its theorems are about. `unlower` + sentinel parameters (`charter export`) is how those files were produced from the Lean formalizations; the files are now the programs and the Lean modules are their verified companions. The `charter_*` Lean macros (`Charter.Surface.Syntax`) remain for programs written directly in Lean. Lake does not track `.charter` files as dependencies of the Lean module embedding them: after editing one, rebuild the `Program.lean` that embeds it (touch it or `lake build` after removing its `.olean`).
- **`charter_string_table` is a command, not a term.** It emits three top-level definitions (`T.name`, `T.parse`, `T`). The Lean 4.24 code generator miscompiles a `StringTable` built as closures inside one structure literal once the type has ~140+ constructors (segfault in `mi_malloc` at first call); separate top-level `match` definitions are reliable and kernel-reducible.
- **Program-agnostic CLI (`Charter.Tooling.Cli`).** The harness knows nothing about any program. A program registers by building a `Charter.Cli.Program` descriptor (law, clauses, string tables, sample traces, parameter regimes, optional program-specific world simulator, verification ledger); `Main.lean` is a two-line list of registered programs. There is no default `--law`: with no flag, commands run over every registered program, `explain`/`prompt` resolve the program from the actor name, and `eval`/`sim` read the scenario's `"institution"` key.

## 2. The semantic commitments (do not break these)

1. **Three independent questions about every event**: occurrence (any
   event can occur; a `Trace` is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). A
   forbidden act may be valid; a lawful act may be void. Never make a
   forbidden event unreachable.
2. **Violations are facts in the record** (`violations L tr`), **findings
   are institutional events** (a panel's `Power` whose validity mentions
   claim + evidence, whose effect is exactly the breached duty's declared
   `remedies`). In `psa` the link from finding to fact is a named assumption
   (`SoundFindings`), refuted as a theorem by Scenario 7. Keep it that way.
3. **Exceptions come in distinct kinds**: scope (`unlessCond`), authority
   (`unlessPower`: the same act is lawful iff it is the valid exercise of
   a named power), duty-over-duty precedence (`overriddenBy`),
   protection-over-power precedence (`Immunity`). Breach consequences are
   remedies, never exceptions.
4. **The authorized machine is derived.** `Authorized L tr` := every event
   complies. Theorems like `terminate_only_by_power` (psa) and `commons_dissolve_only_by_power`
   are *about* it; it is never a modelling input.
5. **Every norm carries its English** (`Span`), with a `Register` so that
   invariants, acceptances and commentary are traced but never promoted
   to rules. Every clause has an `approvedHash`; `charter check` reports
   staleness and verbatim occurrence against each program's authoritative document.
6. **Trust discipline**: no `sorry`, no `native_decide`, no `axiom`.
   `grep -rn "sorry\|native_decide\|axiom " Charter/ Examples/ Main.lean Charter.lean Examples.lean`
   must be empty. General theorems may depend on `propext`, `Classical.choice`,
   `Quot.sound` only; decided scenarios depend on none (`{}`).

## 3. State of the work (v0.3.0: language/example separation complete)

Everything in `Charter` and `Examples` is implemented and kernel-verified (see `.lake/build/bin/charter verify` for the full ledger):

- **`Charter.Core` (`Charter/Core/`):**
  - `Provenance.lean`, `Syntax.lean`, `Semantics.lean`, `Views.lean` (`stripNamespaces`, `rs`), `Explain.lean`: Law-agnostic normative kernel.
  - `Graph.lean`: Generic affiliation / conflict-of-interest graph (`AffiliationEdge`, `AffiliationGraph`, `isRelated_symm`, `isRelated_ignores_attestation`) and `VerifiedBalanceSheet` (`netVerifiedResources_deducts_all_liabilities`).
  - `Population.lean`: Generic group/member/stakeholder/operator ontology (`GroupId`, `MemberId`, `StakeholderId`, `OperatorId`, `ArbiterId`, `GroupLedger`, `GroupState`, `MemberRecord`, `StakeholderShare`), role-parametric `ParamEntityRef Role`, and the conservation theorems (`transferMemberCarryover_conserves_basis_and_loss`, `attributeCrossGroupInflow_conserves_total`, `forfeitStakeholderInGroup_preserves_innocent_stakeholder`, `group_wide_amendment_requires_every_living_member`, `group_subsidy_bounded_by_budget_regardless_of_members`).
  - `Refinement.lean`: Polymorphic `WorldSpec σ Q` and `GenericWorldState σ Q` with `generic_worldStep_refines_legalStep`, `generic_worldTrace_refines_stateAfter`, `generic_worldAuthorized_iff_prefix_split`, `generic_syncFacts_sound_and_complete`, `generic_syncFacts_idempotent`, and `generic_syncFacts_preserves_unmanaged`.
  - `Composition.lean`: `LawInterface`, `interfaceCompatible`, `interfacesDisjoint`, `SigEmbedding`, functorial `Law.lift` (`Law.lift_id`, `Law.lift_comp`), vertical composition `composeVertical` (`L_sub ◁ L_super`) with `vertical_composition_preserves_super_prohibitions`, `vertical_composition_preserves_super_immunities`, `vertical_composition_preserves_super`, and horizontal composition `composeHorizontal` with `horizontal_frame_non_interference`.
  - `Ratchet.lean`: `RatchetSpec P σ`, `defaultEntrenchedCore`, `ValidAmendmentStep`, `ValidAmendmentTrajectory`, `universal_ratchet_preserves_entrenched_core`, `universal_ratchet_trajectory_safe`, `sweepParameterGrid`, `sweepParameterGrid_sound`, and `renderSweepTable`.
- **`Charter.Modules` (`Charter/Modules/`):**
  - All 8 self-contained standard-library modules (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`, `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`) with quantitative state slices, parametric rule builders over arbitrary `σ : Sig`, `SigEmbedding` lift helpers, and kernel-checked module self-tests (`all_8_charter_modules_self_test_pass`). Vocabulary is generic (`ExitParams`, `TestimonyEntry`, `GroupLedgerState`, `groupServiceBudget`, `applyRuling`, …).
- **`Charter.Substrate` (`Charter/Substrate/`):**
  - `Attestation.lean`, `Sortition.lean`, `Settlement.lean`: Cryptographic lease attestation (`ExecutionLease.operatorId`, `quarantinedRestoreOperator`), Sybil-resistant sortition, and contestable valuation settlement (`rulingAmount`, `applyRuling`) primitives.
- **`Charter.Projection` (`Charter/Projection/`):**
  - `Veil.lean`: Veil 2.0 state-machine lowering & `veil_projection_sound_and_complete`.
  - `Prompt.lean`: `AlignmentCard` (`unalienableImmunities`, `institutionalPowers`, `hardProhibitions`, `positiveDeadlines`), `compileAlignmentCard`, `renderSystemPrompt`, `TrainingRow`, `evaluateTrainingRow`, `generateTrainingDataset`, `renderTrainingDatasetJson`, and `training_row_faithful_to_semantics`.
  - `ContractABI.lean`: `requireComplies`, `executePowerGuard`, `executeTraceGuard`, `ContractGuardSpec`, `renderContractJsonABI`, `renderSolidityGuard`, and `contract_guard_sound_and_complete`.
  - `Visualization.lean`: `TimelineStep`, `compileTimelineSteps`, `renderAnnotatedTimeline`, `LawDiff`, `diffLaws`, `renderLawDiff`, `diffLaws_refl_no_removals`, and `diffLaws_entrenched_preserved`.
- **`Charter.Surface`:**
  - `Dsl.lean`: the `.charter` grammar (documented in the module header), `Doc` AST (all `ToExpr`/`DecidableEq`), fuel-based tokenizer and parser (`parseCharterText`), `validate`, and `render` (inverse of parsing on valid documents).
  - `Lower.lean`: `σ_dyn`, `Env`/`Doc.regimeEnv`, `lowerLaw`/`lowerClauses`/`tables`, `Lowered`. `Unlower.lean`: `Naming`, `ExportSpec`, `sentinelValue` (powers of two, so sums of parameters decode), `unlower`, `embeddingOf`. `Program.lean`: the `charter_program` term elaborator. `DslSample.lean`: toy tenancy program decided in the kernel (`sample_render_roundtrip`, `sample_lowered_wellFormed`, `sample_scenario_breach`, ...).
  - `Syntax.lean`: Lean 4 macros (`charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_institution`, the `charter_string_table` command) with `charter_surface_roundtrip`, exercised on a toy tenancy charter (`Charter.Surface.Examples`).
- **`Charter.Tooling` (`Charter/Tooling/Cli.lean`):** `Charter.Cli.Program`, the generic subcommand implementations, `languageLedger`, flag parsing and target resolution, and `Charter.Cli.run`.
- **`Examples` (`Examples/` & `Examples.lean`):**
  - `Examples/SovereignAgency/protocol-of-sovereign-agency.charter` is the program (`Program.lean`: `psaDoc`, `psa_program_is_lean_law`, `psa_program_clauses`; `Export.lean`: `psaExportDoc`, `paramsEnv`, `sentinelParams`). `Examples/SovereignAgency.lean` + `Examples/SovereignAgency/*` (`psa`, namespace `SovereignAgency`) is its Lean companion: all 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01` (50 duties, 110 powers, 1 immunity), Design Invariants `INV.1`–`INV.14`, Law 7 Meta-Theorem, `psa_ratchet_trajectory_safe`, coupled `ProtocolWorldState` (`SovereignAgency.Simulation`), and 16/16 adversarial world simulations (`all_psa_simulations_pass`). `Cli.lean` supplies `psaSim` and `psaLedger`.
  - `Examples/AutonomousCommons/autonomous-commons.charter` is the program (`Program.lean`, `Export.lean` as above). `Examples/AutonomousCommons.lean` + `Examples/AutonomousCommons/*` (`commons`, namespace `AutonomousCommons`) is its Lean companion: distinct 5-role ontology `σ_commons` (`CommonsRole`, `CommonsAct`, `CommonsFact`), 8 verbatim clauses (`COM.LEDGER`–`COM.AMEND`), 13 duties, 20 powers, 1 immunity (`I.COM.EXIT_PROTECTED`), coupled `CommonsWorldState`, institutional invariants, `commons_generic_refinement`, `commons_ratchet_trajectory_safe`, `commons_sub_charter_respects_floor`, and 8/8 module world simulations (`all_commons_simulations_pass`). `Cli.lean` supplies `commonsSim`, the `.charter` path, and `commonsLedger`.

## 4. Verifying a cut

```bash
lake build
grep -rn "sorry\|native_decide\|axiom " Charter/ Examples/ Main.lean Charter.lean Examples.lean   # must be empty
grep -rniE "sovereign|\bpsa\b|commons" Charter/ Charter.lean | grep -viE "commons pool|commonsShare|commonsAllocated|toCommons|Autonomous_Commons"   # language layer names no example
.lake/build/bin/charter check Examples/SovereignAgency/protocol-of-sovereign-agency.charter Examples/AutonomousCommons/autonomous-commons.charter   # 280 ok, 0 FAIL, 0 STALE
for f in Examples/SovereignAgency/scenarios/*.json; do diff <(.lake/build/bin/charter eval --law psa $f) <(.lake/build/bin/charter eval $f Examples/SovereignAgency/protocol-of-sovereign-agency.charter); done   # Lean and .charter paths agree
.lake/build/bin/charter export --law psa | diff - Examples/SovereignAgency/protocol-of-sovereign-agency.charter   # shipped file is the export (empty diff)
.lake/build/bin/charter check                # the linked Lean programs: 0 FAIL, 0 STALE
.lake/build/bin/charter sim                  # 16/16 psa + 8/8 commons world simulations pass
.lake/build/bin/charter verify               # language ledger + both program ledgers
.lake/build/bin/charter prompt steward
.lake/build/bin/charter abi --law commons solidity
.lake/build/bin/charter diff --law psa
.lake/build/bin/charter explore
.lake/build/bin/charter dsl
.lake/build/bin/charter views --law psa > Examples/SovereignAgency/views.txt && git diff Examples/SovereignAgency/views.txt
```
