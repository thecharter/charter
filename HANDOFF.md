# HANDOFF — Charter

Reverse-chronological. Newest section first. Verify every hash below with `git log`
before acting on it. The rules are `AGENTS.md`; read it before this file.

---

# Handoff — 2026-10-23 (night): mission, decisions D1–D11, redesign plan, AGENTS.md; main at bc4d594

## Where

- Branch `main`, pushed through `bc4d594` ("Add mission, decision log (D1–D11), and the redesign plan"). History was rewritten on 2026-10-23 to drop AI co-author trailers: `003e2a3` → `4a6b106`, `1737ec0` → `bc4d594`. No commit on `main` carries one.
- **Uncommitted at handoff:** `AGENTS.md` (new, canonical rules), `CLAUDE.md` (new, a pointer to AGENTS.md), and edits to `docs/plans/2026-10-22-redesign.md` bringing its wording in line with D4–D11. Commit these three together first.
- `.reference/` (ignored) holds four read-only checkouts: `eflint` (Haskell reference implementation plus `examples-corpus/`), `catala`, `quint`, `symboleo` (`ide/`, `pc/`, identical trees). Nine other candidates were cloned and removed; the choice of four is in the session record, not a decision entry.

## What was done this session

1. **Reviewed `docs/charter-spec.md` and the four references.** Findings that drove everything after: the spec is an architecture tour, not a language reference; it claims `check` reports authorship questions (`AuthorshipQuestion` is dead code) and lists four registers (there are five); the 14 `invariant` spans in the PSA name `INV.*` ids nothing links to a theorem; the v0.3 DSL has no quantities, no individuals, no in-file tests, no time model beyond `Nat`, no modules reachable from a program. eFLINT is the one existing language on Charter's square and was adopted as the core (D2).
2. **`docs/mission.md`** (Eric): three goals in precedence order, fourteen laws with test questions.
3. **`docs/meetings/`**: D1–D11, index, and the briefs (`2026-10-22-briefs-for-ruling.md`). D10 and D11 are Eric's words verbatim and overruled the briefs' predictions.
4. **`docs/plans/2026-10-22-redesign.md`**: language (eFLINT core plus Charter additions), compiler pipeline, target repository layout, process borrowed from With, CLI, migration table, five phases with exit criteria. §9 records that all decisions are ruled.
5. **`AGENTS.md`** drafted in With's structure, translated to Charter; `CLAUDE.md` points to it.

## Design facts the next session must not relearn

- Lean-hosted binary, Lean-free output; `prove` is opt-in and fetches its own toolchain by digest (D1, D9). No author-visible text may name Lean (Law 11).
- `Holds when` = lawful, `Valid when` = effective, defaults to true, so eFLINT programs keep eFLINT's "disabled act still has effects" (D5).
- Derivation is stratified; unstratifiable negation is rejected (D6).
- `Time` and `Duration` are distinct types over `Int` (D7). Time is state on facts; `@ t.` and `tick.` are environment input, never trace events (Law 7).
- Module properties are `Invariant`s in the `.charter` module, proved in `lib/lean/` by name (D8).
- **No model of the protocol outside Charter** (D10): `ProtocolWorldState` and the 16 Lean simulations are deleted when their Charter scenarios pass; each simulation is a scenario naming its span in the protocol's Adversarial Tests section; substrate inputs are environment facts and substrate properties are `SUB.*` assumptions; every division states its rounding.
- **Rule amendment is the `Amend` act** over rule records; ratchets are reflexively entrenched `Immunity … Against Amend`, not invariants; `Extend` never changes rules at run time (D11). Consequence: `Core.Law` becomes part of evaluator state, addressable by rule id. Design the Phase 1 agreement proof with a mutable rule set from the start.
- Two eFLINT tolerances are still unruled and look delegable: report a duty's violation on transition only (not every phrase while it stays violated); error on duplicate declarations instead of silently replacing. Record each as a delegated decision before implementing.

## State of the code (unchanged since 4a6b106)

The v0.3 tree described in the next section still builds and passes: `lake build` 122 jobs clean, trust grep 0, leak grep 0, `charter check` on both `.charter` files 280 ok / 0 FAIL / 0 STALE, `charter sim` 16/16 and 8/8, `charter export` byte-identical to the shipped files. Nothing in the plan has been implemented yet; Phase 0 (process scaffolding) is partly done by the docs above and `AGENTS.md`, and `tools/battery`, `test/gates/`, and `docs/spec/` do not exist.

## Next

Phase 0's remainder, then Phase 1 (the eFLINT core), per the plan §8. First concrete tasks: commit the three uncommitted files; record the two delegated tolerance decisions; create `docs/spec/README.md` with the chapter list and move `docs/charter-spec.md` under `docs/completed/`; vendor `.reference/eflint/tests` and `examples-corpus` into `test/eflint-corpus/` as the Phase 1 target; write `test/gates/` for the trust grep, leak grep, and the Law 11 string check so the battery has something to run.

## Standing rules

`AGENTS.md`. In particular: no AI co-author trailer; never edit an English document or an `Approved` hash to make a check pass; `.reference/` is read-only; `git stash` is banned.

---

# Handoff — 2026-10-18: v0.3.0, the .charter DSL is the program format; main at 4a6b106

The sections below are the v0.3.0 handoff as written before the redesign. They describe the code as it still is; their process instructions are superseded by `AGENTS.md` and their forward-looking statements by `docs/plans/2026-10-22-redesign.md`.

### 1. What this project is

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

### 2. The semantic commitments (do not break these)

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

### 3. State of the work (v0.3.0: language/example separation complete)

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

### 4. Verifying a cut

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
