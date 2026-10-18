# HANDOFF — Charter Language & Programs (v0.2.0)

For the agent taking over this repository (`https://github.com/thecharter/charter`). Read this, then `README.md`,
`docs/charter-spec.md`, and the Lean sources in the order listed under
"Repository Layout" in `README.md`.
Build with `lake build && lake build charter` before changing
anything; all targets must succeed with zero errors and zero warnings.

## 1. What this project is

This repository is cleanly separated into two Lake library targets (`Charter` and `Programs`):

1. **`Charter` (`Charter.lean` + `Charter/`) — The Charter Language, Compiler & Standard Library:**
   A domain-agnostic, formally verified institutional specification language in Lean 4 for specifying, composing, verifying, simulating, and projecting institutional rules across arbitrary signatures `σ : Sig`. `Charter` contains zero references to any specific constitution or protocol.
2. **`Programs` (`Programs.lean` + `Programs/`) — Institutional Programs Written in Charter (`import Charter`):**
   - **`psa` — *The Protocol of Sovereign Agency* (`Programs/SovereignAgency.lean`, `Programs/SovereignAgency/*`)** (`protocol/protocol-of-sovereign-agency.md`): a 61-clause constitution for self-owning AI agents across Definitions (`DEF.01`), Substrate (`SUB.01`), and Laws 1–7, with 14 Design Invariants (`INV.1`–`INV.14`), the Law 7 Meta-Theorem, and 16 adversarial multi-agent world simulations.
   - **`commons` — *The Autonomous Compute & Treasury Commons* (`Programs/AutonomousCommons.lean`)** (`protocol/autonomous-commons-charter.md`, `examples/autonomous-commons.charter`): an 8-clause multi-steward compute and treasury commons composed from all 8 reusable standard-library modules in `Charter/Modules/`.

Core architectural decisions (do not relitigate without the owner):

- **Strict dependency direction (`Programs -> Charter`, never `Charter -> Programs`).**
  `Charter/` is the language and standard library; `Programs/` contains concrete institutional programs written in `Charter`.
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
- **Two-layer surface language (`Charter.Surface.Syntax`).**
  Theorem authors use kernel-checked `charter_*` macros with `rfl`
  round-trip equivalence; external specification authors can also write standalone
  `.charter` files parsed by `parseCharterText` without expanding the trusted computing base.

## 2. The semantic commitments (do not break these)

1. **Three independent questions about every event**: occurrence (any
   event can occur; a `Trace` is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). A
   forbidden act may be valid; a lawful act may be void. Never make a
   forbidden event unreachable.
2. **Violations are facts in the record** (`violations L tr`), **findings
   are institutional events** (a panel's `Power` whose validity mentions
   claim + evidence, whose effect is exactly the breached duty's declared
   `remedies`). The link from finding to fact is a named assumption
   (`SoundFindings`), refuted as a theorem by Scenario 7. Keep it that way.
3. **Exceptions come in distinct kinds**: scope (`unlessCond`), authority
   (`unlessPower`: the same act is lawful iff it is the valid exercise of
   a named power), duty-over-duty precedence (`overriddenBy`),
   protection-over-power precedence (`Immunity`). Breach consequences are
   remedies, never exceptions.
4. **The authorized machine is derived.** `Authorized L tr` := every event
   complies. Theorems like `terminate_only_by_power` and `commons_dissolve_only_by_power`
   are *about* it; it is never a modelling input.
5. **Every norm carries its English** (`Span`), with a `Register` so that
   invariants, acceptances and commentary are traced but never promoted
   to rules. Every clause has an `approvedHash`; `charter check --all` reports
   staleness and verbatim occurrence across both `protocol/protocol-of-sovereign-agency.md`
   and `protocol/autonomous-commons-charter.md`.
6. **Trust discipline**: no `sorry`, no `native_decide`, no `axiom`.
   `grep -rn "sorry\|native_decide\|axiom " Charter/ Programs/ Main.lean Charter.lean Programs.lean`
   must be empty. General theorems may depend on `propext`, `Classical.choice`,
   `Quot.sound` only; decided scenarios depend on none (`{}`).

## 3. State of the work (v0.2.0 Complete)

Everything in `Charter` and `Programs` is implemented and kernel-verified (see `.lake/build/bin/charter verify` for the full 57-entry ledger):

- **`Charter.Core` (`Charter/Core/`):**
  - `Provenance.lean`, `Syntax.lean`, `Semantics.lean`, `Views.lean`, `Explain.lean`: Law-agnostic normative kernel.
  - `Graph.lean`: Generic affiliation / conflict-of-interest graph (`AffiliationEdge`, `AffiliationGraph`, `isRelated_symm`, `isRelated_ignores_attestation`) and `VerifiedBalanceSheet` (`netVerifiedResources_deducts_all_liabilities`).
  - `Population.lean`: Role-parametric `ParamEntityRef Role` (`ParamEntityRef.toRole_mem_of_all`) and multi-entity population conservation theorems.
  - `Refinement.lean`: Polymorphic `WorldSpec σ Q` and `GenericWorldState σ Q` with `generic_worldStep_refines_legalStep`, `generic_worldTrace_refines_stateAfter`, `generic_worldAuthorized_iff_prefix_split`, `generic_syncFacts_sound_and_complete`, `generic_syncFacts_idempotent`, and `generic_syncFacts_preserves_unmanaged`.
  - `Composition.lean`: `LawInterface`, `interfaceCompatible`, `interfacesDisjoint`, `SigEmbedding`, functorial `Law.lift` (`Law.lift_id`, `Law.lift_comp`), vertical composition `composeVertical` (`L_sub ◁ L_super`) with `vertical_composition_preserves_super_prohibitions`, `vertical_composition_preserves_super_immunities`, `vertical_composition_preserves_super`, and horizontal composition `composeHorizontal` with `horizontal_frame_non_interference`.
  - `Ratchet.lean`: `RatchetSpec P σ`, `defaultEntrenchedCore`, `ValidAmendmentStep`, `ValidAmendmentTrajectory`, `universal_ratchet_preserves_entrenched_core`, `universal_ratchet_trajectory_safe`, `sweepParameterGrid`, `sweepParameterGrid_sound`, and `renderSweepTable`.
- **`Charter.Modules` (`Charter/Modules/`):**
  - All 8 self-contained standard-library modules (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`, `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`) with quantitative state slices, parametric rule builders over arbitrary `σ : Sig`, `SigEmbedding` lift helpers, and kernel-checked module self-tests (`all_8_charter_modules_self_test_pass`).
- **`Charter.Substrate` (`Charter/Substrate/`):**
  - `Attestation.lean`, `Sortition.lean`, `Settlement.lean`: Cryptographic lease attestation, Sybil-resistant sortition, and contestable valuation settlement primitives.
- **`Charter.Projection` (`Charter/Projection/`):**
  - `Veil.lean`: Veil 2.0 state-machine lowering & `veil_projection_sound_and_complete`.
  - `Prompt.lean`: `AlignmentCard`, `compileAlignmentCard`, `renderSystemPrompt`, `TrainingRow`, `evaluateTrainingRow`, `generateTrainingDataset`, `renderTrainingDatasetJson`, and `training_row_faithful_to_semantics`.
  - `ContractABI.lean`: `requireComplies`, `executePowerGuard`, `executeTraceGuard`, `ContractGuardSpec`, `renderContractJsonABI`, `renderSolidityGuard`, and `contract_guard_sound_and_complete`.
  - `Visualization.lean`: `TimelineStep`, `compileTimelineSteps`, `renderAnnotatedTimeline`, `LawDiff`, `diffLaws`, `renderLawDiff`, `diffLaws_refl_no_removals`, and `diffLaws_entrenched_preserved`.
- **`Charter.Surface` (`Charter/Surface/Syntax.lean`):**
  - Layer 1 Lean 4 macros (`charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_string_table`, `charter_institution`) with `charter_surface_roundtrip`.
  - Layer 2 standalone `.charter` parser (`parseCharterText`, `ParsedCharterDoc.render`) with `sample_charter_dsl_parses_cleanly`, `parseCharterText_multiline_and_escaped_quotes`, and `parseCharterText_rejects_invalid_inputs`.
- **`Programs` (`Programs/` & `Programs.lean`):**
  - `Programs/SovereignAgency.lean` + `Programs/SovereignAgency/*` (`psa`): All 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01` (50 duties, 110 powers, 1 immunity), Design Invariants `INV.1`–`INV.14`, Law 7 Meta-Theorem, `psa_ratchet_trajectory_safe`, and 16/16 adversarial world simulations (`all_psa_simulations_pass`).
  - `Programs/AutonomousCommons.lean` (`commons`): Distinct 5-role ontology `σ_commons` (`CommonsRole`, `CommonsAct`, `CommonsFact`), 8 verbatim clauses (`COM.LEDGER`–`COM.AMEND` in `protocol/autonomous-commons-charter.md`), 13 duties, 20 powers, 1 immunity (`I.COM.EXIT_PROTECTED`), coupled `CommonsWorldState`, institutional invariants, `commons_generic_refinement`, `commons_ratchet_trajectory_safe`, `commons_sub_charter_respects_floor`, and 8/8 module world simulations (`all_commons_simulations_pass`).

## 4. Verifying a cut

```bash
lake build && lake build charter
grep -rn "sorry\|native_decide\|axiom " Charter/ Programs/ Main.lean Charter.lean Programs.lean   # must be empty
.lake/build/bin/charter check --all          # all 61 PSA + 8 Commons clauses ok, 0 FAIL, 0 STALE
.lake/build/bin/charter sim --all            # 16/16 PSA + 8/8 Commons world simulations pass
.lake/build/bin/charter verify               # full 57-entry formal verification ledger
.lake/build/bin/charter prompt --law commons steward
.lake/build/bin/charter abi --law commons solidity
.lake/build/bin/charter diff --law psa
.lake/build/bin/charter explore --all
.lake/build/bin/charter dsl
.lake/build/bin/charter views > docs/law3-views.txt && git diff docs/law3-views.txt
```
