# The Charter Language Specification

**Version:** 1.0.0
**Status:** Approved (Eric, 2026-11-06).
**Implementation status:** Compliant across all twenty specification chapters (`001`–`020`) over both `.charter` and `.eflint` files under one unified contextual grammar (`D1`–`D28`), backed by 155 conformance tests under `test/spec/`, the executable `docs/spec/cheatsheet.charter`, 12 standard-library modules (`lib/`), 46 verified assurance claims (`docs/claims.json`), and both `charter` and operator-blind `charter-server` executables.

This directory is the canonical normative specification of Charter (`AGENTS.md`, "The specification leads"). A change here is a ruling that the product is non-compliant until the code catches up, and only Eric authors or blesses normative wording.

## Changelog

- 2026-11-06 — Gates `G0`–`G5` (`D17`–`D28`): unified contextual eFLINT 4.1 superset parser (`002`, `019`, `020`), `CIR` epochs + pure-Lean SHA-256 & HMAC-SHA256 `Artifact`s, declarative `DeclPhraseStep` & least-fixpoint correspondence (`evalPhrase_sound`/`complete`, `saturateStratum_least_prefixpoint`), lawful/adversarial/mixed explorer + temporal `Property` + `TVIR`/SMT (`013`), `Power` + multi-doc SHA-256 provenance (`005`, `012`), 4-valued `Evidenced` facts + `Finding` + audience-redacted `ReasonGraph` (`003`, `004`), stratified `Default`/`Exception`/`Priority` + `Conflict` (`004`, `007`), dimensional `Money`/`Quantity` + `MulDivRound` (`003`, `010`), rule-level `Amend` + reflexive ratchet proof + `Regime` + `charter diff` (`014`), 4 legal ontology modules in `lib/`, `TreasuryMandate`, operator-blind `charter-server` (`G4`), live `CIR` projections (`017`), and `lsp`/`doc`/`init`/`doctor`/SDKs/benchmarks (`018`). 155 conformance tests.
- 2026-10-25 (6) — `Eval/Properties.lean`: 004.3 in full (`rebaseAndSat_assigned`), 006.2/006.5 agreement (`isViolated_of_holds`), instances compare structurally (`Elem.beq_iff`); 006.4 CHR027 (`Terminated by`/`Created by` must be able to bind the duty's components). 124 conformance tests.
- 2026-10-25 (5) — `Examples/SovereignAgency/law3.eflint` (plan §8, Phase 2's exit): PSA Law 3's fourteen clauses in Charter with the approved texts, its 68 rules as acts, duties and an immunity, INV.8 `frozen-state` and INV.9 `guaranteed-last-choice` as invariants, twelve scenarios, in the battery's `examples` step; `charter prove` decides 122 of its 276 phrases before one exceeds 8 GB (013.4, the reopen condition for interning).
- 2026-10-25 (4) — `Examples/AutonomousCommons/commons.eflint` (plan §8, Phase 2's exit): the commons in Charter over the eight `lib/` modules, its eight clauses with every rule's English, the eight Lean simulations reproduced as scenarios by `charter test`; in the battery's `examples` step.
- 2026-10-25 (3) — `Examples/Tenancy/` (plan §4, §8): the toy program and its document, one clause per Phase 2 addition, six clauses approved, seven scenarios, explored invariants; battery step `examples`.
- 2026-10-25 (2) — 007.3 duty precedence: `Duty d … Overridden by d'` (shared components, declared, one level); CHR026. 123 conformance tests.
- 2026-10-25 — `charter prove` is a checkpointed chain (013.4, ruled by Eric): one kernel theorem per phrase, closed by `kernel_rfl`, memory bounded by a phrase; whole `lib/` tests decide under the default cap. A failing step names the phrase the kernel disagrees about (Law 9). `test/prove/scenario.eflint`.
- 2026-10-24 (night) — `charter prove` lands as Phase 2's maintainer tool (013.3, 013.4, 018.2): the generator embeds phrases as data, one kernel decision per program with `decide +kernel`, one *decided* claim per theorem, capped; `test/prove/`. The evaluator depends on no axiom. Measured limit recorded in 013.4.
- 2026-10-24 — D15 (an act whose domain is not enumerable is judged for the instance; CHR025; the `explore-domain` menu) in 004.1, 004.7, 005.5, 013.2, 018; D16 (`Duration * Int`) in 009.2, 010.2. 121 conformance tests.
- 2026-10-23 (late, 5) — Chapter 018 (toolchain and CLI, today's commands) drafted; `Charter.Prove.Run` gives the evaluator as a pure function for `prove`. The kernel-decision feasibility result is in 013.4.
- 2026-10-23 (late, 4) — Phase 2's sixth slice: invariant exploration, `charter test --explore N` and `//! explore: N` (chapter 013). 110 conformance tests.
- 2026-10-23 (late, 3) — Phase 2's fifth slice: `Module name(params) { … }` and `Use name(args) As prefix` (D8, chapter 015); CHR023. 106 conformance tests.
- 2026-10-23 (late, 2) — Phase 2's fourth slice: `Param` (D11, chapter 014) and fact origins with `?why` (Law 6, 004.10). 102 conformance tests.
- 2026-10-23 (late) — Phase 2's third slice, clauses and provenance (D4): chapter 012; `charter check` and `charter test` run the Law 8 checks as claims; `charter trace`. 99 conformance tests.
- 2026-10-23 (night) — Phase 2's second slice, time (D7): the clock (`@ t.`, `tick.`), `Time`/`Duration` types and domains, stamps on every assignment, `Held(e) For d`, `Creates e For d`, `Due within d`; CHR106. 92 conformance tests.
- 2026-10-23 (evening) — Phase 2's first slice: `Valid when` (005.9), `Except under` (007.2), `Immunity … Against … Unless` (007.4), `Scenario` and the claim phrases (011.11), `--eflint` mode (002.9, 011.10); CHR022. 82 conformance tests.
- 2026-10-23 (later) — Chapters 002–011 drafted from the implementation and eFLINT's semantics, each statement with a conformance test (72 tests, `test/spec/`, all passing; `tools/battery` runs them). 007 and 009 state Phase 2 designs as pending. `Charter.Eval.Properties` proves 004.3 and 005.3.
- 2026-10-23 — Skeleton: chapter list, `diagnostics.md` with the first CHR codes. No chapter has normative text yet. The implementation is NON-COMPLIANT with the plan's §2 grammar; the eFLINT core (chapters 002–011) is being implemented in Phase 1 against the vendored corpus `test/eflint-corpus/`.

## Chapters

Each normative statement in a chapter has a conformance test `test/spec/spec_<chapter>_<section>_<topic>.charter` (plan §5.3). The grammar chapter is checked against the parser by `tools/spec-inventory` once it exists.

| Chapter | File | Status |
|---|---|---|
| 001 design goals | `001_design_goals.md` | approved (`docs/mission.md`, `docs/rfc.md`) |
| 002 lexical structure | `002_lexical_structure.md` | approved; unified contextual grammar (`D17`) |
| 003 types and domains | `003_types_and_domains.md` | approved; includes `Evidenced`, `Money`, `Quantity` (`D7`, `D22`, `D24`) |
| 004 facts and derivation | `004_facts_and_derivation.md` | approved; stratified least fixpoint, `ReasonGraph`, `Default`/`Exception` (`D6`, `D15`, `D22`, `D23`) |
| 005 acts, validity, effects | `005_acts_validity_effects.md` | approved; `Valid when`, `Power`, `Finding`, evidence clauses (`D5`, `D15`, `D21`, `D22`) |
| 006 duties and deadlines | `006_duties_and_deadlines.md` | approved; `Due within`, transition violation reporting (`D12`) |
| 007 immunities and exceptions | `007_immunities_and_exceptions.md` | approved; `Except under`, `Overridden by`, `Immunity`, `Default`/`Exception`/`Conflict` (`D23`) |
| 008 events, physical, syncs | `008_events_physical_syncs.md` | approved |
| 009 time | `009_time.md` | approved; `Time`/`Duration`, half-open `[start, end)` expiry, `Held … For` (`D7`, `D16`) |
| 010 expressions | `010_expressions.md` | approved; dimensional arithmetic & `MulDivRound` (`D14`, `D24`) |
| 011 phrases and scenarios | `011_phrases_and_scenarios.md` | approved; `Scenario`, `?lawful`/`?valid`/`?violated`/`?undetermined`/`?conflict`, `SubmitEvidence` |
| 012 clauses and provenance | `012_clauses_and_provenance.md` | approved; multi-doc SHA-256 `Document`/`Clause`, Markdown anchors, `complete\|partial\|illustrative` (`D4`, `D21`) |
| 013 invariants and proof | `013_invariants_and_proof.md` | approved; `prove` checkpointed chain, `explore`, temporal `Property`, `verify` (`D9`, `D19`, `D20`) |
| 014 parameters and regimes | `014_parameters_and_regimes.md` | approved; `Param`, rule-level `Amend`, `Regime`, reflexive entrenchment (`D11`, `D25`) |
| 015 modules and require | `015_modules_and_require.md` | approved; `Module`/`Use` & 12 standard-library modules (`D8`, `D26`) |
| 016 diagnostics | `diagnostics.md` | approved (`CHR001`–`CHR035`, `CHR100`–`CHR108`; `spec-inventory.sh`) |
| 017 projections | `017_projections.md` | approved (`D28`: `solidity`, `abi`, `quint`, `prompt`, `CHR035`, `T32`–`T33`) |
| 018 toolchain and CLI | `018_toolchain_and_cli.md` | approved: `charter` & operator-blind `charter-server` (`D1`, `D27`) |
| 019 eFLINT compatibility | `019_eflint_compatibility.md` | approved (`D2`, `D6`, `D12`–`D15`, `D17`; 196-file corpus + `tolerances.json`) |
| 020 grammar | `020_grammar.md` | approved (`test/gates/spec-inventory.sh`, `charter fmt` round-trip) |

## Cheat sheet

`docs/spec/cheatsheet.charter` exercises Charter 1.0's constructs end-to-end and is continuously executed as part of `tools/g5-check` in `tools/battery`.
