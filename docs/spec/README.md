# The Charter Language Specification

**Version:** 0.4.0-draft
**Implementation status:** NON-COMPLIANT with the plan's full §2 grammar; **compliant with chapters 002–011 as drafted** (the eFLINT core, Phase 1) for `.eflint` files, every normative statement of those chapters having a passing conformance test under `test/spec/`. The `.charter` extension still means the v0.3 flat grammar (`docs/completed/2026-10-18-charter-spec-v0.3.md`) until Phase 2 moves it to this grammar; the conformance tests therefore use `.eflint` for now. Every chapter is a **draft**: D2 fixes the meaning (eFLINT 4.1 unchanged) and the decisions fix the differences, but the wording is Eric's to bless (`AGENTS.md`, "Spec changes are solemn"). A chapter with no file yet is unwritten, not implied.

This directory replaces `docs/charter-spec.md` (plan §5.3). The spec leads the implementation: a change here is a ruling that the product is non-compliant until the code catches up, and only Eric authors or blesses normative wording (`AGENTS.md`, "The specification leads").

## Changelog

- 2026-10-23 (late) — Phase 2's third slice, clauses and provenance (D4): chapter 012; `charter check` and `charter test` run the Law 8 checks as claims; `charter trace`. 99 conformance tests.
- 2026-10-23 (night) — Phase 2's second slice, time (D7): the clock (`@ t.`, `tick.`), `Time`/`Duration` types and domains, stamps on every assignment, `Held(e) For d`, `Creates e For d`, `Due within d`; CHR106. 92 conformance tests.
- 2026-10-23 (evening) — Phase 2's first slice: `Valid when` (005.9), `Except under` (007.2), `Immunity … Against … Unless` (007.4), `Scenario` and the claim phrases (011.11), `--eflint` mode (002.9, 011.10); CHR022. 82 conformance tests.
- 2026-10-23 (later) — Chapters 002–011 drafted from the implementation and eFLINT's semantics, each statement with a conformance test (72 tests, `test/spec/`, all passing; `tools/battery` runs them). 007 and 009 state Phase 2 designs as pending. `Charter.Eval.Properties` proves 004.3 and 005.3.
- 2026-10-23 — Skeleton: chapter list, `diagnostics.md` with the first CHR codes. No chapter has normative text yet. The implementation is NON-COMPLIANT with the plan's §2 grammar; the eFLINT core (chapters 002–011) is being implemented in Phase 1 against the vendored corpus `test/eflint-corpus/`.

## Chapters

Each normative statement in a chapter has a conformance test `test/spec/spec_<chapter>_<section>_<topic>.charter` (plan §5.3). The grammar chapter is checked against the parser by `tools/spec-inventory` once it exists.

| Chapter | File | Status |
|---|---|---|
| 001 design goals | `001_design_goals.md` | unwritten (source: `docs/mission.md`) |
| 002 lexical structure | `002_lexical_structure.md` | draft; 8 tests green |
| 003 types and domains | `003_types_and_domains.md` | draft; 14 tests green (`Time`/`Duration` in 009) |
| 004 facts and derivation | `004_facts_and_derivation.md` | draft; 11 tests green (D6) |
| 005 acts, validity, effects | `005_acts_validity_effects.md` | draft; 10 tests green, `Valid when` (D5) included |
| 006 duties and deadlines | `006_duties_and_deadlines.md` | draft; 6 tests green, `Due within` included |
| 007 immunities and exceptions | `007_immunities_and_exceptions.md` | draft; 4 tests green (`Except under`, `Immunity`); duty precedence pending |
| 008 events, physical, syncs | `008_events_physical_syncs.md` | draft; 4 tests green |
| 009 time | `009_time.md` | draft; 10 tests green (D7: the clock, `Time`/`Duration`, stamps, `Held … For`, expiry) |
| 010 expressions | `010_expressions.md` | draft; 13 tests green (D14) |
| 011 phrases and scenarios | `011_phrases_and_scenarios.md` | draft; 12 tests green, `Scenario` and claims included |
| 012 clauses and provenance | `012_clauses_and_provenance.md` | draft; 7 tests green (D4, Law 8: `Document`, `Clause … Approved`, register spans, `From`, the six checks) |
| 013 invariants and proof | `013_invariants_and_proof.md` | unwritten (D8, D9) |
| 014 parameters and regimes | `014_parameters_and_regimes.md` | unwritten (D11) |
| 015 modules and require | `015_modules_and_require.md` | unwritten (D8) |
| 016 diagnostics | `diagnostics.md` | started: code registry only |
| 017 projections | `017_projections.md` | unwritten |
| 018 toolchain and CLI | `018_toolchain_and_cli.md` | unwritten (D1, D9) |
| 019 eFLINT compatibility | `019_eflint_compatibility.md` | unwritten; the tolerances live in `test/eflint-corpus/tolerances.md` until this chapter exists |
| 020 grammar | `020_grammar.md` | unwritten |

## Cheat sheet

`cheatsheet.charter` will be a program that exercises every construct and is itself a test (Catala). Not yet written.
