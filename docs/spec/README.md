# The Charter Language Specification

**Version:** 0.4.0-draft
**Implementation status:** NON-COMPLIANT. The compiler on `main` implements the v0.3 flat grammar (`docs/completed/2026-10-18-charter-spec-v0.3.md`) and, as of Phase 1, the eFLINT core of chapters 002–011 for `.eflint` files. Each chapter below says which of its normative statements have a conformance test under `test/spec/` and whether the test passes. A chapter with no file yet is unwritten, not implied.

This directory replaces `docs/charter-spec.md` (plan §5.3). The spec leads the implementation: a change here is a ruling that the product is non-compliant until the code catches up, and only Eric authors or blesses normative wording (`AGENTS.md`, "The specification leads").

## Changelog

- 2026-10-23 — Skeleton: chapter list, `diagnostics.md` with the first CHR codes. No chapter has normative text yet. The implementation is NON-COMPLIANT with the plan's §2 grammar; the eFLINT core (chapters 002–011) is being implemented in Phase 1 against the vendored corpus `test/eflint-corpus/`.

## Chapters

Each normative statement in a chapter has a conformance test `test/spec/spec_<chapter>_<section>_<topic>.charter` (plan §5.3). The grammar chapter is checked against the parser by `tools/spec-inventory` once it exists.

| Chapter | File | Status |
|---|---|---|
| 001 design goals | `001_design_goals.md` | unwritten (source: `docs/mission.md`) |
| 002 lexical structure | `002_lexical_structure.md` | unwritten (source: eFLINT `Parse.hs` `lexer_settings`; D2) |
| 003 types and domains | `003_types_and_domains.md` | unwritten (D7 for `Time`/`Duration`) |
| 004 facts and derivation | `004_facts_and_derivation.md` | unwritten (D6: stratified fixpoint) |
| 005 acts, validity, effects | `005_acts_validity_effects.md` | unwritten (D5: `Valid when` defaults to true) |
| 006 duties and deadlines | `006_duties_and_deadlines.md` | unwritten (D12: violation reported on transition) |
| 007 immunities and exceptions | `007_immunities_and_exceptions.md` | unwritten |
| 008 events, physical, syncs | `008_events_physical_syncs.md` | unwritten |
| 009 time | `009_time.md` | unwritten (D7) |
| 010 expressions | `010_expressions.md` | unwritten |
| 011 phrases and scenarios | `011_phrases_and_scenarios.md` | unwritten |
| 012 clauses and provenance | `012_clauses_and_provenance.md` | unwritten (D4) |
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
