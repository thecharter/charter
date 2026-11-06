# D22 — Four-valued epistemic `Evidence`/`Finding`, 3-valued `Eval`, and audience-redacted `ReasonGraph` (`T04`–`T07`, `T43`)

**Laws:** 1, 2, 3, 5, 6, 8, 9, 10, 12, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §5.1–§5.5, §18.3)

## Ruling
1. **Ontic `Closed` vs. plain `Open` vs. epistemic `Evidenced` facts (`003.13`, `004.11`)**:
   - `Closed` facts keep default `False` (`003.6`), and plain eFLINT `Open` facts keep `CHR100: missing input` when unassigned (`Law 12`).
   - Contextual `Evidenced Fact <id> ... [Confidential [To <audience, ...>]]` declares an `Open` external-world proposition evaluated over Belnap's 4-valued epistemic lattice:
     `EvidenceStatus = Established | Refuted | Unresolved | Conflicted`.
   - `SubmitEvidence [!]<expr> [By <source>].`, `RetractEvidence <expr> [By <source>].`, and act clauses `Supports <expr>` / `Rebuts <expr>` / `Retracts <expr>` update tendered evidence records in `State` (`CHR033` if the target is not `Evidenced`).
2. **Institutional `Finding` acts (`Mission Law 3`, `005.11`)**:
   - Contextual `Finding <id> ... Resolves [!]<expr> [Standard <name>] Valid when <expr> ...` declares an adjudication power (`isPower := true`, requiring `Valid when`, `CHR032`).
   - A valid `Finding` adjudicates its `Evidenced` target to `Established` (or `Refuted` when negated), superseding prior `Unresolved` or `Conflicted` evidence (`finding_resolves_conflict`, `T07`); a void `Finding` occurs without altering epistemic or legal state (`T02`, `T07`).
3. **Kleene 3-valued guard propagation (`TriBool = yes | no | undetermined`)**:
   - Guards reading an `Unresolved` or `Conflicted` `Evidenced` fact propagate `TriBool.undetermined` + `unmetEvidence : List (Tagged × EvidenceStatus)` under strong Kleene truth tables (`no && undetermined = no`, `yes || undetermined = yes`) without aborting via `CHR100` and without inventing truth (`valid` effects require `validTri == .yes`, `T06`).
   - Explicit epistemic predicates `Established(e)`, `Refuted(e)`, `Unresolved(e)`, and `Conflicted(e)` let statutes declare presumptions, burdens, or escalation triggers directly.
4. **Audience-scoped `ReasonGraph` (`charter explain`) & metamorphic impartiality (`--metamorphic`)**:
   - `charter explain` constructs a structured `ReasonGraph` (rule IDs, `From` spans, premise statuses, defeated exceptions, single-condition counterfactuals) and applies `redactForAudience`, proved in Lean (`redactForAudience_preserves_verdict`, `T43`) never to alter `(lawful, valid)`.
   - Advisory phrase notes (`Note "..."`) are proved irrelevant (`advisory_note_irrelevant`, `T04`), and `charter test --metamorphic` (`//! metamorphic`) verifies invariance under advisory stripping and non-salient actor permutation (`T04`, `T05`).

## Context
Real institutions face missing or contradictory external observations (`T06`, `T07`). Halting with `CHR100` blocks runtime adjudication, while collapsing unknown to `false` invents exculpatory/incriminating facts (`Law 6`).

## Mission fit
`Law 3` (breaches/evidence and `Finding`s remain distinct), `Law 5` (`ReasonGraph` is pure data), `Law 6` (unassigned `Evidenced` facts stay `Unresolved`, never invented), `Law 9` (single proved `Eval`), `Law 12` (plain `Open` keeps `CHR100`).

## Cost accepted
Four internal evidence domains (`$ev_support`, `$ev_rebut`, `$ev_finding_pos`, `$ev_finding_neg`) live inside `State.contents` (O(1) `DomMap` bucket lookup; zero overhead when unused).

## Reopens if
Multi-stage appellate stays on `Finding`s require built-in stay timers beyond `Creates ... For d` and standard library modules.
