# D17 — Charter's single-word additions are contextual keywords; one unified grammar parses all `.charter` and `.eflint` programs

**Laws:** 12, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §3.6, §12.1, §18.3)

## Ruling
Charter maintains one unified lexer, parser, and semantics as a strict superset of stratified eFLINT 4.1 (`CHR020` kept), rather than splitting into diverging `eflint-4.1-compat` and `charter-1.x-strict` profiles or requiring `--eflint` lexical mode:

1. Multi-word additions (`Valid when`, `Except under`, `Due within`) are ordinary multi-word keywords: unquoted eFLINT atoms cannot contain spaces, so `Valid`, `Except`, and `Due` remain atoms everywhere.
2. Single-word uppercase additions (`Document`, `Clause`, `Approved`, `Text`, `Norm`, `Definition`, `Acceptance`, `Commentary`, `From`, `Immunity`, `Against`, `Unless`, `Duration`, `Held`, `Param`, `Module`, `Use`, `As`, `Scenario`) lex as `.atom` tokens and are matched contextually by the parser only in declaration/clause positions and `Held(`; they remain valid unquoted atoms in `Identified by` lists and expressions.
3. Lowercase `tick` lexes as an ordinary identifier so eFLINT programs may declare `Event tick` and trigger `tick()` or `tick.`; a standalone `tick.` advances the clock only when no type `tick` is declared in scope.
4. `--eflint` remains accepted on the CLI as a no-op compatibility alias for existing scripts.

## Context
Previously `Lexer.lean` reserved Charter's 19 single-word uppercase additions and `tick` globally unless `--eflint` was passed, colliding with `Event tick` in `caretaker_contract/template.eflint` and with unquoted atoms in eFLINT programs. `docs/rfc.md` initially considered forking into two profiles (`eflint-4.1-compat` vs. `charter-1.x-strict`).

## Alternatives weighed
Two diverging profiles (`eflint-4.1-compat` vs. `charter-1.x-strict`): rejected — violates Law 12 and Law 13 and doubles the parser, specification, and proof matrix. Topological-SCC inflationary self-negation for `D6(b)` (`archetypes.eflint`): rejected — breaks post-state premise truth in `?why` / `ReasonGraph` (Law 6) and Tarski least-fixpoint translations.

## What the references do
eFLINT's GLL parser (`Parse.hs`) distinguishes lowercase `domId`s from uppercase `Atom`s; uppercase words cannot be applied to arguments or juxtaposed with identifiers or strings inside expressions, making declaration-level contextual matching deterministic with 1-token lookahead.

## Mission fit
Law 12 is literal without a mode flag: every stratified eFLINT 4.1 file is a Charter file as-is. Law 13 holds: one grammar, one meaning.

## Cost accepted
The parser checks 1-token lookahead on contextual uppercase frames (`Immunity`, `Clause`, `Document`, `Param`, `Module`, `Use`, `Scenario`, `Held(`) and `Resolve` checks `findDecl "tick"` on bare `tick.`.

## Reopens if
A planned syntax extension introduces a genuine LR(1)/LL(2) ambiguity with an existing eFLINT atom construct.
