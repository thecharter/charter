# D13 — An instance named through a placeholder is an instance of the aliased type (third eFLINT tolerance; delegated)

**Laws:** 12, 13 (docs/mission.md).
**Date:** 2026-10-23
**Status:** delegated (agent prediction 85%; reversible; one line in `Eval.eval`). Eric may veto: a veto is a revert plus a new entry.

## Ruling
`Placeholder a For b` makes `a` another name for `b`. An instance written through the placeholder, `+a(1,2)`, is the instance `b(1,2)`: it is stored under `b`, every rule over `b` sees it, and `?b(2,1)` holds when a rule derives it. Charter tags every instance built by an application with the type the name resolves to (`Spec.chaseAlias`).

## Context
eFLINT's `Eval.hs` (`eval (App d params)`) returns `ResTagged (Product args, d)` with the name as written, so `+a(1,2)` stores an instance tagged `a`, while `every_valid_subs` for a variable of type `a` resolves the name to `b` and enumerates the instances tagged `b`. eFLINT's own test `tests/placeholders/with2.eflint` exercises exactly this and fails under eFLINT 4.1.0.1 (verified with the Haskell build: `query failed`). Variables already behave as Charter now does: `substitute_var` re-tags a bound value with the resolved type.

## Alternatives weighed
Keep the alias tag and make lookups alias-aware everywhere (state lookups, `assigned_instances`, projections). Rejected: two names for one instance in the state is a second spelling of one fact (Law 13), and every reader of the state would have to know the alias table.

## What the references do
eFLINT: as above. Catala: no aliases of types. Quint: `import … as` renames a module, not a type; instances are values of one type. Symboleo: no aliasing.

## Mission fit
Law 13: a placeholder is a spelling, not a type; one instance, one tag. Law 12: eFLINT's documented defect (its own failing test) is fixed under a decision and listed in `test/eflint-corpus/tolerances.md`.

## Cost accepted
A program that relied on `a(1,2)` and `b(1,2)` being different instances changes meaning; none exists in the corpus, and such a program would contradict `Placeholder`'s documented purpose.

## Reopens if
Eric vetoes, or Phase 2's resolved AST wants placeholders erased at resolution instead (then this rule is implemented there and the evaluator never sees an alias).
