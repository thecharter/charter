# D14 — In `e When c` the condition extends as far right as it can: `When`/`Where` has the lowest precedence (fourth eFLINT tolerance; delegated)

**Laws:** 8, 12, 13 (docs/mission.md).
**Date:** 2026-10-23
**Status:** delegated (agent prediction 85%; reversible: one precedence level in `Charter.Surface.Parser`). The normative wording of spec chapters 010 (expressions) and 020 (grammar) is Eric's; this entry fixes the behaviour and the tolerance until he words it.

## Ruling
Expression precedence, lowest to highest: `When`/`Where` (left-associative), `||`, `&&`, the comparisons (`== != <= >= < >`, non-associative), `+ -` (left), `* / %` (left), the prefix operators `!`/`Not`/`Holds`/`Present`/`Violated`/`Enabled`, the postfix projection `e.x` and tag `e:t`, atoms. So `Terminates grounded When date + 1 == grounded.date` means `Terminates grounded When ((date + 1) == grounded.date)`.

## Context
eFLINT's grammar (`Parse.hs`, `value_expr`) lists `When` as an alternative with no priority annotation; its generalised (GLL) parser produces every parse and the interpreter takes the first. On the examples repository's own `homework-benchmark/caretaker_contract/template.eflint` line 68 it takes `((grounded When date) + 1) == grounded.date` and rejects the program with "cannot convert TyTagged grounded to TyInts" (verified with the Haskell build). The author's comment on line 58, "grounded until `date + days`", says what was meant. The four files that include the template fail in eFLINT and pass in Charter.

## Alternatives weighed
- Reproduce eFLINT's choice. Rejected: it rejects a well-typed program for an ill-typed reading of it, and the reading is not what the English says (Law 8).
- Require parentheses around a `When` condition. Rejected: the corpus writes `+x(y) When y == 5`, `Creates values When (values % 2 == 0)`, and `… When data-provider-for(sender, application) && …` unparenthesised, and all read as intended under the lowest-precedence rule.

## What the references do
Catala: `under condition … consequence` is a clause, not an expression operator; no ambiguity. Quint: no conditional-filter operator; `if` is an expression with mandatory `else`. Symboleo: `when`/`until` are clause keywords. All three commit to one grammar; none keeps every parse.

## Mission fit
Law 13: one spelling, one reading. Law 12: an eFLINT defect (an ambiguity the tool resolves against the program's own author) fixed under a decision and listed in `test/eflint-corpus/tolerances.md`. Law 8: the reading matches the English beside it.

## Cost accepted
A Charter reading can differ from eFLINT's for an unparenthesised `When` with an arithmetic or comparison right-hand side; every such corpus occurrence agrees with the author's intent under this rule and the four that differ fail in eFLINT.

## Reopens if
Eric words chapter 010 differently, or the PSA rewrite finds a clause whose natural spelling wants `When` to bind tighter than `||`.
