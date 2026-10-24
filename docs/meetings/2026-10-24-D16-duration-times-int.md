# D16 — `Duration * Int`, `Int * Duration` and `Duration / Int` are durations; a duration is never multiplied by a duration, an instant is never scaled

**Laws:** 8, 13 (docs/mission.md).
**Date:** 2026-10-24
**Status:** ruled by Eric (brief B12, `2026-10-24-briefs-for-ruling.md`). Spec wording of 009.2 and 010.2 below is the agent's rendering; Eric's replaces it when written.

## Ruling
Allow `Duration * Int`, `Int * Duration`, and `Duration / Int`, each a `Duration`; `/` rounds toward negative infinity, as `Int /` does and as D10 asks of every division ("every division states its rounding"). Refuse `Duration * Duration`, `Time * anything`, `anything * Time`, `Time / anything`, and `Int / Duration`, all CHR012. In `*`, at most one operand may be a `Duration`. A literal beside a `Duration` resolves to `Int`, so `base * 2` is unambiguous under D7's coerce-by-demand rule. `Duration / Duration : Int` (a ratio) is deferred until the PSA asks: one spelling per meaning argues against operators nobody has needed.

## Context
`Charter/Modules/CollateralPool.lean` scales an observation window multiplicatively (`base * max 1 domainMultiplier * max 1 irreversibilityMultiplier`). Charter had `Duration + Duration` only, so `lib/collateral_pool.eflint` wrote the window as a base plus one extension per risk class and admitted the deviation in its header.

## Why, in Eric's words
The decisive argument is Law 8, not convenience. The protocol's English scales the window multiplicatively; `base + risk-extension` is a lowering that behaves differently from the sentence it cites. That is the workaround category the rules forbid regardless of what tests say, and the module header admitting it is a report that the language is wrong.

## Alternatives weighed
- Durations additive only. Rejected: Law 8, above.
- Also `Duration / Duration : Int`. Deferred: no clause has asked for a ratio.

## What the references do
Quint and Catala treat durations as integers or dates with integer arithmetic; neither distinguishes the types, so neither has the question. D7 made the distinction, so Charter has to say which products exist.

## Mission fit
Law 8: the window is written as the English says it. Law 13: one spelling for scaling, `*`.

## Cost accepted
Resolve's arithmetic typing gains a second table (`compileScale`) beside `compileArith`.

## Implementation
`Resolve.compileScale`; fixtures `spec_009_2d_duration_times_int` (seen failing with 14 CHR012 before the change), `spec_009_2e_no_duration_times_duration`, `spec_009_2f_no_int_over_duration`, `spec_009_2g_no_time_times_int`. `lib/collateral_pool.eflint`: multipliers as `Param`s, per-action factors derived (1 where the class does not apply or the multiplier is below 1, the Lean module's `max 1`), one `commit` act, window `base-observation-window * risk-factor.int * irreversibility-factor.int`.

## Reopens if
The PSA rewrite needs a ratio of durations, or a calendar (D7's deferral) makes scaling non-uniform.
