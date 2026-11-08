# 010 — Expressions

**Status:** approved (Eric, 2026-11-06; Charter 1.0.0). Fixed by D2 (eFLINT `Eval.hs`, `StaticEval.hs`), D14, and D24. Implementation: compliant; all conformance tests pass.

An expression denotes zero or more values: a term with free variables takes every value it has under every binding of those variables to valid instances (004.7). A query over no values holds; a condition over no values is never true.

**10.1 Booleans.** `&&`, `||`, `!` and `Not`; `&&` and `||` do not evaluate the right operand when the left decides. `test/spec/spec_010_1_booleans.eflint`

**10.2 Arithmetic.** `+ - * / %` on integers; `/` and `%` round toward negative infinity (the sign of `%` follows the divisor), as eFLINT's Haskell `div` and `mod`. `+` and `-` also combine times and durations, and `*` and `/` scale a duration by an integer, as 009.2 says (D7, D16). `test/spec/spec_010_2_arithmetic.eflint`, `spec_009_2_time_and_duration_types.eflint`, `spec_009_2d_duration_times_int.eflint`

**10.3 Comparisons.** `< <= > >=` on integers; `==` and `!=` on integers, strings, booleans, and instances (structurally). For `==`/`!=` the two sides are resolved to one type by trying the left side's type first, then the right's. `test/spec/spec_010_3_comparisons.eflint`

**10.4 Conversions.** Resolution inserts: an instance of an integer or string type where that value is needed (`x + 1`), an instance where a condition is needed meaning *it holds*, an integer where a condition is needed meaning *at least 1*, and a value where an instance is needed meaning the instance of that value. Anything else is CHR012. `test/spec/spec_010_4_conversions.eflint`, `spec_010_10_type_error.eflint`

**10.5 `When`.** `e When c` is `e` where `c` holds and no value otherwise. `When`/`Where` has the lowest precedence and associates to the left (D14). `test/spec/spec_010_5_when.eflint`

**10.6 Quantifiers.** `(Exists xs: e)` holds if some binding of `xs` makes `e` true; `(Forall xs: e)` if every binding does. When a binder ranges over an enumerable type and `e` is a constant boolean literal (`True` or `False`), resolution warns with CHR028 because the quantifier tests only whether the domain is non-empty rather than whether an instance holds (`Exists f: f`). `test/spec/spec_010_6_exists_forall.eflint`, `spec_010_6b_vacuous_enumerable_exists.eflint`

**10.7 Aggregates.** `Count(Foreach xs: e)` is the number of values of `e`; `Sum`, `Max`, `Min` of integer values; `Max` and `Min` of no values are 0. When `xs` binds an enumerable type and `e` is an unfiltered constructor application `f(…)`, resolution warns with `CHR039` because `e` constructs an instance for every domain element without testing whether `f(…)` holds (`When f(…)`). `test/spec/spec_010_7_aggregates.eflint`, `spec_010_7b_count_of_constructor_warns.charter`

**10.8 State questions.** `Holds(e)` (also `Present(e)`), `Enabled(e)`, `Violated(e)` ask the three state questions of an instance (004, 005.5, 006.2); on a value that is not an instance they are CHR015. `test/spec/spec_010_8_holds_enabled_violated.eflint`, `spec_010_8b_holds_on_literal.eflint`

**10.9 Projection.** `e.x` is the component `x` of the product instance `e`; `x` must be a component of `e`'s type, else CHR016. `test/spec/spec_010_9_projection.eflint`, `spec_010_9b_projection_error.eflint`

**10.10 Precedence**, lowest to highest: `When`/`Where`; `||`; `&&`; `== != <= >= < >` (non-associative); `+ -`; `* / %`; the prefix operators `!`, `Not`, `Holds`, `Present`, `Violated`, `Enabled`; the postfix projection `e.x` and tag `e:t`; literals, variables, applications, and parenthesised forms. `Exists`, `Forall`, and the aggregates' `Foreach` are always parenthesised.

**10.11 Time.** `Current Time` is the clock (009.1), of type `Time`; `Held(e) For d` is the stamp condition (009.3).

**10.12 Dimensional `Money`/`Quantity` arithmetic and `MulDivRound` (`D24`, `G3.4`).** `+`, `-`, comparisons, and `Sum`/`Max`/`Min` preserve `Money(CUR, SCALE)` and `Quantity(UNIT)` across identical dimensional tags (with integer literals coercing by demand) and reject mismatched currencies, scales, or units with `CHR012`. `*` and `/` scale `Money` or `Quantity` by `Int`. `MulDivRound(x, num, den, Floor | Ceil | NearestEven | ExactOrReject)` evaluates `(x * num) / den` in exact integer arithmetic with explicit rounding, preserving `x`'s dimensional type and raising `CHR108` on zero `den` or inexact `ExactOrReject` (`T10`, `T11`). `test/spec/spec_010_12_money_tiers_and_rounding.charter`, `spec_010_12b_exact_or_reject_error.charter`

**10.13 Functional application, `Count(pred)`, `Amount`, `Decided by`, and bare `Bool` (`D36`, `#46`, `#50`, `#61`).** Applying a 2-component `Function f` to one key argument `f(k)` returns `f`'s value at `k`; `Count(pred)` counts holding instances of `pred`; `Amount name [: Dom] Is expr` defines a derived scalar value readable by name; `Decided by voter [Weighted by fn] At least n/d In vote-fact` adds a fractional or weighted ballot `Valid when` condition; `(Forall | Exists) v Except e: body` ranges over holding instances of `v` other than `e`; and 0-arity `Bool`/`Invariant` names may be written without `()`. `test/spec/spec_010_13_function_app_count_pred_amount_and_bool_bare.charter`

**10.14 Money literals, currency shorthands, declaration-site `Var` initializers, and `Rate`s (`D37`, `#42`, `#58`, `#22`).** `$10,000.00` and `$500` denote exact `Money(USD, 2)` minor units; `: USD` / `EUR` / `GBP` / `Rate` may appear directly in `Param`, `Var v : USD = init`, `Related to`, and `Identified by`; `6%` (`600 bps`), `5.25%` (`525 bps`), and `150 bps` have dimensional type `Rate` (rejected if added to `Money` or `Int`, `CHR012`), scaled via 3-argument `MulDivRound(amt, rate, mode)`; and 4-argument `MulDivRound(x, num, den, mode)` accepts same-unit dimensional ratios. `test/spec/spec_010_14_money_literals_rates_and_var_init.charter`, `spec_010_14b_rate_money_mismatch.charter`

**10.15 `Share`, `ProRata` with required `Remainder To`, `If`, and 2-argument `Min`/`Max` (`D37`, `#56`, `#45`).** `Share(pool Among party Remainder To target)` and `ProRata(pool By weightFn Among party Remainder To target)` divide `pool` by floor and assign the exact remainder `pool - sum(floors)` to `target` (omitting `Remainder To` is `CHR003`); `If(c, t, e)`, `Min(a, b)`, and `Max(a, b)` evaluate conditionally while preserving dimensional types. `test/spec/spec_010_15_share_prorata_remainder_and_waterfall.charter`, `spec_010_15b_share_requires_remainder.charter`

*Differences from eFLINT:* 10.5 and 10.10 commit to one reading where eFLINT's grammar has several (D14).
