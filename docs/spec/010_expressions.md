# 010 — Expressions

**Status:** draft (2026-10-23). Meaning fixed by D2 (eFLINT `Eval.hs`, `StaticEval.hs`) and D14; wording awaits Eric. Implementation: compliant; all tests pass.

An expression denotes zero or more values: a term with free variables takes every value it has under every binding of those variables to valid instances (004.7). A query over no values holds; a condition over no values is never true.

**10.1 Booleans.** `&&`, `||`, `!` and `Not`; `&&` and `||` do not evaluate the right operand when the left decides. `test/spec/spec_010_1_booleans.eflint`

**10.2 Arithmetic.** `+ - * / %` on integers; `/` and `%` round toward negative infinity (the sign of `%` follows the divisor), as eFLINT's Haskell `div` and `mod`. `+` and `-` also combine times and durations, and `*` and `/` scale a duration by an integer, as 009.2 says (D7, D16). `test/spec/spec_010_2_arithmetic.eflint`, `spec_009_2_time_and_duration_types.eflint`, `spec_009_2d_duration_times_int.eflint`

**10.3 Comparisons.** `< <= > >=` on integers; `==` and `!=` on integers, strings, booleans, and instances (structurally). For `==`/`!=` the two sides are resolved to one type by trying the left side's type first, then the right's. `test/spec/spec_010_3_comparisons.eflint`

**10.4 Conversions.** Resolution inserts: an instance of an integer or string type where that value is needed (`x + 1`), an instance where a condition is needed meaning *it holds*, an integer where a condition is needed meaning *at least 1*, and a value where an instance is needed meaning the instance of that value. Anything else is CHR012. `test/spec/spec_010_4_conversions.eflint`, `spec_010_10_type_error.eflint`

**10.5 `When`.** `e When c` is `e` where `c` holds and no value otherwise. `When`/`Where` has the lowest precedence and associates to the left (D14). `test/spec/spec_010_5_when.eflint`

**10.6 Quantifiers.** `(Exists xs: e)` holds if some binding of `xs` makes `e` true; `(Forall xs: e)` if every binding does. `test/spec/spec_010_6_exists_forall.eflint`

**10.7 Aggregates.** `Count(Foreach xs: e)` is the number of values of `e`; `Sum`, `Max`, `Min` of integer values; `Max` and `Min` of no values are 0. `test/spec/spec_010_7_aggregates.eflint`

**10.8 State questions.** `Holds(e)` (also `Present(e)`), `Enabled(e)`, `Violated(e)` ask the three state questions of an instance (004, 005.5, 006.2); on a value that is not an instance they are CHR015. `test/spec/spec_010_8_holds_enabled_violated.eflint`, `spec_010_8b_holds_on_literal.eflint`

**10.9 Projection.** `e.x` is the component `x` of the product instance `e`; `x` must be a component of `e`'s type, else CHR016. `test/spec/spec_010_9_projection.eflint`, `spec_010_9b_projection_error.eflint`

**10.10 Precedence**, lowest to highest: `When`/`Where`; `||`; `&&`; `== != <= >= < >` (non-associative); `+ -`; `* / %`; the prefix operators `!`, `Not`, `Holds`, `Present`, `Violated`, `Enabled`; the postfix projection `e.x` and tag `e:t`; literals, variables, applications, and parenthesised forms. `Exists`, `Forall`, and the aggregates' `Foreach` are always parenthesised.

**10.11 Time.** `Current Time` is the clock (009.1), of type `Time`; `Held(e) For d` is the stamp condition (009.3).

*Differences from eFLINT:* 10.5 and 10.10 commit to one reading where eFLINT's grammar has several (D14).
