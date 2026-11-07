# 011 — Phrases and scenarios

**Status:** approved (Eric, 2026-11-06; Charter 1.0.0). Fixed by D2, D7, D10, D17, D22, and D23. Implementation: compliant (`src/Charter/Eval/Step.lean`, `src/Charter/Eval/Interpreter.lean`).

A file is a sequence of phrases and directives. Each phrase is a step: it is resolved against the current declarations, evaluated against the current state, its effects are applied, derived facts are recomputed (004.4), and violations are reported (006.5).

**11.1 Assignments.** `+e` makes the instances `e` produces hold; `-e` makes them not hold; `~e` forgets their assignment. Free variables are bound to every valid instance, so `+x.` over an enumerable type creates every instance and over a non-enumerable one re-asserts those that hold. `test/spec/spec_011_1_assignments.eflint`

**11.2 Triggers.** `a(args)`, `(Foreach xs: a(args))`, or `a` performs every instance the term produces (005, 008). The term of a trigger, a `+`, a `-`, or a `~` denotes an instance: a bare number, string, or condition is CHR012 (so `10000.00.`, which is the integer `10000`, a terminator, and the phrase `00.`, is refused). `test/spec/spec_011_2_triggers_enumerate.eflint`, `spec_011_2b_bare_literal_is_not_a_phrase.charter`

**11.3 Queries.** `?e` holds when every value of `e` is true (and when `e` has no value); `?!e` and `!?e` query the negation; `?-e` lists the instances `e` produces and `?--e` those that hold. A query is a *claim* tagged *checked*, about *holds*; a failed query fails `charter test` and is never a diagnostic. `test/spec/spec_011_3_queries.eflint`

**11.4 Free variables in queries.** The free variables of a query are bound existentially; for `?!e` the quantifier is inside the negation (`?!p` asks that no `p` holds). `test/spec/spec_011_4_free_variables_existential.eflint`

**11.5 Parallel blocks.** `{ p₁. p₂. … }` evaluates every phrase against the same state and merges their effects with create > terminate > obfuscate (005.3); declarations in the block take effect first; a query inside is answered in the state before the block. If any phrase fails, the block has no effect. `test/spec/spec_011_5_parallel_block.eflint`

**11.6 Declarations.** A block of declarations is a phrase; its types and placeholders are introduced together, so they may refer to each other in any order, and extensions apply after. `test/spec/spec_011_6_declarations_are_phrases.eflint`

**11.7 Directives.** `#include "f"` splices the items of `f` at that point; `#require "f"` does so once per file. `f` is resolved against the including file's directory, the directories of every file included so far, and the working directory, with `.eflint` appended when needed; a file that cannot be found is CHR005. `test/spec/spec_011_7_include_require.eflint`

**11.8 Terminators.** Every phrase ends with `.`; the last phrase of a file may omit it. A declaration block ends with `.` like any phrase: a `+` after an unterminated declaration continues the declaration (as a list or an expression), never starts a phrase. `test/spec/spec_011_8_terminator.eflint`, `spec_011_10_declarations_need_terminator.eflint`

**11.9 Failure.** A phrase that produces an error diagnostic leaves the configuration unchanged; later phrases run against the state before it. `test/spec/spec_011_9_failed_phrase_leaves_state.eflint`

**11.10 Test mode.** `charter test` passes a file that produces no error diagnostic and whose every claim holds (eFLINT's `--test-mode` criterion); `//!` directives may instead expect a diagnostic or declare a known issue (`src/Charter/Cli/Test.lean`). Under the unified contextual grammar (002.9, D17), `.eflint` and `.charter` files share one parser without needing `--eflint`. `test/spec/spec_002_9_eflint_mode.eflint`

**11.13 `?why`.** `?why e` reports the origin of each instance of `e` (004.10); it is a report, not a claim, and never fails a test.

**11.12 The clock.** `@ t.` and `tick.` are phrases that set the clock (009.1); they are environment input, report no transition, and recompute derived facts and violations like any phrase.

**11.11 Scenarios and claims.** `Scenario name [From CLAUSE "span" …] { phrases }` is a named test: `charter test` runs its phrases from the configuration at that point in the file and leaves it unchanged; `charter check` resolves its phrases without leaking local declarations and verifies any `From` spans against the clause (012.3, D10); `charter run` only notes it. `?lawful e`, `?valid e`, `?violated e`, `?undetermined e`, `?conflict e` are claims about the instances of `e` (an act, duty, or defeasible fact instance; free variables bound to every instance), labelled with the question they answer (Law 2, D22, D23); `?!lawful`, `?!valid`, `?!violated`, `?!undetermined`, `?!conflict` claim the opposite. A claim keyword is one only when followed by whitespace, so `?valid(5)` queries a fact named `valid`. `test/spec/spec_011_11_scenario.eflint`, `spec_011_11b_expectations.eflint`, `spec_012_3c_scenario_from.eflint`

**11.14 Epistemic evidence phrases and advisory notes (`D22`, `G3.2`).** `SubmitEvidence [!]e [By s].` and `RetractEvidence e [By s].` tender or retract external evidence on an `Evidenced` fact `e` (`CHR033` if `e` is not `Evidenced`). A trigger phrase may carry a trailing `Note "…"` recording non-operative advisory commentary (`T04`: advisory notes never affect lawfulness, validity, or state transitions). `test/spec/spec_003_13_evidenced_unresolved.charter`, `spec_004_11_metamorphic_impartiality.charter`
