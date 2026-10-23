# 011 — Phrases and scenarios

**Status:** draft (2026-10-23). Meaning fixed by D2 (eFLINT `Interpreter.hs`, `REPL.hs`); wording awaits Eric. Implementation: compliant, including 11.11 (`Scenario` and the claim phrases, Phase 2's first slice).

A file is a sequence of phrases and directives. Each phrase is a step: it is resolved against the current declarations, evaluated against the current state, its effects are applied, derived facts are recomputed (004.4), and violations are reported (006.5).

**11.1 Assignments.** `+e` makes the instances `e` produces hold; `-e` makes them not hold; `~e` forgets their assignment. Free variables are bound to every valid instance, so `+x.` over an enumerable type creates every instance and over a non-enumerable one re-asserts those that hold. `test/spec/spec_011_1_assignments.eflint`

**11.2 Triggers.** `a(args)`, `(Foreach xs: a(args))`, or `a` performs every instance the term produces (005, 008). `test/spec/spec_011_2_triggers_enumerate.eflint`

**11.3 Queries.** `?e` holds when every value of `e` is true (and when `e` has no value); `?!e` and `!?e` query the negation; `?-e` lists the instances `e` produces and `?--e` those that hold. A query is a *claim* tagged *checked*, about *holds*; a failed query fails `charter test` and is never a diagnostic. `test/spec/spec_011_3_queries.eflint`

**11.4 Free variables in queries.** The free variables of a query are bound existentially; for `?!e` the quantifier is inside the negation (`?!p` asks that no `p` holds). `test/spec/spec_011_4_free_variables_existential.eflint`

**11.5 Parallel blocks.** `{ p₁. p₂. … }` evaluates every phrase against the same state and merges their effects with create > terminate > obfuscate (005.3); declarations in the block take effect first; a query inside is answered in the state before the block. If any phrase fails, the block has no effect. `test/spec/spec_011_5_parallel_block.eflint`

**11.6 Declarations.** A block of declarations is a phrase; its types and placeholders are introduced together, so they may refer to each other in any order, and extensions apply after. `test/spec/spec_011_6_declarations_are_phrases.eflint`

**11.7 Directives.** `#include "f"` splices the items of `f` at that point; `#require "f"` does so once per file. `f` is resolved against the including file's directory, the directories of every file included so far, and the working directory, with `.eflint` appended when needed; a file that cannot be found is CHR005. `test/spec/spec_011_7_include_require.eflint`

**11.8 Terminators.** Every phrase ends with `.`; the last phrase of a file may omit it. A declaration block ends with `.` like any phrase: a `+` after an unterminated declaration continues the declaration (as a list or an expression), never starts a phrase. `test/spec/spec_011_8_terminator.eflint`, `spec_011_10_declarations_need_terminator.eflint`

**11.9 Failure.** A phrase that produces an error diagnostic leaves the configuration unchanged; later phrases run against the state before it. `test/spec/spec_011_9_failed_phrase_leaves_state.eflint`

**11.10 Test mode.** `charter test` passes a file that produces no error diagnostic and whose every claim holds (eFLINT's `--test-mode` criterion); `//!` directives may instead expect a diagnostic or declare a known issue (`src/Charter/Cli/Test.lean`). `--eflint` restricts the keywords to eFLINT's, so a corpus file may use `Valid`, `Against`, or `Scenario` as atoms (002.3). `test/spec/spec_002_9_eflint_mode.eflint`

**11.13 `?why`.** `?why e` reports the origin of each instance of `e` (004.10); it is a report, not a claim, and never fails a test.

**11.12 The clock.** `@ t.` and `tick.` are phrases that set the clock (009.1); they are environment input, report no transition, and recompute derived facts and violations like any phrase.

**11.11 Scenarios and claims.** `Scenario name { phrases }` is a named test: `charter test` runs its phrases from the configuration at that point in the file and leaves it unchanged; `charter run` only notes it. `?lawful e`, `?valid e`, `?violated e` are claims about the instances of `e` (an act or duty instance; free variables bound to every instance), labelled with the question they answer (Law 2); `?!lawful`, `?!valid`, `?!violated` claim the opposite. A claim keyword is one only when followed by whitespace, so `?valid(5)` queries a fact named `valid`. `test/spec/spec_011_11_scenario.eflint`, `spec_011_11b_expectations.eflint`
