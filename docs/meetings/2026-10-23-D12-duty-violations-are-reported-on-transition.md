# D12 — A duty's violation is reported once, when it begins; `Violated()` still answers at any time (second eFLINT tolerance; delegated)

**Laws:** 2, 3, 7, 12 (docs/mission.md). Plan §2.1 ("duties are re-reported while they stay violated").
**Date:** 2026-10-23
**Status:** delegated (agent prediction 80%; reversible; output only, no change to what holds). Eric may veto: a veto is a revert of the report filter plus a new entry.

## Ruling
After each phrase, `charter run` reports a duty violation only for duties that are violated now and were not violated after the previous phrase (and, for a parallel block, were not violated before the block). The *state* of being violated is unchanged: `Violated(d)` evaluates the duty's `Violated when` conditions against the current state at any time, exactly as eFLINT does, and the query answers are unaffected. Invariant violations and disabled-act violations are events of the phrase that produced them and are reported as eFLINT reports them.

## Context
eFLINT's `Interpreter.hs` (`new_context`) recomputes `find_duty_violations` over every held duty after every phrase and emits all of them, so a duty violated for ten phrases is reported ten times. eFLINT's own `TODO.txt` records the intent to change this: "new duties and newly violated duties should be computed rather than collected (so that a violated duty which is immediately satisfied by next phrases is not reported if two phrases are composed)". The test corpus is unaffected: in `--test-mode` eFLINT prints no violations at all (`REPL.hs`, `display_violations` is `Default` verbosity), so a test passes or fails on errors and failed queries only.

## Alternatives weighed
- Re-report every phrase (eFLINT today). Rejected: the report stream then says "a breach occurred" once per phrase for one breach, which reads as a new event each time (Law 3: a breach is recorded when it occurs; Law 7: the persistence of a fact is state, not a sequence of events).
- Report once and also print the set of currently violated duties after each phrase. Not needed for `run`; it is a query (`?Violated(d)`, and `?-` over duties) and belongs to `charter repl`/`why` if wanted.

## What the references do
- eFLINT: re-reports (`Interpreter.hs:new_context`, `State.hs:Violation`); intends otherwise (`TODO.txt`).
- Symboleo: an obligation enters the `violated` state once in its lifecycle automaton (`.reference/symboleo/pc/.../SymboleoPC-library.nuXmv`); monitors observe the transition.
- Catala, Quint: no deontic reporting.

## Mission fit
Law 2: the report answers "did a breach begin at this step" and the query answers "is this duty violated now"; two questions, two outputs, neither collapsed into the other. Law 12: eFLINT's *meaning* (which duties are violated when) is unchanged; only the default-mode print differs, and the difference is listed in `test/eflint-corpus/tolerances.md`.

## Cost accepted
`charter run` output differs from `eflint-repl` default output for persistent violations. A consumer that wants the full violated set after each phrase queries it.

## Reopens if
A projection or the LSP needs the full violated set per phrase as a report rather than a query, or Eric vetoes.
