# D45 — The Quint target carries a rule's guard and effects or refuses the program; it never writes `true` for what it cannot say

**Laws:** 5, 9, 10, 11, 14 (`docs/mission.md`). Instance of `D28` and spec `017.2`; no spec wording changed.
**Date:** 2026-11-18
**Status:** delegated (implemented under `D28` / `017.2`; Eric vetoes afterwards)

## What was wrong

`main` was red in CI on all eight runs (head `de90413`): `projections` 7 passed, 1 failed. The failing case was `d42-differential-targets`, at `quint parse`:

```
Error [QNT000]: extraneous input 'fact_active_lease' expecting {'}', ','}
  13:     fact_active_lease' = Set() // Set[(str, str)],
```

`renderQuintModule` wrote each `init` assignment's separating comma after a `//` comment, so the comma was commented out. The local battery was green because `tools/differential-targets-check` skipped `quint` (and `solc`, `forge`, `z3`) without a word when they were not installed.

The parse error was the visible part. The emitted model carried none of the program: every action's effect was `clock_now' = clock_now`, `qntTerm` fell through to `"true"` for any term it did not handle (every quantifier, so the lease fixture's invariant was `val inv_single_active_lease: bool = true`), `step` called each action on `""`, and the "imported counterexample" `--verify-output` reported was found and replayed by Charter's own explorer with the Quint text never consulted. That is the silent dropping `017.2` and `AGENTS.md` ("No silent fallbacks") forbid.

## Ruling (delegated)

1. `compileQuintModule` lowers each act, event, and invariant through the finite guard fragment the Solidity target already uses (`compileSolExpr`, `compileSolEffect`). An action has its `Holds when` and `Conditioned by` as `lawful_…`, its `Valid when` as `valid_…`, and its `Creates [For d]` / `Terminates` as updates to one `held_` set and one `exp_` map per fact, create beating terminate (`005.3`), expiry half-open (`D7`).
2. Anything outside that fragment is `CHR035` naming the rule and the construct. The list is in `docs/targets.md`.
3. An act component that is not enumerable needs an `explore-domain` menu, or the act is refused. The explorer's fallback (every value held in the current state) changes as the state changes; a model has one fixed universe.
4. Of `Property` forms only `Always` over a state condition is carried. Quint has no `until`; `Next` and the fairness-gated forms (`D20`) were not shown to mean the same thing there.
5. `--verify-output` explores the model's step relation and the evaluator in lockstep to depth 3 (`differentialQuint`), failing on the first difference in candidate steps, state, or violated invariants. In CI the emitted text is typechecked by `quint` and Quint's simulator must reach Charter's verdict.

## Evidence

- `charter generate --target quint --mode adversarial --verify-output test/verify/safe_fenced_lease.charter`: 50 reachable states safe, 138 steps agree with the evaluator (the old explorer-only run also visited 50).
- `test/verify/t26_t27_partition_lease.charter`: counterexample for `single-authority-fenced` in 1 step on both; `quint run` finds the same step (`unfenced-activate("Coord", N2)`).
- `test/verify/quint_booking_effects.charter` (new): 450 steps agree in adversarial mode, 36 in lawful.
- `tools/projections-check` with all four tools required: 13 passed, 0 failed.

## Alternatives weighed

- **Move the comma.** Makes CI green over a model that says nothing. Dropped: `AGENTS.md`, "did I make the success condition true by doing the work, or by redefining the success condition?"
- **A second lowering written for Quint.** A second derivation of what a guard means (One owner per fact). The guard IR has a proved step semantics (`execSolStep_sound`) and a differential check already.
- **Candidates from the starting state when no menu is given, stated as an assumption.** Matches `charter explore` at step 0 and diverges after any step that adds a value. Dropped for item 3.

## Cost accepted

The Quint fragment is the Solidity guard fragment plus events, clock advances, and invariants; it is smaller than the row `docs/targets.md` used to claim. `benchmarks/04_veil_quint_lease_handover.charter` (a `WeakUntil` property) and `Examples/TreasuryMandate` are refused. `test/verify/t26_t27_partition_lease.charter` gained `//! explore-domain: actor = "Coord"`. Rejection messages that come from `compileSolExpr` still speak of the Solidity guard.

## Reopens if

A trace found by Quint is imported and replayed (`B35`), which would let the check read the emitted text rather than the model it was printed from; or derived facts are lowered into the guard IR, which widens both targets at once.
