# D20 — Temporal `Property` declarations, fairness-gated liveness (`T31`), and symbolic `TVIR`/SMT (`T30`)

**Laws:** 7, 9, 10, 11, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §7.4, §7.6, §18.3)

## Ruling
1. Charter adds contextual `Property <name> [Assumes <id, ...>] When <TemporalFormula> [From CLAUSE "span"]` declarations (`Always φ`, `Always (e => Next ψ)`, `Always (req => Eventually resp)`, `Always (req => EventuallyWithin d resp)`, `Until(φ, ψ)`, `WeakUntil(φ, ψ)`), stored in `Spec.temporalProperties` outside the `Charter.Eval` TCB.
2. Unbounded liveness (`Always (req => Eventually resp)` and strong `Until`) requires explicit scheduler/clock fairness assumptions in `Assumes` (`T31`); without them, `charter verify` reports `INCONCLUSIVE` (exit `3`) rather than a vacuous finite-trace pass.
3. `charter verify` exposes `--backend finite | smt | inductive` (never engine names, `Law 11`):
   - `finite` checks `Invariant` and `Property` obligations over `Verify.Explorer` + `Verify.Temporal`;
   - `smt` lowers symbolic `Int`/`Time`/`Duration` transitions into `Verify.TVIR`, emits standard `QF_LIA` SMT-LIB2 (`--emit-smt`), runs `z3`/`cvc5` when available or the built-in linear-threshold witness solver, **replays every candidate counterexample natively through `Charter.Eval`**, and marks bounds shallower than `--min-depth` as `inconclusive` (`T30`);
   - `inductive` invokes the proof kernel over initial-state and step-preservation obligations.

## Context
State invariants (`Invariant`) cannot express bounded adjudication (`EventuallyWithin`), next-step transition postconditions, or fairness-conditioned liveness (`docs/rfc.md` §7.4), and finite `explore-domain` menus cannot search arbitrary symbolic `Int` thresholds without manual hints (`T30`).

## Mission fit
`Law 7` (time remains state over `s.time`, never synthetic timeout events), `Law 9` (every SMT counterexample is confirmed by the single proved `Charter.Eval`), `Law 10` (SMT/finite checks stay tagged `checked` with `bounded-exhaustive` scope, never `proved`), `Law 11` (`--backend inductive | finite | smt`).

## Cost accepted
`Spec` carries an inert `temporalProperties : List TemporalSpec := []` metadata field inspected by `Verify/`, `Pretty`, and `Provenance` only.

## Reopens if
Nested arbitrary-depth LTL quantifier alternation is needed beyond the six canonical temporal forms of `docs/rfc.md` §7.4.
