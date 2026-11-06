# D23 — Stratified `Default` / `Exception` / `Priority` calculus and typed `Conflict` (`T21`, `T22`)

**Laws:** 4, 5, 9, 10, 12, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §3.6, §4.4, §18.3)

## Ruling
1. **Named defeasible rules on `Fact`, `Bool`, `Var`, and `Function` (`004.12`, `007.6`)**:
   - Relational (`Fact`/`Bool`): `Default <id> (Holds when | Rejects when) <expr>` and `Exception <id> Overrides <id, ...> (Holds when | Rejects when) <expr>`.
   - Functional (`Function`/`Var`): `Default <id> Yields <val> When <cond>` and `Exception <id> Overrides <id, ...> Yields <val> When <cond>`.
   - Explicit priority edges: `Priority <higher-id> Over <lower-id, ...>`.
2. **Static acyclicity & stratification (`CHR034`)**:
   - `Resolve` verifies that all `Overrides` and `Priority ... Over` targets name declared defeasible rules on the same type (`CHR010`) and that the transitive priority relation `beats` is strictly acyclic (`CHR034` on any cycle).
   - All rule guards and value expressions participate in `Stratify.strata` (`D6`), providing Charter's stratified replacement for `archetypes.eflint`'s cyclic self-negating default pattern without relaxing `CHR020`.
3. **No last-rule-wins; explicit `Conflict` (`T21`, `T22`)**:
   - Among active rules on an instance/key, a rule is undefeated iff no higher-ranked (`beats⁺`) rule is active.
   - If undefeated active rules agree on a single outcome, that outcome holds (`T22`, including multi-level Catala exception-to-exception chains).
   - If two undefeated active rules prescribe distinct outcomes (`true` vs. `false`, or `v₁ ≠ v₂`), **neither** outcome holds, a derived normative conflict `(r₁, r₂)` is recorded and reported (`Output.conflict`, `Conflict(e)`, `?conflict e`), and any `Act`/`Power` guard reading that conflicted proposition evaluates to `TriBool.undetermined` (`T21`).
   - `evalCompiledDAG_eq_spec` (`Core/Defeasible.lean`) proves that single-pass topological decision-DAG evaluation equals the declarative undefeated-rule specification.

## Context
Statutory and contractual drafting relies heavily on general defaults, scoped exceptions, and exceptions to exceptions (Catala's motivating calculus), while arbitrary textual rule ordering ("last rule wins") silently masks drafting conflicts (`T21`).

## Mission fit
`Law 4` (statutory rule-priority exceptions have their own explicit spelling distinct from `Except under`, `Overridden by`, and `Immunity`), `Law 5` (rules and priority edges are inspectable data), `Law 9` (compiled decision DAG proved equivalent to declarative spec), `Law 12` (contextual keywords keep 196/196 eFLINT compatibility).

## Cost accepted
Derived conflict markers live in `State.contents` (`$def_conflict`, `fromSat = true`) so `State.rebase` clears and recomputes conflicts automatically on every transition.

## Reopens if
Cross-module priority declarations (`Priority modA.r1 Over modB.r2` across distinct `Fact` names) are needed beyond `lib/jurisdiction.charter` (`G3.6`).
