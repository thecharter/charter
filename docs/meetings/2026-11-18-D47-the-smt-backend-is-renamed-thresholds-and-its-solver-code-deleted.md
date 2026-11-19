# D47 — The `smt` backend ran no solver: it is renamed `thresholds`, `--backend smt` is refused, and the solver code is deleted

**Laws:** 10, 13, 14 (`docs/mission.md`). Brief `B36` (`2026-11-18-briefs-for-ruling.md`). Corrects `D20` (`T30`) and `docs/claims.json`.
**Date:** 2026-11-18
**Status:** ruled (Eric, 2026-11-18): option A as predicted, sharpened: the name and the dead code go too

## Context

`charter verify --backend smt` wrote `TVIR.emitSmtLib2`, ran `z3` on it, and on any answer set its label to `smt/z3+native-replay`. The verdict came from `Verify.search` over a menu of threshold witnesses. The encoding declared one `Bool` per type and, for `test/verify/t30_smt_symbolic_int.charter`, asserted `(or (not (not true)))`: `z3` answered `sat` at depth 1, 2, and 3 while Charter reported safe at depth 1 and violated at 2 and 3. `docs/claims.json` said "CI solc/Foundry + quint + z3 execution". The CI step that exercised it ran a fixture that did not exist under `|| true`. A label that says a solver took part in a verdict it did not take part in is a false claim tag (`Law 10`).

## Ruling

1. The backend is named for what it does: `--backend thresholds` (`src/Charter/Verify/Thresholds.lean`). It offers `c - 1, c, c + 1` around every integer constant of the program as candidates for every integer-carried type and runs the ordinary bounded search; every step is a step of `Charter.Eval`. Output label `[thresholds]`; the certificate note is `backend=thresholds`.
2. `--backend smt` is a usage error (exit 2) that says it is not implemented. It does not fall through to another search.
3. Deleted, not deprecated (`Law 13`): `--solver`, `--emit-smt`, `findBinary`, `runExternalSolver`, `SolverChoice`, `TVIR.emitSmtLib2`, `renderSmtTerm`, `smtIdent`, the `z3`/`cvc5` lines of `charter doctor`, the `z3` step of `tools/differential-targets-check`, and the `z3` install in CI.
4. A program that couples integer variables (`x + y`, `x * y`, a sum) is outside the fragment where threshold witnesses cover every case. The backend used to pass it when a solver binary was on `PATH`. It is now always `INCONCLUSIVE`, which is the truthful answer until a solver-backed backend exists.
5. `docs/claims.json` (`project.emitted_targets_differential_checked`), spec `013` and `018`, the README, and the usage text say `thresholds` and name no solver.

## Exit criterion for a solver-backed backend (Eric's, set before the work starts)

The trap was an encoding that could not fail. A solver-backed backend is done only when:

- there is a fixture where the solver's answer and the threshold search **disagree**, and the disagreement is explained; and
- the encoding has either a faithfulness theorem against the guard IR or a differential suite against the evaluator.

A check that cannot fail is not a check.

## Evidence

- `test/verify/d47_coupled_arithmetic.charter` (new): the guard is `amount + credit < 100` and the invariant bounds `amount` by 1000000. The threshold witnesses never pair `amount = 1000001` with `credit = -1000001`; the backend reports `INCONCLUSIVE` (exit 3). With that pair supplied by `--explore-domain` the same command finds the violation in one step. This is the first half of the exit criterion's fixture: a program the threshold search cannot decide and a solver could.
- `tools/verify-check`: 22 passed. `--backend smt`, `--solver`, and `--emit-smt` each exit 2.
- `rg -i 'smt|z3|cvc5' src/Charter` finds only the refusal message and the two module headers that say what was deleted.

## Alternatives weighed

- **Keep the name, fix the label.** A backend called `smt` that runs no solver is a second misnomer replacing the first.
- **Leave `--emit-smt` switched off.** An option that exists and does nothing is a spelling to maintain and a promise in the usage text.
- **B, write the encoding now.** Its own work package, with the exit criterion above.

## Cost accepted

`test/verify/t30_smt_symbolic_int.charter` is renamed `t30_threshold_symbolic_int.charter`. Anyone who scripted `--backend smt` gets exit 2 and a message naming `thresholds`. `docs/rfc.md` still describes an SMT backend as design intent (§10, §14 `T30`); it is the plan, not a claim about the binary, and is left for Eric.

## Reopens if

The solver-backed backend is taken up, under the exit criterion above.
