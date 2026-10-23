# Tolerated differences from eFLINT

The complete list of ways Charter's outcome on a corpus file may differ from
eFLINT 4.1.0.1's, each under the decision that names the eFLINT defect and the
fix (D2). A difference not listed here is a Charter bug. `charter test` reads the
`Files` column: a listed file is expected to differ (the runner reports it as
`tolerated`, and fails if it unexpectedly matches eFLINT's outcome); an unlisted
failing file fails the run.

| Decision | eFLINT behaviour | Charter behaviour | Files whose test-mode outcome differs |
|---|---|---|---|
| D5 | effects of a disabled act apply | same, because `Valid when` defaults to true; an eFLINT program never writes `Valid when` | none |
| D6 | derivation is an unstratified inflationary fixpoint whose result can depend on type order (`Saturation.hs`) | stratified fixpoint; a program with a negative cycle is rejected with CHR020 | none found in the corpus as of 2026-10-23 (filled in when the corpus runs; see `HANDOFF.md`) |
| D7 | `Current Time` never advances; `Time` domain enumerates `0..time` | Phase 1 keeps time at 0 (no `@ t.` / `tick.` yet); the `Time` domain enumerates `0..0` | none |
| D12 | a violated duty is reported after every phrase while it stays violated | reported once, when it becomes violated; `Violated()` unchanged | none: test mode prints no violations |
| B9 (pending) | a second declaration of a type silently replaces the first | same, plus warning CHR019 | none: a warning does not fail a test. If B9 is ruled "error", `tests/truth/infinite_even.eflint` and `tests/parallel-comp/no_violations.eflint` move to this column |
