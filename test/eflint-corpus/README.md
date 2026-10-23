# The eFLINT corpus

Vendored unchanged (D2, plan §5.4) and run as Charter regression tests. Every file
here is protected: a Charter change that breaks one is a defect in the change
(`AGENTS.md`, "Editing a protected program to make it pass"). The only accepted
differences between eFLINT's outcome and Charter's are the ruled tolerances in
`tolerances.md`, each naming its decision.

## Provenance

| Directory | Source | Commit |
|---|---|---|
| `tests/` | `https://gitlab.com/eflint/haskell-implementation`, `tests/` | `7c74596dad69fa2072cbc44175af1b745ef3ee0a` (2026-08-24, "HTML version of report not needed"), eFLINT 4.1.0.1 |
| `examples/` | `https://gitlab.com/eflint/eflint-examples` | `da4b194e6a9a8e206137bc6990b9abd938ea3bed` (2026-07-06, "fixed example, generalised hardcoded 10 and brought in sync with paper") |

`LICENSE-eflint` is the BSD-3 licence of the Haskell implementation and covers
`tests/`. The examples repository ships no licence file; it is published under
the same eFLINT project by the same authors, and the files are retained here as
test inputs only.

## What a test means

eFLINT's own runner (`run_tests.sh` in the implementation) runs each file in
`tests/` with `eflint-repl <file> --test-mode` and passes it when the exit status
is zero and standard output is empty. In test mode eFLINT prints only
compilation and runtime errors (including missing input for open types), failed
queries (`query failed`), and the results of instance queries (`?-`, `?--`).
Violations and transitions are not printed. `charter test` applies the same
criterion: a file passes when it produces no diagnostic and every claim holds.

`examples/` is run the same way. Files that only declare types pass trivially;
scenario files `#require` their models relative to their own directory.

## Running

    charter test test/eflint-corpus/tests test/eflint-corpus/examples

`tools/battery` runs this as part of the PR tier and fails if any file outside
`tolerances.md` fails, or if a file listed there passes (a tolerance that is no
longer needed is deleted, not kept).
