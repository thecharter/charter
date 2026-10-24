# 018 — Toolchain and CLI

**Status:** draft (2026-10-23). Fixed by D1 and D9; wording awaits Eric. Implementation: the commands marked *today* exist for `.eflint` programs; the rest are the plan's (§6) and pending. The `.charter` extension still runs the v0.3 harness until the grammar moves (README).

**18.1 One binary (D1).** `charter` is one native executable that parses, checks, runs, tests, and projects programs itself. No diagnostic, path, flag, or help text names the engine (Law 11; the gate `test/gates/law11-no-engine-in-output.sh`).

**18.2 Commands, today.**

| Command | Does |
|---|---|
| `charter check <file.eflint> …` | resolve every phrase in order without evaluating; report diagnostics and, for a program with `Document`/`Clause`s, the Law 8 provenance checks (012) |
| `charter run <file.eflint>` | run the top-level phrases: each transition with its three answers (*occurred*, *lawful*, *valid*), violations, claims, fact changes, the clock; scenarios are noted, not run |
| `charter test <files or directories> …` | eFLINT's test-mode criterion per file (011.10): no error and every claim holds; runs `Scenario` blocks (011.11), the provenance checks (012), and `--explore N` (013.2); honours the `//!` directives (`expect-error`, `expect-warning`, `known-issue`, `expect-failed-claims`, `explore`, `explore-domain`) |
| `charter repl [file.eflint]` | load the file, then run phrases typed at `charter> ` (`:display`, `:help`, `:quit`) |
| `charter trace <clause> <file.eflint>` | a clause's span table (012.9) |

Flags shared by `check`, `run`, `test`: `--out json` (one record per line: `diagnostic`, `claim`, `transition`, `violation`, `fact`, `clock`, `why`, `scenario`, `summary`), `--eflint` (eFLINT's keyword set only, 002.9), `--explore N` and `--explore-domain "<type> = values"` (`run`, `test`; 013.2, D15). `test` also takes `--expect <outcomes>` and `--tolerate <tolerances.md>` for the corpus comparison (`test/eflint-corpus/README.md`).

**18.3 Exit status.** `0` when every file passed; `1` when any failed; `2` for a usage error.

**18.4 Diagnostics and claims are data (plan §3).** Every error and warning is a record with a CHR code (016); every claim carries a tag (*checked* today; *decided* and *proved* with `prove`) and the question it answers (*holds*, *lawful*, *valid*, *violated*, *provenance*, *invariants*).

**18.5 Pending (plan §6).** `init`, `fmt`, `lsp`, `doc`; `why <fact>` as a command (the phrase `?why` exists, 004.10); `prove` (13.4, D9: a generator that fetches its own pinned toolchain by digest into `~/.charter/toolchains/<digest>/`, `--offline` refusing rather than searching PATH); the projections `render`, `prompt`, `abi`, `views`, `explain`, `veil`, `diff`, `explore`; `import x.eflint`; `--itf`; and the second binary `charter-server` (plan §3a: `serve`, `replay`, `verify`).
