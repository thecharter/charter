# 018 — Toolchain and CLI

**Status:** draft (2026-10-23; updated 2026-11-06 for standalone `.charter` cutover). Fixed by D1, D9, and D10; wording awaits Eric. Implementation: all commands marked *today* run directly on `.charter` and `.eflint` programs, from inside or outside the Charter repository (`test/spec/spec_018_1_charter_extension.charter`, `test/gates/g0-independence.sh`).

**18.1 One binary (D1).** `charter` is one native executable that parses, checks, runs, tests, and projects programs itself. No diagnostic, path, flag, or help text names the engine (Law 11; the gate `test/gates/law11-no-engine-in-output.sh`).

**18.2 Commands, today.**

| Command | Does |
|---|---|
| `charter init [<dir>]` | scaffold a reproducible Charter project (`agreement.md`, `main.charter`, `charter.toml`, `charter.lock`, `uat/smoke.sh`) (`G5.4`) |
| `charter check <file.charter> …` | resolve every phrase in order without evaluating; report diagnostics and, for a program with `Document`/`Clause`s, the Law 8 provenance checks (012) |
| `charter build <file.charter> [-o <artifact>] [--sign-key <key>]` | elaborate into validated `CIR` epochs and emit a signed SHA-256 content-addressed `Artifact` bundle (`D18`, `D27`) |
| `charter fmt [--check] [--stdout] <file.charter> …` | format files canonically while preserving `//!` directives and verifying round-trip AST equality (`020`, `test/spec/spec_018_4_fmt_roundtrip.charter`) |
| `charter doc <file.charter> [-o <out.md>] [--out json]` | generate a consolidated institutional rulebook with clause tables and `Default`/`Exception` decision tables (`G5.4`) |
| `charter lsp` | run the stdio JSON-RPC Language Server Protocol (`initialize`, live `CHR` diagnostics, `hover`, `definition` to Markdown clauses, `formatting`) (`G5.3`) |
| `charter doctor [--claims <path>] [--fail-on-unbacked] [--lock [<dir>]]` | verify `claims.json` theorem/gate backing, `charter.lock` SHA-256 digests, and optional external solver availability (`G5.4`) |
| `charter explore [flags] <file.charter> …` | explore `lawful`, `adversarial`, or `mixed` state spaces with counterexample minimization and `--regime` overlays (`G2.1`, `G3.5`) |
| `charter verify [flags] <file.charter> …` | verify `Invariant`s and temporal `Property`s via `--backend finite \| smt \| inductive` (`D20`, `G2.3`–`G2.5`) |
| `charter run <file.charter>` | run the top-level phrases: each transition with its three answers (*occurred*, *lawful*, *valid*), violations, claims, fact changes, the clock; scenarios are noted, not run |
| `charter test <files or directories> …` | eFLINT's test-mode criterion per file (011.10): no error and every claim holds; runs `Scenario` blocks (011.11), the provenance checks (012), and `--explore N` (013.2); honours the `//!` directives (`expect-error`, `expect-warning`, `known-issue`, `expect-failed-claims`, `explore`, `explore-domain`) |
| `charter repl [file.eflint]` | load the file, then run phrases typed at `charter> ` (`:display`, `:help`, `:quit`) |
| `charter explain <expr> <file.charter> [--scenario <name>] [--audience <role>] [--out json]` | build the structured `ReasonGraph` for `<expr>` (rule ID, `From` span, premise/evidence statuses, defeated exceptions, single-condition counterfactuals) under audience-scoped redaction (`004.11`, `D22`, `T43`) |
| `charter diff <old.charter> <new.charter> [--out json]` | three-view semantic diff: (1) English `Document`/`Clause` changes, (2) `CIR` rule/priority changes (flagging `REVIEW-REQUIRED` when formal rules change under unchanged English, `T38`), and (3) differential scenario verdicts & entrenchment checks (`D25`, `G3.5`) |
| `charter generate --target <solidity\|abi\|quint\|prompt> [--verify-output] [-o <path>] <file.charter>` | emit and validate live `CIR` projections with `CHR035` unsupported-fragment rejection (`017`, `D28`, `T32`, `T33`) |
| `charter trace <clause> <file.eflint>` | a clause's span table (012.9) |
| `charter prove <file.eflint> …` | decide every claim and invariant of the program in the kernel (013.4): a checkpointed chain, one kernel theorem per phrase in modules of `--chunk` phrases (default 5) run as separate processes, so memory is bounded by a module and not by the program; one *decided* claim per theorem; `--memory MB` (each process) and `--time S` (the run) caps (defaults 6144, 300), `--dir` for the project, `--show-checker` to see the checker's output, `--emit-only` to write the project and stop; a maintainer tool run inside the repository until Phase 4 |

Flags shared by `check`, `run`, `test`: `--out json` (one record per line: `diagnostic`, `claim`, `transition`, `violation`, `fact`, `clock`, `why`, `scenario`, `summary`), `--eflint` (accepted as a no-op alias under the unified contextual grammar, 002.9, D17), `--scenario <name>` (repeatable on `run` and `test`: execute only the named `Scenario` block(s) after top-level setup, failing with CHR003 if any named scenario is undeclared), `--explore N` and `--explore-domain "<type> = values"` (`run`, `test`; 013.2, D15), and the opt-in static assurance gates `--require-provenance` (`CHR029`, 012.10), `--forbid-midstream-decls` (`CHR030`), `--require-complete-explore` (`CHR031`), and `--deny-warnings` (`test/spec/spec_018_3_assurance_gates.charter`). `test` also takes `--metamorphic` (or `//! metamorphic`: re-run after stripping advisory metadata and permuting non-salient actor atoms, `T04`–`T05`) and `--expect <outcomes>` / `--tolerate <tolerances.json|tolerances.md>` for the corpus comparison (`test/eflint-corpus/README.md`).

**18.3 Exit status.** `0` when every file passed; `1` when any failed; `2` for a usage error.

**18.4 Diagnostics and claims are data (plan §3).** Every error and warning is a record with a CHR code (016); every claim carries a tag (*checked* today; *decided* and *proved* with `prove`) and the question it answers (*holds*, *lawful*, *valid*, *violated*, *provenance*, *invariants*).

**18.5 Second executable: `charter-server` (`D27`, `G4`).** `charter-server` (`verify`, `replay`, `serve`) loads signed `.artifact` bundles with zero `Surface/`, `Resolve/`, or `Prove/` dependencies (`test/gates/operator-blind.sh`), enforces `Reserve` → `Authorize` → `ConfirmExecution` / `ExecutedUnknown` capability sagas over a hash-chained durable log, and verifies offline state-root determinism (`test/gates/replay.sh`, `test/gates/certificate-at-office.sh`).
