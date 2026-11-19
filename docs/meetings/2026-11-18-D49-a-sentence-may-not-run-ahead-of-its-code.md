# D49 — A sentence may not run ahead of its code: spec flags and identifiers resolve in `src/`, and no CI command ends in an unconditional pass

**Laws:** 14, 10 (`docs/mission.md`). Follows `D45`–`D48`.
**Date:** 2026-11-18
**Status:** ruled (Eric, 2026-11-18)

## Context

`B34`, `B35`, and `B36` were one defect three times: a claim the tool made that nothing behind it earned. `importQuintTrace` in `017.4`; "z3 execution" in `docs/claims.json`; a CI step that ran a fixture that did not exist and could not fail; `ok` over a skipped check. Each was a sentence ahead of its code, and nothing mechanical noticed.

## Ruling

`test/gates/law14-sentences-resolve.sh`, run by `tools/battery`:

1. Every command-line flag written in backticks in `docs/spec/`, `docs/targets.md`, or `docs/claims.json` occurs in `src/`.
2. Every code identifier written in backticks there (camelCase, a theorem name, or a `Charter.`-qualified name) occurs as a whole word in `src/` or `lib/`.
3. No command in `.github/workflows/`, `tools/battery`, `tools/*-check`, or `test/gates/*.sh` ends in an unconditional pass.

The gate first shows it can fail: it runs its three scans on the sentences it exists for (`importQuintTrace`, `--emit-smt`, a command followed by an unconditional pass) and fails itself if any is not caught. A check that cannot fail is not a check (`D47`).

## Evidence

81 flags and 116 identifiers in 23 documents resolve; 25 CI scripts are clean. The one unconditional pass in the tree was this session's own (the `quint run` that is expected to exit non-zero because it finds a violation, `D48`); it now tests the exit status and that the trace was written.

## Limits, stated

- One name is exempt, with its reason in the gate: `sorryAx`, the proof checker's axiom, which `013` names as what the inductive backend refuses. `Cli/Verify.lean` spells it in two halves so that `law10-trust-grep` does not read the refusal as a use.
- "Occurs in `src/`" is a grep. It catches a name that exists nowhere; it does not show that the name does what the sentence says. That is what the conformance tests and `claims-backed` are for.
- `docs/targets.md` is added to the two trees the ruling named, since it makes the same kind of claim.
- Paths are not checked. A scan of backticked paths in `docs/spec/` found five that name nothing in the tree; they are spec sentences and are filed as `B37` rather than edited or exempted here.

## Reopens if

The grep proves too coarse (a name that exists and is unrelated satisfies it), or `B37` is ruled and paths join the gate.
