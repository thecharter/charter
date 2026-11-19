# D48 — A trace Quint finds is replayed through the evaluator by `charter verify --replay`; the verdicts must agree

**Laws:** 9, 10, 13, 14 (`docs/mission.md`). Brief `B35` (`2026-11-18-briefs-for-ruling.md`). Rewords spec `017.4`; corrects `D28` item 3; closes the reopening condition of `D45`.
**Date:** 2026-11-18
**Status:** ruled (Eric, 2026-11-18): option A, in two moves, with the flag on `verify` rather than `generate`. The words of `017.4` are an agent's draft and await Eric's blessing (below).

## Context

Spec `017.4` and `D28` item 3 said Quint counterexamples "are certified by native replay through `Charter.Eval`" by `importQuintTrace`. No such function existed (`rg importQuintTrace src/` was empty before and after `D45`). After `D45` the model was checked against the evaluator step by step, but that check reads the model the text was printed from and trusts the printer (`Law 9`).

## Ruling

1. **First, the sentence ahead of its code is removed** (`Law 14`). `017.4` and `D28` item 3 say what is checked: the lockstep differential under `--verify-output`, and in CI `quint typecheck` and the simulator's verdict. Landed as its own commit (`31e2794`), independent of item 2.
2. **Then the replay is built**, as `charter verify --replay <trace.itf.json> <file.charter>`. Replay is a verification, not a generation, so it is not under `generate`; the format is detected from the trace (`#meta.format`), so there is one flag for "replay a history" (`Law 13`). Today it reads one format: the Informal Trace Format as written by `quint run --mbt --out-itf`.
3. **What it does** (`src/Charter/Project/QuintReplay.lean`). For each state after the first it reads `mbt::actionTaken` and `mbt::nondetPicks`, maps the action back to the Charter act, event, or clock advance the model's action was generated from, and performs that step through `Charter.Eval`. It fails if the action is not one of the model's, a pick is not one of the model's candidates, the evaluator does not offer the step in the given `--mode`, or the evaluator cannot take it. At the end the verdicts must agree: Quint says `violation` exactly when the evaluator reports an invariant violated.
4. **What it does not do.** It does not compare intermediate states. That would mean reading `held_`/`exp_` back out of the trace, a second statement of the state encoding with no theorem behind it. Verdict agreement first; state agreement when there is a theorem about the encoding.
5. **The tag is `checked`**, scope one concrete trace. The spec says "replayed", not "certified".

## Words (`017.4`), for Eric's blessing

*Blessed with one change (Eric, 2026-11-18; `D50`):* the sentence below stated only the violation direction. The spec now carries Eric's words, which state the agreement both ways, name the `--mode`, and say that intermediate states are not compared. `--replay` is confirmed. Failures are split by kind: a finding exits 1, an input that is not a trace of this program's model exits 2 (`D50`).

> A counterexample trace Quint finds on the emitted text (`quint run --mbt --out-itf`) is replayed by `charter verify --replay <trace.itf.json> <file.charter>`: each recorded action, with the values Quint picked for it, is performed through `Charter.Eval`, and the replay passes only when the evaluator reports an invariant violated at the end, as Quint did (`D48`).

The rest of `017.4` (commit `31e2794`) is also a draft: it restates `D45` and the CI workflow. The flag's spelling, `--replay`, is the ruling's suggestion and was left as Eric's call.

## Evidence

- `tools/differential-targets-check` (CI): for both fixtures on which Charter finds a counterexample (`t26_t27_partition_lease`, `quint_booking_effects` in adversarial mode), Quint's simulator finds one on the emitted text, writes it with `--mbt --out-itf`, and `charter verify --replay` performs it through the evaluator and reports the same violation.
- `tools/verify-check`, with no external tool: Quint's own trace for the partition lease is committed (`test/verify/replay/partition_lease.itf.json`, three steps) and replays; the same trace is refused in `--mode lawful` (the evaluator does not offer the unlawful step), against another program, and when cut to its first state while still claiming a violation.

## Alternatives weighed

- **`charter generate --target quint --replay-trace`** (the brief's spelling). A checking action under the producing command.
- **Compare every state.** Item 4.
- **B, reword only.** Leaves the Quint target's only check trusting its own printer.

## Cost accepted

- A replay that confirms a counterexample exits 0: the claim checked is that the trace replays and the verdicts agree, and the line names the violated invariant. A script that wants the invariant's status reads the line or runs `verify` without `--replay`.
- The replay needs the `--mode` the model was generated in. A lawful-mode trace also replays in adversarial mode; an adversarial trace with an unlawful step fails in lawful mode, with the step named.
- The initial state of the trace is not compared with the program's (item 4).

## Reopens if

A theorem relates the model's state encoding to `Charter.Eval`'s state (then intermediate states are compared), or a second trace format is to be replayed (the server's histories).
