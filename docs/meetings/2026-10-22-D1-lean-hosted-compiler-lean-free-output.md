# D1 — The `charter` binary is a Lean-hosted compiler with Lean-free output; per-program kernel proofs are an opt-in `charter prove`

**Laws:** 9, 10, 11 (docs/mission.md).
**Date:** 2026-10-22
**Status:** ruled (Eric)

## Ruling
The `charter` binary is written in Lean and ships as one native executable that parses, checks, evaluates, simulates, and projects `.charter` programs itself. Lean proofs certify the compiler and semantics once, at Charter's own build. Users install one binary. Lean never appears in a diagnostic. Per-program kernel proofs are an opt-in `charter prove` that drives a Lean toolchain the binary manages (D9).

## Context
"Lean is the engine but developers never see it" could also be met by compiling every program to Lean and checking it with a hidden toolchain by default. That requires a Lean install for every author, seconds-to-minutes per check, and some Lean errors leaking through.

## Alternatives weighed
Compile-every-program-to-Lean (rejected: Law 11 cannot be kept; goal 2's authors would need a proof assistant).

## What the references do
Catala and Quint ship native binaries; their formal artifacts (F* proofs, Apalache) are separate from the user path. With carries its toolchain inside the compiler.

## Mission fit
Law 9: one evaluator, proved, is the thing the binary runs. Law 11: no author-visible Lean. Law 10: `prove` keeps the kernel as the only trusted checker for per-program claims.

## Reopens if
The evaluator's agreement proof with the semantics cannot be completed, in which case per-program kernel checking becomes the default again and Law 11 is met by hiding the toolchain rather than by not needing it.
