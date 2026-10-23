# Decision Log

Architecture and design decisions and *why*. Newest first. Each entry records the ruling, the laws it instances (`docs/mission.md`), the context, the alternatives weighed, what the reference projects do (`.reference/`), mission fit, the cost accepted, and the condition that would reopen it. A decision that supersedes or sharpens an earlier one says so in both. Delegated decisions (an agent's committed prediction of Eric's ruling, at 75% or better, on a reversible question that is not about semantics or trust) record the full brief; a veto is a revert plus a new entry. Examples, UAT fixtures, and spec wording are never delegated.

Briefs awaiting or supporting rulings: `2026-10-22-briefs-for-ruling.md`.

## Decisions

- [D11 — Rule amendment is an act (`Amend`) whose effects target rule records; ratchets are immunities against `Amend`, reflexively entrenched; `Extend` never changes rules at run time](2026-10-23-D11-rule-amendment-is-an-act-ratchets-are-immunities.md)
- [D10 — No model of the protocol is retained outside Charter: `ProtocolWorldState` and the 16 Lean simulations are deleted when their Charter replacements pass (sharpens D3)](2026-10-23-D10-no-model-of-the-protocol-is-retained-outside-charter.md)
- [D9 — `charter prove` downloads and manages its own pinned toolchain; it never asks the author to install Lean](2026-10-23-D9-prove-manages-its-own-pinned-toolchain.md)
- [D8 — A standard-library module's properties are declared as `Invariant`s in its `.charter` file and proved in `lib/lean/` by name](2026-10-23-D8-module-properties-declared-in-charter-proved-in-lib-lean-by-name.md)
- [D7 — `Time` and `Duration` are distinct types over `Int`; calendars are deferred](2026-10-23-D7-time-and-duration-are-distinct-types-over-int.md)
- [D6 — Derivation is a stratified fixpoint; unstratifiable negation is rejected (first eFLINT tolerance)](2026-10-23-D6-stratified-negation-unstratifiable-programs-are-rejected.md)
- [D5 — `Holds when` is lawful, `Valid when` is effective and defaults to true, so disabled acts keep eFLINT's effects](2026-10-23-D5-valid-when-defaults-to-true-so-disabled-acts-keep-eflint-effects.md)
- [D4 — A `.charter` file is code that quotes its English in `Clause` blocks; a literate `.charter.md` container comes later](2026-10-23-D4-code-first-files-with-clause-blocks.md)
- [D3 — The Protocol of Sovereign Agency is rewritten in Charter; Lean remains only for what the language cannot say (sharpened by D10)](2026-10-22-D3-the-psa-is-rewritten-in-charter.md)
- [D2 — Every eFLINT program is a Charter program: eFLINT's constructs, phrases, and semantics are Charter's core, extended and never revised](2026-10-22-D2-every-eflint-program-is-a-charter-program.md)
- [D1 — The `charter` binary is a Lean-hosted compiler with Lean-free output; per-program kernel proofs are an opt-in `charter prove`](2026-10-22-D1-lean-hosted-compiler-lean-free-output.md)
