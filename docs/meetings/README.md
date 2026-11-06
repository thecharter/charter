# Decision Log

Architecture and design decisions and *why*. Newest first. Each entry records the ruling, the laws it instances (`docs/mission.md`), the context, the alternatives weighed, what the reference projects do (`.reference/`), mission fit, the cost accepted, and the condition that would reopen it. A decision that supersedes or sharpens an earlier one says so in both. Delegated decisions (an agent's committed prediction of Eric's ruling, at 75% or better, on a reversible question that is not about semantics or trust) record the full brief; a veto is a revert plus a new entry. Examples, UAT fixtures, and spec wording are never delegated.

Briefs awaiting or supporting rulings: `2026-10-22-briefs-for-ruling.md` (B1–B8, ruled as D4–D11), `2026-10-23-briefs-for-ruling.md` (B9, duplicate declarations; B10, the certificate's signer; awaiting ruling), `2026-10-24-briefs-for-ruling.md` (B11, acts that name an amount; B12, `Duration * Int`; ruled as D15–D16).

## Decisions

- [D25 — Rule-level `Amend` acts, reflexive `Immunity` entrenchment, `Regime` overlays, and 3-view `charter diff` (`D11`, `T23`, `T24`, `T38`)](2026-11-06-D25-rule-amendment-reflexive-ratchet-and-semantic-diff.md)
- [D24 — Static dimensional `Money(CUR, SCALE)` and `Quantity(UNIT)` over exact `Int` with `MulDivRound` (`T10`, `T11`)](2026-11-06-D24-dimensional-money-quantity-and-rounding.md)
- [D23 — Stratified `Default` / `Exception` / `Priority` calculus and typed `Conflict` (`T21`, `T22`)](2026-11-06-D23-defeasible-defaults-exceptions-and-conflict.md)
- [D22 — Four-valued epistemic `Evidence`/`Finding`, 3-valued `Eval`, and audience-redacted `ReasonGraph` (`T04`–`T07`, `T43`)](2026-11-06-D22-epistemic-evidence-findings-and-reasongraph.md)
- [D21 — `Power` competence requirement (`CHR032`) and multi-document SHA-256 provenance (`T08`, `T37`, `T39`)](2026-11-06-D21-power-competence-and-multidoc-provenance.md)
- [D20 — Temporal `Property` declarations, fairness-gated liveness (`T31`), and symbolic `TVIR`/SMT (`T30`)](2026-11-06-D20-temporal-properties-and-symbolic-tvir.md)
- [D19 — Structured assurance certificates (`scope` + `completion`) and monotonic symbol interning](2026-11-06-D19-assurance-certificates-and-interning.md)
- [D18 — Canonical `CIR` evolves from `Core.Spec` with `LawVersion` epochs and pure-Lean SHA-256 `Artifact` digests](2026-11-06-D18-canonical-cir-and-artifact-hashing.md)
- [D17 — Charter's single-word additions are contextual keywords; one unified grammar parses all `.charter` and `.eflint` programs](2026-11-06-D17-unified-contextual-eflint-superset.md)
- [D16 — `Duration * Int`, `Int * Duration` and `Duration / Int` are durations; a duration is never multiplied by a duration, an instant is never scaled](2026-10-24-D16-duration-times-int.md)
- [D15 — An act whose domain is not enumerable is judged for the instance asked about: `Holds when` is read with the components bound, never materialised (fifth eFLINT tolerance)](2026-10-24-D15-an-act-that-names-an-amount-is-judged-for-the-instance.md)
- [D14 — In `e When c` the condition extends as far right as it can: `When`/`Where` has the lowest precedence (fourth eFLINT tolerance; delegated)](2026-10-23-D14-when-has-the-lowest-precedence.md)
- [D13 — An instance named through a placeholder is an instance of the aliased type (third eFLINT tolerance; delegated)](2026-10-23-D13-placeholder-instances-belong-to-the-aliased-type.md)
- [D12 — A duty's violation is reported once, when it begins; `Violated()` still answers at any time (second eFLINT tolerance; delegated)](2026-10-23-D12-duty-violations-are-reported-on-transition.md)
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
