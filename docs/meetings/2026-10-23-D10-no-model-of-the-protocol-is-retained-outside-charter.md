# D10 — No model of the protocol is retained outside Charter: `ProtocolWorldState` and the 16 Lean simulations are deleted when their Charter replacements pass

**Laws:** goal 1; 6, 8, 9, 10, 13, 14 (docs/mission.md). Brief: B7. **Sharpens:** D3.
**Date:** 2026-10-23
**Status:** ruled (Eric), differs from the prediction (which was a scope commitment at 60%); Eric's words below are the ruling

## Ruling (Eric, verbatim)
No model of the protocol is retained outside Charter. `ProtocolWorldState` and the 16 Lean simulations are deleted when their Charter replacements pass, not deprecated. Decided now; only the residue triage waits for the end of Phase 3.

1. **Simulations are protocol text.** Each of the 16 is a clause of the protocol's Adversarial Tests section. Each becomes a Charter scenario that names its span (Law 8). Tag: *decided* where the inputs are concrete, *proved* where the test quantifies over strategies or parameters (Law 10).
2. **Lean may prove, not hold.** Lean code may state and prove properties *of a Charter program* against the semantics. It may not define a protocol state, quantity, party, or rule (Laws 9, 13).
3. **Substrate inputs are facts; substrate properties are assumptions.** Affiliation, beneficial control, sortition outcomes, and valuations are supplied as environment facts (Law 6). Properties such as unbiased draws or attested erasure are named assumptions (`SUB.*`, tag *assumed*). Neither is a reason to keep a Lean model.
4. **Residue procedure.** A simulation the evaluator cannot run is filed as a language feature request before the end of Phase 3. v1.0 does not ship until each request is either implemented (and then generalized, per goal 1) or the protocol is amended to drop or restate the test. Amendment changes the English first (Law 8); it is never met by keeping a Lean model.
5. **Arithmetic is stated, not inherited.** The 13 quantities become `Int` facts with aggregates. Every division states its rounding as the protocol states it (floor, in the agent's favour), so the Charter scenario and the protocol cannot disagree by one unit.

## Gates (Law 14)
- `test/gates/goal1-no-shadow-model`: fails if any Lean module outside the semantics, evaluator, and projection proofs declares a structure, inductive, or definition named for, or spanned to, a protocol clause.
- `test/gates/psa-adversarial-tests`: one scenario per test in the protocol's Adversarial Tests section; fails if the section and the scenarios differ in count, or if any scenario's span text has drifted.

## Consequences for the plan
`Charter/Substrate/*` (attestation, sortition, settlement) is substrate: its inputs become environment facts and its theorems become named `SUB.*` assumptions cited by programs, not models the evaluator runs. Phase 3's exit is "all 16 adversarial tests run as Charter scenarios", not "or listed as Lean-only".

## Reopens if
Never on the retention question. The residue procedure in clause 4 is the only path.
