# D28 — Live `CIR` projections (`solidity`, `abi`, `quint`, `prompt`), `CHR035` fragment rejection, and truthful target boundaries (`T32`, `T33`)

**Laws:** 5, 9, 10, 11, 13, 14 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §7.6, §9.1–§9.7, §18.3)

## Ruling
1. **`charter generate --target solidity | abi | quint | prompt` operates directly on live `Core.Spec` (`CIR`)**:
   - Replaces disconnected Phase-0 `Law σ` demo projections with live `CIR` projections reading `Spec` records directly (`Mission Law 5`).
   - Unsupported constructs for a target (e.g., non-enumerable unbounded quantifiers or runtime `Installs` rule synthesis in `--target solidity`) fail loudly with **`CHR035`** naming the construct and rule — never silently dropping a rule (`AGENTS.md`).
2. **On-chain / API Guard target (`Project/GuardTarget.lean`, `T33`)**:
   - Lowers finite/scalar `CIR` rules into a typed `GuardIR` state-transition guard, proves `cir_guard_step_correspondence` in Lean (connecting `evalGuardIR` to `Eval`'s `(lawful, valid)` and state transitions), emits Solidity `^0.8.24` + canonical Ethereum JSON ABI, and validates 1-to-1 trace verdict parity against `charter-server` (`--verify-output`, invoking `solc` when installed on `PATH`).
3. **Protocol Verifier target (`Project/QuintTarget.lean`, `T32`)**:
   - Emits typed Quint (`.qnt`) protocol specifications in both `--mode lawful` and `--mode adversarial`, validates emitted syntax and transition structure (invoking `quint` CLI when installed), and provides `importQuintTrace` to replay counterexample traces natively in `Charter.Eval` (`T26`, `T27`, `T32`).
4. **Advisory AI Briefing target (`Project/PromptTarget.lean`, §9.7)**:
   - Emits role-scoped `AlignmentCard` markdown and JSON tool schemas stamped `advisoryOnly: true` (never advertised as an enforcement boundary).

## Context
Implements `WP-7` (`G5.1`–`G5.2`) while enforcing `docs/rfc.md` §1.3 & §9.1's requirement to separate proved internal IR correspondence from checked external target output.

## Mission fit
`Law 5` (projections inspect `Spec` data without re-parsing prose), `Law 9` (every counterexample trace replays in `Charter.Eval`), `Law 10` (certificates distinguish `proved` `GuardIR` correspondence from `checked` external compiler runs), `Law 11` (no engine names in CLI).

## Cost accepted
Infinite-domain existential guards outside Solidity's bounded storage model are rejected with `CHR035` rather than approximated unsafely.

## Reopens if
Pinned Veil 2.0 binary releases stabilize upstream and are added alongside `quint` as a second external protocol target.
