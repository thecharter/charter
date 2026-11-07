# 017 — Projections and Target Interoperability

**Status:** draft (2026-11-06; `D28`, `G5.1`–`G5.2`). Implementation: compliant (`src/Charter/Project/{GuardTarget,QuintTarget,PromptTarget}.lean`, `src/Charter/Cli/Generate.lean`).

Every projection reads the elaborated `Core.Spec` (`CIR`) records directly (Law 5) and never re-parses English prose.

**17.1 Command (`charter generate`).** `charter generate --target <solidity|abi|quint|prompt> [--mode lawful|adversarial] [--actor <role>] [--verify-output] [-o <path>] <file.charter>` compiles `<file.charter>` to `CIR`, checks fragment eligibility for the requested target, emits the target artifact, and (under `--verify-output`) validates target syntax, ABI round-trip, and differential trace parity against `Charter.Eval` / `charter-server`.

**17.2 No silent dropping (`CHR035`).** Every construct in the input `Spec` is classified as `supported`, `lowered-with-assumption`, or `rejected`. If a program uses a construct outside the target's supported fragment (such as unbounded `Exists`/`Forall` over infinite `Int`/`String` domains or dynamic `Amend ... Installs` in `--target solidity`), `charter generate` fails with `CHR035` naming the rule and construct rather than omitting it.

**17.3 Solidity & JSON ABI guards (`T33`).** `--target solidity` and `--target abi` lower finite/scalar `CIR` specifications to `GuardIR` (`Charter.Project.cir_guard_step_correspondence`), emitting a deterministic Solidity `^0.8.24` state-transition guard contract pinning `LAW_SHA256` and an Ethereum JSON ABI. `--verify-output` checks ABI/contract structural validity, runs differential compliant and adversarial traces against `charter-server`, and invokes `solc` when present on `PATH`.

**17.4 Quint protocol target and trace replay (`T32`).** `--target quint` emits a typed `.qnt` module (`--mode lawful` or `--mode adversarial` including `ObserveExternal` / clock transitions), safety `val` invariants, and temporal properties. Counterexample traces (`importQuintTrace`) replay directly through `Charter.Eval` (`T26`, `T27`, `T32`).

**17.5 Advisory AI briefings (`--target prompt`).** `--target prompt [--actor <role>]` emits role-scoped `AlignmentCard` briefings and JSON tool schemas citing verbatim `From` English spans, explicitly stamped `advisoryOnly: true` (`docs/rfc.md` §9.7: prompts inform proposals and never replace `charter-server` enforcement).
