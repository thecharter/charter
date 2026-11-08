# 017 — Projections and Target Interoperability

**Status:** approved (Eric, 2026-11-06; Charter 1.0.0; `D28`, `G5.1`–`G5.2`). Implementation: compliant (`src/Charter/Project/{GuardTarget,QuintTarget,PromptTarget}.lean`, `src/Charter/Cli/Generate.lean`).

Every projection reads the elaborated `Core.Spec` (`CIR`) records directly (Law 5) and never re-parses English prose.

**17.1 Command (`charter generate`).** `charter generate --target <solidity|abi|quint|prompt> [--mode lawful|adversarial] [--actor <role>] [--verify-output] [-o <path>] <file.charter>` compiles `<file.charter>` to `CIR`, checks fragment eligibility for the requested target, emits the target artifact, and (under `--verify-output`) validates target syntax, ABI round-trip, and differential trace parity against `Charter.Eval` / `charter-server`.

**17.2 No silent dropping (`CHR035`).** Every construct in the input `Spec` is classified as `supported`, `lowered-with-assumption`, or `rejected`. If a program uses a construct outside the target's supported fragment (such as unbounded `Exists`/`Forall` over infinite `Int`/`String` domains or dynamic `Amend ... Installs` in `--target solidity`), `charter generate` fails with `CHR035` naming the rule and construct rather than omitting it.

**17.3 Solidity & JSON ABI guards (`T33`, `D42`, `#66`).** `--target solidity` and `--target abi` lower finite/scalar `CIR` specifications through `GuardIR` (`Charter.Project.cir_guard_step_correspondence`) into typed `SolidityIR` (`SolContract`), whose step and scalar expression semantics are proved in Lean (`Charter.Project.execSolStep_sound`, `Charter.Project.compileScalarExpr_sound_for_declEval`, tagged **`proved`**) under explicit EVM word-range, `keccak256` collision-freedom, and monotonic `block.timestamp` hypotheses (tagged **`assumed`**), and emit deterministic Solidity `^0.8.24` source pinning `LAW_SHA256` plus an Ethereum JSON ABI (surface syntax & ABI parity tagged **`checked`**, validated by 3-way stateful differential execution in `--verify-output` and by `solc`/Foundry in `.github/workflows/differential-targets.yml`).

**17.4 Quint protocol target and trace replay (`T32`, `D42`, `#66`).** `--target quint` emits a typed `.qnt` module (`--mode lawful` or `--mode adversarial` including `ObserveExternal` / clock transitions), safety `val` invariants, and temporal properties. Emitted `.qnt` syntax and bounded searches carry Law 10's **`checked`** tag; counterexample traces (`importQuintTrace`) are certified by native replay through `Charter.Eval` (`T26`, `T27`, `T32`).

**17.5 Advisory AI briefings (`--target prompt`, `D42`, `#66`).** `--target prompt [--actor <role>]` emits role-scoped `AlignmentCard` briefings and JSON tool schemas citing verbatim `From` English spans, explicitly stamped `advisoryOnly: true` and `authoritative: false` (`docs/rfc.md` §9.7: prompts inform proposals and never replace `charter-server` enforcement).
