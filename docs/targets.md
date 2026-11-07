# Target Coverage & Projection Assurance Matrix (`G5.1`–`G5.2`, `D28`)

Per `docs/rfc.md` §1.3 and §9.1, Charter separates **proved internal IR correspondence** from **checked external compiler/solver acceptance** and **advisory briefings**:

| Target (`--target`) | Output Format | Supported `CIR` Fragment | Rejected (`CHR035`) | Internal Assurance | External Validation (`--verify-output`) |
|---|---|---|---|---|---|
| `solidity` | Solidity `^0.8.24` guard contract | Boolean/scalar facts, `Param`, `Money`/`Quantity`/`Duration`/`Time`, `Act`/`Power` (`Holds when`, `Valid when`), `Immunity`, `Duty` | Unbounded `Exists`/`Forall`/`Sum` over infinite domains; runtime `Amend ... Installs` | `proved`: `cir_guard_step_correspondence` (`GuardIR` ↔ `Eval` step) | `checked`: ABI round-trip + differential trace parity vs. `charter-server` (+ `solc` compilation when installed) |
| `abi` | Ethereum JSON ABI (`.abi.json`) | Same as `solidity` | Same as `solidity` | `checked` schema correspondence | `checked` JSON ABI schema & selector check |
| `quint` | Quint `.qnt` protocol module | Finite-domain `Fact`, `Act`/`Power`/`Physical`, `Duty`, `Immunity`, `Invariant`, `Property`, `Time` | Unbounded string synthesis | `checked` typed `QuintModule` AST & trace replay | `checked`: `.qnt` structural validator + `importQuintTrace` replay in `Charter.Eval` (+ `quint` CLI when installed) |
| `prompt` | Markdown `AlignmentCard` + JSON tool schema | Full `CIR` (`Clause`, `From`, `Power`, `Duty`, `Immunity`, `Evidenced`) | None | Non-authoritative (`advisoryOnly: true`) | Structural schema check; `charter-server` remains sole enforcement authority |
