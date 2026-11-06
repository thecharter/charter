# Trusted Computing Base and Environmental Assumptions

This document enumerates what a user or auditor of Charter trusts for each class of claim (`docs/rfc.md` §0.2 Invariant 5, `docs/mission.md` Law 10).

---

## 1. Kernel-Proved Claims (`proved`)

A claim tagged `proved` is a Lean 4 theorem compiled during `lake build`.

- **Trusted**:
  1. The pinned Lean `v4.24.0` typechecker kernel (`lean-toolchain`).
  2. Standard foundational axioms of Lean's logic (`propext`, `Quot.sound`; `Classical.choice` only if explicitly listed by `#print axioms`), verified automatically to contain zero `sorry`, zero `native_decide`, and zero custom `axiom` declarations by `test/gates/law10-trust-grep.sh`.
  3. Accurate statement of the theorem in `src/Charter/` (e.g., today `src/Charter/Eval/Properties.lean` proves local properties of the live evaluator `Charter.Eval`, while `src/Charter/Projection/*` and `src/Charter/Core/{Composition,Ratchet,Refinement}.lean` prove theorems over the idealized `Law σ` model pending Gate G1/G5 retargeting onto `Core.Spec`).
- **Not trusted**: C code generation, I/O libraries, CLI formatting, or finite scenario inputs.

---

## 2. Kernel-Decided Program Claims (`decided`)

A claim tagged `decided` is produced by `charter prove <file.charter>`.

- **Trusted**:
  1. The Lean `v4.24.0` kernel checking each generated `step_k` checkpoint equality via `kernel_rfl` (`Eq.refl` handed directly to the kernel) and verifying `#print axioms` reports `{}` (**zero axioms**, not even `propext`).
  2. The source loader (`Cli/Load.lean`), lexer (`Surface/Lexer.lean`), and parser (`Surface/Parser.lean`) that parsed `<file.charter>` into the embedded `List Item` AST written at the top of the generated proof project.
- **Not trusted**: The compiled native `Charter.Eval` binary's runtime execution — if the compiled evaluator and the kernel's definitional reduction of `stepSummary` ever disagreed on any phrase, `kernel_rfl` rejects that phrase's `step_k` theorem and names the line (`Law 9`).

---

## 3. Runtime-Checked Claims (`checked`)

A claim tagged `checked` is produced by `charter check`, `charter run`, or `charter test` (including `--explore N`).

- **Trusted**:
  1. Everything in §2.2 (loader, lexer, parser), plus `Resolve/Static.lean`, `Eval/{Eval,Interpreter}.lean`, Lean `v4.24.0`'s C compiler/runtime, libc, and host OS execution.
  2. For bounded exploration (`--explore N`): completeness holds **only** over the finite horizon `N`, enabled-act mode (until G2 `--mode adversarial`), and explicit candidate values listed in `//! explore-domain` (`D15`). It never certifies unreachable depths or unlisted infinite `Int`/`String` arguments.
  3. For verbatim provenance (`Law 8`): `charter check` certifies byte-exact substring occurrence in `Document` and FNV-1a approval-hash freshness; **whether the formal rule accurately captures the legal meaning of the English prose is a human review judgment, never a mechanical guarantee**.

---

## 4. Environmental and Deployment Hypotheses (`assumed`)

Charter applies institutional rules to supplied inputs; it has no omniscient access to the physical or economic world (`Law 6`):

1. **External world inputs (`Open` facts)**: Truth values supplied for `Open` types represent external assertions or oracle/custodian reports. Charter tracks their `Origin` (`supplied by the environment at phrase k`) and raises `CHR100` when an unassigned `Open` fact is queried, but cannot independently verify whether an off-ledger physical event occurred unless reported.
2. **Clock inputs (`@ t.`, `tick.`)**: Charter enforces monotonicity (`CHR106`: time never moves backwards), but relies on the host or environment to supply authentic wall-clock or logical timestamps.
3. **External targets (Veil, Solidity/EVM, LLM prompts)**: Until Gate G5 target validators and external compiler round-trips land, internal projection theorems (`Projection/{Veil,ContractABI,Prompt}.lean`) apply to their internal Lean target structures over `Law σ`, not to deployed EVM bytecode or non-deterministic LLM behavior. Prompts are advisory explanations, never enforcement boundaries.
