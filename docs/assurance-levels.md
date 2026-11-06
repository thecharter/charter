# Assurance Levels and Scope Taxonomy

Every verification or conformance claim emitted by Charter carries **one of the four `Law 10` assurance tags** paired with explicit **scope** and **completion** descriptors (`docs/mission.md` Law 10; `docs/rfc.md` §7.1, §18.3).

---

## 1. The Four Assurance Tags (`Law 10`)

| Tag       | Meaning                                                                                                  | Verified by                                           |
| --------- | -------------------------------------------------------------------------------------------------------- | ----------------------------------------------------- |
| `proved`  | Universally quantified theorem over all admitted states/traces/parameters under stated hypotheses        | Lean 4 kernel (`lake build`, `law10-trust-grep.sh`)   |
| `decided` | Concrete finite program trace and end-state invariants recomputed and accepted with zero axioms (`{}`)   | Lean 4 kernel (`charter prove`, `kernel_rfl`)         |
| `checked` | Evaluated at runtime by the native `charter` binary on concrete scenarios or a finite exploration domain | Native `Charter.Eval` (`charter check`, `test`, `run`)|
| `assumed` | Explicit environmental, substrate, or external-oracle hypothesis declared by the institution or deployment| Human / deployment audit (`SUB.*`, `Open` inputs)     |

Charter never invents a fifth assurance tag. Bounded model checking (`--explore` or future SMT BMC) is always tagged `checked` with a `bounded-exhaustive` scope — never `proved`.

---

## 2. Orthogonal Scope & Completion Fields

To prevent narrow theorems or truncated searches from being misread as universal end-to-end guarantees, claims are qualified along two orthogonal axes:

### 2.1 `scope`
- `live-evaluator`: Proven or executed directly over `Charter.Core.{Term,Spec,State}` and `Charter.Eval`.
- `idealized-core-model`: Proven over the Phase-0 typed `Charter.Core.Semantics` (`Law σ`) representation (scheduled to bridge/retarget to `Core.Spec` in Gate G1/G5).
- `concrete-trace`: Holds for the specific phrase sequence and `Scenario` blocks in a file.
- `bounded-exhaustive`: Holds across all transitions up to depth `N` over finite domains and declared `explore-domain` menus.

### 2.2 `completion`
- `complete`: Full domain/proof obligation discharged without truncation.
- `inconclusive`: Search or decision stopped due to missing `explore-domain` menu (`D15`), depth bound, or unsupported construct — reported as a non-pass, never silent success.
- `timeout` / `oom`: Stopped by `tools/kernel-probe` or `charter prove` wall-clock (`--time`) or resident-memory (`--memory`) caps.
