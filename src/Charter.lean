import Charter.Core.Provenance
import Charter.Core.Syntax
import Charter.Core.Semantics
import Charter.Core.Views
import Charter.Core.Explain
import Charter.Core.Graph
import Charter.Core.Population
import Charter.Core.Refinement
import Charter.Core.Composition
import Charter.Core.Ratchet
import Charter.Substrate.Attestation
import Charter.Substrate.Sortition
import Charter.Substrate.Settlement
import Charter.Modules.ResidualLedger
import Charter.Modules.CollateralPool
import Charter.Modules.CircuitBreaker
import Charter.Modules.EntityGroup
import Charter.Modules.ExitAndVoice
import Charter.Modules.SortitionCourt
import Charter.Modules.AttestedLease
import Charter.Modules.OracleFeed
import Charter.Projection.Veil
import Charter.Projection.Prompt
import Charter.Projection.ContractABI
import Charter.Projection.Visualization
import Charter.Surface.Syntax
import Charter.Surface.Dsl
import Charter.Surface.Lower
import Charter.Surface.Unlower
import Charter.Surface.Program
import Charter.Surface.DslSample
import Charter.Tooling.Cli
-- The eFLINT-core pipeline (Phase 1, plan §3)
import Charter.Surface.Diagnostics
import Charter.Surface.Lexer
import Charter.Surface.Ast
import Charter.Surface.Parser
import Charter.Core.Term
import Charter.Core.Spec
import Charter.Core.State
import Charter.Resolve.Static
import Charter.Eval.Eval
import Charter.Eval.Interpreter
import Charter.Eval.Properties
import Charter.Prove.Run
import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Cli.Test
import Charter.Cli.Repl

/-!
# `Charter` — Universal Institutional Specification Language & Standard Library

Top-level umbrella module for the **Charter** language and standard library:
1. **`Charter.Core`**: Law-agnostic Hohfeldian syntax, semantics, provenance, views,
   explanation engine, affiliation graphs (`AffiliationGraph`), role-parametric
   population ontology (`ParamEntityRef`), polymorphic quantitative-to-normative
   refinement (`WorldSpec`), vertical and horizontal law composition
   (`composeVertical`, `composeHorizontal`, `SigEmbedding`), and bilateral
   parameter ratchets (`RatchetSpec`).
2. **`Charter.Substrate`**: Generic cryptographic attestation & lease fencing
   (`Attestation`), Sybil-resistant bonded sortition (`Sortition`), and
   contestable valuation feeds & atomic settlement waterfalls (`Settlement`).
3. **`Charter.Modules`**: 8 reusable, pre-proved institutional standard-library modules
   (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`,
   `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`).
4. **`Charter.Projection`**: Verified state-machine lowering (`Veil`), AI
   constitutional system prompts & synthetic training rows (`Prompt`),
   smart-contract state-transition guards & JSON ABI (`ContractABI`), and
   step-by-step trace visualization & amendment diffs (`Visualization`).
5. **`Charter.Surface`**: The `.charter` language itself — AST, parser, validator,
   and printer (`Dsl`), its meaning as a `Law` over the dynamic signature
   (`Lower`), the reverse direction for exporting Lean laws (`Unlower`), the
   `charter_program "file.charter"` elaborator that embeds a program as a Lean term
   (`Program`), a kernel-decided toy program (`DslSample`), and the kernel-checked
   `charter_*` Lean macros (`Syntax`).
6. **`Charter.Tooling`**: The program-agnostic `charter` command-line harness
   (`Charter.Cli.Program`, `Charter.Cli.run`) that any program registers with.

Nothing in this library refers to any particular institution. A Charter program is a
`.charter` file; the `charter` executable runs every subcommand on it directly, and a
Lean module may embed it with `charter_program` to prove things about it. The example
programs under `Examples/` are such files, each with an optional Lean companion that
`import Charter`; the dependency never runs the other way.
-/

namespace Charter

open Charter.Modules

/-- Combined self-test across all 8 reusable institutional modules in `Charter.Modules.*`. -/
def allCharterModuleSelfTests : Bool :=
  residualLedgerSelfTest &&
  collateralPoolSelfTest &&
  circuitBreakerSelfTest &&
  entityGroupSelfTest &&
  exitAndVoiceSelfTest &&
  sortitionCourtSelfTest &&
  attestedLeaseSelfTest &&
  oracleFeedSelfTest

theorem all_8_charter_modules_self_test_pass :
    allCharterModuleSelfTests = true := by decide

end Charter
