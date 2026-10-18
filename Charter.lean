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
5. **`Charter.Surface`**: Kernel-checked `charter_*` macros and standalone
   `.charter` textual DSL parser (`parseCharterText`).

Programs written in Charter (such as **The Protocol of Sovereign Agency** in
`Programs.SovereignAgency` and **The Autonomous Compute & Treasury Commons** in
`Programs.AutonomousCommons`) live in `Programs/` and `import Charter`.
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
