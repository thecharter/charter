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
import Charter.Modules.LegalOntologies
import Charter.Projection.Veil
import Charter.Projection.Prompt
import Charter.Projection.ContractABI
import Charter.Projection.Visualization
-- Unified eFLINT-superset Charter pipeline
import Charter.Surface.Diagnostics
import Charter.Surface.Lexer
import Charter.Surface.Ast
import Charter.Surface.Parser
import Charter.Surface.Pretty
import Charter.Core.Evidence
import Charter.Core.Scale
import Charter.Core.Term
import Charter.Core.Defeasible
import Charter.Core.Intern
import Charter.Core.Spec
import Charter.Core.Amend
import Charter.Core.State
import Charter.Core.Derivation
import Charter.Artifact.Hash
import Charter.Artifact.Cert
import Charter.Artifact.Runtime
import Charter.Resolve.Static
import Charter.Resolve.ElaborateCIR
import Charter.Resolve.AssuranceGates
import Charter.Artifact.Format
import Charter.Eval.Eval
import Charter.Eval.Step
import Charter.Eval.Interpreter
import Charter.Core.Transition
import Charter.Eval.Properties
import Charter.Verify.Reduction
import Charter.Verify.Explorer
import Charter.Verify.Temporal
import Charter.Verify.TVIR
import Charter.Verify.Smt
import Charter.Prove.Run
import Charter.Prove.LeanGen
import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Cli.Test
import Charter.Cli.Repl
import Charter.Cli.Prove
import Charter.Cli.Fmt
import Charter.Cli.Build
import Charter.Cli.Explore
import Charter.Cli.Verify
import Charter.Cli.Explain
import Charter.Project.Diff
import Charter.Project.GuardTarget
import Charter.Project.QuintTarget
import Charter.Project.PromptTarget
import Charter.Cli.Diff
import Charter.Cli.Generate
import Charter.Cli.Main
import Charter.Server.StateStore
import Charter.Server.Reservations
import Charter.Server.Protocol
import Charter.Server.Api

/-!
# `Charter` — Universal Institutional Specification Language & Compiler

Top-level umbrella module for the **Charter** language, evaluator, proofs, and CLI.
Nothing in this library refers to any particular institution (`Law 13`, `G0-INDEPENDENCE`).
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
