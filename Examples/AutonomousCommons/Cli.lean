import Charter.Tooling.Cli
import Examples.AutonomousCommons
import Examples.AutonomousCommons.Export

/-!
# Examples.AutonomousCommons.Cli — `commons` registration with the `charter` front end

Wires the Autonomous Compute & Treasury Commons into the program-agnostic CLI
harness (`Charter.Cli.Program`), supplying its coupled `CommonsWorldState`
simulator as the `sim` subcommand, its standalone `.charter` file for `dsl`, and
its own verification ledger.
-/

namespace AutonomousCommons

open Charter Charter.Cli

/-- Standalone `.charter` DSL specification of the commons (`charter dsl --law commons`). -/
def commonsDslPath : String := "Examples/AutonomousCommons/autonomous-commons.charter"

/-- `charter sim --law commons [scenario.json]`: without a scenario, runs the 8 module
world simulations; with one, executes it on the coupled `CommonsWorldState`. -/
def commonsSim (path? : Option System.FilePath) : IO Unit := do
  match path? with
  | none =>
    IO.println "== Autonomous Compute & Treasury Commons: 8 Module World Simulations =="
    for (name, (ok, summary)) in commonsSimulations do
      IO.println s!"{status ok} {name}"
      IO.println s!"     {summary}"
    let allOk := commonsSimulations.all (fun x => x.2.1)
    IO.println s!"\nOverall world-simulation status: {status allOk} ({commonsSimulations.length}/8 scenarios passed)"
  | some p =>
    let (L, tr) ← parseScenarioWith commonsOntologyTables commonsL0 p
    let W0 : CommonsWorldState := { initCommonsWorld commonsDefaultParams with legal := L.init }
    let WF := commonsWorldTrace commonsDefaultParams W0 tr
    let auth := (List.range tr.length).all fun i =>
      match tr[i]? with
      | none => true
      | some e => commonsWorldStepComplies commonsDefaultParams (commonsWorldTrace commonsDefaultParams W0 (tr.take i)) e
    IO.println "== Commons World Simulation Trace =="
    IO.println s!"now={WF.now}, treasuryBal={WF.treasuryBal}, boughtOut={WF.boughtOut}, stewards={WF.stewards.length}"
    IO.println s!"CommonsWorldAuthorized: {auth}"
    IO.println "\n== Normative Evaluation =="
    IO.println (evalTrace L tr)

/-- Verification ledger of the Autonomous Commons (`charter verify --law commons`). -/
def commonsLedger : List LedgerEntry := [
  ("commons_program_is_lean_law / commons_program_clauses (Examples.AutonomousCommons.Program)", "decided", "lowering autonomous-commons.charter yields exactly the Lean law commonsL0 and its 8 clauses, so every theorem below is a theorem about the .charter file"),

  ("commons_wellFormed / commons_english_covered / commons_norms_interpreted / commons_reverse_provenance", "decided", "lexical, normative, and reverse provenance coverage of all 8 clauses of the Autonomous Compute & Treasury Commons (13 duties, 20 powers, 1 immunity)"),
  ("commons_rules_built_from_modules", "proved", "every duty, power, and immunity of commonsLaw is definitionally an instantiation of a Charter.Modules rule builder over σ_commons"),
  ("commons_outsiders_disabled / commons_exit_always_enabled / commons_dissolve_only_by_power / commons_ragequit_defeats_expulsion / commons_ledger_conserved / commons_court_bounded", "proved", "Hohfeldian outsider disability, unalienable ragequit exit, dissolution closure, ragequit immunity against expulsion, treasury conservation, and bounded sortition court"),
  ("commons_generic_refinement / commons_ratchet_trajectory_safe / commons_sub_charter_respects_floor", "proved", "instantiation of WorldSpec, RatchetSpec, and composeVertical on the commons"),
  ("all_commons_simulations_pass", "decided", "all 8 end-to-end Autonomous Commons module world simulations (simCom1–simCom8) pass") ]

/-- The Autonomous Compute & Treasury Commons as a registered `charter` program. -/
def cli : Charter.Cli.Program where
  id         := commonsId
  title      := commonsTitle
  docPath    := commonsDocPath
  dslPath    := some commonsDslPath
  clauses    := commonsClauses
  actorNames := commonsOntologyTables.actors.names
  check      := checkGeneric commonsL0 commonsClauses commonsDocPath
  views      := viewsGeneric commonsL0 [CommonsRole.steward, .contributor, .auditor, .arbiter, .outsider]
  veil       := veilGeneric commonsL0
  eval       := evalGeneric commonsOntologyTables commonsL0
  sim        := commonsSim
  explain    := explainGeneric commonsOntologyTables commonsL0
  prompt     := promptGeneric commonsTitle commonsOntologyTables commonsL0 .steward commonsSampleTrainingEvents
  abi        := abiGeneric "AutonomousCommonsGuard" commonsL0
  diff       := diffGeneric commonsL0 commonsAmendedLaw commonsClauses commonsAmendedClauses commonsSampleTimelineTrace
  explore    := exploreGeneric commonsTitle commonsRatchetSpec commonsLaw commonsDefaultParams commonsCandidateRegimes
  ledger     := commonsLedger
  exporter   := some (IO.println (Charter.Dsl.render commonsExportDoc))

end AutonomousCommons
