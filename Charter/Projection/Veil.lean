import SPL.Projection.Veil

/-!
# Charter.Projection.Veil — Veil 2.0 State-Machine Projection & Preservation Theorem

Re-exports the Veil 2.0 state-machine projection (`VeilSpec`, `compileToVeil`,
`authorizedMachine`, `adversarialMachine`, `renderVeil`) and the machine-checked
soundness and completeness theorems (`veil_projection_sound_and_complete`,
`authorizedMachine_sound_and_complete`, `adversarialMachine_accepts_all`)
under the `Charter.Projection` and `Charter` namespaces.
-/

namespace Charter.Projection

export SPL (
  VeilTransition
  VeilInvariant
  VeilSpec
  OpMachine
  compileTransition
  compileInvariant
  compileToVeil
  authorizedMachine
  adversarialMachine
  veilStep
  veilTraceState
  veilStateBefore
  veilEvalConduct
  veilActivatedAt
  veilLapsedRequirements
  veilEventComplies
  veilStepComplies
  veilViolations
  veilAcceptsTrace
  veilExercisesTransition_compileToVeil
  veilEvalConduct_compileToVeil
  veilInvariantViolatedBy_compileToVeil
  veilEventComplies_compileToVeil
  veilStep_compileToVeil
  veilTraceState_compileToVeil
  veilStateBefore_compileToVeil
  veilStepComplies_compileToVeil
  veilAcceptsTrace_compileToVeil
  veilViolations_compileToVeil
  veilActivatedAt_compileToVeil
  veilRequirementViolated_compileToVeil
  veilLapsedRequirements_compileToVeil
  veil_projection_sound_and_complete
  veilIdent
  renderVeil
  veilAcceptsTrace_nil
  veilTraceState_nil
  veilViolations_nil
  authorizedMachine_sound_and_complete
  adversarialMachine_accepts_all
  adversarialMachine_step
  adversarialMachine_traceState
  adversarialMachine_violations
)

end Charter.Projection

namespace Charter

export Charter.Projection (
  VeilTransition
  VeilInvariant
  VeilSpec
  OpMachine
  compileTransition
  compileInvariant
  compileToVeil
  authorizedMachine
  adversarialMachine
  veilStep
  veilTraceState
  veilStateBefore
  veilEvalConduct
  veilActivatedAt
  veilLapsedRequirements
  veilEventComplies
  veilStepComplies
  veilViolations
  veilAcceptsTrace
  veilExercisesTransition_compileToVeil
  veilEvalConduct_compileToVeil
  veilInvariantViolatedBy_compileToVeil
  veilEventComplies_compileToVeil
  veilStep_compileToVeil
  veilTraceState_compileToVeil
  veilStateBefore_compileToVeil
  veilStepComplies_compileToVeil
  veilAcceptsTrace_compileToVeil
  veilViolations_compileToVeil
  veilActivatedAt_compileToVeil
  veilRequirementViolated_compileToVeil
  veilLapsedRequirements_compileToVeil
  veil_projection_sound_and_complete
  veilIdent
  renderVeil
  veilAcceptsTrace_nil
  veilTraceState_nil
  veilViolations_nil
  authorizedMachine_sound_and_complete
  adversarialMachine_accepts_all
  adversarialMachine_step
  adversarialMachine_traceState
  adversarialMachine_violations
)

end Charter
