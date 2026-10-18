import Charter.Core.Syntax
import SPL.Core.Semantics

/-!
# Charter.Core.Semantics — Universal Normative Semantics

Exports the law-agnostic normative interpretation functions (`defeatedByImmunity`,
`validExercises`, `isValidExerciseOf`, `remediesOf`, `step`, `stateAfter`,
`stateBefore`, `dutyInForce`, `breaches`, `activatedAt`, `requirementViolated`,
`complies`, `violations`, `lapsedRequirements`, `Authorized`, and derived
Hohfeldian positions `hasPowerToEstablish`, `hasPowerByAct`, `disability`,
`immuneFrom`, `claimRight`, `privilege`) into `Charter` and `Charter.Core`.
-/

namespace Charter

open SPL

export SPL (
  defeatedByImmunity
  validExercises
  isValidExerciseOf
  remediesOf
  step
  stateAfter
  stateBefore
  dutyInForce
  breaches
  activatedAt
  requirementViolated
  complies
  violations
  lapsedRequirements
  Authorized
  hasPowerToEstablish
  hasPowerByAct
  disability
  immuneFrom
  claimRight
  privilege
)

instance {σ : Sig} (L : Law σ) (tr : Trace σ) : Decidable (Authorized L tr) := by
  unfold Authorized
  infer_instance

namespace LegalState
export SPL.LegalState (
  has
  activeAt
  has_of_activeAt
  since
  count
)
end LegalState

namespace Who
export SPL.Who (mem)
end Who

namespace Cond
export SPL.Cond (eval)
end Cond

namespace Conduct
export SPL.Conduct (matchesAct eval)
end Conduct

namespace Law
export SPL.Law (
  powerById
  spans
  immunityIds
  dutyIds
  powerIds
  wellFormed
)
end Law

namespace Core

export SPL (
  defeatedByImmunity
  validExercises
  isValidExerciseOf
  remediesOf
  step
  stateAfter
  stateBefore
  dutyInForce
  breaches
  activatedAt
  requirementViolated
  complies
  violations
  lapsedRequirements
  Authorized
  hasPowerToEstablish
  hasPowerByAct
  disability
  immuneFrom
  claimRight
  privilege
)

namespace LegalState
export SPL.LegalState (
  has
  activeAt
  has_of_activeAt
  since
  count
)
end LegalState

namespace Who
export SPL.Who (mem)
end Who

namespace Cond
export SPL.Cond (eval)
end Cond

namespace Conduct
export SPL.Conduct (matchesAct eval)
end Conduct

namespace Law
export SPL.Law (
  powerById
  spans
  immunityIds
  dutyIds
  powerIds
  wellFormed
)
end Law

end Core

end Charter
