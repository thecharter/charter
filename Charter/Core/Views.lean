import Charter.Core.Semantics
import SPL.Core.Views

/-!
# Charter.Core.Views — Multi-Audience Projections from the Normative AST

Exports the legal, agent, operational, and provenance trace views (`rs`,
`Duty.legalRow`, `Power.legalRow`, `Immunity.legalRow`, `Law.legalView`,
`Law.agentView`, `Law.operationalView`, `Clause.traceTable`) into `Charter` and
`Charter.Core`.
-/

namespace Charter

open SPL

export SPL (
  rs
)

namespace Who
export SPL.Who (render)
end Who

namespace Cond
export SPL.Cond (render)
end Cond

namespace Conduct
export SPL.Conduct (render)
end Conduct

namespace Demand
export SPL.Demand (render)
end Demand

namespace Duty
export SPL.Duty (legalRow)
end Duty

namespace Power
export SPL.Power (legalRow)
end Power

namespace Immunity
export SPL.Immunity (legalRow)
end Immunity

namespace Law
export SPL.Law (legalView agentView operationalView)
end Law

namespace Clause
export SPL.Clause (traceTable)
end Clause

namespace Core

export SPL (
  rs
)

namespace Who
export SPL.Who (render)
end Who

namespace Cond
export SPL.Cond (render)
end Cond

namespace Conduct
export SPL.Conduct (render)
end Conduct

namespace Demand
export SPL.Demand (render)
end Demand

namespace Duty
export SPL.Duty (legalRow)
end Duty

namespace Power
export SPL.Power (legalRow)
end Power

namespace Immunity
export SPL.Immunity (legalRow)
end Immunity

namespace Law
export SPL.Law (legalView agentView operationalView)
end Law

namespace Clause
export SPL.Clause (traceTable)
end Clause

end Core

end Charter
