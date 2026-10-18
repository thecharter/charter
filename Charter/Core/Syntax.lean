import Charter.Core.Provenance
import SPL.Core.Syntax

/-!
# Charter.Core.Syntax — Typed Normative AST (Deep Embedding)

Exports the law-agnostic typed normative AST (`Time`, `Sig`, `Event`, `Trace`,
`LegalState`, `Who`, `Cond`, `Conduct`, `Demand`, `Duty`, `Power`, `Immunity`,
`Law`) into `Charter` and `Charter.Core`.
-/

namespace Charter

open SPL

export SPL (
  Time
  Sig
  Event
  Trace
  LegalState
  Who
  Cond
  Conduct
  Demand
  Duty
  Power
  Immunity
  Law
)

namespace Who
export SPL.Who (anyone only except tagged)
end Who

namespace Cond
export SPL.Cond (tt ff holds heldFor countGe countAtLeast not and or)
end Cond

namespace Conduct
export SPL.Conduct (act anyOf exerciseOf not and or)
end Conduct

namespace Demand
export SPL.Demand (forbid require)
end Demand

namespace Core

export SPL (
  Time
  Sig
  Event
  Trace
  LegalState
  Who
  Cond
  Conduct
  Demand
  Duty
  Power
  Immunity
  Law
)

namespace Who
export SPL.Who (anyone only except tagged)
end Who

namespace Cond
export SPL.Cond (tt ff holds heldFor countGe countAtLeast not and or)
end Cond

namespace Conduct
export SPL.Conduct (act anyOf exerciseOf not and or)
end Conduct

namespace Demand
export SPL.Demand (forbid require)
end Demand

end Core

end Charter
