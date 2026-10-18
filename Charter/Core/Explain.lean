import Charter.Core.Views
import SPL.Core.Explain

/-!
# Charter.Core.Explain — Structured Compliance and Validity Explanations

Exports `BreachExplanation`, `Explanation`, `explain`, `Explanation.render`, and
`evalTrace` into `Charter` and `Charter.Core`.
-/

namespace Charter

open SPL

export SPL (
  BreachExplanation
  Explanation
  explain
  evalTrace
)

namespace Explanation
export SPL.Explanation (render)
end Explanation

namespace Core

export SPL (
  BreachExplanation
  Explanation
  explain
  evalTrace
)

namespace Explanation
export SPL.Explanation (render)
end Explanation

end Core

end Charter
