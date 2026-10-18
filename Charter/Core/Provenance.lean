import SPL.Core.Provenance

/-!
# Charter.Core.Provenance — Verbatim English Provenance & Authorship Questions

Exports the law-agnostic provenance kernel (`ClauseId`, `Register`, `Span`,
`Clause`, `reverseProvenance`, `reverseProvenanceWith`) into `Charter` and
`Charter.Core`, and introduces `AuthorshipQuestion` so institutions can
explicitly record open interpretive questions alongside their chosen formal
readings (§12 Q4).
-/

namespace Charter

open SPL

export SPL (
  ClauseId
  Register
  Span
  Clause
  reverseProvenance
  reverseProvenanceWith
)

namespace Register
export SPL.Register (
  norm
  invariant
  acceptance
  commentary
  definition
)
end Register

namespace Clause
export SPL.Clause (
  stale
  invalidated
  covered
  normsInterpreted
)
end Clause

/-- An explicit record of an open interpretive question where the English source
admits multiple readings, documenting the question and the chosen formal reading (§12 Q4). -/
structure AuthorshipQuestion where
  id            : String
  clauseId      : String
  question      : String
  chosenReading : String
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Core

export SPL (
  ClauseId
  Register
  Span
  Clause
  reverseProvenance
  reverseProvenanceWith
)

namespace Register
export SPL.Register (
  norm
  invariant
  acceptance
  commentary
  definition
)
end Register

namespace Clause
export SPL.Clause (
  stale
  invalidated
  covered
  normsInterpreted
)
end Clause

export Charter (
  AuthorshipQuestion
)

end Core

end Charter
