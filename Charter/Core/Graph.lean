import Charter.Core.Semantics
import SPL.Core.Definitions

/-!
# Charter.Core.Graph — Generic Affiliation Graphs & Verified Balance Sheets

Exports the law-agnostic affiliation / conflict-of-interest graph (`RelatedPartyEdge`,
`RelatedPartyGraph`, aliased as `AffiliationEdge` and `AffiliationGraph`, along
with `isRelated`, `isRelated_refl`, `isRelated_symm`, `isRelated_ignores_attestation`)
and the balance-sheet valuation primitives (`VerifiedBalanceSheet`,
`netVerifiedResources`, `netVerifiedResources_deducts_all_liabilities`) into
`Charter` and `Charter.Core`, without embedding institution-specific clauses in
the universal core (§3.3).
-/

namespace Charter

open SPL

export SPL (
  RelatedPartyEdge
  RelatedPartyGraph
  isRelated
  isRelated_refl
  connects_symm
  any_connects_symm
  isRelated_symm
  connects_ignores_attestation
  isRelated_ignores_attestation
  VerifiedBalanceSheet
  netVerifiedResources
  netVerifiedResources_deducts_all_liabilities
)

namespace RelatedPartyEdge
export SPL.RelatedPartyEdge (hasRelation connects)
end RelatedPartyEdge

/-- Law-agnostic alias for `RelatedPartyEdge` (§3.3). -/
abbrev AffiliationEdge := RelatedPartyEdge

/-- Law-agnostic alias for `RelatedPartyGraph` (§3.3). -/
abbrev AffiliationGraph := RelatedPartyGraph

namespace Core

export SPL (
  RelatedPartyEdge
  RelatedPartyGraph
  isRelated
  isRelated_refl
  connects_symm
  any_connects_symm
  isRelated_symm
  connects_ignores_attestation
  isRelated_ignores_attestation
  VerifiedBalanceSheet
  netVerifiedResources
  netVerifiedResources_deducts_all_liabilities
)

namespace RelatedPartyEdge
export SPL.RelatedPartyEdge (hasRelation connects)
end RelatedPartyEdge

export Charter (
  AffiliationEdge
  AffiliationGraph
)

end Core

end Charter
