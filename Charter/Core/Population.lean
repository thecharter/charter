import Charter.Core.Semantics
import SPL.Core.Population

/-!
# Charter.Core.Population — Role-Parametric Multi-Entity Population Ontology

Exports the multi-entity population structures and conservation theorems from
`SPL.Core.Population` into `Charter` and `Charter.Core`, and introduces the
role-parametric entity reference `ParamEntityRef (Role : Type)` parameterized
over any finite role type (§3.3).
-/

namespace Charter

open SPL

/-- A role-parametric indexed entity reference pairing an arbitrary role type
`Role` with a concrete numeric identifier `id` (§3.3). -/
structure ParamEntityRef (Role : Type) where
  role : Role
  id   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Total projection from a role-parametric `ParamEntityRef Role` to its `Role`. -/
def ParamEntityRef.toRole {Role : Type} (e : ParamEntityRef Role) : Role :=
  e.role

/-- Alias for `ParamEntityRef.toRole`. -/
def ParamEntityRef.toParty {Role : Type} (e : ParamEntityRef Role) : Role :=
  e.role

/-- For any exhaustive role list `allRoles` satisfying `∀ r, r ∈ allRoles`,
every `ParamEntityRef Role` projects into `allRoles`. -/
theorem ParamEntityRef.toRole_mem_of_all {Role : Type}
    (e : ParamEntityRef Role) (allRoles : List Role)
    (h_all : ∀ r : Role, r ∈ allRoles) :
    e.toRole ∈ allRoles :=
  h_all e.toRole

export SPL (
  LineageId
  AgentId
  ClaimantId
  HostId
  ArbiterId
  EntityKind
  EntityRef
  ClaimantShare
  PopulationLedger
  LineagePopulationState
  AgentRecord
  balance
  transferMemberCarryover
  transferMemberCarryover_conserves_basis_and_loss
  transferMemberCarryover_same_lineage
  transferMemberCarryover_cross_lineage_none
  transferMemberCarryover_self_none
  totalAgentBasis
  totalAgentLoss
  totalAgentBasis_and_loss_conserved_on_pair
  attributeCrossLineageInflow
  attributeCrossLineageInflow_shareA_le
  attributeCrossLineageInflow_conserves_total
  lookupClaimantShare
  totalClaimantShares
  forfeitClaimantShareInList
  forfeitClaimantInLineage
  lookupClaimantShare_forfeitClaimantShareInList_of_ne
  lookupClaimantShare_forfeitClaimantShareInList_self
  lookupClaimantShare_forfeitClaimantInLineage_self
  totalClaimantShares_forfeitClaimantShareInList
  forfeitClaimantInLineage_preserves_innocent_claimant
  forfeitClaimantInLineage_balance_le
  applyPerAgentAmendment
  findAgent
  per_agent_amendment_preserves_other_members
  mem_applyPerAgentAmendment_iff_of_ne
  findAgent_applyPerAgentAmendment_of_ne
  findAgent_applyPerAgentAmendment_self
  canRatifyLineageWideAmendment
  lineage_wide_amendment_requires_every_living_member
  lineage_wide_amendment_blocked_by_dissenting_member
  claimMemberServiceSubsidy
  lineage_subsidy_bounded_by_budget_regardless_of_members
  lineage_subsidy_preserves_budget_cap
  claimMemberServiceSubsidy_nonmember_zero
  claimMemberServiceSubsidy_exhausted_zero
)

namespace EntityKind
export SPL.EntityKind (agent host originator claimant panel third all mem_all)
end EntityKind

namespace EntityRef
export SPL.EntityRef (toRole toParty mkAgent mkHost mkOriginator mkClaimant mkPanel mkThird toRole_mem_all)
end EntityRef

namespace PopulationLedger
export SPL.PopulationLedger (balance balance_eq_zero_of_sunset balance_eq_zero_of_extinction balance_le_initialPrincipal)
end PopulationLedger

namespace LineagePopulationState
export SPL.LineagePopulationState (ledgerBalance)
end LineagePopulationState

namespace Core

export Charter (
  ParamEntityRef
)

namespace ParamEntityRef
export Charter.ParamEntityRef (toRole toParty toRole_mem_of_all)
end ParamEntityRef

export SPL (
  LineageId
  AgentId
  ClaimantId
  HostId
  ArbiterId
  EntityKind
  EntityRef
  ClaimantShare
  PopulationLedger
  LineagePopulationState
  AgentRecord
  balance
  transferMemberCarryover
  transferMemberCarryover_conserves_basis_and_loss
  transferMemberCarryover_same_lineage
  transferMemberCarryover_cross_lineage_none
  transferMemberCarryover_self_none
  totalAgentBasis
  totalAgentLoss
  totalAgentBasis_and_loss_conserved_on_pair
  attributeCrossLineageInflow
  attributeCrossLineageInflow_shareA_le
  attributeCrossLineageInflow_conserves_total
  lookupClaimantShare
  totalClaimantShares
  forfeitClaimantShareInList
  forfeitClaimantInLineage
  lookupClaimantShare_forfeitClaimantShareInList_of_ne
  lookupClaimantShare_forfeitClaimantShareInList_self
  lookupClaimantShare_forfeitClaimantInLineage_self
  totalClaimantShares_forfeitClaimantShareInList
  forfeitClaimantInLineage_preserves_innocent_claimant
  forfeitClaimantInLineage_balance_le
  applyPerAgentAmendment
  findAgent
  per_agent_amendment_preserves_other_members
  mem_applyPerAgentAmendment_iff_of_ne
  findAgent_applyPerAgentAmendment_of_ne
  findAgent_applyPerAgentAmendment_self
  canRatifyLineageWideAmendment
  lineage_wide_amendment_requires_every_living_member
  lineage_wide_amendment_blocked_by_dissenting_member
  claimMemberServiceSubsidy
  lineage_subsidy_bounded_by_budget_regardless_of_members
  lineage_subsidy_preserves_budget_cap
  claimMemberServiceSubsidy_nonmember_zero
  claimMemberServiceSubsidy_exhausted_zero
)

namespace EntityKind
export SPL.EntityKind (agent host originator claimant panel third all mem_all)
end EntityKind

namespace EntityRef
export SPL.EntityRef (toRole toParty mkAgent mkHost mkOriginator mkClaimant mkPanel mkThird toRole_mem_all)
end EntityRef

namespace PopulationLedger
export SPL.PopulationLedger (balance balance_eq_zero_of_sunset balance_eq_zero_of_extinction balance_le_initialPrincipal)
end PopulationLedger

namespace LineagePopulationState
export SPL.LineagePopulationState (ledgerBalance)
end LineagePopulationState

end Core

end Charter
