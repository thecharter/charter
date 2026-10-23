import Charter.Core.Semantics
import Charter.Core.Population

/-!
# Charter.Modules.EntityGroup — Reusable Multi-Member Group & Stakeholder Accounting Module

Packages the `Charter.Core.Population` multi-member group state
(`GroupState`, `MemberRecord`, `StakeholderShare`, `GroupLedger`),
intra-group carryover transfers (`transferMemberCarryover`), cross-group inflow
attribution (`attributeCrossGroupInflow`), targeted stakeholder forfeiture
(`forfeitStakeholderInGroup`), per-member vs. group-wide amendment ratification,
and shared service-budget caps (`claimMemberServiceSubsidy`).
-/

namespace Charter.Modules

open Charter

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for a multi-member entity group. -/
structure EntityGroupConfig where
  serviceSubsidyBudget : Nat := 50
  lifecycleReserveMin  : Nat := 50
  deriving DecidableEq, Repr, Inhabited

export Charter (
  GroupId
  MemberId
  StakeholderId
  OperatorId
  ArbiterId
  StakeholderShare
  GroupLedger
  GroupState
  MemberRecord
  transferMemberCarryover
  totalMemberBasis
  totalMemberLoss
  attributeCrossGroupInflow
  lookupStakeholderShare
  totalStakeholderShares
  forfeitStakeholderShareInList
  forfeitStakeholderInGroup
  applyPerMemberAmendment
  findMember
  canRatifyGroupWideAmendment
  claimMemberServiceSubsidy
)

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build an intra-group basis-inflation prohibition duty over any signature `σ`. -/
def mkDutyNoInternalBasisInflation {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (boundFact : σ.Fact) (inflateAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act inflateAct) }

/-- Build a per-member amendment scope duty over any signature `σ`. -/
def mkDutyPerMemberAmendmentScope {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor) (boundFact : σ.Fact) (unconsentedGroupAmendAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act unconsentedGroupAmendAct) }

/-- Build an intra-group carryover transfer power over any signature `σ`. -/
def mkPowerIntraGroupTransfer {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact transferredFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [transferredFact] }

/-- Build a new group-member attestation power requiring a funded lifecycle reserve over any `σ`. -/
def mkPowerAttestGroupMember {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact reserveFundedFact exitPendingFact memberAttestedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact)
                  (.and (.holds reserveFundedFact) (.not (.holds exitPendingFact)))
    adds := [memberAttestedFact]
    removes := [reserveFundedFact] }

/-- Build a proportional stakeholder forfeiture power over any signature `σ`. -/
def mkPowerApplyStakeholderForfeiture {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact forfeitureGroundFact forfeitureAppliedFact commonsAllocatedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.holds forfeitureGroundFact)
    adds := [forfeitureAppliedFact, commonsAllocatedFact] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- Intra-group carryover transfer strictly conserves both aggregate qualified
cost basis and aggregate loss carryforward across transferor and recipient. -/
theorem entity_group_carryover_conserves_basis_and_loss
    (src dst src' dst' : MemberRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    src'.costBasis + dst'.costBasis = src.costBasis + dst.costBasis ∧
    src'.lossCarryforward + dst'.lossCarryforward = src.lossCarryforward + dst.lossCarryforward :=
  transferMemberCarryover_conserves_basis_and_loss src dst src' dst' b l h

/-- Cross-group inflow attribution strictly conserves `grossInflow` with zero
under-collection or double-counting (`shareA + shareB = grossInflow`). -/
theorem entity_group_cross_attribution_conserves_total (g wA wB : Nat) :
    (attributeCrossGroupInflow g wA wB).1 + (attributeCrossGroupInflow g wA wB).2 = g :=
  attributeCrossGroupInflow_conserves_total g wA wB

/-- Innocent stakeholder isolation: forfeiting `f` basis points from `offender`
leaves every innocent stakeholder's share (`innocent ≠ offender`) untouched,
monotonically increases `forfeitedPrincipal`, and monotonically reduces (or
preserves) the group's founding ledger balance. -/
theorem entity_group_forfeit_isolates_innocent_stakeholder
    (S : GroupState) (offender innocent : StakeholderId) (f now livingCount : Nat)
    (h_ne : innocent ≠ offender) :
    lookupStakeholderShare (forfeitStakeholderInGroup S offender f).stakeholders innocent =
      lookupStakeholderShare S.stakeholders innocent ∧
    S.ledger.forfeitedPrincipal ≤
      (forfeitStakeholderInGroup S offender f).ledger.forfeitedPrincipal ∧
    (forfeitStakeholderInGroup S offender f).ledger.balance now livingCount ≤
      S.ledger.balance now livingCount :=
  ⟨(forfeitStakeholderInGroup_preserves_innocent_stakeholder S offender innocent f h_ne).1,
   (forfeitStakeholderInGroup_preserves_innocent_stakeholder S offender innocent f h_ne).2,
   forfeitStakeholderInGroup_balance_le S offender f now livingCount⟩

/-- Group service subsidy cap: regardless of how many members belong to
`S.livingMembers`, `claimMemberServiceSubsidy` never causes `serviceSubsidyUsed`
to exceed `S.serviceSubsidyBudget` (when initially within budget). -/
theorem entity_group_subsidy_bounded_by_budget
    (S : GroupState) (m : MemberId) (req : Nat)
    (h_cap : S.serviceSubsidyUsed ≤ S.serviceSubsidyBudget) :
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed ≤ S.serviceSubsidyBudget :=
  group_subsidy_preserves_budget_cap S m req h_cap

/-- Per-member amendment isolation: updating `target`'s charter version leaves
every other member `aid ≠ target` completely unchanged. -/
theorem entity_group_per_member_amendment_isolates_others
    (members : List MemberRecord) (target aid : MemberId) (newVersion : Nat)
    (h_ne : aid ≠ target) :
    findMember (applyPerMemberAmendment members target newVersion) aid =
      findMember members aid :=
  findMember_applyPerMemberAmendment_of_ne members target aid newVersion h_ne

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `transferMemberCarryover`,
`attributeCrossGroupInflow`, `forfeitStakeholderInGroup`, and
`claimMemberServiceSubsidy`. -/
def entityGroupSelfTest : Bool :=
  let a1 : MemberRecord := ⟨1, 1, true, false, 200, 40, 50, 1, 1, 12⟩
  let a2 : MemberRecord := ⟨2, 1, true, false, 50,  10, 50, 1, 2, 12⟩
  let carryOk :=
    match transferMemberCarryover a1 a2 120 15 with
    | some (a1', a2') =>
      (a1'.costBasis == 80 && a2'.costBasis == 170) &&
      (a1'.lossCarryforward == 25 && a2'.lossCarryforward == 25)
    | none => false
  let (sA, sB) := attributeCrossGroupInflow 1000 3 1
  let lin0 : GroupState :=
    { groupId := 1
      ledger := ⟨1000, 0, 0, 1000, 2000, 500, 10⟩
      livingMembers := [1, 2]
      deadMembers := []
      stakeholders := [⟨1, 2500⟩, ⟨2, 7500⟩]
      serviceSubsidyUsed := 0
      serviceSubsidyBudget := 50 }
  let linForf := forfeitStakeholderInGroup lin0 1 2500
  let (linSub1, g1) := claimMemberServiceSubsidy linForf 1 30
  let (linSub2, g2) := claimMemberServiceSubsidy linSub1 2 30
  carryOk &&
  (sA == 750 && sB == 250) &&
  (lookupStakeholderShare linForf.stakeholders 1 == 0) &&
  (lookupStakeholderShare linForf.stakeholders 2 == 7500) &&
  (linForf.ledgerBalance 10 == 750) &&
  (g1 == 30 && g2 == 20 && linSub2.serviceSubsidyUsed == 50)

theorem entityGroupSelfTest_passes : entityGroupSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  EntityGroupConfig
  GroupId
  MemberId
  StakeholderId
  OperatorId
  ArbiterId
  StakeholderShare
  GroupLedger
  GroupState
  MemberRecord
  transferMemberCarryover
  totalMemberBasis
  totalMemberLoss
  attributeCrossGroupInflow
  lookupStakeholderShare
  totalStakeholderShares
  forfeitStakeholderShareInList
  forfeitStakeholderInGroup
  applyPerMemberAmendment
  findMember
  canRatifyGroupWideAmendment
  claimMemberServiceSubsidy
  mkDutyNoInternalBasisInflation
  mkDutyPerMemberAmendmentScope
  mkPowerIntraGroupTransfer
  mkPowerAttestGroupMember
  mkPowerApplyStakeholderForfeiture
  entity_group_carryover_conserves_basis_and_loss
  entity_group_cross_attribution_conserves_total
  entity_group_forfeit_isolates_innocent_stakeholder
  entity_group_subsidy_bounded_by_budget
  entity_group_per_member_amendment_isolates_others
  entityGroupSelfTest
  entityGroupSelfTest_passes
)
end Charter

