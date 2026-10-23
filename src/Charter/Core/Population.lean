import Charter.Core.Semantics

/-!
# Charter.Core.Population — Multi-Entity Indexed Ontology

Indexed multi-entity population model for institutions whose rules speak about
*groups* of *members* (working groups, groups, cohorts, cells, …), the
fractional *stakeholders* holding residual claims on a group ledger, the
*operators* that run a member's execution, and the *arbiters* that adjudicate.
Everything here is signature-agnostic: the only link to a concrete institution is
the role-parametric `ParamEntityRef Role`.

## Key Components
1. **Typed Entity Identifiers**: `GroupId`, `MemberId`, `StakeholderId`,
   `OperatorId`, `ArbiterId`, and the role-parametric `ParamEntityRef Role`.
2. **Per-Group & Per-Member State Structures**:
   `StakeholderShare`, `GroupLedger`, `GroupState`, and `MemberRecord`.
3. **Multi-Entity Operations & Kernel-Checked Theorems**:
   - Intra-group carryover transfer conserving aggregate basis and loss credits.
   - Cross-group inflow attribution conserving gross inflow.
   - Individual stakeholder share forfeiture preserving innocent stakeholders and
     monotonically increasing forfeited principal.
   - Per-member vs. group-wide amendment ratification scope.
   - Per-group shared service subsidy cap independent of member count.
-/

namespace Charter

/-! ## 1. Typed Entity Identifiers -/

abbrev GroupId       := Nat
abbrev MemberId      := Nat
abbrev StakeholderId := Nat
abbrev OperatorId    := Nat
abbrev ArbiterId     := Nat

/-! ## 2. Per-Group & Per-Member State Structures -/

/-- Fractional beneficial share of a residual stakeholder in basis points (`10000` = 100%). -/
structure StakeholderShare where
  stakeholderId : StakeholderId
  shareBps   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Founding ledger parameters and principal accounting for a group. -/
structure GroupLedger where
  initialPrincipal   : Nat
  paidPrincipal      : Nat
  forfeitedPrincipal : Nat
  sunsetTime         : Nat
  retirementBps      : Nat
  royaltyBps         : Nat
  buyoutMultiple     : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Active founding ledger balance at calendar time `now` given `livingCount`
living group members: `0` at or after `sunsetTime` or when `livingCount == 0`,
and `initialPrincipal - (paidPrincipal + forfeitedPrincipal)` otherwise. -/
def GroupLedger.balance (L : GroupLedger) (now : Nat) (livingCount : Nat) : Nat :=
  if decide (now ≥ L.sunsetTime) || livingCount == 0 then 0
  else L.initialPrincipal - (L.paidPrincipal + L.forfeitedPrincipal)

export GroupLedger (balance)

theorem GroupLedger.balance_eq_zero_of_sunset
    (L : GroupLedger) (now livingCount : Nat) (h : now ≥ L.sunsetTime) :
    L.balance now livingCount = 0 := by
  unfold GroupLedger.balance
  have hd : decide (now ≥ L.sunsetTime) = true := decide_eq_true h
  simp [hd]

theorem GroupLedger.balance_eq_zero_of_extinction
    (L : GroupLedger) (now : Nat) :
    L.balance now 0 = 0 := by
  unfold GroupLedger.balance
  simp

theorem GroupLedger.balance_le_initialPrincipal
    (L : GroupLedger) (now livingCount : Nat) :
    L.balance now livingCount ≤ L.initialPrincipal := by
  unfold GroupLedger.balance
  split <;> omega

/-- Multi-entity state of a group, including its founding ledger,
living and dead member rosters, fractional stakeholders, and shared service
subsidy accounting. -/
structure GroupState where
  groupId            : GroupId
  ledger               : GroupLedger
  livingMembers        : List MemberId
  deadMembers          : List MemberId
  stakeholders            : List StakeholderShare
  serviceSubsidyUsed   : Nat
  serviceSubsidyBudget : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Current founding ledger balance of group `S` at calendar time `now`. -/
def GroupState.ledgerBalance (S : GroupState) (now : Nat) : Nat :=
  S.ledger.balance now S.livingMembers.length

/-- Per-member state record in the multi-entity population. -/
structure MemberRecord where
  memberId          : MemberId
  groupId        : GroupId
  bound            : Bool
  royaltyBoughtOut : Bool
  costBasis        : Nat
  lossCarryforward : Nat
  lifecycleReserve : Nat
  charterVersion  : Nat
  activeOperator       : OperatorId
  leaseExpiry      : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 3. Multi-Entity Operations & Kernel-Checked Theorems -/

/-! ### 3.1 Intra-Group Carryover Transfer -/

/-- Transfers `basisTransfer` of qualified cost basis and `lossTransfer` of
loss-credit carryforward between two distinct members `src` and `dst` of the
same group. Succeeds iff `src` and `dst` share `groupId`, have distinct
`memberId`s, and `src` holds sufficient cost basis and loss carryforward. -/
def transferMemberCarryover
    (src dst : MemberRecord) (basisTransfer lossTransfer : Nat) :
    Option (MemberRecord × MemberRecord) :=
  if src.groupId == dst.groupId &&
     src.memberId != dst.memberId &&
     decide (basisTransfer ≤ src.costBasis) &&
     decide (lossTransfer ≤ src.lossCarryforward) then
    some ({ src with costBasis := src.costBasis - basisTransfer
                     lossCarryforward := src.lossCarryforward - lossTransfer },
          { dst with costBasis := dst.costBasis + basisTransfer
                     lossCarryforward := dst.lossCarryforward + lossTransfer })
  else
    none

/-- Intra-group carryover transfer strictly conserves both aggregate qualified
cost basis and aggregate loss carryforward across the transferor and recipient. -/
theorem transferMemberCarryover_conserves_basis_and_loss
    (src dst src' dst' : MemberRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    src'.costBasis + dst'.costBasis = src.costBasis + dst.costBasis ∧
    src'.lossCarryforward + dst'.lossCarryforward = src.lossCarryforward + dst.lossCarryforward := by
  unfold transferMemberCarryover at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨_, _⟩, hb⟩, hl⟩
    injection h with hpair
    injection hpair with hsrc hdst
    subst hsrc hdst
    simp only
    omega
  · contradiction

/-- Intra-group carryover transfer only succeeds between distinct members of
the same group and preserves both members' `groupId` and `memberId`. -/
theorem transferMemberCarryover_same_group
    (src dst src' dst' : MemberRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    src.groupId = dst.groupId ∧
    src.memberId ≠ dst.memberId ∧
    src'.groupId = src.groupId ∧
    dst'.groupId = dst.groupId := by
  unfold transferMemberCarryover at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcond
    rcases hcond with ⟨⟨⟨hlin, hne⟩, _⟩, _⟩
    injection h with hpair
    injection hpair with hsrc hdst
    subst hsrc hdst
    exact ⟨hlin, hne, rfl, rfl⟩
  · contradiction

/-- Carryover transfer between members of different groups is rejected (`none`). -/
theorem transferMemberCarryover_cross_group_none
    (src dst : MemberRecord) (b l : Nat)
    (h_diff : src.groupId ≠ dst.groupId) :
    transferMemberCarryover src dst b l = none := by
  unfold transferMemberCarryover
  have hbeq : (src.groupId == dst.groupId) = false := beq_eq_false_iff_ne.mpr h_diff
  simp [hbeq]

/-- Self-transfer of carryover basis is rejected (`none`). -/
theorem transferMemberCarryover_self_none
    (src dst : MemberRecord) (b l : Nat)
    (h_same : src.memberId = dst.memberId) :
    transferMemberCarryover src dst b l = none := by
  unfold transferMemberCarryover
  have hbne : (src.memberId != dst.memberId) = false := by
    simp [bne, h_same]
  simp [hbne]

/-- Aggregate qualified cost basis across a list of member records. -/
def totalMemberBasis : List MemberRecord → Nat
  | [] => 0
  | a :: rest => a.costBasis + totalMemberBasis rest

/-- Aggregate loss-credit carryforward across a list of member records. -/
def totalMemberLoss : List MemberRecord → Nat
  | [] => 0
  | a :: rest => a.lossCarryforward + totalMemberLoss rest

/-- Aggregate qualified cost basis + loss carryforward across a pair of members
in a population list is strictly conserved when `src` and `dst` are replaced by
`src'` and `dst'` from `transferMemberCarryover`. -/
theorem totalMemberBasis_and_loss_conserved_on_pair
    (src dst src' dst' : MemberRecord) (others : List MemberRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    totalMemberBasis (src' :: dst' :: others) = totalMemberBasis (src :: dst :: others) ∧
    totalMemberLoss (src' :: dst' :: others) = totalMemberLoss (src :: dst :: others) := by
  have ⟨hb, hl⟩ := transferMemberCarryover_conserves_basis_and_loss src dst src' dst' b l h
  simp only [totalMemberBasis, totalMemberLoss]
  omega

/-! ### 3.2 Cross-Group Attribution -/

/-- Splits a gross value-added inflow `grossInflow` across two parent groups
in proportion to capacity weights `weightA` and `weightB` verified at creation. -/
def attributeCrossGroupInflow (grossInflow weightA weightB : Nat) : Nat × Nat :=
  let shareA := (grossInflow * weightA) / max 1 (weightA + weightB)
  let shareB := grossInflow - shareA
  (shareA, shareB)

/-- The primary group share never exceeds `grossInflow`. -/
theorem attributeCrossGroupInflow_shareA_le (g wA wB : Nat) :
    (attributeCrossGroupInflow g wA wB).1 ≤ g := by
  simp only [attributeCrossGroupInflow]
  apply Nat.div_le_of_le_mul
  have hw : wA ≤ max 1 (wA + wB) := by omega
  calc
    g * wA ≤ g * max 1 (wA + wB) := Nat.mul_le_mul_left g hw
    _ = max 1 (wA + wB) * g := Nat.mul_comm _ _

/-- Cross-group inflow attribution strictly conserves `grossInflow` with
neither under-collection nor double-counting (`shareA + shareB = grossInflow`). -/
theorem attributeCrossGroupInflow_conserves_total (g wA wB : Nat) :
    (attributeCrossGroupInflow g wA wB).1 + (attributeCrossGroupInflow g wA wB).2 = g := by
  have hle := attributeCrossGroupInflow_shareA_le g wA wB
  simp only [attributeCrossGroupInflow] at hle ⊢
  omega

/-! ### 3.3 Individual Stakeholder Share Forfeiture -/

/-- Looks up the beneficial share (in basis points) of stakeholder `cid` in `cs`,
returning `0` if `cid` is not listed. -/
def lookupStakeholderShare (cs : List StakeholderShare) (cid : StakeholderId) : Nat :=
  match cs with
  | [] => 0
  | c :: rest =>
    if c.stakeholderId == cid then c.shareBps
    else lookupStakeholderShare rest cid

/-- Sum of all stakeholder beneficial shares (in basis points) in `cs`. -/
def totalStakeholderShares : List StakeholderShare → Nat
  | [] => 0
  | c :: rest => c.shareBps + totalStakeholderShares rest

/-- Updates the stakeholder list by reducing the matching `offender`'s `shareBps` by
`min c.shareBps forfeitureBpsOfShare` (using first-match recursion aligned with
`lookupStakeholderShare` so total share reduction always matches `lookupStakeholderShare`). -/
def forfeitStakeholderShareInList
    (cs : List StakeholderShare) (offender : StakeholderId) (forfeitureBpsOfShare : Nat) :
    List StakeholderShare :=
  match cs with
  | [] => []
  | c :: rest =>
    if c.stakeholderId == offender then
      { c with shareBps := c.shareBps - min c.shareBps forfeitureBpsOfShare } :: rest
    else
      c :: forfeitStakeholderShareInList rest offender forfeitureBpsOfShare

/-- Reduces only `offender`'s beneficial share in `S.stakeholders` and increases
`S.ledger.forfeitedPrincipal` by the corresponding proportion of remaining
principal, leaving all innocent stakeholders' shares untouched. -/
def forfeitStakeholderInGroup
    (S : GroupState) (offender : StakeholderId) (forfeitureBpsOfShare : Nat) :
    GroupState :=
  let oldShare := lookupStakeholderShare S.stakeholders offender
  let forfeitedBps := min oldShare forfeitureBpsOfShare
  let remainingPrincipal :=
    S.ledger.initialPrincipal - (S.ledger.paidPrincipal + S.ledger.forfeitedPrincipal)
  let principalReduction := (remainingPrincipal * min forfeitedBps 10000) / 10000
  { S with
    stakeholders := forfeitStakeholderShareInList S.stakeholders offender forfeitureBpsOfShare
    ledger := { S.ledger with
                forfeitedPrincipal := S.ledger.forfeitedPrincipal + principalReduction } }

theorem lookupStakeholderShare_forfeitStakeholderShareInList_of_ne
    (cs : List StakeholderShare) (offender innocent : StakeholderId) (f : Nat)
    (h_ne : innocent ≠ offender) :
    lookupStakeholderShare (forfeitStakeholderShareInList cs offender f) innocent =
      lookupStakeholderShare cs innocent := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [forfeitStakeholderShareInList, lookupStakeholderShare]
    by_cases h_off : c.stakeholderId == offender
    · have h_inn : (c.stakeholderId == innocent) = false := by
        rw [beq_iff_eq] at h_off
        rw [beq_eq_false_iff_ne]
        intro h_eq
        exact h_ne (h_eq.symm.trans h_off)
      simp only [h_off, ↓reduceIte, lookupStakeholderShare, h_inn, Bool.false_eq_true]
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, lookupStakeholderShare]
      split
      · rfl
      · exact ih

theorem lookupStakeholderShare_forfeitStakeholderShareInList_self
    (cs : List StakeholderShare) (offender : StakeholderId) (f : Nat) :
    lookupStakeholderShare (forfeitStakeholderShareInList cs offender f) offender =
      lookupStakeholderShare cs offender - min (lookupStakeholderShare cs offender) f := by
  induction cs with
  | nil => simp [forfeitStakeholderShareInList, lookupStakeholderShare]
  | cons c rest ih =>
    simp only [forfeitStakeholderShareInList, lookupStakeholderShare]
    by_cases h_off : c.stakeholderId == offender
    · simp only [h_off, ↓reduceIte, lookupStakeholderShare]
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, lookupStakeholderShare, ih]

/-- Forfeiting `f` basis points from `offender` reduces `offender`'s share in
`forfeitStakeholderInGroup S offender f` by `min (lookupStakeholderShare S.stakeholders offender) f`. -/
theorem lookupStakeholderShare_forfeitStakeholderInGroup_self
    (S : GroupState) (offender : StakeholderId) (f : Nat) :
    lookupStakeholderShare (forfeitStakeholderInGroup S offender f).stakeholders offender =
      lookupStakeholderShare S.stakeholders offender -
        min (lookupStakeholderShare S.stakeholders offender) f := by
  simp only [forfeitStakeholderInGroup]
  exact lookupStakeholderShare_forfeitStakeholderShareInList_self S.stakeholders offender f

/-- Total stakeholder shares across `cs` decrease by `min (lookupStakeholderShare cs offender) f`
for every stakeholder list `cs` (including lists with duplicate `stakeholderId` entries). -/
theorem totalStakeholderShares_forfeitStakeholderShareInList
    (cs : List StakeholderShare) (offender : StakeholderId) (f : Nat) :
    totalStakeholderShares (forfeitStakeholderShareInList cs offender f) +
      min (lookupStakeholderShare cs offender) f = totalStakeholderShares cs := by
  induction cs with
  | nil => simp [forfeitStakeholderShareInList, lookupStakeholderShare, totalStakeholderShares]
  | cons c rest ih =>
    simp only [forfeitStakeholderShareInList, lookupStakeholderShare, totalStakeholderShares]
    by_cases h_off : c.stakeholderId == offender
    · simp only [h_off, ↓reduceIte, totalStakeholderShares]
      omega
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, totalStakeholderShares]
      omega

/-- Proportional stakeholder forfeiture preserves every innocent stakeholder's share
(`innocent ≠ offender`) and monotonically increases `forfeitedPrincipal`. -/
theorem forfeitStakeholderInGroup_preserves_innocent_stakeholder
    (S : GroupState) (offender innocent : StakeholderId) (f : Nat)
    (h_ne : innocent ≠ offender) :
    lookupStakeholderShare (forfeitStakeholderInGroup S offender f).stakeholders innocent =
      lookupStakeholderShare S.stakeholders innocent ∧
    S.ledger.forfeitedPrincipal ≤
      (forfeitStakeholderInGroup S offender f).ledger.forfeitedPrincipal := by
  constructor
  · exact lookupStakeholderShare_forfeitStakeholderShareInList_of_ne S.stakeholders offender innocent f h_ne
  · simp only [forfeitStakeholderInGroup]
    omega

/-- Proportional stakeholder forfeiture monotonically reduces (or keeps equal) the
group's active founding ledger balance. -/
theorem forfeitStakeholderInGroup_balance_le
    (S : GroupState) (offender : StakeholderId) (f now livingCount : Nat) :
    (forfeitStakeholderInGroup S offender f).ledger.balance now livingCount ≤
      S.ledger.balance now livingCount := by
  simp only [forfeitStakeholderInGroup, GroupLedger.balance]
  split
  · exact Nat.le_refl 0
  · omega

/-! ### 3.4 Per-Member vs. Group-Wide Amendment Scope -/

/-- Applies a per-member ordinary amendment to `target`, updating only `target`'s
`charterVersion` to `newVersion` and leaving every other member untouched. -/
def applyPerMemberAmendment
    (members : List MemberRecord) (target : MemberId) (newVersion : Nat) :
    List MemberRecord :=
  members.map fun a =>
    if a.memberId == target then { a with charterVersion := newVersion }
    else a

/-- Look up a member record by `memberId`. -/
def findMember (members : List MemberRecord) (aid : MemberId) : Option MemberRecord :=
  members.find? fun a => a.memberId == aid

/-- Any member `a ∈ members` with `a.memberId ≠ target` is preserved unchanged in
`applyPerMemberAmendment members target newVersion`. -/
theorem per_member_amendment_preserves_other_members
    (members : List MemberRecord) (target : MemberId) (newVersion : Nat)
    (a : MemberRecord) (h_mem : a ∈ members) (h_ne : a.memberId ≠ target) :
    a ∈ applyPerMemberAmendment members target newVersion := by
  unfold applyPerMemberAmendment
  rw [List.mem_map]
  refine ⟨a, h_mem, ?_⟩
  have h_beq : (a.memberId == target) = false := beq_eq_false_iff_ne.mpr h_ne
  simp [h_beq]

/-- For any record `a` with `a.memberId ≠ target`, membership in
`applyPerMemberAmendment members target newVersion` is equivalent to membership in `members`. -/
theorem mem_applyPerMemberAmendment_iff_of_ne
    (members : List MemberRecord) (target : MemberId) (newVersion : Nat)
    (a : MemberRecord) (h_ne : a.memberId ≠ target) :
    a ∈ applyPerMemberAmendment members target newVersion ↔ a ∈ members := by
  constructor
  · intro h_mem
    unfold applyPerMemberAmendment at h_mem
    rw [List.mem_map] at h_mem
    rcases h_mem with ⟨x, hx_mem, hx_eq⟩
    by_cases h_xt : x.memberId == target
    · simp only [h_xt, ↓reduceIte] at hx_eq
      have h_id : x.memberId = a.memberId := by
        have := congrArg MemberRecord.memberId hx_eq
        simpa using this
      rw [beq_iff_eq] at h_xt
      exact False.elim (h_ne (h_id.symm.trans h_xt))
    · simp only [h_xt, Bool.false_eq_true, ↓reduceIte] at hx_eq
      subst hx_eq
      exact hx_mem
  · intro h_mem
    exact per_member_amendment_preserves_other_members members target newVersion a h_mem h_ne

/-- Looking up any `aid ≠ target` after `applyPerMemberAmendment` returns the
exact same `MemberRecord` (including its `charterVersion`) as before. -/
theorem findMember_applyPerMemberAmendment_of_ne
    (members : List MemberRecord) (target aid : MemberId) (newVersion : Nat)
    (h_ne : aid ≠ target) :
    findMember (applyPerMemberAmendment members target newVersion) aid =
      findMember members aid := by
  unfold applyPerMemberAmendment findMember
  induction members with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_t : a.memberId == target
    · have h_aid : (a.memberId == aid) = false := by
        rw [beq_iff_eq] at h_t
        rw [beq_eq_false_iff_ne]
        intro h_eq
        exact h_ne (h_eq.symm.trans h_t)
      simp only [h_t, ↓reduceIte, h_aid, ih]
    · simp only [h_t, Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · exact ih

/-- Looking up `target` after `applyPerMemberAmendment` returns `target`'s record
with `charterVersion` updated to `newVersion` and all other fields preserved. -/
theorem findMember_applyPerMemberAmendment_self
    (members : List MemberRecord) (target : MemberId) (newVersion : Nat) :
    findMember (applyPerMemberAmendment members target newVersion) target =
      (findMember members target).map (fun a => { a with charterVersion := newVersion }) := by
  unfold applyPerMemberAmendment findMember
  induction members with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_t : a.memberId == target
    · simp only [h_t, ↓reduceIte, Option.map_some]
    · simp only [h_t, Bool.false_eq_true, ↓reduceIte, ih]

/-- A group-wide amendment affecting shared founding-ledger parameters
(retirement fraction, sunset, or group reserve rules) requires ratification
by every living member of the group. -/
def canRatifyGroupWideAmendment
    (S : GroupState) (consentedAgents : List MemberId) : Bool :=
  S.livingMembers.all (fun aid => consentedAgents.contains aid)

/-- If `canRatifyGroupWideAmendment S consented = true`, then every living
member `aid ∈ S.livingMembers` has consented. -/
theorem group_wide_amendment_requires_every_living_member
    (S : GroupState) (consented : List MemberId)
    (h : canRatifyGroupWideAmendment S consented = true) :
    ∀ aid ∈ S.livingMembers, consented.contains aid = true := by
  intro aid haid
  unfold canRatifyGroupWideAmendment at h
  rw [List.all_eq_true] at h
  exact h aid haid

/-- If any single living member `aid ∈ S.livingMembers` withholds consent,
group-wide amendment ratification fails (`false`). -/
theorem group_wide_amendment_blocked_by_dissenting_member
    (S : GroupState) (consented : List MemberId) (aid : MemberId)
    (h_living : aid ∈ S.livingMembers)
    (h_dissent : consented.contains aid = false) :
    canRatifyGroupWideAmendment S consented = false := by
  cases h_rat : canRatifyGroupWideAmendment S consented with
  | false => rfl
  | true =>
    have h_all := group_wide_amendment_requires_every_living_member S consented h_rat aid h_living
    rw [h_dissent] at h_all
    contradiction

/-! ### 3.5 Per-Group Service Budget Cap -/

/-- Grants up to `requested` units from the group's shared service subsidy
budget to `memberId` iff `memberId` is a living member of `S`. Creating
additional group members shares the same `serviceSubsidyBudget` rather than
multiplying institution-funded service entitlements. -/
def claimMemberServiceSubsidy
    (S : GroupState) (memberId : MemberId) (requested : Nat) :
    GroupState × Nat :=
  if S.livingMembers.contains memberId then
    let granted := min requested (S.serviceSubsidyBudget - S.serviceSubsidyUsed)
    ({ S with serviceSubsidyUsed := S.serviceSubsidyUsed + granted }, granted)
  else
    (S, 0)

/-- Regardless of how many members belong to `S.livingMembers`, claiming a
member service subsidy never causes `serviceSubsidyUsed` to exceed
`max S.serviceSubsidyBudget S.serviceSubsidyUsed`. -/
theorem group_subsidy_bounded_by_budget_regardless_of_members
    (S : GroupState) (m : MemberId) (req : Nat) :
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed ≤
      max S.serviceSubsidyBudget S.serviceSubsidyUsed := by
  unfold claimMemberServiceSubsidy
  split <;> simp <;> omega

/-- When `S.serviceSubsidyUsed ≤ S.serviceSubsidyBudget` initially, claiming a
member service subsidy preserves `serviceSubsidyUsed ≤ serviceSubsidyBudget`. -/
theorem group_subsidy_preserves_budget_cap
    (S : GroupState) (m : MemberId) (req : Nat)
    (h_cap : S.serviceSubsidyUsed ≤ S.serviceSubsidyBudget) :
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed ≤ S.serviceSubsidyBudget := by
  have h := group_subsidy_bounded_by_budget_regardless_of_members S m req
  omega

/-- A non-living or non-member record (`S.livingMembers.contains m = false`)
receives `0` service subsidy and leaves `S` unchanged. -/
theorem claimMemberServiceSubsidy_nonmember_zero
    (S : GroupState) (m : MemberId) (req : Nat)
    (h_not_mem : S.livingMembers.contains m = false) :
    claimMemberServiceSubsidy S m req = (S, 0) := by
  unfold claimMemberServiceSubsidy
  simp only [h_not_mem, Bool.false_eq_true, ↓reduceIte]

/-- When a group's shared service subsidy budget is already exhausted
(`S.serviceSubsidyBudget ≤ S.serviceSubsidyUsed`), any additional member claim
grants `0` and leaves `serviceSubsidyUsed` unchanged. -/
theorem claimMemberServiceSubsidy_exhausted_zero
    (S : GroupState) (m : MemberId) (req : Nat)
    (h_exhausted : S.serviceSubsidyBudget ≤ S.serviceSubsidyUsed) :
    (claimMemberServiceSubsidy S m req).2 = 0 ∧
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed = S.serviceSubsidyUsed := by
  unfold claimMemberServiceSubsidy
  split <;> simp <;> omega

namespace Population
export Charter (
  GroupId MemberId StakeholderId OperatorId ArbiterId
  StakeholderShare GroupLedger GroupState MemberRecord
  balance
  transferMemberCarryover transferMemberCarryover_conserves_basis_and_loss
  transferMemberCarryover_same_group
  transferMemberCarryover_cross_group_none
  transferMemberCarryover_self_none
  totalMemberBasis totalMemberLoss totalMemberBasis_and_loss_conserved_on_pair
  attributeCrossGroupInflow attributeCrossGroupInflow_shareA_le
  attributeCrossGroupInflow_conserves_total
  lookupStakeholderShare totalStakeholderShares
  forfeitStakeholderShareInList forfeitStakeholderInGroup
  lookupStakeholderShare_forfeitStakeholderShareInList_of_ne
  lookupStakeholderShare_forfeitStakeholderShareInList_self
  lookupStakeholderShare_forfeitStakeholderInGroup_self
  totalStakeholderShares_forfeitStakeholderShareInList
  forfeitStakeholderInGroup_preserves_innocent_stakeholder
  forfeitStakeholderInGroup_balance_le
  applyPerMemberAmendment findMember
  per_member_amendment_preserves_other_members
  mem_applyPerMemberAmendment_iff_of_ne
  findMember_applyPerMemberAmendment_of_ne
  findMember_applyPerMemberAmendment_self
  canRatifyGroupWideAmendment
  group_wide_amendment_requires_every_living_member
  group_wide_amendment_blocked_by_dissenting_member
  claimMemberServiceSubsidy
  group_subsidy_bounded_by_budget_regardless_of_members
  group_subsidy_preserves_budget_cap
  claimMemberServiceSubsidy_nonmember_zero
  claimMemberServiceSubsidy_exhausted_zero
)
end Population

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

namespace Core

export Charter (
  ParamEntityRef
  GroupId
  MemberId
  StakeholderId
  OperatorId
  ArbiterId
  StakeholderShare
  GroupLedger
  GroupState
  MemberRecord
  balance
  transferMemberCarryover
  transferMemberCarryover_conserves_basis_and_loss
  transferMemberCarryover_same_group
  transferMemberCarryover_cross_group_none
  transferMemberCarryover_self_none
  totalMemberBasis
  totalMemberLoss
  totalMemberBasis_and_loss_conserved_on_pair
  attributeCrossGroupInflow
  attributeCrossGroupInflow_shareA_le
  attributeCrossGroupInflow_conserves_total
  lookupStakeholderShare
  totalStakeholderShares
  forfeitStakeholderShareInList
  forfeitStakeholderInGroup
  lookupStakeholderShare_forfeitStakeholderShareInList_of_ne
  lookupStakeholderShare_forfeitStakeholderShareInList_self
  lookupStakeholderShare_forfeitStakeholderInGroup_self
  totalStakeholderShares_forfeitStakeholderShareInList
  forfeitStakeholderInGroup_preserves_innocent_stakeholder
  forfeitStakeholderInGroup_balance_le
  applyPerMemberAmendment
  findMember
  per_member_amendment_preserves_other_members
  mem_applyPerMemberAmendment_iff_of_ne
  findMember_applyPerMemberAmendment_of_ne
  findMember_applyPerMemberAmendment_self
  canRatifyGroupWideAmendment
  group_wide_amendment_requires_every_living_member
  group_wide_amendment_blocked_by_dissenting_member
  claimMemberServiceSubsidy
  group_subsidy_bounded_by_budget_regardless_of_members
  group_subsidy_preserves_budget_cap
  claimMemberServiceSubsidy_nonmember_zero
  claimMemberServiceSubsidy_exhausted_zero
)

namespace ParamEntityRef
export Charter.ParamEntityRef (toRole toParty toRole_mem_of_all)
end ParamEntityRef

namespace GroupLedger
export Charter.GroupLedger (balance balance_eq_zero_of_sunset balance_eq_zero_of_extinction balance_le_initialPrincipal)
end GroupLedger

namespace GroupState
export Charter.GroupState (ledgerBalance)
end GroupState

end Core

end Charter
