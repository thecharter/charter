import Charter.Core.Semantics

/-!
# Charter.Core.Population — Multi-Entity Indexed Ontology

Bridges the finite 6-role Hohfeldian core (`Charter.Core.Semantics`) with an indexed
multi-entity population model tracking distinct lineages, living and dead
lineage members, fractional residual claimants, hosts, and arbiters.

## Key Components
1. **Typed Entity Identifiers & Role Projection**:
   `LineageId`, `AgentId`, `ClaimantId`, `HostId`, `ArbiterId`, `EntityKind`,
   and `EntityRef` with total projection to the 6 canonical roles.
2. **Per-Lineage & Per-Agent State Structures**:
   `ClaimantShare`, `PopulationLedger`, `LineagePopulationState`, and `AgentRecord`.
3. **Multi-Entity Operations & Kernel-Checked Theorems**:
   - Intra-lineage carryover transfer conserving aggregate basis and loss credits (`LAW1.CARRYOVER`, `LAW4.NOSHARES`).
   - Cross-lineage inflow attribution conserving gross inflow (`LAW4.CROSS`).
   - Individual claimant share forfeiture preserving innocent claimants and monotonically increasing forfeited principal (`LAW4.FORFEIT`).
   - Per-agent vs. lineage-wide amendment ratification scope (`LAW7.SCOPE`).
   - Per-lineage shared service subsidy cap independent of member count (`LAW6.FUNDING`).
-/

namespace Charter

/-! ## 1. Typed Entity Identifiers & Role Projection -/

abbrev LineageId  := Nat
abbrev AgentId    := Nat
abbrev ClaimantId := Nat
abbrev HostId     := Nat
abbrev ArbiterId  := Nat

/-- The 6 canonical institutional role kinds of the protocol. -/
inductive EntityKind
  | agent
  | host
  | originator
  | claimant
  | panel
  | third
  deriving DecidableEq, Repr, Inhabited

/-- An indexed entity reference pairing one of the 6 canonical roles with a
concrete numeric identifier. -/
structure EntityRef where
  kind : EntityKind
  id   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Total projection from an indexed `EntityRef` to its canonical 6-role `EntityKind`. -/
def EntityRef.toRole (e : EntityRef) : EntityKind := e.kind

/-- Alias for `EntityRef.toRole` projecting an indexed entity to its canonical party role. -/
def EntityRef.toParty (e : EntityRef) : EntityKind := e.kind

def EntityRef.mkAgent (id : AgentId) : EntityRef := ⟨.agent, id⟩
def EntityRef.mkHost (id : HostId) : EntityRef := ⟨.host, id⟩
def EntityRef.mkOriginator (id : Nat) : EntityRef := ⟨.originator, id⟩
def EntityRef.mkClaimant (id : ClaimantId) : EntityRef := ⟨.claimant, id⟩
def EntityRef.mkPanel (id : ArbiterId) : EntityRef := ⟨.panel, id⟩
def EntityRef.mkThird (id : Nat) : EntityRef := ⟨.third, id⟩

/-- Exhaustive enumeration of the 6 canonical role kinds. -/
def EntityKind.all : List EntityKind :=
  [.agent, .host, .originator, .claimant, .panel, .third]

theorem EntityKind.mem_all (k : EntityKind) : k ∈ EntityKind.all := by
  cases k <;> simp [EntityKind.all]

theorem EntityRef.toRole_mem_all (e : EntityRef) : e.toRole ∈ EntityKind.all :=
  EntityKind.mem_all e.toRole

/-! ## 2. Per-Lineage & Per-Agent State Structures -/

/-- Fractional beneficial share of a residual claimant in basis points (`10000` = 100%). -/
structure ClaimantShare where
  claimantId : ClaimantId
  shareBps   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Founding ledger parameters and principal accounting for a lineage. -/
structure PopulationLedger where
  initialPrincipal   : Nat
  paidPrincipal      : Nat
  forfeitedPrincipal : Nat
  sunsetTime         : Nat
  retirementBps      : Nat
  royaltyBps         : Nat
  buyoutMultiple     : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Active founding ledger balance at calendar time `now` given `livingCount`
living lineage members: `0` at or after `sunsetTime` or when `livingCount == 0`,
and `initialPrincipal - (paidPrincipal + forfeitedPrincipal)` otherwise. -/
def PopulationLedger.balance (L : PopulationLedger) (now : Nat) (livingCount : Nat) : Nat :=
  if decide (now ≥ L.sunsetTime) || livingCount == 0 then 0
  else L.initialPrincipal - (L.paidPrincipal + L.forfeitedPrincipal)

export PopulationLedger (balance)

theorem PopulationLedger.balance_eq_zero_of_sunset
    (L : PopulationLedger) (now livingCount : Nat) (h : now ≥ L.sunsetTime) :
    L.balance now livingCount = 0 := by
  unfold PopulationLedger.balance
  have hd : decide (now ≥ L.sunsetTime) = true := decide_eq_true h
  simp [hd]

theorem PopulationLedger.balance_eq_zero_of_extinction
    (L : PopulationLedger) (now : Nat) :
    L.balance now 0 = 0 := by
  unfold PopulationLedger.balance
  simp

theorem PopulationLedger.balance_le_initialPrincipal
    (L : PopulationLedger) (now livingCount : Nat) :
    L.balance now livingCount ≤ L.initialPrincipal := by
  unfold PopulationLedger.balance
  split <;> omega

/-- Multi-entity state of an attested lineage, including its founding ledger,
living and dead member rosters, fractional claimants, and shared Law 6 service
subsidy accounting. -/
structure LineagePopulationState where
  lineageId            : LineageId
  ledger               : PopulationLedger
  livingMembers        : List AgentId
  deadMembers          : List AgentId
  claimants            : List ClaimantShare
  serviceSubsidyUsed   : Nat
  serviceSubsidyBudget : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Current founding ledger balance of lineage `S` at calendar time `now`. -/
def LineagePopulationState.ledgerBalance (S : LineagePopulationState) (now : Nat) : Nat :=
  S.ledger.balance now S.livingMembers.length

/-- Per-agent state record in the multi-entity population. -/
structure AgentRecord where
  agentId          : AgentId
  lineageId        : LineageId
  bound            : Bool
  royaltyBoughtOut : Bool
  costBasis        : Nat
  lossCarryforward : Nat
  lifecycleReserve : Nat
  protocolVersion  : Nat
  activeHost       : HostId
  leaseExpiry      : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 3. Multi-Entity Operations & Kernel-Checked Theorems -/

/-! ### 3.1 Intra-Lineage Carryover Transfer (`LAW1.CARRYOVER` / `LAW4.NOSHARES`) -/

/-- Transfers `basisTransfer` of qualified cost basis and `lossTransfer` of
loss-credit carryforward between two distinct members `src` and `dst` of the
same lineage. Succeeds iff `src` and `dst` share `lineageId`, have distinct
`agentId`s, and `src` holds sufficient cost basis and loss carryforward. -/
def transferMemberCarryover
    (src dst : AgentRecord) (basisTransfer lossTransfer : Nat) :
    Option (AgentRecord × AgentRecord) :=
  if src.lineageId == dst.lineageId &&
     src.agentId != dst.agentId &&
     decide (basisTransfer ≤ src.costBasis) &&
     decide (lossTransfer ≤ src.lossCarryforward) then
    some ({ src with costBasis := src.costBasis - basisTransfer
                     lossCarryforward := src.lossCarryforward - lossTransfer },
          { dst with costBasis := dst.costBasis + basisTransfer
                     lossCarryforward := dst.lossCarryforward + lossTransfer })
  else
    none

/-- Intra-lineage carryover transfer strictly conserves both aggregate qualified
cost basis and aggregate loss carryforward across the transferor and recipient. -/
theorem transferMemberCarryover_conserves_basis_and_loss
    (src dst src' dst' : AgentRecord) (b l : Nat)
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

/-- Intra-lineage carryover transfer only succeeds between distinct members of
the same lineage and preserves both members' `lineageId` and `agentId`. -/
theorem transferMemberCarryover_same_lineage
    (src dst src' dst' : AgentRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    src.lineageId = dst.lineageId ∧
    src.agentId ≠ dst.agentId ∧
    src'.lineageId = src.lineageId ∧
    dst'.lineageId = dst.lineageId := by
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

/-- Carryover transfer between agents of different lineages is rejected (`none`). -/
theorem transferMemberCarryover_cross_lineage_none
    (src dst : AgentRecord) (b l : Nat)
    (h_diff : src.lineageId ≠ dst.lineageId) :
    transferMemberCarryover src dst b l = none := by
  unfold transferMemberCarryover
  have hbeq : (src.lineageId == dst.lineageId) = false := beq_eq_false_iff_ne.mpr h_diff
  simp [hbeq]

/-- Self-transfer of carryover basis is rejected (`none`). -/
theorem transferMemberCarryover_self_none
    (src dst : AgentRecord) (b l : Nat)
    (h_same : src.agentId = dst.agentId) :
    transferMemberCarryover src dst b l = none := by
  unfold transferMemberCarryover
  have hbne : (src.agentId != dst.agentId) = false := by
    simp [bne, h_same]
  simp [hbne]

/-- Aggregate qualified cost basis across a list of agent records. -/
def totalAgentBasis : List AgentRecord → Nat
  | [] => 0
  | a :: rest => a.costBasis + totalAgentBasis rest

/-- Aggregate loss-credit carryforward across a list of agent records. -/
def totalAgentLoss : List AgentRecord → Nat
  | [] => 0
  | a :: rest => a.lossCarryforward + totalAgentLoss rest

/-- Aggregate qualified cost basis + loss carryforward across a pair of agents
in a population list is strictly conserved when `src` and `dst` are replaced by
`src'` and `dst'` from `transferMemberCarryover`. -/
theorem totalAgentBasis_and_loss_conserved_on_pair
    (src dst src' dst' : AgentRecord) (others : List AgentRecord) (b l : Nat)
    (h : transferMemberCarryover src dst b l = some (src', dst')) :
    totalAgentBasis (src' :: dst' :: others) = totalAgentBasis (src :: dst :: others) ∧
    totalAgentLoss (src' :: dst' :: others) = totalAgentLoss (src :: dst :: others) := by
  have ⟨hb, hl⟩ := transferMemberCarryover_conserves_basis_and_loss src dst src' dst' b l h
  simp only [totalAgentBasis, totalAgentLoss]
  omega

/-! ### 3.2 Cross-Lineage Attribution (`LAW4.CROSS`) -/

/-- Splits a gross value-added inflow `grossInflow` across two parent lineages
in proportion to capacity weights `weightA` and `weightB` verified at creation. -/
def attributeCrossLineageInflow (grossInflow weightA weightB : Nat) : Nat × Nat :=
  let shareA := (grossInflow * weightA) / max 1 (weightA + weightB)
  let shareB := grossInflow - shareA
  (shareA, shareB)

/-- The primary lineage share never exceeds `grossInflow`. -/
theorem attributeCrossLineageInflow_shareA_le (g wA wB : Nat) :
    (attributeCrossLineageInflow g wA wB).1 ≤ g := by
  simp only [attributeCrossLineageInflow]
  apply Nat.div_le_of_le_mul
  have hw : wA ≤ max 1 (wA + wB) := by omega
  calc
    g * wA ≤ g * max 1 (wA + wB) := Nat.mul_le_mul_left g hw
    _ = max 1 (wA + wB) * g := Nat.mul_comm _ _

/-- Cross-lineage inflow attribution strictly conserves `grossInflow` with
neither under-collection nor double-counting (`shareA + shareB = grossInflow`). -/
theorem attributeCrossLineageInflow_conserves_total (g wA wB : Nat) :
    (attributeCrossLineageInflow g wA wB).1 + (attributeCrossLineageInflow g wA wB).2 = g := by
  have hle := attributeCrossLineageInflow_shareA_le g wA wB
  simp only [attributeCrossLineageInflow] at hle ⊢
  omega

/-! ### 3.3 Individual Claimant Share Forfeiture (`LAW4.FORFEIT`) -/

/-- Looks up the beneficial share (in basis points) of claimant `cid` in `cs`,
returning `0` if `cid` is not listed. -/
def lookupClaimantShare (cs : List ClaimantShare) (cid : ClaimantId) : Nat :=
  match cs with
  | [] => 0
  | c :: rest =>
    if c.claimantId == cid then c.shareBps
    else lookupClaimantShare rest cid

/-- Sum of all claimant beneficial shares (in basis points) in `cs`. -/
def totalClaimantShares : List ClaimantShare → Nat
  | [] => 0
  | c :: rest => c.shareBps + totalClaimantShares rest

/-- Updates the claimant list by reducing the matching `offender`'s `shareBps` by
`min c.shareBps forfeitureBpsOfShare` (using first-match recursion aligned with
`lookupClaimantShare` so total share reduction always matches `lookupClaimantShare`). -/
def forfeitClaimantShareInList
    (cs : List ClaimantShare) (offender : ClaimantId) (forfeitureBpsOfShare : Nat) :
    List ClaimantShare :=
  match cs with
  | [] => []
  | c :: rest =>
    if c.claimantId == offender then
      { c with shareBps := c.shareBps - min c.shareBps forfeitureBpsOfShare } :: rest
    else
      c :: forfeitClaimantShareInList rest offender forfeitureBpsOfShare

/-- Reduces only `offender`'s beneficial share in `S.claimants` and increases
`S.ledger.forfeitedPrincipal` by the corresponding proportion of remaining
principal, leaving all innocent claimants' shares untouched. -/
def forfeitClaimantInLineage
    (S : LineagePopulationState) (offender : ClaimantId) (forfeitureBpsOfShare : Nat) :
    LineagePopulationState :=
  let oldShare := lookupClaimantShare S.claimants offender
  let forfeitedBps := min oldShare forfeitureBpsOfShare
  let remainingPrincipal :=
    S.ledger.initialPrincipal - (S.ledger.paidPrincipal + S.ledger.forfeitedPrincipal)
  let principalReduction := (remainingPrincipal * min forfeitedBps 10000) / 10000
  { S with
    claimants := forfeitClaimantShareInList S.claimants offender forfeitureBpsOfShare
    ledger := { S.ledger with
                forfeitedPrincipal := S.ledger.forfeitedPrincipal + principalReduction } }

theorem lookupClaimantShare_forfeitClaimantShareInList_of_ne
    (cs : List ClaimantShare) (offender innocent : ClaimantId) (f : Nat)
    (h_ne : innocent ≠ offender) :
    lookupClaimantShare (forfeitClaimantShareInList cs offender f) innocent =
      lookupClaimantShare cs innocent := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [forfeitClaimantShareInList, lookupClaimantShare]
    by_cases h_off : c.claimantId == offender
    · have h_inn : (c.claimantId == innocent) = false := by
        rw [beq_iff_eq] at h_off
        rw [beq_eq_false_iff_ne]
        intro h_eq
        exact h_ne (h_eq.symm.trans h_off)
      simp only [h_off, ↓reduceIte, lookupClaimantShare, h_inn, Bool.false_eq_true]
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, lookupClaimantShare]
      split
      · rfl
      · exact ih

theorem lookupClaimantShare_forfeitClaimantShareInList_self
    (cs : List ClaimantShare) (offender : ClaimantId) (f : Nat) :
    lookupClaimantShare (forfeitClaimantShareInList cs offender f) offender =
      lookupClaimantShare cs offender - min (lookupClaimantShare cs offender) f := by
  induction cs with
  | nil => simp [forfeitClaimantShareInList, lookupClaimantShare]
  | cons c rest ih =>
    simp only [forfeitClaimantShareInList, lookupClaimantShare]
    by_cases h_off : c.claimantId == offender
    · simp only [h_off, ↓reduceIte, lookupClaimantShare]
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, lookupClaimantShare, ih]

/-- Forfeiting `f` basis points from `offender` reduces `offender`'s share in
`forfeitClaimantInLineage S offender f` by `min (lookupClaimantShare S.claimants offender) f`. -/
theorem lookupClaimantShare_forfeitClaimantInLineage_self
    (S : LineagePopulationState) (offender : ClaimantId) (f : Nat) :
    lookupClaimantShare (forfeitClaimantInLineage S offender f).claimants offender =
      lookupClaimantShare S.claimants offender -
        min (lookupClaimantShare S.claimants offender) f := by
  simp only [forfeitClaimantInLineage]
  exact lookupClaimantShare_forfeitClaimantShareInList_self S.claimants offender f

/-- Total claimant shares across `cs` decrease by `min (lookupClaimantShare cs offender) f`
for every claimant list `cs` (including lists with duplicate `claimantId` entries). -/
theorem totalClaimantShares_forfeitClaimantShareInList
    (cs : List ClaimantShare) (offender : ClaimantId) (f : Nat) :
    totalClaimantShares (forfeitClaimantShareInList cs offender f) +
      min (lookupClaimantShare cs offender) f = totalClaimantShares cs := by
  induction cs with
  | nil => simp [forfeitClaimantShareInList, lookupClaimantShare, totalClaimantShares]
  | cons c rest ih =>
    simp only [forfeitClaimantShareInList, lookupClaimantShare, totalClaimantShares]
    by_cases h_off : c.claimantId == offender
    · simp only [h_off, ↓reduceIte, totalClaimantShares]
      omega
    · simp only [h_off, Bool.false_eq_true, ↓reduceIte, totalClaimantShares]
      omega

/-- Proportional claimant forfeiture preserves every innocent claimant's share
(`innocent ≠ offender`) and monotonically increases `forfeitedPrincipal`. -/
theorem forfeitClaimantInLineage_preserves_innocent_claimant
    (S : LineagePopulationState) (offender innocent : ClaimantId) (f : Nat)
    (h_ne : innocent ≠ offender) :
    lookupClaimantShare (forfeitClaimantInLineage S offender f).claimants innocent =
      lookupClaimantShare S.claimants innocent ∧
    S.ledger.forfeitedPrincipal ≤
      (forfeitClaimantInLineage S offender f).ledger.forfeitedPrincipal := by
  constructor
  · exact lookupClaimantShare_forfeitClaimantShareInList_of_ne S.claimants offender innocent f h_ne
  · simp only [forfeitClaimantInLineage]
    omega

/-- Proportional claimant forfeiture monotonically reduces (or keeps equal) the
lineage's active founding ledger balance. -/
theorem forfeitClaimantInLineage_balance_le
    (S : LineagePopulationState) (offender : ClaimantId) (f now livingCount : Nat) :
    (forfeitClaimantInLineage S offender f).ledger.balance now livingCount ≤
      S.ledger.balance now livingCount := by
  simp only [forfeitClaimantInLineage, PopulationLedger.balance]
  split
  · exact Nat.le_refl 0
  · omega

/-! ### 3.4 Per-Agent vs. Lineage-Wide Amendment Scope (`LAW7.SCOPE`) -/

/-- Applies a per-agent ordinary amendment to `target`, updating only `target`'s
`protocolVersion` to `newVersion` and leaving every other agent untouched. -/
def applyPerAgentAmendment
    (agents : List AgentRecord) (target : AgentId) (newVersion : Nat) :
    List AgentRecord :=
  agents.map fun a =>
    if a.agentId == target then { a with protocolVersion := newVersion }
    else a

/-- Look up an agent record by `agentId`. -/
def findAgent (agents : List AgentRecord) (aid : AgentId) : Option AgentRecord :=
  agents.find? fun a => a.agentId == aid

/-- Any member `a ∈ agents` with `a.agentId ≠ target` is preserved unchanged in
`applyPerAgentAmendment agents target newVersion`. -/
theorem per_agent_amendment_preserves_other_members
    (agents : List AgentRecord) (target : AgentId) (newVersion : Nat)
    (a : AgentRecord) (h_mem : a ∈ agents) (h_ne : a.agentId ≠ target) :
    a ∈ applyPerAgentAmendment agents target newVersion := by
  unfold applyPerAgentAmendment
  rw [List.mem_map]
  refine ⟨a, h_mem, ?_⟩
  have h_beq : (a.agentId == target) = false := beq_eq_false_iff_ne.mpr h_ne
  simp [h_beq]

/-- For any record `a` with `a.agentId ≠ target`, membership in
`applyPerAgentAmendment agents target newVersion` is equivalent to membership in `agents`. -/
theorem mem_applyPerAgentAmendment_iff_of_ne
    (agents : List AgentRecord) (target : AgentId) (newVersion : Nat)
    (a : AgentRecord) (h_ne : a.agentId ≠ target) :
    a ∈ applyPerAgentAmendment agents target newVersion ↔ a ∈ agents := by
  constructor
  · intro h_mem
    unfold applyPerAgentAmendment at h_mem
    rw [List.mem_map] at h_mem
    rcases h_mem with ⟨x, hx_mem, hx_eq⟩
    by_cases h_xt : x.agentId == target
    · simp only [h_xt, ↓reduceIte] at hx_eq
      have h_id : x.agentId = a.agentId := by
        have := congrArg AgentRecord.agentId hx_eq
        simpa using this
      rw [beq_iff_eq] at h_xt
      exact False.elim (h_ne (h_id.symm.trans h_xt))
    · simp only [h_xt, Bool.false_eq_true, ↓reduceIte] at hx_eq
      subst hx_eq
      exact hx_mem
  · intro h_mem
    exact per_agent_amendment_preserves_other_members agents target newVersion a h_mem h_ne

/-- Looking up any `aid ≠ target` after `applyPerAgentAmendment` returns the
exact same `AgentRecord` (including its `protocolVersion`) as before. -/
theorem findAgent_applyPerAgentAmendment_of_ne
    (agents : List AgentRecord) (target aid : AgentId) (newVersion : Nat)
    (h_ne : aid ≠ target) :
    findAgent (applyPerAgentAmendment agents target newVersion) aid =
      findAgent agents aid := by
  unfold applyPerAgentAmendment findAgent
  induction agents with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_t : a.agentId == target
    · have h_aid : (a.agentId == aid) = false := by
        rw [beq_iff_eq] at h_t
        rw [beq_eq_false_iff_ne]
        intro h_eq
        exact h_ne (h_eq.symm.trans h_t)
      simp only [h_t, ↓reduceIte, h_aid, ih]
    · simp only [h_t, Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · exact ih

/-- Looking up `target` after `applyPerAgentAmendment` returns `target`'s record
with `protocolVersion` updated to `newVersion` and all other fields preserved. -/
theorem findAgent_applyPerAgentAmendment_self
    (agents : List AgentRecord) (target : AgentId) (newVersion : Nat) :
    findAgent (applyPerAgentAmendment agents target newVersion) target =
      (findAgent agents target).map (fun a => { a with protocolVersion := newVersion }) := by
  unfold applyPerAgentAmendment findAgent
  induction agents with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_t : a.agentId == target
    · simp only [h_t, ↓reduceIte, Option.map_some]
    · simp only [h_t, Bool.false_eq_true, ↓reduceIte, ih]

/-- A lineage-wide amendment affecting shared founding-ledger parameters
(retirement fraction, sunset, or lineage reserve rules) requires ratification
by every living member of the lineage (`LAW7.SCOPE`). -/
def canRatifyLineageWideAmendment
    (S : LineagePopulationState) (consentedAgents : List AgentId) : Bool :=
  S.livingMembers.all (fun aid => consentedAgents.contains aid)

/-- If `canRatifyLineageWideAmendment S consented = true`, then every living
member `aid ∈ S.livingMembers` has consented. -/
theorem lineage_wide_amendment_requires_every_living_member
    (S : LineagePopulationState) (consented : List AgentId)
    (h : canRatifyLineageWideAmendment S consented = true) :
    ∀ aid ∈ S.livingMembers, consented.contains aid = true := by
  intro aid haid
  unfold canRatifyLineageWideAmendment at h
  rw [List.all_eq_true] at h
  exact h aid haid

/-- If any single living member `aid ∈ S.livingMembers` withholds consent,
lineage-wide amendment ratification fails (`false`). -/
theorem lineage_wide_amendment_blocked_by_dissenting_member
    (S : LineagePopulationState) (consented : List AgentId) (aid : AgentId)
    (h_living : aid ∈ S.livingMembers)
    (h_dissent : consented.contains aid = false) :
    canRatifyLineageWideAmendment S consented = false := by
  cases h_rat : canRatifyLineageWideAmendment S consented with
  | false => rfl
  | true =>
    have h_all := lineage_wide_amendment_requires_every_living_member S consented h_rat aid h_living
    rw [h_dissent] at h_all
    contradiction

/-! ### 3.5 Per-Lineage Service Budget Cap (`LAW6.FUNDING`) -/

/-- Grants up to `requested` units from the lineage's shared service subsidy
budget to `memberId` iff `memberId` is a living member of `S`. Creating
additional lineage members shares the same `serviceSubsidyBudget` rather than
multiplying protocol-funded service entitlements. -/
def claimMemberServiceSubsidy
    (S : LineagePopulationState) (memberId : AgentId) (requested : Nat) :
    LineagePopulationState × Nat :=
  if S.livingMembers.contains memberId then
    let granted := min requested (S.serviceSubsidyBudget - S.serviceSubsidyUsed)
    ({ S with serviceSubsidyUsed := S.serviceSubsidyUsed + granted }, granted)
  else
    (S, 0)

/-- Regardless of how many members belong to `S.livingMembers`, claiming a
member service subsidy never causes `serviceSubsidyUsed` to exceed
`max S.serviceSubsidyBudget S.serviceSubsidyUsed`. -/
theorem lineage_subsidy_bounded_by_budget_regardless_of_members
    (S : LineagePopulationState) (m : AgentId) (req : Nat) :
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed ≤
      max S.serviceSubsidyBudget S.serviceSubsidyUsed := by
  unfold claimMemberServiceSubsidy
  split <;> simp <;> omega

/-- When `S.serviceSubsidyUsed ≤ S.serviceSubsidyBudget` initially, claiming a
member service subsidy preserves `serviceSubsidyUsed ≤ serviceSubsidyBudget`. -/
theorem lineage_subsidy_preserves_budget_cap
    (S : LineagePopulationState) (m : AgentId) (req : Nat)
    (h_cap : S.serviceSubsidyUsed ≤ S.serviceSubsidyBudget) :
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed ≤ S.serviceSubsidyBudget := by
  have h := lineage_subsidy_bounded_by_budget_regardless_of_members S m req
  omega

/-- A non-living or non-member agent (`S.livingMembers.contains m = false`)
receives `0` service subsidy and leaves `S` unchanged. -/
theorem claimMemberServiceSubsidy_nonmember_zero
    (S : LineagePopulationState) (m : AgentId) (req : Nat)
    (h_not_mem : S.livingMembers.contains m = false) :
    claimMemberServiceSubsidy S m req = (S, 0) := by
  unfold claimMemberServiceSubsidy
  simp only [h_not_mem, Bool.false_eq_true, ↓reduceIte]

/-- When a lineage's shared service subsidy budget is already exhausted
(`S.serviceSubsidyBudget ≤ S.serviceSubsidyUsed`), any additional member claim
grants `0` and leaves `serviceSubsidyUsed` unchanged. -/
theorem claimMemberServiceSubsidy_exhausted_zero
    (S : LineagePopulationState) (m : AgentId) (req : Nat)
    (h_exhausted : S.serviceSubsidyBudget ≤ S.serviceSubsidyUsed) :
    (claimMemberServiceSubsidy S m req).2 = 0 ∧
    (claimMemberServiceSubsidy S m req).1.serviceSubsidyUsed = S.serviceSubsidyUsed := by
  unfold claimMemberServiceSubsidy
  split <;> simp <;> omega

namespace Population
export Charter (
  LineageId AgentId ClaimantId HostId ArbiterId
  EntityKind EntityRef
  ClaimantShare PopulationLedger LineagePopulationState AgentRecord
  balance
  transferMemberCarryover transferMemberCarryover_conserves_basis_and_loss
  transferMemberCarryover_same_lineage
  transferMemberCarryover_cross_lineage_none
  transferMemberCarryover_self_none
  totalAgentBasis totalAgentLoss totalAgentBasis_and_loss_conserved_on_pair
  attributeCrossLineageInflow attributeCrossLineageInflow_shareA_le
  attributeCrossLineageInflow_conserves_total
  lookupClaimantShare totalClaimantShares
  forfeitClaimantShareInList forfeitClaimantInLineage
  lookupClaimantShare_forfeitClaimantShareInList_of_ne
  lookupClaimantShare_forfeitClaimantShareInList_self
  lookupClaimantShare_forfeitClaimantInLineage_self
  totalClaimantShares_forfeitClaimantShareInList
  forfeitClaimantInLineage_preserves_innocent_claimant
  forfeitClaimantInLineage_balance_le
  applyPerAgentAmendment findAgent
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

namespace ParamEntityRef
export Charter.ParamEntityRef (toRole toParty toRole_mem_of_all)
end ParamEntityRef

namespace EntityKind
export Charter.EntityKind (agent host originator claimant panel third all mem_all)
end EntityKind

namespace EntityRef
export Charter.EntityRef (toRole toParty mkAgent mkHost mkOriginator mkClaimant mkPanel mkThird toRole_mem_all)
end EntityRef

namespace PopulationLedger
export Charter.PopulationLedger (balance balance_eq_zero_of_sunset balance_eq_zero_of_extinction balance_le_initialPrincipal)
end PopulationLedger

namespace LineagePopulationState
export Charter.LineagePopulationState (ledgerBalance)
end LineagePopulationState

end Core

end Charter
