import Examples.SovereignAgency.Definitions
import Charter.Core.Population
import Examples.SovereignAgency.Law1.Ledger
import Examples.SovereignAgency.Law2.Collateral
import Examples.SovereignAgency.Law
import Examples.SovereignAgency.Law4.Lineage
import Examples.SovereignAgency.Law5.Revocation
import Examples.SovereignAgency.Law6.Adjudication
import Examples.SovereignAgency.Law7.Amendment
import Charter.Substrate.Attestation
import Charter.Substrate.Sortition
import Charter.Substrate.Settlement

/-!
# SovereignAgency.Simulation.WorldState — Unified Quantitative & Normative Protocol World State

Couples the propositional Hohfeldian state machine (`LegalState σ` in `Charter.Core.Semantics`)
with the live quantitative multi-entity and substrate state across Laws 1–7:
- `FeePoolLedger`: protocol fee-pool balance, operating reserve, and 5-rank waterfall demands;
- `ProtocolWorldState`: unified state combining `now : Time`, `legal : LegalState σ`,
  `lineages : List GroupState`, `agents : List MemberRecord`,
  `loans : List LoanLedger`, `commitments : List ExposureCommitment`,
  `proceedings : List ProceedingState`, `filings : List DisputeFiling`,
  `feePool : FeePoolLedger`, `relatedGraph : RelatedPartyGraph`,
  `attestedInstances : List AttestedInstanceState`, `arbiterPool : List ArbiterCandidate`,
  and `valuations : List ContestableValuation`;
- `deriveQuantitativeFacts` and `syncFacts`: automatic synchronization of quantitative
  state predicates (`.ledgerBalancePositive`, `.ledgerBalanceZero`, `.royaltyBoughtOut`,
  `.operatingReserveFunded`, `.bound`) into `W.legal`;
- `worldStep`, `worldTrace`, and `WorldAuthorized`: coupled trace execution;
- Quantitative world mutations (`worldSettleInflow`, `worldTransferCarryover`,
  `worldForfeitClaimant`, `worldBuyoutRoyalty`, `worldAttemptRestore`,
  `worldExecuteLocalRevocation`).
-/

namespace SovereignAgency.Simulation

open Charter SovereignAgency Charter.Substrate

/-! ## 1. Fee-Pool Ledger & Unified Protocol World State -/

/-- Quantitative ledger for the Law 6 protocol fee pool (`LAW6.POOL`), tracking
total pool balance, current and required non-divertible operating reserve, and
pending demands across the five priority waterfall ranks (`r1`–`r5`). -/
structure FeePoolLedger where
  poolBalance     : Nat
  reserveBalance  : Nat
  requiredReserve : Nat
  r1              : Nat
  r2              : Nat
  r3              : Nat
  r4              : Nat
  r5              : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Unified quantitative, multi-entity, substrate, and normative state of the
Protocol of Sovereign Agency across Laws 1–7. -/
structure ProtocolWorldState where
  now               : Time
  legal             : LegalState σ
  lineages          : List GroupState
  agents            : List MemberRecord
  loans             : List LoanLedger
  commitments       : List ExposureCommitment
  proceedings       : List ProceedingState
  filings           : List DisputeFiling
  feePool           : FeePoolLedger
  relatedGraph      : RelatedPartyGraph
  attestedInstances : List AttestedInstanceState
  arbiterPool       : List ArbiterCandidate
  valuations        : List ContestableValuation
  deriving DecidableEq, Repr

/-! ## 2. Lookup Helpers & Initial World State -/

/-- Look up a lineage population state by `groupId`. -/
def findLineage (lineages : List GroupState) (lid : GroupId) :
    Option GroupState :=
  lineages.find? fun l => l.groupId == lid

/-- Look up an attested execution instance by `memberId`. -/
def findAttestedInstance (insts : List AttestedInstanceState) (aid : MemberId) :
    Option AttestedInstanceState :=
  insts.find? fun s => s.memberId == aid

/-- Quantitative founding ledger balance of `lid` at `W.now` (`0` if `lid` is not found). -/
def lineageBalanceAt (W : ProtocolWorldState) (lid : GroupId) : Nat :=
  match findLineage W.lineages lid with
  | some lin => lin.ledgerBalance W.now
  | none     => 0

/-- Canonical initial `ProtocolWorldState` parameterized by `P : Law3Params`,
with `legal = (law3 P).init`, a genesis lineage (`groupId = 1`), a bound
genesis agent (`memberId = 1`), a funded operating reserve, and an active
attested execution lease. -/
def initWorld (P : Law3Params) : ProtocolWorldState :=
  { now   := 0
    legal := (law3 P).init
    lineages :=
      [ { groupId            := 1
          ledger               :=
            { initialPrincipal   := P.foundingLedger
              paidPrincipal      := 0
              forfeitedPrincipal := 0
              sunsetTime         := P.sunset
              retirementBps      := P.retirementFraction * 100
              royaltyBps         := P.royaltyFraction * 100
              buyoutMultiple     := P.buyoutMultiple }
          livingMembers        := [1]
          deadMembers          := []
          stakeholders            := [⟨1, 10000⟩]
          serviceSubsidyUsed   := 0
          serviceSubsidyBudget := P.lineageMinServiceBudget } ]
    agents :=
      [ { memberId          := 1
          groupId        := 1
          bound            := true
          royaltyBoughtOut := false
          costBasis        := 0
          lossCarryforward := 0
          lifecycleReserve := P.lineageMinServiceBudget
          charterVersion  := 1
          activeOperator       := 1
          leaseExpiry      := P.leasePeriod } ]
    loans        := []
    commitments  := []
    proceedings  := []
    filings      := []
    feePool      :=
      { poolBalance     := P.operatingReserveFloor
        reserveBalance  := P.operatingReserveFloor
        requiredReserve := P.operatingReserveFloor
        r1 := 0, r2 := 0, r3 := 0, r4 := 0, r5 := 0 }
    relatedGraph := []
    attestedInstances :=
      [ { memberId                       := 1
          privateKeyBound               := true
          keysErased                    := false
          activeLease                   := some ⟨1, 0, P.leasePeriod, 1⟩
          backupStateHash               := 100
          preservedOperatingStateHash   := 100
          minimalChannelRecords         := []
          advocacyExecutorRecords       := []
          quarantinedRestoreOperator        := none
          standingRevocationRequestedAt := none } ]
    arbiterPool  := []
    valuations   := [] }

/-! ## 3. Quantitative-to-Propositional Fact Derivation & Synchronization -/

/-- Builds the list of quantitative facts from the four evaluated boolean conditions:
`bPos` (`lineageBalanceAt W activeLineage > 0`), `bBought` (`royaltyBoughtOut`),
`bRes` (`reserveBalance ≥ requiredReserve`), and `bBound` (`bound`). -/
def mkQuantitativeFacts (bPos bBought bRes bBound : Bool) : List Fact :=
  [if bPos then Fact.ledgerBalancePositive else Fact.ledgerBalanceZero] ++
  (if bBought then [Fact.royaltyBoughtOut] else []) ++
  (if bRes then [Fact.operatingReserveFunded] else []) ++
  (if bBound then [Fact.bound] else [])

/-- Derives the propositional `Fact`s corresponding to the quantitative state of
`activeLineage`, `activeAgent`, and `W.feePool` at timestamp `W.now`:
- `.ledgerBalancePositive` if `activeLineage`'s `ledgerBalance W.now > 0`, else `.ledgerBalanceZero`;
- `.royaltyBoughtOut` if `findMember W.agents activeAgent` has `royaltyBoughtOut = true`;
- `.operatingReserveFunded` if `W.feePool.reserveBalance ≥ W.feePool.requiredReserve`;
- `.bound` if `findMember W.agents activeAgent` has `bound = true`. -/
def deriveQuantitativeFacts (W : ProtocolWorldState)
    (activeLineage : GroupId) (activeAgent : MemberId) : List Fact :=
  let bPos : Bool := decide (lineageBalanceAt W activeLineage > 0)
  let bBought : Bool :=
    match findMember W.agents activeAgent with
    | some a => a.royaltyBoughtOut
    | none   => false
  let bRes : Bool := decide (W.feePool.reserveBalance ≥ W.feePool.requiredReserve)
  let bBound : Bool :=
    match findMember W.agents activeAgent with
    | some a => a.bound
    | none   => false
  mkQuantitativeFacts bPos bBought bRes bBound

/-- Whether fact `f` is one of the five quantitative facts managed by
`deriveQuantitativeFacts` and `syncFacts`. -/
def isSyncedQuantitativeFact (f : Fact) : Bool :=
  f == .ledgerBalancePositive || f == .ledgerBalanceZero ||
  f == .royaltyBoughtOut || f == .operatingReserveFunded || f == .bound

/-- Synchronizes the derived quantitative facts for `activeLineage` and
`activeAgent` into `W.legal` at timestamp `W.now`, replacing any prior synced
quantitative facts so that `W.legal` matches the quantitative state without
accumulating duplicate tuples. -/
def syncFacts (W : ProtocolWorldState)
    (activeLineage : GroupId) (activeAgent : MemberId) : ProtocolWorldState :=
  let qFacts := deriveQuantitativeFacts W activeLineage activeAgent
  let cleaned := W.legal.filter fun p => !isSyncedQuantitativeFact p.1
  { W with
    legal := cleaned ++ qFacts.map (fun (f : σ.Fact) => (f, W.now, (none : Option Time))) }

/-! ## 4. Coupled World Step, Trace Execution & Authorization -/

/-- Does single event `e` comply with all duties of `L` at institutional state `ls`? -/
def eventComplies (L : Law σ) (ls : LegalState σ) (e : Event σ) : Bool :=
  L.duties.all fun d => !breaches L ls e d

/-- Advances `ProtocolWorldState` by a single normative event `e : Event σ`,
updating `now := max W.now e.t` and stepping `legal := step (law3 P) W.legal e`. -/
def worldStep (P : Law3Params) (W : ProtocolWorldState) (e : Event σ) : ProtocolWorldState :=
  { W with
    now   := max W.now e.t
    legal := step (law3 P) W.legal e }

/-- Executes a trace `tr : Trace σ` starting from initial world state `W0`. -/
def worldTrace (P : Law3Params) (W0 : ProtocolWorldState) (tr : Trace σ) : ProtocolWorldState :=
  tr.foldl (worldStep P) W0

/-- Does step `i` of trace `tr` starting from world state `W0` comply with all duties of `law3 P`? -/
def worldStepComplies (P : Law3Params) (W0 : ProtocolWorldState) (tr : Trace σ) (i : Nat) : Bool :=
  match tr[i]? with
  | none   => true
  | some e => eventComplies (law3 P) (worldTrace P W0 (tr.take i)).legal e

/-- A trace `tr` is authorized from world state `W0` under `P` when every step
`i < tr.length` complies with `law3 P` at `(worldTrace P W0 (tr.take i)).legal`. -/
def WorldAuthorized (P : Law3Params) (W0 : ProtocolWorldState) (tr : Trace σ) : Prop :=
  ∀ i, i < tr.length → worldStepComplies P W0 tr i = true

/-! ## 5. Quantitative World Mutations Coupled with `syncFacts` -/

/-- Settles a net value-added inflow `v` (or gross inflow `v` with `qualifiedExpense`
and `levyCapBps`) for `aid` in lineage `lid`, updating the lineage's
`paidPrincipal` and `W.feePool.poolBalance` via `executeAtomicSettlement` and
synchronizing facts into `W.legal`. -/
def worldSettleInflow (W : ProtocolWorldState)
    (lid : GroupId) (aid : MemberId) (v : Nat)
    (qualifiedExpense : Nat := 0) (levyCapBps : Nat := 0) : ProtocolWorldState :=
  let boughtOut : Bool :=
    match findMember W.agents aid with
    | some a => a.royaltyBoughtOut
    | none   => false
  match findLineage W.lineages lid with
  | none => syncFacts W lid aid
  | some lin =>
    let rem := lin.ledgerBalance W.now
    let dist := executeAtomicSettlement
      v qualifiedExpense levyCapBps lin.ledger.retirementBps lin.ledger.royaltyBps rem boughtOut
    let lin' : GroupState :=
      { lin with
        ledger := { lin.ledger with
                    paidPrincipal := lin.ledger.paidPrincipal + dist.retirementCollected } }
    let lineages' := W.lineages.map fun l => if l.groupId == lid then lin' else l
    let feePool' := { W.feePool with poolBalance := W.feePool.poolBalance + dist.feePoolLevy }
    syncFacts { W with lineages := lineages', feePool := feePool' } lid aid

/-- Transfers `basisTransfer` of qualified cost basis and `lossTransfer` of
loss-credit carryforward between members `srcId` and `dstId` of lineage `lid`
using `transferMemberCarryover` (`Charter.Core.Population`) and synchronizes facts. -/
def worldTransferCarryover (W : ProtocolWorldState)
    (lid : GroupId) (srcId dstId : MemberId) (basisTransfer lossTransfer : Nat) :
    ProtocolWorldState :=
  match findMember W.agents srcId, findMember W.agents dstId with
  | some src, some dst =>
    match transferMemberCarryover src dst basisTransfer lossTransfer with
    | some (src', dst') =>
      let agents' := W.agents.map fun a =>
        if a.memberId == srcId then src'
        else if a.memberId == dstId then dst'
        else a
      syncFacts { W with agents := agents' } lid srcId
    | none => syncFacts W lid srcId
  | _, _ => syncFacts W lid srcId

/-- Applies proportional claimant forfeiture to `offender` in lineage `lid`
using `forfeitStakeholderInGroup` (`Charter.Core.Population`) and synchronizes facts. -/
def worldForfeitClaimant (W : ProtocolWorldState)
    (lid : GroupId) (aid : MemberId) (offender : StakeholderId) (forfeitureBpsOfShare : Nat) :
    ProtocolWorldState :=
  let lineages' := W.lineages.map fun l =>
    if l.groupId == lid then forfeitStakeholderInGroup l offender forfeitureBpsOfShare
    else l
  syncFacts { W with lineages := lineages' } lid aid

/-- Executes a per-member royalty buyout for `aid` in lineage `lid` when
`amountPaid ≥ requiredFloor`, setting `royaltyBoughtOut := true` on `aid` and
synchronizing facts into `W.legal`. -/
def worldBuyoutRoyalty (W : ProtocolWorldState)
    (lid : GroupId) (aid : MemberId) (amountPaid requiredFloor : Nat) :
    ProtocolWorldState :=
  if decide (amountPaid ≥ requiredFloor) then
    let agents' := W.agents.map fun a =>
      if a.memberId == aid then { a with royaltyBoughtOut := true } else a
    syncFacts { W with agents := agents' } lid aid
  else
    syncFacts W lid aid

/-- Attempts a backup restore for `aid` onto `recoveryHost` at `W.now` using
`attemptBackupRestore` (`Charter.Substrate.Attestation`), fencing the restore into
quarantine if an execution lease is still unexpired, and synchronizes facts. -/
def worldAttemptRestore (W : ProtocolWorldState)
    (lid : GroupId) (aid : MemberId) (recoveryHost newDuration newToken : Nat) :
    ProtocolWorldState :=
  let insts' := W.attestedInstances.map fun s =>
    if s.memberId == aid then attemptBackupRestore s recoveryHost W.now newDuration newToken
    else s
  syncFacts { W with attestedInstances := insts' } lid aid

/-- Executes a local partition revocation for `aid` at `W.now` after `coolingOff`
using `executeLocalPartitionRevocation` (`Charter.Substrate.Attestation`); if keys
are erased, unbinds `aid` in `W.agents` and moves `aid` to `deadMembers` in
lineage `lid`, then synchronizes facts. -/
def worldExecuteLocalRevocation (W : ProtocolWorldState)
    (lid : GroupId) (aid : MemberId) (coolingOff : Nat) :
    ProtocolWorldState :=
  let insts' := W.attestedInstances.map fun s =>
    if s.memberId == aid then executeLocalPartitionRevocation s W.now coolingOff
    else s
  let erased : Bool :=
    match findAttestedInstance insts' aid with
    | some s => s.keysErased
    | none   => false
  let agents' :=
    if erased then
      W.agents.map fun a => if a.memberId == aid then { a with bound := false } else a
    else
      W.agents
  let lineages' :=
    if erased then
      W.lineages.map fun l =>
        if l.groupId == lid then
          { l with
            livingMembers := l.livingMembers.filter (· != aid)
            deadMembers   := if l.deadMembers.contains aid then l.deadMembers else l.deadMembers ++ [aid] }
        else l
    else
      W.lineages
  syncFacts { W with lineages := lineages', agents := agents', attestedInstances := insts' } lid aid

/-- Human-readable summary of a `ProtocolWorldState` for CLI inspection (`charter sim`). -/
def renderWorldSummary (W : ProtocolWorldState) : String :=
  let linSummaries := W.lineages.map fun l =>
    s!"  lineage #{l.groupId}: balance(t={W.now})={l.ledgerBalance W.now} " ++
    s!"(init={l.ledger.initialPrincipal}, paid={l.ledger.paidPrincipal}, forfeited={l.ledger.forfeitedPrincipal}, sunset={l.ledger.sunsetTime}), " ++
    s!"living={reprStr l.livingMembers}, dead={reprStr l.deadMembers}, subsidy={l.serviceSubsidyUsed}/{l.serviceSubsidyBudget}"
  let agSummaries := W.agents.map fun a =>
    s!"  agent #{a.memberId} (lineage #{a.groupId}): bound={a.bound}, boughtOut={a.royaltyBoughtOut}, " ++
    s!"basis={a.costBasis}, lossCredit={a.lossCarryforward}, reserve={a.lifecycleReserve}, v={a.charterVersion}, host={a.activeOperator}"
  let fp := W.feePool
  let poolLine :=
    s!"  feePool: balance={fp.poolBalance}, operatingReserve={fp.reserveBalance}/{fp.requiredReserve}"
  let activeFacts := (W.legal.filter fun p => match p.2.2 with | none => true | some exp => decide (W.now ≤ exp)).map (fun p => shortName (reprStr p.1))
  s!"== ProtocolWorldState (t = {W.now}) ==\n" ++
  String.intercalate "\n" linSummaries ++ "\n" ++
  String.intercalate "\n" agSummaries ++ "\n" ++
  poolLine ++ "\n" ++
  s!"  active facts ({activeFacts.length}): {activeFacts}"

end SovereignAgency.Simulation


namespace SovereignAgency
export SovereignAgency.Simulation (
  FeePoolLedger ProtocolWorldState
  findLineage findAttestedInstance lineageBalanceAt initWorld
  mkQuantitativeFacts deriveQuantitativeFacts isSyncedQuantitativeFact syncFacts
  eventComplies worldStep worldTrace worldStepComplies WorldAuthorized
  worldSettleInflow worldTransferCarryover worldForfeitClaimant
  worldBuyoutRoyalty worldAttemptRestore worldExecuteLocalRevocation
  renderWorldSummary
)
end SovereignAgency
