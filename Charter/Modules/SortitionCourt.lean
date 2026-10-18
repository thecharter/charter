import SPL.Core.Semantics
import SPL.Law6.Adjudication
import SPL.Substrate.Sortition
import SPL.Law3.Theorems


/-!
# Charter.Modules.SortitionCourt — Reusable Bonded Sortition, Appeals & Fee Waterfall Module

Extracts and generalizes Law 6 and Substrate 2 decentralized contestable
adjudication: Sybil-resistant bonded sortition (`selectSybilResistantPanel`,
`supermajorityPassed`), related-party case consolidation
(`consolidateRelatedFilings`), bounded appellate proceedings
(`stepProceeding`, `runProceeding`), and the 5-rank priority fee-pool
waterfall (`allocateFeePool`).
-/

namespace Charter.Modules

open SPL SPL.Law3 SPL.Substrate

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for a bonded sortition court and fee pool. -/
structure SortitionCourtConfig where
  minFidelityBond       : Nat  := 100
  panelSize             : Nat  := 3
  maxAppealTiers        : Nat  := 3
  appealTierDeadline    : Time := 10
  operatingReserveFloor : Nat  := 100
  minServiceBudget      : Nat  := 50
  instantiationLevyCap  : Nat  := 2
  deriving DecidableEq, Repr, Inhabited

export SPL.Substrate (
  ArbiterCandidate
  eligibleCandidate
  filterEligibleCandidates
  selectSortitionPanel
  supermajorityPassed
  dedupSybilClusters
  selectSybilResistantPanel
  sortition_panel_all_independent_and_bonded
  sortition_panel_bounded_size
  sortition_supermajority_blocks_minority_coalition
  sortition_sybil_resistant_panel_properties
  sortition_empty_panel_never_passes
  sortition_panel_independent_and_unbiased
)

export SPL.Law3 (
  totalAdjudicationBound
  ProceedingState
  stepProceeding
  initProceeding
  runProceeding
  FeePoolAllocation
  allocateFeePool
  lineageServiceBudget
  settleLineageSubsidyDemand
  validSharedInfraChange
  DisputeFiling
  consolidateRelatedFilings
)

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build an arbiter recusal & diversity duty over any signature `σ`. -/
def mkDutyArbiterRecusalAndDiversity {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor) (boundFact : σ.Fact) (seatConflictedAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act seatConflictedAct) }

/-- Build a finality bar on repeat proceedings over any signature `σ`. -/
def mkDutyFinalityNoRepeat {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor)
    (boundFact finalFact newEvidenceFact : σ.Fact) (repeatFilingAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .and (.holds boundFact) (.holds finalFact)
    demand := .forbid (.act repeatFilingAct)
    unlessCond := .holds newEvidenceFact }

/-- Build a prohibition on contingent arbiter fees over any signature `σ`. -/
def mkDutyNoContingentFees {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor) (boundFact : σ.Fact) (contingentFeeAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act contingentFeeAct) }

/-- Build a sortition panel drawing power over any signature `σ`. -/
def mkPowerDrawSortitionPanel {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact panelDrawnFact bondsPostedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [panelDrawnFact, bondsPostedFact] }

/-- Build an appeal power over any signature `σ`. -/
def mkPowerAppealRuling {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact finalFact appealedFact bondPostedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.not (.holds finalFact))
    adds := [appealedFact, bondPostedFact] }

/-- Build a ruling finalization power over any signature `σ`. -/
def mkPowerFinalizeRuling {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact finalFact appealedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [finalFact]
    removes := [appealedFact] }

/-- Build a fee-pool waterfall allocation power over any signature `σ`. -/
def mkPowerAllocateFeePool {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact reserveMaintainedFact poolAllocatedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [reserveMaintainedFact, poolAllocatedFact] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- Sybil-resistant sortition guarantees independence, minimum bond, panel-size
cap, and at most one seat per `sybilClusterId`. -/
theorem sortition_court_sybil_resistant_panel_properties
    (minBond sz clusterId : Nat) (cs : List ArbiterCandidate) :
    (∀ c ∈ selectSybilResistantPanel minBond sz cs,
      c.relatedToDispute = false ∧ c.bond ≥ minBond) ∧
    (selectSybilResistantPanel minBond sz cs).length ≤ sz ∧
    ((selectSybilResistantPanel minBond sz cs).filter
      (fun c => c.sybilClusterId == clusterId)).length ≤ 1 :=
  sortition_sybil_resistant_panel_properties minBond sz clusterId cs

/-- Related-party filing consolidation preserves the single existing
`counterStake` and `feeCap`, preventing litigation DoS from multiplying fees. -/
theorem sortition_court_consolidate_preserves_cap
    (isRel : Nat → Nat → Bool) (existing incoming merged : DisputeFiling)
    (h : consolidateRelatedFilings isRel existing incoming = some merged) :
    merged = existing ∧
    merged.counterStake = existing.counterStake ∧
    merged.feeCap = existing.feeCap := by
  unfold consolidateRelatedFilings at h
  split at h
  · injection h with hEq
    subst hEq
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- Each step of a tiered sortition proceeding increases `elapsedTime` by at
most `st.tierDeadline` (and leaves `elapsedTime` unchanged once finalized). -/
theorem sortition_court_step_proceeding_bounded
    (st : ProceedingState) (dt : Nat) (appeal : Bool) :
    (stepProceeding st dt appeal).elapsedTime ≤ st.elapsedTime + st.tierDeadline ∧
    (st.finalized = true → stepProceeding st dt appeal = st) := by
  refine ⟨?_, fun hFin => by simp [stepProceeding, hFin]⟩
  unfold stepProceeding
  have hMin : min dt st.tierDeadline ≤ st.tierDeadline := Nat.min_le_right _ _
  split
  · omega
  · split <;> dsimp <;> omega

/-- Strict 5-rank priority waterfall (`allocateFeePool`) funds the
non-divertible operating reserve first (`min poolBalance operatingReserve`) and
conserves 100% of `poolBalance` across the reserve, 5 ranked charges, and surplus. -/
theorem sortition_court_fee_pool_conserves_balance
    (poolBalance operatingReserve r1 r2 r3 r4 r5 : Nat) :
    let wf := allocateFeePool poolBalance operatingReserve r1 r2 r3 r4 r5
    wf.operatingReserveFunded = min poolBalance operatingReserve ∧
    wf.operatingReserveFunded + wf.rank1FinalHearingMinCh + wf.rank2ColdStorage +
      wf.rank3TestimonyVoice + wf.rank4ArbiterGuarantee + wf.rank5AdvocacyFunding +
      wf.unspentPoolSurplus = poolBalance := by
  dsimp [allocateFeePool]
  have h0 : min poolBalance operatingReserve ≤ poolBalance := Nat.min_le_left _ _
  have h1 : min (poolBalance - min poolBalance operatingReserve) r1 ≤
      poolBalance - min poolBalance operatingReserve := Nat.min_le_left _ _
  have h2 : min (poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1) r2 ≤
      poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 := Nat.min_le_left _ _
  have h3 : min (poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2) r3 ≤
      poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2 := Nat.min_le_left _ _
  have h4 : min (poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2) r3) r4 ≤
      poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2) r3 := Nat.min_le_left _ _
  have h5 : min (poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2) r3 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1 -
          min (poolBalance - min poolBalance operatingReserve -
            min (poolBalance - min poolBalance operatingReserve) r1) r2) r3) r4) r5 ≤
      poolBalance - min poolBalance operatingReserve -
      min (poolBalance - min poolBalance operatingReserve) r1 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1) r2 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2) r3 -
      min (poolBalance - min poolBalance operatingReserve -
        min (poolBalance - min poolBalance operatingReserve) r1 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1) r2 -
        min (poolBalance - min poolBalance operatingReserve -
          min (poolBalance - min poolBalance operatingReserve) r1 -
          min (poolBalance - min poolBalance operatingReserve -
            min (poolBalance - min poolBalance operatingReserve) r1) r2) r3) r4 := Nat.min_le_left _ _
  exact ⟨rfl, by omega⟩

/-- Multi-step bounded adjudication finality (`INV.12`): across any sequence of
tier decisions `steps : List (Nat × Bool)` starting from `initProceeding maxTiers tierDeadline`
(with `0 < maxTiers`), total elapsed time never exceeds
`totalAdjudicationBound maxTiers tierDeadline` (`maxTiers * tierDeadline`), and
whenever `maxTiers ≤ steps.length`, the proceeding reaches `finalized = true`. -/
theorem sortition_court_run_proceeding_bounded
    (maxTiers tierDeadline : Nat) (steps : List (Nat × Bool)) (hTiers : 0 < maxTiers) :
    (runProceeding (initProceeding maxTiers tierDeadline) steps).elapsedTime ≤
      totalAdjudicationBound maxTiers tierDeadline ∧
    (maxTiers ≤ steps.length →
      (runProceeding (initProceeding maxTiers tierDeadline) steps).finalized = true) := by
  have hRun := (runProceeding_bound (initProceeding maxTiers tierDeadline) steps).2 rfl hTiers
  dsimp [initProceeding, totalAdjudicationBound] at hRun ⊢
  exact ⟨by have := hRun.1; omega, fun hlen => hRun.2 (by omega)⟩

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `selectSybilResistantPanel`,
`supermajorityPassed`, `consolidateRelatedFilings`, `runProceeding`, and
`allocateFeePool`. -/
def sortitionCourtSelfTest : Bool :=
  let pool : List ArbiterCandidate :=
    [ ⟨1, 200, 10, true⟩,
      ⟨2, 50,  20, false⟩,
      ⟨3, 150, 30, false⟩,
      ⟨4, 180, 30, false⟩,
      ⟨5, 220, 40, false⟩,
      ⟨6, 160, 50, false⟩ ]
  let panel := selectSybilResistantPanel 100 3 pool
  let f1 : DisputeFiling := ⟨1, 10, 99, 50, 20⟩
  let f2 : DisputeFiling := ⟨2, 10, 99, 50, 20⟩
  let merged := consolidateRelatedFilings (fun a b => a == b) f1 f2
  let pFinal := runProceeding (initProceeding 3 10) [(8, true), (12, true), (9, true)]
  let wf := allocateFeePool 180 100 30 20 15 10 25
  (panel.map (·.arbiterId) == [3, 5, 6]) &&
  (!supermajorityPassed 1 3) &&
  supermajorityPassed 2 3 &&
  (merged == some f1) &&
  (pFinal.finalized && pFinal.currentTier == 2 && pFinal.elapsedTime == 27) &&
  (wf.operatingReserveFunded == 100 && wf.rank5AdvocacyFunding == 5 && wf.unspentPoolSurplus == 0)

theorem sortitionCourtSelfTest_passes : sortitionCourtSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  SortitionCourtConfig
  ArbiterCandidate
  eligibleCandidate
  filterEligibleCandidates
  selectSortitionPanel
  supermajorityPassed
  dedupSybilClusters
  selectSybilResistantPanel
  sortition_panel_all_independent_and_bonded
  sortition_panel_bounded_size
  sortition_supermajority_blocks_minority_coalition
  sortition_sybil_resistant_panel_properties
  sortition_empty_panel_never_passes
  sortition_panel_independent_and_unbiased
  totalAdjudicationBound
  ProceedingState
  stepProceeding
  initProceeding
  runProceeding
  FeePoolAllocation
  allocateFeePool
  lineageServiceBudget
  settleLineageSubsidyDemand
  validSharedInfraChange
  DisputeFiling
  consolidateRelatedFilings
  mkDutyArbiterRecusalAndDiversity
  mkDutyFinalityNoRepeat
  mkDutyNoContingentFees
  mkPowerDrawSortitionPanel
  mkPowerAppealRuling
  mkPowerFinalizeRuling
  mkPowerAllocateFeePool
  sortition_court_sybil_resistant_panel_properties
  sortition_court_consolidate_preserves_cap
  sortition_court_step_proceeding_bounded
  sortition_court_run_proceeding_bounded
  sortition_court_fee_pool_conserves_balance
  sortitionCourtSelfTest
  sortitionCourtSelfTest_passes
)
end Charter

