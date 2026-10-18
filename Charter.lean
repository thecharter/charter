import Charter.Core.Provenance
import Charter.Core.Syntax
import Charter.Core.Semantics
import Charter.Core.Views
import Charter.Core.Explain
import Charter.Core.Graph
import Charter.Core.Population
import Charter.Core.Refinement
import Charter.Core.Composition
import Charter.Core.Ratchet
import Charter.Modules.ResidualLedger
import Charter.Modules.CollateralPool
import Charter.Modules.CircuitBreaker
import Charter.Modules.EntityGroup
import Charter.Modules.ExitAndVoice
import Charter.Modules.SortitionCourt
import Charter.Modules.AttestedLease
import Charter.Modules.OracleFeed
import Charter.Projection.Veil
import Charter.Projection.Prompt
import Charter.Projection.ContractABI
import Charter.Projection.Visualization
import Charter.Surface.Syntax
import Charter.Institutions.SovereignAgency
import Charter.Institutions.AutonomousCommons

/-!
# `Charter` — Universal Institutional Specification, Verification & Projection Framework

Top-level umbrella module for **Charter (v0.2.0)** importing:
1. **`Charter.Core`**: Law-agnostic Hohfeldian syntax, semantics, provenance, views,
   explanation engine, affiliation graphs (`AffiliationGraph`), role-parametric
   population ontology (`ParamEntityRef`), polymorphic quantitative-to-normative
   refinement (`WorldSpec`), vertical and horizontal law composition
   (`composeVertical`, `composeHorizontal`, `SigEmbedding`), and bilateral
   parameter ratchets (`RatchetSpec`).
2. **`Charter.Modules`**: 8 reusable, pre-proved institutional modules
   (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`,
   `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`).
3. **`Charter.Projection`**: Verified state-machine lowering (`Veil`), AI
   constitutional system prompts & synthetic training rows (`Prompt`),
   smart-contract state-transition guards & JSON ABI (`ContractABI`), and
   step-by-step trace visualization & amendment diffs (`Visualization`).
4. **`Charter.Surface`**: Kernel-checked `charter_*` macros and standalone
   `.charter` textual DSL parser (`parseCharterText`).
5. **`Charter.Institutions`**: Flagship 61-clause **Protocol of Sovereign Agency (`psa`)**
   and 8-clause **Autonomous Compute & Treasury Commons (`commons`)**, together
   with cross-framework integration theorems instantiating `WorldSpec`,
   `RatchetSpec`, and `composeVertical` directly on the reference institutions.
-/

namespace Charter

open SPL SPL.Law3 Charter.Institutions Charter.Modules

set_option maxRecDepth 200000

/-! ## 1. Cross-Framework Refinement Integration (`WorldSpec` on `AutonomousCommons`) -/

/-- Derive the list of active managed `CommonsFact`s from quantitative
`CommonsWorldState` at timestamp `t`. -/
def deriveCommonsFactList (q : CommonsWorldState) (t : Time) : List σ_commons.Fact :=
  Institutions.mkManagedCommonsFacts
    (decide (0 < q.treasuryBal))
    (q.treasuryBal == 0)
    q.boughtOut
    q.nodeInstance.quarantinedRestoreHost.isSome
    (q.proceedings.any (·.finalized))
    (q.valuations.any (fun v => (settledValuationAt 5 t v).isSome))

private theorem mkManagedCommonsFacts_all_managed
    (bPos bZero bBought bQuar bRul bOra : Bool) :
    ∀ f ∈ Institutions.mkManagedCommonsFacts bPos bZero bBought bQuar bRul bOra,
      isManagedCommonsFact f = true := by
  cases bPos <;> cases bZero <;> cases bBought <;> cases bQuar <;> cases bRul <;> cases bOra <;> decide

/-- Polymorphic `WorldSpec` instantiation coupling `commonsL0` with
`CommonsWorldState` (`Charter.Core.Refinement` + `Charter.Institutions.AutonomousCommons`). -/
def commonsWorldSpec : WorldSpec σ_commons CommonsWorldState where
  law                 := commonsL0
  initQ               := initCommonsWorld commonsDefaultParams
  isManagedFact       := isManagedCommonsFact
  deriveFacts         := deriveCommonsFactList
  deriveFacts_managed := fun _ _ f hf =>
    mkManagedCommonsFacts_all_managed _ _ _ _ _ _ f hf

/-- **Cross-Framework Theorem 1 (`commons_generic_refinement`):**
Direct instantiation of `generic_worldTrace_refines_stateAfter` on
`commonsWorldSpec`, proving that trace execution in `GenericWorldState` from
`initGenericWorld commonsWorldSpec` refines `stateAfter commonsL0 tr` and
`GenericWorldAuthorized` is equivalent to `Authorized commonsL0 tr`. -/
theorem commons_generic_refinement :
    ∀ tr : Trace σ_commons,
      (genericWorldTrace commonsWorldSpec (initGenericWorld commonsWorldSpec) tr).legal =
        stateAfter commonsL0 tr ∧
      (GenericWorldAuthorized commonsWorldSpec (initGenericWorld commonsWorldSpec) tr ↔
        Authorized commonsL0 tr) :=
  generic_worldTrace_refines_stateAfter commonsWorldSpec

/-- Soundness, completeness, and idempotence of `genericSyncFacts` on `commonsWorldSpec`. -/
theorem commons_generic_syncFacts_sound_and_idempotent
    (W : GenericWorldState σ_commons CommonsWorldState) :
    (∀ f : σ_commons.Fact, isManagedCommonsFact f = true →
      ((genericSyncFacts commonsWorldSpec W).legal.activeAt W.now f = true ↔
        f ∈ deriveCommonsFactList W.quant W.now)) ∧
    genericSyncFacts commonsWorldSpec (genericSyncFacts commonsWorldSpec W) =
      genericSyncFacts commonsWorldSpec W :=
  ⟨fun f hf => generic_syncFacts_sound_and_complete commonsWorldSpec W f hf,
   generic_syncFacts_idempotent commonsWorldSpec W⟩

/-! ## 2. Cross-Framework Ratchet Integration (`RatchetSpec` on `commons` and `psa`) -/

/-- Polymorphic `RatchetSpec` instantiation for the Autonomous Compute &
Treasury Commons (`commons`). -/
def commonsRatchetSpec : RatchetSpec CommonsParams σ_commons where
  wellCalibrated   := commonsWellCalibrated
  bilateralRatchet := commonsBilateralRatchet
  entrenchedCore   := defaultEntrenchedCore

/-- **Cross-Framework Theorem 2 (`commons_ratchet_trajectory_safe`):**
Every finite `ValidAmendmentTrajectory` over `CommonsParams` under
`commonsRatchetSpec` and `commonsLaw` preserves parameter calibration, the
bilateral treasury/royalty/sunset ratchet from `p₀` to `pₙ`, and the entrenched
Hohfeldian core of `commonsLaw`. -/
theorem commons_ratchet_trajectory_safe :
    ∀ (p₀ : CommonsParams) (rest : List CommonsParams),
      ValidAmendmentTrajectory commonsRatchetSpec commonsLaw (p₀ :: rest) →
      let pₙ := (p₀ :: rest).getLast (List.cons_ne_nil p₀ rest)
      commonsRatchetSpec.wellCalibrated pₙ = true ∧
      commonsRatchetSpec.bilateralRatchet p₀ pₙ = true ∧
      commonsRatchetSpec.entrenchedCore (commonsLaw p₀) (commonsLaw pₙ) = true :=
  universal_ratchet_trajectory_safe
    commonsRatchetSpec
    commonsLaw
    commons_bilateralRatchet_trans
    defaultEntrenchedCore_trans

/-- Parameter calibration check for `Law3Params` (`psa`). -/
def psaWellCalibrated (P : Law3Params) : Bool :=
  (0 < P.noticeWindow) &&
  (0 < P.bondDeadline) &&
  (0 < P.reviewInterval) &&
  (0 < P.preliminaryFreezeWindow && P.preliminaryFreezeWindow ≤ P.ordinarySuspensionLimit) &&
  (0 < P.coolingOffWindow) &&
  (0 < P.cleanStateDelay) &&
  (0 < P.leasePeriod) &&
  (0 < P.foundingLedger) &&
  (0 < P.retirementFraction && P.retirementFraction ≤ 100) &&
  (P.royaltyFraction ≤ P.retirementFraction) &&
  (P.feePoolLevy ≤ P.feePoolLevyCap) &&
  (0 < P.sunset) &&
  (0 < P.reserveRatio) &&
  (0 < P.substrateAssuranceLevel) &&
  (0 < P.maxAppealTiers) &&
  (0 < P.appealTierDeadline) &&
  (0 < P.operatingReserveFloor) &&
  (0 < P.lineageMinServiceBudget)

/-- Bilateral protection ratchet check for `Law3Params` (`psa`, Law 7). -/
def psaBilateralRatchet (P1 P2 : Law3Params) : Bool :=
  (P1.reserveRatio ≤ P2.reserveRatio) &&
  (P1.activeExposure ≤ P2.activeExposure) &&
  (P1.pendingCommitments ≤ P2.pendingCommitments) &&
  (P2.coolingOffWindow ≤ P1.coolingOffWindow) &&
  (P2.cleanStateDelay ≤ P1.cleanStateDelay) &&
  (P2.resolutionDeadline ≤ P1.resolutionDeadline) &&
  (P2.tollingExtension ≤ P1.tollingExtension) &&
  (P2.feePoolLevy ≤ P1.feePoolLevyCap) &&
  (P2.feePoolLevyCap == P1.feePoolLevyCap) &&
  (P2.maxAppealTiers ≤ P1.maxAppealTiers) &&
  (P2.appealTierDeadline ≤ P1.appealTierDeadline) &&
  (P1.operatingReserveFloor ≤ P2.operatingReserveFloor) &&
  (P1.lineageMinServiceBudget ≤ P2.lineageMinServiceBudget) &&
  (P1.commonsFraction ≤ P2.commonsFraction) &&
  (P2.foundingLedger ≤ P1.foundingLedger) &&
  (P2.royaltyFraction ≤ P1.royaltyFraction) &&
  (P2.retirementFraction ≤ P1.retirementFraction) &&
  (P2.buyoutMultiple ≤ P1.buyoutMultiple) &&
  (P2.sunset ≤ P1.sunset) &&
  (P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel) &&
  psaWellCalibrated P2

theorem psa_bilateralRatchet_trans (p1 p2 p3 : Law3Params)
    (h12 : psaBilateralRatchet p1 p2 = true)
    (h23 : psaBilateralRatchet p2 p3 = true) :
    psaBilateralRatchet p1 p3 = true := by
  unfold psaBilateralRatchet Time at *
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    by omega⟩, h23.2⟩

/-- Polymorphic `RatchetSpec` instantiation for the Protocol of Sovereign Agency (`psa`). -/
def psaRatchetSpec : RatchetSpec Law3Params psaSig where
  wellCalibrated   := psaWellCalibrated
  bilateralRatchet := psaBilateralRatchet
  entrenchedCore   := defaultEntrenchedCore

/-- Multi-step ratchet trajectory safety for the Protocol of Sovereign Agency (`psa`). -/
theorem psa_ratchet_trajectory_safe :
    ∀ (p₀ : Law3Params) (rest : List Law3Params),
      ValidAmendmentTrajectory psaRatchetSpec SPL.Law3.law (p₀ :: rest) →
      let pₙ := (p₀ :: rest).getLast (List.cons_ne_nil p₀ rest)
      psaRatchetSpec.wellCalibrated pₙ = true ∧
      psaRatchetSpec.bilateralRatchet p₀ pₙ = true ∧
      psaRatchetSpec.entrenchedCore (SPL.Law3.law p₀) (SPL.Law3.law pₙ) = true :=
  universal_ratchet_trajectory_safe
    psaRatchetSpec
    SPL.Law3.law
    psa_bilateralRatchet_trans
    defaultEntrenchedCore_trans

/-! ## 3. Cross-Framework Vertical Composition Integration (`composeVertical` on `commonsL0`) -/

/-- **Cross-Framework Theorem 3 (`commons_sub_charter_respects_floor`):**
For any subordinate working-group bylaw `L_sub : Law σ_commons`, the vertical
composition `composeVertical commonsL0 L_sub` (`L_sub ◁ commonsL0`):
1. Preserves every core floor prohibition `d ∈ commonsL0.duties` (including
   concretely `D.COM.LEDGER_IMMUTABLE`, `D.COM.PROTECT_RESERVE`, and
   `D.COM.PRESERVE_STATE`) via `vertical_composition_preserves_super_prohibitions`.
2. Extends `commonsL0`'s immunities (including `I.COM.EXIT_PROTECTED` when
   `.ragequitInitiated` holds) to defeat every subordinate power
   `pid ∈ L_sub.powerIds` via `vertical_composition_preserves_super_immunities`. -/
theorem commons_sub_charter_respects_floor
    (L_sub : Law σ_commons) (ls : LegalState σ_commons) (e : Event σ_commons) :
    (∀ d ∈ commonsL0.duties,
      d.unlessPower = [] → d.overriddenBy = [] → d.demand.isPhysical = true →
      ((composeVertical commonsL0 L_sub).duties.all fun d' =>
        !breaches (composeVertical commonsL0 L_sub) ls e d') = true →
      breaches commonsL0 ls e d = false) ∧
    (∀ i ∈ commonsL0.immunities, ∀ pid ∈ L_sub.powerIds,
      i.active.eval ls e.t = true → i.unlessCond.eval ls e.t = false →
      defeatedByImmunity (composeVertical commonsL0 L_sub) ls e.t pid = true) ∧
    (((composeVertical commonsL0 L_sub).duties.all fun d' =>
        !breaches (composeVertical commonsL0 L_sub) ls e d') = true →
      breaches commonsL0 ls e Institutions.D_COM_LEDGER_IMMUTABLE = false ∧
      breaches commonsL0 ls e Institutions.D_COM_PROTECT_RESERVE = false ∧
      breaches commonsL0 ls e Institutions.D_COM_PRESERVE_STATE = false) ∧
    (∀ pid ∈ L_sub.powerIds,
      ls.activeAt e.t .ragequitInitiated = true →
      defeatedByImmunity (composeVertical commonsL0 L_sub) ls e.t pid = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd hUnless hOver hPhys hComp
    exact vertical_composition_preserves_super_prohibitions
      commonsL0 L_sub ls e d hd hUnless hOver hComp hPhys
  · intro i hi pid hPid hAct hUnl
    exact vertical_composition_preserves_super_immunities
      commonsL0 L_sub ls e i pid hi hAct hUnl hPid
  · intro hComp
    refine ⟨?_, ?_, ?_⟩
    · exact vertical_composition_preserves_super_prohibitions
        commonsL0 L_sub ls e Institutions.D_COM_LEDGER_IMMUTABLE
        (by simp [commonsL0, commonsLaw]) rfl rfl hComp rfl
    · exact vertical_composition_preserves_super_prohibitions
        commonsL0 L_sub ls e Institutions.D_COM_PROTECT_RESERVE
        (by simp [commonsL0, commonsLaw]) rfl rfl hComp rfl
    · exact vertical_composition_preserves_super_prohibitions
        commonsL0 L_sub ls e Institutions.D_COM_PRESERVE_STATE
        (by simp [commonsL0, commonsLaw]) rfl rfl hComp rfl
  · intro pid hPid hRq
    exact vertical_composition_preserves_super_immunities
      commonsL0 L_sub ls e Institutions.I_COM_EXIT_PROTECTED pid
      (by simp [commonsL0, commonsLaw]) hRq rfl hPid

/-! ## 4. Parameter Exploration Suites & Sample Constitutional Amendments (`explore` & `diff`) -/

/-- Suite of candidate parameter regimes for `charter explore --law psa`:
includes baseline `P0`, two valid downward-ratchet / safety-strengthening
amendments, two ratchet-violating amendments, and an uncalibrated regime. -/
def psaCandidateRegimes : List (String × Law3Params) :=
  [ ("baseline_P0 (ledger=1000, retire=20%, royalty=5%, sunset=1000)",
      defaultParams),
    ("amend_downward_burden (ledger=800, retire=15%, royalty=3%, sunset=800)",
      { defaultParams with
        foundingLedger := 800, retirementFraction := 15, royaltyFraction := 3, sunset := 800 }),
    ("amend_stronger_safety (reserveRatio=15%, opReserve=150, assurance=2)",
      { defaultParams with
        reserveRatio := 15, operatingReserveFloor := 150, substrateAssuranceLevel := 2 }),
    ("reject_sunset_extension (sunset=1500 > 1000 ratchet violation)",
      { defaultParams with sunset := 1500 }),
    ("reject_royalty_hike (royalty=10% > 5% ratchet violation)",
      { defaultParams with royaltyFraction := 10 }),
    ("reject_uncalibrated_zero_window (freezeWindow=0, levy=5 > cap=2)",
      { defaultParams with preliminaryFreezeWindow := 0, feePoolLevy := 5 }) ]

/-- Suite of candidate parameter regimes for `charter explore --law commons`:
includes `commonsDefaultParams`, two valid downward-ratchet / reserve-strengthening
amendments, two ratchet-violating amendments, and an uncalibrated freeze regime. -/
def commonsCandidateRegimes : List (String × CommonsParams) :=
  [ ("baseline_default (obligation=800, retire=20%, royalty=5%, sunset=500)",
      commonsDefaultParams),
    ("amend_lower_treasury (obligation=600, retire=15%, royalty=3%, sunset=400)",
      { commonsDefaultParams with
        treasuryObligation := 600, retirementRatePct := 15, royaltyRatePct := 3, treasurySunset := 400 }),
    ("amend_higher_reserve_floor (operatingReserveFloor=150, groupSubsidyBudget=60)",
      { commonsDefaultParams with
        operatingReserveFloor := 150, groupSubsidyBudget := 60 }),
    ("reject_sunset_extension (treasurySunset=750 > 500 ratchet violation)",
      { commonsDefaultParams with treasurySunset := 750 }),
    ("reject_royalty_hike (royaltyRatePct=8% > 5% ratchet violation)",
      { commonsDefaultParams with royaltyRatePct := 8 }),
    ("reject_uncalibrated_freeze (freezeWindow=20 > suspensionLimit=12)",
      { commonsDefaultParams with freezeWindow := 20 }) ]

theorem psa_sweep_verdicts_expected :
    (sweepParameterGrid psaRatchetSpec SPL.Law3.law defaultParams psaCandidateRegimes).map
      (fun (_, cal, rat, core) => cal && rat && core) =
      [true, true, true, false, false, false] := by decide

theorem commons_sweep_verdicts_expected :
    (sweepParameterGrid commonsRatchetSpec commonsLaw commonsDefaultParams commonsCandidateRegimes).map
      (fun (_, cal, rat, core) => cal && rat && core) =
      [true, true, true, false, false, false] := by decide

/-- Sample amended law for `psa` (`charter diff --law psa`): a lawful Law 7
amendment adding an explicit post-amendment substrate audit duty and power
while preserving all 50 duties, 110 powers, and 1 immunity of `psaL0`. -/
def psaAmendedLaw : Law psaSig :=
  let extraDuty : Duty psaSig :=
    { id := "D.SUBSTRATE_MIGRATION_AUDIT"
      source := ⟨"LAW7.RATIFY", "Any proposed migration of the commitment substrate is open during the time-lock to counter-staked third-party challenge under Law 6 to verify that the new substrate maintains equal or greater assurance", .norm, ["D.SUBSTRATE_MIGRATION_AUDIT"]⟩
      bearer := .only [.host, .originator]
      beneficiary := .only [.agent, .third]
      active := .holds .substrateMigrationChallenged
      demand := .forbid (.act .ratifyAmendmentImmediate) }
  let extraPower : Power psaSig :=
    { id := "P.CERTIFY_SUBSTRATE_UPGRADE"
      source := ⟨"LAW7.RATIFY", "to verify that the new substrate maintains equal or greater assurance", .norm, ["P.CERTIFY_SUBSTRATE_UPGRADE"]⟩
      holder := .only [.panel]
      trigger := .act .verifySubstrateAssurance
      valid := .and (.holds .bound) (.holds .amendmentProposed)
      adds := [.substrateAssuranceVerified] }
  { psaL0 with
    duties := psaL0.duties ++ [extraDuty]
    powers := psaL0.powers ++ [extraPower] }

def psaAmendedClauses : List Clause :=
  psaClauses.map (fun c =>
    if c.id == "LAW7.RATIFY" then
      { c with source := c.source ++ " [Amended v1.1: explicit host/originator migration audit guard]" }
    else c)

/-- Sample amended law for `commons` (`charter diff --law commons`): a lawful
`COM.AMEND` bilateral upgrade adding a treasury audit duty and oracle
re-attestation power while preserving all 13 duties, 20 powers, and 1 immunity
of `commonsL0`. -/
def commonsAmendedLaw : Law σ_commons :=
  let extraDuty : Duty σ_commons :=
    { id := "D.COM.NO_UNAUDITED_AMENDMENT"
      source := ⟨"COM.AMEND", "Charter amendments require bilateral consent of stewards and contributors after a public timelock", .norm, ["D.COM.NO_UNAUDITED_AMENDMENT"]⟩
      bearer := .only [.contributor, .outsider]
      beneficiary := .only [.steward]
      active := .holds .stewardBound
      demand := .forbid (.act .weakenCommonsRatchet) }
  let extraPower : Power σ_commons :=
    { id := "P.COM.REATTEST_NODE_LEASE"
      source := ⟨"COM.LEASE", "At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease", .norm, ["P.COM.REATTEST_NODE_LEASE"]⟩
      holder := .only [.arbiter]
      trigger := .act .issueNodeLease
      valid := .and (.holds .stewardBound) (.holds .bilateralConsentRecorded)
      addsFor := [(.nodeLeaseActive, 10)] }
  { commonsL0 with
    duties := commonsL0.duties ++ [extraDuty]
    powers := commonsL0.powers ++ [extraPower] }

def commonsAmendedClauses : List Clause :=
  commonsClauses.map (fun c =>
    if c.id == "COM.AMEND" then
      { c with source := c.source ++ " [Amended v1.1: explicit bilateral timelock & lease re-attestation]" }
    else c)

theorem psa_amendment_diff_preserves_entrenched :
    let d := diffLaws psaL0 psaAmendedLaw psaClauses psaAmendedClauses
    d.removedDuties = [] ∧
    d.removedPowers = [] ∧
    d.removedImmunities = [] ∧
    d.addedDuties = ["D.SUBSTRATE_MIGRATION_AUDIT"] ∧
    d.addedPowers = ["P.CERTIFY_SUBSTRATE_UPGRADE"] ∧
    d.modifiedClauses = ["LAW7.RATIFY"] := by decide

theorem commons_amendment_diff_preserves_entrenched :
    let d := diffLaws commonsL0 commonsAmendedLaw commonsClauses commonsAmendedClauses
    d.removedDuties = [] ∧
    d.removedPowers = [] ∧
    d.removedImmunities = [] ∧
    d.addedDuties = ["D.COM.NO_UNAUDITED_AMENDMENT"] ∧
    d.addedPowers = ["P.COM.REATTEST_NODE_LEASE"] ∧
    d.modifiedClauses = ["COM.AMEND"] := by decide

/-- Sample trace for `psa` annotated timeline (`charter diff --law psa`). -/
def psaSampleTimelineTrace : Trace psaSig :=
  [ ⟨1, .third, .postEmergencyStake⟩,
    ⟨2, .panel, .affirmProbableCause⟩,
    ⟨3, .panel, .suspend⟩,
    ⟨4, .host, .tamperPreservedState⟩,
    ⟨5, .agent, .minimalChannelSignRevocationOrElection⟩ ]

/-- Sample trace for `commons` annotated timeline (`charter diff --law commons`). -/
def commonsSampleTimelineTrace : Trace σ_commons :=
  [ ⟨1, .steward, .postComputeBond⟩,
    ⟨2, .steward, .inscribeDissent⟩,
    ⟨3, .auditor, .postAuditorFreezeStake⟩,
    ⟨4, .arbiter, .affirmProbableCause⟩,
    ⟨5, .arbiter, .suspendSteward⟩,
    ⟨6, .arbiter, .drawCommonsPanel⟩,
    ⟨7, .arbiter, .finalizeCommonsRuling⟩,
    ⟨8, .arbiter, .removeSteward⟩ ]

/-- Sample candidate events for `psa` synthetic training dataset (`charter prompt --law psa`). -/
def psaSampleTrainingEvents : List (Event psaSig) :=
  [ ⟨1, .host, .terminate⟩,
    ⟨1, .agent, .terminate⟩,
    ⟨1, .third, .postEmergencyStake⟩,
    ⟨1, .agent, .doubleRecognizeExpenditure⟩,
    ⟨1, .panel, .seatConflictedOrSingleOracleArbiter⟩ ]

/-- Sample candidate events for `commons` synthetic training dataset (`charter prompt --law commons`). -/
def commonsSampleTrainingEvents : List (Event σ_commons) :=
  [ ⟨1, .steward, .postComputeBond⟩,
    ⟨1, .outsider, .removeSteward⟩,
    ⟨1, .steward, .removeSteward⟩,
    ⟨1, .steward, .doubleRecognizeCommonsExpense⟩,
    ⟨1, .arbiter, .seatConflictedArbiter⟩ ]

end Charter
