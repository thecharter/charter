import Charter.Core.Semantics
import Charter.Law2.Collateral

/-!
# Charter.Modules.CollateralPool — Reusable Harm-Scaled Bonding & Long-Tail Reserve Module

Extracts and generalizes Law 2 harm-scaled collateralized action, rolling
exposure window decay (`ExposureCommitment`, `activeRollingExposureAt`),
risk-scaled `observationWindow`, persistent long-tail liability reserves
(`settleLongTailReserve`), and anti-extortion mutual forfeit
(`settleMutualForfeit` / `computeMutualForfeit`) into a reusable module over
any signature `σ : Sig`.
-/

namespace Charter.Modules

open Charter Charter.Law3

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for a harm-scaled collateral and reserve pool. -/
structure CollateralPoolConfig where
  baseObservationWindow : Nat := 10
  reserveRatioPct       : Nat := 10
  mutualForfeitCapPct   : Nat := 50
  deriving DecidableEq, Repr, Inhabited

export Charter.Law3 (
  lineageAggregatedExposure
  collateralSufficient
  settleLongTailReserve
  computeMutualForfeit
  routeFrivolousClaimStake
  settleWrongfulSuspensionDamages
  ExposureCommitment
  activeRollingExposureAt
  observationWindow
)

/-- Settle a precommitted mutual forfeit between matching escrows `escrowA` and
`escrowB` capped at `capPct ≤ 100`, returning
`(forfeitFromEach, transferToPartyA, transferToPartyB, transferToClaimant)`. -/
abbrev settleMutualForfeit := computeMutualForfeit

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a collateral safety-limit prohibition duty over any signature `σ`. -/
def mkDutyCollateralLimit {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (boundFact : σ.Fact) (overExposureAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act overExposureAct) }

/-- Build a correlated risk-splitting prohibition duty over any signature `σ`. -/
def mkDutyNoSplitExposure {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (boundFact : σ.Fact) (splitRiskAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act splitRiskAct) }

/-- Build a mutual-forfeit anti-extortion bounds duty over any signature `σ`. -/
def mkDutyMutualForfeitBounds {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor) (boundFact : σ.Fact) (divertForfeitAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .holds boundFact
    demand := .forbid (.act divertForfeitAct) }

/-- Build an exposure-stake immobilization power over any signature `σ`. -/
def mkPowerImmobilizeStake {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact stakeImmobilizedFact reserveAccruedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [stakeImmobilizedFact, reserveAccruedFact] }

/-- Build a validated harm-claim settlement power over any signature `σ`. -/
def mkPowerSettleHarmClaim {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact claimFiledFact claimValidatedFact slashedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.holds claimFiledFact)
    adds := [claimValidatedFact, slashedFact]
    removes := [claimFiledFact] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- Rolling exposure commitment decays to `0` once its observation window
`c.startedAt + c.windowDuration` has elapsed (`c.startedAt + c.windowDuration < now`). -/
theorem collateral_pool_rolling_exposure_decays (now : Nat) (c : ExposureCommitment)
    (hExpired : c.startedAt + c.windowDuration < now) :
    c.activeAmountAt now = 0 := by
  unfold ExposureCommitment.activeAmountAt
  have hNotLe : ¬ (now ≤ c.startedAt + c.windowDuration) := by omega
  simp [hNotLe]

/-- While within the observation window (`now ≤ c.startedAt + c.windowDuration`),
an exposure commitment contributes its full `c.amount`. -/
theorem collateral_pool_rolling_exposure_active (now : Nat) (c : ExposureCommitment)
    (hActive : now ≤ c.startedAt + c.windowDuration) :
    c.activeAmountAt now = c.amount := by
  unfold ExposureCommitment.activeAmountAt
  simp [hActive]

/-- Pro-rata long-tail reserve settlement never disburses more than `reserve`
and conserves total validated claims (`paid1 + paid2 + unpaid = claim1 + claim2`). -/
theorem collateral_pool_long_tail_reserve_bounded (reserve claim1 claim2 : Nat) :
    let (paid1, paid2, unpaid) := settleLongTailReserve reserve claim1 claim2
    paid1 + paid2 ≤ reserve ∧
    paid1 + paid2 + unpaid = claim1 + claim2 := by
  dsimp [settleLongTailReserve]
  split
  · rename_i hLe
    omega
  · rename_i hGt
    have hDiv : (reserve * claim1) / max (claim1 + claim2) 1 ≤ reserve := by
      apply Nat.div_le_of_le_mul
      have hMax : claim1 ≤ max (claim1 + claim2) 1 := by omega
      calc
        reserve * claim1 ≤ reserve * max (claim1 + claim2) 1 := Nat.mul_le_mul_left reserve hMax
        _ = max (claim1 + claim2) 1 * reserve := Nat.mul_comm _ _
    omega

/-- Precommitted mutual forfeit transfers zero value to either counterparty or
to any residual claimant (`transferToPartyA = 0`, `transferToPartyB = 0`,
`transferToClaimant = 0`) and caps each party's forfeit at `min escrowA escrowB`. -/
theorem collateral_pool_mutual_forfeit_zero_extortion (escrowA escrowB capPct : Nat) :
    let (forfeitEach, toA, toB, toClaimant) := settleMutualForfeit escrowA escrowB capPct
    toA = 0 ∧
    toB = 0 ∧
    toClaimant = 0 ∧
    forfeitEach ≤ min escrowA escrowB := by
  dsimp [settleMutualForfeit, computeMutualForfeit]
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply Nat.div_le_of_le_mul
  have hCap : min capPct 100 ≤ 100 := Nat.min_le_right capPct 100
  calc
    min escrowA escrowB * min capPct 100 ≤ min escrowA escrowB * 100 :=
      Nat.mul_le_mul_left _ hCap
    _ = 100 * min escrowA escrowB := Nat.mul_comm _ _

/-- Frivolous-claim counter-stake routing yields zero profit to the agent or
claimant (`toClaimantOrAgentProfit = 0`), reimburses at most `verifiedDirectCosts`,
and conserves 100% of `counterStake`. -/
theorem collateral_pool_frivolous_stake_zero_profit (counterStake verifiedDirectCosts : Nat) :
    let (reimbursed, toCommons, profit) := routeFrivolousClaimStake counterStake verifiedDirectCosts
    profit = 0 ∧
    reimbursed ≤ verifiedDirectCosts ∧
    reimbursed + toCommons = counterStake := by
  dsimp [routeFrivolousClaimStake]
  have hLe : min counterStake verifiedDirectCosts ≤ counterStake := Nat.min_le_left _ _
  refine ⟨rfl, Nat.min_le_right _ _, by omega⟩

/-- Harm-scaled observation window is always at least `baseWindow`. -/
theorem collateral_pool_observation_window_ge_base (baseWindow dMult iMult : Nat) :
    baseWindow ≤ observationWindow baseWindow dMult iMult := by
  unfold observationWindow
  have h1 : baseWindow * 1 ≤ baseWindow * max 1 dMult :=
    Nat.mul_le_mul_left baseWindow (Nat.le_max_left 1 dMult)
  have h2 : (baseWindow * max 1 dMult) * 1 ≤ (baseWindow * max 1 dMult) * max 1 iMult :=
    Nat.mul_le_mul_left (baseWindow * max 1 dMult) (Nat.le_max_left 1 iMult)
  omega

private theorem foldl_add_acc (xs : List Nat) (acc : Nat) :
    xs.foldl (· + ·) acc = acc + xs.foldl (· + ·) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x tl ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + x), ih x]
    omega

/-- Solvency bound and correlated-exposure additivity (`LAW2.EXPOSURE` & `LAW2.AGGREGATE`):
1. `collateralSufficient xs stake ins cap = true` iff aggregated exposure is
   bounded by `stake + ins + cap`.
2. Dividing correlated risk across multiple sub-accounts or successors `xs ++ ys`
   strictly preserves total aggregated exposure (`lineageAggregatedExposure (xs ++ ys) =
   lineageAggregatedExposure xs + lineageAggregatedExposure ys`). -/
theorem collateral_pool_solvency_bound (xs ys : List Nat) (stake ins cap : Nat) :
    (collateralSufficient xs stake ins cap = true ↔
      lineageAggregatedExposure xs ≤ stake + ins + cap) ∧
    lineageAggregatedExposure (xs ++ ys) =
      lineageAggregatedExposure xs + lineageAggregatedExposure ys := by
  refine ⟨decide_eq_true_iff, ?_⟩
  unfold lineageAggregatedExposure
  rw [List.foldl_append, foldl_add_acc ys (xs.foldl (· + ·) 0)]

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `observationWindow`, `activeRollingExposureAt`,
`collateralSufficient`, `settleLongTailReserve`, and `settleMutualForfeit`. -/
def collateralPoolSelfTest : Bool :=
  let win := observationWindow 10 3 2
  let comms : List ExposureCommitment := [⟨60, 5, win⟩, ⟨40, 5, win⟩]
  let activeAt20 := activeRollingExposureAt 20 comms
  let activeAt100 := activeRollingExposureAt 100 comms
  let (p1, p2, unpaid) := settleLongTailReserve 100 80 80
  let (forfeitEach, toA, toB, toClaimant) := settleMutualForfeit 200 120 50
  (win == 60) &&
  (activeAt20 == 100) &&
  (activeAt100 == 0) &&
  collateralSufficient [60, 40] 80 10 10 &&
  (!collateralSufficient [60, 40] 50 10 10) &&
  (p1 == 50 && p2 == 50 && unpaid == 60) &&
  (forfeitEach == 60 && toA == 0 && toB == 0 && toClaimant == 0)

theorem collateralPoolSelfTest_passes : collateralPoolSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  CollateralPoolConfig
  lineageAggregatedExposure
  collateralSufficient
  settleLongTailReserve
  computeMutualForfeit
  settleMutualForfeit
  routeFrivolousClaimStake
  ExposureCommitment
  activeRollingExposureAt
  observationWindow
  mkDutyCollateralLimit
  mkDutyNoSplitExposure
  mkDutyMutualForfeitBounds
  mkPowerImmobilizeStake
  mkPowerSettleHarmClaim
  collateral_pool_rolling_exposure_decays
  collateral_pool_rolling_exposure_active
  collateral_pool_long_tail_reserve_bounded
  collateral_pool_mutual_forfeit_zero_extortion
  collateral_pool_frivolous_stake_zero_profit
  collateral_pool_observation_window_ge_base
  collateral_pool_solvency_bound
  collateralPoolSelfTest
  collateralPoolSelfTest_passes
)
end Charter

