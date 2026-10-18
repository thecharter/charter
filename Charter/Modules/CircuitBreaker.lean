import Charter.Core.Semantics
import Charter.Modules.CollateralPool

/-!
# Charter.Modules.CircuitBreaker — Reusable Two-Stage Emergency Pause & Remediation Module

Provides the law-agnostic two-stage emergency pause: scaled emergency
counter-stake, time-bounded preliminary freeze window, probable-cause
affirmation, claimant conflict-of-interest multiplier, repeat-attempt
escalation, isolated minimal & advocacy channels, time-limited investigative
renewal, wrongful-pause consequential liability, and notwithstanding immunity
against termination over objection over any signature `σ : Sig`.
-/

namespace Charter.Modules

open Charter

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Instantiation parameters for two-stage adjudicated suspension. -/
structure ASParams where
  preliminaryFreezeWindow : Time
  ordinarySuspensionLimit : Time
  damagesPaymentWindow    : Time
  activeExposure          : Nat := 100
  pendingCommitments      : Nat := 80
  claimantMultiplier      : Nat := 2
  repeatEscalationStep    : Nat := 50
  deriving DecidableEq, Repr, Inhabited

/-- Instantiation parameter for periodic remediation review. -/
structure RemediationParams where
  reviewInterval : Time
  deriving DecidableEq, Repr, Inhabited

/-- The required emergency counter-stake: scaled to the greater of active
bonded exposure and registered pending commitments, multiplied by the
elevated claimant multiplier for residual claimants, and rising with each
prior wrongful attempt. -/
def requiredEmergencyStake (P : ASParams) (isClaimant : Bool) (priorWrongful : Nat) : Nat :=
  let base := max P.activeExposure P.pendingCommitments
  let mult := if isClaimant then P.claimantMultiplier else 1
  base * mult + priorWrongful * P.repeatEscalationStep

/-- Parametric configuration for a two-stage institutional circuit breaker. -/
structure CircuitBreakerConfig where
  preliminaryFreezeWindow : Time := 3
  ordinarySuspensionLimit : Time := 15
  damagesPaymentWindow    : Time := 10
  activeExposure          : Nat  := 100
  pendingCommitments      : Nat  := 80
  claimantMultiplier      : Nat  := 2
  repeatEscalationStep    : Nat  := 50
  reviewInterval          : Time := 30
  deriving DecidableEq, Repr, Inhabited

/-- Project a `CircuitBreakerConfig` to `ASParams`. -/
def CircuitBreakerConfig.toASParams (cfg : CircuitBreakerConfig) : ASParams :=
  { preliminaryFreezeWindow := cfg.preliminaryFreezeWindow
    ordinarySuspensionLimit := cfg.ordinarySuspensionLimit
    damagesPaymentWindow    := cfg.damagesPaymentWindow
    activeExposure          := cfg.activeExposure
    pendingCommitments      := cfg.pendingCommitments
    claimantMultiplier      := cfg.claimantMultiplier
    repeatEscalationStep    := cfg.repeatEscalationStep }

/-- Compute the required emergency stake from a `CircuitBreakerConfig`. -/
def configuredEmergencyStake (cfg : CircuitBreakerConfig)
    (isClaimant : Bool) (priorWrongful : Nat) : Nat :=
  requiredEmergencyStake cfg.toASParams isClaimant priorWrongful

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a state-preservation duty during preliminary freeze or full pause over any `σ`. -/
def mkDutyPreservePausedState {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor)
    (boundFact freezeFact pausedFact : σ.Fact)
    (tamperActs : List σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .and (.holds boundFact) (.or (.holds freezeFact) (.holds pausedFact))
    demand := .forbid (.anyOf tamperActs) }

/-- Build an advocacy-channel capability limit duty over any signature `σ`. -/
def mkDutyAdvocacyLimits {σ : Sig} (id : String) (sp : Span)
    (bearers : List σ.Actor) (pausedFact : σ.Fact) (operatingAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .except bearers
    active := .holds pausedFact
    demand := .forbid (.act operatingAct) }

/-- Build a preliminary-freeze trigger power with time-to-live `freezeWindow` over any `σ`. -/
def mkPowerEmergencyFreeze {σ : Sig} (id : String) (sp : Span)
    (holder : Who σ) (triggerActs : List σ.Act) (freezeWindow : Time)
    (boundFact stakePostedFact freezeFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := holder
    trigger := .anyOf triggerActs
    valid := .holds boundFact
    adds := [stakePostedFact]
    addsFor := [(freezeFact, freezeWindow)] }

/-- Build a probable-cause affirmation power over any signature `σ`. -/
def mkPowerAffirmProbableCause {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact freezeFact pcFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.holds freezeFact)
    adds := [pcFact] }

/-- Build a full adjudicated suspension power requiring an active preliminary
freeze and affirmed probable cause over any signature `σ`. -/
def mkPowerFullSuspend {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act) (pauseLimit : Time)
    (boundFact freezeFact pcFact pausedFact statePreservedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.and (.holds freezeFact) (.holds pcFact))
    adds := [statePreservedFact]
    addsFor := [(pausedFact, pauseLimit)]
    removes := [freezeFact] }

/-- Build a time-limited investigative suspension renewal power over any signature `σ`. -/
def mkPowerRenewSuspension {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act) (pauseLimit : Time)
    (pausedFact findingMadeFact limitReachedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds pausedFact)
                  (.and (.holds findingMadeFact) (.not (.holds limitReachedFact)))
    addsFor := [(pausedFact, pauseLimit)] }

/-- Build an immunity protecting a bound member against a termination/expulsion
power unless a safety exception condition holds. -/
def mkImmunityAgainstTermination {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (againstPowers : List String)
    (activeCond unlessCond : Cond σ) : Immunity σ :=
  { id := id
    source := sp
    holder := .only holders
    against := againstPowers
    active := activeCond
    unlessCond := unlessCond }

/-! ## 3. Module-Level Invariant Theorems -/

/-- The required emergency stake strictly increases with each wrongful attempt
whenever `repeatEscalationStep > 0`. -/
theorem stake_rises_with_wrongful_attempts (P : ASParams) (isClaimant : Bool) (k : Nat)
    (hs : 0 < P.repeatEscalationStep) :
    requiredEmergencyStake P isClaimant k < requiredEmergencyStake P isClaimant (k + 1) := by
  unfold requiredEmergencyStake
  simp [Nat.add_one_mul]
  omega

/-- Repeat-attempt escalation: required emergency stake strictly increases with
each prior wrongful attempt whenever `0 < P.repeatEscalationStep`. -/
theorem circuit_breaker_stake_escalates (P : ASParams) (isClaimant : Bool) (k : Nat)
    (hs : 0 < P.repeatEscalationStep) :
    requiredEmergencyStake P isClaimant k < requiredEmergencyStake P isClaimant (k + 1) :=
  stake_rises_with_wrongful_attempts P isClaimant k hs

/-- Conflict-of-interest multiplier: whenever `1 ≤ P.claimantMultiplier`, a
residual claimant's required emergency stake is at least as large as a
non-claimant's stake at the same repeat-attempt count. -/
theorem circuit_breaker_claimant_multiplier_ge (P : ASParams) (k : Nat)
    (hm : 1 ≤ P.claimantMultiplier) :
    requiredEmergencyStake P false k ≤ requiredEmergencyStake P true k := by
  unfold requiredEmergencyStake
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hBase : max P.activeExposure P.pendingCommitments * 1 ≤
      max P.activeExposure P.pendingCommitments * P.claimantMultiplier :=
    Nat.mul_le_mul_left _ hm
  omega

/-- Preliminary freeze expires automatically after `t0 + w` for any signature `σ`
and any `freezeFact : σ.Fact`. -/
theorem circuit_breaker_preliminary_freeze_expires {σ : Sig} (freezeFact : σ.Fact)
    (t0 w now : Time) (h : t0 + w < now) :
    LegalState.activeAt (σ := σ) [(freezeFact, t0, some (t0 + w))] now freezeFact = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- An unconfirmed temporary suspension entry stamped at `t0` with duration
`limit` expires for all `now > t0 + limit` for any signature `σ` and `pausedFact : σ.Fact`. -/
theorem circuit_breaker_unconfirmed_suspension_time_bounded {σ : Sig} (pausedFact : σ.Fact)
    (t0 limit now : Time) (h : t0 + limit < now) :
    LegalState.activeAt (σ := σ) [(pausedFact, t0, some (t0 + limit))] now pausedFact = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- Wrongful-suspension consequential damages accounting conserves total damages
(`totalCollectedNow + unpaidEnforceableDeficit = actualDamages + delayDamages`)
and caps assured stake recovery at `min stake (actualDamages + delayDamages)`. -/
theorem circuit_breaker_wrongful_pause_damages_conserved
    (stake actualDamages delayDamages initiatorAssets : Nat) :
    let (fromStake, totalNow, unpaidDeficit) :=
      settleWrongfulSuspensionDamages stake actualDamages delayDamages initiatorAssets
    fromStake = min stake (actualDamages + delayDamages) ∧
    fromStake ≤ totalNow ∧
    totalNow + unpaidDeficit = actualDamages + delayDamages := by
  dsimp [settleWrongfulSuspensionDamages]
  have h1 : min stake (actualDamages + delayDamages) ≤ actualDamages + delayDamages :=
    Nat.min_le_right _ _
  have h2 :
      min initiatorAssets (actualDamages + delayDamages - min stake (actualDamages + delayDamages)) ≤
      actualDamages + delayDamages - min stake (actualDamages + delayDamages) :=
    Nat.min_le_right _ _
  refine ⟨rfl, by omega, by omega⟩

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `configuredEmergencyStake` (non-claimant,
claimant multiplier, and repeat escalation) and `settleWrongfulSuspensionDamages`. -/
def circuitBreakerSelfTest : Bool :=
  let cfg : CircuitBreakerConfig := {}
  let sNonClaimant0 := configuredEmergencyStake cfg false 0
  let sClaimant0    := configuredEmergencyStake cfg true 0
  let sClaimant2    := configuredEmergencyStake cfg true 2
  let (fromStake, totalNow, deficit) := settleWrongfulSuspensionDamages 100 150 40 30
  (sNonClaimant0 == 100) &&
  (sClaimant0 == 200) &&
  (sClaimant2 == 300) &&
  (fromStake == 100 && totalNow == 130 && deficit == 60)

theorem circuitBreakerSelfTest_passes : circuitBreakerSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  CircuitBreakerConfig
  ASParams
  RemediationParams
  requiredEmergencyStake
  configuredEmergencyStake
  mkDutyPreservePausedState
  mkDutyAdvocacyLimits
  mkPowerEmergencyFreeze
  mkPowerAffirmProbableCause
  mkPowerFullSuspend
  mkPowerRenewSuspension
  mkImmunityAgainstTermination
  stake_rises_with_wrongful_attempts
  circuit_breaker_stake_escalates
  circuit_breaker_claimant_multiplier_ge
  circuit_breaker_preliminary_freeze_expires
  circuit_breaker_unconfirmed_suspension_time_bounded
  circuit_breaker_wrongful_pause_damages_conserved
  circuitBreakerSelfTest
  circuitBreakerSelfTest_passes
)
end Charter
