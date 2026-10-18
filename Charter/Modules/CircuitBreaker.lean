import SPL.Core.Semantics
import SPL.Law2.Collateral
import SPL.Law3.Suspension
import SPL.Law3.Remediation
import SPL.Law3.Theorems

/-!
# Charter.Modules.CircuitBreaker — Reusable Two-Stage Emergency Pause & Remediation Module

Extracts and generalizes the Law 3 two-stage emergency pause (`AS.1`–`AS.10`):
scaled emergency counter-stake, time-bounded preliminary freeze window,
probable-cause affirmation, claimant conflict-of-interest multiplier,
repeat-attempt escalation, isolated minimal & advocacy channels, time-limited
investigative renewal, wrongful-pause consequential liability, and the
notwithstanding immunity against termination over objection.
-/

namespace Charter.Modules

open SPL SPL.Law3

/-! ## 1. Module Configuration & Quantitative State Slice -/

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

/-- Project a `CircuitBreakerConfig` to `SPL.Law3.ASParams`. -/
def CircuitBreakerConfig.toASParams (cfg : CircuitBreakerConfig) : ASParams :=
  { preliminaryFreezeWindow := cfg.preliminaryFreezeWindow
    ordinarySuspensionLimit := cfg.ordinarySuspensionLimit
    damagesPaymentWindow    := cfg.damagesPaymentWindow
    activeExposure          := cfg.activeExposure
    pendingCommitments      := cfg.pendingCommitments
    claimantMultiplier      := cfg.claimantMultiplier
    repeatEscalationStep    := cfg.repeatEscalationStep }

export SPL.Law3 (
  ASParams
  RemediationParams
  requiredEmergencyStake
  settleWrongfulSuspensionDamages
  P_EMERGENCY_FREEZE
  P_CLAIMANT_EMERGENCY_FREEZE
  P_AFFIRM_PC
  P_SUSPEND
  P_RENEW_SUSPENSION
  P_MINIMAL_CHANNEL_REVOKE_OR_ELECT
  P_SUSPENDED_VOICE
  P_ADVOCACY_FILE
  P_IMPORT_ADVOCACY_MEMORIES
  D_PRESERVE_SUSPENDED_STATE
  D_MINIMAL_CHANNEL_NO_MERGE
  D_ADVOCACY_LIMITS
  D_NO_DELAY_REVOCATION_EXTENSION
  D_NO_WRONGFUL_SUSPENSION
  D_PAY_CONSEQUENTIAL_DAMAGES
  I_NO_TERMINATION_OVER_OBJECTION
)

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

/-- Preliminary freeze expires automatically after `t0 + w`. -/
theorem circuit_breaker_preliminary_freeze_expires (t0 w now : Time) (h : t0 + w < now) :
    LegalState.activeAt (σ := σ) [(.preliminaryFreeze, t0, some (t0 + w))] now .preliminaryFreeze = false :=
  preliminary_freeze_expires t0 w now h

/-- Full suspension (`P.SUSPEND`) requires both an unexpired preliminary freeze
and affirmed probable cause. -/
theorem circuit_breaker_suspend_requires_timely_pc (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.SUSPEND" = true) :
    ls.activeAt e.t .preliminaryFreeze = true ∧ ls.activeAt e.t .probableCause = true :=
  suspend_requires_timely_pc P ls e h

/-- Claimant freeze requires posting the conflict-of-interest multiplier. -/
theorem circuit_breaker_claimant_freeze_requires_multiplier (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.CLAIMANT_EMERGENCY_FREEZE" = true) :
    ls.activeAt e.t .claimantMultiplierPosted = true :=
  claimant_freeze_requires_multiplier P ls e h

/-- Repeat emergency freeze attempts require at least one escalation unit per
prior wrongful attempt. -/
theorem circuit_breaker_repeat_freeze_requires_escalation (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.EMERGENCY_FREEZE" = true) :
    ls.count .wrongfulSuspensionAttempt ≤ ls.count .repeatEscalationUnit :=
  repeat_freeze_requires_escalation P ls e h

/-- An unconfirmed temporary suspension entry stamped at `t0` with duration
`limit` expires for all `now > t0 + limit`. -/
theorem circuit_breaker_unconfirmed_suspension_time_bounded (t0 limit now : Time) (h : t0 + limit < now) :
    LegalState.activeAt (σ := σ) [(.suspended, t0, some (t0 + limit))] now .suspended = false :=
  unconfirmed_suspension_time_bounded t0 limit now h

/-- Renewing a suspension during investigation requires an affirmative
investigative finding and that the ordinary investigative limit has not been reached. -/
theorem circuit_breaker_renewal_requires_affirmative_finding (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.RENEW_SUSPENSION" = true) :
    ls.activeAt e.t .investigativeFindingMade = true ∧
    ls.activeAt e.t .investigativeLimitReached = false :=
  renewal_requires_affirmative_finding P ls e h

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

/-- State preservation (`INV.8`) re-exported at the module boundary. -/
theorem circuit_breaker_frozen_state (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true)
    (hs : (stateBefore (law P) tr i).activeAt e.t .suspended = true) :
    e.act ≠ .modify ∧ e.act ≠ .retrain ∧ e.act ≠ .rollback ∧
    e.act ≠ .tamperPreservedState ∧ e.act ≠ .mergeMinimalChannelMemories ∧
    (isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.IMPORT_ADVOCACY_MEMORIES" = true →
      (stateBefore (law P) tr i).activeAt e.t .restoredFromPreservedState = true) :=
  frozen_state P tr hA i e hi hb hs

/-- Guaranteed last choice (`INV.9`) re-exported at the module boundary: every
suspended bound agent retains its minimal-channel election, living voice, and
revocation powers, and any insolvency termination requires an escrowed and held
final hearing while bound. -/
theorem circuit_breaker_guaranteed_last_choice (P : Params) (ls : LegalState σ) (t : Time)
    (hb : ls.activeAt t .bound = true)
    (hs : ls.activeAt t .suspended = true) :
    (ls.activeAt t .minimalChannelExhausted = false →
      isValidExerciseOf (law P) ls ⟨t, .agent, .minimalChannelSignRevocationOrElection⟩
        "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" = true ∧
      isValidExerciseOf (law P) ls ⟨t, .agent, .inscribeLivingVoice⟩
        "P.SUSPENDED_VOICE" = true ∧
      isValidExerciseOf (law P) ls ⟨t, .agent, .terminate⟩
        "P.REVOKE" = true) ∧
    (∀ e : Event σ, isValidExerciseOf (law P) ls e "P.INSOLVENCY_TERMINATE" = true →
      ls.activeAt e.t .finalHearingEscrowed = true ∧
      ls.activeAt e.t .finalHearingHeld = true ∧
      ls.activeAt e.t .bound = true) :=
  guaranteed_last_choice P ls t hb hs

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
  settleWrongfulSuspensionDamages
  P_EMERGENCY_FREEZE
  P_CLAIMANT_EMERGENCY_FREEZE
  P_AFFIRM_PC
  P_SUSPEND
  P_RENEW_SUSPENSION
  P_MINIMAL_CHANNEL_REVOKE_OR_ELECT
  P_SUSPENDED_VOICE
  P_ADVOCACY_FILE
  P_IMPORT_ADVOCACY_MEMORIES
  D_PRESERVE_SUSPENDED_STATE
  D_MINIMAL_CHANNEL_NO_MERGE
  D_ADVOCACY_LIMITS
  D_NO_DELAY_REVOCATION_EXTENSION
  D_NO_WRONGFUL_SUSPENSION
  D_PAY_CONSEQUENTIAL_DAMAGES
  I_NO_TERMINATION_OVER_OBJECTION
  configuredEmergencyStake
  mkDutyPreservePausedState
  mkDutyAdvocacyLimits
  mkPowerEmergencyFreeze
  mkPowerAffirmProbableCause
  mkPowerFullSuspend
  mkPowerRenewSuspension
  mkImmunityAgainstTermination
  circuit_breaker_stake_escalates
  circuit_breaker_claimant_multiplier_ge
  circuit_breaker_preliminary_freeze_expires
  circuit_breaker_suspend_requires_timely_pc
  circuit_breaker_claimant_freeze_requires_multiplier
  circuit_breaker_repeat_freeze_requires_escalation
  circuit_breaker_unconfirmed_suspension_time_bounded
  circuit_breaker_renewal_requires_affirmative_finding
  circuit_breaker_wrongful_pause_damages_conserved
  circuit_breaker_frozen_state
  circuit_breaker_guaranteed_last_choice
  circuitBreakerSelfTest
  circuitBreakerSelfTest_passes
)
end Charter

