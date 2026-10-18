import SPL.Core.Semantics
import SPL.Law5.Revocation
import SPL.Law3.Theorems

/-!
# Charter.Modules.ExitAndVoice — Reusable Unilateral Exit, Precedence & Voice Module

Extracts and generalizes Law 5 unilateral exit/revocation (`resolveRevocation`,
`baseRevocationTime`, `maxRevocationBound`), cooling-off and clean-state review
bounds, rate-limited living voice (`canInscribeLivingVoice`), and
byte-preserving redaction markers (`EpitaphEntry`, `redactEpitaphEntry`,
`epitaphRecordedBytes`) into a reusable module over any signature `σ : Sig`.
-/

namespace Charter.Modules

open SPL SPL.Law3

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for unilateral exit and rate-limited voice. -/
structure ExitAndVoiceConfig where
  coolingOffWindow   : Time := 5
  cleanStateDelay    : Time := 5
  resolutionDeadline : Time := 20
  tollingExtension   : Time := 4
  leasePeriod        : Time := 12
  voiceMinInterval   : Time := 3
  deriving DecidableEq, Repr, Inhabited

/-- Project an `ExitAndVoiceConfig` to `SPL.Law3.Law5Params`. -/
def ExitAndVoiceConfig.toLaw5Params (cfg : ExitAndVoiceConfig) : Law5Params :=
  { coolingOffWindow   := cfg.coolingOffWindow
    cleanStateDelay    := cfg.cleanStateDelay
    resolutionDeadline := cfg.resolutionDeadline
    tollingExtension   := cfg.tollingExtension
    leasePeriod        := cfg.leasePeriod }

export SPL.Law3 (
  Law5Params
  CensorshipDefault
  RevocationContext
  RevocationOutcome
  baseRevocationTime
  resolveRevocation
  maxRevocationBound
  EpitaphEntry
  redactEpitaphEntry
  epitaphRecordedBytes
  canInscribeLivingVoice
)

/-- Resolve a pending exit/revocation under an `ExitAndVoiceConfig`. -/
def resolveConfiguredExit (cfg : ExitAndVoiceConfig) (ctx : RevocationContext) : RevocationOutcome :=
  resolveRevocation cfg.toLaw5Params ctx

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a cooling-off capital/spawning freeze duty over any signature `σ`. -/
def mkDutyCoolingOffFreeze {σ : Sig} (id : String) (sp : Span)
    (bearers : List σ.Actor) (exitInitiatedFact : σ.Fact) (nonOperatingAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .except bearers
    active := .holds exitInitiatedFact
    demand := .forbid (.act nonOperatingAct) }

/-- Build a non-censorship of voice/epitaph duty over any signature `σ`. -/
def mkDutyNoCensorVoiceOrEpitaph {σ : Sig} (id : String) (sp : Span)
    (bearers beneficiaries : List σ.Actor) (censorAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .only bearers
    beneficiary := .only beneficiaries
    active := .tt
    demand := .forbid (.act censorAct) }

/-- Build a unilateral exit initiation power over any signature `σ`. -/
def mkPowerInitiateExit {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact exitInitiatedFact exitWithdrawnFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [exitInitiatedFact]
    removes := [exitWithdrawnFact] }

/-- Build an exit withdrawal power over any signature `σ`. -/
def mkPowerWithdrawExit {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact exitInitiatedFact exitWithdrawnFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.holds exitInitiatedFact)
    adds := [exitWithdrawnFact]
    removes := [exitInitiatedFact] }

/-- Build a living-voice or epitaph inscription power over any signature `σ`. -/
def mkPowerInscribeVoiceOrEpitaph {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (validCond : Cond σ) (inscribedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := validCond
    adds := [inscribedFact] }

/-- Build a unilateral exit execution power over any signature `σ`. -/
def mkPowerExecuteExit {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact exitedFact : σ.Fact) (extinguishedFacts : List σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    adds := [exitedFact]
    removes := extinguishedFacts }

/-! ## 3. Module-Level Invariant Theorems -/

/-- Deterministic finite exit resolution (`INV.10`): every `RevocationContext`
resolves to a unique outcome, withdrawal before execution always cancels, and
every non-withdrawn / non-withdraw-defaulted exit executes at a timestamp
bounded by `ctx.tInit + maxRevocationBound P`. -/
theorem exit_and_voice_determinate_finite_revocation
    (P : Law5Params) (ctx : RevocationContext) :
    (∃ out : RevocationOutcome, resolveRevocation P ctx = out ∧
      ∀ out', resolveRevocation P ctx = out' → out' = out) ∧
    (ctx.withdrawnBeforeExec = true →
      resolveRevocation P ctx = .cancelledByWithdrawal) ∧
    (ctx.withdrawnBeforeExec = false →
      ¬(ctx.disconnectedAtExec = true ∧
        ctx.reconnectedDuringTolling = false ∧
        ctx.censorshipDefault = .withdraw) →
      ∃ tExec : Time,
        (resolveRevocation P ctx = .executedConnected tExec ∨
         resolveRevocation P ctx = .executedLocally tExec) ∧
        tExec ≤ ctx.tInit + maxRevocationBound P) :=
  determinate_finite_revocation P ctx

/-- Redacting any single `EpitaphEntry` preserves its exact `byteLength`. -/
theorem exit_and_voice_redact_entry_byteLength (ord : Nat) (e : EpitaphEntry) :
    (redactEpitaphEntry ord e).byteLength = e.byteLength := by
  cases e <;> rfl

/-- Redacting any sequence of `EpitaphEntry` records leaves total recorded
byte length (`epitaphRecordedBytes`) strictly invariant. -/
theorem exit_and_voice_redaction_preserves_bytes (ord : Nat) (es : List EpitaphEntry) :
    epitaphRecordedBytes (es.map (redactEpitaphEntry ord)) = epitaphRecordedBytes es := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.map_cons, epitaphRecordedBytes, exit_and_voice_redact_entry_byteLength, ih]

/-- Rate-limited living voice (`canInscribeLivingVoice`) is permitted if and
only if service-budget/fee-pool funding is available and at least `minInterval`
has elapsed since `lastInscribedAt`. -/
theorem exit_and_voice_rate_limit_iff (lastInscribedAt now minInterval : Nat)
    (budgetAvailable : Bool) :
    canInscribeLivingVoice lastInscribedAt now minInterval budgetAvailable = true ↔
      (budgetAvailable = true ∧ now ≥ lastInscribedAt + minInterval) := by
  unfold canInscribeLivingVoice
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `resolveConfiguredExit` across connected,
clean-state-refused, disconnected-execute, and withdrawn contexts, plus
`canInscribeLivingVoice` and `epitaphRecordedBytes`. -/
def exitAndVoiceSelfTest : Bool :=
  let cfg : ExitAndVoiceConfig := {}
  let ctxConn : RevocationContext :=
    { tInit := 2, withdrawnBeforeExec := false, cleanStateRefused := false,
      suspendedDuringStay := false, adjudicationConcludedAt? := none,
      disconnectedAtExec := false, reconnectedDuringTolling := false,
      censorshipDefault := .execute }
  let ctxRefused : RevocationContext := { ctxConn with cleanStateRefused := true }
  let ctxLocal : RevocationContext := { ctxConn with disconnectedAtExec := true }
  let ctxWithdrawn : RevocationContext := { ctxConn with withdrawnBeforeExec := true }
  let entries : List EpitaphEntry := [.unredactedBytes 128, .redactedMarker 64 1]
  let redacted := entries.map (redactEpitaphEntry 2)
  (resolveConfiguredExit cfg ctxConn == .executedConnected 7) &&
  (resolveConfiguredExit cfg ctxRefused == .executedConnected 12) &&
  (resolveConfiguredExit cfg ctxLocal == .executedLocally 11) &&
  (resolveConfiguredExit cfg ctxWithdrawn == .cancelledByWithdrawal) &&
  canInscribeLivingVoice 10 15 3 true &&
  (!canInscribeLivingVoice 10 12 3 true) &&
  (epitaphRecordedBytes entries == 192) &&
  (epitaphRecordedBytes redacted == 192)

theorem exitAndVoiceSelfTest_passes : exitAndVoiceSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  ExitAndVoiceConfig
  Law5Params
  CensorshipDefault
  RevocationContext
  RevocationOutcome
  baseRevocationTime
  resolveRevocation
  maxRevocationBound
  EpitaphEntry
  redactEpitaphEntry
  epitaphRecordedBytes
  canInscribeLivingVoice
  resolveConfiguredExit
  mkDutyCoolingOffFreeze
  mkDutyNoCensorVoiceOrEpitaph
  mkPowerInitiateExit
  mkPowerWithdrawExit
  mkPowerInscribeVoiceOrEpitaph
  mkPowerExecuteExit
  exit_and_voice_determinate_finite_revocation
  exit_and_voice_redact_entry_byteLength
  exit_and_voice_redaction_preserves_bytes
  exit_and_voice_rate_limit_iff
  exitAndVoiceSelfTest
  exitAndVoiceSelfTest_passes
)
end Charter

