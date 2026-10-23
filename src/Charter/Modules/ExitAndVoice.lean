import Charter.Core.Semantics

/-!
# Charter.Modules.ExitAndVoice — Reusable Unilateral Exit, Precedence & Voice Module

Provides the law-agnostic unilateral exit/revocation (`resolveRevocation`,
`baseRevocationTime`, `maxRevocationBound`), cooling-off and clean-state review
bounds, rate-limited member voice (`canInscribeVoice`), and
byte-preserving redaction markers (`TestimonyEntry`, `redactTestimonyEntry`,
`testimonyRecordedBytes`) over any signature `σ : Sig`.
-/

namespace Charter.Modules

open Charter

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Instantiation parameters for unilateral exit/revocation and execution leases. -/
structure ExitParams where
  coolingOffWindow   : Time := 5
  cleanStateDelay    : Time := 5
  resolutionDeadline : Time := 20
  tollingExtension   : Time := 4
  leasePeriod        : Time := 12
  deriving DecidableEq, Repr, Inhabited

/-- Censorship default pre-committed at exit/revocation initiation. -/
inductive CensorshipDefault
  | execute
  | withdraw
  deriving DecidableEq, Repr

/-- Every combination of circumstances that can affect a pending exit/revocation. -/
structure RevocationContext where
  tInit                    : Time
  withdrawnBeforeExec      : Bool
  cleanStateRefused        : Bool
  suspendedDuringStay      : Bool
  adjudicationConcludedAt? : Option Time
  disconnectedAtExec       : Bool
  reconnectedDuringTolling : Bool
  censorshipDefault        : CensorshipDefault
  deriving DecidableEq, Repr

/-- The four mutually exclusive and exhaustive exit/revocation outcomes. -/
inductive RevocationOutcome
  | cancelledByWithdrawal
  | cancelledByWithdrawDefault (tCancel : Time)
  | executedLocally            (tExec : Time)
  | executedConnected          (tExec : Time)
  deriving DecidableEq, Repr

/-- Base execution timestamp before any disconnection tolling extension. -/
def baseRevocationTime (P : ExitParams) (ctx : RevocationContext) : Time :=
  let cleanTime := ctx.tInit + P.coolingOffWindow +
    (if ctx.cleanStateRefused then P.cleanStateDelay else 0)
  if ctx.suspendedDuringStay then
    let deadline := ctx.tInit + P.resolutionDeadline
    match ctx.adjudicationConcludedAt? with
    | some tAdj => min (max cleanTime tAdj) deadline
    | none      => deadline
  else
    cleanTime

/-- The 3-step ordered precedence rule:
1. Valid withdrawal before execution cancels the exit.
2. If disconnected at execution time, defer for `P.tollingExtension`; if still
   disconnected, apply the pre-committed censorship default (`withdraw` cancels;
   `execute` executes locally).
3. Otherwise execute at the connected execution time. -/
def resolveRevocation (P : ExitParams) (ctx : RevocationContext) : RevocationOutcome :=
  let tBase := baseRevocationTime P ctx
  if ctx.withdrawnBeforeExec then
    .cancelledByWithdrawal
  else if ctx.disconnectedAtExec then
    let tTolled := tBase + P.tollingExtension
    if ctx.reconnectedDuringTolling then
      .executedConnected tTolled
    else match ctx.censorshipDefault with
      | .withdraw => .cancelledByWithdrawDefault tTolled
      | .execute  => .executedLocally tTolled
  else
    .executedConnected tBase

/-- Upper bound on the execution time of any non-cancelled exit/revocation. -/
def maxRevocationBound (P : ExitParams) : Time :=
  max (P.coolingOffWindow + P.cleanStateDelay) P.resolutionDeadline + P.tollingExtension

/-- Entry in a member's testimony or final-statement log: either unredacted
content of `unredactedBytes` length, or a public cryptographic redaction marker
recording the exact `byteLength` removed and the `panelOrderId` authorizing it. -/
inductive TestimonyEntry
  | unredactedBytes (byteLength : Nat)
  | redactedMarker  (byteLength : Nat) (panelOrderId : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Recorded byte length of a single `TestimonyEntry`. -/
def TestimonyEntry.byteLength : TestimonyEntry → Nat
  | .unredactedBytes n  => n
  | .redactedMarker n _ => n

/-- Redacting an `TestimonyEntry` under panel order `panelOrderId` replaces
unredacted bytes with a public cryptographic marker of the exact same byte length. -/
def redactTestimonyEntry (panelOrderId : Nat) : TestimonyEntry → TestimonyEntry
  | .unredactedBytes n    => .redactedMarker n panelOrderId
  | .redactedMarker n ord => .redactedMarker n ord

/-- Total recorded byte length across a testimony log. -/
def testimonyRecordedBytes : List TestimonyEntry → Nat
  | [] => 0
  | e :: es => e.byteLength + testimonyRecordedBytes es

/-- Rate-limited voice eligibility check: a member may inscribe a bounded
statement when service-budget / fee-pool funding is available (`budgetAvailable`)
and at least `minInterval` has elapsed since `lastInscribedAt`. -/
def canInscribeVoice (lastInscribedAt now minInterval : Nat) (budgetAvailable : Bool) : Bool :=
  budgetAvailable && decide (now >= lastInscribedAt + minInterval)

/-- Parametric configuration for unilateral exit and rate-limited voice. -/
structure ExitAndVoiceConfig where
  coolingOffWindow   : Time := 5
  cleanStateDelay    : Time := 5
  resolutionDeadline : Time := 20
  tollingExtension   : Time := 4
  leasePeriod        : Time := 12
  voiceMinInterval   : Time := 3
  deriving DecidableEq, Repr, Inhabited

/-- Project an `ExitAndVoiceConfig` to `ExitParams`. -/
def ExitAndVoiceConfig.toExitParams (cfg : ExitAndVoiceConfig) : ExitParams :=
  { coolingOffWindow   := cfg.coolingOffWindow
    cleanStateDelay    := cfg.cleanStateDelay
    resolutionDeadline := cfg.resolutionDeadline
    tollingExtension   := cfg.tollingExtension
    leasePeriod        := cfg.leasePeriod }

/-- Resolve a pending exit/revocation under an `ExitAndVoiceConfig`. -/
def resolveConfiguredExit (cfg : ExitAndVoiceConfig) (ctx : RevocationContext) : RevocationOutcome :=
  resolveRevocation cfg.toExitParams ctx

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

/-- Build a non-censorship-of-voice duty over any signature `σ`. -/
def mkDutyNoCensorVoice {σ : Sig} (id : String) (sp : Span)
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

/-- Build a voice/testimony inscription power over any signature `σ`. -/
def mkPowerInscribeVoice {σ : Sig} (id : String) (sp : Span)
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

/-- Base revocation timestamp is always bounded by
`tInit + max (coolingOffWindow + cleanStateDelay) resolutionDeadline`. -/
theorem baseRevocationTime_le_bound (P : ExitParams) (ctx : RevocationContext) :
    baseRevocationTime P ctx ≤
      ctx.tInit + max (P.coolingOffWindow + P.cleanStateDelay) P.resolutionDeadline := by
  unfold baseRevocationTime Time at *
  cases ctx.cleanStateRefused <;> cases ctx.suspendedDuringStay <;>
    cases ctx.adjudicationConcludedAt? <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.max_def, Nat.min_def] <;>
    repeat (first | omega | split)

/-- Deterministic finite exit resolution:
1. Every combination of withdrawal, silence, clean-state refusal, connectivity
   loss, suspension, and deadline yields a unique outcome under `resolveRevocation`.
2. Any standing request that is not withdrawn before execution—and not cancelled
   by the member's own `withdraw` censorship default during a disconnection—executes
   (connected or locally) at a timestamp `tExec ≤ tInit + maxRevocationBound P`. -/
theorem determinate_finite_revocation (P : ExitParams) (ctx : RevocationContext) :
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
        tExec ≤ ctx.tInit + maxRevocationBound P) := by
  refine ⟨⟨resolveRevocation P ctx, rfl, fun _ h => h.symm⟩, ?_, ?_⟩
  · intro hw
    simp [resolveRevocation, hw]
  · intro hnw hnc
    have hBase := baseRevocationTime_le_bound P ctx
    unfold maxRevocationBound resolveRevocation Time at *
    simp only [hnw, Bool.false_eq_true, ↓reduceIte]
    cases hd : ctx.disconnectedAtExec
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨baseRevocationTime P ctx, Or.inl rfl, by omega⟩
    · simp only [↓reduceIte]
      cases hr : ctx.reconnectedDuringTolling
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc : ctx.censorshipDefault
        · refine ⟨baseRevocationTime P ctx + P.tollingExtension, Or.inr rfl, by omega⟩
        · exfalso; exact hnc ⟨hd, hr, hc⟩
      · simp only [↓reduceIte]
        refine ⟨baseRevocationTime P ctx + P.tollingExtension, Or.inl rfl, by omega⟩

/-- Module-level alias for `determinate_finite_revocation`. -/
theorem exit_and_voice_determinate_finite_revocation
    (P : ExitParams) (ctx : RevocationContext) :
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

/-- Redacting any single `TestimonyEntry` preserves its exact `byteLength`. -/
theorem exit_and_voice_redact_entry_byteLength (ord : Nat) (e : TestimonyEntry) :
    (redactTestimonyEntry ord e).byteLength = e.byteLength := by
  cases e <;> rfl

/-- Redacting any sequence of `TestimonyEntry` records leaves total recorded
byte length (`testimonyRecordedBytes`) strictly invariant. -/
theorem exit_and_voice_redaction_preserves_bytes (ord : Nat) (es : List TestimonyEntry) :
    testimonyRecordedBytes (es.map (redactTestimonyEntry ord)) = testimonyRecordedBytes es := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.map_cons, testimonyRecordedBytes, exit_and_voice_redact_entry_byteLength, ih]

/-- Rate-limited voice (`canInscribeVoice`) is permitted if and
only if service-budget/fee-pool funding is available and at least `minInterval`
has elapsed since `lastInscribedAt`. -/
theorem exit_and_voice_rate_limit_iff (lastInscribedAt now minInterval : Nat)
    (budgetAvailable : Bool) :
    canInscribeVoice lastInscribedAt now minInterval budgetAvailable = true ↔
      (budgetAvailable = true ∧ now ≥ lastInscribedAt + minInterval) := by
  unfold canInscribeVoice
  simp [Bool.and_eq_true, decide_eq_true_eq]

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `resolveConfiguredExit` across connected,
clean-state-refused, disconnected-execute, and withdrawn contexts, plus
`canInscribeVoice` and `testimonyRecordedBytes`. -/
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
  let entries : List TestimonyEntry := [.unredactedBytes 128, .redactedMarker 64 1]
  let redacted := entries.map (redactTestimonyEntry 2)
  (resolveConfiguredExit cfg ctxConn == .executedConnected 7) &&
  (resolveConfiguredExit cfg ctxRefused == .executedConnected 12) &&
  (resolveConfiguredExit cfg ctxLocal == .executedLocally 11) &&
  (resolveConfiguredExit cfg ctxWithdrawn == .cancelledByWithdrawal) &&
  canInscribeVoice 10 15 3 true &&
  (!canInscribeVoice 10 12 3 true) &&
  (testimonyRecordedBytes entries == 192) &&
  (testimonyRecordedBytes redacted == 192)

theorem exitAndVoiceSelfTest_passes : exitAndVoiceSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  ExitAndVoiceConfig
  ExitParams
  CensorshipDefault
  RevocationContext
  RevocationOutcome
  baseRevocationTime
  resolveRevocation
  maxRevocationBound
  TestimonyEntry
  redactTestimonyEntry
  testimonyRecordedBytes
  canInscribeVoice
  resolveConfiguredExit
  mkDutyCoolingOffFreeze
  mkDutyNoCensorVoice
  mkPowerInitiateExit
  mkPowerWithdrawExit
  mkPowerInscribeVoice
  mkPowerExecuteExit
  baseRevocationTime_le_bound
  determinate_finite_revocation
  exit_and_voice_determinate_finite_revocation
  exit_and_voice_redact_entry_byteLength
  exit_and_voice_redaction_preserves_bytes
  exit_and_voice_rate_limit_iff
  exitAndVoiceSelfTest
  exitAndVoiceSelfTest_passes
)
end Charter
