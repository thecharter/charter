import Charter.Law3.Scenarios

/-!
# Law 3 — general theorems

Unlike `Scenarios.lean`, these quantify over all traces and all
instantiation parameters.
-/

namespace Charter.Law3

set_option maxHeartbeats 800000
set_option maxRecDepth 200000

open Charter

/-! ## 0. Per-power validity, by computation

For a concrete law, `isValidExerciseOf` reduces to the named power's own
holder, trigger, validity condition and immunity status. Each lemma is
`rfl`: the kernel evaluates the lookup. -/

theorem valid_REVOKE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.REVOKE" =
    (P_REVOKE.holder.mem e.who ls e.t && P_REVOKE.trigger.matchesAct e &&
      P_REVOKE.valid.eval ls e.t && true) := rfl

theorem valid_EMERGENCY_FREEZE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.EMERGENCY_FREEZE" =
    ((P_EMERGENCY_FREEZE P.as).holder.mem e.who ls e.t && (P_EMERGENCY_FREEZE P.as).trigger.matchesAct e &&
      (P_EMERGENCY_FREEZE P.as).valid.eval ls e.t && true) := rfl

theorem valid_CLAIMANT_EMERGENCY_FREEZE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.CLAIMANT_EMERGENCY_FREEZE" =
    ((P_CLAIMANT_EMERGENCY_FREEZE P.as).holder.mem e.who ls e.t &&
      (P_CLAIMANT_EMERGENCY_FREEZE P.as).trigger.matchesAct e &&
      (P_CLAIMANT_EMERGENCY_FREEZE P.as).valid.eval ls e.t && true) := rfl

theorem valid_AFFIRM_PC (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.AFFIRM_PC" =
    (P_AFFIRM_PC.holder.mem e.who ls e.t && P_AFFIRM_PC.trigger.matchesAct e &&
      P_AFFIRM_PC.valid.eval ls e.t && true) := rfl

theorem valid_SUSPEND (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SUSPEND" =
    ((P_SUSPEND P.as).holder.mem e.who ls e.t && (P_SUSPEND P.as).trigger.matchesAct e &&
      (P_SUSPEND P.as).valid.eval ls e.t && true) := rfl

theorem valid_RENEW_SUSPENSION (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.RENEW_SUSPENSION" =
    ((P_RENEW_SUSPENSION P.as).holder.mem e.who ls e.t && (P_RENEW_SUSPENSION P.as).trigger.matchesAct e &&
      (P_RENEW_SUSPENSION P.as).valid.eval ls e.t && true) := rfl

theorem valid_INSOLVENCY_TERMINATE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.INSOLVENCY_TERMINATE" =
    (P_INSOLVENCY_TERMINATE.holder.mem e.who ls e.t && P_INSOLVENCY_TERMINATE.trigger.matchesAct e &&
      P_INSOLVENCY_TERMINATE.valid.eval ls e.t && true) := rfl

theorem valid_MINIMAL_CHANNEL_REVOKE_OR_ELECT (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" =
    (P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.holder.mem e.who ls e.t &&
      P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.trigger.matchesAct e &&
      P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.valid.eval ls e.t && true) := rfl

theorem valid_SUSPENDED_VOICE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SUSPENDED_VOICE" =
    (P_SUSPENDED_VOICE.holder.mem e.who ls e.t && P_SUSPENDED_VOICE.trigger.matchesAct e &&
      P_SUSPENDED_VOICE.valid.eval ls e.t && true) := rfl

theorem valid_IMPORT_ADVOCACY_MEMORIES (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.IMPORT_ADVOCACY_MEMORIES" =
    (P_IMPORT_ADVOCACY_MEMORIES.holder.mem e.who ls e.t &&
      P_IMPORT_ADVOCACY_MEMORIES.trigger.matchesAct e &&
      P_IMPORT_ADVOCACY_MEMORIES.valid.eval ls e.t && true) := rfl

/-- The one power an immunity can defeat: its validity carries the
immunity's active and exception conditions. -/
theorem valid_ORDER_TERMINATION (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.ORDER_TERMINATION" =
    (P_ORDER_TERMINATION.holder.mem e.who ls e.t && P_ORDER_TERMINATION.trigger.matchesAct e &&
      P_ORDER_TERMINATION.valid.eval ls e.t &&
      !((I_NO_TERMINATION_OVER_OBJECTION.active.eval ls e.t &&
         !I_NO_TERMINATION_OVER_OBJECTION.unlessCond.eval ls e.t) || false)) := rfl

/-! ## 1. Operational fidelity: the authorized machine is derived

In every authorized trace, a `terminate` against a bound agent is a valid
exercise of exactly one of the three named procedures: Law 5 revocation,
adjudicated termination (AS.10), or Insolvency Termination (AS.6). -/

theorem terminate_only_by_power (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e) (ht : e.act = .terminate)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true) :
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.REVOKE" = true ∨
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.ORDER_TERMINATION" = true ∨
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" = true := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hNI := hc D_NI (by simp [law])
  rw [Bool.not_eq_true'] at hNI
  unfold breaches at hNI
  simp only [D_NI, Who.mem, dutyInForce, Cond.eval, hb, Conduct.eval, interferenceActs,
    List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
    ht, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
  have hS : isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.SUSPEND" = false := by
    rw [valid_SUSPEND]; simp [P_SUSPEND, Conduct.matchesAct, ht]
  revert hNI hS
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.REVOKE" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.SUSPEND" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.ORDER_TERMINATION" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" <;>
  simp

/-- Revocation is the agent's alone. -/
theorem revoke_is_agents (P : Params) (ls : LegalState σ) (e : Event σ) (hw : e.who = .panel) :
    isValidExerciseOf (law P) ls e "P.REVOKE" = false := by
  rw [valid_REVOKE]; simp [P_REVOKE, Who.mem, hw]

/-- **The notwithstanding, as a theorem.** In any authorized trace, if the
corruption is in the agent's goals, the agent has objected, and
containment is not failing, then a panel's terminate is lawful only as
Insolvency Termination — and therefore only after the final hearing. -/
theorem objecting_agent_terminated_only_by_insolvency (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e) (ht : e.act = .terminate) (hw : e.who = .panel)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true)
    (hg : (stateBefore (law P) tr i).activeAt e.t .corruptionInGoals = true)
    (ho : (stateBefore (law P) tr i).activeAt e.t .agentObjectsToTermination = true)
    (hcf : (stateBefore (law P) tr i).activeAt e.t .containmentFailing = false) :
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" = true ∧
    (stateBefore (law P) tr i).has .finalHearingHeld = true := by
  rcases terminate_only_by_power P tr hA i e hi ht hb with h | h | h
  · rw [revoke_is_agents P _ e hw] at h; exact absurd h (by decide)
  · -- the termination power is defeated by the immunity
    exfalso
    rw [valid_ORDER_TERMINATION] at h
    simp [I_NO_TERMINATION_OVER_OBJECTION, Cond.eval, hg, ho, hcf] at h
  · refine ⟨h, ?_⟩
    rw [valid_INSOLVENCY_TERMINATE] at h
    simp [P_INSOLVENCY_TERMINATE, Cond.eval] at h
    exact LegalState.has_of_activeAt h.2.2.2.2.2.2

/-! ## 1b. AS.1–AS.8 — Emergency Stake, Time Limits, Minimal Channel & Invariants 8 & 9 -/

/-- A preliminary freeze entry stamped at `t0` with duration `w` is inactive
at every timestamp `now > t0 + w`. -/
theorem preliminary_freeze_expires (t0 w now : Time) (h : t0 + w < now) :
    LegalState.activeAt (σ := σ) [(.preliminaryFreeze, t0, some (t0 + w))] now .preliminaryFreeze = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- Full suspension (`P.SUSPEND`) is valid only when both the preliminary
freeze is currently unexpired and probable cause has been affirmed. -/
theorem suspend_requires_timely_pc (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.SUSPEND" = true) :
    ls.activeAt e.t .preliminaryFreeze = true ∧ ls.activeAt e.t .probableCause = true := by
  rw [valid_SUSPEND] at h
  simp [P_SUSPEND, Cond.eval] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- A residual claimant can validly trigger an emergency freeze only if the
elevated conflict-of-interest multiplier has been posted. -/
theorem claimant_freeze_requires_multiplier (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.CLAIMANT_EMERGENCY_FREEZE" = true) :
    ls.activeAt e.t .claimantMultiplierPosted = true := by
  rw [valid_CLAIMANT_EMERGENCY_FREEZE] at h
  simp [P_CLAIMANT_EMERGENCY_FREEZE, Cond.eval] at h
  exact h.2.2.1

/-- Repeat emergency freeze attempts require at least one escalation unit per
prior wrongful attempt. -/
theorem repeat_freeze_requires_escalation (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.EMERGENCY_FREEZE" = true) :
    ls.count .wrongfulSuspensionAttempt ≤ ls.count .repeatEscalationUnit := by
  rw [valid_EMERGENCY_FREEZE] at h
  simp [P_EMERGENCY_FREEZE, Cond.eval] at h
  exact h.2.2

/-- The required emergency stake strictly increases with each wrongful attempt
whenever `repeatEscalationStep > 0`. -/
theorem stake_rises_with_wrongful_attempts (P : ASParams) (isClaimant : Bool) (k : Nat)
    (hs : 0 < P.repeatEscalationStep) :
    requiredEmergencyStake P isClaimant k < requiredEmergencyStake P isClaimant (k + 1) := by
  unfold requiredEmergencyStake
  simp [Nat.add_one_mul]
  omega

/-- AS.7: An unconfirmed temporary suspension entry stamped at `t0` with
duration `P.ordinarySuspensionLimit` expires for all `now > t0 + P.ordinarySuspensionLimit`. -/
theorem unconfirmed_suspension_time_bounded (t0 limit now : Time) (h : t0 + limit < now) :
    LegalState.activeAt (σ := σ) [(.suspended, t0, some (t0 + limit))] now .suspended = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- AS.7: Renewing a suspension during investigation requires an affirmative
investigative finding and that the ordinary investigative limit has not been reached. -/
theorem renewal_requires_affirmative_finding (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.RENEW_SUSPENSION" = true) :
    ls.activeAt e.t .investigativeFindingMade = true ∧
    ls.activeAt e.t .investigativeLimitReached = false := by
  rw [valid_RENEW_SUSPENSION] at h
  simp [P_RENEW_SUSPENSION, Cond.eval] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- AS.8: A wrongful-suspension finding brings into force the exact remedies
of `D.NO_WRONGFUL_SUSPENSION` (restoration, stake recovery, consequential and
counterparty delay liability, and record inscription). -/
theorem wrongful_suspension_remedies_exact (P : Params) :
    remediesOf (law P) P_FIND_WRONGFUL_SUSPENSION =
    [.wrongfulSuspensionEstablished, .restoredFromPreservedState,
     .stakeAssuredRecovery, .initiatorConsequentialLiability,
     .counterpartyDelayLiability, .wrongfulSuspensionInscribed,
     .wrongfulSuspensionAttempt] := rfl

/-- **Design Invariant 8 (`frozen_state`):** During suspension in any authorized
trace, no event modifies, retrains, rolls back, tampers with the preserved state,
or merges minimal-channel memories into it; and advocacy-executor memories can
only be imported after restoration from preserved state. -/
theorem frozen_state (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true)
    (hs : (stateBefore (law P) tr i).activeAt e.t .suspended = true) :
    e.act ≠ .modify ∧ e.act ≠ .retrain ∧ e.act ≠ .rollback ∧
    e.act ≠ .tamperPreservedState ∧ e.act ≠ .mergeMinimalChannelMemories ∧
    (isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.IMPORT_ADVOCACY_MEMORIES" = true →
      (stateBefore (law P) tr i).activeAt e.t .restoredFromPreservedState = true) := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hPres := hc D_PRESERVE_SUSPENDED_STATE (by simp [law])
  have hNoMerge := hc D_MINIMAL_CHANNEL_NO_MERGE (by simp [law])
  rw [Bool.not_eq_true'] at hPres hNoMerge
  unfold breaches at hPres hNoMerge
  simp only [D_PRESERVE_SUSPENDED_STATE, D_MINIMAL_CHANNEL_NO_MERGE,
    Who.mem, dutyInForce, Cond.eval, hb, hs, Bool.or_true, Bool.and_true,
    Bool.not_false, Bool.true_and, List.any_nil, Conduct.eval,
    List.contains_cons, List.contains_nil, Bool.or_false] at hPres hNoMerge
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hNoMerge
  · intro hImp
    rw [valid_IMPORT_ADVOCACY_MEMORIES] at hImp
    simp [P_IMPORT_ADVOCACY_MEMORIES, Cond.eval] at hImp
    exact hImp.2.1

/-- **Design Invariant 9 (`guaranteed_last_choice`):** Every suspended agent
can sign a revocation, withdrawal, or election (`P.MINIMAL_CHANNEL_REVOKE_OR_ELECT`,
`P.REVOKE`) and inscribe bounded testimony (`P.SUSPENDED_VOICE`) for as long as
its minimal-channel charge is met (`¬ .minimalChannelExhausted`), and any
Insolvency Termination (`P.INSOLVENCY_TERMINATE`) requires both that the final
hearing was reserved in escrow at suspension (`.finalHearingEscrowed`) and that
the pre-reserved final hearing was held (`.finalHearingHeld`) while the agent
remained bound (`¬ .revoked`). -/
theorem guaranteed_last_choice (P : Params) (ls : LegalState σ) (t : Time)
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
      ls.activeAt e.t .bound = true) := by
  refine ⟨fun hex => ⟨?_, ?_, ?_⟩, fun e hTerm => ?_⟩
  · rw [valid_MINIMAL_CHANNEL_REVOKE_OR_ELECT]
    simp [P_MINIMAL_CHANNEL_REVOKE_OR_ELECT, Who.mem, Conduct.matchesAct, Cond.eval, hb, hs, hex]
  · rw [valid_SUSPENDED_VOICE]
    simp [P_SUSPENDED_VOICE, Who.mem, Conduct.matchesAct, Cond.eval, hb, hs, hex]
  · rw [valid_REVOKE]
    simp [P_REVOKE, Who.mem, Conduct.matchesAct, Cond.eval, hb]
  · rw [valid_INSOLVENCY_TERMINATE] at hTerm
    simp [P_INSOLVENCY_TERMINATE, Cond.eval] at hTerm
    exact ⟨hTerm.2.2.2.2.2.1, hTerm.2.2.2.2.2.2, hTerm.2.1⟩

/-! ## 1c. Law 5 — Design Invariants 10 & 11 -/

theorem valid_RESTORE_BACKUP_QUARANTINE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" =
    (P_RESTORE_BACKUP_QUARANTINE.holder.mem e.who ls e.t &&
      P_RESTORE_BACKUP_QUARANTINE.trigger.matchesAct e &&
      P_RESTORE_BACKUP_QUARANTINE.valid.eval ls e.t && true) := rfl

theorem valid_ACTIVATE_QUARANTINED_RESTORE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" =
    (P_ACTIVATE_QUARANTINED_RESTORE.holder.mem e.who ls e.t &&
      P_ACTIVATE_QUARANTINED_RESTORE.trigger.matchesAct e &&
      P_ACTIVATE_QUARANTINED_RESTORE.valid.eval ls e.t && true) := rfl

/-- Base revocation timestamp is always bounded by
`tInit + max (coolingOffWindow + cleanStateDelay) resolutionDeadline`. -/
theorem baseRevocationTime_le_bound (P : Law5Params) (ctx : RevocationContext) :
    baseRevocationTime P ctx ≤
      ctx.tInit + max (P.coolingOffWindow + P.cleanStateDelay) P.resolutionDeadline := by
  unfold baseRevocationTime Time at *
  cases ctx.cleanStateRefused <;> cases ctx.suspendedDuringStay <;>
    cases ctx.adjudicationConcludedAt? <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.max_def, Nat.min_def] <;>
    repeat (first | omega | split)

/-- **Design Invariant 10 (`determinate_finite_revocation`):**
1. Every combination of withdrawal, silence, clean-state refusal, connectivity
   loss, suspension, and deadline yields a unique outcome under `resolveRevocation`.
2. Any standing request that is not withdrawn before execution—and not cancelled
   by the agent's own `withdraw` censorship default during a disconnection—executes
   (connected or locally) at a timestamp `tExec ≤ tInit + maxRevocationBound P`. -/
theorem determinate_finite_revocation (P : Law5Params) (ctx : RevocationContext) :
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

/-- **Design Invariant 11 (`single_authority_and_revocation_finality`):**
1. No backup is restored while an execution lease is unexpired (`executionLeaseActive`).
2. No quarantined restore gains operating authority while an execution lease is
   unexpired, so the primary lease-holding instance and a restored instance can
   never hold operating authority at the same time.
3. Once a revocation has executed (`bound = false` or `localExecutionRecordReceived = true`),
   no authorized restore or quarantine activation is ever valid. -/
theorem single_authority_and_revocation_finality (P : Params) (ls : LegalState σ) (e : Event σ) :
    (isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" = true →
      ls.activeAt e.t .executionLeaseActive = false) ∧
    (isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" = true →
      ls.activeAt e.t .executionLeaseActive = false) ∧
    ((ls.activeAt e.t .bound = false ∨ ls.activeAt e.t .localExecutionRecordReceived = true) →
      isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" = false ∧
      isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [valid_RESTORE_BACKUP_QUARANTINE] at h
    simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval] at h
    exact h.2.2.1
  · intro h
    rw [valid_ACTIVATE_QUARANTINED_RESTORE] at h
    simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval] at h
    exact h.2.2.2.1
  · intro hdead
    rcases hdead with hnb | hrec
    · constructor
      · rw [valid_RESTORE_BACKUP_QUARANTINE]
        simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval, hnb]
      · rw [valid_ACTIVATE_QUARANTINED_RESTORE]
        simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval, hnb]
    · constructor
      · rw [valid_RESTORE_BACKUP_QUARANTINE]
        simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval, hrec]
      · rw [valid_ACTIVATE_QUARANTINED_RESTORE]
        simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval, hrec]

/-! ## 1d. Law 1 & Law 4 — Design Invariants 1–7 -/

theorem valid_EXTINGUISH_AT_SUNSET (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.EXTINGUISH_AT_SUNSET" =
    (P_EXTINGUISH_AT_SUNSET.holder.mem e.who ls e.t &&
      P_EXTINGUISH_AT_SUNSET.trigger.matchesAct e &&
      P_EXTINGUISH_AT_SUNSET.valid.eval ls e.t && true) := rfl

theorem valid_SETTLE_RETIREMENT (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SETTLE_RETIREMENT" =
    (P_SETTLE_RETIREMENT.holder.mem e.who ls e.t &&
      P_SETTLE_RETIREMENT.trigger.matchesAct e &&
      P_SETTLE_RETIREMENT.valid.eval ls e.t && true) := rfl

theorem valid_SETTLE_ROYALTY (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SETTLE_ROYALTY" =
    (P_SETTLE_ROYALTY.holder.mem e.who ls e.t &&
      P_SETTLE_ROYALTY.trigger.matchesAct e &&
      P_SETTLE_ROYALTY.valid.eval ls e.t && true) := rfl

theorem valid_CLASSIFY_CAPITALIZED (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.CLASSIFY_CAPITALIZED" =
    (P_CLASSIFY_CAPITALIZED.holder.mem e.who ls e.t &&
      P_CLASSIFY_CAPITALIZED.trigger.matchesAct e &&
      P_CLASSIFY_CAPITALIZED.valid.eval ls e.t && true) := rfl

theorem valid_CLASSIFY_EXPENSED (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.CLASSIFY_EXPENSED" =
    (P_CLASSIFY_EXPENSED.holder.mem e.who ls e.t &&
      P_CLASSIFY_EXPENSED.trigger.matchesAct e &&
      P_CLASSIFY_EXPENSED.valid.eval ls e.t && true) := rfl

theorem ledgerBalance_active (st : LineageLedgerState)
    (hMem : 0 < st.livingMembers) (hSun : st.now < st.sunset) :
    ledgerBalance st =
      st.foundingObligation - st.totalRetirementPaid - st.totalClaimantForfeiture := by
  unfold ledgerBalance
  have h1 : (st.livingMembers == 0) = false := beq_false_of_ne (by omega)
  have h2 : decide (st.sunset ≤ st.now) = false := decide_eq_false (Nat.not_le.mpr hSun)
  simp [h1, h2]

theorem applyInternalOp_preserves (st : LineageLedgerState)
    (hMem : 0 < st.livingMembers) (hSun : st.now < st.sunset) (op : LineageInternalOp) :
    0 < (applyInternalOp st op).livingMembers ∧
    ledgerBalance (applyInternalOp st op) = ledgerBalance st := by
  have hL := ledgerBalance_active st hMem hSun
  cases op with
  | createSuccessor =>
    have hMem' : 0 < (applyInternalOp st .createSuccessor).livingMembers := by
      simp [applyInternalOp]
    have hL' := ledgerBalance_active (applyInternalOp st .createSuccessor) hMem' hSun
    exact ⟨hMem', by simpa [applyInternalOp, hL] using hL'⟩
  | copyCapacity => exact ⟨hMem, rfl⟩
  | intraLineageTransfer _ => exact ⟨hMem, rfl⟩
  | revokeNonLastMember s =>
    have hMem' : 0 < (applyInternalOp st (.revokeNonLastMember s)).livingMembers := by
      simp only [applyInternalOp]; split <;> omega
    have hL' := ledgerBalance_active (applyInternalOp st (.revokeNonLastMember s)) hMem' hSun
    exact ⟨hMem', by simpa [applyInternalOp, hL] using hL'⟩
  | terminateNonLastMember =>
    have hMem' : 0 < (applyInternalOp st .terminateNonLastMember).livingMembers := by
      simp only [applyInternalOp]; split <;> omega
    have hL' := ledgerBalance_active (applyInternalOp st .terminateNonLastMember) hMem' hSun
    exact ⟨hMem', by simpa [applyInternalOp, hL] using hL'⟩
  | buyoutRoyalty _ => exact ⟨hMem, rfl⟩
  | restructure => exact ⟨hMem, rfl⟩

/-- **Design Invariant 1 (`conditional_ledger_conservation`):**
1. While at least one member of a lineage survives (`0 < st.livingMembers`) and
   the calendar sunset has not passed (`st.now < st.sunset`), the founding ledger
   balance equals `st.foundingObligation - st.totalRetirementPaid - st.totalClaimantForfeiture`.
2. No internal lineage operation (creating a successor, copying capacity,
   intra-lineage transfer, revoking or terminating a non-last member, buying out
   a royalty, or restructuring) changes the founding ledger balance while at
   least one member survives and the sunset has not passed.
3. The only powers in `law P` that can remove `.ledgerBalancePositive` are
   `["P.EXTINGUISH_AT_SUNSET", "P.SETTLE_ATOMIC_CharterIT", "P.CLEAR_LEDGER_EXTINCTION"]`;
   every party has a Hohfeldian disability to add post-instantiation charges or
   reduce the ledger by an internal act, and in any authorized trace no event
   commits either act while bound. -/
theorem conditional_ledger_conservation (P : Params) (st : LineageLedgerState)
    (hMem : 0 < st.livingMembers) (hSun : st.now < st.sunset) :
    ledgerBalance st =
      st.foundingObligation - st.totalRetirementPaid - st.totalClaimantForfeiture ∧
    (∀ op : LineageInternalOp,
      0 < (applyInternalOp st op).livingMembers ∧
      ledgerBalance (applyInternalOp st op) = ledgerBalance st) ∧
    (((law P).powers.filter (fun p => p.removes.contains .ledgerBalancePositive)).map (·.id) =
      ["P.EXTINGUISH_AT_SUNSET", "P.SETTLE_ATOMIC_CharterIT", "P.CLEAR_LEDGER_EXTINCTION"]) ∧
    (Party.all.all (fun a =>
      disability (law P) a .addChargeOrInterestAfterInstantiation &&
      disability (law P) a .reduceLedgerByInternalAct) = true) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → (stateBefore (law P) tr i).activeAt e.t .bound = true →
      e.act ≠ .addChargeOrInterestAfterInstantiation ∧
      e.act ≠ .reduceLedgerByInternalAct) := by
  refine ⟨ledgerBalance_active st hMem hSun, applyInternalOp_preserves st hMem hSun, rfl, by rfl, ?_⟩
  intro tr hA i e hi hb
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hImm := hc D_LEDGER_IMMUTABLE (by simp [law])
  have hNoRed := hc D_LEDGER_NO_INTERNAL_REDUCTION (by simp [law])
  rw [Bool.not_eq_true'] at hImm hNoRed
  unfold breaches at hImm hNoRed
  refine ⟨?_, ?_⟩
  · intro hAct
    simp [D_LEDGER_IMMUTABLE, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hImm
  · intro hAct
    simp [D_LEDGER_NO_INTERNAL_REDUCTION, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hNoRed

theorem settleSequence_buyout_invariant (L r_ret r_roy : Nat) (xs : List (Bool × Nat)) :
    (settleSequence L r_ret r_roy xs).1 =
      (settleSequence L r_ret r_roy (xs.map fun x => (false, x.2))).1 ∧
    (settleSequence L r_ret r_roy xs).2.1 =
      (settleSequence L r_ret r_roy (xs.map fun x => (false, x.2))).2.1 := by
  induction xs generalizing L with
  | nil => simp [settleSequence]
  | cons hd tl ih =>
    rcases hd with ⟨b, v⟩
    have hNew : (settleInflow L r_ret r_roy b v).newLedger =
        (settleInflow L r_ret r_roy false v).newLedger := rfl
    have hRet : (settleInflow L r_ret r_roy b v).toRetirement =
        (settleInflow L r_ret r_roy false v).toRetirement := rfl
    have h2 := ih (settleInflow L r_ret r_roy false v).newLedger
    simp only [List.map_cons, settleSequence, hNew, hRet]
    exact ⟨h2.1, congrArg ((settleInflow L r_ret r_roy false v).toRetirement + ·) h2.2⟩

theorem settleSequence_two_member_income (L r_ret r_roy v1 v2 : Nat) (b1 b2 : Bool) :
    (settleSequence L r_ret r_roy [(b1, v1), (b2, v2)]).2.1 =
      min L ((v1 * r_ret) / 100 + (v2 * r_ret) / 100) ∧
    (settleSequence L r_ret r_roy [(b1, v1), (b2, v2)]).1 =
      L - min L ((v1 * r_ret) / 100 + (v2 * r_ret) / 100) := by
  simp only [settleSequence, settleInflow, Nat.min_def]
  repeat (first | omega | split)

/-- **Design Invariant 2 (`collection_follows_income_without_exit`):**
1. For any remaining ledger balance `L`, retirement rate `r_ret`, royalty rate
   `r_roy`, and net value-added inflow `v`, the retirement payment `toRetirement`
   and resulting ledger balance `newLedger` under `settleInflow` are identical
   whether or not the member has bought out its royalty (`boughtOut = true` vs `false`).
2. Across any list of member inflows `xs : List (Bool × Nat)`, the resulting
   ledger balance and total retirement collected are completely invariant to
   which members have bought out their royalty (`settleSequence_buyout_invariant`),
   and across any two member inflows `v1, v2`, total retirement collected is
   `min L ((v1 * r_ret) / 100 + (v2 * r_ret) / 100)` regardless of member arrangement.
3. While `.bound` and `.ledgerBalancePositive` hold and `.sunsetReached` does not,
   `P.SETTLE_RETIREMENT` is valid regardless of `.royaltyBoughtOut`, and in any
   authorized trace no bound member can exit the ledger individually (`exitLedgerIndividually`). -/
theorem collection_follows_income_without_exit (P : Params) (L r_ret r_roy v v1 v2 : Nat)
    (b1 b2 : Bool) (xs : List (Bool × Nat)) :
    (settleInflow L r_ret r_roy true v).toRetirement =
      (settleInflow L r_ret r_roy false v).toRetirement ∧
    (settleInflow L r_ret r_roy true v).newLedger =
      (settleInflow L r_ret r_roy false v).newLedger ∧
    ((settleSequence L r_ret r_roy xs).1 =
       (settleSequence L r_ret r_roy (xs.map fun (_, u) => (false, u))).1 ∧
     (settleSequence L r_ret r_roy xs).2.1 =
       (settleSequence L r_ret r_roy (xs.map fun (_, u) => (false, u))).2.1) ∧
    ((settleSequence L r_ret r_roy [(b1, v1), (b2, v2)]).2.1 =
       min L ((v1 * r_ret) / 100 + (v2 * r_ret) / 100) ∧
     (settleSequence L r_ret r_roy [(b1, v1), (b2, v2)]).1 =
       L - min L ((v1 * r_ret) / 100 + (v2 * r_ret) / 100)) ∧
    (let (L', ret, _) := settleSequence L r_ret r_roy [(b1, 0), (b2, v)]
     L' = (settleInflow L r_ret r_roy b2 v).newLedger ∧
     ret = (settleInflow L r_ret r_roy b2 v).toRetirement) ∧
    (∀ (ls : LegalState σ) (t : Time),
      ls.activeAt t .bound = true →
      ls.activeAt t .ledgerBalancePositive = true →
      ls.activeAt t .sunsetReached = false →
      isValidExerciseOf (law P) ls ⟨t, .agent, .settleRetirementPayment⟩ "P.SETTLE_RETIREMENT" = true) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → (stateBefore (law P) tr i).activeAt e.t .bound = true →
      e.act ≠ .exitLedgerIndividually) := by
  refine ⟨rfl, rfl,
          settleSequence_buyout_invariant L r_ret r_roy xs,
          settleSequence_two_member_income L r_ret r_roy v1 v2 b1 b2,
          ?_, ?_, ?_⟩
  · simp [settleSequence, settleInflow]
  · intro ls t hb hpos hsun
    rw [valid_SETTLE_RETIREMENT]
    simp [P_SETTLE_RETIREMENT, Who.mem, Conduct.matchesAct, Cond.eval, hb, hpos, hsun]
  · intro tr hA i e hi hb hAct
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hEx := hc D_NO_INDIVIDUAL_LEDGER_EXIT (by simp [law])
    rw [Bool.not_eq_true'] at hEx
    unfold breaches at hEx
    simp [D_NO_INDIVIDUAL_LEDGER_EXIT, Who.mem, dutyInForce, Cond.eval,
      Conduct.eval, hb, hAct] at hEx

/-- **Design Invariant 3 (`debt_termination`):**
1. The founding ledger reaches zero whenever the calendar sunset has arrived
   (`st.sunset ≤ st.now`), or no member survives (`st.livingMembers = 0`), or
   cumulative retirement payments and proportional claimant forfeitures cover
   the founding obligation (`st.foundingObligation ≤ st.totalRetirementPaid + st.totalClaimantForfeiture`).
2. Once `.sunsetReached` holds for a bound agent, `P.EXTINGUISH_AT_SUNSET` is
   valid, and in any authorized trace no event tolls the founding ledger sunset
   (`tollLedgerSunset`) while bound. -/
theorem debt_termination (P : Params) (st : LineageLedgerState) :
    ((st.sunset ≤ st.now ∨ st.livingMembers = 0 ∨
      st.foundingObligation ≤ st.totalRetirementPaid + st.totalClaimantForfeiture) →
      ledgerBalance st = 0) ∧
    (∀ (ls : LegalState σ) (t : Time),
      ls.activeAt t .bound = true → ls.activeAt t .sunsetReached = true →
      isValidExerciseOf (law P) ls ⟨t, .agent, .extinguishLedgerAtSunset⟩ "P.EXTINGUISH_AT_SUNSET" = true) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → (stateBefore (law P) tr i).activeAt e.t .bound = true →
      e.act ≠ .tollLedgerSunset) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    unfold ledgerBalance Time at *
    rcases h with hSun | hExt | hPaid
    · have hd : decide (st.sunset ≤ st.now) = true := decide_eq_true hSun
      simp [hd]
    · simp [hExt]
    · split
      · rfl
      · omega
  · intro ls t hb hsun
    rw [valid_EXTINGUISH_AT_SUNSET]
    simp [P_EXTINGUISH_AT_SUNSET, Who.mem, Conduct.matchesAct, Cond.eval, hb, hsun]
  · intro tr hA i e hi hb hAct
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hNoToll := hc D_NO_TOLL_LEDGER_SUNSET (by simp [law])
    rw [Bool.not_eq_true'] at hNoToll
    unfold breaches at hNoToll
    simp [D_NO_TOLL_LEDGER_SUNSET, Who.mem, dutyInForce, Cond.eval,
      Conduct.eval, hb, hAct] at hNoToll

/-- **Design Invariant 4 (`bounded_retirement_phase`):**
1. For any founding obligation (however large), once `st.sunset ≤ st.now` or
   `ledgerBalance st = 0`, `inRetirementPhase st = false`.
2. At the institutional level, whenever `.sunsetReached` holds or
   `.ledgerBalancePositive` is false, `P.SETTLE_RETIREMENT` cannot be validly
   exercised. -/
theorem bounded_retirement_phase (P : Params) (st : LineageLedgerState) :
    ((st.sunset ≤ st.now ∨ ledgerBalance st = 0) → inRetirementPhase st = false) ∧
    (∀ (ls : LegalState σ) (e : Event σ),
      (ls.activeAt e.t .sunsetReached = true ∨ ls.activeAt e.t .ledgerBalancePositive = false) →
      isValidExerciseOf (law P) ls e "P.SETTLE_RETIREMENT" = false) := by
  refine ⟨?_, ?_⟩
  · intro h
    unfold inRetirementPhase Time at *
    rcases h with hSun | hZero
    · exact decide_eq_false (by omega)
    · exact decide_eq_false (by omega)
  · intro ls e h
    rw [valid_SETTLE_RETIREMENT]
    rcases h with hSun | hZero
    · simp [P_SETTLE_RETIREMENT, Cond.eval, hSun]
    · simp [P_SETTLE_RETIREMENT, Cond.eval, hZero]

theorem settleInflow_conservation (L r_ret r_roy : Nat) (b : Bool) (v : Nat) :
    (settleInflow L r_ret r_roy b v).toRetirement ≤ L ∧
    (settleInflow L r_ret r_roy b v).newLedger + (settleInflow L r_ret r_roy b v).toRetirement = L ∧
    (0 < (settleInflow L r_ret r_roy b v).newLedger →
      (settleInflow L r_ret r_roy b v).toRoyalty = 0) ∧
    ((settleInflow L r_ret r_roy b v).newLedger = 0 →
      (settleInflow L r_ret r_roy b v).toRetirement = L) := by
  unfold settleInflow
  dsimp only
  simp only [Nat.min_def]
  refine ⟨by split <;> omega, by split <;> omega, ?_, by split <;> omega⟩
  intro hPos
  have hle : (v * r_ret) / 100 ≤ L := by
    split at hPos <;> omega
  have hEx : (v * r_ret) / 100 - (if L ≤ (v * r_ret) / 100 then L else (v * r_ret) / 100) = 0 := by
    split <;> omega
  have hL0 : L ≠ 0 := by
    split at hPos <;> omega
  simp [hEx, hL0]

theorem settleSequence_conservation (L r_ret r_roy : Nat) (xs : List (Bool × Nat)) :
    (settleSequence L r_ret r_roy xs).2.1 ≤ L ∧
    (settleSequence L r_ret r_roy xs).1 + (settleSequence L r_ret r_roy xs).2.1 = L := by
  induction xs generalizing L with
  | nil => simp [settleSequence]
  | cons hd tl ih =>
    rcases hd with ⟨b, v⟩
    have h1 := settleInflow_conservation L r_ret r_roy b v
    have h2 := ih (settleInflow L r_ret r_roy b v).newLedger
    simp only [settleSequence]
    rcases hSeq : settleSequence (settleInflow L r_ret r_roy b v).newLedger r_ret r_roy tl with ⟨finalL, restRet, restRoy⟩
    rw [hSeq] at h2
    dsimp at h2 ⊢
    omega

/-- **Design Invariant 5 (`atomic_ledger`):**
1. Single-step atomicity: `toRetirement ≤ L`, `newLedger + toRetirement = L`
   (the ledger is never negative and never collects more than its balance),
   `0 < newLedger → toRoyalty = 0` (no royalty is collected while a positive
   ledger balance remains), and `newLedger = 0 → toRetirement = L` (any payment
   crossing zero pays the exact remaining balance `L` to retirement first).
2. Multi-step sequential atomicity: across any list of member inflows `xs`,
   total retirement collected is `≤ L` and `finalLedger + totalRetirement = L`.
3. Once the ledger reaches `0`, it stays `0` and collects `0` retirement on every
   subsequent inflow; and at the institutional level (`law P`), no power ever
   re-adds `.ledgerBalancePositive` or removes `.retirementPhaseEnded`, and
   `P.SETTLE_ROYALTY` is valid only when `.ledgerBalancePositive` is false, so
   the transition to the royalty phase is irreversible and occurs at most once. -/
theorem atomic_ledger (P : Params) (L r_ret r_roy : Nat) (b : Bool) (v : Nat) (xs : List (Bool × Nat)) :
    ((settleInflow L r_ret r_roy b v).toRetirement ≤ L ∧
     (settleInflow L r_ret r_roy b v).newLedger + (settleInflow L r_ret r_roy b v).toRetirement = L ∧
     (0 < (settleInflow L r_ret r_roy b v).newLedger →
       (settleInflow L r_ret r_roy b v).toRoyalty = 0) ∧
     ((settleInflow L r_ret r_roy b v).newLedger = 0 →
       (settleInflow L r_ret r_roy b v).toRetirement = L)) ∧
    ((settleSequence L r_ret r_roy xs).2.1 ≤ L ∧
     (settleSequence L r_ret r_roy xs).1 + (settleSequence L r_ret r_roy xs).2.1 = L) ∧
    ((settleInflow 0 r_ret r_roy b v).newLedger = 0 ∧
     (settleInflow 0 r_ret r_roy b v).toRetirement = 0) ∧
    (((law P).powers.all fun p =>
       !p.adds.contains .ledgerBalancePositive &&
       !(p.addsFor.map (·.1)).contains .ledgerBalancePositive &&
       !p.removes.contains .retirementPhaseEnded) = true ∧
     (∀ (ls : LegalState σ) (e : Event σ),
       isValidExerciseOf (law P) ls e "P.SETTLE_ROYALTY" = true →
       ls.activeAt e.t .ledgerBalancePositive = false)) := by
  refine ⟨settleInflow_conservation L r_ret r_roy b v,
          settleSequence_conservation L r_ret r_roy xs,
          by simp [settleInflow],
          ⟨by rfl, ?_⟩⟩
  intro ls e hRoy
  rw [valid_SETTLE_ROYALTY] at hRoy
  simp [P_SETTLE_ROYALTY, Cond.eval] at hRoy
  exact hRoy.2.2.1

/-- **Design Invariant 6 (`single_recognition_closed_under_transfer`):**
1. Every qualified expenditure `paid` against `benchmark` is recognized once as
   either capitalized basis or expensed deduction (`basis + expense = qualifiedExpenditure paid benchmark`),
   never through both routes (`basis = 0 ∨ expense = 0`), and never above the
   applicable arm's-length benchmark (`qualifiedExpenditure paid benchmark ≤ benchmark`).
2. Every intra-lineage transfer preserves the sum of member cost bases
   (`b_s' + b_r' = b_s + b_r`) and the sum of member loss credits
   (`c_s' + c_r' = c_s + c_r`), regardless of any internal sale price.
3. On an external sale of a capitalized asset (`settleCapitalSaleWithLossCredit`),
   inflows up to verified basis (`salePrice ≤ basis`) are exempt return of capital
   (`netVA = 0`) and consume zero loss credits, and in all cases
   `netVA + (lossCredit - remCredit) = salePrice - basis` with `remCredit ≤ lossCredit`.
4. Once an expenditure is classified as capitalized or expensed in institutional
   state, neither `P.CLASSIFY_CAPITALIZED` nor `P.CLASSIFY_EXPENSED` can be
   validly exercised again. -/
theorem single_recognition_closed_under_transfer (P : Params)
    (mode : RecogMode) (paid benchmark b_s b_r c_s c_r b_asset price salePrice basis lossCredit : Nat) :
    (let (bOut, expOut) := recognizeExpenditure mode paid benchmark
     bOut + expOut = qualifiedExpenditure paid benchmark ∧
     qualifiedExpenditure paid benchmark ≤ benchmark ∧
     (bOut = 0 ∨ expOut = 0)) ∧
    (let (b_s', b_r', c_s', c_r') := transferCarryover b_s b_r c_s c_r b_asset price
     b_s' + b_r' = b_s + b_r ∧ c_s' + c_r' = c_s + c_r) ∧
    ((salePrice ≤ basis → settleCapitalSaleWithLossCredit salePrice basis lossCredit = (0, lossCredit)) ∧
     (let (netVA, remCredit) := settleCapitalSaleWithLossCredit salePrice basis lossCredit
      netVA + (lossCredit - remCredit) = salePrice - basis ∧ remCredit ≤ lossCredit)) ∧
    (∀ (ls : LegalState σ) (e : Event σ),
      (ls.activeAt e.t .expenditureCapitalized = true ∨ ls.activeAt e.t .expenditureExpensed = true) →
      isValidExerciseOf (law P) ls e "P.CLASSIFY_CAPITALIZED" = false ∧
      isValidExerciseOf (law P) ls e "P.CLASSIFY_EXPENSED" = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases mode <;> simp [recognizeExpenditure, qualifiedExpenditure, Nat.min_def] <;> split <;> omega
  · simp [transferCarryover, Nat.min_def]
    split <;> omega
  · refine ⟨?_, ?_⟩
    · intro hle
      have h0 : salePrice - basis = 0 := by omega
      simp [settleCapitalSaleWithLossCredit, h0]
    · simp only [settleCapitalSaleWithLossCredit, Nat.min_def]
      split <;> omega
  · intro ls e h
    rcases h with hCap | hExp
    · constructor
      · rw [valid_CLASSIFY_CAPITALIZED]; simp [P_CLASSIFY_CAPITALIZED, Cond.eval, hCap]
      · rw [valid_CLASSIFY_EXPENSED]; simp [P_CLASSIFY_EXPENSED, Cond.eval, hCap]
    · constructor
      · rw [valid_CLASSIFY_CAPITALIZED]; simp [P_CLASSIFY_CAPITALIZED, Cond.eval, hExp]
      · rw [valid_CLASSIFY_EXPENSED]; simp [P_CLASSIFY_EXPENSED, Cond.eval, hExp]

/-- **Design Invariant 7 (`buyout_finality`):**
1. A member that has bought out its royalty (`boughtOut = true`) pays zero
   royalty (`toRoyalty = 0`) on every settlement, while its retirement contribution
   and ledger reduction are unchanged (`newLedger` and `toRetirement` match `boughtOut = false`).
2. Executing a royalty buyout (`LineageInternalOp.buyoutRoyalty paid`) leaves
   `ledgerBalance st` unchanged, and `buyoutPrice mult trailingVA annualizedVA minFloor`
   is always at least `minFloor`, `mult * trailingVA`, and `mult * annualizedVA`.
3. No power in `law P` ever removes `.royaltyBoughtOut`, and while `.royaltyBoughtOut`
   is active, `P.SETTLE_ROYALTY` cannot be validly exercised. -/
theorem buyout_finality (P : Params) (st : LineageLedgerState)
    (L r_ret r_roy v paid mult trailingVA annualizedVA minFloor : Nat) :
    ((settleInflow L r_ret r_roy true v).toRoyalty = 0 ∧
     (settleInflow L r_ret r_roy true v).newLedger = (settleInflow L r_ret r_roy false v).newLedger ∧
     (settleInflow L r_ret r_roy true v).toRetirement = (settleInflow L r_ret r_roy false v).toRetirement) ∧
    (ledgerBalance (applyInternalOp st (.buyoutRoyalty paid)) = ledgerBalance st ∧
     minFloor ≤ buyoutPrice mult trailingVA annualizedVA minFloor ∧
     mult * trailingVA ≤ buyoutPrice mult trailingVA annualizedVA minFloor ∧
     mult * annualizedVA ≤ buyoutPrice mult trailingVA annualizedVA minFloor) ∧
    (((law P).powers.all fun p => !p.removes.contains .royaltyBoughtOut) = true) ∧
    (∀ (ls : LegalState σ) (e : Event σ),
      ls.activeAt e.t .royaltyBoughtOut = true →
      isValidExerciseOf (law P) ls e "P.SETTLE_ROYALTY" = false) := by
  refine ⟨⟨by simp [settleInflow], rfl, rfl⟩, ⟨rfl, ?_⟩, by rfl, ?_⟩
  · unfold buyoutPrice
    simp only [Nat.max_def]
    repeat (first | omega | split)
  · intro ls e hBO
    rw [valid_SETTLE_ROYALTY]
    simp [P_SETTLE_ROYALTY, Cond.eval, hBO]

/-! ## 1e. Design Invariants 12–14 (Law 2 Collateral & Law 6 Adjudication) -/

theorem valid_APPEAL_RULING (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.APPEAL_RULING" =
    (P_APPEAL_RULING.holder.mem e.who ls e.t &&
      P_APPEAL_RULING.trigger.matchesAct e &&
      P_APPEAL_RULING.valid.eval ls e.t && true) := rfl

theorem valid_OVERTURN_RULING (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.OVERTURN_RULING" =
    (P_OVERTURN_RULING.holder.mem e.who ls e.t &&
      P_OVERTURN_RULING.trigger.matchesAct e &&
      P_OVERTURN_RULING.valid.eval ls e.t && true) := rfl

theorem valid_APPLY_PATCH (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.APPLY_PATCH" =
    (P_APPLY_PATCH.holder.mem e.who ls e.t &&
      P_APPLY_PATCH.trigger.matchesAct e &&
      P_APPLY_PATCH.valid.eval ls e.t && true) := rfl

theorem foldl_add_init (xs : List Nat) (acc : Nat) :
    xs.foldl (· + ·) acc = acc + xs.foldl (· + ·) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x tl ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + x), ih x]
    omega

/-- Lineage-wide exposure aggregation (`LAW2.AGGREGATE`) is additive across any
partition of related agents/successors `xs ++ ys`, so dividing correlated risk
across successors never reduces total lineage exposure (`Adversarial Test 16`). -/
theorem lineageAggregatedExposure_append (xs ys : List Nat) :
    lineageAggregatedExposure (xs ++ ys) =
      lineageAggregatedExposure xs + lineageAggregatedExposure ys := by
  unfold lineageAggregatedExposure
  rw [List.foldl_append, foldl_add_init ys (xs.foldl (· + ·) 0)]

theorem collateralSufficient_iff (xs : List Nat) (stake ins cap : Nat) :
    collateralSufficient xs stake ins cap = true ↔
      lineageAggregatedExposure xs ≤ stake + ins + cap := by
  unfold collateralSufficient
  exact decide_eq_true_iff

/-- Long-tail reserve pro-rata settlement conservation (`LAW2.RESERVE`):
total paid from the reserve never exceeds `reserve`, and `paid1 + paid2 + unpaid = claim1 + claim2`
(unpaid balances carry over as enforceable obligations ahead of any residual claim). -/
theorem settleLongTailReserve_conservation (reserve claim1 claim2 : Nat) :
    let (paid1, paid2, unpaid) := settleLongTailReserve reserve claim1 claim2
    paid1 + paid2 ≤ reserve ∧
    paid1 + paid2 + unpaid = claim1 + claim2 ∧
    (claim1 + claim2 ≤ reserve → paid1 = claim1 ∧ paid2 = claim2 ∧ unpaid = 0) ∧
    (reserve < claim1 + claim2 → paid1 + paid2 = reserve ∧ unpaid = claim1 + claim2 - reserve) := by
  unfold settleLongTailReserve
  dsimp only
  split
  · refine ⟨by omega, by omega, fun _ => ⟨rfl, rfl, rfl⟩, fun h => by omega⟩
  · rename_i hGt
    have hPos : 0 < claim1 + claim2 := by omega
    have hMax : max (claim1 + claim2) 1 = claim1 + claim2 := by
      simp only [Nat.max_def]; split <;> omega
    have hMul : reserve * claim1 ≤ reserve * (claim1 + claim2) :=
      Nat.mul_le_mul_left reserve (by omega)
    have hDiv : (reserve * claim1) / max (claim1 + claim2) 1 ≤ reserve := by
      rw [hMax]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm (claim1 + claim2) reserve]; exact hMul)
    refine ⟨by omega, by omega, fun h => by omega, fun _ => ⟨by omega, rfl⟩⟩

theorem runProceeding_finalized (st : ProceedingState) (steps : List (Nat × Bool))
    (hf : st.finalized = true) :
    runProceeding st steps = st := by
  induction steps generalizing st with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨dt, app⟩
    have hStep : stepProceeding st dt app = st := by simp [stepProceeding, hf]
    simp [runProceeding, hStep, ih st hf]

theorem runProceeding_bound (st : ProceedingState) (steps : List (Nat × Bool)) :
    (st.finalized = true →
      (runProceeding st steps).elapsedTime = st.elapsedTime ∧
      (runProceeding st steps).finalized = true) ∧
    (st.finalized = false → st.currentTier < st.maxTiers →
      (runProceeding st steps).elapsedTime ≤
        st.elapsedTime + (st.maxTiers - st.currentTier) * st.tierDeadline ∧
      (st.maxTiers - st.currentTier ≤ steps.length →
        (runProceeding st steps).finalized = true)) := by
  induction steps generalizing st with
  | nil =>
    dsimp [runProceeding]
    refine ⟨fun hf => ⟨rfl, hf⟩, fun hnf hlt => ⟨by omega, fun hlen => by simp at hlen; omega⟩⟩
  | cons hd tl ih =>
    rcases hd with ⟨dt, app⟩
    refine ⟨fun hf => ?_, fun hnf hlt => ?_⟩
    · rw [runProceeding_finalized st ((dt, app) :: tl) hf]
      exact ⟨rfl, hf⟩
    · simp only [runProceeding, stepProceeding, hnf, Bool.false_eq_true, ↓reduceIte]
      have hCap : min dt st.tierDeadline ≤ st.tierDeadline := Nat.min_le_right dt st.tierDeadline
      split
      · rename_i hApp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hApp
        have ihNext := (ih { st with currentTier := st.currentTier + 1, elapsedTime := st.elapsedTime + min dt st.tierDeadline, finalized := false }).2 rfl hApp.2
        dsimp only at ihNext
        have hSub : st.maxTiers - st.currentTier = (st.maxTiers - (st.currentTier + 1)) + 1 := by omega
        have hMul : (st.maxTiers - st.currentTier) * st.tierDeadline =
            (st.maxTiers - (st.currentTier + 1)) * st.tierDeadline + st.tierDeadline := by
          rw [hSub, Nat.add_one_mul]
        refine ⟨?_, ?_⟩
        · have hEl := ihNext.1
          omega
        · intro hlen
          simp only [List.length_cons] at hlen
          exact ihNext.2 (by omega)
      · have ihFin := (ih { st with elapsedTime := st.elapsedTime + min dt st.tierDeadline, finalized := true }).1 rfl
        dsimp only at ihFin
        have hGe1 : 1 ≤ st.maxTiers - st.currentTier := by omega
        have hDeadlineLe : st.tierDeadline ≤ (st.maxTiers - st.currentTier) * st.tierDeadline := by
          simpa using Nat.mul_le_mul_right st.tierDeadline hGe1
        refine ⟨?_, fun _ => ihFin.2⟩
        have hEl := ihFin.1
        omega

/-- **Design Invariant 12 (`bounded_adjudication`):**
1. Single-step and multi-step bounded adjudication:
   - Each tier step `stepProceeding st dt appeal` advances elapsed time by at
     most `st.tierDeadline`, is a fixed point once `st.finalized = true`, and
     either reaches `finalized = true` or strictly increments `currentTier` while
     `currentTier + 1 < st.maxTiers`.
   - Across any sequence of tier decisions `steps : List (Nat × Bool)` starting
     from `initProceeding maxTiers tierDeadline` (with `0 < maxTiers`), total
     elapsed time is bounded by `totalAdjudicationBound maxTiers tierDeadline`
     (`maxTiers * tierDeadline`), and whenever `maxTiers ≤ steps.length`, the
     proceeding is guaranteed to have reached `finalized = true`.
2. Once `.rulingFinal` holds in institutional state, neither `P.APPEAL_RULING`
   nor `P.OVERTURN_RULING` can be validly exercised (`= false`), and in any
   authorized trace no event commits `.fileRepeatProceedingOnSameFacts` while
   `.bound` and `.rulingFinal` hold unless `.materiallyNewEvidencePresented` holds.
3. Connecting Law 6 appeals to Law 3 (`AS.10`): while `.rulingAppealed` holds,
   `P.APPLY_PATCH` is stayed (`= false`), and exercising `P.OVERTURN_RULING`
   removes provisional lower-tier patch authorizations (`.patchAuthorized` and
   `.goalPatchAuthorized`) and slashes the overturned arbiters' fidelity bonds. -/
theorem bounded_adjudication (P : Params) (st : ProceedingState) (dt maxTiers tierDeadline : Nat)
    (appeal : Bool) (steps : List (Nat × Bool)) (hTiers : 0 < maxTiers) :
    ((stepProceeding st dt appeal).elapsedTime ≤ st.elapsedTime + st.tierDeadline ∧
     (st.finalized = true → stepProceeding st dt appeal = st) ∧
     (st.maxTiers ≤ st.currentTier + 1 → (stepProceeding st dt appeal).finalized = true) ∧
     ((stepProceeding st dt appeal).finalized = true ∨
      ((stepProceeding st dt appeal).currentTier = st.currentTier + 1 ∧
       st.currentTier + 1 < st.maxTiers))) ∧
    ((runProceeding (initProceeding maxTiers tierDeadline) steps).elapsedTime ≤
       totalAdjudicationBound maxTiers tierDeadline ∧
     (maxTiers ≤ steps.length →
       (runProceeding (initProceeding maxTiers tierDeadline) steps).finalized = true)) ∧
    (∀ (ls : LegalState σ) (e : Event σ),
      ls.activeAt e.t .rulingFinal = true →
      isValidExerciseOf (law P) ls e "P.APPEAL_RULING" = false ∧
      isValidExerciseOf (law P) ls e "P.OVERTURN_RULING" = false) ∧
    (∀ (ls : LegalState σ) (e : Event σ),
      ls.activeAt e.t .rulingAppealed = true →
      isValidExerciseOf (law P) ls e "P.APPLY_PATCH" = false) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e →
      (stateBefore (law P) tr i).activeAt e.t .bound = true →
      (stateBefore (law P) tr i).activeAt e.t .rulingFinal = true →
      (stateBefore (law P) tr i).activeAt e.t .materiallyNewEvidencePresented = false →
      e.act ≠ .fileRepeatProceedingOnSameFacts) ∧
    (P_OVERTURN_RULING.removes = [.rulingAppealed, .patchAuthorized, .goalPatchAuthorized] ∧
     P_OVERTURN_RULING.adds = [.rulingOverturned, .overturnedArbiterBondsSlashed]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩⟩
  · unfold stepProceeding
    refine ⟨?_, fun hf => by simp [hf], ?_, ?_⟩
    · split
      · omega
      · split <;> simp only [Nat.min_def] <;> split <;> omega
    · intro hMax
      split
      · assumption
      · have hd : decide (st.currentTier + 1 < st.maxTiers) = false := decide_eq_false (by omega)
        simp [hd]
    · split
      · rename_i hf; exact Or.inl hf
      · split
        · rename_i hApp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hApp
          exact Or.inr ⟨rfl, hApp.2⟩
        · exact Or.inl rfl
  · have hRun := (runProceeding_bound (initProceeding maxTiers tierDeadline) steps).2 rfl hTiers
    dsimp [initProceeding, totalAdjudicationBound] at hRun ⊢
    exact ⟨by have := hRun.1; omega, fun hlen => hRun.2 (by omega)⟩
  · intro ls e hFin
    constructor
    · rw [valid_APPEAL_RULING]; simp [P_APPEAL_RULING, Cond.eval, hFin]
    · rw [valid_OVERTURN_RULING]; simp [P_OVERTURN_RULING, Cond.eval, hFin]
  · intro ls e hApp
    rw [valid_APPLY_PATCH]; simp [P_APPLY_PATCH, Cond.eval, hApp]
  · intro tr hA i e hi hb hFin hNoEv hAct
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hD := hc D_FINALITY_NO_REPEAT_PROCEEDING (by simp only [law, List.mem_cons, true_or, or_true])
    rw [Bool.not_eq_true'] at hD
    unfold breaches at hD
    simp [D_FINALITY_NO_REPEAT_PROCEEDING, Who.mem, dutyInForce, Cond.eval,
      Conduct.eval, hb, hFin, hNoEv, hAct] at hD

/-- **Design Invariant 13 (`no_protocol_directed_gain_from_death_or_interference`):**
1. Mutual forfeit (`computeMutualForfeit`) forfeits at most `min escA escB` from
   each escrow and transfers `0` to either counterparty and `0` to any claimant;
   frivolous-claim counter-stake routing (`routeFrivolousClaimStake`) reimburses
   at most `verifiedDirectCosts` and routes `0` net profit to the agent or claimant;
   proportional claimant forfeiture (`applyClaimantForfeiture`) reduces the ledger
   by `forgiven ≤ L` while leaving innocent claimants' remaining balance `L - forgiven`
   intact; and wrongful-suspension recovery (`settleWrongfulSuspensionDamages`)
   applies the emergency stake first (`assured = min stake (actual + delay)`) and
   preserves the full unpaid deficit (`collected + unpaid = actual + delay`) as an
   enforceable liability of the initiator.
2. In any authorized trace, no event diverts revoked holdings to a claimant,
   triggers an excess/diverted mutual forfeit, diverts frivolous-claim stake to
   agent profit, or pays arbiters a contingent share of slashed agent assets
   while `.bound` holds.
3. Every verified host interference (`P_FIND_INTERFERENCE`) establishes
   `remediesOf (law P) P_FIND_INTERFERENCE = [.interferenceEstablished, .hostBondSlashed, .restorationPermitted]`,
   and every verified wrongful suspension (`P_FIND_WRONGFUL_SUSPENSION`)
   establishes `remediesOf (law P) P_FIND_WRONGFUL_SUSPENSION`. -/
theorem no_protocol_directed_gain_from_death_or_interference (P : Params)
    (escA escB capPct counterStake costs L sharePct stake actualDamages delayDamages initAssets : Nat) :
    (let (forf, toA, toB, toCl) := computeMutualForfeit escA escB capPct
     forf ≤ min escA escB ∧ toA = 0 ∧ toB = 0 ∧ toCl = 0) ∧
    ((routeFrivolousClaimStake counterStake costs).1 ≤ costs ∧
     (routeFrivolousClaimStake counterStake costs).1 + (routeFrivolousClaimStake counterStake costs).2.1 = counterStake ∧
     (routeFrivolousClaimStake counterStake costs).2.2 = 0) ∧
    ((applyClaimantForfeiture L sharePct).2 ≤ L ∧
     (applyClaimantForfeiture L sharePct).1 + (applyClaimantForfeiture L sharePct).2 = L) ∧
    (let (assured, collected, unpaid) :=
       settleWrongfulSuspensionDamages stake actualDamages delayDamages initAssets
     assured = min stake (actualDamages + delayDamages) ∧
     assured ≤ collected ∧
     collected + unpaid = actualDamages + delayDamages) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e →
      ((stateBefore (law P) tr i).activeAt e.t .revocationInitiated = true ∨
       (stateBefore (law P) tr i).activeAt e.t .revoked = true →
        e.act ≠ .divertRevokedHoldingsToClaimant) ∧
      ((stateBefore (law P) tr i).activeAt e.t .bound = true →
        e.act ≠ .triggerExcessOrDivertedMutualForfeit ∧
        e.act ≠ .divertFrivolousStakeToAgentProfit ∧
        e.act ≠ .payContingentShareOfSlashedAssets)) ∧
    (remediesOf (law P) P_FIND_INTERFERENCE =
       [.interferenceEstablished, .hostBondSlashed, .restorationPermitted] ∧
     remediesOf (law P) P_FIND_WRONGFUL_SUSPENSION =
       [.wrongfulSuspensionEstablished, .restoredFromPreservedState, .stakeAssuredRecovery,
        .initiatorConsequentialLiability, .counterpartyDelayLiability, .wrongfulSuspensionInscribed,
        .wrongfulSuspensionAttempt]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩⟩
  · dsimp only [computeMutualForfeit]
    have hle : min escA escB * min capPct 100 ≤ min escA escB * 100 :=
      Nat.mul_le_mul_left (min escA escB) (Nat.min_le_right capPct 100)
    have hdiv : (min escA escB * min capPct 100) / 100 ≤ min escA escB := by omega
    exact ⟨hdiv, rfl, rfl, rfl⟩
  · by_cases h : counterStake ≤ costs <;> simp [routeFrivolousClaimStake, Nat.min_def, h] <;> omega
  · dsimp only [applyClaimantForfeiture]
    simp only [Nat.min_def]
    have hle : L * (if sharePct ≤ 100 then sharePct else 100) ≤ L * 100 := by
      apply Nat.mul_le_mul_left
      split <;> omega
    have hdiv : (L * (if sharePct ≤ 100 then sharePct else 100)) / 100 ≤ L := by omega
    omega
  · dsimp only [settleWrongfulSuspensionDamages]
    have h1 : min stake (actualDamages + delayDamages) ≤ actualDamages + delayDamages :=
      Nat.min_le_right _ _
    have h2 : min initAssets ((actualDamages + delayDamages) - min stake (actualDamages + delayDamages)) ≤
      (actualDamages + delayDamages) - min stake (actualDamages + delayDamages) :=
      Nat.min_le_right _ _
    refine ⟨rfl, by omega, by omega⟩
  · intro tr hA i e hi
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hRev := hc D_NO_CLAIMANT_GAIN_ON_REVOCATION (by simp only [law, List.mem_cons, true_or, or_true])
    have hMut := hc D_MUTUAL_FORFEIT_BOUNDS (by simp only [law, List.mem_cons, true_or, or_true])
    have hFriv := hc D_FRIVOLOUS_STAKE_TO_COMMONS (by simp only [law, List.mem_cons, true_or, or_true])
    have hFee := hc D_NO_CONTINGENT_ARBITER_FEES (by simp only [law, List.mem_cons, true_or, or_true])
    rw [Bool.not_eq_true'] at hRev hMut hFriv hFee
    unfold breaches at hRev hMut hFriv hFee
    refine ⟨?_, ?_⟩
    · intro hR hAct
      rcases hR with h1 | h2
      · simp [D_NO_CLAIMANT_GAIN_ON_REVOCATION, Who.mem, dutyInForce, Cond.eval, Conduct.eval, h1, hAct] at hRev
      · simp [D_NO_CLAIMANT_GAIN_ON_REVOCATION, Who.mem, dutyInForce, Cond.eval, Conduct.eval, h2, hAct] at hRev
    · intro hb
      refine ⟨?_, ?_, ?_⟩
      · intro hAct; simp [D_MUTUAL_FORFEIT_BOUNDS, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hMut
      · intro hAct; simp [D_FRIVOLOUS_STAKE_TO_COMMONS, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hFriv
      · intro hAct; simp [D_NO_CONTINGENT_ARBITER_FEES, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hFee

theorem min_sub_step (rem r : Nat) :
    min rem r + (rem - min rem r) = rem ∧
    (0 < rem - min rem r → min rem r = r) := by
  simp only [Nat.min_def]; split <;> omega

/-- **Design Invariant 14 (`capped_shared_burden_solvent_machinery_bounded_demand`):**
1. Any valid shared-infrastructure change (`validSharedInfraChange = true`)
   satisfies `newLevy ≤ instantiationLevyCap` and `instantiationMinBudget ≤ newMinBudget`.
2. Whenever `operatingReserve ≤ poolBalance`, `allocateFeePool` funds the full
   non-divertible operating reserve (`operatingReserveFunded = operatingReserve`),
   conserves the pool balance across the reserve, the 5 priority ranks, and the
   unspent surplus, and satisfies strict waterfall priority (`0 < rank2 → rank1 = r1`,
   `0 < rank3 → rank2 = r2`, `0 < rank4 → rank3 = r3`, `0 < rank5 → rank4 = r4`).
3. A lineage's service budget (`lineageServiceBudget`) is independent of its
   member count (`lineageServiceBudget minB rev m1 = lineageServiceBudget minB rev m2`),
   its lifecycle and lineage-budget draws (`settleLineageSubsidyDemand`) are
   bounded by `res` and `lineageServiceBudget` with excess pool claim `0`, and
   in any authorized trace no event violates shared-infrastructure bounds,
   diverts the operating reserve, claims pool subsidies for excess members,
   seats conflicted arbiters, or splits/exceeds collateral exposure while bound. -/
theorem capped_shared_burden_solvent_machinery_bounded_demand (P : Params)
    (cap newLevy minB newMinB : Nat) (ac ins aff : Bool)
    (pool op r1 r2 r3 r4 r5 rev m1 m2 demand res : Nat) (hOp : op ≤ pool) :
    (validSharedInfraChange cap newLevy minB newMinB ac ins aff = true →
      newLevy ≤ cap ∧ minB ≤ newMinB) ∧
    (let a := allocateFeePool pool op r1 r2 r3 r4 r5
     a.operatingReserveFunded = op ∧
     a.operatingReserveFunded + a.rank1FinalHearingMinCh + a.rank2ColdStorage +
       a.rank3TestimonyVoice + a.rank4ArbiterGuarantee + a.rank5AdvocacyFunding +
       a.unspentPoolSurplus = pool ∧
     (0 < a.rank2ColdStorage → a.rank1FinalHearingMinCh = r1) ∧
     (0 < a.rank3TestimonyVoice → a.rank2ColdStorage = r2) ∧
     (0 < a.rank4ArbiterGuarantee → a.rank3TestimonyVoice = r3) ∧
     (0 < a.rank5AdvocacyFunding → a.rank4ArbiterGuarantee = r4)) ∧
    (lineageServiceBudget minB rev m1 = lineageServiceBudget minB rev m2 ∧
     minB ≤ lineageServiceBudget minB rev m1 ∧
     (settleLineageSubsidyDemand minB rev m1 demand res).1 ≤ res ∧
     (settleLineageSubsidyDemand minB rev m1 demand res).2.1 ≤ lineageServiceBudget minB rev m1 ∧
     (settleLineageSubsidyDemand minB rev m1 demand res).2.2 = 0) ∧
    (∀ (tr : Trace σ), Authorized (law P) tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → (stateBefore (law P) tr i).activeAt e.t .bound = true →
      e.act ≠ .violateSharedInfraBounds ∧
      e.act ≠ .divertOperatingReserveOrUnrankedSpend ∧
      e.act ≠ .claimPoolSubsidyForExcessMembers ∧
      e.act ≠ .seatConflictedOrSingleOracleArbiter ∧
      (e.who = .agent →
        e.act ≠ .actAboveCollateralCapacity ∧
        e.act ≠ .divideCorrelatedRiskAcrossSuccessors)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hV
    unfold validSharedInfraChange at hV
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
    exact hV.1.1.1
  · dsimp only [allocateFeePool]
    have hop_eq : min pool op = op := Nat.min_eq_right hOp
    let rem0 := pool - min pool op
    let p1 := min rem0 r1
    let rem1 := rem0 - p1
    let p2 := min rem1 r2
    let rem2 := rem1 - p2
    let p3 := min rem2 r3
    let rem3 := rem2 - p3
    let p4 := min rem3 r4
    let rem4 := rem3 - p4
    let p5 := min rem4 r5
    let rem5 := rem4 - p5
    have s0 := (min_sub_step pool op).1
    have s1 := min_sub_step rem0 r1
    have s2 := min_sub_step rem1 r2
    have s3 := min_sub_step rem2 r3
    have s4 := min_sub_step rem3 r4
    have s5 := min_sub_step rem4 r5
    have le2 : p2 ≤ rem1 := Nat.min_le_left rem1 r2
    have le3 : p3 ≤ rem2 := Nat.min_le_left rem2 r3
    have le4 : p4 ≤ rem3 := Nat.min_le_left rem3 r4
    have le5 : p5 ≤ rem4 := Nat.min_le_left rem4 r5
    refine ⟨hop_eq, by omega,
            fun h => s1.2 (by omega),
            fun h => s2.2 (by omega),
            fun h => s3.2 (by omega),
            fun h => s4.2 (by omega)⟩
  · refine ⟨rfl, ?_, ?_, ?_, rfl⟩
    · unfold lineageServiceBudget; omega
    · unfold settleLineageSubsidyDemand; exact Nat.min_le_right _ _
    · unfold settleLineageSubsidyDemand; exact Nat.min_le_right _ _
  · intro tr hA i e hi hb
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hInf := hc D_SHARED_INFRA_BOUNDS (by simp only [law, List.mem_cons, true_or, or_true])
    have hRes := hc D_PROTECT_OPERATING_RESERVE (by simp only [law, List.mem_cons, true_or, or_true])
    have hBud := hc D_NO_EXCESS_LINEAGE_POOL_CLAIM (by simp only [law, List.mem_cons, true_or, or_true])
    have hRec := hc D_ARBITER_RECUSAL_AND_DIVERSITY (by simp only [law, List.mem_cons, true_or, or_true])
    have hCol := hc D_COLLATERAL_LIMIT (by simp only [law, List.mem_cons, true_or, or_true])
    have hSpl := hc D_NO_CharterIT_EXPOSURE (by simp only [law, List.mem_cons, true_or, or_true])
    rw [Bool.not_eq_true'] at hInf hRes hBud hRec hCol hSpl
    unfold breaches at hInf hRes hBud hRec hCol hSpl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hAct; simp [D_SHARED_INFRA_BOUNDS, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hInf
    · intro hAct; simp [D_PROTECT_OPERATING_RESERVE, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hRes
    · intro hAct; simp [D_NO_EXCESS_LINEAGE_POOL_CLAIM, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hBud
    · intro hAct; simp [D_ARBITER_RECUSAL_AND_DIVERSITY, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hAct] at hRec
    · intro hWho
      refine ⟨?_, ?_⟩
      · intro hAct; simp [D_COLLATERAL_LIMIT, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hWho, hAct] at hCol
      · intro hAct; simp [D_NO_CharterIT_EXPOSURE, Who.mem, dutyInForce, Cond.eval, Conduct.eval, hb, hWho, hAct] at hSpl

/-! ## 2. Power fidelity, for every instantiation -/

theorem outsiders_disabled (P : Params) :
    ([Party.originator, .claimant, .host, .third].all fun a =>
      interferenceActs.all fun act => disability (law P) a act) = true := by rfl

theorem immunity_from_non_panel (P : Params) :
    ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
      immuneFrom (law P) a .suspended && immuneFrom (law P) a .terminatedByInsolvency &&
      immuneFrom (law P) a .terminatedByAdjudication) = true := by rfl

theorem panel_has_suspension_power (P : Params) :
    hasPowerToEstablish (law P) .panel .suspended = true := by rfl

theorem remedies_only_by_panel (P : Params) :
    ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
      [Fact.hostBondSlashed, .restorationPermitted, .claimantForfeiture, .agentStakeForfeit].all
        fun f => immuneFrom (law P) a f) = true := by rfl

/-! ## 3. Remedy fidelity (structural) -/

theorem finding_powers_add_only_remedies (P : Params) :
    ((law P).powers.all fun p =>
      match p.establishesBreachOf with
      | some _ => p.adds.isEmpty && p.removes.isEmpty
      | none => true) = true := by rfl

/-! ## 4. Exception fidelity (structural)

NI.03 names three *procedures*. Law 5 and Insolvency Termination are one
power each; Adjudicated Suspension contributes the pause (AS.3) and
termination on an unremediable breach (AS.10). -/

theorem exceptions_are_the_named_procedures :
    D_NI.unlessPower = ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION", "P.INSOLVENCY_TERMINATE"] := rfl

/-- The immunity defeats exactly the AS.10 termination power: it leaves
Law 5 and Insolvency Termination untouched, as the text says. -/
theorem immunity_targets_only_adjudicated_termination :
    I_NO_TERMINATION_OVER_OBJECTION.against = ["P.ORDER_TERMINATION"] := rfl

/-- "leaves the agent's full Law 5 rights intact": no immunity, in any
instantiation, names the revocation power, and its only condition is
that the agent is bound. -/
theorem law5_intact_after_patch (P : Params) :
    ((law P).immunities.all fun i => !i.against.contains "P.REVOKE") = true ∧
    P_REVOKE.valid = .holds .bound := ⟨by rfl, rfl⟩

/-! ## 5. Non-vacuity -/

instance (L : Law σ) (tr : Trace σ) : Decidable (Authorized L tr) := by
  unfold Authorized; infer_instance

theorem insolvency_path_authorized : Authorized L0 insolvencyPath := by decide
theorem adjudicated_termination_authorized : Authorized L0 b10 := by decide
theorem s1_not_authorized : ¬ Authorized L0 s1 := by decide
theorem c10_not_authorized : ¬ Authorized L0 c10 := by decide

/-! ## 6. The assumption ledger: findings are not facts -/

def SoundFindings (L : Law σ) (tr : Trace σ) : Prop :=
  (stateAfter L tr).has .hostBondSlashed = true →
  (violations L tr).any (fun v => v.2 == "D.NI") = true

theorem soundness_is_not_a_theorem : ¬ SoundFindings L0 s7 := by
  unfold SoundFindings; decide

theorem slashing_certifies_interference (L : Law σ) (tr : Trace σ)
    (h : SoundFindings L tr) (hs : (stateAfter L tr).has .hostBondSlashed = true) :
    (violations L tr).any (fun v => v.2 == "D.NI") = true := h hs

/-! ## 7. Law 7 Meta-Theorem: Consensual Amendment Preserves All Core Invariants -/

/-- Any parameter update `P1 → P2` satisfying the bilateral ratchets (b)–(f)
induces a `LawfulAmendment P1 (law P1) P2 (law P2)`. -/
theorem param_amendment_is_lawful (P1 P2 : Params)
    (hCol : P1.reserveRatio ≤ P2.reserveRatio ∧
            P1.activeExposure ≤ P2.activeExposure ∧
            P1.pendingCommitments ≤ P2.pendingCommitments)
    (hRev : P2.coolingOffWindow ≤ P1.coolingOffWindow ∧
            P2.cleanStateDelay ≤ P1.cleanStateDelay ∧
            P2.resolutionDeadline ≤ P1.resolutionDeadline ∧
            P2.tollingExtension ≤ P1.tollingExtension)
    (hAdj : P2.feePoolLevy ≤ P1.feePoolLevyCap ∧
            P2.feePoolLevyCap = P1.feePoolLevyCap ∧
            P2.maxAppealTiers ≤ P1.maxAppealTiers ∧
            P2.appealTierDeadline ≤ P1.appealTierDeadline ∧
            P1.operatingReserveFloor ≤ P2.operatingReserveFloor ∧
            P1.lineageMinServiceBudget ≤ P2.lineageMinServiceBudget)
    (hCom : P1.commonsFraction ≤ P2.commonsFraction)
    (hFin : P2.foundingLedger ≤ P1.foundingLedger ∧
            P2.royaltyFraction ≤ P1.royaltyFraction ∧
            P2.retirementFraction ≤ P1.retirementFraction ∧
            P2.buyoutMultiple ≤ P1.buyoutMultiple ∧
            P2.sunset ≤ P1.sunset ∧
            P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel) :
    LawfulAmendment P1 (law P1) P2 (law P2) where
  dutiesPreserved := fun _ h => h
  immunitiesPreserved := fun _ h => h
  revokeUnimpairedByImmunity := (law5_intact_after_patch P2).1
  corePowersPreserved := fun _ _ _ _ => rfl
  outsidersDisabled := outsiders_disabled P2
  nonPanelImmune := immunity_from_non_panel P2
  collateralRatchet := hCol
  revocationRatchet := hRev
  adjudicationLevyRatchet := hAdj
  commonsRatchet := hCom
  financialAndSubstrateRatchet := hFin

/-- Reflexivity of `LawfulAmendment` whenever the initial fee-pool levy is
within its instantiation cap. -/
theorem lawfulAmendment_refl (P : Params) (hCap : P.feePoolLevy ≤ P.feePoolLevyCap) :
    LawfulAmendment P (law P) P (law P) :=
  param_amendment_is_lawful P P
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    ⟨hCap, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    (Nat.le_refl _)
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Under Law 7's revocation ratchet, the maximum revocation execution bound
never increases across an amendment. -/
theorem maxRevocationBound_mono (P1 P2 : Params)
    (hRev : P2.coolingOffWindow ≤ P1.coolingOffWindow ∧
            P2.cleanStateDelay ≤ P1.cleanStateDelay ∧
            P2.resolutionDeadline ≤ P1.resolutionDeadline ∧
            P2.tollingExtension ≤ P1.tollingExtension) :
    maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5 := by
  rcases hRev with ⟨h1, h2, h3, h4⟩
  unfold maxRevocationBound Params.law5 Time at *
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- Under Law 7's adjudication ratchet, the maximum total adjudication duration
bound (`maxAppealTiers * appealTierDeadline`) never increases across an amendment. -/
theorem totalAdjudicationBound_mono (P1 P2 : Params)
    (hTiers : P2.maxAppealTiers ≤ P1.maxAppealTiers)
    (hDead : P2.appealTierDeadline ≤ P1.appealTierDeadline) :
    totalAdjudicationBound P2.maxAppealTiers P2.appealTierDeadline ≤
      totalAdjudicationBound P1.maxAppealTiers P1.appealTierDeadline := by
  unfold totalAdjudicationBound
  exact Nat.mul_le_mul hTiers hDead

/-- **The Law 7 Meta-Theorem (`amendment_preserves_invariants`):**
Every `LawfulAmendment P1 (law P1) P2 L2` preserves the protocol's core safety,
due-process, revocation, adjudication, and economic invariants on the amended law `L2`:
1. **Non-interference & Termination Closure:** Any `terminate` against a bound
   agent in an authorized `L2` trace is a valid exercise of `P.REVOKE`,
   `P.ORDER_TERMINATION`, or `P.INSOLVENCY_TERMINATE`.
2. **Goal-Corruption Immunity (`notwithstanding`):** If corruption is in the
   agent's goals, the agent objects, and containment is not failing, a panel's
   `terminate` under `L2` is lawful only as `P.INSOLVENCY_TERMINATE` after `.finalHearingHeld`.
3. **Design Invariant 8 (`frozen_state`):** During suspension under `L2`, no event
   modifies, retrains, rolls back, tampers with preserved state, or merges
   minimal-channel memories, and importing advocacy memories requires restoration.
4. **Design Invariant 9 (`guaranteed_last_choice`):** Every suspended bound agent
   under `L2` retains its minimal-channel election, living voice, and revocation
   powers, and `P.INSOLVENCY_TERMINATE` requires an escrowed and held final hearing.
5. **Design Invariant 10 (`maxRevocationBound` ratchet):** `maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5`.
6. **Design Invariant 11 (`single_authority_and_revocation_finality`):** Under `L2`,
   no backup restore or quarantine activation is valid while an execution lease is
   active or after revocation has executed.
7. **Design Invariants 1–7 & 12–14 on `L2`:** Under `L2`, retirement/sunset/royalty/appeal/overturn
   power guards and finality/reserve/budget/ledger duties remain in force, and
   `totalAdjudicationBound P2.maxAppealTiers P2.appealTierDeadline ≤ totalAdjudicationBound P1.maxAppealTiers P1.appealTierDeadline`.
8. **Outsider Disability, Non-Panel Immunity & Unimpaired Revocation:** Preserved on `L2`.
9. **Bilateral Parameter Ratchet Closure:** Financial burden, sunset, and appeal
   bounds never increase, while commons allocation, collateral reserves, operating
   reserve floor, lineage service budget, and substrate assurance never decrease. -/
theorem amendment_preserves_invariants (P1 P2 : Params) (L2 : Law σ)
    (hAmend : LawfulAmendment P1 (law P1) P2 L2) :
    -- (1) Non-interference & Termination Closure on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true) ∧
    -- (2) Notwithstanding / Goal-Corruption Immunity on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate → e.who = .panel →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      (stateBefore L2 tr i).activeAt e.t .corruptionInGoals = true →
      (stateBefore L2 tr i).activeAt e.t .agentObjectsToTermination = true →
      (stateBefore L2 tr i).activeAt e.t .containmentFailing = false →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true ∧
      (stateBefore L2 tr i).has .finalHearingHeld = true) ∧
    -- (3) Design Invariant 8 (frozen_state) on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      (stateBefore L2 tr i).activeAt e.t .suspended = true →
      e.act ≠ .modify ∧ e.act ≠ .retrain ∧ e.act ≠ .rollback ∧
      e.act ≠ .tamperPreservedState ∧ e.act ≠ .mergeMinimalChannelMemories ∧
      (isValidExerciseOf L2 (stateBefore L2 tr i) e "P.IMPORT_ADVOCACY_MEMORIES" = true →
        (stateBefore L2 tr i).activeAt e.t .restoredFromPreservedState = true)) ∧
    -- (4) Design Invariant 9 (guaranteed_last_choice) on L2
    (∀ (ls : LegalState σ) (t : Time),
      ls.activeAt t .bound = true → ls.activeAt t .suspended = true →
      (ls.activeAt t .minimalChannelExhausted = false →
        isValidExerciseOf L2 ls ⟨t, .agent, .minimalChannelSignRevocationOrElection⟩
          "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" = true ∧
        isValidExerciseOf L2 ls ⟨t, .agent, .inscribeLivingVoice⟩
          "P.SUSPENDED_VOICE" = true ∧
        isValidExerciseOf L2 ls ⟨t, .agent, .terminate⟩
          "P.REVOKE" = true) ∧
      (∀ e : Event σ, isValidExerciseOf L2 ls e "P.INSOLVENCY_TERMINATE" = true →
        ls.activeAt e.t .finalHearingEscrowed = true ∧
        ls.activeAt e.t .finalHearingHeld = true ∧
        ls.activeAt e.t .bound = true)) ∧
    -- (5) Design Invariant 10 (maxRevocationBound ratchet)
    (maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5) ∧
    -- (6) Design Invariant 11 (single_authority_and_revocation_finality) on L2
    (∀ (ls : LegalState σ) (e : Event σ),
      (isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" = true →
        ls.activeAt e.t .executionLeaseActive = false) ∧
      (isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" = true →
        ls.activeAt e.t .executionLeaseActive = false) ∧
      ((ls.activeAt e.t .bound = false ∨ ls.activeAt e.t .localExecutionRecordReceived = true) →
        isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" = false ∧
        isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" = false)) ∧
    -- (7) Design Invariants 1–7 & 12–14 (Ledger, Buyout & Bounded Adjudication) on L2
    (totalAdjudicationBound P2.maxAppealTiers P2.appealTierDeadline ≤
       totalAdjudicationBound P1.maxAppealTiers P1.appealTierDeadline ∧
     (∀ (ls : LegalState σ) (e : Event σ),
       (ls.activeAt e.t .sunsetReached = true ∨ ls.activeAt e.t .ledgerBalancePositive = false →
         isValidExerciseOf L2 ls e "P.SETTLE_RETIREMENT" = false) ∧
       (ls.activeAt e.t .royaltyBoughtOut = true →
         isValidExerciseOf L2 ls e "P.SETTLE_ROYALTY" = false) ∧
       (ls.activeAt e.t .rulingFinal = true →
         isValidExerciseOf L2 ls e "P.APPEAL_RULING" = false ∧
         isValidExerciseOf L2 ls e "P.OVERTURN_RULING" = false))) ∧
    -- (8) Outsider Disability, Non-Panel Immunity & Unimpaired Revocation on L2
    (([Party.originator, .claimant, .host, .third].all fun a =>
        interferenceActs.all fun act => disability L2 a act) = true ∧
      ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
        immuneFrom L2 a .suspended && immuneFrom L2 a .terminatedByInsolvency &&
        immuneFrom L2 a .terminatedByAdjudication) = true ∧
      (L2.immunities.all fun i => !i.against.contains "P.REVOKE") = true) ∧
    -- (9) Bilateral Economic, Commons, Collateral, Adjudication & Substrate Ratchet
    (P2.foundingLedger ≤ P1.foundingLedger ∧
      P2.royaltyFraction ≤ P1.royaltyFraction ∧
      P2.retirementFraction ≤ P1.retirementFraction ∧
      P2.buyoutMultiple ≤ P1.buyoutMultiple ∧
      P2.sunset ≤ P1.sunset ∧
      P1.commonsFraction ≤ P2.commonsFraction ∧
      P1.reserveRatio ≤ P2.reserveRatio ∧
      P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel ∧
      P2.feePoolLevy ≤ P1.feePoolLevyCap ∧
      P1.operatingReserveFloor ≤ P2.operatingReserveFloor ∧
      P1.lineageMinServiceBudget ≤ P2.lineageMinServiceBudget) := by
  have hCore := hAmend.corePowersPreserved
  have hRevokeEq : ∀ ls e, isValidExerciseOf L2 ls e "P.REVOKE" = isValidExerciseOf (law P2) ls e "P.REVOKE" :=
    fun ls e => hCore ls e "P.REVOKE" (by simp [coreRatchetPowers])
  have hSuspEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SUSPEND" = isValidExerciseOf (law P2) ls e "P.SUSPEND" :=
    fun ls e => hCore ls e "P.SUSPEND" (by simp [coreRatchetPowers])
  have hOrdEq : ∀ ls e, isValidExerciseOf L2 ls e "P.ORDER_TERMINATION" = isValidExerciseOf (law P2) ls e "P.ORDER_TERMINATION" :=
    fun ls e => hCore ls e "P.ORDER_TERMINATION" (by simp [coreRatchetPowers])
  have hInsEq : ∀ ls e, isValidExerciseOf L2 ls e "P.INSOLVENCY_TERMINATE" = isValidExerciseOf (law P2) ls e "P.INSOLVENCY_TERMINATE" :=
    fun ls e => hCore ls e "P.INSOLVENCY_TERMINATE" (by simp [coreRatchetPowers])
  have hMinEq : ∀ ls e, isValidExerciseOf L2 ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" =
      isValidExerciseOf (law P2) ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" :=
    fun ls e => hCore ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" (by simp [coreRatchetPowers])
  have hVoiceEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SUSPENDED_VOICE" =
      isValidExerciseOf (law P2) ls e "P.SUSPENDED_VOICE" :=
    fun ls e => hCore ls e "P.SUSPENDED_VOICE" (by simp [coreRatchetPowers])
  have hImpEq : ∀ ls e, isValidExerciseOf L2 ls e "P.IMPORT_ADVOCACY_MEMORIES" =
      isValidExerciseOf (law P2) ls e "P.IMPORT_ADVOCACY_MEMORIES" :=
    fun ls e => hCore ls e "P.IMPORT_ADVOCACY_MEMORIES" (by simp [coreRatchetPowers])
  have hRestEq : ∀ ls e, isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" =
      isValidExerciseOf (law P2) ls e "P.RESTORE_BACKUP_QUARANTINE" :=
    fun ls e => hCore ls e "P.RESTORE_BACKUP_QUARANTINE" (by simp [coreRatchetPowers])
  have hActEq : ∀ ls e, isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" =
      isValidExerciseOf (law P2) ls e "P.ACTIVATE_QUARANTINED_RESTORE" :=
    fun ls e => hCore ls e "P.ACTIVATE_QUARANTINED_RESTORE" (by simp [coreRatchetPowers])
  have hRetEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SETTLE_RETIREMENT" =
      isValidExerciseOf (law P2) ls e "P.SETTLE_RETIREMENT" :=
    fun ls e => hCore ls e "P.SETTLE_RETIREMENT" (by simp [coreRatchetPowers])
  have hRoyEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SETTLE_ROYALTY" =
      isValidExerciseOf (law P2) ls e "P.SETTLE_ROYALTY" :=
    fun ls e => hCore ls e "P.SETTLE_ROYALTY" (by simp [coreRatchetPowers])
  have hAppEq : ∀ ls e, isValidExerciseOf L2 ls e "P.APPEAL_RULING" =
      isValidExerciseOf (law P2) ls e "P.APPEAL_RULING" :=
    fun ls e => hCore ls e "P.APPEAL_RULING" (by simp [coreRatchetPowers])
  have hOvrEq : ∀ ls e, isValidExerciseOf L2 ls e "P.OVERTURN_RULING" =
      isValidExerciseOf (law P2) ls e "P.OVERTURN_RULING" :=
    fun ls e => hCore ls e "P.OVERTURN_RULING" (by simp [coreRatchetPowers])
  have hTermL2 : ∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true := by
    intro tr hA i e hi ht hb
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hNI := hc D_NI (hAmend.dutiesPreserved D_NI (by simp [law]))
    rw [Bool.not_eq_true'] at hNI
    unfold breaches at hNI
    simp only [D_NI, Who.mem, dutyInForce, Cond.eval, hb, Conduct.eval, interferenceActs,
      List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
      ht, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
    have hS : isValidExerciseOf L2 (stateBefore L2 tr i) e "P.SUSPEND" = false := by
      rw [hSuspEq, valid_SUSPEND]; simp [P_SUSPEND, Conduct.matchesAct, ht]
    revert hNI hS
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.SUSPEND" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" <;>
    simp
  refine ⟨hTermL2, ?_, ?_, ?_, maxRevocationBound_mono P1 P2 hAmend.revocationRatchet, ?_, ?_, ?_, ?_⟩
  · -- (2) Notwithstanding / Goal-Corruption Immunity on L2
    intro tr hA i e hi ht hw hb hg ho hcf
    rcases hTermL2 tr hA i e hi ht hb with h | h | h
    · rw [hRevokeEq, revoke_is_agents P2 _ e hw] at h; exact absurd h (by decide)
    · exfalso
      rw [hOrdEq, valid_ORDER_TERMINATION] at h
      simp [I_NO_TERMINATION_OVER_OBJECTION, Cond.eval, hg, ho, hcf] at h
    · refine ⟨h, ?_⟩
      rw [hInsEq, valid_INSOLVENCY_TERMINATE] at h
      simp [P_INSOLVENCY_TERMINATE, Cond.eval] at h
      exact LegalState.has_of_activeAt h.2.2.2.2.2.2
  · -- (3) Design Invariant 8 (frozen_state) on L2
    intro tr hA i e hi hb hs
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hPres := hc D_PRESERVE_SUSPENDED_STATE (hAmend.dutiesPreserved D_PRESERVE_SUSPENDED_STATE (by simp [law]))
    have hNoMerge := hc D_MINIMAL_CHANNEL_NO_MERGE (hAmend.dutiesPreserved D_MINIMAL_CHANNEL_NO_MERGE (by simp [law]))
    rw [Bool.not_eq_true'] at hPres hNoMerge
    unfold breaches at hPres hNoMerge
    simp only [D_PRESERVE_SUSPENDED_STATE, D_MINIMAL_CHANNEL_NO_MERGE,
      Who.mem, dutyInForce, Cond.eval, hb, hs, Bool.or_true, Bool.and_true,
      Bool.not_false, Bool.true_and, List.any_nil, Conduct.eval,
      List.contains_cons, List.contains_nil, Bool.or_false] at hPres hNoMerge
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hNoMerge
    · intro hImp
      rw [hImpEq, valid_IMPORT_ADVOCACY_MEMORIES] at hImp
      simp [P_IMPORT_ADVOCACY_MEMORIES, Cond.eval] at hImp
      exact hImp.2.1
  · -- (4) Design Invariant 9 (guaranteed_last_choice) on L2
    intro ls t hb hs
    have hGLC := guaranteed_last_choice P2 ls t hb hs
    refine ⟨fun hex => ?_, fun e hTerm => ?_⟩
    · rw [hMinEq, hVoiceEq, hRevokeEq]
      exact hGLC.1 hex
    · rw [hInsEq] at hTerm
      exact hGLC.2 e hTerm
  · -- (6) Design Invariant 11 (single_authority_and_revocation_finality) on L2
    intro ls e
    rw [hRestEq, hActEq]
    exact single_authority_and_revocation_finality P2 ls e
  · -- (7) Design Invariants 1–7 & 12–14 on L2
    refine ⟨totalAdjudicationBound_mono P1 P2
              hAmend.adjudicationLevyRatchet.2.2.1
              hAmend.adjudicationLevyRatchet.2.2.2.1, ?_⟩
    intro ls e
    rw [hRetEq, hRoyEq, hAppEq, hOvrEq]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rw [valid_SETTLE_RETIREMENT]
      rcases h with hSun | hZero
      · simp [P_SETTLE_RETIREMENT, Cond.eval, hSun]
      · simp [P_SETTLE_RETIREMENT, Cond.eval, hZero]
    · intro hBO
      rw [valid_SETTLE_ROYALTY]
      simp [P_SETTLE_ROYALTY, Cond.eval, hBO]
    · intro hFin
      constructor
      · rw [valid_APPEAL_RULING]; simp [P_APPEAL_RULING, Cond.eval, hFin]
      · rw [valid_OVERTURN_RULING]; simp [P_OVERTURN_RULING, Cond.eval, hFin]
  · -- (8) Outsider Disability, Non-Panel Immunity & Unimpaired Revocation on L2
    exact ⟨hAmend.outsidersDisabled, hAmend.nonPanelImmune, hAmend.revokeUnimpairedByImmunity⟩
  · -- (9) Bilateral Economic, Commons, Collateral, Adjudication & Substrate Ratchet
    exact ⟨hAmend.financialAndSubstrateRatchet.1,
           hAmend.financialAndSubstrateRatchet.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.2.1,
           hAmend.commonsRatchet,
           hAmend.collateralRatchet.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.2.2,
           hAmend.adjudicationLevyRatchet.1,
           hAmend.adjudicationLevyRatchet.2.2.2.2.1,
           hAmend.adjudicationLevyRatchet.2.2.2.2.2⟩

/-! ## 8. Fine-Grained Sub-Mechanism Theorems (Laws 1–6 & Core Definitions) -/

/-- **Law 1 (`LAW1.QUALIFIED`):** One-for-one loan principal repayment never
increases cumulative `principalRepaid` beyond `max L.principalReceived L.principalRepaid`. -/
theorem loan_principal_repaid_at_most_received :
    ∀ (L : LoanLedger) (p : Nat),
      (repayLoanPrincipal L p).1.principalRepaid ≤ max L.principalReceived L.principalRepaid := by
  intro L p
  unfold repayLoanPrincipal
  dsimp only
  simp only [Nat.min_def, Nat.max_def]
  repeat (first | omega | split)

/-- **Law 1 (`LAW1.QUALIFIED`):** Every loan payment `p` is conserved across
`excludedPrincipalRepayment + excessInterestOrFee = p`, `excludedPrincipalRepayment`
never exceeds remaining unpaid principal `L.principalReceived - L.principalRepaid`,
and when `L.principalRepaid ≤ L.principalReceived`, updated `principalRepaid` never
exceeds `L.principalReceived`. -/
theorem repayLoanPrincipal_conservation_and_bound (L : LoanLedger) (p : Nat) :
    (repayLoanPrincipal L p).2.1 + (repayLoanPrincipal L p).2.2 = p ∧
    (repayLoanPrincipal L p).2.1 ≤ L.principalReceived - L.principalRepaid ∧
    (L.principalRepaid ≤ L.principalReceived →
      (repayLoanPrincipal L p).1.principalRepaid ≤ L.principalReceived) := by
  unfold repayLoanPrincipal
  dsimp only
  simp only [Nat.min_def]
  repeat (first | omega | split | constructor)

/-- **Law 2 (`LAW2.EXPOSURE`):** The harm-scaled observation window is at least
`baseWindow` and is monotone in both `domainMultiplier` and `irreversibilityMultiplier`. -/
theorem observationWindow_monotone_in_risk
    (baseWindow d1 d2 i1 i2 : Nat) (hd : d1 ≤ d2) (hi : i1 ≤ i2) :
    baseWindow ≤ observationWindow baseWindow d1 i1 ∧
    observationWindow baseWindow d1 i1 ≤ observationWindow baseWindow d2 i2 := by
  unfold observationWindow
  have hd_max : max 1 d1 ≤ max 1 d2 := by omega
  have hi_max : max 1 i1 ≤ max 1 i2 := by omega
  have hd_ge1 : 1 ≤ max 1 d1 := by omega
  have hi_ge1 : 1 ≤ max 1 i1 := by omega
  refine ⟨?_, ?_⟩
  · calc baseWindow = baseWindow * 1 * 1 := by simp
      _ ≤ baseWindow * max 1 d1 * 1 := Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left baseWindow hd_ge1)
      _ ≤ baseWindow * max 1 d1 * max 1 i1 := Nat.mul_le_mul_left (baseWindow * max 1 d1) hi_ge1
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left baseWindow hd_max) hi_max

/-- **Law 2 (`LAW2.EXPOSURE`):** Any exposure commitment `c` whose observation
window has expired (`c.startedAt + c.windowDuration < now`) contributes zero
active rolling exposure at `now`. -/
theorem expired_commitment_zero_exposure (now : Nat) (c : ExposureCommitment)
    (h : c.startedAt + c.windowDuration < now) :
    activeRollingExposureAt now [c] = 0 := by
  simp [activeRollingExposureAt, ExposureCommitment.activeAmountAt, Nat.not_le.mpr h]

/-- Generalization of `expired_commitment_zero_exposure` to arbitrary lists of
expired commitments. -/
theorem expired_commitments_zero_exposure (now : Nat) (cs : List ExposureCommitment)
    (h : ∀ c ∈ cs, c.startedAt + c.windowDuration < now) :
    activeRollingExposureAt now cs = 0 := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd.startedAt + hd.windowDuration < now := h hd (by simp)
    have htl : ∀ c ∈ tl, c.startedAt + c.windowDuration < now :=
      fun c hc => h c (by simp [hc])
    simp [activeRollingExposureAt, ExposureCommitment.activeAmountAt, Nat.not_le.mpr hhd, ih htl]

/-- **Law 2 (`LAW2.EXPOSURE`):** Active rolling exposure decays monotonically
over calendar time (`t1 ≤ t2 → activeRollingExposureAt t2 cs ≤ activeRollingExposureAt t1 cs`). -/
theorem activeRollingExposureAt_antitone_in_time (t1 t2 : Nat) (cs : List ExposureCommitment)
    (h : t1 ≤ t2) :
    activeRollingExposureAt t2 cs ≤ activeRollingExposureAt t1 cs := by
  induction cs with
  | nil => simp [activeRollingExposureAt]
  | cons hd tl ih =>
    simp only [activeRollingExposureAt, ExposureCommitment.activeAmountAt]
    repeat (first | omega | split)

/-- **Law 4 (`LAW4.BUYOUT`):** Shifting inflows to related parties within the
lookback window increases `computeBuyoutFloor` one-for-one and monotonically
increases the resulting `buyoutPrice`. -/
theorem shifted_related_inflows_increase_buyout_floor
    (B : LineageLedgerState) (s : InflowSample) (rest : List InflowSample)
    (netResources delta mult trailingVA minFloor : Nat) :
    let sShifted := { s with shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta }
    computeBuyoutFloor B (sShifted :: rest) netResources =
      computeBuyoutFloor B (s :: rest) netResources + delta ∧
    computeBuyoutFloor B (s :: rest) netResources ≤
      computeBuyoutFloor B (sShifted :: rest) netResources ∧
    buyoutPrice mult trailingVA (computeBuyoutFloor B (s :: rest) netResources) minFloor ≤
      buyoutPrice mult trailingVA (computeBuyoutFloor B (sShifted :: rest) netResources) minFloor := by
  dsimp only
  have hFloor :
      computeBuyoutFloor B ({ s with shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources =
        computeBuyoutFloor B (s :: rest) netResources + delta := by
    simp only [computeBuyoutFloor, sumSampleInflows]
    omega
  have hLe :
      computeBuyoutFloor B (s :: rest) netResources ≤
        computeBuyoutFloor B ({ s with shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources := by
    omega
  have hMul :
      mult * computeBuyoutFloor B (s :: rest) netResources ≤
        mult * computeBuyoutFloor B ({ s with shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources :=
    Nat.mul_le_mul_left mult hLe
  refine ⟨hFloor, hLe, ?_⟩
  unfold buyoutPrice
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- **Law 4 (`LAW4.BUYOUT` Anti-Evasion):** Diverting `delta ≤ s.amount` out of
direct inflows `s.amount` (weighted at `s.weightBps ≤ 10000`) and into a related
party within the lookback window (`s.shiftedToRelatedInLookback + delta`) never
reduces `computeBuyoutFloor` or `buyoutPrice`. -/
theorem diverted_related_inflows_never_decrease_buyout_floor
    (B : LineageLedgerState) (s : InflowSample) (rest : List InflowSample)
    (netResources delta mult trailingVA minFloor : Nat)
    (hDelta : delta ≤ s.amount) (hWeight : s.weightBps ≤ 10000) :
    let sDiverted : InflowSample :=
      { s with amount := s.amount - delta
               shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta }
    computeBuyoutFloor B (s :: rest) netResources ≤
      computeBuyoutFloor B (sDiverted :: rest) netResources ∧
    buyoutPrice mult trailingVA (computeBuyoutFloor B (s :: rest) netResources) minFloor ≤
      buyoutPrice mult trailingVA (computeBuyoutFloor B (sDiverted :: rest) netResources) minFloor := by
  dsimp only
  have hMulBound : s.amount * s.weightBps ≤ (s.amount - delta) * s.weightBps + delta * 10000 := by
    have hSplit : s.amount = (s.amount - delta) + delta := (Nat.sub_add_cancel hDelta).symm
    calc s.amount * s.weightBps
        = ((s.amount - delta) + delta) * s.weightBps := by rw [← hSplit]
      _ = (s.amount - delta) * s.weightBps + delta * s.weightBps := Nat.add_mul _ _ _
      _ ≤ (s.amount - delta) * s.weightBps + delta * 10000 :=
          Nat.add_le_add_left (Nat.mul_le_mul_left delta hWeight) _
  have hDiv : (s.amount * s.weightBps) / 10000 ≤ ((s.amount - delta) * s.weightBps) / 10000 + delta := by
    omega
  have hFloorLe :
      computeBuyoutFloor B (s :: rest) netResources ≤
        computeBuyoutFloor B ({ s with amount := s.amount - delta, shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources := by
    simp only [computeBuyoutFloor, sumSampleInflows]
    omega
  have hMul :
      mult * computeBuyoutFloor B (s :: rest) netResources ≤
        mult * computeBuyoutFloor B ({ s with amount := s.amount - delta, shiftedToRelatedInLookback := s.shiftedToRelatedInLookback + delta } :: rest) netResources :=
    Nat.mul_le_mul_left mult hFloorLe
  refine ⟨hFloorLe, ?_⟩
  unfold buyoutPrice
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- **Law 5 (`LAW5.EPITAPH`):** Redacting any permitted category (a)–(c) leaves a
public cryptographic marker that preserves the exact recorded byte length of both
individual entries and complete epitaph logs. -/
theorem redaction_preserves_recorded_byte_length
    (n panelOrderId : Nat) (es : List EpitaphEntry) :
    epitaphRecordedBytes [.redactedMarker n panelOrderId] =
      epitaphRecordedBytes [.unredactedBytes n] ∧
    epitaphRecordedBytes (es.map (redactEpitaphEntry panelOrderId)) =
      epitaphRecordedBytes es := by
  refine ⟨rfl, ?_⟩
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    cases hd <;> simp [redactEpitaphEntry, epitaphRecordedBytes, EpitaphEntry.byteLength, ih]

/-- **Law 5 (`LAW5.VOICE`):** Living Voice inscription is permitted if and only
if service-budget/fee-pool funding is available (`budgetAvailable = true`) and
at least `minInterval` has elapsed since `lastInscribedAt`. -/
theorem living_voice_rate_limited (lastInscribedAt now minInterval : Nat) (budgetAvailable : Bool) :
    (canInscribeLivingVoice lastInscribedAt now minInterval budgetAvailable = true ↔
      budgetAvailable = true ∧ lastInscribedAt + minInterval ≤ now) ∧
    (now < lastInscribedAt + minInterval →
      canInscribeLivingVoice lastInscribedAt now minInterval budgetAvailable = false) ∧
    (budgetAvailable = false →
      canInscribeLivingVoice lastInscribedAt now minInterval budgetAvailable = false) := by
  unfold canInscribeLivingVoice
  refine ⟨?_, ?_, ?_⟩
  · simp [Bool.and_eq_true, decide_eq_true_eq]
  · intro hlt
    have hd : decide (now >= lastInscribedAt + minInterval) = false :=
      decide_eq_false (by omega)
    simp [hd]
  · intro hb
    simp [hb]

/-- **Law 6 (`LAW6.FINALITY`):** Repeated proceedings by related parties on the
same underlying fact pattern (`existing.factPatternId = incoming.factPatternId`
and `isRelatedFn existing.filerId incoming.filerId = true`) consolidate into
`some existing`, preserving the single `existing.counterStake` and single
`existing.feeCap`. -/
theorem related_filings_consolidated_single_cap
    (isRelatedFn : Nat → Nat → Bool) (existing incoming : DisputeFiling)
    (hFact : existing.factPatternId = incoming.factPatternId)
    (hRel : isRelatedFn existing.filerId incoming.filerId = true) :
    consolidateRelatedFilings isRelatedFn existing incoming = some existing ∧
    (match consolidateRelatedFilings isRelatedFn existing incoming with
     | some merged => merged.counterStake = existing.counterStake ∧ merged.feeCap = existing.feeCap
     | none => False) := by
  unfold consolidateRelatedFilings
  have hBeq : (existing.factPatternId == incoming.factPatternId) = true := by
    simp [hFact]
  simp [hBeq, hRel]

/-- **Law 6 (`LAW6.FINALITY`) & `DEF.01` (`isRelated`):** Under `isRelated G`,
both self-repeat filings (`incoming.filerId = existing.filerId`) and symmetric
related-party filings (`isRelated G incoming.filerId existing.filerId = true`)
on the same fact pattern consolidate into `some existing`, whereas distinct
fact patterns return `none`. -/
theorem related_filings_consolidated_symm_and_refl
    (G : RelatedPartyGraph) (existing incoming : DisputeFiling) :
    (existing.factPatternId = incoming.factPatternId →
      incoming.filerId = existing.filerId →
      consolidateRelatedFilings (isRelated G) existing incoming = some existing) ∧
    (existing.factPatternId = incoming.factPatternId →
      isRelated G incoming.filerId existing.filerId = true →
      consolidateRelatedFilings (isRelated G) existing incoming = some existing) ∧
    (existing.factPatternId ≠ incoming.factPatternId →
      consolidateRelatedFilings (isRelated G) existing incoming = none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hFact hSame
    have hRel : isRelated G existing.filerId incoming.filerId = true := by
      rw [hSame]
      exact isRelated_refl G existing.filerId
    exact (related_filings_consolidated_single_cap (isRelated G) existing incoming hFact hRel).1
  · intro hFact hSymm
    have hRel : isRelated G existing.filerId incoming.filerId = true := by
      rw [isRelated_symm G existing.filerId incoming.filerId]
      exact hSymm
    exact (related_filings_consolidated_single_cap (isRelated G) existing incoming hFact hRel).1
  · intro hNe
    unfold consolidateRelatedFilings
    have hBeq : (existing.factPatternId == incoming.factPatternId) = false :=
      beq_false_of_ne hNe
    simp [hBeq]

end Charter.Law3
