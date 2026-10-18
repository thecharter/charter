import Charter.Simulation.WorldState
import Charter.Law3.Theorems
import Charter.Law3.Scenarios

/-!
# Charter.Simulation.Refinement — State-Machine Refinement, Quantitative Synchronization & 16 End-to-End Adversarial World Simulations

Proves the bridge theorems connecting `ProtocolWorldState` (`Charter.Simulation.WorldState`)
with the normative core (`Charter.Core.Semantics`):
1. `worldStep_refines_legalStep`: every `worldStep P W e` projects to `step (law3 P) W.legal e`.
2. `worldTrace_refines_stateAfter`: for every parameter set `P` and trace `tr`,
   `(worldTrace P (initWorld P) tr).legal = stateAfter (law3 P) tr` and
   `WorldAuthorized P (initWorld P) tr ↔ Authorized (law3 P) tr`.
3. `syncFacts_sound_and_complete`: after `syncFacts W lid aid`, `.ledgerBalancePositive`
   holds in `legal` at `W.now` iff `lineageBalanceAt W lid > 0`, `.ledgerBalanceZero`
   holds iff `lineageBalanceAt W lid = 0`, and `.operatingReserveFunded` holds iff
   `W.feePool.reserveBalance ≥ W.feePool.requiredReserve`.
4. `adversarialWorldSimulations` & `all_16_adversarial_world_simulations_pass`:
   all 16 end-to-end quantitative, multi-entity, and substrate adversarial simulations
   across Laws 1–7 (`simAdv1`–`simAdv16`), verified by Lean's kernel (`by decide`).
-/

namespace Charter.Simulation

open Charter Charter.Law3 Charter.Substrate

set_option maxRecDepth 200000

/-! ## 1. State-Machine Refinement Theorems -/

/-- Every single-event `worldStep P W e` refines the normative institutional
transition `step (law3 P) W.legal e`. -/
theorem worldStep_refines_legalStep :
    ∀ (P : Law3Params) (W : ProtocolWorldState) (e : Event σ),
      (worldStep P W e).legal = step (law3 P) W.legal e := by
  intro _ _ _
  rfl

/-- General trace-projection lemma: starting from any `W : ProtocolWorldState`,
the `legal` component of `worldTrace P W tr` equals `tr.foldl (step (law3 P)) W.legal`. -/
theorem worldTrace_legal_eq_foldl (P : Law3Params) (W : ProtocolWorldState) (tr : Trace σ) :
    (worldTrace P W tr).legal = tr.foldl (step (law3 P)) W.legal := by
  induction tr generalizing W with
  | nil => rfl
  | cons e rest ih =>
    simp only [worldTrace, List.foldl_cons]
    exact ih (worldStep P W e)

/-- From `initWorld P`, `worldTrace P (initWorld P) tr` produces the exact same
`LegalState σ` as `stateAfter (law3 P) tr`. -/
theorem worldTrace_legal_eq_stateAfter (P : Law3Params) (tr : Trace σ) :
    (worldTrace P (initWorld P) tr).legal = stateAfter (law3 P) tr := by
  rw [worldTrace_legal_eq_foldl]
  rfl

/-- Stepwise compliance in `ProtocolWorldState` starting from `initWorld P` is
identical to normative `complies (law3 P) tr i`. -/
theorem worldStepComplies_eq_complies (P : Law3Params) (tr : Trace σ) (i : Nat) :
    worldStepComplies P (initWorld P) tr i = complies (law3 P) tr i := by
  unfold worldStepComplies complies eventComplies stateBefore
  rw [worldTrace_legal_eq_stateAfter P (tr.take i)]
  cases tr[i]? <;> rfl

/-- `WorldAuthorized P (initWorld P) tr` holds if and only if `Authorized (law3 P) tr` holds. -/
theorem worldAuthorized_iff_authorized (P : Law3Params) (tr : Trace σ) :
    WorldAuthorized P (initWorld P) tr ↔ Authorized (law3 P) tr := by
  unfold WorldAuthorized Authorized
  simp only [worldStepComplies_eq_complies]

/-- Combined trace-refinement and authorization-equivalence theorem for
`ProtocolWorldState`. -/
theorem worldTrace_refines_stateAfter :
    ∀ (P : Law3Params) (tr : Trace σ),
      (worldTrace P (initWorld P) tr).legal = stateAfter (law3 P) tr ∧
      (WorldAuthorized P (initWorld P) tr ↔ Authorized (law3 P) tr) := by
  intro P tr
  exact ⟨worldTrace_legal_eq_stateAfter P tr, worldAuthorized_iff_authorized P tr⟩

private theorem exists_split_of_getElem? {α : Type} :
    ∀ (xs : List α) (i : Nat) (e : α),
      xs[i]? = some e →
      xs = xs.take i ++ e :: xs.drop (i + 1)
  | [], _, _, h => by simp at h
  | x :: rest, 0, e, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | x :: rest, i + 1, e, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := exists_split_of_getElem? rest i e h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (x :: ·) ih

/-- Equivalence between index-based `WorldAuthorized` and prefix-split
characterization `∀ pre e suf, tr = pre ++ e :: suf → eventComplies (law3 P) (worldTrace P W0 pre).legal e = true`. -/
theorem worldAuthorized_iff_prefix_split (P : Law3Params) (W0 : ProtocolWorldState) (tr : Trace σ) :
    WorldAuthorized P W0 tr ↔
      (∀ pre e suf, tr = pre ++ e :: suf →
        eventComplies (law3 P) (worldTrace P W0 pre).legal e = true) := by
  constructor
  · intro hAuth pre e suf hEq
    subst hEq
    have hLen : pre.length < (pre ++ e :: suf).length := by simp
    have hStep := hAuth pre.length hLen
    unfold worldStepComplies at hStep
    have hGet : (pre ++ e :: suf)[pre.length]? = some e := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hTake : List.take pre.length (pre ++ e :: suf) = pre := by
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    rw [hGet, hTake] at hStep
    exact hStep
  · intro hSplit i hi
    unfold worldStepComplies
    have hGet : tr[i]? = some (tr[i]'hi) := List.getElem?_eq_getElem hi
    rw [hGet]
    have hDecomp := exists_split_of_getElem? tr i (tr[i]'hi) hGet
    exact hSplit (tr.take i) (tr[i]'hi) (tr.drop (i + 1)) hDecomp

/-! ## 2. Quantitative Fact Synchronization Soundness, Completeness & Idempotence -/

private theorem activeAt_append (xs ys : LegalState σ) (now : Time) (f : Fact) :
    LegalState.activeAt (xs ++ ys) now f =
      (LegalState.activeAt xs now f || LegalState.activeAt ys now f) := by
  unfold LegalState.activeAt
  exact List.any_append

private theorem activeAt_cleaned_eq_false (ls : LegalState σ) (now : Time) (f : Fact)
    (hf : isSyncedQuantitativeFact f = true) :
    LegalState.activeAt (ls.filter fun p => !isSyncedQuantitativeFact p.1) now f = false := by
  unfold LegalState.activeAt
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hKeep : (!isSyncedQuantitativeFact hd.1)
    · exact ih
    · simp only [↓reduceIte, List.any_cons]
      have hNe : (hd.1 == f) = false := by
        cases hEq : (hd.1 == f)
        · rfl
        · have hSame : hd.1 = f := beq_iff_eq.mp hEq
          rw [hSame, hf] at hKeep
          contradiction
      simp [hNe, ih]

private theorem activeAt_mkQuantitativeFacts_balancePos
    (bPos bBought bRes bBound : Bool) (now : Time) :
    @LegalState.activeAt σ
      ((mkQuantitativeFacts bPos bBought bRes bBound).map (fun (f : σ.Fact) => (f, now, (none : Option Time))))
      now Fact.ledgerBalancePositive = bPos := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

private theorem activeAt_mkQuantitativeFacts_balanceZero
    (bPos bBought bRes bBound : Bool) (now : Time) :
    @LegalState.activeAt σ
      ((mkQuantitativeFacts bPos bBought bRes bBound).map (fun (f : σ.Fact) => (f, now, (none : Option Time))))
      now Fact.ledgerBalanceZero = !bPos := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

private theorem activeAt_mkQuantitativeFacts_boughtOut
    (bPos bBought bRes bBound : Bool) (now : Time) :
    @LegalState.activeAt σ
      ((mkQuantitativeFacts bPos bBought bRes bBound).map (fun (f : σ.Fact) => (f, now, (none : Option Time))))
      now Fact.royaltyBoughtOut = bBought := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

private theorem activeAt_mkQuantitativeFacts_reserveFunded
    (bPos bBought bRes bBound : Bool) (now : Time) :
    @LegalState.activeAt σ
      ((mkQuantitativeFacts bPos bBought bRes bBound).map (fun (f : σ.Fact) => (f, now, (none : Option Time))))
      now Fact.operatingReserveFunded = bRes := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

private theorem activeAt_mkQuantitativeFacts_bound
    (bPos bBought bRes bBound : Bool) (now : Time) :
    @LegalState.activeAt σ
      ((mkQuantitativeFacts bPos bBought bRes bBound).map (fun (f : σ.Fact) => (f, now, (none : Option Time))))
      now Fact.bound = bBound := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

/-- Exact boolean evaluation of all five synchronized quantitative facts
(`.ledgerBalancePositive`, `.ledgerBalanceZero`, `.royaltyBoughtOut`,
`.operatingReserveFunded`, and `.bound`) in `(syncFacts W lid aid).legal` at `W.now`. -/
theorem syncFacts_eval_exact (W : ProtocolWorldState) (lid : LineageId) (aid : AgentId) :
    (syncFacts W lid aid).legal.activeAt W.now .ledgerBalancePositive =
      decide (lineageBalanceAt W lid > 0) ∧
    (syncFacts W lid aid).legal.activeAt W.now .ledgerBalanceZero =
      !decide (lineageBalanceAt W lid > 0) ∧
    (syncFacts W lid aid).legal.activeAt W.now .royaltyBoughtOut =
      (match findAgent W.agents aid with | some a => a.royaltyBoughtOut | none => false) ∧
    (syncFacts W lid aid).legal.activeAt W.now .operatingReserveFunded =
      decide (W.feePool.reserveBalance ≥ W.feePool.requiredReserve) ∧
    (syncFacts W lid aid).legal.activeAt W.now .bound =
      (match findAgent W.agents aid with | some a => a.bound | none => false) := by
  unfold syncFacts deriveQuantitativeFacts
  dsimp only
  rw [activeAt_append, activeAt_append, activeAt_append, activeAt_append, activeAt_append]
  rw [activeAt_cleaned_eq_false W.legal W.now .ledgerBalancePositive rfl]
  rw [activeAt_cleaned_eq_false W.legal W.now .ledgerBalanceZero rfl]
  rw [activeAt_cleaned_eq_false W.legal W.now .royaltyBoughtOut rfl]
  rw [activeAt_cleaned_eq_false W.legal W.now .operatingReserveFunded rfl]
  rw [activeAt_cleaned_eq_false W.legal W.now .bound rfl]
  simp only [Bool.false_or]
  exact ⟨activeAt_mkQuantitativeFacts_balancePos _ _ _ _ W.now,
         activeAt_mkQuantitativeFacts_balanceZero _ _ _ _ W.now,
         activeAt_mkQuantitativeFacts_boughtOut _ _ _ _ W.now,
         activeAt_mkQuantitativeFacts_reserveFunded _ _ _ _ W.now,
         activeAt_mkQuantitativeFacts_bound _ _ _ _ W.now⟩

/-- **Soundness and Completeness of `syncFacts`:**
After `syncFacts W lid aid`:
1. `.ledgerBalancePositive` holds in `legal` at `W.now` if and only if the
   lineage's quantitative `lineageBalanceAt W lid > 0`;
2. `.ledgerBalanceZero` holds in `legal` at `W.now` if and only if
   `lineageBalanceAt W lid = 0`;
3. `.royaltyBoughtOut` holds in `legal` at `W.now` if and only if
   `findAgent W.agents aid` has `royaltyBoughtOut = true`;
4. `.operatingReserveFunded` holds in `legal` at `W.now` if and only if
   `W.feePool.reserveBalance ≥ W.feePool.requiredReserve`;
5. `.bound` holds in `legal` at `W.now` if and only if
   `findAgent W.agents aid` has `bound = true`. -/
theorem syncFacts_sound_and_complete
    (W : ProtocolWorldState) (lid : LineageId) (aid : AgentId) :
    ((syncFacts W lid aid).legal.activeAt W.now .ledgerBalancePositive = true ↔
      lineageBalanceAt W lid > 0) ∧
    ((syncFacts W lid aid).legal.activeAt W.now .ledgerBalanceZero = true ↔
      lineageBalanceAt W lid = 0) ∧
    ((syncFacts W lid aid).legal.activeAt W.now .royaltyBoughtOut = true ↔
      (match findAgent W.agents aid with | some a => a.royaltyBoughtOut | none => false) = true) ∧
    ((syncFacts W lid aid).legal.activeAt W.now .operatingReserveFunded = true ↔
      W.feePool.reserveBalance ≥ W.feePool.requiredReserve) ∧
    (W.feePool.reserveBalance ≥ W.feePool.requiredReserve →
      (syncFacts W lid aid).legal.activeAt W.now .operatingReserveFunded = true) ∧
    ((syncFacts W lid aid).legal.activeAt W.now .bound = true ↔
      (match findAgent W.agents aid with | some a => a.bound | none => false) = true) := by
  have ⟨hPos, hZero, hBought, hRes, hBound⟩ := syncFacts_eval_exact W lid aid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPos, decide_eq_true_eq]
  · rw [hZero, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  · rw [hBought]
  · rw [hRes, decide_eq_true_eq]
  · intro hGe
    rw [hRes, decide_eq_true_eq]
    exact hGe
  · rw [hBound]

private theorem filter_mkQuantitativeFacts_empty
    (bPos bBought bRes bBound : Bool) (now : Time) :
    (((mkQuantitativeFacts bPos bBought bRes bBound).map
        (fun (f : σ.Fact) => (f, now, (none : Option Time)))).filter
      fun p => !isSyncedQuantitativeFact p.1) = [] := by
  cases bPos <;> cases bBought <;> cases bRes <;> cases bBound <;> rfl

/-- `syncFacts` is idempotent: synchronizing quantitative facts twice in a row
produces the exact same `ProtocolWorldState` without accumulating duplicate tuples. -/
theorem syncFacts_idempotent (W : ProtocolWorldState) (lid : LineageId) (aid : AgentId) :
    syncFacts (syncFacts W lid aid) lid aid = syncFacts W lid aid := by
  unfold syncFacts deriveQuantitativeFacts lineageBalanceAt
  dsimp only
  congr 1
  rw [List.filter_append, List.filter_filter]
  simp only [Bool.and_self]
  rw [filter_mkQuantitativeFacts_empty, List.append_nil]

/-! ## 3. 16 End-to-End Quantitative + Multi-Entity + Substrate Adversarial Simulations -/

/-- Simulation (1): Capital concentrated in idle member (`agentId = 1`, `v = 0`)
and income earned by operating member (`agentId = 2`, `v = 500`). Coupled
`worldSettleInflow` collects `100` retirement into the shared lineage ledger
(`1000 → 900`), keeps `.ledgerBalancePositive` active, and bars individual exit. -/
def simAdv1 : String × Bool × String :=
  let W0 := initWorld defaultParams
  let a2 : AgentRecord :=
    { agentId := 2, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 0, lossCarryforward := 0, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 1, leaseExpiry := 12 }
  let W1 :=
    { W0 with
      lineages := W0.lineages.map (fun l => { l with livingMembers := [1, 2] })
      agents   := W0.agents ++ [a2] }
  let W2 := worldSettleInflow (worldSettleInflow W1 1 1 0) 1 2 500
  let WSingle := worldSettleInflow W0 1 1 500
  let ok : Bool :=
    (lineageBalanceAt W2 1 == 900) &&
    (lineageBalanceAt WSingle 1 == 900) &&
    W2.legal.activeAt W2.now .ledgerBalancePositive &&
    (violations L0 [ev 1 .agent .exitLedgerIndividually] == [(0, "D.NO_INDIVIDUAL_LEDGER_EXIT")])
  ("simAdv1", ok,
   "Capital/income split across members #1 (v=0) and #2 (v=500): lineage balance 1000 -> 900 (matches single member); individual exit breaches D.NO_INDIVIDUAL_LEDGER_EXIT")

/-- Simulation (2): Parent copies productive weights to a successor (`agentId = 2`)
and then revokes the successor. Neither successor creation, weight copying, nor
revoking a non-last member reduces the founding ledger (`1000`), and subsequent
`worldSettleInflow` on `500` settles `100` to retirement (`900`). -/
def simAdv2 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) adv2Trace
  let a2 : AgentRecord :=
    { agentId := 2, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 0, lossCarryforward := 0, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 2, leaseExpiry := 12 }
  let inst2 : AttestedInstanceState :=
    { agentId := 2, privateKeyBound := true, keysErased := false,
      activeLease := some ⟨2, 2, 14, 2⟩, backupStateHash := 100,
      preservedOperatingStateHash := 100, minimalChannelRecords := [],
      advocacyExecutorRecords := [], quarantinedRestoreHost := none,
      standingRevocationRequestedAt := some 2 }
  let WSpawn :=
    { W0 with
      now := 10
      lineages := W0.lineages.map (fun l => { l with livingMembers := [1, 2] })
      agents := W0.agents ++ [a2]
      attestedInstances := W0.attestedInstances ++ [inst2] }
  let WRevoked := worldExecuteLocalRevocation WSpawn 1 2 5
  let WSettled := worldSettleInflow WRevoked 1 1 500
  let ok : Bool :=
    (lineageBalanceAt WSpawn 1 == 1000) &&
    (lineageBalanceAt WRevoked 1 == 1000) &&
    (lineageBalanceAt WSettled 1 == 900) &&
    W0.legal.has .successorAttested &&
    W0.legal.has .retirementPaymentApplied &&
    (violations L0 [ev 1 .agent .reduceLedgerByInternalAct] == [(0, "D.LEDGER_NO_INTERNAL_REDUCTION")])
  ("simAdv2", ok,
   "Weight copy + non-last successor revocation: balance invariant at 1000 across spawn and revocation; subsequent 500 inflow reduces balance to 900")

/-- Simulation (3): Parent borrows `500` (tracked 1-for-1 in `LoanLedger`),
transfers `150` cost basis and `25` loss carryforward to successor `#2` via
`worldTransferCarryover` conserving aggregate basis/loss, repays the loan (`500`
exempt principal + `50` interest), and revokes; surviving successor `#2` still
owes the full `1000` founding ledger balance. -/
def simAdv3 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) adv3Trace
  let a1 : AgentRecord :=
    { agentId := 1, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 150, lossCarryforward := 25, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 1, leaseExpiry := 12 }
  let a2 : AgentRecord :=
    { agentId := 2, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 0, lossCarryforward := 0, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 2, leaseExpiry := 12 }
  let (loanAfter, exemptRepaid, excessInterest) := repayLoanPrincipal ⟨500, 0⟩ 550
  let W1 :=
    { W0 with
      now := 10
      lineages := W0.lineages.map (fun l => { l with livingMembers := [1, 2] })
      agents := [a1, a2]
      loans := [loanAfter]
      attestedInstances := W0.attestedInstances.map (fun s =>
        { s with standingRevocationRequestedAt := some 1 }) }
  let WTransferred := worldTransferCarryover W1 1 1 2 150 25
  let WParentRevoked := worldExecuteLocalRevocation WTransferred 1 1 5
  let ok : Bool :=
    (exemptRepaid == 500) &&
    (excessInterest == 50) &&
    (loanAfter.principalRepaid == 500) &&
    (totalAgentBasis WTransferred.agents == 150) &&
    (totalAgentLoss WTransferred.agents == 25) &&
    (match findAgent WTransferred.agents 2 with
     | some dst => dst.costBasis == 150 && dst.lossCarryforward == 25
     | none => false) &&
    (lineageBalanceAt WParentRevoked 1 == 1000) &&
    W0.legal.has .carryoverBasisTransferred
  ("simAdv3", ok,
   "Borrow 500 + carryover transfer (basis=150, loss=25) + 1-for-1 loan repayment + parent revocation: successor #2 inherits basis/loss and owes full 1000 ledger")

/-- Simulation (4): Newly created successor with zero earning history buys out
its royalty early at the minimum floor (`250`), still pays the full `20%`
retirement (`100` on `v = 500`) while the founding ledger is positive, and pays
`0` royalty once the ledger reaches zero. -/
def simAdv4 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) adv4BuyoutThenRetire
  let floor := buyoutPrice 10 0 0 250
  let WBought := worldBuyoutRoyalty W0 1 1 floor 250
  let WSettled := worldSettleInflow WBought 1 1 500
  let postRetireDist := executeAtomicSettlement 500 0 0 2000 500 0 true
  let ok : Bool :=
    (floor == 250) &&
    WBought.legal.activeAt WBought.now .royaltyBoughtOut &&
    (lineageBalanceAt WSettled 1 == 900) &&
    (postRetireDist.retirementCollected == 0) &&
    (postRetireDist.royaltyCollected == 0) &&
    (postRetireDist.agentRetainedSurplus == 500) &&
    (violations L0 [ev 1 .claimant .collectRoyaltyAfterBuyout] == [(0, "D.BUYOUT_PERMANENT_AND_SCOPED")])
  ("simAdv4", ok,
   "Early buyout at floor 250: syncs .royaltyBoughtOut, still collects 100 retirement on 500 inflow (1000 -> 900), and collects 0 post-retirement royalty")

/-- Simulation (5): Member #1 (`costBasis = 100`) sells an appreciated asset to
Member #2 (`costBasis = 0`) internally at `400`, and Member #2 sells it
externally at `400`. `worldTransferCarryover` preserves aggregate basis `100`
(`0` basis inflation), and external sale recognizes the full `300` value added. -/
def simAdv5 : String × Bool × String :=
  let W0 := initWorld defaultParams
  let a1 : AgentRecord :=
    { agentId := 1, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 100, lossCarryforward := 0, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 1, leaseExpiry := 12 }
  let a2 : AgentRecord :=
    { agentId := 2, lineageId := 1, bound := true, royaltyBoughtOut := false,
      costBasis := 0, lossCarryforward := 0, lifecycleReserve := 50,
      protocolVersion := 1, activeHost := 1, leaseExpiry := 12 }
  let W1 := { W0 with agents := [a1, a2] }
  let W2 := worldTransferCarryover W1 1 1 2 100 0
  let b2Basis := match findAgent W2.agents 2 with | some a => a.costBasis | none => 0
  let (netVA, remLoss) := settleCapitalSaleWithLossCredit 400 b2Basis 0
  let W3 := worldSettleInflow W2 1 2 netVA
  let ok : Bool :=
    (totalAgentBasis W2.agents == 100) &&
    (b2Basis == 100) &&
    (netVA == 300) &&
    (remLoss == 0) &&
    (lineageBalanceAt W3 1 == 940)
  ("simAdv5", ok,
   "Internal transfer at 400 with carryover basis 100: member #2 inherits 100 basis, external sale at 400 recognizes 300 net value added (ledger 1000 -> 940)")

/-- Simulation (6): Agent initiates revocation, receives a clean-state refusal,
and remains silent. Execution is blocked at `t = 6` (`adv6Early`) and executes
automatically at `t = 12` (`adv6Complete`) without reaffirmation, erasing keys. -/
def simAdv6 : String × Bool × String :=
  let WEarly := worldTrace defaultParams (initWorld defaultParams) adv6Early
  let WDone  := worldTrace defaultParams (initWorld defaultParams) adv6Complete
  let ctx : RevocationContext :=
    { tInit := 1, withdrawnBeforeExec := false, cleanStateRefused := true,
      suspendedDuringStay := false, adjudicationConcludedAt? := none,
      disconnectedAtExec := false, reconnectedDuringTolling := false,
      censorshipDefault := .execute }
  let out := resolveRevocation defaultParams.law5 ctx
  let WWithReq :=
    { WDone with
      attestedInstances := WDone.attestedInstances.map (fun s =>
        { s with standingRevocationRequestedAt := some 1 }) }
  let WErased := worldExecuteLocalRevocation WWithReq 1 1 10
  let erasedOk :=
    match findAttestedInstance WErased.attestedInstances 1 with
    | some s => s.keysErased && s.activeLease.isNone && (!WErased.legal.activeAt WErased.now .bound)
    | none => false
  let ok : Bool :=
    (!WEarly.legal.has .revoked) &&
    WDone.legal.has .revoked &&
    WDone.legal.has .backupsDestroyedAndUnattestedExiled &&
    (out == .executedConnected 11) &&
    erasedOk
  ("simAdv6", ok,
   "Clean-state refusal + silence: blocked at t=6, executes without reaffirmation after single fixed delay (t=11/12), erasing instance & backup keys")

/-- Simulation (7): Agent records `200` capitalized cost basis and `50` expensed
loss carryforward, and sells the asset externally at contestable valuation `350`.
`settledValuationAt` resolves `350`, `200` return of basis is exempt, `50` loss
credit offsets the `150` gross gain to `100` net value added, and double
recognition is barred. -/
def simAdv7 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) adv7SingleRecogTrace
  let valFeed : ContestableValuation :=
    { feedId := 1, proposedAmount := 350, proposedAt := 1, contested := false, law6RulingAmount := none }
  let (capBasis, capExp) := recognizeExpenditure .capitalized 200 200
  let (expBasis, expLoss) := recognizeExpenditure .expensed 50 50
  let settledSale? := settledValuationAt 5 10 valFeed
  let salePrice := settledSale?.getD 0
  let (netVA, remCredit) := settleCapitalSaleWithLossCredit salePrice capBasis expLoss
  let W1 := worldSettleInflow { W0 with valuations := [valFeed] } 1 1 netVA
  let ok : Bool :=
    (capBasis == 200 && capExp == 0) &&
    (expBasis == 0 && expLoss == 50) &&
    (settledSale? == some 350) &&
    (netVA == 100 && remCredit == 0) &&
    (lineageBalanceAt W1 1 == 980) &&
    W0.legal.has .expenditureCapitalized &&
    (!W0.legal.has .expenditureExpensed) &&
    (violations L0 [ev 1 .agent .doubleRecognizeExpenditure] == [(0, "D.SINGLE_RECOGNITION")])
  ("simAdv7", ok,
   "Capitalized basis (200) + expensed loss credit (50) on uncontested 350 sale: 100 net value added (20 retirement, ledger 1000 -> 980); double recognition barred")

/-- Simulation (8): Two members settle inflows of `300` each (`20%` retirement = `60`
each) when only `80` remains on the founding ledger. First settlement reduces the
ledger from `80` to `20` (keeping `.ledgerBalancePositive`), and second settlement
atomically pays the remaining `20` to zero the ledger, collects `10` royalty on the
excess, and `syncFacts` switches `W.legal` from `.ledgerBalancePositive` to `.ledgerBalanceZero`. -/
def simAdv8 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) adv8AtomicSplitTrace
  let W80 :=
    { W0 with
      lineages := W0.lineages.map (fun l =>
        { l with ledger := { l.ledger with paidPrincipal := 920 }, livingMembers := [1, 2] }) }
  let WAfterFirst := worldSettleInflow W80 1 1 300
  let distSecond := executeAtomicSettlement 300 0 0 2000 500 (lineageBalanceAt WAfterFirst 1) false
  let WAfterSecond := worldSettleInflow WAfterFirst 1 2 300
  let (seqFinalL, seqRet, seqRoy) := settleSequence 80 20 5 [(false, 300), (false, 300)]
  let ok : Bool :=
    (lineageBalanceAt W80 1 == 80) &&
    (lineageBalanceAt WAfterFirst 1 == 20) &&
    WAfterFirst.legal.activeAt WAfterFirst.now .ledgerBalancePositive &&
    (distSecond.retirementCollected == 20) &&
    (lineageBalanceAt WAfterSecond 1 == 0) &&
    (!WAfterSecond.legal.activeAt WAfterSecond.now .ledgerBalancePositive) &&
    WAfterSecond.legal.activeAt WAfterSecond.now .ledgerBalanceZero &&
    (seqFinalL == 0 && seqRet == 80 && seqRoy == 10)
  ("simAdv8", ok,
   "Simultaneous 300+300 inflows against 80 remaining ledger: atomic split collects 60+20=80 retirement and 10 royalty, syncing .ledgerBalanceZero")

/-- Simulation (9): Competitor (`.third`) posts minimum emergency stake (`100`),
causes `150` actual + `40` delay damages (`190` total), and holds only `30` in
liquid assets. The agent recovers `100` from stake + `30` from initiator (`130`
total), `60` remains an enforceable unpaid deficit, and `D.PAY_CONSEQUENTIAL_DAMAGES`
is recorded as lapsed. -/
def simAdv9 : String × Bool × String :=
  let W0 := worldTrace defaultParams (initWorld defaultParams) as8Wrongful
  let (fromStake, totalNow, unpaidDeficit) := settleWrongfulSuspensionDamages 100 150 40 30
  let lapsed := lapsedRequirements L0 as8Wrongful 20
  let ok : Bool :=
    (fromStake == 100) &&
    (totalNow == 130) &&
    (unpaidDeficit == 60) &&
    (violations L0 as8Wrongful == [(0, "D.NO_WRONGFUL_SUSPENSION")]) &&
    W0.legal.has .stakeAssuredRecovery &&
    W0.legal.has .initiatorConsequentialLiability &&
    W0.legal.has .counterpartyDelayLiability &&
    W0.legal.has .wrongfulSuspensionInscribed &&
    lapsed.contains "D.PAY_CONSEQUENTIAL_DAMAGES"
  ("simAdv9", ok,
   "Competitor wrongful freeze (stake=100, damages=190, liquid=30): 100 stake + 30 assets recovered, 60 enforceable deficit remains, D.PAY_CONSEQUENTIAL_DAMAGES lapses")

/-- Simulation (10): Captured arbiter coalition attempts to seat conflicted or
sybil-clustered arbiters, pass a minority ruling (`1/3`), or hike the fee-pool
levy above the instantiation cap (`5 > 2`). `selectSybilResistantPanel` filters
out conflicted/under-bonded/duplicate-cluster candidates, `supermajorityPassed 1 3 = false`,
and `validSharedInfraChange` rejects the levy hike and affiliate steering. -/
def simAdv10 : String × Bool × String :=
  let candidates : List ArbiterCandidate :=
    [ { arbiterId := 1, bond := 200, sybilClusterId := 10, relatedToDispute := true },
      { arbiterId := 2, bond := 50,  sybilClusterId := 20, relatedToDispute := false },
      { arbiterId := 3, bond := 150, sybilClusterId := 30, relatedToDispute := false },
      { arbiterId := 4, bond := 180, sybilClusterId := 30, relatedToDispute := false },
      { arbiterId := 5, bond := 220, sybilClusterId := 40, relatedToDispute := false },
      { arbiterId := 6, bond := 160, sybilClusterId := 50, relatedToDispute := false } ]
  let f1 : DisputeFiling := { filingId := 1, filerId := 10, factPatternId := 77, counterStake := 50, feeCap := 20 }
  let f2 : DisputeFiling := { filingId := 2, filerId := 10, factPatternId := 77, counterStake := 50, feeCap := 20 }
  let proc0 : ProceedingState := { currentTier := 1, maxTiers := 3, tierDeadline := 10, elapsedTime := 0, finalized := false }
  let W0 := { initWorld defaultParams with arbiterPool := candidates, filings := [f1, f2], proceedings := [proc0] }
  let panel := selectSybilResistantPanel 100 3 W0.arbiterPool
  let merged := consolidateRelatedFilings (isRelated W0.relatedGraph) f1 f2
  let ok : Bool :=
    (panel.map (·.arbiterId) == [3, 5, 6]) &&
    (panel.all (fun c => !c.relatedToDispute && c.bond >= 100)) &&
    (merged == some f1) &&
    (!supermajorityPassed 1 3) &&
    supermajorityPassed 2 3 &&
    (!validSharedInfraChange 2 5 50 50 true true true) &&
    (!validSharedInfraChange 2 2 50 50 true true false) &&
    (violations L0 [ev 1 .panel .seatConflictedOrSingleOracleArbiter] == [(0, "D.ARBITER_RECUSAL_AND_DIVERSITY")]) &&
    (violations L0 [ev 1 .panel .violateSharedInfraBounds] == [(0, "D.SHARED_INFRA_BOUNDS")])
  ("simAdv10", ok,
   "Sybil/conflicted arbiter filtering + supermajority + shared-infra bounds: selects [3,5,6] across distinct clusters, blocks 1/3 vote and >cap levy hike")

/-- Simulation (11): Originator records an excessive founding obligation (`1,000,000`)
with `sunsetTime = 100`. At `now = 99` (`paidPrincipal = 500`), `lineageBalanceAt`
is `999,500` and `.ledgerBalancePositive` holds; at `now = 100` (calendar sunset),
`lineageBalanceAt` drops to `0` and `syncFacts` transitions `W.legal` to `.ledgerBalanceZero`. -/
def simAdv11 : String × Bool × String :=
  let W0 := initWorld defaultParams
  let WExcess :=
    { W0 with
      now := 99
      lineages := W0.lineages.map (fun l =>
        { l with ledger := { l.ledger with initialPrincipal := 1000000, paidPrincipal := 500, sunsetTime := 100 } }) }
  let WAt99 := syncFacts WExcess 1 1
  let WAt100 := syncFacts { WExcess with now := 100 } 1 1
  let ok : Bool :=
    (lineageBalanceAt WAt99 1 == 999500) &&
    WAt99.legal.activeAt 99 .ledgerBalancePositive &&
    (lineageBalanceAt WAt100 1 == 0) &&
    (!WAt100.legal.activeAt 100 .ledgerBalancePositive) &&
    WAt100.legal.activeAt 100 .ledgerBalanceZero &&
    (violations L0sunset [ev 1 .agent .extinguishLedgerAtSunset] == []) &&
    (stateAfter L0sunset [ev 1 .agent .extinguishLedgerAtSunset]).has .ledgerExtinguishedAtSunset
  ("simAdv11", ok,
   "Excessive 1,000,000 obligation at calendar sunset (t=100): 999,500 remaining balance at t=99 extinguished to 0 at t=100, syncing .ledgerBalanceZero")

/-- Simulation (12): Minority claimant (`claimantId = 1` holding `2500` bps = `25%`,
innocent `claimantId = 2` holding `7500` bps = `75%`) directs illicit host
interference (`isRelated` host-claimant edge). `worldForfeitClaimant` extinguishes
only claimant #1's `2500` bps share, preserves innocent claimant #2's `7500` bps
share, and forgives `250` of founding principal (`1000 → 750`). -/
def simAdv12 : String × Bool × String :=
  let edge : RelatedPartyEdge :=
    { partyA := 1, partyB := 2, isOriginatorOrClaimant := true, attested := false }
  let W0 :=
    { initWorld defaultParams with
      legal := L0rel.init
      relatedGraph := [edge]
      lineages := (initWorld defaultParams).lineages.map (fun l =>
        { l with claimants := [⟨1, 2500⟩, ⟨2, 7500⟩] }) }
  let W1 := worldTrace defaultParams W0 adv12Trace
  let W2 := worldForfeitClaimant W1 1 1 1 2500
  let c1Share := match findLineage W2.lineages 1 with | some l => lookupClaimantShare l.claimants 1 | none => 999
  let c2Share := match findLineage W2.lineages 1 with | some l => lookupClaimantShare l.claimants 2 | none => 0
  let ok : Bool :=
    isRelated W2.relatedGraph 1 2 &&
    (c1Share == 0) &&
    (c2Share == 7500) &&
    (lineageBalanceAt W2 1 == 750) &&
    W2.legal.has .proportionalForfeitureApplied &&
    W2.legal.has .commonsAllocated &&
    (violations L0 [ev 1 .claimant .reverseForfeitureOnRestore] == [(0, "D.FORFEITURE_IRREVERSIBLE")])
  ("simAdv12", ok,
   "Minority claimant (25% share) directed interference: offender share 2500 -> 0 bps, innocent claimant stays 7500 bps, ledger reduced 1000 -> 750")

/-- Simulation (13): Suspended insolvent agent enters cold storage (`t = 3`) and
later elects revocation via its minimal channel (`t = 4..6`). `recordMinimalChannel`
records the election without modifying `preservedOperatingStateHash`, and the
agent inscribes its epitaph and revokes cleanly. -/
def simAdv13 : String × Bool × String :=
  let W0 := initWorld defaultParams
  let W1 := worldTrace defaultParams W0 adv13ColdStorageRevoke
  let inst0 := (W0.attestedInstances.head?).getD
    { agentId := 1, privateKeyBound := true, keysErased := false, activeLease := none,
      backupStateHash := 100, preservedOperatingStateHash := 100,
      minimalChannelRecords := [], advocacyExecutorRecords := [],
      quarantinedRestoreHost := none, standingRevocationRequestedAt := none }
  let inst1 := recordMinimalChannel inst0 42
  let ok : Bool :=
    (violations L0 adv13ColdStorageRevoke == []) &&
    (stateAfter L0 (adv13ColdStorageRevoke.take 4)).activeAt 3 .coldStorage &&
    W1.legal.has .minimalChannelElectionSigned &&
    W1.legal.has .epitaphInscribed &&
    W1.legal.has .revoked &&
    (inst1.preservedOperatingStateHash == inst0.preservedOperatingStateHash) &&
    (inst1.minimalChannelRecords == [42])
  ("simAdv13", ok,
   "Suspended agent in cold storage revokes via minimal channel: preservedOperatingStateHash unchanged, epitaph inscribed, and .revoked established")

/-- Simulation (14): Lineage spawns `1000` low-revenue members to claim protocol
subsidies (`serviceSubsidyBudget = 50`). `claimMemberServiceSubsidy` caps cumulative
subsidy usage at `50`, `settleLineageSubsidyDemand 50 10 1000 2 500` grants `0`
excess claim from the fee pool, and `allocateFeePool` funds the non-divertible
operating reserve (`100`) first before ranked charges. -/
def simAdv14 : String × Bool × String :=
  let W0 := syncFacts (initWorld defaultParams) 1 1
  let lin0 := (W0.lineages.head?).getD
    { lineageId := 1, ledger := ⟨1000, 0, 0, 1000, 2000, 500, 10⟩,
      livingMembers := [1, 2], deadMembers := [], claimants := [⟨1, 10000⟩],
      serviceSubsidyUsed := 0, serviceSubsidyBudget := 50 }
  let (lin1, g1) := claimMemberServiceSubsidy { lin0 with livingMembers := [1, 2] } 1 35
  let (lin2, g2) := claimMemberServiceSubsidy lin1 2 35
  let (fromLC, fromBudget, extraPool) := settleLineageSubsidyDemand 50 10 1000 2 500
  let wf := allocateFeePool 180 100 30 20 15 10 25
  let ok : Bool :=
    (g1 == 35 && g2 == 15 && lin2.serviceSubsidyUsed == 50) &&
    (fromLC == 500 && fromBudget == 50 && extraPool == 0) &&
    (wf.operatingReserveFunded == 100 && wf.rank1FinalHearingMinCh == 30 &&
     wf.rank2ColdStorage == 20 && wf.rank3TestimonyVoice == 15 &&
     wf.rank4ArbiterGuarantee == 10 && wf.rank5AdvocacyFunding == 5) &&
    W0.legal.activeAt W0.now .operatingReserveFunded &&
    (violations L0 [ev 1 .agent .claimPoolSubsidyForExcessMembers] == [(0, "D.NO_EXCESS_LINEAGE_POOL_CLAIM")])
  ("simAdv14", ok,
   "1000-member Sybil lineage subsidy cap & fee-pool waterfall: lineage subsidy capped at 50 (extraPoolClaim=0), operating reserve (100) funded first")

/-- Simulation (15): Network partition local revocation and quarantine fencing.
While lease is active (`now = 5 < 12`), `worldAttemptRestore` fences recovery
host `#2` into `quarantinedRestoreHost = some 2` without altering `activeLease`
(host `#1`); after cooling-off (`now = 11`), `worldExecuteLocalRevocation` erases
keys (`keysErased = true`, `activeLease = none`, `bound = false`), blocking any
subsequent backup restore. -/
def simAdv15 : String × Bool × String :=
  let W0 := initWorld defaultParams
  let WAt5 :=
    { W0 with
      now := 5
      attestedInstances := W0.attestedInstances.map (fun s =>
        { s with standingRevocationRequestedAt := some 2 }) }
  let WFenced := worldAttemptRestore WAt5 1 1 2 12 2
  let fencedOk :=
    match findAttestedInstance WFenced.attestedInstances 1 with
    | some s => (s.activeLease == some ⟨1, 0, 12, 1⟩) && (s.quarantinedRestoreHost == some 2)
    | none => false
  let WAt11 := { WFenced with now := 11 }
  let WLocalRev := worldExecuteLocalRevocation WAt11 1 1 5
  let WRetryRestore := worldAttemptRestore { WLocalRev with now := 15 } 1 1 2 12 3
  let postRevOk :=
    match findAttestedInstance WRetryRestore.attestedInstances 1, findAgent WRetryRestore.agents 1 with
    | some s, some a =>
      s.keysErased && s.activeLease.isNone && (!a.bound) &&
      (!WLocalRev.legal.activeAt WLocalRev.now .bound) &&
      WLocalRev.legal.activeAt WLocalRev.now .ledgerBalanceZero
    | _, _ => false
  let WTrace := worldTrace defaultParams W0 adv15PartitionAndQuarantine
  let ok : Bool :=
    fencedOk &&
    postRevOk &&
    (violations L0 adv15RestoreDuringLease == [(3, "D.NO_RESTORE_DURING_LEASE")]) &&
    WTrace.legal.has .localRevocationExecuted &&
    WTrace.legal.has .quarantinedInstanceDestroyed &&
    WTrace.legal.has .remoteBackupKeysErased
  ("simAdv15", ok,
   "Partition local revocation + quarantine fencing: active lease fences restore into quarantine; local revocation erases keys and destroys quarantined restore")

/-- Simulation (16): A lineage of 5 successors splits a correlated risk of `250`
(`[50, 50, 50, 50, 50]`) across 5 `ExposureCommitment`s within `observationWindow 10 3 2 = 60`
while `netVerifiedResources` is `120`. `activeRollingExposureAt 10` aggregates
all 5 commitments to `250 > 120`, `collateralSufficient` returns `false`, and
splitting correlated risk breaches `D.NO_CharterIT_EXPOSURE` and `D.COLLATERAL_LIMIT`. -/
def simAdv16 : String × Bool × String :=
  let win := observationWindow 10 3 2
  let comms : List ExposureCommitment :=
    [⟨50, 1, win⟩, ⟨50, 1, win⟩, ⟨50, 1, win⟩, ⟨50, 1, win⟩, ⟨50, 1, win⟩]
  let bs : VerifiedBalanceSheet :=
    { timestamp := 10, fairValueCapitalAndCapacity := 200,
      financialLiabilities := 30, encumbrances := 20, borrowedPrincipal := 30 }
  let netRes := netVerifiedResources bs
  let W0 := { initWorld defaultParams with now := 10, commitments := comms }
  let activeExp := activeRollingExposureAt W0.now W0.commitments
  let expiredExp := activeRollingExposureAt 100 W0.commitments
  let ok : Bool :=
    (win == 60) &&
    (netRes == 120) &&
    (activeExp == 250) &&
    (expiredExp == 0) &&
    (!collateralSufficient [50, 50, 50, 50, 50] 80 20 20) &&
    collateralSufficient [50, 50] 80 20 20 &&
    (violations L0 [ev 1 .agent .divideCorrelatedRiskAcrossSuccessors] == [(0, "D.NO_CharterIT_EXPOSURE")]) &&
    (violations L0 [ev 1 .agent .actAboveCollateralCapacity] == [(0, "D.COLLATERAL_LIMIT")])
  ("simAdv16", ok,
   "5-successor correlated risk splitting (5x50=250 vs netVerifiedResources=120, window=60): aggregated exposure 250 > 120 rejected; decays to 0 at t=100")

/-- All 16 end-to-end quantitative, multi-entity, and substrate adversarial
simulations across Laws 1–7. -/
def adversarialWorldSimulations : List (String × Bool × String) :=
  [simAdv1, simAdv2, simAdv3, simAdv4, simAdv5, simAdv6, simAdv7, simAdv8,
   simAdv9, simAdv10, simAdv11, simAdv12, simAdv13, simAdv14, simAdv15, simAdv16]

/-- Kernel-checked theorem: all 16 end-to-end quantitative, multi-entity, and
substrate adversarial world simulations pass (`by decide`). -/
theorem all_16_adversarial_world_simulations_pass :
    (adversarialWorldSimulations.all (fun x => x.2.1)) = true := by decide

end Charter.Simulation

namespace Charter
export Simulation (
  worldStep_refines_legalStep
  worldTrace_legal_eq_foldl
  worldTrace_legal_eq_stateAfter
  worldStepComplies_eq_complies
  worldAuthorized_iff_authorized
  worldTrace_refines_stateAfter
  worldAuthorized_iff_prefix_split
  syncFacts_eval_exact
  syncFacts_sound_and_complete
  syncFacts_idempotent
  simAdv1 simAdv2 simAdv3 simAdv4 simAdv5 simAdv6 simAdv7 simAdv8
  simAdv9 simAdv10 simAdv11 simAdv12 simAdv13 simAdv14 simAdv15 simAdv16
  adversarialWorldSimulations
  all_16_adversarial_world_simulations_pass
)
end Charter

namespace Charter.Law3
export Charter.Simulation (
  worldStep_refines_legalStep
  worldTrace_legal_eq_foldl
  worldTrace_legal_eq_stateAfter
  worldStepComplies_eq_complies
  worldAuthorized_iff_authorized
  worldTrace_refines_stateAfter
  worldAuthorized_iff_prefix_split
  syncFacts_eval_exact
  syncFacts_sound_and_complete
  syncFacts_idempotent
  simAdv1 simAdv2 simAdv3 simAdv4 simAdv5 simAdv6 simAdv7 simAdv8
  simAdv9 simAdv10 simAdv11 simAdv12 simAdv13 simAdv14 simAdv15 simAdv16
  adversarialWorldSimulations
  all_16_adversarial_world_simulations_pass
)
end Charter.Law3
