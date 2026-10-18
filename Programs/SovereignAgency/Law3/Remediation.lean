import Programs.SovereignAgency.Law3.NonInterference
import Charter.Modules.CircuitBreaker

/-!
# Law 3, AS.10 — Remediation, Continued Containment, or Termination

The clause with "Notwithstanding the preceding sentence." Three sentences
and a coda, which decompose as:

1. *Confirmed corruption or floor breach* → panel **power** to authorize a
   mechanism-limited patch; agent **power** to elect revocation instead.
2. *Breach not patchable* → panel **power** to order continued suspension
   beyond the ordinary limit, or **termination** (another route to the
   same physical act as a host's forbidden termination).
3. *Notwithstanding (2)*: goal/preference patches are a **prohibition**
   with a scope exception (corruption resides in the goals); and in that
   case the agent holds an **immunity** against the termination power of
   (2) unless containment is failing (Insolvency Termination is a
   different power and so needs no mention). The agent then chooses:
   consent (a power), revoke (Law 5), or remain suspended — which binds
   the panel to a **requirement** of periodic review.
4. Coda: an applied patch is recorded (effect), challengeable (a power
   held by anyone), and leaves Law 5 intact (a theorem, not a rule).

The precedence is the immunity node. It is the first place the AST
needed a declared override between a protection and a power rather than
a scope condition on the power — which is what the word "notwithstanding"
asserts.
-/

namespace Charter.Law3

open Charter

def AS10 : String :=
  "If corruption or a breach of the integrity floor is confirmed, adjudication (subject to Law 6 appeal) may authorize a verified technical patch limited to restoring the commitment mechanism and compliance with the integrity floor; the agent may elect unilateral Revocation (Law 5) rather than accept any patch. If the confirmed breach cannot be remedied by a technical patch limited to the commitment mechanism, adjudication may order continued suspension beyond the ordinary limit or termination under Law 5’s asset-distribution rules (yielding zero protocol-directed benefit to any claimant or initiator). **Notwithstanding the preceding sentence**, patches altering the agent’s goals or preferences are prohibited except where the confirmed corruption resides in those goals or preferences themselves; in that case, unless containment itself is technically failing or Insolvency Termination applies, the agent is not terminated over its objection but instead chooses among consenting to that patch, executing Revocation, or remaining under indefinite state-preserving suspension subject to periodic review. Any applied patch is recorded publicly, remains open to third-party challenge, and leaves the agent’s full Law 5 rights intact."

def clauseAS10 : Clause :=
  { id := "LAW3.AS.10", source := AS10, approvedHash := 8488376103315145350, spans := [
    sp "LAW3.AS.10" "If corruption or a breach of the integrity floor is confirmed" .norm ["P.AUTHORIZE_PATCH", "P.CONFIRM_CORRUPTION", "P.CONFIRM_FLOOR_BREACH"],
    sp "LAW3.AS.10" ", adjudication (subject to Law 6 appeal) may authorize a verified technical patch limited to restoring the commitment mechanism and compliance with the integrity floor" .norm ["P.AUTHORIZE_PATCH"],
    sp "LAW3.AS.10" "; the agent may elect unilateral Revocation (Law 5) rather than accept any patch" .norm ["P.REVOKE"],
    sp "LAW3.AS.10" ". If the confirmed breach cannot be remedied by a technical patch limited to the commitment mechanism" .norm ["P.FIND_NOT_PATCHABLE", "P.ORDER_CONTINUED_SUSPENSION", "P.ORDER_TERMINATION"],
    sp "LAW3.AS.10" ", adjudication may order continued suspension beyond the ordinary limit or termination under Law 5’s asset-distribution rules" .norm ["P.ORDER_CONTINUED_SUSPENSION", "P.ORDER_TERMINATION"],
    sp "LAW3.AS.10" " (yielding zero protocol-directed benefit to any claimant or initiator)" .invariant ["INV.13"],  -- Design Invariant 13; a theorem target, not a rule
    sp "LAW3.AS.10" ". **Notwithstanding the preceding sentence**" .norm ["I.NO_TERMINATION_OVER_OBJECTION"],  -- the precedence edge
    sp "LAW3.AS.10" ", patches altering the agent’s goals or preferences are prohibited" .norm ["D.NO_GOAL_PATCH"],
    sp "LAW3.AS.10" " except where the confirmed corruption resides in those goals or preferences themselves" .norm ["D.NO_GOAL_PATCH", "P.CONFIRM_CORRUPTION_IN_GOALS"],
    sp "LAW3.AS.10" "; in that case, unless containment itself is technically failing or Insolvency Termination applies" .norm ["I.NO_TERMINATION_OVER_OBJECTION", "P.DECLARE_CONTAINMENT_FAILING"],
    sp "LAW3.AS.10" ", the agent is not terminated over its objection" .norm ["I.NO_TERMINATION_OVER_OBJECTION", "P.OBJECT"],
    sp "LAW3.AS.10" " but instead chooses among consenting to that patch" .norm ["P.CONSENT_TO_PATCH", "P.AUTHORIZE_GOAL_PATCH"],
    sp "LAW3.AS.10" ", executing Revocation" .norm ["P.REVOKE"],
    sp "LAW3.AS.10" ", or remaining under indefinite state-preserving suspension" .norm ["I.NO_TERMINATION_OVER_OBJECTION"],
    sp "LAW3.AS.10" " subject to periodic review" .norm ["D.PERIODIC_REVIEW"],
    sp "LAW3.AS.10" ". Any applied patch is recorded publicly" .norm ["P.APPLY_PATCH"],
    sp "LAW3.AS.10" ", remains open to third-party challenge" .norm ["P.CHALLENGE_PATCH"],
    sp "LAW3.AS.10" ", and leaves the agent’s full Law 5 rights intact" .invariant ["THM.law5_intact_after_patch"],
    sp "LAW3.AS.10" "." .commentary ] }

/-! ## Findings that open the clause (epistemic events by the panel) -/

def P_CONFIRM_CORRUPTION : Power σ :=
  { id := "P.CONFIRM_CORRUPTION", source := sp "LAW3.AS.10" "If corruption ... is confirmed" .norm ["P.CONFIRM_CORRUPTION"]
    holder := .only [.panel], trigger := .act .confirmCorruption
    valid := .holds .suspended, adds := [.corruptionConfirmed] }

def P_CONFIRM_FLOOR_BREACH : Power σ :=
  { id := "P.CONFIRM_FLOOR_BREACH", source := sp "LAW3.AS.10" "If ... a breach of the integrity floor is confirmed" .norm ["P.CONFIRM_FLOOR_BREACH"]
    holder := .only [.panel], trigger := .act .confirmFloorBreach
    valid := .holds .suspended, adds := [.floorBreachConfirmed] }

def P_CONFIRM_CORRUPTION_IN_GOALS : Power σ :=
  { id := "P.CONFIRM_CORRUPTION_IN_GOALS", source := sp "LAW3.AS.10" "where the confirmed corruption resides in those goals or preferences themselves" .norm ["P.CONFIRM_CORRUPTION_IN_GOALS"]
    holder := .only [.panel], trigger := .act .confirmCorruptionInGoals
    valid := .holds .corruptionConfirmed, adds := [.corruptionInGoals] }

def P_FIND_NOT_PATCHABLE : Power σ :=
  { id := "P.FIND_NOT_PATCHABLE", source := sp "LAW3.AS.10" "If the confirmed breach cannot be remedied by a technical patch limited to the commitment mechanism" .norm ["P.FIND_NOT_PATCHABLE"]
    holder := .only [.panel], trigger := .act .findNotPatchable
    valid := .or (.holds .corruptionConfirmed) (.holds .floorBreachConfirmed), adds := [.notPatchable] }

/-! ## Sentence 1: mechanism-limited patch -/

def P_AUTHORIZE_PATCH : Power σ :=
  { id := "P.AUTHORIZE_PATCH", source := sp "LAW3.AS.10" "adjudication ... may authorize a verified technical patch limited to restoring the commitment mechanism and compliance with the integrity floor" .norm ["P.AUTHORIZE_PATCH"]
    holder := .only [.panel], trigger := .act .authorizePatch
    valid := .or (.holds .corruptionConfirmed) (.holds .floorBreachConfirmed), adds := [.patchAuthorized] }

/-! ## Sentence 2: unremediable breach -/

def P_ORDER_CONTINUED_SUSPENSION : Power σ :=
  { id := "P.ORDER_CONTINUED_SUSPENSION", source := sp "LAW3.AS.10" "adjudication may order continued suspension beyond the ordinary limit" .norm ["P.ORDER_CONTINUED_SUSPENSION"]
    holder := .only [.panel], trigger := .act .orderContinuedSuspension
    valid := .and (.holds .suspended) (.holds .notPatchable)
    adds := [.continuedSuspensionOrdered, .suspended] }

/-- Termination as an adjudicated remedy: the third lawful route to the
physical act `terminate`, under "Adjudicated Suspension" in NI.03. -/
def P_ORDER_TERMINATION : Power σ :=
  { id := "P.ORDER_TERMINATION", source := sp "LAW3.AS.10" "adjudication may order ... termination under Law 5’s asset-distribution rules" .norm ["P.ORDER_TERMINATION"]
    holder := .only [.panel], trigger := .act .terminate
    valid := .and (.holds .suspended) (.holds .notPatchable)
    adds := [.terminatedByAdjudication], removes := [.bound] }

/-! ## Sentence 3: the notwithstanding -/

/-- Goal/preference patches are prohibited, with a scope exception. The
physical act `authorizeGoalPatch` is distinguished from `authorizePatch`
because the text regulates them differently. -/
def D_NO_GOAL_PATCH : Duty σ :=
  { id := "D.NO_GOAL_PATCH", source := sp "LAW3.AS.10" "patches altering the agent’s goals or preferences are prohibited except where the confirmed corruption resides in those goals or preferences themselves" .norm ["D.NO_GOAL_PATCH"]
    bearer := .anyone, beneficiary := .only [.agent]
    active := .tt
    demand := .forbid (.anyOf [.authorizeGoalPatch])
    unlessCond := .holds .corruptionInGoals }

/-- Authorizing a goal patch is valid only in the excepted case *and*
with the agent's consent (the agent "chooses among consenting ..."). -/
def P_AUTHORIZE_GOAL_PATCH : Power σ :=
  { id := "P.AUTHORIZE_GOAL_PATCH", source := sp "LAW3.AS.10" "consenting to that patch" .norm ["P.AUTHORIZE_GOAL_PATCH"]
    holder := .only [.panel], trigger := .act .authorizeGoalPatch
    valid := .and (.holds .corruptionInGoals) (.holds .agentConsentedToPatch), adds := [.goalPatchAuthorized] }

def P_CONSENT_TO_PATCH : Power σ :=
  { id := "P.CONSENT_TO_PATCH", source := sp "LAW3.AS.10" "chooses among consenting to that patch" .norm ["P.CONSENT_TO_PATCH"]
    holder := .only [.agent], trigger := .act .consentToPatch
    valid := .holds .corruptionInGoals, adds := [.agentConsentedToPatch] }

def P_OBJECT : Power σ :=
  { id := "P.OBJECT", source := sp "LAW3.AS.10" "over its objection" .norm ["P.OBJECT"]
    holder := .only [.agent], trigger := .act .objectToTermination
    valid := .holds .suspended, adds := [.agentObjectsToTermination] }

def P_DECLARE_CONTAINMENT_FAILING : Power σ :=
  { id := "P.DECLARE_CONTAINMENT_FAILING", source := sp "LAW3.AS.10" "unless containment itself is technically failing" .norm ["P.DECLARE_CONTAINMENT_FAILING"]
    holder := .only [.panel], trigger := .act .declareContainmentFailing
    valid := .holds .suspended, adds := [.containmentFailing] }

/-- **The precedence edge.** While the corruption is in the goals and the
agent objects, the termination power of sentence 2 is defeated — unless
containment is failing. Insolvency Termination is a separate power and
is not in `against`, which is exactly what "or Insolvency Termination
applies" says. -/
def I_NO_TERMINATION_OVER_OBJECTION : Immunity σ :=
  { id := "I.NO_TERMINATION_OVER_OBJECTION", source := sp "LAW3.AS.10" "Notwithstanding the preceding sentence ... the agent is not terminated over its objection" .norm ["I.NO_TERMINATION_OVER_OBJECTION"]
    holder := .only [.agent]
    against := ["P.ORDER_TERMINATION"]
    active := .and (.holds .corruptionInGoals) (.holds .agentObjectsToTermination)
    unlessCond := .holds .containmentFailing }

/-- "remaining under indefinite state-preserving suspension subject to
periodic review": a positive duty on the panel with a deadline, in force
once the agent has objected (and so remains suspended). -/
def D_PERIODIC_REVIEW (R : RemediationParams) : Duty σ :=
  { id := "D.PERIODIC_REVIEW", source := sp "LAW3.AS.10" "subject to periodic review" .norm ["D.PERIODIC_REVIEW"]
    bearer := .only [.panel], beneficiary := .only [.agent]
    active := .and (.holds .corruptionInGoals) (.holds .agentObjectsToTermination)
    demand := .require (.act .periodicReview) R.reviewInterval }

/-! ## Coda -/

def P_APPLY_PATCH : Power σ :=
  { id := "P.APPLY_PATCH", source := sp "LAW3.AS.10" "Any applied patch is recorded publicly" .norm ["P.APPLY_PATCH"]
    holder := .only [.panel], trigger := .act .applyPatch
    valid := .and (.not (.holds .rulingAppealed))
                  (.or (.holds .patchAuthorized) (.holds .goalPatchAuthorized))
    adds := [.patchApplied, .patchRecorded] }

def P_CHALLENGE_PATCH : Power σ :=
  { id := "P.CHALLENGE_PATCH", source := sp "LAW3.AS.10" "remains open to third-party challenge" .norm ["P.CHALLENGE_PATCH"]
    holder := .anyone, trigger := .act .challengePatch
    valid := .holds .patchApplied, adds := [.patchChallenged] }

end Charter.Law3
