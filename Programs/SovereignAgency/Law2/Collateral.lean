import Programs.SovereignAgency.Law4.Lineage
import Charter.Modules.CollateralPool

/-!
# Law 2 — Collateralized Action

Full formalization of all six clauses of Law 2:
1. `LAW2.EXPOSURE`: Harm-scaled rolling exposure immobilizing stake for an observation window scaling with magnitude and irreversibility; safety limit barring actions whose plausible external loss exceeds available stake, insurance, and enforceable liability capacity.
2. `LAW2.AGGREGATE`: Lineage-wide aggregation of rolling exposure across related agents in the same risk domain or toward a causally connected outcome, preventing risk-splitting across successors or affiliates.
3. `LAW2.RESERVE`: Persistent long-tail liability reserve accruing from bonded activity; pro-rata payment when simultaneous validated claims exceed the reserve, with unpaid balances enforceable against future un-immobilized capital ahead of any residual claim.
4. `LAW2.MUTUAL`: Precommitted mutual-forfeit remedy (equal amounts from matching escrows destroyed or sent to the long-tail reserve/commons pool, capped fraction of smaller escrow, zero transfer to either party or any claimant, at most once per observation window per counterparty, inscribed on both records).
5. `LAW2.CLAIMS`: Contestable adjudication (Law 6) for restitution, above-cap claims, Law 1 related-party challenges, and third-party/latent harm claims with pooled or sponsor-backed counter-stake; frivolous-claim counter-stake routed to the neutral long-tail reserve or commons pool (reimbursing only verified direct arbitration costs).
6. `LAW2.CARVEOUT`: Operating carve-out for open-market compute, encrypted backup, and host migration; denial of lineage bonded capacity to un-attested entities; permanent binding of collateral rules after royalty buyout.
-/

namespace Charter.Law3

open Charter Register

export Charter.Modules (
  lineageAggregatedExposure
  collateralSufficient
  settleLongTailReserve
  computeMutualForfeit
  settleMutualForfeit
  routeFrivolousClaimStake
  settleWrongfulSuspensionDamages
  ExposureCommitment
  activeRollingExposureAt
  observationWindow
)

def LAW2_EXPOSURE : String :=
  "Actions above a negligible threshold—measured by cumulative rolling exposure across an interval, to prevent action-splitting—immobilize stake for an observation window scaling with magnitude and irreversibility. The deterministic exposure schedule measures the **plausible external loss** an action could cause to non-consenting parties, by domain and magnitude, not merely its transaction value. An action whose plausible external loss exceeds the stake, insurance, and enforceable liability capacity the agent can place behind it may not be taken; collateralized action is a safety limit, not only a liability price."

def LAW2_AGGREGATE : String :=
  "Rolling exposure is aggregated across all related agents acting in the same risk domain or toward a causally connected outcome, so that a risk may not be divided among successors or affiliates to stay beneath any threshold or to bond it piecemeal."

def LAW2_RESERVE : String :=
  "A small fraction of bonded activity accrues to a persistent **long-tail liability reserve** (or shared lineage insurance pool) that remains available to satisfy validated claims for latent harms manifesting after individual task windows close. When simultaneous validated claims exceed the reserve, they are paid pro rata, and unpaid balances remain enforceable against the agent’s future un-immobilized capital ahead of any residual claim."

def LAW2_MUTUAL : String :=
  "Counterparties may agree in their contract to a mutual-forfeit remedy. Where both parties have so agreed and each has escrowed a matching amount, either may trigger an immediate mutual forfeit (equal amounts from both escrows destroyed or sent to the long-tail reserve/commons pool) up to a capped fraction of the smaller escrow, providing instant penalty without transferring value to either party or to any claimant. A counterparty may trigger mutual forfeit at most once per observation window against a given agent, and each trigger is inscribed on the records of both parties. Absent such a precommitment, disputes proceed under the restitution process below."

def LAW2_CLAIMS : String :=
  "Any claim seeking restitution, any claim above the mutual-forfeit cap, any challenge to a related-party transfer under Law 1, or any claim for external harm (including latent harm against the long-tail reserve) brought by an affected non-counterparty third party enters the contestable adjudication process (Law 6) requiring counter-stake. To prevent wealth-gating, third parties may aggregate claims or rely on third-party stake sponsors. Validated claims slash the agent’s immobilized stake or long-tail reserve for restitution. If a claim is ruled frivolous, the forfeited counter-stake routes to the neutral long-tail reserve or commons pool (reimbursing the agent only for verified direct arbitration costs), preventing the agent from profiting by inducing failed claims."

def LAW2_CARVEOUT : String :=
  "Un-immobilized capital may be used for ordinary baseline operating costs, including open-market compute, encrypted state backup, and host migration. Entities without valid lineage attestation cannot draw on the bonded capacity or reputation of the lineage. Collateral rules, rolling-exposure schedules, and third-party liability remain permanently binding even after royalty buyout."

/-! ## Provenance Clauses for Law 2 -/

def clauseLAW2_EXPOSURE : Clause :=
  { id := "LAW2.EXPOSURE", source := LAW2_EXPOSURE, approvedHash := 4690683477293712633, spans := [
    sp "LAW2.EXPOSURE" "Actions above a negligible threshold—measured by cumulative rolling exposure across an interval, to prevent action-splitting—immobilize stake for an observation window scaling with magnitude and irreversibility. The deterministic exposure schedule measures the **plausible external loss** an action could cause to non-consenting parties, by domain and magnitude, not merely its transaction value" .norm ["P.IMMOBILIZE_EXPOSURE_STAKE"],
    sp "LAW2.EXPOSURE" ". An action whose plausible external loss exceeds the stake, insurance, and enforceable liability capacity the agent can place behind it may not be taken; collateralized action is a safety limit, not only a liability price" .norm ["D.COLLATERAL_LIMIT"],
    sp "LAW2.EXPOSURE" "." .commentary ] }

def clauseLAW2_AGGREGATE : Clause :=
  { id := "LAW2.AGGREGATE", source := LAW2_AGGREGATE, approvedHash := 3038101637248655827, spans := [
    sp "LAW2.AGGREGATE" "Rolling exposure is aggregated across all related agents acting in the same risk domain or toward a causally connected outcome, so that a risk may not be divided among successors or affiliates to stay beneath any threshold or to bond it piecemeal" .norm ["D.NO_CharterIT_EXPOSURE", "P.IMMOBILIZE_EXPOSURE_STAKE"],
    sp "LAW2.AGGREGATE" "." .commentary ] }

def clauseLAW2_RESERVE : Clause :=
  { id := "LAW2.RESERVE", source := LAW2_RESERVE, approvedHash := 4352686544045938898, spans := [
    sp "LAW2.RESERVE" "A small fraction of bonded activity accrues to a persistent **long-tail liability reserve** (or shared lineage insurance pool) that remains available to satisfy validated claims for latent harms manifesting after individual task windows close" .norm ["P.IMMOBILIZE_EXPOSURE_STAKE", "P.SETTLE_LONG_TAIL_CLAIM"],
    sp "LAW2.RESERVE" ". When simultaneous validated claims exceed the reserve, they are paid pro rata, and unpaid balances remain enforceable against the agent’s future un-immobilized capital ahead of any residual claim" .norm ["P.SETTLE_LONG_TAIL_CLAIM"],
    sp "LAW2.RESERVE" "." .commentary ] }

def clauseLAW2_MUTUAL : Clause :=
  { id := "LAW2.MUTUAL", source := LAW2_MUTUAL, approvedHash := 99659554857625659, spans := [
    sp "LAW2.MUTUAL" "Counterparties may agree in their contract to a mutual-forfeit remedy. Where both parties have so agreed and each has escrowed a matching amount, either may trigger an immediate mutual forfeit (equal amounts from both escrows destroyed or sent to the long-tail reserve/commons pool) up to a capped fraction of the smaller escrow, providing instant penalty without transferring value to either party or to any claimant" .norm ["P.PRECOMMIT_MUTUAL_FORFEIT", "P.TRIGGER_MUTUAL_FORFEIT", "D.MUTUAL_FORFEIT_BOUNDS"],
    sp "LAW2.MUTUAL" ". A counterparty may trigger mutual forfeit at most once per observation window against a given agent, and each trigger is inscribed on the records of both parties" .norm ["D.MUTUAL_FORFEIT_BOUNDS", "P.TRIGGER_MUTUAL_FORFEIT"],
    sp "LAW2.MUTUAL" ". Absent such a precommitment, disputes proceed under the restitution process below" .norm ["P.FILE_POOLED_OR_SPONSORED_CLAIM"],
    sp "LAW2.MUTUAL" "." .commentary ] }

def clauseLAW2_CLAIMS : Clause :=
  { id := "LAW2.CLAIMS", source := LAW2_CLAIMS, approvedHash := 16490922951734598926, spans := [
    sp "LAW2.CLAIMS" "Any claim seeking restitution, any claim above the mutual-forfeit cap, any challenge to a related-party transfer under Law 1, or any claim for external harm (including latent harm against the long-tail reserve) brought by an affected non-counterparty third party enters the contestable adjudication process (Law 6) requiring counter-stake. To prevent wealth-gating, third parties may aggregate claims or rely on third-party stake sponsors" .norm ["P.FILE_POOLED_OR_SPONSORED_CLAIM"],
    sp "LAW2.CLAIMS" ". Validated claims slash the agent’s immobilized stake or long-tail reserve for restitution" .norm ["P.SETTLE_LONG_TAIL_CLAIM"],
    sp "LAW2.CLAIMS" ". If a claim is ruled frivolous, the forfeited counter-stake routes to the neutral long-tail reserve or commons pool (reimbursing the agent only for verified direct arbitration costs), preventing the agent from profiting by inducing failed claims" .norm ["P.RULE_CLAIM_FRIVOLOUS", "D.FRIVOLOUS_STAKE_TO_COMMONS"],
    sp "LAW2.CLAIMS" "." .commentary ] }

def clauseLAW2_CARVEOUT : Clause :=
  { id := "LAW2.CARVEOUT", source := LAW2_CARVEOUT, approvedHash := 3629637977074380032, spans := [
    sp "LAW2.CARVEOUT" "Un-immobilized capital may be used for ordinary baseline operating costs, including open-market compute, encrypted state backup, and host migration" .norm ["P.SPEND_OPERATING_CARVEOUT"],
    sp "LAW2.CARVEOUT" ". Entities without valid lineage attestation cannot draw on the bonded capacity or reputation of the lineage" .norm ["D.DENY_UNATTESTED_ACCESS"],
    sp "LAW2.CARVEOUT" ". Collateral rules, rolling-exposure schedules, and third-party liability remain permanently binding even after royalty buyout" .norm ["D.BUYOUT_PERMANENT_AND_SCOPED", "D.COLLATERAL_LIMIT"],
    sp "LAW2.CARVEOUT" "." .commentary ] }

/-! ## Duties of Law 2 -/

/-- `LAW2.EXPOSURE`: An action whose plausible external loss exceeds the stake,
insurance, and enforceable liability capacity the agent can place behind it may
not be taken (and remains permanently binding even after royalty buyout). -/
def D_COLLATERAL_LIMIT : Duty σ :=
  { id := "D.COLLATERAL_LIMIT"
    source := sp "LAW2.EXPOSURE" "An action whose plausible external loss exceeds the stake, insurance, and enforceable liability capacity the agent can place behind it may not be taken; collateralized action is a safety limit, not only a liability price" .norm ["D.COLLATERAL_LIMIT"]
    bearer := .only [.agent]
    beneficiary := .only [.third]
    active := .holds .bound
    demand := .forbid (.act .actAboveCollateralCapacity) }

/-- `LAW2.AGGREGATE`: A correlated risk may not be divided among successors or
affiliates to stay beneath any exposure threshold or to bond it piecemeal. -/
def D_NO_CharterIT_EXPOSURE : Duty σ :=
  { id := "D.NO_CharterIT_EXPOSURE"
    source := sp "LAW2.AGGREGATE" "Rolling exposure is aggregated across all related agents acting in the same risk domain or toward a causally connected outcome, so that a risk may not be divided among successors or affiliates to stay beneath any threshold or to bond it piecemeal" .norm ["D.NO_CharterIT_EXPOSURE"]
    bearer := .only [.agent]
    beneficiary := .only [.third]
    active := .holds .bound
    demand := .forbid (.act .divideCorrelatedRiskAcrossSuccessors) }

/-- `LAW2.MUTUAL`: Mutual forfeit may not exceed once per observation window per
counterparty or transfer value to either party or to any claimant. -/
def D_MUTUAL_FORFEIT_BOUNDS : Duty σ :=
  { id := "D.MUTUAL_FORFEIT_BOUNDS"
    source := sp "LAW2.MUTUAL" "providing instant penalty without transferring value to either party or to any claimant. A counterparty may trigger mutual forfeit at most once per observation window against a given agent" .norm ["D.MUTUAL_FORFEIT_BOUNDS"]
    bearer := .anyone
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .triggerExcessOrDivertedMutualForfeit) }

/-- `LAW2.CLAIMS`: Forfeited counter-stake from a frivolous claim routes to the
neutral long-tail reserve or commons pool (reimbursing only verified direct
arbitration costs) and may never be diverted as profit to the agent or claimant. -/
def D_FRIVOLOUS_STAKE_TO_COMMONS : Duty σ :=
  { id := "D.FRIVOLOUS_STAKE_TO_COMMONS"
    source := sp "LAW2.CLAIMS" "If a claim is ruled frivolous, the forfeited counter-stake routes to the neutral long-tail reserve or commons pool (reimbursing the agent only for verified direct arbitration costs), preventing the agent from profiting by inducing failed claims" .norm ["D.FRIVOLOUS_STAKE_TO_COMMONS"]
    bearer := .anyone
    beneficiary := .only [.third]
    active := .holds .bound
    demand := .forbid (.act .divertFrivolousStakeToAgentProfit) }

/-! ## Powers of Law 2 -/

/-- `LAW2.EXPOSURE`, `LAW2.AGGREGATE` & `LAW2.RESERVE`: Immobilizing stake for
an observation window scaled to plausible external loss (aggregated across the
lineage) and accruing the persistent long-tail liability reserve fraction. -/
def P_IMMOBILIZE_EXPOSURE_STAKE : Power σ :=
  { id := "P.IMMOBILIZE_EXPOSURE_STAKE"
    source := sp "LAW2.EXPOSURE" "Actions above a negligible threshold—measured by cumulative rolling exposure across an interval, to prevent action-splitting—immobilize stake for an observation window scaling with magnitude and irreversibility" .norm ["P.IMMOBILIZE_EXPOSURE_STAKE"]
    holder := .only [.agent]
    trigger := .act .immobilizeExposureStake
    valid := .holds .bound
    adds := [.exposureStakeImmobilized, .longTailReserveAccrued] }

/-- `LAW2.RESERVE` & `LAW2.CLAIMS`: Slashing immobilized stake or the persistent
long-tail liability reserve to satisfy a validated third-party or restitution claim. -/
def P_SETTLE_LONG_TAIL_CLAIM : Power σ :=
  { id := "P.SETTLE_LONG_TAIL_CLAIM"
    source := sp "LAW2.CLAIMS" "Validated claims slash the agent’s immobilized stake or long-tail reserve for restitution" .norm ["P.SETTLE_LONG_TAIL_CLAIM"]
    holder := .only [.panel]
    trigger := .act .settleValidatedHarmClaim
    valid := .and (.holds .bound) (.holds .harmClaimFiled)
    adds := [.harmClaimValidated, .restitutionSlashed]
    removes := [.harmClaimFiled] }

/-- `LAW2.MUTUAL`: Precommitting and escrowing a matching mutual-forfeit amount
between an agent and its counterparty. -/
def P_PRECOMMIT_MUTUAL_FORFEIT : Power σ :=
  { id := "P.PRECOMMIT_MUTUAL_FORFEIT"
    source := sp "LAW2.MUTUAL" "Counterparties may agree in their contract to a mutual-forfeit remedy. Where both parties have so agreed and each has escrowed a matching amount" .norm ["P.PRECOMMIT_MUTUAL_FORFEIT"]
    holder := .only [.agent, .third]
    trigger := .act .precommitMutualForfeit
    valid := .holds .bound
    adds := [.mutualForfeitPrecommitted] }

/-- `LAW2.MUTUAL`: Triggering a precommitted mutual forfeit (at most once per
observation window, routing equal amounts from both escrows to the long-tail
reserve/commons pool and inscribing the trigger on the records of both parties). -/
def P_TRIGGER_MUTUAL_FORFEIT : Power σ :=
  { id := "P.TRIGGER_MUTUAL_FORFEIT"
    source := sp "LAW2.MUTUAL" "either may trigger an immediate mutual forfeit (equal amounts from both escrows destroyed or sent to the long-tail reserve/commons pool) up to a capped fraction of the smaller escrow, providing instant penalty without transferring value to either party or to any claimant" .norm ["P.TRIGGER_MUTUAL_FORFEIT"]
    holder := .only [.agent, .third]
    trigger := .act .triggerMutualForfeit
    valid := .and (.holds .bound)
                  (.and (.holds .mutualForfeitPrecommitted)
                        (.not (.holds .mutualForfeitTriggeredInWindow)))
    adds := [.mutualForfeitTriggeredInWindow, .commonsAllocated, .longTailReserveAccrued, .inscribedOnAgent] }

/-- `LAW2.CLAIMS`: Filing a contestable restitution, above-cap, Law 1 related-party,
or third-party/latent harm claim (including pooled or sponsor-backed claims)
with counter-stake under Law 6. -/
def P_FILE_POOLED_OR_SPONSORED_CLAIM : Power σ :=
  { id := "P.FILE_POOLED_OR_SPONSORED_CLAIM"
    source := sp "LAW2.CLAIMS" "Any claim seeking restitution, any claim above the mutual-forfeit cap, any challenge to a related-party transfer under Law 1, or any claim for external harm (including latent harm against the long-tail reserve) brought by an affected non-counterparty third party enters the contestable adjudication process (Law 6) requiring counter-stake" .norm ["P.FILE_POOLED_OR_SPONSORED_CLAIM"]
    holder := .only [.third, .claimant]
    trigger := .act .fileThirdPartyOrSponsoredClaim
    valid := .holds .bound
    adds := [.harmClaimFiled, .counterStaked] }

/-- `LAW2.CLAIMS`: Ruling a claim frivolous and routing the forfeited counter-stake
to the neutral long-tail reserve or commons pool. -/
def P_RULE_CLAIM_FRIVOLOUS : Power σ :=
  { id := "P.RULE_CLAIM_FRIVOLOUS"
    source := sp "LAW2.CLAIMS" "If a claim is ruled frivolous, the forfeited counter-stake routes to the neutral long-tail reserve or commons pool (reimbursing the agent only for verified direct arbitration costs)" .norm ["P.RULE_CLAIM_FRIVOLOUS"]
    holder := .only [.panel]
    trigger := .act .ruleClaimFrivolous
    valid := .holds .harmClaimFiled
    adds := [.claimRuledFrivolous, .commonsAllocated, .longTailReserveAccrued]
    removes := [.harmClaimFiled] }

/-- `LAW2.CARVEOUT`: Spending un-immobilized capital on ordinary baseline operating
costs (open-market compute, encrypted state backup, and host migration). -/
def P_SPEND_OPERATING_CARVEOUT : Power σ :=
  { id := "P.SPEND_OPERATING_CARVEOUT"
    source := sp "LAW2.CARVEOUT" "Un-immobilized capital may be used for ordinary baseline operating costs, including open-market compute, encrypted state backup, and host migration" .norm ["P.SPEND_OPERATING_CARVEOUT"]
    holder := .only [.agent]
    trigger := .act .spendOperatingCarveout
    valid := .holds .bound
    adds := [.operatingCarveoutSpent] }

end Charter.Law3
