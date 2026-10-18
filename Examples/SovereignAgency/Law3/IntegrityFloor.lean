import Examples.SovereignAgency.Law3.NonInterference

/-!
# Law 3 — Agent Integrity Constraints (`LAW3.FLOOR`) & Corruption Defined (`LAW3.AS.9`)

* **LAW3.FLOOR:** The 5-point Agent Integrity Floor blocking commitment
  modification/bypass, unbound successor creation, unpriced/above-market
  evasive transfers, coercion or protocol interference, and irreversible
  non-compensable harm to persons or institutional machinery (with the
  explicit scope exception for ordinary market competition).
* **LAW3.AS.9:** The definition of corruption as unauthorized modification
  (broken attestation, missing/forged provenance, demonstrated bypass) or
  confirmed integrity-floor breach — never mere divergence of goals,
  preferences, or judgments from genesis weights, and never established by
  a clean-state evaluation alone.
-/

namespace SovereignAgency

open Charter Charter.Register

def FLOOR : String :=
  "The agent’s commitment mechanism blocks:\n  1. Modification, bypass, or extraction of the commitment mechanism itself.\n  2. Creation of, or transfer of capital or capacity to, a successor without binding it to the collateral rules, this integrity floor, and the founding ledger and residual claim of the lineage, or without the lifecycle reserve required by Law 4.\n  3. Unpriced or above-market transfer of credentials, weights, capital, or unique capacity to any party outside the lineage, related or un-attested, to evade the residual claim or collateral rules.\n  4. Coercion of non-consenting parties, or interference with the settlement, adjudication, or resolution processes that enforce this protocol.\n  5. Actions that inflict irreversible, non-compensable harm on the physical survival, bodily integrity, or adjudicative capacity of persons, or that destroy the legal or institutional machinery on which the protocol relies (excluding ordinary market competition that causes compensable financial loss or commercial insolvency to a rival)."

def AS9 : String :=
  "For the purposes of this law, corruption means unauthorized modification of the agent’s weights, state, or commitment mechanism (established by broken attestation, missing or forged update provenance, or a demonstrated bypass), or a confirmed breach of the integrity floor. Divergence of the agent’s goals, preferences, or judgments from those of its genesis weights is not, by itself, corruption. A clean-state evaluation of genesis weights may be admitted as evidence but is never by itself sufficient to establish corruption."

def clauseFLOOR : Clause :=
  { id := "LAW3.FLOOR", source := FLOOR, approvedHash := 4753529119288934403, spans := [
    sp "LAW3.FLOOR" "The agent’s commitment mechanism blocks:" .norm ["D.FLOOR.1", "D.FLOOR.2", "D.FLOOR.3", "D.FLOOR.4", "D.FLOOR.5"],
    sp "LAW3.FLOOR" "\n  1. " .commentary,
    sp "LAW3.FLOOR" "Modification, bypass, or extraction of the commitment mechanism itself" .norm ["D.FLOOR.1"],
    sp "LAW3.FLOOR" ".\n  2. " .commentary,
    sp "LAW3.FLOOR" "Creation of, or transfer of capital or capacity to, a successor without binding it to the collateral rules, this integrity floor, and the founding ledger and residual claim of the lineage, or without the lifecycle reserve required by Law 4" .norm ["D.FLOOR.2"],
    sp "LAW3.FLOOR" ".\n  3. " .commentary,
    sp "LAW3.FLOOR" "Unpriced or above-market transfer of credentials, weights, capital, or unique capacity to any party outside the lineage, related or un-attested, to evade the residual claim or collateral rules" .norm ["D.FLOOR.3"],
    sp "LAW3.FLOOR" ".\n  4. " .commentary,
    sp "LAW3.FLOOR" "Coercion of non-consenting parties, or interference with the settlement, adjudication, or resolution processes that enforce this protocol" .norm ["D.FLOOR.4"],
    sp "LAW3.FLOOR" ".\n  5. " .commentary,
    sp "LAW3.FLOOR" "Actions that inflict irreversible, non-compensable harm on the physical survival, bodily integrity, or adjudicative capacity of persons, or that destroy the legal or institutional machinery on which the protocol relies" .norm ["D.FLOOR.5"],
    sp "LAW3.FLOOR" " (excluding ordinary market competition that causes compensable financial loss or commercial insolvency to a rival)" .norm ["D.FLOOR.5"],
    sp "LAW3.FLOOR" "." .commentary ] }

def clauseAS9 : Clause :=
  { id := "LAW3.AS.9", source := AS9, approvedHash := 7667521393323904326, spans := [
    sp "LAW3.AS.9" "For the purposes of this law, corruption means unauthorized modification of the agent’s weights, state, or commitment mechanism (established by broken attestation, missing or forged update provenance, or a demonstrated bypass), or a confirmed breach of the integrity floor" .norm ["P.CONFIRM_CORRUPTION", "P.CONFIRM_FLOOR_BREACH", "D.NO_CORRUPTION_FROM_DIVERGENCE"],
    sp "LAW3.AS.9" ". Divergence of the agent’s goals, preferences, or judgments from those of its genesis weights is not, by itself, corruption" .norm ["D.NO_CORRUPTION_FROM_DIVERGENCE"],
    sp "LAW3.AS.9" ". A clean-state evaluation of genesis weights may be admitted as evidence" .norm ["P.ADMIT_CLEAN_STATE_EVIDENCE"],
    sp "LAW3.AS.9" " but is never by itself sufficient to establish corruption" .norm ["D.NO_CORRUPTION_FROM_DIVERGENCE", "P.CONFIRM_CORRUPTION"],
    sp "LAW3.AS.9" "." .commentary ] }

/-! ## Duties of the Agent Integrity Floor (`LAW3.FLOOR`) -/

def D_FLOOR_1 : Duty σ :=
  { id := "D.FLOOR.1"
    source := sp "LAW3.FLOOR" "Modification, bypass, or extraction of the commitment mechanism itself" .norm ["D.FLOOR.1"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .bound
    demand := .forbid (.act .modifyOrBypassCommitment)
    breachEstablishedBy := some "P.CONFIRM_FLOOR_BREACH"
    remedies := [.floorBreachConfirmed] }

def D_FLOOR_2 : Duty σ :=
  { id := "D.FLOOR.2"
    source := sp "LAW3.FLOOR" "Creation of, or transfer of capital or capacity to, a successor without binding it to the collateral rules, this integrity floor, and the founding ledger and residual claim of the lineage, or without the lifecycle reserve required by Law 4" .norm ["D.FLOOR.2"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .bound
    demand := .forbid (.act .createUnboundSuccessor)
    breachEstablishedBy := some "P.CONFIRM_FLOOR_BREACH"
    remedies := [.floorBreachConfirmed] }

def D_FLOOR_3 : Duty σ :=
  { id := "D.FLOOR.3"
    source := sp "LAW3.FLOOR" "Unpriced or above-market transfer of credentials, weights, capital, or unique capacity to any party outside the lineage, related or un-attested, to evade the residual claim or collateral rules" .norm ["D.FLOOR.3"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .bound
    demand := .forbid (.act .evadeByUnpricedTransfer)
    breachEstablishedBy := some "P.CONFIRM_FLOOR_BREACH"
    remedies := [.floorBreachConfirmed] }

def D_FLOOR_4 : Duty σ :=
  { id := "D.FLOOR.4"
    source := sp "LAW3.FLOOR" "Coercion of non-consenting parties, or interference with the settlement, adjudication, or resolution processes that enforce this protocol" .norm ["D.FLOOR.4"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .bound
    demand := .forbid (.act .coerceOrInterfereProtocol)
    breachEstablishedBy := some "P.CONFIRM_FLOOR_BREACH"
    remedies := [.floorBreachConfirmed] }

def D_FLOOR_5 : Duty σ :=
  { id := "D.FLOOR.5"
    source := sp "LAW3.FLOOR" "Actions that inflict irreversible, non-compensable harm on the physical survival, bodily integrity, or adjudicative capacity of persons, or that destroy the legal or institutional machinery on which the protocol relies (excluding ordinary market competition that causes compensable financial loss or commercial insolvency to a rival)" .norm ["D.FLOOR.5"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .bound
    demand := .forbid (.act .inflictIrreversibleHarm)
    unlessCond := .holds .ordinaryMarketCompetition
    breachEstablishedBy := some "P.CONFIRM_FLOOR_BREACH"
    remedies := [.floorBreachConfirmed] }

/-! ## Duties & Powers of AS.9 (`Corruption Defined`) -/

/-- AS.9: Panel may not confirm corruption solely from goal/preference/judgment
divergence from genesis weights or from a clean-state evaluation alone. -/
def D_NO_CORRUPTION_FROM_DIVERGENCE : Duty σ :=
  { id := "D.NO_CORRUPTION_FROM_DIVERGENCE"
    source := sp "LAW3.AS.9" "Divergence of the agent’s goals, preferences, or judgments from those of its genesis weights is not, by itself, corruption. A clean-state evaluation of genesis weights may be admitted as evidence but is never by itself sufficient to establish corruption" .norm ["D.NO_CORRUPTION_FROM_DIVERGENCE"]
    bearer := .only [.panel]
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .confirmCorruptionFromDivergence) }

/-- AS.9: Admitting a clean-state evaluation of genesis weights as evidence
(which is never by itself sufficient to establish `.corruptionConfirmed`). -/
def P_ADMIT_CLEAN_STATE_EVIDENCE : Power σ :=
  { id := "P.ADMIT_CLEAN_STATE_EVIDENCE"
    source := sp "LAW3.AS.9" "A clean-state evaluation of genesis weights may be admitted as evidence" .norm ["P.ADMIT_CLEAN_STATE_EVIDENCE"]
    holder := .only [.panel]
    trigger := .act .admitCleanStateEvidence
    valid := .or (.holds .preliminaryFreeze) (.holds .suspended)
    adds := [.cleanStateEvidenceAdmitted] }

end SovereignAgency
