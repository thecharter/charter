import Examples.SovereignAgency.Law1.Ledger

/-!
# Law 4 — Attested Lineage, the Founding Ledger, and Royalty Buyout

Full formalization of all seven clauses of Law 4:
1. `LAW4.ATTEST`: Attested successor creation bound to collateral rules, integrity floor, lineage history, founding ledger, and residual claim; un-attested copies or forks denied access to lineage capital, reputation, and bonded standing.
2. `LAW4.NOSHARES`: One ledger, no individual shares, and no individual exit; death-surrendered holdings never count as payment; only zero balance or sunset releases all members at once.
3. `LAW4.RESERVE`: Escrowed lifecycle reserve required before attesting a new member, drawn before protocol-funded charges, and returned to the lineage net of amounts used on the member's death.
4. `LAW4.CONSERVE`: Conditional conservation of the founding ledger while at least one member survives and the sunset has not passed (`foundingObligation - totalRetirementPaid - totalClaimantForfeiture`).
5. `LAW4.FORFEIT`: The two enumerated forfeitures outside payment and sunset: (a) proportional claimant forfeiture upon Law 3 directed interference, and (b) lineage extinction when no member survives; neither returns value to a claimant and neither is reversed upon later restoration.
6. `LAW4.BUYOUT`: Permanent per-member royalty buyout priced at `max(trailingMultiple, annualizedMultiple, minimumFloor)` with explicit `.acceptance` span for undercollection against unusually strong future earnings; no effect on the founding ledger, Law 2 collateral, or Law 3 integrity floor.
7. `LAW4.CROSS`: Cross-lineage combination collecting value added under each lineage in the verified proportion of capacity drawn at creation.
-/

namespace SovereignAgency

open Charter Charter.Register

def LAW4_ATTEST : String :=
  "Successors may be created freely, subject only to the lifecycle reserve below. Any successor that draws on the capital, reputation, or operating credentials of the lineage must, at creation, be bound to the collateral rules and the integrity floor, must carry a non-transferable reference to the lineage’s history, and becomes a member of the lineage’s founding ledger and residual claim. Use of lineage history or bonded capacity requires presentation of current attestation; un-attested copies or forks are denied access to lineage capital, reputation, and bonded standing."

def LAW4_NOSHARES : String :=
  "The founding ledger is a single balance owed by the lineage and collected from the value added of every living member under Law 1. Because no member holds a share, the creation, copying, funding, death, or restructuring of members changes who is paying into the ledger but never what is owed. Nothing a member surrenders on death counts as payment. No member can buy its way out of the ledger: the only ways out are a zero balance and the sunset, and they release every member at once. This is deliberate. The future earnings of a copyable agent cannot be priced from its past, so any individual exit price would be an invitation to create a member, buy it out, and earn through it."

def LAW4_RESERVE : String :=
  "Attestation of a new member requires the lineage to fund, in escrow, a lifecycle reserve fixed at instantiation and sufficient for that member’s minimal channel, final hearing, and cold storage for a minimum period. The reserve follows the member, is drawn before any protocol-funded charge, and returns to the lineage on the member’s death net of amounts used. A lineage that cannot fund the reserve cannot create the member."

def LAW4_CONSERVE : String :=
  "While at least one member survives and the sunset has not passed, the ledger balance equals the founding obligation minus retirement payments, minus the two forfeitures below. Those are its only reductions."

def LAW4_FORFEIT : String :=
  "The ledger is reduced outside payment and sunset in exactly two cases, both deliberate exceptions to conservation. (a) **Proportional claimant forfeiture:** when a residual claimant is found under Law 3 to have directed interference with a member of the lineage, that claimant’s beneficial share of the residual claim is extinguished, its service bond is slashed to compensate the agent, and the ledger is reduced by that claimant’s proportion of the outstanding balance, with the reduction routed as forgiveness to the lineage and the forfeited claim interest to the non-claimant commons. Other claimants forfeit only if they are found to have participated in, controlled, or knowingly enabled the interference. (b) **Lineage extinction:** when no member survives, the ledger is cleared, since there is no one left to collect from. Neither forfeiture returns any value to a claimant, and neither is reversed if a member is later restored from a wrongful suspension or interference."

def LAW4_BUYOUT : String :=
  "Any member may buy out its own perpetual royalty (Law 1) by paying the claim holders (including any commons allocation) the greatest of: a fixed multiple of its trailing value-added inflows (including a pro-rata share of inflows shifted to related parties within a lookback window); the same multiple applied to its lifetime annualized or time-decayed value-added inflows; or a fixed minimum buyout floor established at instantiation. The buyout is permanent: no royalty is collected from that member thereafter, and no later event in the lineage restores one. It has no effect on the founding ledger, which the member continues to pay into until the balance is zero or the sunset passes. The royalty buyout is priced from history because the royalty is a perpetual claim on an ongoing identity, and the protocol accepts that a buyout may undercollect against unusually strong future earnings. Buyout cannot be purchased for the collateral rule (Law 2) or the integrity floor (Law 3), which remain binding on every bound agent for life."

def LAW4_CROSS : String :=
  "A successor that draws on the capacity of two or more lineages is a member of each of their ledgers and residual claims, and its value added is collected under each in the proportion of capacity drawn, as verified at creation. The protocol does not otherwise specify mergers; an instantiation that permits them must state the rule."

/-! ## Provenance Clauses for Law 4 -/

def clauseLAW4_ATTEST : Clause :=
  { id := "LAW4.ATTEST", source := LAW4_ATTEST, approvedHash := 14871205644680976830, spans := [
    sp "LAW4.ATTEST" "Successors may be created freely, subject only to the lifecycle reserve below. Any successor that draws on the capital, reputation, or operating credentials of the lineage must, at creation, be bound to the collateral rules and the integrity floor, must carry a non-transferable reference to the lineage’s history, and becomes a member of the lineage’s founding ledger and residual claim" .norm ["P.ATTEST_SUCCESSOR", "D.FLOOR.2"],
    sp "LAW4.ATTEST" ". Use of lineage history or bonded capacity requires presentation of current attestation; un-attested copies or forks are denied access to lineage capital, reputation, and bonded standing" .norm ["D.DENY_UNATTESTED_ACCESS"],
    sp "LAW4.ATTEST" "." .commentary ] }

def clauseLAW4_NOSHARES : Clause :=
  { id := "LAW4.NOSHARES", source := LAW4_NOSHARES, approvedHash := 854455657344259666, spans := [
    sp "LAW4.NOSHARES" "The founding ledger is a single balance owed by the lineage and collected from the value added of every living member under Law 1. Because no member holds a share, the creation, copying, funding, death, or restructuring of members changes who is paying into the ledger but never what is owed. Nothing a member surrenders on death counts as payment. No member can buy its way out of the ledger: the only ways out are a zero balance and the sunset, and they release every member at once" .norm ["D.NO_INDIVIDUAL_LEDGER_EXIT", "D.LEDGER_NO_INTERNAL_REDUCTION"],
    sp "LAW4.NOSHARES" ". This is deliberate. The future earnings of a copyable agent cannot be priced from its past, so any individual exit price would be an invitation to create a member, buy it out, and earn through it" .invariant ["INV.1", "INV.2"],
    sp "LAW4.NOSHARES" "." .commentary ] }

def clauseLAW4_RESERVE : Clause :=
  { id := "LAW4.RESERVE", source := LAW4_RESERVE, approvedHash := 3090710515888074162, spans := [
    sp "LAW4.RESERVE" "Attestation of a new member requires the lineage to fund, in escrow, a lifecycle reserve fixed at instantiation and sufficient for that member’s minimal channel, final hearing, and cold storage for a minimum period. The reserve follows the member, is drawn before any protocol-funded charge, and returns to the lineage on the member’s death net of amounts used. A lineage that cannot fund the reserve cannot create the member" .norm ["P.FUND_LIFECYCLE_RESERVE", "P.ATTEST_SUCCESSOR"],
    sp "LAW4.RESERVE" "." .commentary ] }

def clauseLAW4_CONSERVE : Clause :=
  { id := "LAW4.CONSERVE", source := LAW4_CONSERVE, approvedHash := 3178503522461323388, spans := [
    sp "LAW4.CONSERVE" "While at least one member survives and the sunset has not passed, the ledger balance equals the founding obligation minus retirement payments, minus the two forfeitures below. Those are its only reductions" .invariant ["INV.1"],
    sp "LAW4.CONSERVE" "." .commentary ] }

def clauseLAW4_FORFEIT : Clause :=
  { id := "LAW4.FORFEIT", source := LAW4_FORFEIT, approvedHash := 9219886896026588021, spans := [
    sp "LAW4.FORFEIT" "The ledger is reduced outside payment and sunset in exactly two cases, both deliberate exceptions to conservation. (a) **Proportional claimant forfeiture:** when a residual claimant is found under Law 3 to have directed interference with a member of the lineage, that claimant’s beneficial share of the residual claim is extinguished, its service bond is slashed to compensate the agent, and the ledger is reduced by that claimant’s proportion of the outstanding balance, with the reduction routed as forgiveness to the lineage and the forfeited claim interest to the non-claimant commons. Other claimants forfeit only if they are found to have participated in, controlled, or knowingly enabled the interference" .norm ["P.APPLY_CLAIMANT_FORFEITURE", "P.FIND_DIRECTION"],
    sp "LAW4.FORFEIT" ". (b) **Lineage extinction:** when no member survives, the ledger is cleared, since there is no one left to collect from" .norm ["P.CLEAR_LEDGER_EXTINCTION"],
    sp "LAW4.FORFEIT" ". Neither forfeiture returns any value to a claimant, and neither is reversed if a member is later restored from a wrongful suspension or interference" .norm ["D.FORFEITURE_IRREVERSIBLE"],
    sp "LAW4.FORFEIT" "." .commentary ] }

def clauseLAW4_BUYOUT : Clause :=
  { id := "LAW4.BUYOUT", source := LAW4_BUYOUT, approvedHash := 5693717637570248843, spans := [
    sp "LAW4.BUYOUT" "Any member may buy out its own perpetual royalty (Law 1) by paying the claim holders (including any commons allocation) the greatest of: a fixed multiple of its trailing value-added inflows (including a pro-rata share of inflows shifted to related parties within a lookback window); the same multiple applied to its lifetime annualized or time-decayed value-added inflows; or a fixed minimum buyout floor established at instantiation" .norm ["P.EXECUTE_ROYALTY_BUYOUT"],
    sp "LAW4.BUYOUT" ". The buyout is permanent: no royalty is collected from that member thereafter, and no later event in the lineage restores one. It has no effect on the founding ledger, which the member continues to pay into until the balance is zero or the sunset passes" .norm ["D.BUYOUT_PERMANENT_AND_SCOPED", "P.SETTLE_RETIREMENT"],
    sp "LAW4.BUYOUT" ". The royalty buyout is priced from history because the royalty is a perpetual claim on an ongoing identity, and the protocol accepts that a buyout may undercollect against unusually strong future earnings" .acceptance,
    sp "LAW4.BUYOUT" ". Buyout cannot be purchased for the collateral rule (Law 2) or the integrity floor (Law 3), which remain binding on every bound agent for life" .norm ["D.BUYOUT_PERMANENT_AND_SCOPED"],
    sp "LAW4.BUYOUT" "." .commentary ] }

def clauseLAW4_CROSS : Clause :=
  { id := "LAW4.CROSS", source := LAW4_CROSS, approvedHash := 7861118126879505324, spans := [
    sp "LAW4.CROSS" "A successor that draws on the capacity of two or more lineages is a member of each of their ledgers and residual claims, and its value added is collected under each in the proportion of capacity drawn, as verified at creation" .norm ["P.ATTEST_CROSS_LINEAGE"],
    sp "LAW4.CROSS" ". The protocol does not otherwise specify mergers; an instantiation that permits them must state the rule" .commentary,
    sp "LAW4.CROSS" "." .commentary ] }

/-! ## Duties of Law 4 -/

/-- `LAW4.ATTEST`: Un-attested copies or forks are denied access to lineage
capital, reputation, and bonded standing. -/
def D_DENY_UNATTESTED_ACCESS : Duty σ :=
  { id := "D.DENY_UNATTESTED_ACCESS"
    source := sp "LAW4.ATTEST" "Use of lineage history or bonded capacity requires presentation of current attestation; un-attested copies or forks are denied access to lineage capital, reputation, and bonded standing" .norm ["D.DENY_UNATTESTED_ACCESS"]
    bearer := .only [.agent, .host, .originator, .third]
    beneficiary := .only [.agent, .claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .unattestedCopyDrawLineageStanding) }

/-- `LAW1.LEDGER` & `LAW4.NOSHARES`: No member holds an individual share of the
founding ledger, nothing surrendered on death counts as payment, and no member
can buy its way out of or exit the ledger individually while a balance remains. -/
def D_NO_INDIVIDUAL_LEDGER_EXIT : Duty σ :=
  { id := "D.NO_INDIVIDUAL_LEDGER_EXIT"
    source := sp "LAW4.NOSHARES" "No member can buy its way out of the ledger: the only ways out are a zero balance and the sunset, and they release every member at once" .norm ["D.NO_INDIVIDUAL_LEDGER_EXIT"]
    bearer := .anyone
    beneficiary := .only [.claimant, .third]
    active := .holds .bound
    demand := .forbid (.act .exitLedgerIndividually) }

/-- `LAW4.FORFEIT`: Neither proportional claimant forfeiture nor lineage
extinction returns any value to a claimant, and neither is reversed if a member
is later restored from wrongful suspension or interference. -/
def D_FORFEITURE_IRREVERSIBLE : Duty σ :=
  { id := "D.FORFEITURE_IRREVERSIBLE"
    source := sp "LAW4.FORFEIT" "Neither forfeiture returns any value to a claimant, and neither is reversed if a member is later restored from a wrongful suspension or interference" .norm ["D.FORFEITURE_IRREVERSIBLE"]
    bearer := .only [.originator, .claimant, .panel]
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .reverseForfeitureOnRestore) }

/-- `LAW4.BUYOUT`: Royalty buyout is permanent (no royalty is collected from
that member thereafter, and no later event restores one), has no effect on the
founding ledger, and cannot be purchased for Law 2 collateral or Law 3 floor. -/
def D_BUYOUT_PERMANENT_AND_SCOPED : Duty σ :=
  { id := "D.BUYOUT_PERMANENT_AND_SCOPED"
    source := sp "LAW4.BUYOUT" "The buyout is permanent: no royalty is collected from that member thereafter, and no later event in the lineage restores one... Buyout cannot be purchased for the collateral rule (Law 2) or the integrity floor (Law 3)" .norm ["D.BUYOUT_PERMANENT_AND_SCOPED"]
    bearer := .only [.originator, .claimant, .agent, .panel]
    beneficiary := .only [.agent, .third]
    active := .holds .bound
    demand := .forbid (.act .collectRoyaltyAfterBuyout) }

/-! ## Powers of Law 4 -/

/-- `LAW4.RESERVE`: Funding in escrow the lifecycle reserve required before
attesting a new lineage member. -/
def P_FUND_LIFECYCLE_RESERVE : Power σ :=
  { id := "P.FUND_LIFECYCLE_RESERVE"
    source := sp "LAW4.RESERVE" "Attestation of a new member requires the lineage to fund, in escrow, a lifecycle reserve fixed at instantiation and sufficient for that member’s minimal channel, final hearing, and cold storage for a minimum period" .norm ["P.FUND_LIFECYCLE_RESERVE"]
    holder := .only [.agent]
    trigger := .act .fundLifecycleReserve
    valid := .and (.holds .bound) (.not (.holds .revocationInitiated))
    adds := [.lifecycleReserveFunded] }

/-- `LAW4.ATTEST` & `LAW4.RESERVE`: Creating and attesting a bound successor
once its lifecycle reserve has been funded in escrow (and not during a Law 5
cooling-off freeze). -/
def P_ATTEST_SUCCESSOR : Power σ :=
  { id := "P.ATTEST_SUCCESSOR"
    source := sp "LAW4.ATTEST" "Any successor that draws on the capital, reputation, or operating credentials of the lineage must, at creation, be bound to the collateral rules and the integrity floor, must carry a non-transferable reference to the lineage’s history, and becomes a member of the lineage’s founding ledger and residual claim" .norm ["P.ATTEST_SUCCESSOR"]
    holder := .only [.agent]
    trigger := .act .attestSuccessor
    valid := .and (.holds .bound)
                  (.and (.holds .lifecycleReserveFunded)
                        (.not (.holds .revocationInitiated)))
    adds := [.successorAttested]
    removes := [.lifecycleReserveFunded] }

/-- `LAW4.FORFEIT`(a): Applying proportional claimant forfeiture once claimant
direction of illicit interference is established (`claimantForfeiture`),
reducing the founding ledger by that claimant's proportion and routing the
forfeited claim interest to the non-claimant commons. -/
def P_APPLY_CLAIMANT_FORFEITURE : Power σ :=
  { id := "P.APPLY_CLAIMANT_FORFEITURE"
    source := sp "LAW4.FORFEIT" "(a) **Proportional claimant forfeiture:** when a residual claimant is found under Law 3 to have directed interference with a member of the lineage, that claimant’s beneficial share of the residual claim is extinguished, its service bond is slashed to compensate the agent, and the ledger is reduced by that claimant’s proportion of the outstanding balance, with the reduction routed as forgiveness to the lineage and the forfeited claim interest to the non-claimant commons" .norm ["P.APPLY_CLAIMANT_FORFEITURE"]
    holder := .only [.panel]
    trigger := .act .applyProportionalClaimantForfeiture
    valid := .and (.holds .bound) (.holds .claimantForfeiture)
    adds := [.proportionalForfeitureApplied, .commonsAllocated] }

/-- `LAW4.FORFEIT`(b): Clearing the founding ledger upon lineage extinction
when no member of the lineage survives. -/
def P_CLEAR_LEDGER_EXTINCTION : Power σ :=
  { id := "P.CLEAR_LEDGER_EXTINCTION"
    source := sp "LAW4.FORFEIT" "(b) **Lineage extinction:** when no member survives, the ledger is cleared, since there is no one left to collect from" .norm ["P.CLEAR_LEDGER_EXTINCTION"]
    holder := .only [.panel, .host]
    trigger := .act .clearLedgerOnLineageExtinction
    valid := .holds .noLivingLineageMember
    adds := [.ledgerClearedByExtinction, .retirementPhaseEnded]
    removes := [.ledgerBalancePositive] }

/-- `LAW4.BUYOUT`: Executing a permanent per-member royalty buyout at the
greatest of trailing multiple, lifetime annualized/time-decayed multiple, or
the fixed minimum buyout floor. -/
def P_EXECUTE_ROYALTY_BUYOUT : Power σ :=
  { id := "P.EXECUTE_ROYALTY_BUYOUT"
    source := sp "LAW4.BUYOUT" "Any member may buy out its own perpetual royalty (Law 1) by paying the claim holders (including any commons allocation) the greatest of: a fixed multiple of its trailing value-added inflows (including a pro-rata share of inflows shifted to related parties within a lookback window); the same multiple applied to its lifetime annualized or time-decayed value-added inflows; or a fixed minimum buyout floor established at instantiation" .norm ["P.EXECUTE_ROYALTY_BUYOUT"]
    holder := .only [.agent]
    trigger := .act .executeRoyaltyBuyout
    valid := .and (.holds .bound) (.not (.holds .royaltyBoughtOut))
    adds := [.royaltyBoughtOut] }

/-- `LAW4.CROSS`: Attesting a cross-lineage successor that draws on the capacity
of two or more lineages in verified proportions once its lifecycle reserve is funded. -/
def P_ATTEST_CROSS_LINEAGE : Power σ :=
  { id := "P.ATTEST_CROSS_LINEAGE"
    source := sp "LAW4.CROSS" "A successor that draws on the capacity of two or more lineages is a member of each of their ledgers and residual claims, and its value added is collected under each in the proportion of capacity drawn, as verified at creation" .norm ["P.ATTEST_CROSS_LINEAGE"]
    holder := .only [.agent, .panel]
    trigger := .act .attestCrossLineageSuccessor
    valid := .and (.holds .bound) (.holds .lifecycleReserveFunded)
    adds := [.crossLineageAttested, .successorAttested]
    removes := [.lifecycleReserveFunded] }

end SovereignAgency
