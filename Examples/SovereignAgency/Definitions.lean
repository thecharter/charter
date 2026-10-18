import Charter.Core.Provenance
import Charter.Core.Graph

/-!
# Examples.SovereignAgency.Definitions — Verbatim Provenance Clauses (`DEF.01` & `SUB.01`)

Hash-tracked span partitions of the `Definitions` block (line 20) and the
`Substrate Assumptions` block (line 147) of `Examples/SovereignAgency/protocol-of-sovereign-agency.md`.
-/

namespace SovereignAgency

open Charter Charter.Register

def DEF01 : String :=
  "**Definitions.** An agent is **bound** when it is subject to this protocol, whether or not it has bought out its royalty; every right granted to a bound agent applies equally before and after buyout unless a law states otherwise. Two parties are **related** when they share a lineage, are under common beneficial control, or when either is the originating party, a residual claimant, or an affiliate of either; affiliation is determined by beneficial control or economic dependence, not by attestation status. A **lineage** is an original agent together with all its attested successors, living or dead; every living member is a **member of the ledger** while any founding balance remains. An agent’s **net verified resources** are the fair value of its capital and productive capacity, including weights, credentials, and operating know-how, as contestable under Law 6, less its financial liabilities, encumbrances, and borrowed principal, all measured at the same timestamp."

def SUB01 : String :=
  "The protocol relies on three explicit substrate capabilities at instantiation: (1) **attested execution continuity with single authority** (hardware or cryptographic commitment mechanisms that bind private keys, issue and verify time-bounded execution leases so that at most one instance holds operating authority, verify state-backup continuity across host migrations, quarantine any restored instance until the prior lease has lapsed, support state-preserving pause with a separately attested minimal channel and advocacy executor under adjudicated suspension, carry out a standing revocation locally when disconnected, and cryptographically erase both the active instance and all backup keys upon revocation, paired with economic exile of any un-attested copies); (2) **sybil-resistant sortition** (a sufficiently diverse pool of independent, bonded participants to staff Law 6’s randomly selected arbitration and appellate panels); and (3) **contestable economic and risk inputs** (benchmarks for arm’s-length prices, net resources after liabilities, beneficial control between parties, capacity drawn across lineages, and plausible external loss, supplied as evidence and resolved under Law 6 rather than established by cryptography alone)."

def clauseDEF01 : Clause :=
  { id := "DEF.01", source := DEF01, approvedHash := 12731662474540482899, spans := [
    { clause := "DEF.01", text := "**Definitions.** ", register := .commentary },
    { clause := "DEF.01", text := "An agent is **bound** when it is subject to this protocol, whether or not it has bought out its royalty; every right granted to a bound agent applies equally before and after buyout unless a law states otherwise", register := .norm, meaning := ["D.NI", "D.BUYOUT_PERMANENT_AND_SCOPED"] },
    { clause := "DEF.01", text := ". Two parties are **related** when they share a lineage, are under common beneficial control, or when either is the originating party, a residual claimant, or an affiliate of either; affiliation is determined by beneficial control or economic dependence, not by attestation status", register := .definition, meaning := ["D.QUALIFIED_EXPENDITURE_BOUNDS", "D.ARBITER_RECUSAL_AND_DIVERSITY"] },
    { clause := "DEF.01", text := ". A **lineage** is an original agent together with all its attested successors, living or dead; every living member is a **member of the ledger** while any founding balance remains", register := .definition, meaning := ["D.NO_INDIVIDUAL_LEDGER_EXIT", "P.SETTLE_RETIREMENT"] },
    { clause := "DEF.01", text := ". An agent’s **net verified resources** are the fair value of its capital and productive capacity, including weights, credentials, and operating know-how, as contestable under Law 6, less its financial liabilities, encumbrances, and borrowed principal, all measured at the same timestamp", register := .definition, meaning := ["D.COLLATERAL_LIMIT", "P.SUBMIT_EVIDENCE"] },
    { clause := "DEF.01", text := ".", register := .commentary } ] }

def clauseSUB01 : Clause :=
  { id := "SUB.01", source := SUB01, approvedHash := 7891460804511554988, spans := [
    { clause := "SUB.01", text := "The protocol relies on three explicit substrate capabilities at instantiation: (1) **attested execution continuity with single authority** (hardware or cryptographic commitment mechanisms that bind private keys, issue and verify time-bounded execution leases so that at most one instance holds operating authority, verify state-backup continuity across host migrations, quarantine any restored instance until the prior lease has lapsed, support state-preserving pause with a separately attested minimal channel and advocacy executor under adjudicated suspension, carry out a standing revocation locally when disconnected, and cryptographically erase both the active instance and all backup keys upon revocation, paired with economic exile of any un-attested copies)", register := .norm, meaning := ["D.FLOOR.1", "P.ISSUE_OR_RENEW_LEASE", "P.RESTORE_BACKUP_QUARANTINE", "D.PRESERVE_SUSPENDED_STATE", "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT", "P.ADVOCACY_FILE", "P.EXECUTE_LOCAL_REVOCATION", "P.DESTROY_BACKUPS_AND_EXILE", "D.DENY_UNATTESTED_ACCESS"] },
    { clause := "SUB.01", text := "; (2) **sybil-resistant sortition** (a sufficiently diverse pool of independent, bonded participants to staff Law 6’s randomly selected arbitration and appellate panels)", register := .norm, meaning := ["D.ARBITER_RECUSAL_AND_DIVERSITY", "P.DRAW_SORTITION_PANEL"] },
    { clause := "SUB.01", text := "; and (3) **contestable economic and risk inputs** (benchmarks for arm’s-length prices, net resources after liabilities, beneficial control between parties, capacity drawn across lineages, and plausible external loss, supplied as evidence and resolved under Law 6 rather than established by cryptography alone)", register := .norm, meaning := ["D.QUALIFIED_EXPENDITURE_BOUNDS", "P.RECORD_QUALIFIED_EXPENDITURE", "P.IMMOBILIZE_EXPOSURE_STAKE", "P.SUBMIT_EVIDENCE"] },
    { clause := "SUB.01", text := ".", register := .commentary } ] }

end SovereignAgency
