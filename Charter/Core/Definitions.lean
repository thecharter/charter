import Charter.Core.Provenance
import Charter.Core.Semantics

/-!
# Charter.Core.Definitions — Formal Definitions & Substrate Assumptions Provenance

Formalization of:
1. **Related-Party Graph (`RelatedPartyEdge`, `RelatedPartyGraph`, `isRelated`)**:
   Models the four relatedness criteria from the `Definitions` block (line 20 of
   `protocol/protocol-of-sovereign-agency.md`):
   - `sharesLineage`
   - `commonBeneficialControl`
   - `isOriginatorOrClaimant`
   - `economicallyDependent`
   Explicitly independent of `attested : Bool`, with proofs of reflexivity,
   symmetry (`isRelated_symm`), and attestation-independence (`isRelated_ignores_attestation`).
2. **Net Verified Resources (`VerifiedBalanceSheet`, `netVerifiedResources`)**:
   Models an agent's timestamped balance sheet (`fairValueCapitalAndCapacity` less
   `financialLiabilities`, `encumbrances`, and `borrowedPrincipal`, all measured at
   the same `timestamp`), with theorem `netVerifiedResources_deducts_all_liabilities`.
3. **Verbatim Provenance Clauses (`clauseDEF01` and `clauseSUB01`)**:
   Hash-tracked span partitions of the `Definitions` block (line 20) and the
   `Substrate Assumptions` block (line 147) of `protocol/protocol-of-sovereign-agency.md`.
-/

namespace Charter

open Register

/-! ## 1. Related-Party Graph & Attestation-Independent Relatedness -/

/-- A relationship record between two parties (`partyA` and `partyB`), tracking
the four protocol criteria of relatedness (`sharesLineage`,
`commonBeneficialControl`, `isOriginatorOrClaimant`, `economicallyDependent`)
alongside `attested : Bool` (which never establishes or defeats relatedness). -/
structure RelatedPartyEdge where
  partyA                  : Nat
  partyB                  : Nat
  sharesLineage           : Bool := false
  commonBeneficialControl : Bool := false
  isOriginatorOrClaimant  : Bool := false
  economicallyDependent   : Bool := false
  attested                : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A graph of related-party edges across entities. -/
abbrev RelatedPartyGraph := List RelatedPartyEdge

/-- Whether a `RelatedPartyEdge` satisfies at least one of the four relatedness
criteria of `DEF.01` (independent of `e.attested`). -/
def RelatedPartyEdge.hasRelation (e : RelatedPartyEdge) : Bool :=
  e.sharesLineage || e.commonBeneficialControl ||
  e.isOriginatorOrClaimant || e.economicallyDependent

/-- Whether edge `e` witnesses a relatedness link between `a` and `b` in either
direction. -/
def RelatedPartyEdge.connects (e : RelatedPartyEdge) (a b : Nat) : Bool :=
  ((e.partyA == a && e.partyB == b) || (e.partyA == b && e.partyB == a)) &&
  e.hasRelation

/-- Decidable relatedness predicate (`DEF.01`): reflexive (`a == b`) and
symmetric across all active relatedness edges in `G`, ignoring `attested`. -/
def isRelated (G : RelatedPartyGraph) (a b : Nat) : Bool :=
  (a == b) || G.any fun e => e.connects a b

theorem isRelated_refl (G : RelatedPartyGraph) (a : Nat) :
    isRelated G a a = true := by
  simp [isRelated]

theorem connects_symm (e : RelatedPartyEdge) (a b : Nat) :
    e.connects a b = e.connects b a := by
  unfold RelatedPartyEdge.connects
  rw [Bool.or_comm]

theorem any_connects_symm (G : RelatedPartyGraph) (a b : Nat) :
    (G.any fun e => e.connects a b) = (G.any fun e => e.connects b a) := by
  induction G with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.any_cons, connects_symm hd a b, ih]

/-- Relatedness is symmetric for all graphs `G` and entity IDs `a, b`. -/
theorem isRelated_symm : ∀ (G : RelatedPartyGraph) (a b : Nat),
    isRelated G a b = isRelated G b a := by
  intro G a b
  unfold isRelated
  have hBeq : (a == b) = (b == a) := by
    by_cases h : a = b
    · subst h; rfl
    · have h1 : (a == b) = false := beq_false_of_ne h
      have h2 : (b == a) = false := beq_false_of_ne (Ne.symm h)
      rw [h1, h2]
  rw [hBeq, any_connects_symm G a b]

/-- Toggling or modifying `attested` on any edge does not alter `e.connects a b`. -/
theorem connects_ignores_attestation (e : RelatedPartyEdge) (att : Bool) (a b : Nat) :
    ({ e with attested := att } : RelatedPartyEdge).connects a b = e.connects a b := rfl

/-- Toggling attestation status across `G` does not alter `isRelated G a b`
("affiliation is determined by beneficial control or economic dependence, not by
attestation status"). -/
theorem isRelated_ignores_attestation (G : RelatedPartyGraph) (a b : Nat) :
    isRelated (G.map fun e => { e with attested := !e.attested }) a b =
      isRelated G a b := by
  unfold isRelated
  congr 1
  induction G with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.map_cons, List.any_cons, connects_ignores_attestation, ih]

/-! ## 2. Verified Balance Sheet & Net Verified Resources -/

/-- Timestamped balance sheet of an agent (`DEF.01`), measuring capital and
productive capacity (weights, credentials, operating know-how) and all financial
liabilities, encumbrances, and borrowed principal at the same `timestamp`. -/
structure VerifiedBalanceSheet where
  timestamp                   : Nat
  fairValueCapitalAndCapacity : Nat
  financialLiabilities        : Nat
  encumbrances                : Nat
  borrowedPrincipal           : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An agent's net verified resources at `b.timestamp` (`DEF.01`):
`fairValueCapitalAndCapacity` less `financialLiabilities`, `encumbrances`, and
`borrowedPrincipal`. -/
def netVerifiedResources (b : VerifiedBalanceSheet) : Nat :=
  b.fairValueCapitalAndCapacity -
    (b.financialLiabilities + b.encumbrances + b.borrowedPrincipal)

/-- `netVerifiedResources` deducts all three liability categories (`financialLiabilities`,
`encumbrances`, and `borrowedPrincipal`) from `fairValueCapitalAndCapacity` at the
same timestamp `b.timestamp`. -/
theorem netVerifiedResources_deducts_all_liabilities (b : VerifiedBalanceSheet) :
    netVerifiedResources b =
      b.fairValueCapitalAndCapacity -
        (b.financialLiabilities + b.encumbrances + b.borrowedPrincipal) ∧
    netVerifiedResources b ≤ b.fairValueCapitalAndCapacity - b.financialLiabilities ∧
    netVerifiedResources b ≤ b.fairValueCapitalAndCapacity - b.encumbrances ∧
    netVerifiedResources b ≤ b.fairValueCapitalAndCapacity - b.borrowedPrincipal ∧
    (b.fairValueCapitalAndCapacity ≤
      b.financialLiabilities + b.encumbrances + b.borrowedPrincipal →
      netVerifiedResources b = 0) := by
  unfold netVerifiedResources
  refine ⟨rfl, by omega, by omega, by omega, fun _ => by omega⟩

/-! ## 3. Verbatim Provenance Clauses (`DEF.01` and `SUB.01`) -/

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

end Charter
