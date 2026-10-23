import Charter.Core.Semantics

/-!
# Charter.Core.Graph — Generic Affiliation Graphs & Verified Balance Sheets

Defines the law-agnostic affiliation / conflict-of-interest graph (`RelatedPartyEdge`,
`RelatedPartyGraph`, aliased as `AffiliationEdge` and `AffiliationGraph`, along
with `isRelated`, `isRelated_refl`, `isRelated_symm`, `isRelated_ignores_attestation`)
and the balance-sheet valuation primitives (`VerifiedBalanceSheet`,
`netVerifiedResources`, `netVerifiedResources_deducts_all_liabilities`) for the
universal Charter core (§3.3).
-/

namespace Charter

/-! ## 1. Affiliation / Related-Party Graph & Attestation-Independent Relatedness -/

/-- A relationship record between two parties (`partyA` and `partyB`), tracking
four structural criteria of relatedness (`sharesGroup`,
`commonBeneficialControl`, `isFounderOrStakeholder`, `economicallyDependent`)
alongside `attested : Bool` (which never establishes or defeats relatedness). -/
structure RelatedPartyEdge where
  partyA                  : Nat
  partyB                  : Nat
  sharesGroup           : Bool := false
  commonBeneficialControl : Bool := false
  isFounderOrStakeholder  : Bool := false
  economicallyDependent   : Bool := false
  attested                : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A graph of related-party edges across entities. -/
abbrev RelatedPartyGraph := List RelatedPartyEdge

/-- Law-agnostic alias for `RelatedPartyEdge` (§3.3). -/
abbrev AffiliationEdge := RelatedPartyEdge

/-- Law-agnostic alias for `RelatedPartyGraph` (§3.3). -/
abbrev AffiliationGraph := RelatedPartyGraph

/-- Whether a `RelatedPartyEdge` satisfies at least one of the four structural
relatedness criteria (independent of `e.attested`). -/
def RelatedPartyEdge.hasRelation (e : RelatedPartyEdge) : Bool :=
  e.sharesGroup || e.commonBeneficialControl ||
  e.isFounderOrStakeholder || e.economicallyDependent

/-- Whether edge `e` witnesses a relatedness link between `a` and `b` in either
direction. -/
def RelatedPartyEdge.connects (e : RelatedPartyEdge) (a b : Nat) : Bool :=
  ((e.partyA == a && e.partyB == b) || (e.partyA == b && e.partyB == a)) &&
  e.hasRelation

/-- Decidable relatedness predicate: reflexive (`a == b`) and symmetric across
all active relatedness edges in `G`, ignoring `attested`. -/
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

/-- Toggling attestation status across `G` does not alter `isRelated G a b`. -/
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

/-- Timestamped balance sheet of an entity, measuring capital and productive
capacity and all financial liabilities, encumbrances, and borrowed principal
at the same `timestamp`. -/
structure VerifiedBalanceSheet where
  timestamp                   : Nat
  fairValueCapitalAndCapacity : Nat
  financialLiabilities        : Nat
  encumbrances                : Nat
  borrowedPrincipal           : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An entity's net verified resources at `b.timestamp`:
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

namespace Core

export Charter (
  RelatedPartyEdge
  RelatedPartyGraph
  isRelated
  isRelated_refl
  connects_symm
  any_connects_symm
  isRelated_symm
  connects_ignores_attestation
  isRelated_ignores_attestation
  VerifiedBalanceSheet
  netVerifiedResources
  netVerifiedResources_deducts_all_liabilities
  AffiliationEdge
  AffiliationGraph
)

namespace RelatedPartyEdge
export Charter.RelatedPartyEdge (hasRelation connects)
end RelatedPartyEdge

end Core

end Charter
