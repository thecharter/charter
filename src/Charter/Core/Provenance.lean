/-!
# Charter.Core.Provenance

Every formal object in Charter carries a `Span`: the exact English it is the
meaning of. Every span is classified into a `Register`, so that the model
can distinguish the kinds of sentence an institutional text mixes freely:

* a **norm** — something an actor must, may, can, or cannot do;
* an **invariant** — a property the norms are *intended* to secure
  (these become theorems about the norms, never rules);
* an **acceptance** — a limit the institution states it tolerates
  ("the charter accepts that..."); provably not a rule;
* **commentary** — rationale, foreword, examples;
* a **definition** — a term the norms are written over.

Lexical completeness of a clause means every token of its source text
belongs to at least one span, and every span has a register. This file
gives the data model; checking coverage is a function over the table.
-/

namespace Charter

/-- A stable clause identifier, e.g. `ART.3.2`. -/
abbrev ClauseId := String

/-- The register of a span of English: what *kind* of sentence it is. -/
inductive Register
  | norm          -- an obligation, prohibition, permission, power or immunity
  | invariant     -- a property the norms should secure; becomes a theorem
  | acceptance    -- a stated, tolerated limit; never a rule
  | commentary    -- rationale, motivation, examples
  | definition    -- a term introduced for the norms to use
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An exact span of the authoritative English, with the formal objects
that give it meaning. `meaning` lists the ids of the duties, powers, or
theorems that interpret it; a non-normative span has an empty `meaning`
and a register that says why. -/
structure Span where
  clause   : ClauseId
  text     : String
  register : Register
  meaning  : List String := []
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A clause is a contiguous passage of the source together with the
spans that partition it. -/
structure Clause where
  id     : ClauseId
  source : String
  spans  : List Span
  /-- Hash of the source text at the moment its spans and meanings were
  reviewed and approved. If the English changes, the approval is stale
  and every formal id the clause names loses its reviewed status until
  the mapping is re-approved. `0` = never approved. -/
  approvedHash : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Has the English drifted from what was approved? -/
def Clause.stale (c : Clause) : Bool := c.source.hash != c.approvedHash

/-- Formal ids whose review status is invalidated by a stale clause. -/
def Clause.invalidated (c : Clause) : List String :=
  if c.stale then (c.spans.flatMap (·.meaning)).eraseDups else []

/-- Lexical coverage: the spans, concatenated in order, reproduce the
source text exactly. This is the mechanical half of traceability; whether
each span's `meaning` is *faithful* is an act of review, not computation. -/
def Clause.covered (c : Clause) : Bool :=
  String.join (c.spans.map (·.text)) == c.source

/-- Normative coverage: every span in the `norm` register names at least
one formal object that interprets it. -/
def Clause.normsInterpreted (c : Clause) : Bool :=
  c.spans.all fun s => s.register != .norm || !s.meaning.isEmpty

/-- Reverse provenance: every formal id in `ids` is named by some span of
some clause. A formal rule with no English authority fails this check. -/
def reverseProvenance (clauses : List Clause) (ids : List String) : Bool :=
  ids.all fun i => clauses.any fun c => c.spans.any fun s => s.meaning.contains i

/-- All spans of a set of clauses plus any extra spans (e.g. the
`source` fields of a law's duties and powers, for provisions whose
clause tables are not yet written). -/
def reverseProvenanceWith (clauses : List Clause) (extra : List Span) (ids : List String) : Bool :=
  ids.all fun i =>
    (clauses.any fun c => c.spans.any fun s => s.meaning.contains i) ||
    (extra.any fun s => s.meaning.contains i)

/-- An explicit record of an open interpretive question where the English source
admits multiple readings, documenting the question and the chosen formal reading (§12 Q4). -/
structure AuthorshipQuestion where
  id            : String
  clauseId      : String
  question      : String
  chosenReading : String
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Core

export Charter (
  ClauseId
  Register
  Span
  Clause
  reverseProvenance
  reverseProvenanceWith
  AuthorshipQuestion
)

namespace Register
export Charter.Register (
  norm
  invariant
  acceptance
  commentary
  definition
)
end Register

namespace Clause
export Charter.Clause (
  stale
  invalidated
  covered
  normsInterpreted
)
end Clause

end Core

end Charter
