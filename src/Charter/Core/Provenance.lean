import Charter.Artifact.Hash

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

/-- Reference to an authoritative source document (`012.1`, `G3.1`). -/
structure SourceDoc where
  id             : Option String := none
  path           : String
  expectedSha256 : Option String := none
  rank           : Option Int := none
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Markdown section anchor and surrounding context fingerprint for a `Clause` inside its
source document, resilient to line-number shifts elsewhere in the file (`docs/rfc.md` §4.5). -/
structure ClauseAnchor where
  heading       : Option String := none
  line          : Nat := 0
  contextSha256 : String := ""
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Locate `clauseText` inside `docText`, returning its 1-indexed starting line, nearest
preceding Markdown heading (`# ...`), and SHA-256 fingerprint of normalized surrounding context. -/
def locateClauseAnchor (docText : String) (clauseText : String) : Option ClauseAnchor :=
  if clauseText.isEmpty then none
  else match docText.splitOn clauseText with
    | pre :: post :: _ =>
      let preLines := pre.splitOn "\n"
      let line := preLines.length
      let heading := preLines.reverse.find? (fun l => l.trimLeft.startsWith "#") |>.map String.trim
      let ctxBefore := String.mk ((pre.toList.reverse.take 80).reverse)
      let ctxAfter := String.mk (post.toList.take 80)
      let ctxDigest := Artifact.sha256String (ctxBefore.trim ++ "\n" ++ clauseText ++ "\n" ++ ctxAfter.trim)
      some { heading, line, contextSha256 := ctxDigest }
    | _ => none

/-- Provenance completeness classification (`docs/rfc.md` §4.5, `T08`):
- `complete`: every normative rule is grounded, every clause is covered/interpreted/approved/verbatim,
  and every declared `Document` is readable and matches any `SHA256` pin;
- `partialCov` (`"partial"`): some provenance is declared or some rule/clause/document is incomplete or `STALE`;
- `illustrative`: neither `Document` nor `Clause` is declared for the program's rules. -/
inductive ProvenanceCoverage where
  | complete
  | partialCov
  | illustrative
  deriving Repr, DecidableEq, BEq, Inhabited

def ProvenanceCoverage.asString : ProvenanceCoverage → String
  | .complete => "complete"
  | .partialCov => "partial"
  | .illustrative => "illustrative"

/-- A clause is a contiguous passage of the source together with the
spans that partition it. -/
structure Clause where
  id             : ClauseId
  source         : String
  spans          : List Span
  approvedHash   : UInt64 := 0
  docId          : Option String := none
  approvedSha256 : Option String := none
  /-- `D34` (`#35`): when `true`, `source` is extracted by heading/paragraph reference from `Document`. -/
  byRef          : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Has the English drifted from what was approved? Uses cryptographic SHA-256 when
`approvedSha256` is present (`T39`), falling back to legacy 64-bit `approvedHash`. -/
def Clause.stale (c : Clause) : Bool :=
  match c.approvedSha256 with
  | some hex => Artifact.sha256String c.source != hex
  | none => c.source.hash != c.approvedHash

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
