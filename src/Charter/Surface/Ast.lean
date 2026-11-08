import Charter.Core.Spec
import Charter.Surface.Diagnostics

/-!
# Charter.Surface.Ast — Phrases and directives

What a file says, phrase by phrase (eFLINT `Phrase`, `Directive`), with the
position of each top-level item so diagnostics and claims can name their line.
Declarations are `Charter.Decl` records (`Charter.Core.Spec`); expressions are
`Charter.Term`.
-/

namespace Charter

/-- One phrase (eFLINT `Phrase`, plus Charter's scenarios, expectations, and epistemic evidence). Binders of
`Foreach` forms are the `xs` lists. -/
inductive Phrase where
  /-- `a(args) [Note "..."]`, `(Foreach x: a(x))`: trigger an act or event, with optional advisory note (`T04`). -/
  | trigger (xs : List Var) (t : Term) (note : Option String := none)
  /-- `+e` -/
  | create (xs : List Var) (t : Term)
  /-- `-e` -/
  | terminate (xs : List Var) (t : Term)
  /-- `~e` -/
  | obfuscate (xs : List Var) (t : Term)
  /-- `?e` (and `?!e`, `!?e` as `?` of a negation) -/
  | query (t : Term)
  /-- `?-e` (`mustHold = false`) and `?--e` (`mustHold = true`): list instances. -/
  | instQuery (mustHold : Bool) (xs : List Var) (t : Term)
  /-- A block of declarations. -/
  | decls (ds : List Decl)
  /-- `{ p₁. p₂. … }`: phrases evaluated against the same state, effects merged. -/
  | par (ps : List Phrase)
  /-- Charter: `Scenario name [From CLAUSE "span" ...] { phrases }`, a named test run by
  `charter test` from the configuration at this point, leaving it unchanged. -/
  | scenario (name : String) (ps : List Phrase) (spans : List (ClauseId × String) := [])
  /-- Charter: `?lawful e`, `?valid e`, `?violated e`, and their `?!` negations: a claim
  about an act or duty instance. -/
  | expect (what : Expect) (negated : Bool) (t : Term)
  /-- Charter (D7, Law 6): `@ t.` sets the clock; environment input, not an event. -/
  | setTime (t : Term)
  /-- Charter (D7): `tick.` advances the clock by one. -/
  | tick
  /-- Charter (Law 6, plan §2.2.11): `?why e` prints where each instance of `e` came from. -/
  | why (t : Term)
  /-- Charter (D22, G3.2, 011.14): `SubmitEvidence [!]e [By src].` -/
  | submitEvidence (polarity : Bool) (t : Term) (src : String := "")
  /-- Charter (D22, G3.2, 011.14): `RetractEvidence e [By src].` -/
  | retractEvidence (t : Term) (src : String := "")
  deriving Repr, Inhabited

/-- `#include "file"` and `#require "file"`. -/
inductive Directive where
  | include (path : String)
  | require (path : String)
  deriving Repr, Inhabited

/-- A top-level item with the position of its first token. -/
structure Item where
  pos    : Pos
  /-- The source text of the item's first line, for `run` output and claims. -/
  text   : String := ""
  /-- Per-phrase source positions for `Scenario` bodies (`#29`). -/
  subPos : List Pos := []
  val    : Sum Directive Phrase

instance : Inhabited Item := ⟨⟨{}, "", [], .inr (.query (.boolLit true))⟩⟩

mutual
def Phrase.stripPos : Phrase → Phrase
  | .decls ds => .decls (Decl.stripAllPosList ds)
  | .par ps => .par (Phrase.stripPosList ps)
  | .scenario s ps sps => .scenario s (Phrase.stripPosList ps) sps
  | p => p
def Phrase.stripPosList : List Phrase → List Phrase
  | [] => []
  | p :: ps => p.stripPos :: Phrase.stripPosList ps
end

mutual
def Phrase.substAlias (name : String) (val : Term) : Phrase → Phrase
  | .trigger xs t n => .trigger xs (t.substAlias name val) n
  | .create xs t => .create xs (t.substAlias name val)
  | .terminate xs t => .terminate xs (t.substAlias name val)
  | .obfuscate xs t => .obfuscate xs (t.substAlias name val)
  | .query t => .query (t.substAlias name val)
  | .instQuery b xs t => .instQuery b xs (t.substAlias name val)
  | .par ps => .par (Phrase.substAliasList name val ps)
  | .scenario s ps sps => .scenario s (Phrase.substAliasList name val ps) sps
  | .expect w neg t => .expect w neg (t.substAlias name val)
  | .setTime t => .setTime (t.substAlias name val)
  | .why t => .why (t.substAlias name val)
  | .submitEvidence pol t src => .submitEvidence pol (t.substAlias name val) src
  | .retractEvidence t src => .retractEvidence (t.substAlias name val) src
  | p => p
def Phrase.substAliasList (name : String) (val : Term) : List Phrase → List Phrase
  | [] => []
  | p :: ps => p.substAlias name val :: Phrase.substAliasList name val ps
end

end Charter
