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

/-- Which of the answers an expectation phrase asks about (Charter, plan §2.2.6, D22). -/
inductive Expect
  | lawful
  | valid
  | violated
  | undetermined
  deriving Repr, DecidableEq, Inhabited

def Expect.name : Expect → String
  | .lawful => "lawful" | .valid => "valid" | .violated => "violated" | .undetermined => "undetermined"

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
  pos  : Pos
  /-- The source text of the item's first line, for `run` output and claims. -/
  text : String := ""
  val  : Sum Directive Phrase

instance : Inhabited Item := ⟨⟨{}, "", .inr (.query (.boolLit true))⟩⟩

end Charter
