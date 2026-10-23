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

/-- One phrase (eFLINT `Phrase`). Binders of `Foreach` forms are the `xs` lists. -/
inductive Phrase where
  /-- `a(args)`, `(Foreach x: a(x))`: trigger an act or event. -/
  | trigger (xs : List Var) (t : Term)
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
