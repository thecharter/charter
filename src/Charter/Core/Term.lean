import Charter.Core.Evidence
import Charter.Core.Scale

/-!
# Charter.Core.Term — Values, domains, and the term language of the eFLINT core

The data of a Charter program's expressions, as records (Law 5). Spelling and
meaning follow eFLINT 4.1 (`.reference/eflint/src/Language/EFLINT/Spec.hs`), per
D2: a `Var` is a type identifier with a decoration (`person1`, `actor'`), an
`Elem` is a string, an integer, or a product of tagged elements, a `Tagged` is an
element with the type it belongs to, and `Term` is the expression language shared
by conditions, derivations, effects, and phrases. The surface parser produces
these terms; `Charter.Resolve` rewrites them into their checked form (explicit
tags, untags, `Present` conversions, bound variable lists); `Charter.Eval` gives
them meaning.
-/

namespace Charter

/-- A type identifier (eFLINT `DomId`): lowercase words with `-` and `_`. -/
abbrev DomId := String

/-- A decorated type identifier: `Var "person" "1"` is written `person1`. -/
structure Var where
  dom : DomId
  dec : String := ""
  deriving Repr, DecidableEq, Inhabited, Hashable

instance : ToString Var := ⟨fun v => v.dom ++ v.dec⟩

/-- Elements of domains. A product carries its components tagged with their types. -/
inductive Elem where
  | str  (s : String)
  | int  (i : Int)
  | prod (args : List (Elem × DomId))
  deriving Repr, Inhabited

/-- A tagged element: an element together with the type it is an instance of. -/
abbrev Tagged := Elem × DomId

namespace Tagged
def elem (te : Tagged) : Elem := te.1
def dom  (te : Tagged) : DomId := te.2
end Tagged

mutual
def Elem.beq : Elem → Elem → Bool
  | .str a, .str b => a == b
  | .int a, .int b => a == b
  | .prod xs, .prod ys => Elem.beqArgs xs ys
  | _, _ => false
def Elem.beqArgs : List (Elem × DomId) → List (Elem × DomId) → Bool
  | [], [] => true
  | (e, d) :: xs, (e', d') :: ys => d == d' && Elem.beq e e' && Elem.beqArgs xs ys
  | _, _ => false
end

instance : BEq Elem := ⟨Elem.beq⟩

-- Lexicographic order on elements, used to keep states canonical.
mutual
def Elem.cmp : Elem → Elem → Ordering
  | .str a, .str b => compare a b
  | .str _, _ => .lt
  | .int _, .str _ => .gt
  | .int a, .int b => compare a b
  | .int _, .prod _ => .lt
  | .prod xs, .prod ys => Elem.cmpArgs xs ys
  | .prod _, _ => .gt
def Elem.cmpArgs : List (Elem × DomId) → List (Elem × DomId) → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | (e, d) :: xs, (e', d') :: ys =>
    match compare d d' with
    | .eq => match Elem.cmp e e' with
      | .eq => Elem.cmpArgs xs ys
      | o => o
    | o => o
end

def Tagged.cmp (a b : Tagged) : Ordering :=
  match compare a.2 b.2 with
  | .eq => Elem.cmp a.1 b.1
  | o => o

instance : BEq Tagged := ⟨fun a b => a.2 == b.2 && Elem.beq a.1 b.1⟩

/-- Haskell `show` of a string: double quotes, with `"` and `\` escaped. Folds over the
character list, not with `String.foldl`, whose termination proof uses `propext`: a decided
program must depend on no axioms (Law 10, 013.4). -/
def showString (s : String) : String :=
  "\"" ++ (s.toList.foldl (fun acc c => acc ++ (match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | c => c.toString)) "") ++ "\""

-- eFLINT's `ppTagged`: `actor("Alice")`, `x(3)`, `comp(a("A1"),b("B2"))`.
mutual
def Elem.pp (e : Elem) (d : DomId) : String :=
  match e with
  | .str s => d ++ "(" ++ showString s ++ ")"
  | .int i => d ++ "(" ++ toString i ++ ")"
  | .prod args => d ++ "(" ++ Elem.ppArgs args ++ ")"
def Elem.ppArgs : List (Elem × DomId) → String
  | [] => ""
  | [(e, d)] => Elem.pp e d
  | (e, d) :: rest => Elem.pp e d ++ "," ++ Elem.ppArgs rest
end

def Tagged.pp (te : Tagged) : String := Elem.pp te.1 te.2

instance : ToString Tagged := ⟨Tagged.pp⟩

/-- Domains of types (eFLINT `Domain`). `time` is kept for D7's Phase 2 work. -/
inductive Domain where
  | anyString
  | anyInt
  | strings (ss : List String)
  | ints (is : List Int)
  | products (xs : List Var)
  | time
  /-- Charter (D7): differences of instants, over `Int`. -/
  | duration
  /-- Charter (D24, G3.4): `Money(CUR, SCALE)` minor units over exact `Int`. -/
  | money (currency : String) (scale : Nat)
  /-- Charter (D24, G3.4): `Quantity(UNIT)` units over exact `Int`. -/
  | quantity (unit : String)
  deriving Repr, Inhabited, BEq

def Domain.isDimensionalInt : Domain → Bool
  | .time | .duration | .money _ _ | .quantity _ => true
  | _ => false

mutual
/-- The term language (eFLINT `Term`). `tag`/`untag` are inserted by resolution. -/
inductive Term where
  | not (t : Term)
  | and (a b : Term)
  | or (a b : Term)
  | boolLit (b : Bool)
  | leq (a b : Term)
  | geq (a b : Term)
  | ge (a b : Term)
  | le (a b : Term)
  | sub (a b : Term)
  | add (a b : Term)
  | mult (a b : Term)
  | mod (a b : Term)
  | div (a b : Term)
  | intLit (i : Int)
  | stringLit (s : String)
  | eq (a b : Term)
  | neq (a b : Term)
  | exists_ (xs : List Var) (t : Term)
  | forall_ (xs : List Var) (t : Term)
  | count (xs : List Var) (t : Term)
  | sum (xs : List Var) (t : Term)
  | max (xs : List Var) (t : Term)
  | min (xs : List Var) (t : Term)
  | when (t c : Term)
  | present (t : Term)
  | violated (t : Term)
  | enabled (t : Term)
  | project (t : Term) (x : Var)
  | tag (t : Term) (d : DomId)
  | untag (t : Term)
  | ref (x : Var)
  | app (d : DomId) (args : Args)
  | currentTime
  /-- Charter (D7): `Held(e) For d`: `e` holds and has held for at least the duration `d`. -/
  | heldFor (t : Term) (d : Term)
  /-- Charter (D22, G3.2): `Established(e)` / `Refuted(e)` / `Unresolved(e)` / `Conflicted(e)`. -/
  | evStatus (want : EvidenceStatus) (t : Term)
  /-- Charter (D23, G3.3): `Conflict(e)` tests normative conflict among unranked defeasible rules. -/
  | hasConflict (t : Term)
  /-- Charter (D24, G3.4): `MulDivRound(x, num, den, mode)` exact scaled integer division. -/
  | mulDivRound (x : Term) (num : Term) (den : Term) (mode : RoundingMode)
  /-- Charter (D36, `#46`): `f(key)` 1-argument `Function` value lookup. -/
  | fnApp (d : DomId) (key : Term)
  deriving Repr, Inhabited
/-- Arguments of an application: positional terms or named `x = e` modifiers. -/
inductive Args where
  | pos (ts : List Term)
  | named (ms : List (Var × Term))
  deriving Repr, Inhabited
end

/-- Static types assigned by resolution (eFLINT `Type`). -/
inductive Ty where
  | strings
  | ints
  | bool
  | tagged (d : DomId)
  /-- Charter (D7): an instant. -/
  | time
  /-- Charter (D7): a difference of instants. -/
  | duration
  /-- Charter (D24, G3.4): `Money(CUR, SCALE)` minor units. -/
  | money (currency : String) (scale : Nat)
  /-- Charter (D24, G3.4): `Quantity(UNIT)` units. -/
  | quantity (unit : String)
  deriving Repr, DecidableEq, Inhabited

instance : ToString Ty := ⟨fun
  | .strings => "a string" | .ints => "an integer" | .bool => "a boolean" | .tagged d => s!"an instance of {d}"
  | .time => "a time" | .duration => "a duration"
  | .money c s => s!"Money({c}, {s})" | .quantity u => s!"Quantity({u})"⟩

/-- Run-time values (eFLINT `Value`). -/
inductive Value where
  | bool (b : Bool)
  | str (s : String)
  | int (i : Int)
  | tagged (te : Tagged)
  deriving Repr, Inhabited

def Value.beq : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .int a, .int b => a == b
  | .tagged a, .tagged b => a == b
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

/-- Positional arguments `xs ↦ args`, or the named modifiers as given (eFLINT
`make_substitutions_of`). -/
def Args.substitutions (xs : List Var) : Args → List (Var × Term)
  | .named ms => ms
  | .pos ts => xs.zip ts

-- Pretty-printing of terms for diagnostics and `run` output.
def Term.ppVars (xs : List Var) : String := ", ".intercalate (xs.map toString)

mutual
def Term.pp : Term → String
  | .not t => "!" ++ t.pp
  | .and a b => "(" ++ a.pp ++ " && " ++ b.pp ++ ")"
  | .or a b => "(" ++ a.pp ++ " || " ++ b.pp ++ ")"
  | .boolLit b => if b then "True" else "False"
  | .leq a b => "(" ++ a.pp ++ " <= " ++ b.pp ++ ")"
  | .geq a b => "(" ++ a.pp ++ " >= " ++ b.pp ++ ")"
  | .ge a b => "(" ++ a.pp ++ " > " ++ b.pp ++ ")"
  | .le a b => "(" ++ a.pp ++ " < " ++ b.pp ++ ")"
  | .sub a b => "(" ++ a.pp ++ " - " ++ b.pp ++ ")"
  | .add a b => "(" ++ a.pp ++ " + " ++ b.pp ++ ")"
  | .mult a b => "(" ++ a.pp ++ " * " ++ b.pp ++ ")"
  | .mod a b => "(" ++ a.pp ++ " % " ++ b.pp ++ ")"
  | .div a b => "(" ++ a.pp ++ " / " ++ b.pp ++ ")"
  | .intLit i => toString i
  | .stringLit s => showString s
  | .eq a b => "(" ++ a.pp ++ " == " ++ b.pp ++ ")"
  | .neq a b => "(" ++ a.pp ++ " != " ++ b.pp ++ ")"
  | .exists_ xs t => "(Exists " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .forall_ xs t => "(Forall " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .count xs t => "Count(Foreach " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .sum xs t => "Sum(Foreach " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .max xs t => "Max(Foreach " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .min xs t => "Min(Foreach " ++ Term.ppVars xs ++ " : " ++ t.pp ++ ")"
  | .when t c => "(" ++ t.pp ++ " When " ++ c.pp ++ ")"
  | .present t => "Holds(" ++ t.pp ++ ")"
  | .violated t => "Violated(" ++ t.pp ++ ")"
  | .enabled t => "Enabled(" ++ t.pp ++ ")"
  | .project t x => t.pp ++ "." ++ toString x
  | .tag t d => t.pp ++ ":" ++ d
  | .untag t => t.pp
  | .ref x => toString x
  | .app d args => d ++ "(" ++ args.pp ++ ")"
  | .currentTime => "Current Time"
  | .heldFor t d => "Held(" ++ t.pp ++ ") For " ++ d.pp
  | .evStatus want t => want.kwName ++ "(" ++ t.pp ++ ")"
  | .hasConflict t => "Conflict(" ++ t.pp ++ ")"
  | .mulDivRound x n d m => "MulDivRound(" ++ x.pp ++ ", " ++ n.pp ++ ", " ++ d.pp ++ ", " ++ m.kwName ++ ")"
  | .fnApp d k => d ++ "(" ++ k.pp ++ ")"
def Args.pp : Args → String
  | .pos ts => Term.ppList ts
  | .named ms => Term.ppMods ms
def Term.ppList : List Term → String
  | [] => ""
  | [t] => t.pp
  | t :: ts => t.pp ++ ", " ++ Term.ppList ts
def Term.ppMods : List (Var × Term) → String
  | [] => ""
  | [(x, t)] => toString x ++ " = " ++ t.pp
  | (x, t) :: ms => toString x ++ " = " ++ t.pp ++ ", " ++ Term.ppMods ms
end
instance : ToString Term := ⟨Term.pp⟩

/-- Rename the type names a term mentions (module instantiation, D8). -/
def Var.mapDom (f : DomId → DomId) (x : Var) : Var := { x with dom := f x.dom }

mutual
def Term.mapDom (f : DomId → DomId) : Term → Term
  | .not t => .not (t.mapDom f)
  | .and a b => .and (a.mapDom f) (b.mapDom f)
  | .or a b => .or (a.mapDom f) (b.mapDom f)
  | .boolLit b => .boolLit b
  | .leq a b => .leq (a.mapDom f) (b.mapDom f)
  | .geq a b => .geq (a.mapDom f) (b.mapDom f)
  | .ge a b => .ge (a.mapDom f) (b.mapDom f)
  | .le a b => .le (a.mapDom f) (b.mapDom f)
  | .sub a b => .sub (a.mapDom f) (b.mapDom f)
  | .add a b => .add (a.mapDom f) (b.mapDom f)
  | .mult a b => .mult (a.mapDom f) (b.mapDom f)
  | .mod a b => .mod (a.mapDom f) (b.mapDom f)
  | .div a b => .div (a.mapDom f) (b.mapDom f)
  | .intLit i => .intLit i
  | .stringLit s => .stringLit s
  | .eq a b => .eq (a.mapDom f) (b.mapDom f)
  | .neq a b => .neq (a.mapDom f) (b.mapDom f)
  | .exists_ xs t => .exists_ (xs.map (Var.mapDom f)) (t.mapDom f)
  | .forall_ xs t => .forall_ (xs.map (Var.mapDom f)) (t.mapDom f)
  | .count xs t => .count (xs.map (Var.mapDom f)) (t.mapDom f)
  | .sum xs t => .sum (xs.map (Var.mapDom f)) (t.mapDom f)
  | .max xs t => .max (xs.map (Var.mapDom f)) (t.mapDom f)
  | .min xs t => .min (xs.map (Var.mapDom f)) (t.mapDom f)
  | .when t c => .when (t.mapDom f) (c.mapDom f)
  | .present t => .present (t.mapDom f)
  | .violated t => .violated (t.mapDom f)
  | .enabled t => .enabled (t.mapDom f)
  | .project t x => .project (t.mapDom f) (x.mapDom f)
  | .tag t d => .tag (t.mapDom f) (f d)
  | .untag t => .untag (t.mapDom f)
  | .ref x => .ref (x.mapDom f)
  | .app d args => .app (f d) (args.mapDom f)
  | .currentTime => .currentTime
  | .heldFor t d => .heldFor (t.mapDom f) (d.mapDom f)
  | .evStatus want t => .evStatus want (t.mapDom f)
  | .hasConflict t => .hasConflict (t.mapDom f)
  | .mulDivRound x n d m => .mulDivRound (x.mapDom f) (n.mapDom f) (d.mapDom f) m
  | .fnApp d k => .fnApp (f d) (k.mapDom f)
def Args.mapDom (f : DomId → DomId) : Args → Args
  | .pos ts => .pos (Term.mapDomList f ts)
  | .named ms => .named (Term.mapDomMods f ms)
def Term.mapDomList (f : DomId → DomId) : List Term → List Term
  | [] => []
  | t :: ts => t.mapDom f :: Term.mapDomList f ts
def Term.mapDomMods (f : DomId → DomId) : List (Var × Term) → List (Var × Term)
  | [] => []
  | (x, t) :: ms => (x.mapDom f, t.mapDom f) :: Term.mapDomMods f ms
end

def Domain.mapDom (f : DomId → DomId) : Domain → Domain
  | .products xs => .products (xs.map (Var.mapDom f))
  | d => d

mutual
/-- Substitute free variable references according to `sub` (`D35`, `#57`). Structurally
recursive on `Term` so kernel reduction in `charter prove` introduces zero axioms. -/
def Term.substVars (sub : List (Var × Var)) : Term → Term
  | .not t => .not (t.substVars sub)
  | .and a b => .and (a.substVars sub) (b.substVars sub)
  | .or a b => .or (a.substVars sub) (b.substVars sub)
  | .boolLit b => .boolLit b
  | .leq a b => .leq (a.substVars sub) (b.substVars sub)
  | .geq a b => .geq (a.substVars sub) (b.substVars sub)
  | .ge a b => .ge (a.substVars sub) (b.substVars sub)
  | .le a b => .le (a.substVars sub) (b.substVars sub)
  | .sub a b => .sub (a.substVars sub) (b.substVars sub)
  | .add a b => .add (a.substVars sub) (b.substVars sub)
  | .mult a b => .mult (a.substVars sub) (b.substVars sub)
  | .mod a b => .mod (a.substVars sub) (b.substVars sub)
  | .div a b => .div (a.substVars sub) (b.substVars sub)
  | .intLit n => .intLit n
  | .stringLit s => .stringLit s
  | .eq a b => .eq (a.substVars sub) (b.substVars sub)
  | .neq a b => .neq (a.substVars sub) (b.substVars sub)
  | .exists_ xs t => .exists_ xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .forall_ xs t => .forall_ xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .count xs t => .count xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .sum xs t => .sum xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .max xs t => .max xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .min xs t => .min xs (t.substVars (sub.filter fun p => !xs.contains p.1))
  | .when a b => .when (a.substVars sub) (b.substVars sub)
  | .present t => .present (t.substVars sub)
  | .violated t => .violated (t.substVars sub)
  | .enabled t => .enabled (t.substVars sub)
  | .project t x => .project (t.substVars sub) x
  | .tag t d => .tag (t.substVars sub) d
  | .untag t => .untag (t.substVars sub)
  | .ref x => match sub.find? (·.1 == x) with | some (_, y) => .ref y | none => .ref x
  | .app d args => .app d (args.substVars sub)
  | .currentTime => .currentTime
  | .heldFor t d => .heldFor (t.substVars sub) (d.substVars sub)
  | .evStatus want t => .evStatus want (t.substVars sub)
  | .hasConflict t => .hasConflict (t.substVars sub)
  | .mulDivRound x n d m => .mulDivRound (x.substVars sub) (n.substVars sub) (d.substVars sub) m
  | .fnApp d k => .fnApp d (k.substVars sub)
def Args.substVars (sub : List (Var × Var)) : Args → Args
  | .pos ts => .pos (Term.substVarsList sub ts)
  | .named ms => .named (Term.substVarsMods sub ms)
def Term.substVarsList (sub : List (Var × Var)) : List Term → List Term
  | [] => []
  | t :: ts => t.substVars sub :: Term.substVarsList sub ts
def Term.substVarsMods (sub : List (Var × Var)) : List (Var × Term) → List (Var × Term)
  | [] => []
  | (x, t) :: ms => (x, t.substVars sub) :: Term.substVarsMods sub ms
end

mutual
/-- Substitute a scenario `Let` alias (`name`) with `val` (`D36`, `#41`). -/
def Term.substAlias : Term → String → Term → Term
  | .not t, name, val => .not (t.substAlias name val)
  | .and a b, name, val => .and (a.substAlias name val) (b.substAlias name val)
  | .or a b, name, val => .or (a.substAlias name val) (b.substAlias name val)
  | .boolLit b, _, _ => .boolLit b
  | .leq a b, name, val => .leq (a.substAlias name val) (b.substAlias name val)
  | .geq a b, name, val => .geq (a.substAlias name val) (b.substAlias name val)
  | .ge a b, name, val => .ge (a.substAlias name val) (b.substAlias name val)
  | .le a b, name, val => .le (a.substAlias name val) (b.substAlias name val)
  | .sub a b, name, val => .sub (a.substAlias name val) (b.substAlias name val)
  | .add a b, name, val => .add (a.substAlias name val) (b.substAlias name val)
  | .mult a b, name, val => .mult (a.substAlias name val) (b.substAlias name val)
  | .mod a b, name, val => .mod (a.substAlias name val) (b.substAlias name val)
  | .div a b, name, val => .div (a.substAlias name val) (b.substAlias name val)
  | .intLit n, _, _ => .intLit n
  | .stringLit s, name, val => if s == name then val else .stringLit s
  | .eq a b, name, val => .eq (a.substAlias name val) (b.substAlias name val)
  | .neq a b, name, val => .neq (a.substAlias name val) (b.substAlias name val)
  | .exists_ xs t, name, val => if xs.any (fun x => toString x == name) then .exists_ xs t else .exists_ xs (t.substAlias name val)
  | .forall_ xs t, name, val => if xs.any (fun x => toString x == name) then .forall_ xs t else .forall_ xs (t.substAlias name val)
  | .count xs t, name, val => if xs.any (fun x => toString x == name) then .count xs t else .count xs (t.substAlias name val)
  | .sum xs t, name, val => if xs.any (fun x => toString x == name) then .sum xs t else .sum xs (t.substAlias name val)
  | .max xs t, name, val => if xs.any (fun x => toString x == name) then .max xs t else .max xs (t.substAlias name val)
  | .min xs t, name, val => if xs.any (fun x => toString x == name) then .min xs t else .min xs (t.substAlias name val)
  | .when a b, name, val => .when (a.substAlias name val) (b.substAlias name val)
  | .present t, name, val => .present (t.substAlias name val)
  | .violated t, name, val => .violated (t.substAlias name val)
  | .enabled t, name, val => .enabled (t.substAlias name val)
  | .project t x, name, val => .project (t.substAlias name val) x
  | .tag t d, name, val => .tag (t.substAlias name val) d
  | .untag t, name, val => .untag (t.substAlias name val)
  | .ref x, name, val => if x.dec.isEmpty && x.dom == name then val else .ref x
  | .app d args, name, val => .app d (args.substAlias name val)
  | .currentTime, _, _ => .currentTime
  | .heldFor t d, name, val => .heldFor (t.substAlias name val) (d.substAlias name val)
  | .evStatus want t, name, val => .evStatus want (t.substAlias name val)
  | .hasConflict t, name, val => .hasConflict (t.substAlias name val)
  | .mulDivRound x n d m, name, val => .mulDivRound (x.substAlias name val) (n.substAlias name val) (d.substAlias name val) m
  | .fnApp d k, name, val => .fnApp d (k.substAlias name val)
termination_by structural x => x

def Args.substAlias : Args → String → Term → Args
  | .pos ts, name, val => .pos (Term.substAliasList ts name val)
  | .named ms, name, val => .named (Term.substAliasMods ms name val)
termination_by structural x => x

def Term.substAliasList : List Term → String → Term → List Term
  | [], _, _ => []
  | t :: ts, name, val => t.substAlias name val :: Term.substAliasList ts name val
termination_by structural x => x

def Term.substAliasMods : List (Var × Term) → String → Term → List (Var × Term)
  | [], _, _ => []
  | (x, t) :: ms, name, val => (x, t.substAlias name val) :: Term.substAliasMods ms name val
termination_by structural x => x
end

end Charter
