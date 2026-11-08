import Charter.Core.State
import Charter.Core.Derivation

/-!
# Charter.Core.Meaning — Evaluator-Independent Relational Semantics (`D41`, `#65`, `Law 9`)

Defines the declarative relational meaning of Charter expressions (`DeclEval`) and
compiled phrase steps (`DeclCPhraseMeaning`) directly over `Spec` and `State` —
without fuel bounds, `DomMap` caches, or any dependency on `Charter.Eval.*` (`M`,
`M.eval`, `Interp.semPhrase`, or `runPhrase`).

`Charter.Eval.Properties` proves `M.eval`, `M.evalEffect`, `Interp.evalClockStep`,
and `Interp.semPhrase` sound and complete with respect to these relations (`Law 9`).
-/

namespace Charter

/-- Syntactic evaluation depth of a `Term` (sufficient fuel bound for `M.eval`). -/
def Term.evalDepth : Term → Nat
  | .currentTime | .intLit _ | .dimLit _ _ | .stringLit _ | .boolLit _ | .ref _ => 1
  | .tag a _ | .untag a | .not a | .present a | .violated a | .enabled a
  | .evStatus _ a | .hasConflict a | .doneAt a | .stampOf a | .overdueOf a
  | .calOp1 _ a | .project a _ => a.evalDepth + 1
  | .and a b | .or a b | .leq a b | .le a b | .geq a b | .ge a b
  | .add a b | .sub a b | .mult a b | .div a b | .mod a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    Nat.max a.evalDepth b.evalDepth + 1
  | .ite c t e | .mulDivRound c t e _ =>
    Nat.max c.evalDepth (Nat.max t.evalDepth e.evalDepth) + 1
  | .exists_ _ a | .forall_ _ a | .count _ a | .sum _ a | .max _ a | .min _ a =>
    a.evalDepth + 2
  | .fnApp _ a => a.evalDepth + 2
  | .app _ _ => 2
termination_by structural x => x

/-- Predicate identifying deterministic core terms covered by `DeclEval`. -/
def IsDeclCoreTerm : Term → Bool
  | .currentTime | .intLit _ | .dimLit _ _ | .stringLit _ | .boolLit _ | .ref _ => true
  | .tag a _ | .untag a | .not a => IsDeclCoreTerm a
  | .and a b | .or a b | .leq a b | .le a b | .geq a b | .ge a b
  | .add a b | .sub a b | .mult a b | .div a b | .mod a b
  | .eq a b | .neq a b => IsDeclCoreTerm a && IsDeclCoreTerm b
  | .ite c t e => IsDeclCoreTerm c && IsDeclCoreTerm t && IsDeclCoreTerm e
  | .mulDivRound x n d _ => IsDeclCoreTerm x && IsDeclCoreTerm n && IsDeclCoreTerm d
  | _ => false
termination_by structural x => x

/-- Purely relational, fuel-free, monad-free big-step meaning of a `Term` in `(spec, s, subs)` (`Law 9`, `#65`). -/
inductive DeclEval (spec : Spec) (s : State) (subs : List (Var × Tagged)) : Term → Value → Prop where
  | currentTime :
      DeclEval spec s subs .currentTime (.int s.time)
  | intLit (i : Int) :
      DeclEval spec s subs (.intLit i) (.int i)
  | dimLit (dom : Domain) (n : Int) :
      DeclEval spec s subs (.dimLit dom n) (.int n)
  | stringLit (str : String) :
      DeclEval spec s subs (.stringLit str) (.str str)
  | boolLit (b : Bool) :
      DeclEval spec s subs (.boolLit b) (.bool b)
  | ref (x : Var) (x' : Var) (el : Elem) (d0 : DomId) :
      subs.find? (fun p => p.1 == x) = some (x', (el, d0)) →
      DeclEval spec s subs (.ref x) (.tagged (el, spec.removeDecoration x))
  | tagInt (t : Term) (i : Int) (d : DomId) :
      DeclEval spec s subs t (.int i) →
      DeclEval spec s subs (.tag t d) (.tagged (.int i, d))
  | tagStr (t : Term) (str : String) (d : DomId) :
      DeclEval spec s subs t (.str str) →
      DeclEval spec s subs (.tag t d) (.tagged (.str str, d))
  | tagTagged (t : Term) (el : Elem) (d0 d : DomId) :
      DeclEval spec s subs t (.tagged (el, d0)) →
      DeclEval spec s subs (.tag t d) (.tagged (el, d))
  | untagInt (t : Term) (i : Int) (d0 : DomId) :
      DeclEval spec s subs t (.tagged (.int i, d0)) →
      DeclEval spec s subs (.untag t) (.int i)
  | untagStr (t : Term) (str : String) (d0 : DomId) :
      DeclEval spec s subs t (.tagged (.str str, d0)) →
      DeclEval spec s subs (.untag t) (.str str)
  | not (t : Term) (b : Bool) :
      DeclEval spec s subs t (.bool b) →
      DeclEval spec s subs (.not t) (.bool (!b))
  | andFalse (a b : Term) :
      DeclEval spec s subs a (.bool false) →
      DeclEval spec s subs (.and a b) (.bool false)
  | andTrue (a b : Term) (vb : Bool) :
      DeclEval spec s subs a (.bool true) →
      DeclEval spec s subs b (.bool vb) →
      DeclEval spec s subs (.and a b) (.bool vb)
  | orTrue (a b : Term) :
      DeclEval spec s subs a (.bool true) →
      DeclEval spec s subs (.or a b) (.bool true)
  | orFalse (a b : Term) (vb : Bool) :
      DeclEval spec s subs a (.bool false) →
      DeclEval spec s subs b (.bool vb) →
      DeclEval spec s subs (.or a b) (.bool vb)
  | iteTrue (c t e : Term) (v : Value) :
      DeclEval spec s subs c (.bool true) →
      DeclEval spec s subs t v →
      DeclEval spec s subs (.ite c t e) v
  | iteFalse (c t e : Term) (v : Value) :
      DeclEval spec s subs c (.bool false) →
      DeclEval spec s subs e v →
      DeclEval spec s subs (.ite c t e) v
  | leq (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.leq a b) (.bool (decide (x ≤ y)))
  | le (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.le a b) (.bool (decide (x < y)))
  | geq (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.geq a b) (.bool (decide (x ≥ y)))
  | ge (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.ge a b) (.bool (decide (x > y)))
  | add (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.add a b) (.int (x + y))
  | sub (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.sub a b) (.int (x - y))
  | mult (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.mult a b) (.int (x * y))
  | div (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.div a b) (.int (Int.fdiv x y))
  | mod (a b : Term) (x y : Int) :
      DeclEval spec s subs a (.int x) →
      DeclEval spec s subs b (.int y) →
      DeclEval spec s subs (.mod a b) (.int (Int.fmod x y))
  | eq (a b : Term) (x y : Value) :
      DeclEval spec s subs a x →
      DeclEval spec s subs b y →
      DeclEval spec s subs (.eq a b) (.bool (x == y))
  | neq (a b : Term) (x y : Value) :
      DeclEval spec s subs a x →
      DeclEval spec s subs b y →
      DeclEval spec s subs (.neq a b) (.bool (!(x == y)))
  | mulDivRound (x num den : Term) (mode : RoundingMode) (vx vn vd res : Int) :
      DeclEval spec s subs x (.int vx) →
      DeclEval spec s subs num (.int vn) →
      DeclEval spec s subs den (.int vd) →
      Charter.mulDivRound vx vn vd mode = .ok res →
      DeclEval spec s subs (.mulDivRound x num den mode) (.int res)

/-- Evaluator-independent relational specification of a compiled phrase step (`#65`, `Law 9`):
relates `(spec, s, cp)` to `(newTime?, store, queryVerdicts)` without referencing `M.eval`,
`Interp.semPhrase`, or `Interp.evalClockStep`. -/
inductive DeclCPhraseMeaning (spec : Spec) (s : State) :
    CPhrase → Option Int → Store → List Bool → Prop where
  | onlyDecls (init : Store) :
      DeclCPhraseMeaning spec s (.onlyDecls init) none init []
  | tick :
      DeclCPhraseMeaning spec s .tick (some (s.time + 1)) [] []
  | setTime (t : Term) (t' : Int) :
      DeclEval spec s [] t (.int t') →
      s.time ≤ t' →
      DeclCPhraseMeaning spec s (.setTime t) (some t') [] []
  | query (t : Term) (b : Bool) :
      DeclEval spec s [] t (.bool b) →
      DeclCPhraseMeaning spec s (.query t) none [] [b]
  | createGround (t : Term) (te : Tagged) :
      DeclEval spec s [] t (.tagged te) →
      DeclCPhraseMeaning spec s (.create [] t) none [(te, .holdsTrue none none)] []
  | terminateGround (t : Term) (te : Tagged) :
      DeclEval spec s [] t (.tagged te) →
      DeclCPhraseMeaning spec s (.terminate [] t) none [(te, .holdsFalse none)] []
  | obfuscateGround (t : Term) (te : Tagged) :
      DeclEval spec s [] t (.tagged te) →
      DeclCPhraseMeaning spec s (.obfuscate [] t) none [(te, .unknown)] []

end Charter
