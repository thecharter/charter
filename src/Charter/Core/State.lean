import Charter.Core.Spec

/-!
# Charter.Core.State — The knowledge base and what a transition reports

eFLINT's `State.hs`, per D2: a state assigns truth values to instances (`Info`:
the value and whether saturation derived it) and carries the clock. A `Store` is
a batch of assignments an act or phrase makes, merged with create-beats-terminate
precedence. `TransInfo` is what one trigger did, with the transitions it synced.
Errors of evaluation are records too (`RuntimeError`), rendered by the CLI as
CHR1xx diagnostics.
-/

namespace Charter

structure Info where
  value   : Bool
  fromSat : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The knowledge base: an association list from instances to their info, and the
clock. Lookups compare instances structurally. -/
structure State where
  contents : List (Tagged × Info) := []
  time     : Int := 0
  deriving Inhabited

namespace State

def lookup (s : State) (te : Tagged) : Option Info :=
  (s.contents.find? (·.1 == te)).map (·.2)

def insert (s : State) (te : Tagged) (i : Info) : State :=
  { s with contents := (te, i) :: s.contents.filter (fun p => !(p.1 == te)) }

def erase (s : State) (te : Tagged) : State :=
  { s with contents := s.contents.filter (fun p => !(p.1 == te)) }

/-- Instances assumed to hold (value true). -/
def holdsList (s : State) : List Tagged :=
  s.contents.filterMap fun (te, i) => if i.value then some te else none

def notHoldsList (s : State) : List Tagged :=
  s.contents.filterMap fun (te, i) => if i.value then none else some te

/-- `(trues, falses)` of a type (eFLINT `assigned_instances`). -/
def assignedInstances (s : State) (d : DomId) : List Tagged × List Tagged :=
  (s.contents.filterMap fun (te, i) => if te.2 == d && i.value then some te else none,
   s.contents.filterMap fun (te, i) => if te.2 == d && !i.value then some te else none)

def holds (s : State) (te : Tagged) : Bool :=
  match s.lookup te with
  | some i => i.value
  | none => false

/-- Remove every derived fact (eFLINT `rebase`), before re-deriving. -/
def rebase (s : State) : State :=
  { s with contents := s.contents.filter (fun p => !p.2.fromSat) }

/-- Record a derived fact unless the instance already has an assignment
(eFLINT `derive`: assignment beats derivation). Returns whether anything changed. -/
def derive (s : State) (te : Tagged) : State × Bool :=
  match s.lookup te with
  | some _ => (s, false)
  | none => ({ s with contents := (te, ⟨true, true⟩) :: s.contents }, true)

def deriveAll : State → List Tagged → State × Bool
  | s, [] => (s, false)
  | s, te :: tes =>
    match s.derive te with
    | (s', ch) =>
      match deriveAll s' tes with
      | (s'', ch') => (s'', ch || ch')

end State

/-- The truth value an effect assigns. -/
inductive Assignment
  | holdsTrue
  | holdsFalse
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- A batch of assignments. -/
abbrev Store := List (Tagged × Assignment)

namespace Store

def lookup (st : Store) (te : Tagged) : Option Assignment := (st.find? (·.1 == te)).map (·.2)

/-- Biased union: `holdsTrue > holdsFalse > unknown` (eFLINT `store_union`). -/
def union (a b : Store) : Store :=
  let merged := a.map fun (te, x) => match b.lookup te with
    | some y => (te, combine x y)
    | none => (te, x)
  let onlyB := b.filter fun (te, _) => (a.lookup te).isNone
  merged ++ onlyB
where
  combine : Assignment → Assignment → Assignment
    | .holdsTrue, _ => .holdsTrue
    | _, .holdsTrue => .holdsTrue
    | .holdsFalse, _ => .holdsFalse
    | _, .holdsFalse => .holdsFalse
    | .unknown, .unknown => .unknown

def unions (sts : List Store) : Store := sts.foldr union []

end Store

/-- Apply a store to a state (eFLINT `make_assignments`), honouring `Var` and
`Function` restrictions: a new true instance of a `Var` type falsifies every other
instance of the type; of a `Function` type, every instance with the same first
component. -/
def State.makeAssignments (spec : Spec) (st : Store) (s : State) : State :=
  st.foldr (fun (te, a) s => match a with
    | .holdsTrue =>
      match spec.restrictionOf te.2 with
      | some .var =>
        let s := { s with contents := s.contents.map fun (q : Tagged × Info) =>
          if q.1.2 == te.2 then (q.1, ⟨false, false⟩) else q }
        s.insert te ⟨true, false⟩
      | some .function =>
        match te.1 with
        | .prod [f, _] =>
          let s := { s with contents := s.contents.map fun (q : Tagged × Info) =>
            match q.1.1 with
            | .prod [f', _] => if q.1.2 == te.2 && Elem.beq f.1 f'.1 && f.2 == f'.2 then (q.1, ⟨false, false⟩) else q
            | _ => q }
          s.insert te ⟨true, false⟩
        | _ => s
      | none => s.insert te ⟨true, false⟩
    | .holdsFalse => s.insert te ⟨false, false⟩
    | .unknown => s.erase te) s

/-- What one trigger did (eFLINT `TransInfo`). -/
inductive TransInfo where
  | mk (tagged : Tagged) (assignments : Store) (forced : Bool) (disabled : Bool)
       (actor : Option Tagged) (syncs : List TransInfo)
  deriving Inhabited

namespace TransInfo
def tagged : TransInfo → Tagged | .mk t _ _ _ _ _ => t
def assignments : TransInfo → Store | .mk _ a _ _ _ _ => a
def forced : TransInfo → Bool | .mk _ _ f _ _ _ => f
def disabled : TransInfo → Bool | .mk _ _ _ d _ _ => d
def actor : TransInfo → Option Tagged | .mk _ _ _ _ a _ => a
def syncs : TransInfo → List TransInfo | .mk _ _ _ _ _ s => s
def isAction (t : TransInfo) : Bool := t.actor.isSome
end TransInfo

inductive Violation where
  | duty (te : Tagged)
  | trigger (info : TransInfo)
  | invariant (d : DomId)
  deriving Inhabited

/-- Missing input for an open type (eFLINT `MissingInput`). -/
inductive MissingInput where
  | assignments (unknowns : List Tagged)
  | instances (d : DomId)
  deriving Inhabited

inductive RuntimeError where
  | missingInput (m : MissingInput)
  | enumerateInfiniteDomain (d : DomId)
  | missingSubstitution (x : Var)
  | primitiveApplication (d : DomId)
  | undeclaredType (d : DomId)
  | fuelExhausted (what : String)
  deriving Inhabited

def RuntimeError.code : RuntimeError → String
  | .missingInput _ => "CHR100"
  | .enumerateInfiniteDomain _ => "CHR101"
  | .missingSubstitution _ => "CHR102"
  | .primitiveApplication _ => "CHR105"
  | .undeclaredType _ => "CHR105"
  | .fuelExhausted _ => "CHR104"

def RuntimeError.message : RuntimeError → String
  | .missingInput (.assignments tes) => s!"missing input: no truth value for {", ".intercalate (tes.map Tagged.pp)}"
  | .missingInput (.instances d) => s!"missing input: no instances of the open type {d} are known"
  | .enumerateInfiniteDomain d => s!"cannot enumerate every instance of {d}: its domain is infinite"
  | .missingSubstitution x => s!"variable {x} is not bound"
  | .primitiveApplication d => s!"{d} is a primitive type and cannot be applied to arguments"
  | .undeclaredType d => s!"undeclared type {d}"
  | .fuelExhausted what => s!"evaluation did not finish within its bound while {what}"

def RuntimeError.isMissingInput : RuntimeError → Bool
  | .missingInput _ => true
  | _ => false

end Charter
