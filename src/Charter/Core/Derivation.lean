import Charter.Core.State

/-!
# Charter.Core.Derivation — Topological Stratification (`D6`) & State Fixpoint Ordering (`G1.3`)

Computes polarity-tracked dependency edges across derived types, partitions derived types
into topological strata (`Stratify.strata`), and defines the state-extension preorders
(`PreservesAssigned`, `HoldsSubstate`) used by the least-fixpoint proofs in
`Charter.Eval.Properties`.
-/

namespace Charter

namespace Stratify

inductive Pol | pos | neg
  deriving DecidableEq, Repr

def Pol.under : Pol → Pol → Pol
  | .pos, p => p
  | .neg, _ => .neg

/-- The type an instance-valued checked term denotes, if it is syntactically clear. -/
def typeOf (spec : Spec) : Term → Option DomId
  | .app d _ => some d
  | .ref x => some (spec.removeDecoration x)
  | .project _ x => some (spec.removeDecoration x)
  | .tag _ d => some d
  | .when t _ => typeOf spec t
  | _ => none

abbrev Dep := DomId × Pol

/-- Binding a variable enumerates its type, which reads the type's holding instances
when the domain is not enumerable (and its domain constraint always); every bound
variable is therefore a read of its type. -/
def binderDeps (spec : Spec) (xs : List Var) (p : Pol) : List Dep :=
  xs.map fun x => (spec.removeDecoration x, p)

mutual
/-- The types a checked term reads, with the polarity of each read. `bound` are the
variables bound by enclosing binders (their mention is a binding, not a read). -/
def deps (spec : Spec) : Nat → List Var → Pol → Term → List Dep
  | 0, _, _, _ => []
  | fuel + 1, bound, p, t =>
    match t with
    | .boolLit _ | .intLit _ | .stringLit _ | .currentTime => []
    | .ref x => if bound.contains x then [] else [(spec.removeDecoration x, p)]
    | .app _ args => depsArgs spec fuel bound p args
    | .present t => (typeOf spec t).toList.map (·, p) ++ deps spec fuel bound p t
    | .violated t =>
      let own := (typeOf spec t).toList.map (·, p)
      let conds := match typeOf spec t with
        | some d => match spec.findViolationCond d with
          | some cs => depsList spec fuel (spec.components d) p cs
          | none => []
        | none => []
      own ++ conds ++ deps spec fuel bound p t
    | .enabled t =>
      let own := (typeOf spec t).toList.map (·, p)
      let more := match typeOf spec t with
        | some d => enabledDeps spec fuel [] p d
        | none => []
      own ++ more ++ deps spec fuel bound p t
    | .not t => deps spec fuel bound .neg t
    | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b | .mult a b | .mod a b
    | .div a b | .sub a b | .add a b | .eq a b | .neq a b | .when a b =>
      deps spec fuel bound p a ++ deps spec fuel bound p b
    | .heldFor t d => deps spec fuel bound p t ++ deps spec fuel bound p d
    | .evStatus want t =>
      let pol := if want == .established then p else .neg
      (typeOf spec t).toList.map (·, pol) ++ deps spec fuel bound pol t
    | .hasConflict t =>
      (typeOf spec t).toList.map (·, .neg) ++ deps spec fuel bound .neg t
    | .mulDivRound x n d _ =>
      deps spec fuel bound p x ++ deps spec fuel bound p n ++ deps spec fuel bound p d
    | .exists_ xs t => binderDeps spec xs p ++ deps spec fuel (bound ++ xs) p t
    | .forall_ xs t | .count xs t | .sum xs t | .max xs t | .min xs t =>
      binderDeps spec xs .neg ++ deps spec fuel (bound ++ xs) .neg t
    | .project t _ | .tag t _ | .untag t => deps spec fuel bound p t
def depsArgs (spec : Spec) : Nat → List Var → Pol → Args → List Dep
  | 0, _, _, _ => []
  | fuel + 1, bound, p, args =>
    match args with
    | .pos ts => depsList spec fuel bound p ts
    | .named ms => depsMods spec fuel bound p ms
def depsList (spec : Spec) : Nat → List Var → Pol → List Term → List Dep
  | 0, _, _, _ => []
  | _, _, _, [] => []
  | fuel + 1, bound, p, t :: ts => deps spec fuel bound p t ++ depsList spec fuel bound p ts
def depsMods (spec : Spec) : Nat → List Var → Pol → List (Var × Term) → List Dep
  | 0, _, _, _ => []
  | _, _, _, [] => []
  | fuel + 1, bound, p, (_, t) :: ms => deps spec fuel bound p t ++ depsMods spec fuel bound p ms
/-- What `Enabled(d(...))` reads beyond `d` itself: `d`'s conditions and the
enabledness of every act it syncs with. -/
def enabledDeps (spec : Spec) : Nat → List DomId → Pol → DomId → List Dep
  | 0, _, _, _ => []
  | fuel + 1, seen, p, d =>
    if seen.contains d then [] else
    match spec.findDecl d with
    | none => []
    | some tspec =>
      let xs := spec.components d
      let conds := depsList spec fuel xs p tspec.conditions
      let more := match tspec.kind with
        | .act a =>
          a.syncs.flatMap (fun s =>
            binderDeps spec s.xs p ++ deps spec fuel (xs ++ s.xs) p s.t ++
            (match typeOf spec s.t with
              | some d' => [(d', p)] ++ enabledDeps spec fuel (d :: seen) p d'
              | none => [])) ++
          depsList spec fuel xs p a.validWhen ++
          a.exceptUnder.flatMap (fun d' => [(d', p)] ++ enabledDeps spec fuel (d :: seen) p d')
        | _ => []
      conds ++ more
end

/-- The dependencies of a derived type: its derivation rules, its own conditions
(derived instances must satisfy them), and its domain constraint. -/
def typeDeps (spec : Spec) (d : DomId) (tspec : TypeSpec) : List Dep :=
  let xs := spec.components d
  let fuel := 1000
  let fromDerivations := tspec.derivation.flatMap fun
    | .dv ys t => binderDeps spec ys .pos ++ deps spec fuel ys .pos t
    | .holdsWhen t => binderDeps spec xs .pos ++ deps spec fuel xs .pos t
    | .defeasibleDAG _ rules =>
      binderDeps spec xs .neg ++
      (rules.flatMap fun r =>
        deps spec fuel xs .neg r.cond ++
        (match r.conseq with | .holdsBool _ => [] | .yieldsVal vt => deps spec fuel xs .neg vt))
  let fromConds := depsList spec fuel xs .pos tspec.conditions
  let fromFilter := deps spec fuel xs .pos tspec.domainConstraint
  fromDerivations ++ fromConds ++ fromFilter

/-- Strata of the derived types, lowest first, or the types on a negative cycle. -/
def strata (spec : Spec) : Except (List DomId) (List (List DomId)) :=
  let derived := spec.derivedTypes
  let edges : List (DomId × Dep) := derived.flatMap fun d =>
    match spec.findDecl d with
    | some t => (typeDeps spec d t).filter (fun e => derived.contains e.1) |>.map (d, ·)
    | none => []
  let direct (a b : DomId) : Bool := edges.any fun (x, (y, _)) => x == a && y == b
  let rec closure (fuel : Nat) (reach : List (DomId × DomId)) : List (DomId × DomId) :=
    match fuel with
    | 0 => reach
    | fuel + 1 =>
      let more := reach.flatMap fun (a, b) => reach.filterMap fun (b', c) =>
        if b == b' && !reach.contains (a, c) then some (a, c) else none
      let more := more.eraseDups
      if more.isEmpty then reach else closure fuel (reach ++ more)
  let reach := closure (derived.length * derived.length + 1) (edges.map fun (a, (b, _)) => (a, b))
  let reaches (a b : DomId) : Bool := a == b || reach.contains (a, b)
  let bad := edges.filter fun (a, (b, p)) => p == .neg && reaches b a
  if !bad.isEmpty then .error (bad.map (·.1) |>.eraseDups)
  else
    let rec layers (fuel : Nat) (pending done : List DomId) (acc : List (List DomId)) : List (List DomId) :=
      match fuel with
      | 0 => acc ++ [pending]
      | fuel + 1 =>
        if pending.isEmpty then acc else
        let ready := pending.filter fun d => pending.all fun e =>
          e == d || !(direct d e || reach.contains (d, e)) || reaches e d
        if ready.isEmpty then acc ++ [pending]
        else
          let groups := ready.foldl (fun (gs : List (List DomId)) d =>
            match gs.findIdx? (fun g => g.any fun e => reaches d e && reaches e d) with
            | some i => gs.set i (gs[i]! ++ [d])
            | none => gs ++ [[d]]) []
          layers fuel (pending.filter (fun d => !ready.contains d)) (done ++ ready) (acc ++ groups)
    .ok (layers (derived.length + 1) derived [] [])

end Stratify

namespace State

/-- `s₂` preserves the clock and every entry present in `s₁`. -/
def ExtendsEntries (s₁ s₂ : State) : Prop :=
  s₂.time = s₁.time ∧ ∀ te i, s₁.lookup te = some i → s₂.lookup te = some i

/-- Every instance that holds in `s₁` also holds in `s₂`. -/
def HoldsSubstate (s₁ s₂ : State) : Prop :=
  ∀ te, s₁.holds te = true → s₂.holds te = true

end State

end Charter
