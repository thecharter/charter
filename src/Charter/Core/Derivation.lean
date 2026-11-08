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
        | some d =>
          match spec.findDecl d with
          | some { kind := .duty ds, .. } =>
            depsList spec fuel (spec.components d) p ds.violatedWhen ++
            depsList spec fuel (spec.components d) .neg ds.excusedWhen ++
            ds.overriddenBy.map (·, .neg)
          | _ => []
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
    -- `Held(e) For d` reads whether `e` holds and since when (009.3), as `.present` does
    | .heldFor t d =>
      (typeOf spec t).toList.map (·, p) ++ deps spec fuel bound p t ++ deps spec fuel bound p d
    | .evStatus want t =>
      let pol := if want == .established then p else .neg
      (typeOf spec t).toList.map (·, pol) ++ deps spec fuel bound pol t
    | .hasConflict t =>
      (typeOf spec t).toList.map (·, .neg) ++ deps spec fuel bound .neg t
    | .mulDivRound x n d _ =>
      deps spec fuel bound p x ++ deps spec fuel bound p n ++ deps spec fuel bound p d
    | .fnApp d k =>
      (spec.chaseAlias d, p) :: deps spec fuel bound p k
    | .dimLit _ _ => []
    | .ite c t e =>
      deps spec fuel bound .neg c ++ deps spec fuel bound p t ++ deps spec fuel bound p e
    | .doneAt t | .stampOf t =>
      let own := (typeOf spec t).toList.filter (!spec.triggerable ·) |>.map (·, p)
      own ++ deps spec fuel bound p t
    | .overdueOf t =>
      (typeOf spec t).toList.map (·, p) ++ deps spec fuel bound p t
    | .calOp1 _ t => deps spec fuel bound p t
    | .calOp2 _ t a => deps spec fuel bound p t ++ deps spec fuel bound p a
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
      let domDeps := match tspec.domain with
        | .products pxs => binderDeps spec pxs .pos
        | _ => []
      domDeps ++
      (rules.flatMap fun r =>
        binderDeps spec r.freeVars .neg ++
        deps spec fuel (xs ++ r.freeVars) .neg r.cond ++
        (match r.conseq with | .holdsBool _ => [] | .yieldsVal vt => deps spec fuel (xs ++ r.freeVars) .neg vt))
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

namespace Spec

/-- Decidable structural well-formedness check on a resolved `Spec` (`CIR` snapshot, `D18`):
1. Every product component variable in every declared type's domain resolves to a declared type.
2. Every placeholder alias resolves via `chaseAlias` to a declared type.
3. Every `Power`/`Finding`/`Amend` carries `Valid when`, and every `Immunity`'s `against` target
   and `Act`'s `exceptUnder` target names a declared `Act` (or `"Amend"`).
4. Every `Duty`'s `overriddenBy` target names a declared `Duty`.
5. The derived-type dependency graph is stratifiable (`Stratify.strata` succeeds). -/
def checkWellFormed (s : Spec) : Bool :=
  let componentsOk := s.decls.all fun (_, t) =>
    match t.domain with
    | .products xs => xs.all fun x => (s.findDecl (s.removeDecoration x)).isSome
    | _ => true
  let aliasesOk := s.aliases.all fun (f, _) => (s.lookupDecl (s.chaseAlias f)).isSome
  let actsOk := s.decls.all fun (_, t) =>
    match t.kind with
    | .act a =>
      (!a.isPower || !a.validWhen.isEmpty) &&
      a.exceptUnder.all fun target =>
        match s.findDecl target with
        | some tt => match tt.kind with | .act _ => true | _ => false
        | none => false
    | .immunity im => im.against.all fun target =>
      target == "Amend" ||
      match s.findDecl target with
      | some tt => match tt.kind with | .act _ => true | _ => false
      | none => false
    | .duty du => du.overriddenBy.all fun target =>
      match s.findDecl target with
      | some tt => match tt.kind with | .duty _ => true | _ => false
      | none => false
    | _ => true
  componentsOk && aliasesOk && actsOk && (Stratify.strata s).isOk

/-- Propositional well-formedness of a canonical `Spec` (`CIR`). -/
def WellFormed (s : Spec) : Prop := s.checkWellFormed = true

theorem checkWellFormed_iff (s : Spec) : s.checkWellFormed = true ↔ s.WellFormed := Iff.rfl

/-- Every `Power` declaration in a `WellFormed` `Spec` carries at least one explicit
`Valid when` competence condition (`005.10`, `G3.1`). -/
theorem wellFormed_power_has_validWhen {s : Spec} (hwf : s.WellFormed)
    {d : DomId} {t : TypeSpec} {a : ActSpec}
    (hmem : (d, t) ∈ s.decls) (hkind : t.kind = .act a) (hpow : a.isPower = true) :
    a.validWhen ≠ [] := by
  unfold WellFormed checkWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  have hacts := hwf.1.2
  rw [List.all_eq_true] at hacts
  have ht := hacts (d, t) hmem
  dsimp only at ht
  rw [hkind] at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ht
  cases ht.1 with
  | inl hnp => rw [hpow] at hnp; cases hnp
  | inr hne =>
    intro hemp
    rw [hemp] at hne
    cases hne

end Spec

end Charter
