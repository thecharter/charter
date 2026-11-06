import Charter.Core.Term

/-!
# Charter.Core.Defeasible — Stratified `Default` / `Exception` / `Priority` Calculus (`D23`, `G3.3`)

Implements Charter's Catala-inspired defeasible rule calculus (`docs/rfc.md` §4.4, `T21`, `T22`):
1. Named `Default` and `Exception ... Overrides ...` rules (boolean `Holds`/`Rejects` on `Fact`/`Bool`,
   value-yielding `Yields <val> When <cond>` on `Function`/`Var`) plus explicit `Priority ... Over ...` edges.
2. Static cycle detection (`findPriorityCycle`, `CHR034`) and transitive topological DAG compilation
   (`compileDefeasibleDAG`).
3. Declarative undefeated-rule specification (`resolveDefeasibleSpec`) and single-pass compiled
   topological decision-DAG evaluator (`evalCompiledDAG`), with a constructive kernel proof of
   exact equivalence (`evalCompiledDAG_eq_spec`, zero extra axioms).
-/

namespace Charter

/-- Internal derived domain storing active normative rule conflicts (`(target, r1, r2)`, `fromSat = true`). -/
def defConflictDom : String := "$def_conflict"

/-- Evaluated prescription of a single active defeasible rule (`boolOut` for `Fact`/`Bool`, `elemOut` for `Function`/`Var`). -/
inductive DefeasibleVal where
  | boolOut (b : Bool)
  | elemOut (te : Tagged)
  deriving Repr, Inhabited

def DefeasibleVal.beq : DefeasibleVal → DefeasibleVal → Bool
  | .boolOut a, .boolOut b => a == b
  | .elemOut a, .elemOut b => a == b
  | _, _ => false

instance : BEq DefeasibleVal := ⟨DefeasibleVal.beq⟩

/-- Term-level consequence of a defeasible rule in `Core.Spec`. -/
inductive DefeasibleConseq where
  | holdsBool (b : Bool)
  | yieldsVal (valTerm : Term)
  deriving Repr, Inhabited

def DefeasibleConseq.mapDom (f : DomId → DomId) : DefeasibleConseq → DefeasibleConseq
  | .holdsBool b => .holdsBool b
  | .yieldsVal v => .yieldsVal (v.mapDom f)

/-- One named `Default` or `Exception` rule attached to a `Fact`/`Bool`/`Var`/`Function` (`004.12`). -/
structure DefeasibleRule where
  id        : String
  isDefault : Bool := true
  overrides : List String := []
  cond      : Term
  conseq    : DefeasibleConseq
  deriving Repr, Inhabited

def DefeasibleRule.mapDom (f : DomId → DomId) (r : DefeasibleRule) : DefeasibleRule :=
  { r with cond := r.cond.mapDom f, conseq := r.conseq.mapDom f }

/-- Outcome of evaluating a defeasible rule hierarchy on one instance/key (`T21`, `T22`). -/
inductive DefeasibleResult (α : Type) where
  | none
  | determined (winnerId : String) (val : α)
  | conflict (rule1 : String) (rule2 : String)
  deriving Repr, DecidableEq, Inhabited

/-- One node of a topologically compiled decision DAG: `dominators` lists every rule ID that
transitively beats `id`. -/
structure CompiledRuleNode where
  id         : String
  dominators : List String
  deriving Repr, DecidableEq, Inhabited

namespace Defeasible

/-- Transitive reachability in a finite directed priority edge list `(higher, lower)` bounded by `fuel`. -/
def reaches : Nat → List (String × String) → String → String → Bool
  | 0, _, _, _ => false
  | fuel + 1, edges, src, dst =>
    let nexts := edges.filterMap fun (a, b) => if a == src then some b else none
    if nexts.contains dst then true
    else nexts.any (fun mid => reaches fuel edges mid dst)

/-- Compute strict transitive dominance `beats edges rHi rLo` across `n` rules. -/
def beatsOf (n : Nat) (edges : List (String × String)) (rHi rLo : String) : Bool :=
  reaches (n + 1) edges rHi rLo

/-- Detect any priority cycle (`beats r r = true`) among `ruleIds`, returning the cyclic rule IDs (`CHR034`). -/
def findPriorityCycle (ruleIds : List String) (edges : List (String × String)) : Option (List String) :=
  let cyc := ruleIds.filter fun r => beatsOf ruleIds.length edges r r
  if cyc.isEmpty then none else some cyc

/-- Topologically order `ruleIds` so that whenever `beats rHi rLo = true`, `rHi` precedes `rLo`. -/
def topoOrder : Nat → (String → String → Bool) → List String → List String
  | 0, _, rem => rem
  | _, _, [] => []
  | fuel + 1, beats, rem =>
    let roots := rem.filter fun r => !rem.any (fun other => other != r && beats other r)
    match roots with
    | [] => rem
    | _ =>
      let rest := rem.filter fun r => !roots.contains r
      roots ++ topoOrder fuel beats rest

/-- Compile rule IDs and explicit edges `(higher, lower)` into a topologically ordered `CompiledRuleNode` DAG. -/
def compileDefeasibleDAG (ruleIds : List String) (edges : List (String × String)) : List CompiledRuleNode :=
  let beats := beatsOf ruleIds.length edges
  let ordered := topoOrder (ruleIds.length + 1) beats ruleIds
  ordered.map fun r =>
    { id := r, dominators := ordered.filter (fun hi => beats hi r) }

/-! ## Declarative Specification vs. Single-Pass Compiled DAG Evaluator -/

def activeList {α : Type} (activeOf : String → Option α) : List String → List (String × α)
  | [] => []
  | r :: rs =>
    match activeOf r with
    | some v => (r, v) :: activeList activeOf rs
    | none   => activeList activeOf rs

def undefeatedList {α : Type} (beats : String → String → Bool) (act : List (String × α)) : List (String × α) :=
  act.filter fun p => !act.any (fun q => beats q.1 p.1)

def classifyUndefeated {α : Type} [BEq α] : List (String × α) → DefeasibleResult α
  | [] => .none
  | (r₀, v₀) :: rest =>
    match rest.find? (fun p => !(p.2 == v₀)) with
    | none => .determined r₀ v₀
    | some (r₂, _) => .conflict r₀ r₂

/-- Declarative specification: filter all active rules to those undefeated under `beats`,
then classify into `.none`, `.determined`, or `.conflict` (`docs/rfc.md` §4.4). -/
def resolveDefeasibleSpec {α : Type} [BEq α]
    (beats : String → String → Bool) (ruleIds : List String) (activeOf : String → Option α) : DefeasibleResult α :=
  classifyUndefeated (undefeatedList beats (activeList activeOf ruleIds))

/-- Single-pass step of the compiled topological decision DAG. -/
def evalDAGStep {α : Type} (activeOf : String → Option α) (winners : List (String × α)) (n : CompiledRuleNode) : List (String × α) :=
  match activeOf n.id with
  | none => winners
  | some v =>
    if winners.any (fun w => n.dominators.contains w.1) then winners
    else winners ++ [(n.id, v)]

/-- Evaluate a compiled decision DAG in one linear pass. -/
def evalCompiledDAG {α : Type} [BEq α]
    (dag : List CompiledRuleNode) (activeOf : String → Option α) : DefeasibleResult α :=
  classifyUndefeated (dag.foldl (evalDAGStep activeOf) [])

/-! ## Kernel-Checked Equivalence & Acceptance Proofs (`G3.3`, `T21`, `T22`) -/

/-- Structural validity of a compiled topological DAG with respect to strict partial order `beats`:
1. `beats` is irreflexive and transitive on the DAG's rules;
2. No later node in `dag` beats an earlier node (`topological`);
3. Each node's `dominators` list agrees with `beats` on all earlier nodes. -/
def ValidCompiledDAG (beats : String → String → Bool) (seen : List String) : List CompiledRuleNode → Prop
  | [] => True
  | n :: rest =>
    beats n.id n.id = false ∧
    (∀ s ∈ seen, beats n.id s = false) ∧
    (∀ s ∈ seen, n.dominators.contains s = beats s n.id) ∧
    (∀ w x, w ∈ seen → x ∈ seen → beats w x = true → beats x n.id = true → beats w n.id = true) ∧
    ValidCompiledDAG beats (seen ++ [n.id]) rest

theorem activeList_append {α : Type} (activeOf : String → Option α) (xs ys : List String) :
    activeList activeOf (xs ++ ys) = activeList activeOf xs ++ activeList activeOf ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, activeList]
    cases activeOf x <;> simp only [List.cons_append, ih]

theorem mem_activeList_fst {α : Type} {activeOf : String → Option α} {ids : List String} {p : String × α}
    (h : p ∈ activeList activeOf ids) : p.1 ∈ ids := by
  induction ids with
  | nil => cases h
  | cons r rs ih =>
    simp only [activeList] at h
    cases ha : activeOf r with
    | none =>
      rw [ha] at h
      exact List.mem_cons_of_mem r (ih h)
    | some v =>
      rw [ha, List.mem_cons] at h
      cases h with
      | inl heq => rw [heq]; exact List.mem_cons_self
      | inr hmem => exact List.mem_cons_of_mem r (ih hmem)

theorem filter_congr_mem {β : Type} {l : List β} {f g : β → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.filter f = l.filter g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : f a = g a := h a List.mem_cons_self
    have has : ∀ x ∈ as, f x = g x := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.filter_cons, ha, ih has]

theorem any_append_singleton_false {β : Type} (l : List β) (z : β) (p : β → Bool)
    (hz : p z = false) : (l ++ [z]).any p = l.any p := by
  rw [List.any_append, List.any_cons, List.any_nil, hz, Bool.or_false, Bool.or_false]

/-- Loop invariant for `evalCompiledDAG`:
1. `winners` equals `undefeatedList beats (activeList activeOf seen)`;
2. Every active rule in `seen` is either in `winners` or beaten by some rule in `winners`. -/
def DAGLoopInv {α : Type} (beats : String → String → Bool) (activeOf : String → Option α)
    (seen : List String) (winners : List (String × α)) : Prop :=
  winners = undefeatedList beats (activeList activeOf seen) ∧
  ∀ p ∈ activeList activeOf seen, p ∈ winners ∨ ∃ w ∈ winners, beats w.1 p.1 = true

theorem evalDAGStep_preserves_inv {α : Type} {beats : String → String → Bool}
    {activeOf : String → Option α} {seen : List String} {winners : List (String × α)}
    {n : CompiledRuleNode}
    (hInv : DAGLoopInv beats activeOf seen winners)
    (hIrrefl : beats n.id n.id = false)
    (hTopo : ∀ s ∈ seen, beats n.id s = false)
    (hDoms : ∀ s ∈ seen, n.dominators.contains s = beats s n.id)
    (hTrans : ∀ w x, w ∈ seen → x ∈ seen → beats w x = true → beats x n.id = true → beats w n.id = true) :
    DAGLoopInv beats activeOf (seen ++ [n.id]) (evalDAGStep activeOf winners n) := by
  rcases hInv with ⟨hWinEq, hDomComp⟩
  have hWinSub : ∀ w ∈ winners, w.1 ∈ seen := by
    intro w hw
    rw [hWinEq] at hw
    have hwAct : w ∈ activeList activeOf seen := (List.mem_filter.mp hw).1
    exact mem_activeList_fst hwAct
  unfold evalDAGStep
  cases hAct : activeOf n.id with
  | none =>
    have hApp : activeList activeOf (seen ++ [n.id]) = activeList activeOf seen := by
      rw [activeList_append]; simp [activeList, hAct]
    refine ⟨?_, ?_⟩
    · rw [hApp]; exact hWinEq
    · rw [hApp]; exact hDomComp
  | some v =>
    have hApp : activeList activeOf (seen ++ [n.id]) = activeList activeOf seen ++ [(n.id, v)] := by
      rw [activeList_append]; simp [activeList, hAct]
    -- Earlier active rules are unaffected by `(n.id, v)` because `beats n.id s = false`
    have hEarlierFilter :
        (activeList activeOf seen).filter (fun p => !(activeList activeOf seen ++ [(n.id, v)]).any (fun q => beats q.1 p.1)) =
        undefeatedList beats (activeList activeOf seen) := by
      unfold undefeatedList
      apply filter_congr_mem
      intro p hp
      have hpSeen : p.1 ∈ seen := mem_activeList_fst hp
      have hnb : beats n.id p.1 = false := hTopo p.1 hpSeen
      rw [any_append_singleton_false _ (n.id, v) (fun q => beats q.1 p.1) hnb]
    -- `winners.any (n.dominators.contains ·.1)` iff `(activeList activeOf seen).any (beats ·.1 n.id)`
    have hAnyEq :
        winners.any (fun w => n.dominators.contains w.1) =
        (activeList activeOf seen).any (fun q => beats q.1 n.id) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨w, hw, hcont⟩
        have hwSeen : w.1 ∈ seen := hWinSub w hw
        rw [hDoms w.1 hwSeen] at hcont
        have hwAct : w ∈ activeList activeOf seen := by
          rw [hWinEq] at hw; exact (List.mem_filter.mp hw).1
        exact ⟨w, hwAct, hcont⟩
      · rintro ⟨q, hqAct, hbeats⟩
        have hqSeen : q.1 ∈ seen := mem_activeList_fst hqAct
        cases hDomComp q hqAct with
        | inl hqWin =>
          refine ⟨q, hqWin, ?_⟩
          rw [hDoms q.1 hqSeen]
          exact hbeats
        | inr hw =>
          rcases hw with ⟨w, hwWin, hwBeatsQ⟩
          have hwSeen : w.1 ∈ seen := hWinSub w hwWin
          have hwBeatsN : beats w.1 n.id = true := hTrans w.1 q.1 hwSeen hqSeen hwBeatsQ hbeats
          refine ⟨w, hwWin, ?_⟩
          rw [hDoms w.1 hwSeen]
          exact hwBeatsN
    dsimp only
    by_cases hDef : winners.any (fun w => n.dominators.contains w.1) = true
    · rw [if_pos hDef]
      have hActAny : (activeList activeOf seen).any (fun q => beats q.1 n.id) = true := by
        rw [← hAnyEq]; exact hDef
      have hNewAny : (activeList activeOf seen ++ [(n.id, v)]).any (fun q => beats q.1 n.id) = true := by
        rw [List.any_append, hActAny, Bool.true_or]
      refine ⟨?_, ?_⟩
      · unfold undefeatedList
        rw [hApp, List.filter_append, hEarlierFilter]
        simp only [List.filter_cons, List.filter_nil, hNewAny, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        exact hWinEq
      · rw [hApp]
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        cases hp with
        | inl hpOld => exact hDomComp p hpOld
        | inr hpEq =>
          subst hpEq
          right
          have hEx : ∃ w ∈ winners, n.dominators.contains w.1 = true := List.any_eq_true.mp hDef
          rcases hEx with ⟨w, hw, hcont⟩
          rw [hDoms w.1 (hWinSub w hw)] at hcont
          exact ⟨w, hw, hcont⟩
    · rw [if_neg hDef]
      have hDefF : winners.any (fun w => n.dominators.contains w.1) = false := Bool.eq_false_iff.mpr hDef
      have hActAnyF : (activeList activeOf seen).any (fun q => beats q.1 n.id) = false := by
        rw [← hAnyEq]; exact hDefF
      have hNewAnyF : (activeList activeOf seen ++ [(n.id, v)]).any (fun q => beats q.1 n.id) = false := by
        rw [any_append_singleton_false _ (n.id, v) (fun q => beats q.1 n.id) hIrrefl]
        exact hActAnyF
      refine ⟨?_, ?_⟩
      · unfold undefeatedList
        rw [hApp, List.filter_append, hEarlierFilter]
        simp only [List.filter_cons, List.filter_nil, hNewAnyF, Bool.not_false, ↓reduceIte]
        rw [hWinEq]
      · rw [hApp]
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        cases hp with
        | inl hpOld =>
          cases hDomComp p hpOld with
          | inl hw => left; exact List.mem_append_left _ hw
          | inr hex =>
            rcases hex with ⟨w, hw, hb⟩
            right
            exact ⟨w, List.mem_append_left _ hw, hb⟩
        | inr hpEq =>
          subst hpEq
          left
          exact List.mem_append_right _ List.mem_cons_self

theorem foldl_evalDAGStep_inv {α : Type} (beats : String → String → Bool)
    (activeOf : String → Option α) :
    ∀ (dag : List CompiledRuleNode) (seen : List String) (winners : List (String × α)),
      DAGLoopInv beats activeOf seen winners →
      ValidCompiledDAG beats seen dag →
      DAGLoopInv beats activeOf (seen ++ dag.map (·.id)) (dag.foldl (evalDAGStep activeOf) winners)
  | [], seen, winners, hInv, _ => by
    simp only [List.map_nil, List.append_nil, List.foldl_nil]
    exact hInv
  | n :: rest, seen, winners, hInv, hValid => by
    rcases hValid with ⟨hIrrefl, hTopo, hDoms, hTrans, hRest⟩
    have hStep := evalDAGStep_preserves_inv hInv hIrrefl hTopo hDoms hTrans
    have hRec := foldl_evalDAGStep_inv beats activeOf rest (seen ++ [n.id]) (evalDAGStep activeOf winners n) hStep hRest
    simpa only [List.map_cons, List.append_assoc, List.singleton_append, List.foldl_cons] using hRec

/-- Main correspondence theorem (`G3.3`, `Law 9`): for any valid topologically compiled
decision DAG `dag`, single-pass `evalCompiledDAG` agrees identically with the declarative
specification `resolveDefeasibleSpec`. -/
theorem evalCompiledDAG_eq_spec {α : Type} [BEq α]
    (beats : String → String → Bool) (dag : List CompiledRuleNode) (activeOf : String → Option α)
    (hValid : ValidCompiledDAG beats [] dag) :
    evalCompiledDAG dag activeOf = resolveDefeasibleSpec beats (dag.map (·.id)) activeOf := by
  have hBase : DAGLoopInv beats activeOf [] [] := ⟨rfl, fun _ h => nomatch h⟩
  have hFinal := (foldl_evalDAGStep_inv beats activeOf dag [] [] hBase hValid).1
  simp only [List.nil_append] at hFinal
  unfold evalCompiledDAG resolveDefeasibleSpec
  rw [hFinal]

/-- `T21`: two distinct unranked active rules with incompatible outcomes (`!(v₂ == v₁)`) yield `.conflict r₁ r₂`. -/
theorem unranked_disagreement_yields_conflict {α : Type} [BEq α]
    (r₁ r₂ : String) (v₁ v₂ : α) (hDistinct : (r₂ == r₁) = false) (hNe : (v₂ == v₁) = false) :
    resolveDefeasibleSpec (fun _ _ => false) [r₁, r₂]
      (fun r => if r == r₁ then some v₁ else if r == r₂ then some v₂ else none) =
    .conflict r₁ r₂ := by
  simp [resolveDefeasibleSpec, activeList, undefeatedList, classifyUndefeated, hDistinct, hNe]

/-- `T22`: a three-tier Catala exception-to-exception chain (`r₂ > r₁ > r₀`, transitive `r₂ > r₀`)
yields `v₀` on `{r₀}`, `v₁` on `{r₀, r₁}`, and `v₂` on `{r₀, r₁, r₂}`. -/
theorem exception_to_exception_resolves :
    let edges := [("r2", "r1"), ("r1", "r0")]
    let dag := compileDefeasibleDAG ["r0", "r1", "r2"] edges
    evalCompiledDAG dag (fun r => if r == "r0" then some 20 else none) = .determined "r0" 20 ∧
    evalCompiledDAG dag (fun r => if r == "r0" then some 20 else if r == "r1" then some 0 else none) = .determined "r1" 0 ∧
    evalCompiledDAG dag (fun r => if r == "r0" then some 20 else if r == "r1" then some 0 else if r == "r2" then some 10 else none) = .determined "r2" 10 :=
  ⟨rfl, rfl, rfl⟩

end Defeasible

end Charter
