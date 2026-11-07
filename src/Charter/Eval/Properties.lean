import Charter.Core.Transition

/-!
# Charter.Eval.Properties — What the evaluator is proved to do

Law 9 wants one definition of what a program means and an evaluator proved to
agree with it. Phase 1 has the evaluator; the declarative semantics it must agree
with is not yet written, and this file is the honest beginning: properties of the
evaluator that the spec chapters state, proved outright; the `#print axioms`
lines at the end show each depends on `propext` at most (Law 10).

- 005.3 *create beats terminate*: the precedence of merged assignments.
- 004.3 *assignment beats derivation*: deriving an assigned instance changes
  nothing, and a derivation step that reports no change made none.
- 004.5 *the saturation of a stratum is a fixpoint*: when `saturateStratum`
  returns a state, one more pass over the stratum derives nothing new. This is
  the half of "least fixpoint" that is provable before the declarative semantics
  of `Charter.Eval.eval` exists; leastness needs monotonicity, which needs it.
- 004.3 in full (`Saturate.rebaseAndSat_assigned`, 2026-10-25): an assigned fact is
  exactly what the state holds after saturation, with its stamp, expiry and origin:
  `rebase` keeps it and no derivation step replaces it. Rests on instances comparing
  structurally (`Elem.beq_iff`, `Tagged.beq_iff`: the hand-written `==` is equality).
- 006.2 and 006.5 agree (`isViolated_of_holds`): the query `Violated(d(…))` and the
  report after a phrase both go through `isViolated`, which for an instance that holds
  is the violation condition itself.

Each theorem names the spec statement it discharges. What is still missing for Law 9
(plan §3, Phase 1's exit) is the declarative semantics itself: a relational meaning of
terms, derivation (the least fixpoint), triggers and violations, independent of `M`,
with the evaluator proved sound and complete against it. These theorems are properties
of the evaluator stated in the spec's words, not that agreement proof.
-/

namespace Charter

/-! ## 005.3 Create beats terminate -/

namespace Store

/-- A creation merged with anything is still a creation. -/
theorem combine_true_left (u : Option Int) (b : Option Tagged) (a : Assignment) :
    ∃ u' b', union.combine (.holdsTrue u b) a = .holdsTrue u' b' := by
  cases a <;> exact ⟨_, _, rfl⟩

theorem combine_true_right (u : Option Int) (b : Option Tagged) (a : Assignment) :
    ∃ u' b', union.combine a (.holdsTrue u b) = .holdsTrue u' b' := by
  cases a <;> exact ⟨_, _, rfl⟩

/-- 005.3: within one step, creating an instance beats terminating it, whichever
side of the merge it comes from, and keeps its expiry and origin; terminating beats
forgetting. -/
theorem create_beats_terminate (u : Option Int) (b c : Option Tagged) :
    union.combine (.holdsTrue u b) (.holdsFalse c) = .holdsTrue u b ∧
    union.combine (.holdsFalse c) (.holdsTrue u b) = .holdsTrue u b ∧
    union.combine (.holdsFalse c) .unknown = .holdsFalse c ∧ union.combine .unknown (.holdsFalse c) = .holdsFalse c :=
  ⟨rfl, rfl, rfl, rfl⟩

end Store

/-! ## 004.3 Assignment beats derivation -/

namespace State

/-- Deriving an instance that has an assignment changes nothing. -/
theorem derive_assigned (s : State) (since : Int) (te : Tagged) (i : Info) (h : s.lookup te = some i) :
    s.derive since te = (s, false) := by
  unfold derive; rw [h]

/-- A derivation step that reports no change made none. -/
theorem derive_unchanged (s : State) (since : Int) (te : Tagged) (s1 : State)
    (h : s.derive since te = (s1, false)) : s1 = s := by
  unfold derive at h
  cases hl : s.lookup te <;> rw [hl] at h <;> simp only [Prod.mk.injEq] at h
  · exact absurd h.2 (by decide)
  · exact h.1.symm

theorem deriveAll_unchanged (prev : List (Tagged × Info)) : ∀ (tes : List Tagged) (s s2 : State),
    deriveAll prev s tes = (s2, false) → s2 = s
  | [], _, _, h => by
    simp only [deriveAll, Prod.mk.injEq] at h
    exact h.1.symm
  | te :: tes, s, s2, h => by
    simp only [deriveAll] at h
    rcases h1 : s.derive (stampFrom prev s.time te) te with ⟨s1, ch⟩
    rw [h1] at h
    rcases h2 : deriveAll prev s1 tes with ⟨s2', ch2⟩
    rw [h2] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hs, hb⟩ := h
    have hch : ch = false := by cases ch <;> simp_all
    have hch2 : ch2 = false := by cases ch2 <;> simp_all
    have e1 : s1 = s := derive_unchanged s _ te s1 (by rw [h1, hch])
    have e2 : s2' = s1 := deriveAll_unchanged prev tes s1 s2' (by rw [h2, hch2])
    rw [← hs, e2, e1]

end State

/-! ## 004.5 Saturation reaches a fixpoint -/

namespace Saturate

theorem passType_unchanged (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State),
      passType spec specIdx prev d tspec cs s = .ok (s2, false) → s2 = s
  | [], s, s2, h => by
    simp only [passType, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | c :: cs, s, s2, h => by
    simp only [passType] at h
    split at h
    · cases h
    · next ress _ =>
      rcases h1 : State.deriveAll prev s ress.flatten with ⟨s1, ch⟩
      rw [h1] at h
      split at h
      · cases h
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hb⟩ := h
        have hch : ch = false := by cases ch <;> simp_all
        have hch2 : ch2 = false := by cases ch2 <;> simp_all
        have e1 : s1 = s := State.deriveAll_unchanged prev ress.flatten s s1 (by rw [h1, hch])
        have e2 : s2' = s1 := passType_unchanged spec specIdx prev d tspec cs s1 s2' (by rw [h2, hch2])
        rw [← hs, e2, e1]

theorem pass_unchanged (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State), pass spec specIdx prev types s = .ok (s2, false) → s2 = s
  | [], s, s2, h => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | d :: ds, s, s2, h => by
    simp only [pass] at h
    split at h
    · exact pass_unchanged spec specIdx prev ds s s2 h
    · next tspec _ =>
      split at h
      · cases h
      · next s1 ch h1 =>
        split at h
        · cases h
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, hb⟩ := h
          have hch : ch = false := by cases ch <;> simp_all
          have hch2 : ch2 = false := by cases ch2 <;> simp_all
          have e1 : s1 = s := passType_unchanged spec specIdx prev d tspec tspec.derivation s s1 (by rw [h1, hch])
          have e2 : s2' = s1 := pass_unchanged spec specIdx prev ds s1 s2' (by rw [h2, hch2])
          rw [← hs, e2, e1]

/-- 004.5: the state `saturateStratum` returns is a fixpoint of the stratum's
derivation step: one more pass derives nothing. -/
theorem saturateStratum_fixpoint (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State),
      saturateStratum spec specIdx prev types fuel s = .ok s' → pass spec specIdx prev types s' = .ok (s', false)
  | 0, _, _, h => by simp [saturateStratum] at h
  | fuel + 1, s, s', h => by
    simp only [saturateStratum] at h
    split at h
    · cases h
    · next s1 changed heq =>
      split at h
      · exact saturateStratum_fixpoint spec specIdx prev types fuel s1 s' h
      · next hnot =>
        simp only [Except.ok.injEq] at h
        have hc : changed = false := by cases changed <;> simp_all
        rw [hc] at heq
        have e : s1 = s := pass_unchanged spec specIdx prev types s s1 heq
        subst e
        subst h
        exact heq

end Saturate

/-! ## Instances compare structurally

The state's lookups compare instances with `==` (`Elem.beq`, written by hand because
`Elem` is a nested inductive); every statement below about a lookup needs that this is
equality, which is what the spec means by "lookups compare instances structurally"
(`Charter.Core.State`). -/

mutual
theorem Elem.beq_iff : ∀ (a b : Elem), Elem.beq a b = true ↔ a = b
  | .str a, .str b => by simp [Elem.beq]
  | .str _, .int _ => by simp [Elem.beq]
  | .str _, .prod _ => by simp [Elem.beq]
  | .int _, .str _ => by simp [Elem.beq]
  | .int a, .int b => by simp [Elem.beq]
  | .int _, .prod _ => by simp [Elem.beq]
  | .prod _, .str _ => by simp [Elem.beq]
  | .prod _, .int _ => by simp [Elem.beq]
  | .prod xs, .prod ys => by
    simp only [Elem.beq, Elem.prod.injEq]
    exact Elem.beqArgs_iff xs ys
theorem Elem.beqArgs_iff : ∀ (xs ys : List (Elem × DomId)), Elem.beqArgs xs ys = true ↔ xs = ys
  | [], [] => by simp [Elem.beqArgs]
  | [], _ :: _ => by simp [Elem.beqArgs]
  | _ :: _, [] => by simp [Elem.beqArgs]
  | (e, d) :: xs, (e', d') :: ys => by
    simp only [Elem.beqArgs, Bool.and_eq_true, beq_iff_eq, List.cons.injEq, Prod.mk.injEq]
    rw [Elem.beq_iff e e', Elem.beqArgs_iff xs ys]
    constructor
    · rintro ⟨⟨hd, he⟩, hl⟩; exact ⟨⟨he, hd⟩, hl⟩
    · rintro ⟨⟨he, hd⟩, hl⟩; exact ⟨⟨hd, he⟩, hl⟩
end

theorem Tagged.beq_iff (a b : Tagged) : (a == b) = true ↔ a = b := by
  show (a.2 == b.2 && Elem.beq a.1 b.1) = true ↔ a = b
  simp only [Bool.and_eq_true, beq_iff_eq, Elem.beq_iff]
  constructor
  · rintro ⟨h2, h1⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem Tagged.beq_eq_false_of_ne {a b : Tagged} (h : a ≠ b) : (a == b) = false := by
  cases hb : (a == b)
  · rfl
  · exact absurd ((Tagged.beq_iff a b).mp hb) h

/-! ## 004.3 Assignment beats derivation, in full: an assigned fact survives saturation

Saturation (`rebaseAndSat`) removes the derived facts, then re-derives stratum by stratum.
An assigned fact (one not `fromSat`) is kept by `rebase`, and no derivation step ever
replaces an instance that has an assignment (`derive`), so the assignment, with its stamp,
expiry and origin, is exactly what the state holds afterwards. -/

namespace State

theorem find?_filter_of_find? {α} (p q : α → Bool) : ∀ (l : List α) (x : α),
    l.find? p = some x → q x = true → (l.filter q).find? p = some x
  | [], _, h, _ => by simp at h
  | y :: ys, x, h, hq => by
    simp only [List.find?_cons] at h
    by_cases hp : p y = true
    · rw [hp] at h; simp only [Option.some.injEq] at h; subst h
      simp [hq, hp]
    · have hpf : p y = false := by simpa using hp
      rw [hpf] at h; simp only at h
      by_cases hqy : q y = true
      · simp [hqy, hpf, find?_filter_of_find? p q ys x h hq]
      · have : q y = false := by simpa using hqy
        simp [this, find?_filter_of_find? p q ys x h hq]

/-- `rebase` keeps every assigned fact as it is. -/
theorem rebase_lookup (s : State) (te : Tagged) (i : Info) (h : s.lookup te = some i) (hi : i.fromSat = false) :
    s.rebase.lookup te = some i := by
  unfold lookup at h ⊢
  simp only [rebase]
  rcases hf : s.contents.find? (·.1 == te) with _ | ⟨te', i'⟩
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
    rw [find?_filter_of_find? _ _ s.contents (te', i') hf (by simp [h, hi])]
    simp [h]

/-- `derive` never touches an instance that has an assignment. -/
theorem derive_lookup (s : State) (since : Int) (te te' : Tagged) (i : Info) (h : s.lookup te = some i) :
    (s.derive since te').1.lookup te = some i := by
  unfold derive
  rcases hl : s.lookup te' with _ | i'
  · have hne : te' ≠ te := by rintro rfl; rw [hl] at h; cases h
    simp only [lookup, List.find?_cons, Tagged.beq_eq_false_of_ne hne]
    exact h
  · exact h

theorem deriveAll_lookup (prev : List (Tagged × Info)) : ∀ (tes : List Tagged) (s : State) (te : Tagged) (i : Info),
    s.lookup te = some i → (deriveAll prev s tes).1.lookup te = some i
  | [], _, _, _, h => h
  | te' :: tes, s, te, i, h => by
    simp only [deriveAll]
    rcases h1 : s.derive (stampFrom prev s.time te') te' with ⟨s1, ch⟩
    have := derive_lookup s (stampFrom prev s.time te') te te' i h
    rw [h1] at this
    rcases h2 : deriveAll prev s1 tes with ⟨s2, ch2⟩
    have := deriveAll_lookup prev tes s1 te i this
    rw [h2] at this
    exact this

end State

namespace Saturate

theorem passType_lookup (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State) (b : Bool) (te : Tagged) (i : Info),
      s.lookup te = some i → passType spec specIdx prev d tspec cs s = .ok (s2, b) → s2.lookup te = some i
  | [], s, s2, b, te, i, h, hp => by
    simp only [passType, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]; exact h
  | c :: cs, s, s2, b, te, i, h, hp => by
    simp only [passType] at hp
    split at hp
    · cases hp
    · next ress _ =>
      rcases h1 : State.deriveAll prev s ress.flatten with ⟨s1, ch⟩
      rw [h1] at hp
      have hs1 : s1.lookup te = some i := by
        have := State.deriveAll_lookup prev ress.flatten s te i h
        rw [h1] at this; exact this
      split at hp
      · cases hp
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp
        rw [← hp.1]
        exact passType_lookup spec specIdx prev d tspec cs s1 s2' ch2 te i hs1 h2

theorem pass_lookup (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State) (b : Bool) (te : Tagged) (i : Info),
      s.lookup te = some i → pass spec specIdx prev types s = .ok (s2, b) → s2.lookup te = some i
  | [], s, s2, b, te, i, h, hp => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]; exact h
  | d :: ds, s, s2, b, te, i, h, hp => by
    simp only [pass] at hp
    split at hp
    · exact pass_lookup spec specIdx prev ds s s2 b te i h hp
    · next tspec _ =>
      split at hp
      · cases hp
      · next s1 ch h1 =>
        have hs1 : s1.lookup te = some i :=
          passType_lookup spec specIdx prev d tspec tspec.derivation s s1 ch te i h h1
        split at hp
        · cases hp
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          rw [← hp.1]
          exact pass_lookup spec specIdx prev ds s1 s2' ch2 te i hs1 h2

theorem saturateStratum_lookup (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State) (te : Tagged) (i : Info),
      s.lookup te = some i → saturateStratum spec specIdx prev types fuel s = .ok s' → s'.lookup te = some i
  | 0, _, _, _, _, _, h => by simp [saturateStratum] at h
  | fuel + 1, s, s', te, i, h, hs => by
    simp only [saturateStratum] at hs
    split at hs
    · cases hs
    · next s1 changed heq =>
      have hs1 : s1.lookup te = some i := pass_lookup spec specIdx prev types s s1 changed te i h heq
      split at hs
      · exact saturateStratum_lookup spec specIdx prev types fuel s1 s' te i hs1 hs
      · simp only [Except.ok.injEq] at hs; rw [← hs]; exact hs1

theorem foldl_saturate_lookup (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) :
    ∀ (strata : List (List DomId)) (s s' : State) (te : Tagged) (i : Info),
      s.lookup te = some i →
      strata.foldlM (fun s layer => saturateStratum spec specIdx prev layer 100000 s) s = .ok s' →
      s'.lookup te = some i
  | [], s, s', te, i, h, hf => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hf
    rw [← hf]; exact h
  | layer :: rest, s, s', te, i, h, hf => by
    simp only [List.foldlM, bind, Except.bind] at hf
    split at hf
    · cases hf
    · next s1 h1 =>
      exact foldl_saturate_lookup spec specIdx prev rest s1 s' te i
        (saturateStratum_lookup spec specIdx prev layer 100000 s s1 te i h h1) hf

/-- 004.3, in full: an assigned fact is exactly what the state holds after saturation,
with its stamp, expiry and origin. -/
theorem rebaseAndSat_assigned (spec : Spec) (strata : List (List DomId)) (s s' : State) (te : Tagged) (i : Info)
    (h : s.lookup te = some i) (hi : i.fromSat = false) (hs : rebaseAndSat spec strata s = .ok s') :
    s'.lookup te = some i :=
  foldl_saturate_lookup spec spec.buildIndex s.derivedFacts strata s.rebase s' te i (State.rebase_lookup s te i h hi) hs

end Saturate

/-! ## 006.2 and 006.5: the report and the query agree

`Violated(d(…))` (the query, 006.2) and the report after a phrase (006.5) both go through
`isViolated`; for an instance that holds, `isViolated` is the violation condition itself. -/

namespace M

theorem run_bind_single {α β} (m : M α) (f : α → M β) (c : Ctx) (s : Subs) (a : α)
    (h : m.run c s = .ok [a]) : (m >>= f).run c s = (f a).run c s := by
  show (do let as ← m.run c s; let bss ← as.mapM (fun a => (f a).run c s); pure bss.flatten) = (f a).run c s
  rw [h]
  simp only [List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  rcases hf : (f a).run c s with e | bs
  · rfl
  · simp

end M

/-- Aduty instance that holds is violated exactly when its violation condition holds. -/
theorem isViolated_of_holds (fuel : Nat) (te : Tagged) (c : Ctx) (subs : Subs)
    (h : (M.isHolds fuel te).run c subs = .ok [true]) :
    (M.isViolated (fuel + 1) te).run c subs =
      (M.evalViolationCondition fuel te (c.spec.findViolationCond te.2)).run c subs := by
  show ((do if !(← M.isHolds fuel te) then pure false else M.evalViolationCondition fuel te ((← M.getSpec).findViolationCond te.2)) : M Bool).run c subs = _
  rw [M.run_bind_single _ _ c subs true h]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [M.run_bind_single _ _ c subs c.spec rfl]

/-! ## G1.3a — `DomMap` radix-index refinement (`State.buildIndex` soundness)

`Eval` uses transient 8-bit `DomMap` radix tries (`State.buildIndex`) to accelerate key
and per-`DomId` lookups without changing `State`'s representation. The theorems below
prove unconditionally (even under hash collisions) that `State.buildIndex` returns the
exact filtered bucket of `s.contents` and agrees identically with `State.lookup` and
`State.trueInstances`. -/

namespace DomMap

def WF {α : Type} : Nat → DomMap α → Prop
  | 0, .empty => True
  | 0, .leaf _ => True
  | 0, .branch _ _ => False
  | _ + 1, .empty => True
  | _ + 1, .leaf _ => False
  | n + 1, .branch l r => WF n l ∧ WF n r

theorem wf_empty {α : Type} : ∀ n, WF (α := α) n .empty
  | 0 => trivial
  | _ + 1 => trivial

theorem modifyAux_wf {α : Type} (f : Option α → α) :
    ∀ (n h : Nat) (k : DomId) (m : DomMap α), WF n m → WF n (modifyAux f n h k m)
  | 0, _, _, .empty, _ => trivial
  | 0, _, k, .leaf es, _ => by
    unfold modifyAux
    cases es.find? (·.1 == k) <;> trivial
  | 0, _, _, .branch _ _, hwf => False.elim hwf
  | n + 1, h, k, .empty, _ => by
    unfold modifyAux
    cases he : (h % 2 == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨wf_empty n, modifyAux_wf f n (h / 2) k .empty (wf_empty n)⟩
    · simp only [↓reduceIte]
      exact ⟨modifyAux_wf f n (h / 2) k .empty (wf_empty n), wf_empty n⟩
  | _ + 1, _, _, .leaf _, hwf => False.elim hwf
  | n + 1, h, k, .branch l r, ⟨hl, hr⟩ => by
    unfold modifyAux
    cases he : (h % 2 == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hl, modifyAux_wf f n (h / 2) k r hr⟩
    · simp only [↓reduceIte]
      exact ⟨modifyAux_wf f n (h / 2) k l hl, hr⟩

theorem find?_filter_ne_key {α : Type} (k k' : DomId) (h : (k == k') = false) :
    ∀ (es : List (DomId × α)), (es.filter (·.1 != k)).find? (·.1 == k') = es.find? (·.1 == k')
  | [] => rfl
  | (x, v) :: rest => by
    simp only [List.filter, bne]
    cases hxk : (x == k)
    · simp only [Bool.not_false, List.find?_cons]
      cases (x == k')
      · exact find?_filter_ne_key k k' h rest
      · rfl
    · have xeq : x = k := beq_iff_eq.mp hxk
      subst xeq
      simp only [Bool.not_true, List.find?_cons, h]
      exact find?_filter_ne_key x k' h rest

theorem lookupAux_empty {α : Type} : ∀ (n h : Nat) (k : DomId), lookupAux (α := α) n h .empty k = none
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem lookupAux_modifyAux_self {α : Type} (f : Option α → α) :
    ∀ (n h : Nat) (k : DomId) (m : DomMap α), WF n m →
      lookupAux n h (modifyAux f n h k m) k = some (f (lookupAux n h m k))
  | 0, _, k, .empty, _ => by
    simp [modifyAux, lookupAux]
  | 0, _, k, .leaf es, _ => by
    unfold modifyAux lookupAux
    cases hf : es.find? (·.1 == k) with
    | none => simp
    | some pv =>
      rcases pv with ⟨k0, v⟩
      simp
  | 0, _, _, .branch _ _, hwf => False.elim hwf
  | n + 1, h, k, .empty, _ => by
    unfold modifyAux
    cases he : (h % 2 == 0)
    · simp only [lookupAux, he, Bool.false_eq_true, ↓reduceIte]
      rw [lookupAux_modifyAux_self f n (h / 2) k .empty (wf_empty n), lookupAux_empty]
    · simp only [lookupAux, he, ↓reduceIte]
      rw [lookupAux_modifyAux_self f n (h / 2) k .empty (wf_empty n), lookupAux_empty]
  | _ + 1, _, _, .leaf _, hwf => False.elim hwf
  | n + 1, h, k, .branch l r, ⟨hl, hr⟩ => by
    unfold modifyAux
    cases he : (h % 2 == 0)
    · simp only [lookupAux, he, Bool.false_eq_true, ↓reduceIte]
      exact lookupAux_modifyAux_self f n (h / 2) k r hr
    · simp only [lookupAux, he, ↓reduceIte]
      exact lookupAux_modifyAux_self f n (h / 2) k l hl

theorem lookupAux_modifyAux_ne {α : Type} (f : Option α → α) {k k' : DomId} (hne : (k == k') = false) :
    ∀ (n h h' : Nat) (m : DomMap α), WF n m →
      lookupAux n h' (modifyAux f n h k m) k' = lookupAux n h' m k'
  | 0, _, _, .empty, _ => by
    simp [modifyAux, lookupAux, hne]
  | 0, _, _, .leaf es, _ => by
    unfold modifyAux lookupAux
    cases hf : es.find? (·.1 == k) with
    | none => simp [hne]
    | some pv =>
      rcases pv with ⟨k0, v⟩
      simp [hne, find?_filter_ne_key k k' hne es]
  | 0, _, _, .branch _ _, hwf => False.elim hwf
  | n + 1, h, h', .empty, _ => by
    unfold modifyAux
    cases he : (h % 2 == 0) <;> cases he' : (h' % 2 == 0)
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte]
      rw [lookupAux_modifyAux_ne f hne n (h / 2) (h' / 2) .empty (wf_empty n), lookupAux_empty]
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte, lookupAux_empty]
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte, lookupAux_empty]
    · simp only [lookupAux, he', ↓reduceIte]
      rw [lookupAux_modifyAux_ne f hne n (h / 2) (h' / 2) .empty (wf_empty n), lookupAux_empty]
  | _ + 1, _, _, .leaf _, hwf => False.elim hwf
  | n + 1, h, h', .branch l r, ⟨hl, hr⟩ => by
    unfold modifyAux
    cases he : (h % 2 == 0) <;> cases he' : (h' % 2 == 0)
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte]
      exact lookupAux_modifyAux_ne f hne n (h / 2) (h' / 2) r hr
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte]
    · simp only [lookupAux, he', Bool.false_eq_true, ↓reduceIte]
    · simp only [lookupAux, he', ↓reduceIte]
      exact lookupAux_modifyAux_ne f hne n (h / 2) (h' / 2) l hl

theorem prepend_wf {β : Type} (k : DomId) (v : β) (m : DomMap (List β)) (hwf : WF treeDepth m) :
    WF treeDepth (m.prepend k v) :=
  modifyAux_wf _ treeDepth (hash k) k m hwf

theorem lookup_prepend_self {β : Type} (k : DomId) (v : β) (m : DomMap (List β)) (hwf : WF treeDepth m) :
    ((m.prepend k v).lookup k).getD [] = v :: (m.lookup k).getD [] := by
  unfold prepend lookup
  rw [lookupAux_modifyAux_self _ treeDepth (hash k) k m hwf]
  cases lookupAux treeDepth (hash k) m k <;> rfl

theorem lookup_prepend_ne {β : Type} {k k' : DomId} (hne : (k == k') = false) (v : β)
    (m : DomMap (List β)) (hwf : WF treeDepth m) :
    (m.prepend k v).lookup k' = m.lookup k' :=
  lookupAux_modifyAux_ne _ hne treeDepth (hash k) (hash k') m hwf

end DomMap

namespace State

theorem foldr_prepend_wf :
    ∀ (xs : List (Tagged × Info)), DomMap.WF DomMap.treeDepth (xs.foldr (fun p m => m.prepend p.1.2 p) .empty)
  | [] => DomMap.wf_empty DomMap.treeDepth
  | p :: rest => DomMap.prepend_wf p.1.2 p _ (foldr_prepend_wf rest)

/-- Exact bucket equivalence for `State.buildIndex`: looking up `d` in the radix index
returns the order-preserving list of entries in `s.contents` belonging to `d`. -/
theorem buildIndex_bucket_eq (s : State) (d : DomId) :
    ((s.buildIndex.lookup d).getD []) = s.contents.filter (fun p => p.1.2 == d) := by
  unfold buildIndex
  induction s.contents with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldr_cons, List.filter]
    have hwf := foldr_prepend_wf rest
    cases heq : (p.1.2 == d)
    · rw [DomMap.lookup_prepend_ne heq p _ hwf, ih]
    · have pd : p.1.2 = d := beq_iff_eq.mp heq
      rw [pd, DomMap.lookup_prepend_self d p _ hwf, ih]

theorem find?_filter_dom_eq (te : Tagged) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => p.1.2 == te.2)).find? (·.1 == te) = xs.find? (·.1 == te)
  | [] => rfl
  | p :: rest => by
    simp only [List.filter]
    cases hdom : (p.1.2 == te.2)
    · have hteF : (p.1 == te) = false := by
        cases hb : (p.1 == te)
        · rfl
        · have peq := (Tagged.beq_iff p.1 te).mp hb
          subst peq
          simp at hdom
      simp only [List.find?_cons, hteF]
      exact find?_filter_dom_eq te rest
    · simp only [List.find?_cons]
      cases (p.1 == te)
      · exact find?_filter_dom_eq te rest
      · rfl

/-- Looking up an instance through `State.buildIndex` is identical to `State.lookup`. -/
theorem buildIndex_lookup_eq (s : State) (te : Tagged) :
    (((s.buildIndex.lookup te.2).getD []).find? (·.1 == te)).map (·.2) = s.lookup te := by
  rw [buildIndex_bucket_eq, find?_filter_dom_eq]
  rfl

end State

/-! ## G1.3b — Post-saturation pre-fixpoint closure and Tarski least fixpoint (004.5)

Completes the second half of `004.5` noted in the module header:
1. `saturateStratum_closed`: at the state `s*` returned by `saturateStratum`, every
   consequence derivable from `s*` by any rule in `types` is already present in `s*`.
2. `saturateStratum_least_prefixpoint`: whenever the stratum's rules are monotone over
   extensions of `s₀`, every instance holding in `s*` holds in every closed extension `M`
   of `s₀` — i.e. `s*` computes the unique Tarski least pre-fixpoint above `s₀`. -/

namespace Saturate

/-- Declarative immediate consequence of `types` on `s`: some rule of `d ∈ types` produces `te`. -/
def StratumDerives (spec : Spec) (specIdx : Spec.SpecIndex) (types : List DomId) (s : State) (te : Tagged) : Prop :=
  ∃ d ∈ types, ∃ tspec, (specIdx.lookup d).map (·.1) = some tspec ∧
    ∃ c ∈ tspec.derivation, ∃ ress,
      runM spec specIdx s (deriveClause d tspec c) = .ok ress ∧ te ∈ ress.flatten

/-- Monotonicity of `types` over extensions of `s₀` (satisfied whenever negated/aggregated
dependencies lie strictly in lower strata, `D6`). -/
def MonotoneStratum (spec : Spec) (specIdx : Spec.SpecIndex) (types : List DomId) (s₀ : State) : Prop :=
  ∀ s₁ s₂ te,
    State.ExtendsEntries s₀ s₁ →
    State.ExtendsEntries s₀ s₂ →
    State.HoldsSubstate s₁ s₂ →
    StratumDerives spec specIdx types s₁ te →
    StratumDerives spec specIdx types s₂ te

/-- `M` extends `s₀`'s entries/clock and is closed under `StratumDerives` on unassigned instances. -/
def IsClosedExtension (spec : Spec) (specIdx : Spec.SpecIndex) (types : List DomId) (s₀ M : State) : Prop :=
  State.ExtendsEntries s₀ M ∧
    ∀ te, s₀.lookup te = none → StratumDerives spec specIdx types M te → M.holds te = true

theorem deriveAll_unchanged_mem (prev : List (Tagged × Info)) :
    ∀ (tes : List Tagged) (s s2 : State) (te : Tagged),
      State.deriveAll prev s tes = (s2, false) → te ∈ tes → (s.lookup te).isSome = true
  | [], _, _, _, _, hmem => nomatch hmem
  | hd :: tl, s, s2, te, h, hmem => by
    simp only [State.deriveAll] at h
    rcases h1 : s.derive (State.stampFrom prev s.time hd) hd with ⟨s1, ch1⟩
    rw [h1] at h
    rcases h2 : State.deriveAll prev s1 tl with ⟨s2', ch2⟩
    rw [h2] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, hb⟩ := h
    have hch1 : ch1 = false := by cases ch1 <;> simp_all
    have hch2 : ch2 = false := by cases ch2 <;> simp_all
    have es1 : s1 = s := State.derive_unchanged s _ hd s1 (by rw [h1, hch1])
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      unfold State.derive at h1
      cases hl : s.lookup te with
      | none => rw [hl] at h1; simp [hch1] at h1
      | some _ => rfl
    | inr htl =>
      rw [← es1]
      exact deriveAll_unchanged_mem prev tl s1 s2' te (by rw [h2, hch2]) htl

theorem passType_unchanged_mem (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State) (c : Derivation) (ress : List (List Tagged)) (te : Tagged),
      passType spec specIdx prev d tspec cs s = .ok (s2, false) →
      c ∈ cs →
      runM spec specIdx s (deriveClause d tspec c) = .ok ress →
      te ∈ ress.flatten →
      (s.lookup te).isSome = true
  | [], _, _, _, _, _, _, hmem, _, _ => nomatch hmem
  | c0 :: cs, s, s2, c, ress, te, hp, hmem, hrun, hte => by
    simp only [passType] at hp
    split at hp
    · cases hp
    · next ress0 hrun0 =>
      rcases h1 : State.deriveAll prev s ress0.flatten with ⟨s1, ch1⟩
      rw [h1] at hp
      split at hp
      · cases hp
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp
        obtain ⟨_, hb⟩ := hp
        have hch1 : ch1 = false := by cases ch1 <;> simp_all
        have hch2 : ch2 = false := by cases ch2 <;> simp_all
        have es1 : s1 = s := State.deriveAll_unchanged prev ress0.flatten s s1 (by rw [h1, hch1])
        cases List.mem_cons.mp hmem with
        | inl heq =>
          subst heq
          rw [hrun0] at hrun
          injection hrun with hress
          subst hress
          exact deriveAll_unchanged_mem prev ress0.flatten s s1 te (by rw [h1, hch1]) hte
        | inr hcs =>
          rw [← es1]
          exact passType_unchanged_mem spec specIdx prev d tspec cs s1 s2' c ress te
            (by rw [h2, hch2]) hcs (by rw [es1]; exact hrun) hte

theorem pass_unchanged_mem (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State) (te : Tagged),
      pass spec specIdx prev types s = .ok (s2, false) →
      StratumDerives spec specIdx types s te →
      (s.lookup te).isSome = true
  | [], _, _, _, _, ⟨_, hmem, _⟩ => nomatch hmem
  | d0 :: ds, s, s2, te, hp, ⟨d, hdMem, tspec, htspec, c, hcMem, ress, hrun, hte⟩ => by
    unfold pass at hp
    cases hlook : (specIdx.lookup d0).map (·.1) with
    | none =>
      rw [hlook] at hp
      dsimp only at hp
      cases List.mem_cons.mp hdMem with
      | inl heq => subst heq; rw [hlook] at htspec; cases htspec
      | inr hds =>
        exact pass_unchanged_mem spec specIdx prev ds s s2 te hp
          ⟨d, hds, tspec, htspec, c, hcMem, ress, hrun, hte⟩
    | some tspec0 =>
      rw [hlook] at hp
      dsimp only at hp
      split at hp
      · cases hp
      · next s1 ch1 h1 =>
        split at hp
        · cases hp
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          obtain ⟨_, hb⟩ := hp
          have hch1 : ch1 = false := by cases ch1 <;> simp_all
          have hch2 : ch2 = false := by cases ch2 <;> simp_all
          have es1 : s1 = s := passType_unchanged spec specIdx prev d0 tspec0 tspec0.derivation s s1 (by rw [h1, hch1])
          cases List.mem_cons.mp hdMem with
          | inl heq =>
            rw [heq] at htspec hrun
            rw [hlook] at htspec
            injection htspec with hts
            rw [← hts] at hcMem hrun
            exact passType_unchanged_mem spec specIdx prev d0 tspec0 tspec0.derivation s s1 c ress te
              (by rw [h1, hch1]) hcMem hrun hte
          | inr hds =>
            rw [← es1]
            exact pass_unchanged_mem spec specIdx prev ds s1 s2' te (by rw [h2, hch2])
              ⟨d, hds, tspec, htspec, c, hcMem, ress, (by rw [es1]; exact hrun), hte⟩

/-- Post-saturation pre-fixpoint closure (`004.5`): every consequence derivable from `s'`
by the rules of `types` is already present in `s'`. -/
theorem saturateStratum_closed (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (types : List DomId) (fuel : Nat) (s s' : State)
    (hs : saturateStratum spec specIdx prev types fuel s = .ok s')
    (hder : StratumDerives spec specIdx types s' te) :
    (s'.lookup te).isSome = true :=
  pass_unchanged_mem spec specIdx prev types s' s' te
    (saturateStratum_fixpoint spec specIdx prev types fuel s s' hs) hder

theorem derive_time (s : State) (since : Int) (te : Tagged) : (s.derive since te).1.time = s.time := by
  unfold State.derive
  cases s.lookup te <;> rfl

theorem derive_holds_substate {s₀ M s : State} (since : Int) (te : Tagged)
    (hext : State.ExtendsEntries s₀ s)
    (hsub : State.HoldsSubstate s M)
    (hM : s₀.lookup te = none → M.holds te = true) :
    State.ExtendsEntries s₀ (s.derive since te).1 ∧ State.HoldsSubstate (s.derive since te).1 M := by
  constructor
  · constructor
    · rw [derive_time]; exact hext.1
    · intro te' i hi
      exact State.derive_lookup s since te' te i (hext.2 te' i hi)
  · intro te' hh
    unfold State.derive at hh
    cases hl : s.lookup te with
    | some _ =>
      rw [hl] at hh
      exact hsub te' hh
    | none =>
      rw [hl] at hh
      by_cases heq : te == te'
      · have teEq : te = te' := (Tagged.beq_iff te te').mp heq
        subst teEq
        have hs0 : s₀.lookup te = none := by
          cases hs0l : s₀.lookup te with
          | none => rfl
          | some i0 =>
            have := hext.2 te i0 hs0l
            rw [hl] at this
            cases this
        exact hM hs0
      · have hneF : (te == te') = false := Bool.eq_false_iff.mpr heq
        have hlook : ({ s with contents := (te, ⟨true, true, since, none, .derived te.2 s.step⟩) :: s.contents } : State).lookup te' = s.lookup te' := by
          simp [State.lookup, hneF]
        unfold State.holds at hh
        rw [hlook] at hh
        exact hsub te' hh

theorem deriveAll_holds_substate (prev : List (Tagged × Info)) {s₀ M : State} :
    ∀ (tes : List Tagged) (s : State),
      State.ExtendsEntries s₀ s →
      State.HoldsSubstate s M →
      (∀ te ∈ tes, s₀.lookup te = none → M.holds te = true) →
      State.ExtendsEntries s₀ (State.deriveAll prev s tes).1 ∧ State.HoldsSubstate (State.deriveAll prev s tes).1 M
  | [], s, hext, hsub, _ => ⟨hext, hsub⟩
  | te :: tes, s, hext, hsub, hall => by
    simp only [State.deriveAll]
    have hstep := derive_holds_substate (State.stampFrom prev s.time te) te hext hsub
      (hall te (List.mem_cons_self ..))
    rcases h1 : s.derive (State.stampFrom prev s.time te) te with ⟨s1, ch1⟩
    rw [h1] at hstep
    rcases h2 : State.deriveAll prev s1 tes with ⟨s2, ch2⟩
    have hrest := deriveAll_holds_substate prev tes s1 hstep.1 hstep.2
      (fun te' hm => hall te' (List.mem_cons_of_mem te hm))
    rw [h2] at hrest
    exact hrest

theorem passType_least (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (types : List DomId) (d : DomId) (tspec : TypeSpec)
    (hdMem : d ∈ types) (htspec : (specIdx.lookup d).map (·.1) = some tspec)
    {s₀ M : State} (hmono : MonotoneStratum spec specIdx types s₀)
    (hclosed : IsClosedExtension spec specIdx types s₀ M) :
    ∀ (cs : List Derivation) (s s2 : State) (ch : Bool),
      (∀ c ∈ cs, c ∈ tspec.derivation) →
      State.ExtendsEntries s₀ s →
      State.HoldsSubstate s M →
      passType spec specIdx prev d tspec cs s = .ok (s2, ch) →
      State.ExtendsEntries s₀ s2 ∧ State.HoldsSubstate s2 M
  | [], s, s2, _, _, hext, hsub, hp => by
    simp only [passType, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]; exact ⟨hext, hsub⟩
  | c :: cs, s, s2, ch, hsubCs, hext, hsub, hp => by
    simp only [passType] at hp
    split at hp
    · cases hp
    · next ress hrun =>
      have hall : ∀ te ∈ ress.flatten, s₀.lookup te = none → M.holds te = true := by
        intro te hte hs0
        have hderS : StratumDerives spec specIdx types s te :=
          ⟨d, hdMem, tspec, htspec, c, hsubCs c (List.mem_cons_self ..), ress, hrun, hte⟩
        have hderM : StratumDerives spec specIdx types M te :=
          hmono s M te hext hclosed.1 hsub hderS
        exact hclosed.2 te hs0 hderM
      have h1pair := deriveAll_holds_substate prev ress.flatten s hext hsub hall
      rcases h1 : State.deriveAll prev s ress.flatten with ⟨s1, ch1⟩
      rw [h1] at hp h1pair
      split at hp
      · cases hp
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp
        rw [← hp.1]
        exact passType_least spec specIdx prev types d tspec hdMem htspec hmono hclosed
          cs s1 s2' ch2 (fun c' hm => hsubCs c' (List.mem_cons_of_mem c hm)) h1pair.1 h1pair.2 h2

theorem pass_least (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (allTypes : List DomId) {s₀ M : State}
    (hmono : MonotoneStratum spec specIdx allTypes s₀)
    (hclosed : IsClosedExtension spec specIdx allTypes s₀ M) :
    ∀ (types : List DomId) (s s2 : State) (ch : Bool),
      (∀ d ∈ types, d ∈ allTypes) →
      State.ExtendsEntries s₀ s →
      State.HoldsSubstate s M →
      pass spec specIdx prev types s = .ok (s2, ch) →
      State.ExtendsEntries s₀ s2 ∧ State.HoldsSubstate s2 M
  | [], s, s2, _, _, hext, hsub, hp => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]; exact ⟨hext, hsub⟩
  | d :: ds, s, s2, ch, hsubTypes, hext, hsub, hp => by
    unfold pass at hp
    cases hlook : (specIdx.lookup d).map (·.1) with
    | none =>
      rw [hlook] at hp
      dsimp only at hp
      exact pass_least spec specIdx prev allTypes hmono hclosed ds s s2 ch
        (fun d' hm => hsubTypes d' (List.mem_cons_of_mem d hm)) hext hsub hp
    | some tspec =>
      rw [hlook] at hp
      dsimp only at hp
      split at hp
      · cases hp
      · next s1 ch1 h1 =>
        have hstep := passType_least spec specIdx prev allTypes d tspec
          (hsubTypes d (List.mem_cons_self ..)) hlook hmono hclosed
          tspec.derivation s s1 ch1 (fun _ hm => hm) hext hsub h1
        split at hp
        · cases hp
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          rw [← hp.1]
          exact pass_least spec specIdx prev allTypes hmono hclosed ds s1 s2' ch2
            (fun d' hm => hsubTypes d' (List.mem_cons_of_mem d hm)) hstep.1 hstep.2 h2

theorem saturateStratum_least_aux (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (types : List DomId) {s₀ M : State}
    (hmono : MonotoneStratum spec specIdx types s₀)
    (hclosed : IsClosedExtension spec specIdx types s₀ M) :
    ∀ (fuel : Nat) (s s' : State),
      State.ExtendsEntries s₀ s →
      State.HoldsSubstate s M →
      saturateStratum spec specIdx prev types fuel s = .ok s' →
      State.ExtendsEntries s₀ s' ∧ State.HoldsSubstate s' M
  | 0, _, _, _, _, hs => by simp [saturateStratum] at hs
  | fuel + 1, s, s', hext, hsub, hs => by
    simp only [saturateStratum] at hs
    split at hs
    · cases hs
    · next s1 changed heq =>
      have hstep := pass_least spec specIdx prev types hmono hclosed types s s1 changed
        (fun _ hm => hm) hext hsub heq
      split at hs
      · exact saturateStratum_least_aux spec specIdx prev types hmono hclosed fuel s1 s' hstep.1 hstep.2 hs
      · simp only [Except.ok.injEq] at hs
        rw [← hs]
        exact hstep

/-- Tarski/Kleene least pre-fixpoint theorem (`004.5`): for any monotone stratum `types`,
the state `s'` computed by `saturateStratum` from `s₀` is minimal among all closed
extensions `M` of `s₀` — every instance holding in `s'` holds in `M`. -/
theorem saturateStratum_least_prefixpoint (spec : Spec) (specIdx : Spec.SpecIndex)
    (prev : List (Tagged × Info)) (types : List DomId) (fuel : Nat) (s₀ s' M : State)
    (hmono : MonotoneStratum spec specIdx types s₀)
    (hclosed : IsClosedExtension spec specIdx types s₀ M)
    (hs : saturateStratum spec specIdx prev types fuel s₀ = .ok s') :
    State.HoldsSubstate s' M := by
  have hext0 : State.ExtendsEntries s₀ s₀ := ⟨rfl, fun _ _ h => h⟩
  have hsub0 : State.HoldsSubstate s₀ M := by
    intro te hh
    unfold State.holds at hh ⊢
    cases hl : s₀.lookup te with
    | none => rw [hl] at hh; cases hh
    | some i =>
      rw [hl] at hh
      rw [hclosed.1.2 te i hl, hclosed.1.1]
      exact hh
  exact (saturateStratum_least_aux spec specIdx prev types hmono hclosed fuel s₀ s' hext0 hsub0 hs).2

end Saturate

/-! ## G1.4 — Half-open expiry (`T25`), Frame Preservation, and Live Evaluator Correspondence (`Law 9`)

Proves:
1. `expiry_half_open_boundary` (`T25`): `[t0, t0 + d)` holds at `t0 + d - 1` and expires at `t0 + d` and `t0 + d + 1`.
2. `frame_preservation_other_type` & `frame_preservation_unrestricted`: `State.makeAssignments` leaves unrelated types and untouched unrestricted instances identical (value, `since`, `expiry`, `origin`).
3. `evalPhrase_sound` & `evalPhrase_complete`: `runPhrase` is sound and complete with respect to `DeclPhraseStep`.
4. `replay_deterministic` & `replay_trace_deterministic`: single-step and multi-step transitions are deterministic.
5. `clock_never_decreases`: no transition (successful or failed) ever moves `state.time` backwards (`009.1`). -/

/-- `T25` (`009.3`): an instance created at `t0` for positive duration `d` is live at
`t0` and `t0 + d - 1`, and expired at `t0 + d` and `t0 + d + 1`. -/
theorem expiry_half_open_boundary (t0 d : Int) (orig : Origin) (hd : 0 < d) :
    let i : Info := ⟨true, false, t0, some (t0 + d), orig⟩
    i.live t0 = true ∧
    i.live (t0 + d - 1) = true ∧
    i.live (t0 + d) = false ∧
    i.live (t0 + d + 1) = false := by
  simp only [Info.live, Bool.true_and, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

namespace State

theorem find?_filter_not_beq_ne (te' te : Tagged) (hne : te' ≠ te) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => !(p.1 == te'))).find? (·.1 == te) = xs.find? (·.1 == te)
  | [] => rfl
  | p :: rest => by
    simp only [List.filter]
    cases hp : (p.1 == te')
    · simp only [Bool.not_false, List.find?_cons]
      cases (p.1 == te)
      · exact find?_filter_not_beq_ne te' te hne rest
      · rfl
    · have peq : p.1 = te' := (Tagged.beq_iff p.1 te').mp hp
      have hpte : (p.1 == te) = false := by
        rw [peq]
        exact Tagged.beq_eq_false_of_ne hne
      simp only [Bool.not_true, List.find?_cons, hpte]
      exact find?_filter_not_beq_ne te' te hne rest

theorem insert_lookup_ne (s : State) (te' te : Tagged) (i : Info) (hne : te' ≠ te) :
    (s.insert te' i).lookup te = s.lookup te := by
  unfold insert lookup
  simp only [List.find?_cons, Tagged.beq_eq_false_of_ne hne]
  rw [find?_filter_not_beq_ne te' te hne s.contents]

theorem erase_lookup_ne (s : State) (te' te : Tagged) (hne : te' ≠ te) :
    (s.erase te').lookup te = s.lookup te := by
  unfold erase lookup
  rw [find?_filter_not_beq_ne te' te hne s.contents]

theorem create_lookup_ne (s : State) (te' te : Tagged) (exp : Option Int) (orig : Origin) (hne : te' ≠ te) :
    (s.create te' exp orig).lookup te = s.lookup te := by
  unfold create
  exact insert_lookup_ne s te' te _ hne

theorem find?_map_preserve_at (te : Tagged) (f : (Tagged × Info) → (Tagged × Info))
    (hf1 : ∀ p, (f p).1 = p.1)
    (hfte : ∀ p, p.1 = te → f p = p) :
    ∀ (xs : List (Tagged × Info)), (xs.map f).find? (·.1 == te) = xs.find? (·.1 == te)
  | [] => rfl
  | p :: rest => by
    simp only [List.map_cons, List.find?_cons, hf1 p]
    cases hp : (p.1 == te)
    · exact find?_map_preserve_at te f hf1 hfte rest
    · rw [hfte p ((Tagged.beq_iff p.1 te).mp hp)]

/-- Single-entry frame lemma for an assignment whose type differs from `te.2`. -/
theorem applyAssignment_other_type (spec : Spec) (stepNum : Nat) (p : Tagged × Assignment)
    (s : State) (te : Tagged) (hdom : p.1.2 ≠ te.2) :
    (applyAssignment spec stepNum p s).lookup te = s.lookup te := by
  rcases p with ⟨te', a⟩
  dsimp only at hdom
  have hne : te' ≠ te := by intro heq; apply hdom; rw [heq]
  unfold applyAssignment
  dsimp only
  cases a with
  | holdsFalse by_ => exact insert_lookup_ne s te' te _ hne
  | unknown => exact erase_lookup_ne s te' te hne
  | holdsTrue expiry by_ =>
    dsimp only
    cases hrest : spec.restrictionOf te'.2 with
    | none => exact create_lookup_ne s te' te _ _ hne
    | some r =>
      cases r with
      | var =>
        dsimp only
        rw [create_lookup_ne _ te' te _ _ hne]
        unfold lookup
        rw [find?_map_preserve_at te _
          (fun q => by cases (q.1.2 == te'.2) <;> rfl)
          (fun q hq => by
            have hneDom : (q.1.2 == te'.2) = false := by
              rw [hq]
              cases hb : (te.2 == te'.2)
              · rfl
              · exact absurd (beq_iff_eq.mp hb).symm hdom
            simp [hneDom])]
      | function =>
        dsimp only
        cases te'.1 with
        | str _ => rfl
        | int _ => rfl
        | prod args =>
          cases args with
          | nil => rfl
          | cons f restArgs =>
            cases restArgs with
            | nil => rfl
            | cons g more =>
              cases more with
              | cons _ _ => rfl
              | nil =>
                dsimp only
                rw [create_lookup_ne _ te' te _ _ hne]
                unfold lookup
                rw [find?_map_preserve_at te _
                  (fun q => by
                    cases q.1.1 with
                    | str _ => rfl
                    | int _ => rfl
                    | prod qargs =>
                      cases qargs with
                      | nil => rfl
                      | cons f' qr =>
                        cases qr with
                        | nil => rfl
                        | cons g' qm =>
                          cases qm with
                          | cons _ _ => rfl
                          | nil =>
                            dsimp only
                            cases (q.1.2 == te'.2 && Elem.beq f.1 f'.1 && f.2 == f'.2) <;> rfl)
                  (fun q hq => by
                    have hneDom : (q.1.2 == te'.2) = false := by
                      rw [hq]
                      cases hb : (te.2 == te'.2)
                      · rfl
                      · exact absurd (beq_iff_eq.mp hb).symm hdom
                    cases q.1.1 with
                    | str _ => rfl
                    | int _ => rfl
                    | prod qargs =>
                      cases qargs with
                      | nil => rfl
                      | cons f' qr =>
                        cases qr with
                        | nil => rfl
                        | cons g' qm =>
                          cases qm with
                          | cons _ _ => rfl
                          | nil => simp [hneDom])]

theorem foldr_applyAssignment_other_type (spec : Spec) (stepNum : Nat) :
    ∀ (st : Store) (s : State) (te : Tagged),
      (∀ p ∈ st, p.1.2 ≠ te.2) →
      (st.foldr (applyAssignment spec stepNum) s).lookup te = s.lookup te
  | [], _, _, _ => rfl
  | p :: st, s, te, hall => by
    simp only [List.foldr_cons]
    rw [applyAssignment_other_type spec stepNum p _ te (hall p (List.mem_cons_self ..)),
        foldr_applyAssignment_other_type spec stepNum st s te (fun q hq => hall q (List.mem_cons_of_mem p hq))]

/-- Frame preservation across types: an assignment batch touching no instance of `te.2`
leaves `s.lookup te` (value, `fromSat`, `since`, `expiry`, and `origin`) unchanged. -/
theorem frame_preservation_other_type (spec : Spec) (st : Store) (s : State) (te : Tagged)
    (hall : ∀ p ∈ st, p.1.2 ≠ te.2) :
    (makeAssignments spec st s).lookup te = s.lookup te :=
  foldr_applyAssignment_other_type spec s.step st s te hall

theorem foldr_applyAssignment_unrestricted (spec : Spec) (stepNum : Nat) :
    ∀ (st : Store) (s : State) (te : Tagged),
      spec.restrictionOf te.2 = none →
      (∀ p ∈ st, p.1 ≠ te) →
      (st.foldr (applyAssignment spec stepNum) s).lookup te = s.lookup te
  | [], _, _, _, _ => rfl
  | p :: st, s, te, hrest, hall => by
    simp only [List.foldr_cons]
    have htail := foldr_applyAssignment_unrestricted spec stepNum st s te hrest
      (fun q hq => hall q (List.mem_cons_of_mem p hq))
    by_cases hdom : p.1.2 = te.2
    · rcases p with ⟨te', a⟩
      dsimp only at hdom
      have hne : te' ≠ te := hall (te', a) (List.mem_cons_self ..)
      unfold applyAssignment
      dsimp only
      cases a with
      | holdsFalse _ => rw [insert_lookup_ne _ te' te _ hne]; exact htail
      | unknown => rw [erase_lookup_ne _ te' te hne]; exact htail
      | holdsTrue exp by_ =>
        dsimp only
        rw [hdom, hrest]
        dsimp only
        rw [create_lookup_ne _ te' te _ _ hne]
        exact htail
    · rw [applyAssignment_other_type spec stepNum p _ te hdom, htail]

/-- Frame preservation on unrestricted types (`Fact`, `Duty`, `Act`, `Immunity` without
`Var`/`Function`): any assignment batch that does not mention `te` leaves `s.lookup te` unchanged. -/
theorem frame_preservation_unrestricted (spec : Spec) (st : Store) (s : State) (te : Tagged)
    (hrest : spec.restrictionOf te.2 = none)
    (hall : ∀ p ∈ st, p.1 ≠ te) :
    (makeAssignments spec st s).lookup te = s.lookup te :=
  foldr_applyAssignment_unrestricted spec s.step st s te hrest hall

theorem applyAssignment_time (spec : Spec) (stepNum : Nat) (p : Tagged × Assignment) (s : State) :
    (applyAssignment spec stepNum p s).time = s.time := by
  rcases p with ⟨te, a⟩
  unfold applyAssignment
  dsimp only
  cases a with
  | holdsFalse _ => rfl
  | unknown => rfl
  | holdsTrue exp by_ =>
    dsimp only
    cases spec.restrictionOf te.2 with
    | none => rfl
    | some r =>
      cases r with
      | var => rfl
      | function =>
        dsimp only
        cases te.1 with
        | str _ => rfl
        | int _ => rfl
        | prod args =>
          cases args with
          | nil => rfl
          | cons _ r1 =>
            cases r1 with
            | nil => rfl
            | cons _ r2 =>
              cases r2 with
              | nil => rfl
              | cons _ _ => rfl

theorem foldr_applyAssignment_time (spec : Spec) (stepNum : Nat) :
    ∀ (st : Store) (s : State), (st.foldr (applyAssignment spec stepNum) s).time = s.time
  | [], _ => rfl
  | p :: st, s => by
    simp only [List.foldr_cons]
    rw [applyAssignment_time, foldr_applyAssignment_time spec stepNum st s]

theorem makeAssignments_time (spec : Spec) (st : Store) (s : State) :
    (makeAssignments spec st s).time = s.time :=
  foldr_applyAssignment_time spec s.step st s

end State

/-! ### Soundness, completeness, determinism, and clock monotonicity of `runPhrase` -/

theorem declClock_sound (spec : Spec) (specIdx : Spec.SpecIndex) (s : State) (cp : CPhrase) :
    DeclClock spec specIdx s cp (Interp.evalClockStep spec specIdx s cp) := by
  cases cp with
  | tick => exact .tick
  | setTime t =>
    simp only [Interp.evalClockStep]
    cases hr : (M.eval M.fuel t).run (Ctx.ofIdx spec specIdx s) [] with
    | error e => exact .setTimeEvalErr t e hr
    | ok vs =>
      cases vs with
      | nil => exact .setTimeBadShape t [] hr (fun _ h => nomatch h)
      | cons v rest =>
        cases v with
        | bool _ => exact .setTimeBadShape t _ hr (fun _ h => by injection h with h1; cases h1)
        | str _ => exact .setTimeBadShape t _ hr (fun _ h => by injection h with h1; cases h1)
        | tagged _ => exact .setTimeBadShape t _ hr (fun _ h => by injection h with h1; cases h1)
        | int t' =>
          cases rest with
          | cons _ _ => exact .setTimeBadShape t _ hr (fun _ h => by injection h with _ h2; cases h2)
          | nil =>
            dsimp only
            by_cases hlt : t' < s.time
            · rw [if_pos hlt]; exact .setTimeBackwards t t' hr hlt
            · rw [if_neg hlt]; exact .setTimeOk t t' hr (by omega)
  | trigger _ _ | create _ _ | terminate _ _ | obfuscate _ _ | query _ | instQuery _ _ _
  | onlyDecls _ | par _ | scenario _ _ | expect _ _ _ _ | why _ _
  | submitEvidence _ _ _ _ | retractEvidence _ _ _ =>
    exact .nonClock _ (fun h => nomatch h) (fun _ h => nomatch h)

theorem declClock_complete {spec : Spec} {specIdx : Spec.SpecIndex} {s : State}
    {cp : CPhrase} {res : Except RuntimeError (Option Int)}
    (h : DeclClock spec specIdx s cp res) :
    Interp.evalClockStep spec specIdx s cp = res := by
  cases h with
  | tick => rfl
  | setTimeOk t t' hr hle =>
    simp only [Interp.evalClockStep, hr, Int.not_lt.mpr hle, ↓reduceIte]
  | setTimeBackwards t t' hr hlt =>
    simp only [Interp.evalClockStep, hr, hlt, ↓reduceIte]
  | setTimeEvalErr t e hr =>
    simp only [Interp.evalClockStep, hr]
  | setTimeBadShape t vs hr hshape =>
    cases vs with
    | nil => simp only [Interp.evalClockStep, hr]
    | cons v rest =>
      cases v with
      | bool _ | str _ | tagged _ => simp only [Interp.evalClockStep, hr]
      | int t' =>
        cases rest with
        | nil => exact absurd rfl (hshape t')
        | cons _ _ => simp only [Interp.evalClockStep, hr]
  | nonClock cp hnt hns =>
    cases cp with
    | tick => exact absurd rfl hnt
    | setTime t => exact absurd rfl (hns t)
    | _ => rfl

theorem declClock_monotone {spec : Spec} {specIdx : Spec.SpecIndex} {s : State}
    {cp : CPhrase} {t' : Int}
    (h : DeclClock spec specIdx s cp (.ok (some t'))) :
    s.time ≤ t' := by
  cases h with
  | tick => omega
  | setTimeOk _ _ _ hle => exact hle

/-- Live evaluator soundness (`Law 9`, `G1.4`): every transition produced by `runPhrase`
satisfies `DeclPhraseStep`. -/
theorem evalPhrase_sound (cfg : Config) (p : Phrase) :
    DeclPhraseStep cfg p (runPhrase cfg p).1 (runPhrase cfg p).2 := by
  unfold runPhrase
  cases hres : resolvePhrase cfg.spec p with
  | error ds =>
    dsimp only
    exact .resolveError ds hres
  | ok triple =>
    rcases triple with ⟨spec', cp, ws⟩
    dsimp only
    cases hstr : (if p.hasDecls then Stratify.strata spec' else .ok cfg.strata) with
    | error cycle =>
      dsimp only
      by_cases hdecl : p.hasDecls = true
      · rw [if_pos hdecl] at hstr
        exact .stratifyError spec' cp ws cycle hres hdecl hstr
      · have hdeclF : p.hasDecls = false := Bool.eq_false_iff.mpr hdecl
        rw [hdeclF] at hstr
        cases hstr
    | ok strata =>
      dsimp only
      have hclk : DeclClock spec' spec'.buildIndex cfg.state cp
          (Interp.evalClockStep spec' spec'.buildIndex cfg.state cp) :=
        declClock_sound spec' spec'.buildIndex cfg.state cp
      cases hce : Interp.evalClockStep spec' spec'.buildIndex cfg.state cp with
      | error e =>
        rw [hce] at hclk
        dsimp only
        exact .clockError spec' cp ws strata e hres hstr hclk
      | ok newTime =>
        rw [hce] at hclk
        cases newTime with
        | some t =>
          dsimp only
          rcases hsem : Interp.semPhrase spec' spec'.buildIndex { cfg.state with time := t, step := cfg.state.step + 1 } 1000 cp with ⟨store?, outs⟩
          cases store? with
          | none =>
            exact .semError spec' cp ws strata (some t) _ outs hres hstr hclk rfl hsem
          | some store =>
            dsimp only
            have hpureF : (!p.hasDecls && (some t).isNone && store.isEmpty) = false := by simp
            simp only [hpureF, Bool.false_eq_true, ↓reduceIte]
            have hmut' : p.hasDecls = true ∨ (some t).isSome = true ∨ store ≠ [] := Or.inr (Or.inl rfl)
            rcases hnc : Interp.newContext cfg spec' spec'.buildIndex strata
              (State.makeAssignments spec' store { cfg.state with time := t, step := cfg.state.step + 1 }) with ⟨cfg'?, outs2⟩
            cases cfg'? with
            | none =>
              exact .mutatingError spec' cp ws strata (some t) _ store outs outs2
                hres hstr hclk hmut' rfl hsem hnc
            | some cfg' =>
              exact .mutatingOk cfg' spec' cp ws strata (some t) _ store outs outs2
                hres hstr hclk hmut' rfl hsem hnc
        | none =>
          dsimp only
          rcases hsem : Interp.semPhrase spec' spec'.buildIndex { cfg.state with step := cfg.state.step + 1 } 1000 cp with ⟨store?, outs⟩
          cases store? with
          | none =>
            exact .semError spec' cp ws strata none _ outs hres hstr hclk rfl hsem
          | some store =>
            dsimp only
            by_cases hpure : (!p.hasDecls && (none : Option Int).isNone && store.isEmpty) = true
            · rw [if_pos hpure]
              simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_none, List.isEmpty_iff, and_true] at hpure
              rcases hpure with ⟨hdeclF, hstoreE⟩
              subst hstoreE
              cases hinv : Interp.checkInvariants spec' spec'.buildIndex { cfg.state with step := cfg.state.step + 1 } with
              | error e =>
                exact .pureReadError spec' cp ws strata _ outs e hres hstr hclk hdeclF rfl hsem hinv
              | ok invViol =>
                exact .pureReadOk spec' cp ws strata _ outs invViol hres hstr hclk hdeclF rfl hsem hinv
            · rw [if_neg hpure]
              have hmut' : p.hasDecls = true ∨ (none : Option Int).isSome = true ∨ store ≠ [] := by
                cases hd : p.hasDecls
                · cases store with
                  | nil => simp [hd] at hpure
                  | cons _ _ => right; right; intro h; cases h
                · left; rfl
              rcases hnc : Interp.newContext cfg spec' spec'.buildIndex strata
                (State.makeAssignments spec' store { cfg.state with step := cfg.state.step + 1 }) with ⟨cfg'?, outs2⟩
              cases cfg'? with
              | none =>
                exact .mutatingError spec' cp ws strata none _ store outs outs2
                  hres hstr hclk hmut' rfl hsem hnc
              | some cfg' =>
                exact .mutatingOk cfg' spec' cp ws strata none _ store outs outs2
                  hres hstr hclk hmut' rfl hsem hnc

/-- Live evaluator completeness (`Law 9`, `G1.4`): every valid `DeclPhraseStep` derivation
is computed identically by `runPhrase`. -/
theorem evalPhrase_complete {cfg cfg' : Config} {p : Phrase} {outsTotal : List Output}
    (h : DeclPhraseStep cfg p cfg' outsTotal) :
    runPhrase cfg p = (cfg', outsTotal) := by
  unfold runPhrase
  cases h with
  | resolveError ds hres =>
    rw [hres]
  | stratifyError spec' cp ws cycle hres hdecl hstr =>
    rw [hres]; dsimp only
    rw [if_pos hdecl, hstr]
  | clockError spec' cp ws strata e hres hstr hclk =>
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]
  | semError spec' cp ws strata newTime state0 outs hres hstr hclk hst0 hsem =>
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]
    cases newTime <;> (dsimp only at hst0 ⊢; subst hst0; rw [hsem])
  | pureReadError spec' cp ws strata state0 outs e hres hstr hclk hdeclF hst0 hsem hinv =>
    subst hst0
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]; dsimp only
    rw [hsem]; dsimp only
    have hpure : (!p.hasDecls && (none : Option Int).isNone && ([] : Store).isEmpty) = true := by
      simp [hdeclF]
    rw [if_pos hpure, hinv]
  | pureReadOk spec' cp ws strata state0 outs invViol hres hstr hclk hdeclF hst0 hsem hinv =>
    subst hst0
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]; dsimp only
    rw [hsem]; dsimp only
    have hpure : (!p.hasDecls && (none : Option Int).isNone && ([] : Store).isEmpty) = true := by
      simp [hdeclF]
    rw [if_pos hpure, hinv]
  | mutatingError spec' cp ws strata newTime state0 store outs outs2 hres hstr hclk hmut hst0 hsem hnc =>
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]
    have hpureF : (!p.hasDecls && newTime.isNone && store.isEmpty) = false := by
      rcases hmut with hd | ht | hs
      · simp [hd]
      · cases newTime <;> simp at ht ⊢
      · cases store with
        | nil => exact absurd rfl hs
        | cons _ _ => simp
    cases newTime <;> (dsimp only at hst0 hpureF ⊢; subst hst0; rw [hsem]; simp only [hpureF, Bool.false_eq_true, ↓reduceIte]; rw [hnc])
  | mutatingOk cfg' spec' cp ws strata newTime state0 store outs outs2 hres hstr hclk hmut hst0 hsem hnc =>
    rw [hres]; dsimp only
    rw [hstr]; dsimp only
    rw [declClock_complete hclk]
    have hpureF : (!p.hasDecls && newTime.isNone && store.isEmpty) = false := by
      rcases hmut with hd | ht | hs
      · simp [hd]
      · cases newTime <;> simp at ht ⊢
      · cases store with
        | nil => exact absurd rfl hs
        | cons _ _ => simp
    cases newTime <;> (dsimp only at hst0 hpureF ⊢; subst hst0; rw [hsem]; simp only [hpureF, Bool.false_eq_true, ↓reduceIte]; rw [hnc])

/-- Single-step replay determinism (`docs/rfc.md` §3.4): identical configuration and phrase
yield identical post-configuration and outputs. -/
theorem replay_deterministic {cfg cfg₁ cfg₂ : Config} {p : Phrase} {outs₁ outs₂ : List Output}
    (h₁ : DeclPhraseStep cfg p cfg₁ outs₁)
    (h₂ : DeclPhraseStep cfg p cfg₂ outs₂) :
    cfg₁ = cfg₂ ∧ outs₁ = outs₂ := by
  have e₁ := evalPhrase_complete h₁
  have e₂ := evalPhrase_complete h₂
  rw [e₁] at e₂
  injection e₂ with hc ho
  exact ⟨hc, ho⟩

/-- Multi-step trace replay determinism (`docs/rfc.md` §3.4). -/
theorem replay_trace_deterministic :
    ∀ {ps : List Phrase} {cfg cfg₁ cfg₂ : Config} {os₁ os₂ : List (List Output)},
      DeclTraceStep cfg ps cfg₁ os₁ →
      DeclTraceStep cfg ps cfg₂ os₂ →
      cfg₁ = cfg₂ ∧ os₁ = os₂
  | [], _, _, _, _, _, .nil _, .nil _ => ⟨rfl, rfl⟩
  | _ :: _, _, _, _, _, _, .cons s₁ t₁, .cons s₂ t₂ => by
    obtain ⟨hc, ho⟩ := replay_deterministic s₁ s₂
    subst hc ho
    obtain ⟨hc', hos⟩ := replay_trace_deterministic t₁ t₂
    exact ⟨hc', congrArg _ hos⟩

namespace Saturate

theorem deriveAll_time (prev : List (Tagged × Info)) :
    ∀ (tes : List Tagged) (s : State), (State.deriveAll prev s tes).1.time = s.time
  | [], _ => rfl
  | te :: tes, s => by
    simp only [State.deriveAll]
    rcases h1 : s.derive (State.stampFrom prev s.time te) te with ⟨s1, _⟩
    have ht1 : s1.time = s.time := by
      have := derive_time s (State.stampFrom prev s.time te) te
      rw [h1] at this; exact this
    rcases h2 : State.deriveAll prev s1 tes with ⟨s2, _⟩
    have ht2 := deriveAll_time prev tes s1
    rw [h2] at ht2
    exact ht2.trans ht1

theorem passType_time (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State) (ch : Bool),
      passType spec specIdx prev d tspec cs s = .ok (s2, ch) → s2.time = s.time
  | [], s, s2, _, hp => by
    simp only [passType, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]
  | c :: cs, s, s2, ch, hp => by
    simp only [passType] at hp
    split at hp
    · cases hp
    · next ress _ =>
      rcases h1 : State.deriveAll prev s ress.flatten with ⟨s1, ch1⟩
      rw [h1] at hp
      have ht1 : s1.time = s.time := by
        have := deriveAll_time prev ress.flatten s
        rw [h1] at this; exact this
      split at hp
      · cases hp
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp
        rw [← hp.1, passType_time spec specIdx prev d tspec cs s1 s2' ch2 h2, ht1]

theorem pass_time (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State) (ch : Bool),
      pass spec specIdx prev types s = .ok (s2, ch) → s2.time = s.time
  | [], s, s2, _, hp => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]
  | d :: ds, s, s2, ch, hp => by
    unfold pass at hp
    cases hlook : (specIdx.lookup d).map (·.1) with
    | none =>
      rw [hlook] at hp; dsimp only at hp
      exact pass_time spec specIdx prev ds s s2 ch hp
    | some tspec =>
      rw [hlook] at hp; dsimp only at hp
      split at hp
      · cases hp
      · next s1 ch1 h1 =>
        split at hp
        · cases hp
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          rw [← hp.1, pass_time spec specIdx prev ds s1 s2' ch2 h2,
              passType_time spec specIdx prev d tspec tspec.derivation s s1 ch1 h1]

theorem saturateStratum_time (spec : Spec) (specIdx : Spec.SpecIndex) (prev : List (Tagged × Info))
    (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State),
      saturateStratum spec specIdx prev types fuel s = .ok s' → s'.time = s.time
  | 0, _, _, hs => by simp [saturateStratum] at hs
  | fuel + 1, s, s', hs => by
    simp only [saturateStratum] at hs
    split at hs
    · cases hs
    · next s1 changed heq =>
      have ht1 := pass_time spec specIdx prev types s s1 changed heq
      split at hs
      · rw [saturateStratum_time spec specIdx prev types fuel s1 s' hs, ht1]
      · simp only [Except.ok.injEq] at hs; rw [← hs, ht1]

theorem rebaseAndSatWithIdx_time (spec : Spec) (specIdx : Spec.SpecIndex)
    (strata : List (List DomId)) (s s' : State)
    (h : rebaseAndSatWithIdx spec specIdx strata s = .ok s') :
    s'.time = s.time := by
  unfold rebaseAndSatWithIdx at h
  have hfold : ∀ (layers : List (List DomId)) (st st' : State),
      layers.foldlM (fun acc layer => saturateStratum spec specIdx s.derivedFacts layer 100000 acc) st = .ok st' →
      st'.time = st.time := by
    intro layers
    induction layers with
    | nil =>
      intro st st' hf
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hf
      rw [← hf]
    | cons layer rest ih =>
      intro st st' hf
      simp only [List.foldlM, bind, Except.bind] at hf
      split at hf
      · cases hf
      · next st1 h1 =>
        rw [ih st1 st' hf, saturateStratum_time spec specIdx s.derivedFacts layer 100000 st st1 h1]
  exact hfold strata s.rebase s' h

end Saturate

theorem extractAmendCommits_time (s : State) :
    (Interp.extractAmendCommits s).2.time = s.time := by
  unfold Interp.extractAmendCommits
  dsimp only
  split <;> rfl

theorem newContextAfterAmend_time {cfg cfg' : Config} {effSpec : Spec} {effSpecIdx : Spec.SpecIndex}
    {effStrata : List (List DomId)} {nextVer : Nat} {s1 : State} {outs : List Output}
    (h : Interp.newContextAfterAmend cfg effSpec effSpecIdx effStrata nextVer s1 = (some cfg', outs)) :
    cfg'.state.time = s1.time := by
  unfold Interp.newContextAfterAmend at h
  cases hrs : Saturate.rebaseAndSatWithIdx effSpec effSpecIdx effStrata s1 with
  | error _ => rw [hrs] at h; cases h
  | ok state' =>
    rw [hrs] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Prod.mk.injEq, Option.some.injEq] at h
        rw [← h.1]
        exact Saturate.rebaseAndSatWithIdx_time effSpec effSpecIdx effStrata s1 state' hrs

theorem newContext_time {cfg cfg' : Config} {spec : Spec} {specIdx : Spec.SpecIndex}
    {strata : List (List DomId)} {state1 : State} {outs : List Output}
    (h : Interp.newContext cfg spec specIdx strata state1 = (some cfg', outs)) :
    cfg'.state.time = state1.time := by
  unfold Interp.newContext at h
  have hClean := extractAmendCommits_time state1
  rcases hEx : Interp.extractAmendCommits state1 with ⟨amCommits, state1Clean⟩
  rw [hEx] at h hClean
  dsimp only at h hClean
  by_cases hemp : amCommits.isEmpty = true
  · rw [if_pos hemp] at h
    rw [newContextAfterAmend_time h, hClean]
  · rw [if_neg hemp] at h
    rw [newContextAfterAmend_time h, hClean]

/-- Clock monotonicity (`009.1`): no transition ever moves `state.time` backwards. -/
theorem clock_never_decreases {cfg cfg' : Config} {p : Phrase} {outs : List Output}
    (h : DeclPhraseStep cfg p cfg' outs) :
    cfg.state.time ≤ cfg'.state.time := by
  cases h with
  | resolveError _ _ => exact Int.le_refl _
  | stratifyError _ _ _ _ _ _ _ => exact Int.le_refl _
  | clockError _ _ _ _ _ _ _ _ => exact Int.le_refl _
  | semError _ _ _ _ _ _ _ _ _ _ _ _ => exact Int.le_refl _
  | pureReadError _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Int.le_refl _
  | pureReadOk _ _ _ _ state0 _ _ _ _ _ _ hst0 _ _ =>
    rw [hst0]; exact Int.le_refl _
  | mutatingError _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Int.le_refl _
  | mutatingOk _ spec' _ _ strata newTime state0 store _ _ _ _ hclk _ hst0 _ hnc =>
    rw [newContext_time hnc, State.makeAssignments_time]
    cases newTime with
    | none => rw [hst0]; exact Int.le_refl _
    | some t' =>
      rw [hst0]
      exact declClock_monotone hclk

/-- Idempotent fast-path for an already-converged stratum (`G1.5`): when `pass` reports
no change (`changed = false`), `saturateStratum` returns the identical state in one pass. -/
theorem saturateStratum_idempotent (spec : Spec) (specIdx : Spec.SpecIndex)
    (prev : List (Tagged × Info)) (types : List DomId) (fuel : Nat) (s : State)
    (hp : Saturate.pass spec specIdx prev types s = .ok (s, false)) :
    Saturate.saturateStratum spec specIdx prev types (fuel + 1) s = .ok s := by
  simp [Saturate.saturateStratum, hp]

#print axioms evalPhrase_sound
#print axioms evalPhrase_complete
#print axioms replay_deterministic
#print axioms replay_trace_deterministic
#print axioms clock_never_decreases
#print axioms expiry_half_open_boundary
#print axioms State.frame_preservation_other_type
#print axioms State.frame_preservation_unrestricted
#print axioms Saturate.saturateStratum_fixpoint
#print axioms Saturate.saturateStratum_closed
#print axioms Saturate.saturateStratum_least_prefixpoint
#print axioms Saturate.rebaseAndSat_assigned
#print axioms State.buildIndex_lookup_eq
#print axioms State.deriveAll_unchanged
#print axioms Store.create_beats_terminate
#print axioms isViolated_of_holds
#print axioms Elem.beq_iff

end Charter
