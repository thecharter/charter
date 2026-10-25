import Charter.Eval.Interpreter

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

theorem passType_unchanged (spec : Spec) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State),
      passType spec prev d tspec cs s = .ok (s2, false) → s2 = s
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
        have e2 : s2' = s1 := passType_unchanged spec prev d tspec cs s1 s2' (by rw [h2, hch2])
        rw [← hs, e2, e1]

theorem pass_unchanged (spec : Spec) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State), pass spec prev types s = .ok (s2, false) → s2 = s
  | [], s, s2, h => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | d :: ds, s, s2, h => by
    simp only [pass] at h
    split at h
    · exact pass_unchanged spec prev ds s s2 h
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
          have e1 : s1 = s := passType_unchanged spec prev d tspec tspec.derivation s s1 (by rw [h1, hch])
          have e2 : s2' = s1 := pass_unchanged spec prev ds s1 s2' (by rw [h2, hch2])
          rw [← hs, e2, e1]

/-- 004.5: the state `saturateStratum` returns is a fixpoint of the stratum's
derivation step: one more pass derives nothing. -/
theorem saturateStratum_fixpoint (spec : Spec) (prev : List (Tagged × Info)) (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State),
      saturateStratum spec prev types fuel s = .ok s' → pass spec prev types s' = .ok (s', false)
  | 0, _, _, h => by simp [saturateStratum] at h
  | fuel + 1, s, s', h => by
    simp only [saturateStratum] at h
    split at h
    · cases h
    · next s1 changed heq =>
      split at h
      · exact saturateStratum_fixpoint spec prev types fuel s1 s' h
      · next hnot =>
        simp only [Except.ok.injEq] at h
        have hc : changed = false := by cases changed <;> simp_all
        rw [hc] at heq
        have e : s1 = s := pass_unchanged spec prev types s s1 heq
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

theorem passType_lookup (spec : Spec) (prev : List (Tagged × Info)) (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State) (b : Bool) (te : Tagged) (i : Info),
      s.lookup te = some i → passType spec prev d tspec cs s = .ok (s2, b) → s2.lookup te = some i
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
        exact passType_lookup spec prev d tspec cs s1 s2' ch2 te i hs1 h2

theorem pass_lookup (spec : Spec) (prev : List (Tagged × Info)) :
    ∀ (types : List DomId) (s s2 : State) (b : Bool) (te : Tagged) (i : Info),
      s.lookup te = some i → pass spec prev types s = .ok (s2, b) → s2.lookup te = some i
  | [], s, s2, b, te, i, h, hp => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]; exact h
  | d :: ds, s, s2, b, te, i, h, hp => by
    simp only [pass] at hp
    split at hp
    · exact pass_lookup spec prev ds s s2 b te i h hp
    · next tspec _ =>
      split at hp
      · cases hp
      · next s1 ch h1 =>
        have hs1 : s1.lookup te = some i :=
          passType_lookup spec prev d tspec tspec.derivation s s1 ch te i h h1
        split at hp
        · cases hp
        · next s2' ch2 h2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          rw [← hp.1]
          exact pass_lookup spec prev ds s1 s2' ch2 te i hs1 h2

theorem saturateStratum_lookup (spec : Spec) (prev : List (Tagged × Info)) (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State) (te : Tagged) (i : Info),
      s.lookup te = some i → saturateStratum spec prev types fuel s = .ok s' → s'.lookup te = some i
  | 0, _, _, _, _, _, h => by simp [saturateStratum] at h
  | fuel + 1, s, s', te, i, h, hs => by
    simp only [saturateStratum] at hs
    split at hs
    · cases hs
    · next s1 changed heq =>
      have hs1 : s1.lookup te = some i := pass_lookup spec prev types s s1 changed te i h heq
      split at hs
      · exact saturateStratum_lookup spec prev types fuel s1 s' te i hs1 hs
      · simp only [Except.ok.injEq] at hs; rw [← hs]; exact hs1

theorem foldl_saturate_lookup (spec : Spec) (prev : List (Tagged × Info)) :
    ∀ (strata : List (List DomId)) (s s' : State) (te : Tagged) (i : Info),
      s.lookup te = some i →
      strata.foldlM (fun s layer => saturateStratum spec prev layer 100000 s) s = .ok s' →
      s'.lookup te = some i
  | [], s, s', te, i, h, hf => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hf
    rw [← hf]; exact h
  | layer :: rest, s, s', te, i, h, hf => by
    simp only [List.foldlM, bind, Except.bind] at hf
    split at hf
    · cases hf
    · next s1 h1 =>
      exact foldl_saturate_lookup spec prev rest s1 s' te i
        (saturateStratum_lookup spec prev layer 100000 s s1 te i h h1) hf

/-- 004.3, in full: an assigned fact is exactly what the state holds after saturation,
with its stamp, expiry and origin. -/
theorem rebaseAndSat_assigned (spec : Spec) (strata : List (List DomId)) (s s' : State) (te : Tagged) (i : Info)
    (h : s.lookup te = some i) (hi : i.fromSat = false) (hs : rebaseAndSat spec strata s = .ok s') :
    s'.lookup te = some i :=
  foldl_saturate_lookup spec s.derivedFacts strata s.rebase s' te i (State.rebase_lookup s te i h hi) hs

end Saturate

/-! ## 006.2 and 006.5: the report and the query agree

`Violated(d(…))` (the query, 006.2) and the report after a phrase (006.5) both go through
`isViolated`; for an instance that holds, `isViolated` is the violation condition itself. -/

namespace M

theorem run_bind_single {α β} (m : M α) (f : α → M β) (c : Ctx) (s : Subs) (a : α)
    (h : m.run c s = .ok [a]) : (m >>= f).run c s = (f a).run c s := by
  show (do let as ← m.run c s; as.foldlM (fun acc a => do let bs ← (f a).run c s; pure (acc ++ bs)) []) = (f a).run c s
  rw [h]
  simp only [List.foldlM, bind, Except.bind, pure, Except.pure]
  rcases hf : (f a).run c s with e | bs
  · rfl
  · simp

end M

/-- A duty instance that holds is violated exactly when its violation condition holds. -/
theorem isViolated_of_holds (fuel : Nat) (te : Tagged) (c : Ctx) (subs : Subs)
    (h : (M.isHolds fuel te).run c subs = .ok [true]) :
    (M.isViolated (fuel + 1) te).run c subs =
      (M.evalViolationCondition fuel te (c.spec.findViolationCond te.2)).run c subs := by
  show ((do if !(← M.isHolds fuel te) then pure false else M.evalViolationCondition fuel te ((← M.getSpec).findViolationCond te.2)) : M Bool).run c subs = _
  rw [M.run_bind_single _ _ c subs true h]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [M.run_bind_single _ _ c subs c.spec rfl]

#print axioms Saturate.saturateStratum_fixpoint
#print axioms Saturate.rebaseAndSat_assigned
#print axioms State.deriveAll_unchanged
#print axioms Store.create_beats_terminate
#print axioms isViolated_of_holds
#print axioms Elem.beq_iff

end Charter
