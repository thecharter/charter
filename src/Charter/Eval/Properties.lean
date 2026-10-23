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

Each theorem names the spec statement it discharges.
-/

namespace Charter

/-! ## 005.3 Create beats terminate -/

namespace Store

theorem combine_true_left (a : Assignment) : union.combine .holdsTrue a = .holdsTrue := by
  cases a <;> rfl

theorem combine_true_right (a : Assignment) : union.combine a .holdsTrue = .holdsTrue := by
  cases a <;> rfl

/-- 005.3: within one step, creating an instance beats terminating it, whichever
side of the merge it comes from; terminating beats forgetting. -/
theorem create_beats_terminate :
    union.combine .holdsTrue .holdsFalse = .holdsTrue ∧ union.combine .holdsFalse .holdsTrue = .holdsTrue ∧
    union.combine .holdsFalse .unknown = .holdsFalse ∧ union.combine .unknown .holdsFalse = .holdsFalse :=
  ⟨rfl, rfl, rfl, rfl⟩

end Store

/-! ## 004.3 Assignment beats derivation -/

namespace State

/-- Deriving an instance that has an assignment changes nothing. -/
theorem derive_assigned (s : State) (te : Tagged) (i : Info) (h : s.lookup te = some i) :
    s.derive te = (s, false) := by
  unfold derive; rw [h]

/-- A derivation step that reports no change made none. -/
theorem derive_unchanged (s : State) (te : Tagged) (s1 : State) (h : s.derive te = (s1, false)) :
    s1 = s := by
  unfold derive at h
  cases hl : s.lookup te <;> rw [hl] at h <;> simp only [Prod.mk.injEq] at h
  · exact absurd h.2 (by decide)
  · exact h.1.symm

theorem deriveAll_unchanged : ∀ (tes : List Tagged) (s s2 : State),
    deriveAll s tes = (s2, false) → s2 = s
  | [], _, _, h => by
    simp only [deriveAll, Prod.mk.injEq] at h
    exact h.1.symm
  | te :: tes, s, s2, h => by
    simp only [deriveAll] at h
    rcases h1 : s.derive te with ⟨s1, ch⟩
    rw [h1] at h
    rcases h2 : deriveAll s1 tes with ⟨s2', ch2⟩
    rw [h2] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hs, hb⟩ := h
    have hch : ch = false := by cases ch <;> simp_all
    have hch2 : ch2 = false := by cases ch2 <;> simp_all
    have e1 : s1 = s := derive_unchanged s te s1 (by rw [h1, hch])
    have e2 : s2' = s1 := deriveAll_unchanged tes s1 s2' (by rw [h2, hch2])
    rw [← hs, e2, e1]

end State

/-! ## 004.5 Saturation reaches a fixpoint -/

namespace Saturate

theorem passType_unchanged (spec : Spec) (d : DomId) (tspec : TypeSpec) :
    ∀ (cs : List Derivation) (s s2 : State),
      passType spec d tspec cs s = .ok (s2, false) → s2 = s
  | [], s, s2, h => by
    simp only [passType, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | c :: cs, s, s2, h => by
    simp only [passType] at h
    split at h
    · cases h
    · next ress _ =>
      rcases h1 : s.deriveAll ress.flatten with ⟨s1, ch⟩
      rw [h1] at h
      split at h
      · cases h
      · next s2' ch2 h2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hb⟩ := h
        have hch : ch = false := by cases ch <;> simp_all
        have hch2 : ch2 = false := by cases ch2 <;> simp_all
        have e1 : s1 = s := State.deriveAll_unchanged ress.flatten s s1 (by rw [h1, hch])
        have e2 : s2' = s1 := passType_unchanged spec d tspec cs s1 s2' (by rw [h2, hch2])
        rw [← hs, e2, e1]

theorem pass_unchanged (spec : Spec) :
    ∀ (types : List DomId) (s s2 : State), pass spec types s = .ok (s2, false) → s2 = s
  | [], s, s2, h => by
    simp only [pass, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | d :: ds, s, s2, h => by
    simp only [pass] at h
    split at h
    · exact pass_unchanged spec ds s s2 h
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
          have e1 : s1 = s := passType_unchanged spec d tspec tspec.derivation s s1 (by rw [h1, hch])
          have e2 : s2' = s1 := pass_unchanged spec ds s1 s2' (by rw [h2, hch2])
          rw [← hs, e2, e1]

/-- 004.5: the state `saturateStratum` returns is a fixpoint of the stratum's
derivation step: one more pass derives nothing. -/
theorem saturateStratum_fixpoint (spec : Spec) (types : List DomId) :
    ∀ (fuel : Nat) (s s' : State),
      saturateStratum spec types fuel s = .ok s' → pass spec types s' = .ok (s', false)
  | 0, _, _, h => by simp [saturateStratum] at h
  | fuel + 1, s, s', h => by
    simp only [saturateStratum] at h
    split at h
    · cases h
    · next s1 changed heq =>
      split at h
      · exact saturateStratum_fixpoint spec types fuel s1 s' h
      · next hnot =>
        simp only [Except.ok.injEq] at h
        have hc : changed = false := by cases changed <;> simp_all
        rw [hc] at heq
        have e : s1 = s := pass_unchanged spec types s s1 heq
        subst e
        subst h
        exact heq

end Saturate

#print axioms Saturate.saturateStratum_fixpoint
#print axioms State.deriveAll_unchanged
#print axioms Store.create_beats_terminate

end Charter
