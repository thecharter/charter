import Charter.Eval.Properties

/-!
# Charter.Verify.Reduction — Commutativity Footprints & Symmetry Canonicalization (`G2.2`)

Provides static read/write footprint analysis for ample/commuting transition pruning and
state-key canonicalization, backed by a kernel-checked commutativity proof on disjoint-type
store applications (`makeAssignments_comm_lookup_disjoint`).
-/

namespace Charter.Verify

/-- Single-owner footprint aliases from `Charter.Footprint` (`Charter.Core.Derivation`). -/
abbrev effectWriteTypes := Footprint.effectWriteTypes
abbrev actWriteTypes := Footprint.actWriteTypes
abbrev actReadTypes := Footprint.declDirectReadTypes
abbrev staticallyIndependent := Footprint.staticallyIndependent

/-! ### Disjoint-Store Commutativity Proof (`G2.2`) -/

theorem lookup_insert_self (s : State) (te : Tagged) (i : Info) :
    (s.insert te i).lookup te = some i := by
  unfold State.insert State.lookup
  have hself : (te == te) = true := (Tagged.beq_iff te te).mpr rfl
  simp [hself]

theorem find?_filter_not_self (te : Tagged) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => !(p.1 == te))).find? (·.1 == te) = none
  | [] => rfl
  | p :: rest => by
    simp only [List.filter]
    cases hp : (p.1 == te)
    · simp [hp, find?_filter_not_self te rest]
    · simp [find?_filter_not_self te rest]

theorem lookup_erase_self (s : State) (te : Tagged) :
    (s.erase te).lookup te = none := by
  unfold State.erase State.lookup
  rw [find?_filter_not_self te s.contents]
  rfl

theorem find?_map_val_transform (te : Tagged) (f : (Tagged × Info) → (Tagged × Info))
    (g : Tagged → Info → Info)
    (hf : ∀ k v, f (k, v) = (k, g k v)) :
    ∀ (xs : List (Tagged × Info)),
      ((xs.map f).find? (·.1 == te)).map (·.2) =
      ((xs.find? (·.1 == te)).map (·.2)).map (g te)
  | [] => rfl
  | (k, v) :: rest => by
    simp only [List.map_cons, hf k v, List.find?_cons]
    cases hk : (k == te)
    · exact find?_map_val_transform te f g hf rest
    · have keq : k = te := (Tagged.beq_iff k te).mp hk
      subst keq
      rfl

theorem create_congr_on_type {d : DomId} {s₁ s₂ : State}
    (ht : s₁.time = s₂.time)
    (hl : ∀ q : Tagged, q.2 = d → s₁.lookup q = s₂.lookup q)
    (te' : Tagged) (hd' : te'.2 = d) (exp : Option Int) (orig : Origin)
    (q : Tagged) (hq : q.2 = d) :
    (s₁.create te' exp orig).lookup q = (s₂.create te' exp orig).lookup q := by
  unfold State.create
  rw [hl te' hd', ht]
  by_cases heq : te' = q
  · subst heq
    rw [lookup_insert_self, lookup_insert_self]
  · rw [State.insert_lookup_ne _ te' q _ heq, State.insert_lookup_ne _ te' q _ heq, hl q hq]

theorem applyAssignment_congr_on_type (spec : Spec) (stepNum : Nat) (entry : Tagged × Assignment)
    {d : DomId} {s₁ s₂ : State}
    (ht : s₁.time = s₂.time)
    (hl : ∀ q : Tagged, q.2 = d → s₁.lookup q = s₂.lookup q) :
    ∀ (q : Tagged), q.2 = d →
      (State.applyAssignment spec stepNum entry s₁).lookup q =
      (State.applyAssignment spec stepNum entry s₂).lookup q := by
  intro q hq
  rcases entry with ⟨te', a⟩
  by_cases hdom : te'.2 = d
  · unfold State.applyAssignment
    dsimp only
    cases a with
    | holdsFalse by_ =>
      by_cases heq : te' = q
      · subst heq; rw [lookup_insert_self, lookup_insert_self, ht]
      · rw [State.insert_lookup_ne _ te' q _ heq, State.insert_lookup_ne _ te' q _ heq, hl q hq]
    | unknown =>
      by_cases heq : te' = q
      · subst heq; rw [lookup_erase_self, lookup_erase_self]
      · rw [State.erase_lookup_ne _ te' q heq, State.erase_lookup_ne _ te' q heq, hl q hq]
    | holdsTrue expiry by_ =>
      dsimp only
      cases spec.restrictionOf te'.2 with
      | none => exact create_congr_on_type ht hl te' hdom expiry _ q hq
      | some r =>
        cases r with
        | var =>
          dsimp only
          let orig := match by_ with
            | some act => Origin.byAct act stepNum
            | none => if spec.closedType te'.2 == some false then Origin.environment stepNum else Origin.asserted stepNum
          let g (t : Int) (k : Tagged) (v : Info) : Info :=
            if k.2 == te'.2 then ⟨false, false, t, none, orig⟩ else v
          let fMap (t : Int) (q : Tagged × Info) : Tagged × Info :=
            if q.1.2 == te'.2 then (q.1, ⟨false, false, t, none, orig⟩) else q
          let s₁' : State := { s₁ with contents := s₁.contents.map (fMap s₁.time) }
          let s₂' : State := { s₂ with contents := s₂.contents.map (fMap s₂.time) }
          have ht' : s₁'.time = s₂'.time := ht
          have hl' : ∀ q' : Tagged, q'.2 = d → s₁'.lookup q' = s₂'.lookup q' := by
            intro q' hq'
            unfold State.lookup
            dsimp only [s₁', s₂']
            rw [find?_map_val_transform q' (fMap s₁.time) (g s₁.time) (fun k v => by dsimp only [fMap, g]; cases (k.2 == te'.2) <;> rfl),
                find?_map_val_transform q' (fMap s₂.time) (g s₂.time) (fun k v => by dsimp only [fMap, g]; cases (k.2 == te'.2) <;> rfl)]
            change Option.map (g s₁.time q') (s₁.lookup q') = Option.map (g s₂.time q') (s₂.lookup q')
            rw [hl q' hq', ht]
          exact create_congr_on_type ht' hl' te' hdom expiry orig q hq
        | function =>
          dsimp only
          cases te'.1 with
          | str _ => exact hl q hq
          | int _ => exact hl q hq
          | prod args =>
            cases args with
            | nil => exact hl q hq
            | cons f r1 =>
              cases r1 with
              | nil => exact hl q hq
              | cons g0 r2 =>
                cases r2 with
                | cons _ _ => exact hl q hq
                | nil =>
                  dsimp only
                  let orig := match by_ with
                    | some act => Origin.byAct act stepNum
                    | none => if spec.closedType te'.2 == some false then Origin.environment stepNum else Origin.asserted stepNum
                  let gfn (t : Int) (k : Tagged) (v : Info) : Info :=
                    match k.1 with
                    | .prod [f', _] =>
                      if k.2 == te'.2 && Elem.beq f.1 f'.1 && f.2 == f'.2 then
                        ⟨false, false, t, none, orig⟩
                      else v
                    | _ => v
                  let fMapFn (t : Int) (q : Tagged × Info) : Tagged × Info :=
                    match q.1.1 with
                    | .prod [f', _] =>
                      if q.1.2 == te'.2 && Elem.beq f.1 f'.1 && f.2 == f'.2 then
                        (q.1, ⟨false, false, t, none, orig⟩)
                      else q
                    | _ => q
                  let hfEq (t : Int) : ∀ k v, fMapFn t (k, v) = (k, gfn t k v) := by
                    intro k v
                    dsimp only [fMapFn, gfn]
                    cases k.1 with
                    | str _ | int _ => rfl
                    | prod kargs =>
                      cases kargs with
                      | nil => rfl
                      | cons f' kr1 =>
                        cases kr1 with
                        | nil => rfl
                        | cons _ kr2 =>
                          cases kr2 with
                          | cons _ _ => rfl
                          | nil =>
                            dsimp only
                            cases (k.2 == te'.2 && Elem.beq f.1 f'.1 && f.2 == f'.2) <;> rfl
                  let s₁' : State := { s₁ with contents := s₁.contents.map (fMapFn s₁.time) }
                  let s₂' : State := { s₂ with contents := s₂.contents.map (fMapFn s₂.time) }
                  have ht' : s₁'.time = s₂'.time := ht
                  have hl' : ∀ q' : Tagged, q'.2 = d → s₁'.lookup q' = s₂'.lookup q' := by
                    intro q' hq'
                    unfold State.lookup
                    dsimp only [s₁', s₂']
                    rw [find?_map_val_transform q' (fMapFn s₁.time) (gfn s₁.time) (hfEq s₁.time),
                        find?_map_val_transform q' (fMapFn s₂.time) (gfn s₂.time) (hfEq s₂.time)]
                    change Option.map (gfn s₁.time q') (s₁.lookup q') = Option.map (gfn s₂.time q') (s₂.lookup q')
                    rw [hl q' hq', ht]
                  exact create_congr_on_type ht' hl' te' hdom expiry orig q hq
  · rw [State.applyAssignment_other_type spec stepNum (te', a) s₁ q (by rw [hq]; exact hdom),
        State.applyAssignment_other_type spec stepNum (te', a) s₂ q (by rw [hq]; exact hdom),
        hl q hq]

theorem foldr_applyAssignment_congr_on_type (spec : Spec) (stepNum : Nat) {d : DomId} :
    ∀ (st : Store) {s₁ s₂ : State},
      s₁.time = s₂.time →
      (∀ q : Tagged, q.2 = d → s₁.lookup q = s₂.lookup q) →
      ∀ (q : Tagged), q.2 = d →
        (st.foldr (State.applyAssignment spec stepNum) s₁).lookup q =
        (st.foldr (State.applyAssignment spec stepNum) s₂).lookup q
  | [], _, _, _, hl, q, hq => hl q hq
  | p :: st, s₁, s₂, ht, hl, q, hq => by
    simp only [List.foldr_cons]
    have ht' : (st.foldr (State.applyAssignment spec stepNum) s₁).time =
               (st.foldr (State.applyAssignment spec stepNum) s₂).time := by
      rw [State.foldr_applyAssignment_time, State.foldr_applyAssignment_time, ht]
    have hl' := foldr_applyAssignment_congr_on_type spec stepNum st ht hl
    exact applyAssignment_congr_on_type spec stepNum p ht' hl' q hq

theorem applyAssignment_step (spec : Spec) (stepNum : Nat) (p : Tagged × Assignment) (s : State) :
    (State.applyAssignment spec stepNum p s).step = s.step := by
  rcases p with ⟨te, a⟩
  unfold State.applyAssignment
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
        | str _ | int _ => rfl
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

theorem foldr_applyAssignment_step (spec : Spec) (stepNum : Nat) (st : Store) (s : State) :
    (st.foldr (State.applyAssignment spec stepNum) s).step = s.step := by
  induction st with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldr_cons, applyAssignment_step, ih]

/-- Disjoint-footprint commutativity theorem (`G2.2`): two assignment stores touching
disjoint `DomId` sets commute observationally on `State.lookup` for every instance `te`. -/
theorem makeAssignments_comm_lookup_disjoint (spec : Spec) (st₁ st₂ : Store) (s : State)
    (hdisj : ∀ p₁ ∈ st₁, ∀ p₂ ∈ st₂, p₁.1.2 ≠ p₂.1.2)
    (te : Tagged) :
    (State.makeAssignments spec st₁ (State.makeAssignments spec st₂ s)).lookup te =
    (State.makeAssignments spec st₂ (State.makeAssignments spec st₁ s)).lookup te := by
  by_cases h1 : ∃ p₁ ∈ st₁, p₁.1.2 = te.2
  · obtain ⟨p₁, hp₁, hdom₁⟩ := h1
    have hnot₂ : ∀ p₂ ∈ st₂, p₂.1.2 ≠ te.2 := by
      intro p₂ hp₂ heq
      exact hdisj p₁ hp₁ p₂ hp₂ (hdom₁.trans heq.symm)
    rw [State.frame_preservation_other_type spec st₂ _ te hnot₂]
    unfold State.makeAssignments
    rw [foldr_applyAssignment_step spec s.step st₂ s]
    apply foldr_applyAssignment_congr_on_type spec s.step st₁ (d := te.2)
    · exact State.foldr_applyAssignment_time spec s.step st₂ s
    · intro q hq
      exact State.foldr_applyAssignment_other_type spec s.step st₂ s q (fun p₂ hp₂ => by rw [hq]; exact hnot₂ p₂ hp₂)
    · rfl
  · have hnot₁ : ∀ p₁ ∈ st₁, p₁.1.2 ≠ te.2 := fun p₁ hp₁ heq => h1 ⟨p₁, hp₁, heq⟩
    rw [State.frame_preservation_other_type spec st₁ _ te hnot₁]
    by_cases h2 : ∃ p₂ ∈ st₂, p₂.1.2 = te.2
    · obtain ⟨p₂, hp₂, hdom₂⟩ := h2
      unfold State.makeAssignments
      rw [foldr_applyAssignment_step spec s.step st₁ s]
      symm
      apply foldr_applyAssignment_congr_on_type spec s.step st₂ (d := te.2)
      · exact State.foldr_applyAssignment_time spec s.step st₁ s
      · intro q hq
        exact State.foldr_applyAssignment_other_type spec s.step st₁ s q (fun p₁ hp₁ => by rw [hq]; exact hnot₁ p₁ hp₁)
      · rfl
    · have hnot₂ : ∀ p₂ ∈ st₂, p₂.1.2 ≠ te.2 := fun p₂ hp₂ heq => h2 ⟨p₂, hp₂, heq⟩
      rw [State.frame_preservation_other_type spec st₂ _ te hnot₂,
          State.frame_preservation_other_type spec st₂ _ te hnot₂,
          State.frame_preservation_other_type spec st₁ _ te hnot₁]

#print axioms makeAssignments_comm_lookup_disjoint

end Charter.Verify
