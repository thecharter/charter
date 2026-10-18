import Charter.Core.Semantics

/-!
# Substrate Assumption 2 — Sybil-Resistant Verifiable Sortition

Reference implementation and kernel-checked proofs for the second substrate
capability of the Protocol of Sovereign Agency:
- Filtering candidate arbiters by independence from the dispute
  (`relatedToDispute = false`) and minimum fidelity bond (`bond ≥ minBond`),
- Bounding selected arbitration and appellate panels by `panelSize`,
- Enforcing the two-thirds supermajority threshold (`yesVotes * 3 ≥ totalSeats * 2`
  with `totalSeats > 0`) so any minority coalition strictly below two-thirds of
  panel seats is blocked.
-/

namespace Charter.Substrate

/-- A candidate arbiter in the sortition pool. -/
structure ArbiterCandidate where
  arbiterId        : Nat
  bond             : Nat
  sybilClusterId   : Nat
  relatedToDispute : Bool
  deriving DecidableEq, Repr

/-- An arbiter candidate is eligible iff independent of the dispute and bonded
at or above `minBond`. -/
def eligibleCandidate (minBond : Nat) (c : ArbiterCandidate) : Bool :=
  !c.relatedToDispute && (c.bond >= minBond)

/-- Filter a candidate pool to those satisfying `eligibleCandidate minBond`. -/
def filterEligibleCandidates (minBond : Nat) (cs : List ArbiterCandidate) :
    List ArbiterCandidate :=
  cs.filter (eligibleCandidate minBond)

/-- Select up to `panelSize` eligible, independent, bonded arbiters. -/
def selectSortitionPanel (minBond panelSize : Nat) (cs : List ArbiterCandidate) :
    List ArbiterCandidate :=
  (filterEligibleCandidates minBond cs).take panelSize

/-- Does a vote tally meet the non-empty two-thirds supermajority threshold? -/
def supermajorityPassed (yesVotes totalSeats : Nat) : Bool :=
  totalSeats > 0 && yesVotes * 3 >= totalSeats * 2

/-- Deduplicate candidates by `sybilClusterId` so each Sybil identity cluster
can occupy at most one seat in the sortition pool. -/
def dedupSybilClusters : List ArbiterCandidate → List ArbiterCandidate
  | [] => []
  | c :: cs =>
    c :: (dedupSybilClusters cs).filter (fun x => x.sybilClusterId != c.sybilClusterId)

/-- Select up to `panelSize` eligible, independent, bonded arbiters with at most
one arbiter per `sybilClusterId`. -/
def selectSybilResistantPanel (minBond panelSize : Nat) (cs : List ArbiterCandidate) :
    List ArbiterCandidate :=
  (dedupSybilClusters (filterEligibleCandidates minBond cs)).take panelSize

/-! ## Helper Lemmas on Lists -/

private theorem mem_of_mem_take {α : Type} {n : Nat} {xs : List α} {x : α}
    (h : x ∈ xs.take n) : x ∈ xs := by
  induction xs generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp only [List.take_succ_cons, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

private theorem mem_of_mem_filter {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : x ∈ xs.filter p) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.filter_cons] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | htl
      · exact List.Mem.head tl
      · exact List.Mem.tail hd (ih htl)
    · exact List.Mem.tail hd (ih h)

private theorem prop_of_mem_filter {α : Type} {p : α → Bool} {xs : List α} {x : α}
      (h : x ∈ xs.filter p) : p x = true := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.filter_cons] at h
    split at h
    · rename_i hphd
      simp only [List.mem_cons] at h
      rcases h with rfl | htl
      · exact hphd
      · exact ih htl
    · exact ih h

private theorem mem_of_mem_dedupSybilClusters {cs : List ArbiterCandidate} {x : ArbiterCandidate}
    (h : x ∈ dedupSybilClusters cs) : x ∈ cs := by
  induction cs with
  | nil => simp [dedupSybilClusters] at h
  | cons hd tl ih =>
    simp only [dedupSybilClusters, List.mem_cons] at h ⊢
    rcases h with rfl | htl
    · exact Or.inl rfl
    · exact Or.inr (ih (mem_of_mem_filter htl))

private theorem length_take_le_bound {α : Type} (n : Nat) (xs : List α) :
    (xs.take n).length ≤ n := by
  induction xs generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.take_succ_cons, List.length_cons]
      have h := ih m
      omega

private theorem length_filter_le {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.length_cons]; omega
    · exact Nat.le_trans ih (Nat.le_succ _)

private theorem filter_comm {α : Type} (p q : α → Bool) (xs : List α) :
    (xs.filter p).filter q = (xs.filter q).filter p := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hp : p hd <;> cases hq : q hd <;> simp [hp, hq, ih]

private theorem filter_false_of_imp {α : Type} (p q : α → Bool) (xs : List α)
    (hImp : ∀ x, p x = true → q x = false) :
    (xs.filter p).filter q = [] := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    cases hp : p hd
    · exact ih
    · have hq : q hd = false := hImp hd hp
      simp [hq, ih]

private theorem length_filter_take_le {α : Type} (p : α → Bool) (n : Nat) (xs : List α) :
    ((xs.take n).filter p).length ≤ (xs.filter p).length := by
  induction xs generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.take_succ_cons, List.filter_cons]
      split
      · simp only [List.length_cons]
        have h := ih m
        omega
      · exact ih m

private theorem dedupSybilClusters_cluster_count_le_one
    (clusterId : Nat) (cs : List ArbiterCandidate) :
    ((dedupSybilClusters cs).filter (fun c => c.sybilClusterId == clusterId)).length ≤ 1 := by
  induction cs with
  | nil => simp [dedupSybilClusters]
  | cons hd tl ih =>
    simp only [dedupSybilClusters, List.filter_cons]
    cases hEq : (hd.sybilClusterId == clusterId)
    · rw [filter_comm]
      exact Nat.le_trans
        (length_filter_le (fun x => x.sybilClusterId != hd.sybilClusterId)
          ((dedupSybilClusters tl).filter (fun c => c.sybilClusterId == clusterId)))
        ih
    · have hEmpty :
        (((dedupSybilClusters tl).filter (fun x => x.sybilClusterId != hd.sybilClusterId)).filter
          (fun c => c.sybilClusterId == clusterId)) = [] := by
        apply filter_false_of_imp
        intro x hNe
        simp only [bne_iff_ne, ne_eq] at hNe
        simp only [beq_iff_eq] at hEq
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      simp [hEmpty]

/-! ## Kernel-Checked Substrate Capability 2 Theorems -/

/-- Every arbiter selected into a sortition panel is independent of the dispute
(`relatedToDispute = false`) and meets the minimum bond (`bond ≥ minBond`). -/
theorem sortition_panel_all_independent_and_bonded :
    ∀ (minBond sz : Nat) (cs : List ArbiterCandidate) (c : ArbiterCandidate),
      c ∈ selectSortitionPanel minBond sz cs →
      c.relatedToDispute = false ∧ c.bond ≥ minBond := by
  intro minBond sz cs c hMem
  have hFilt : c ∈ filterEligibleCandidates minBond cs := mem_of_mem_take hMem
  have hElig : eligibleCandidate minBond c = true := prop_of_mem_filter hFilt
  unfold eligibleCandidate at hElig
  simp only [Bool.and_eq_true, Bool.not_eq_true', ge_iff_le, decide_eq_true_eq] at hElig
  exact hElig

/-- Every selected sortition panel has size at most `sz`. -/
theorem sortition_panel_bounded_size :
    ∀ (minBond sz : Nat) (cs : List ArbiterCandidate),
      (selectSortitionPanel minBond sz cs).length ≤ sz := by
  intro minBond sz cs
  unfold selectSortitionPanel
  exact length_take_le_bound sz (filterEligibleCandidates minBond cs)

/-- Any coalition holding strictly fewer than two-thirds of total panel seats
(`yes * 3 < total * 2`) cannot pass a supermajority vote (`Adversarial Test 10`). -/
theorem sortition_supermajority_blocks_minority_coalition :
    ∀ (yes total : Nat),
      yes * 3 < total * 2 → supermajorityPassed yes total = false := by
  intro yes total hLt
  unfold supermajorityPassed
  have hNotGe : decide (yes * 3 ≥ total * 2) = false := decide_eq_false (by omega)
  simp [hNotGe]

/-- Every arbiter in `selectSybilResistantPanel` is independent and bonded, the
panel size is at most `sz`, and every `sybilClusterId` holds at most one seat. -/
theorem sortition_sybil_resistant_panel_properties
    (minBond sz clusterId : Nat) (cs : List ArbiterCandidate) :
    (∀ c ∈ selectSybilResistantPanel minBond sz cs,
      c.relatedToDispute = false ∧ c.bond ≥ minBond) ∧
    (selectSybilResistantPanel minBond sz cs).length ≤ sz ∧
    ((selectSybilResistantPanel minBond sz cs).filter
      (fun c => c.sybilClusterId == clusterId)).length ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hMem
    have hDedup := mem_of_mem_take hMem
    have hFilt := mem_of_mem_dedupSybilClusters hDedup
    have hElig : eligibleCandidate minBond c = true := prop_of_mem_filter hFilt
    unfold eligibleCandidate at hElig
    simp only [Bool.and_eq_true, Bool.not_eq_true', ge_iff_le, decide_eq_true_eq] at hElig
    exact hElig
  · unfold selectSybilResistantPanel
    exact length_take_le_bound sz (dedupSybilClusters (filterEligibleCandidates minBond cs))
  · unfold selectSybilResistantPanel
    exact Nat.le_trans
      (length_filter_take_le (fun c => c.sybilClusterId == clusterId) sz
        (dedupSybilClusters (filterEligibleCandidates minBond cs)))
      (dedupSybilClusters_cluster_count_le_one clusterId (filterEligibleCandidates minBond cs))

/-- An empty panel (`totalSeats = 0`) never passes a supermajority vote. -/
theorem sortition_empty_panel_never_passes (yes : Nat) :
    supermajorityPassed yes 0 = false := by
  rfl

/-- Combined sortition independence, boundedness, and supermajority safety theorem. -/
theorem sortition_panel_independent_and_unbiased
    (minBond sz yes total : Nat) (cs : List ArbiterCandidate) :
    (∀ c ∈ selectSortitionPanel minBond sz cs,
      c.relatedToDispute = false ∧ c.bond ≥ minBond) ∧
    (selectSortitionPanel minBond sz cs).length ≤ sz ∧
    (yes * 3 < total * 2 → supermajorityPassed yes total = false) := by
  exact ⟨sortition_panel_all_independent_and_bonded minBond sz cs,
         sortition_panel_bounded_size minBond sz cs,
         sortition_supermajority_blocks_minority_coalition yes total⟩

end Charter.Substrate

namespace Charter

export Substrate (
  ArbiterCandidate
  eligibleCandidate
  filterEligibleCandidates
  selectSortitionPanel
  supermajorityPassed
  dedupSybilClusters
  selectSybilResistantPanel
  sortition_panel_all_independent_and_bonded
  sortition_panel_bounded_size
  sortition_supermajority_blocks_minority_coalition
  sortition_sybil_resistant_panel_properties
  sortition_empty_panel_never_passes
  sortition_panel_independent_and_unbiased
)

end Charter

namespace Charter.Law3

export Charter.Substrate (
  ArbiterCandidate
  eligibleCandidate
  filterEligibleCandidates
  selectSortitionPanel
  supermajorityPassed
  dedupSybilClusters
  selectSybilResistantPanel
  sortition_panel_all_independent_and_bonded
  sortition_panel_bounded_size
  sortition_supermajority_blocks_minority_coalition
  sortition_sybil_resistant_panel_properties
  sortition_empty_panel_never_passes
  sortition_panel_independent_and_unbiased
)

end Charter.Law3
