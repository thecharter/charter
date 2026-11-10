import Charter.Prove.Run

/-!
# Charter.Prove.Slice — Per-Step Specification Slicing & Zero-Axiom Framing Theorems (`#74`)

Enables `charter prove` at the scale of 700+-type institutional specifications:
1. Projects `Spec` and `State` onto the cone-of-influence slice `(readWriteDoms, coneDoms, coneStrata)`
   touched by a single phrase, so kernel work per checkpoint step scales with the active slice
   (typically 5–60 types) rather than all declared types;
2. Proves the framing theorems (`reframeState_lookup_outside`, `reframeState_lookup_inside`,
   `deriveWithIdx_outside_cone`, `deriveAllWithIdx_outside_cone`, `applyAssignment_outside_cone`,
   `makeAssignments_outside_cone`) **once**, constructively with **zero axioms** (`Law 10`:
   `#print axioms` reports `does not depend on any axioms` — no `simp`, no `propext`, no `Quot.sound`);
3. Provides `summarizeSliced` and `summarySliced` with constructive chaining lemmas (`foldl_step_sliced`,
   `foldl_phrase_sliced`, `foldl_scenario_sliced`) mirroring `Charter.Prove.Run`.
-/

namespace Charter.Prove

/-- Per-phrase slice certificate (`#74`): names the active read/write type slice and the
forward-cone derived strata (grouped into bounded batches of <= 18 strata) that require re-saturation. -/
structure StepSlice where
  useFull       : Bool := true
  isDeclSlice   : Bool := false
  resolveDoms   : List DomId := []
  readWriteDoms : List DomId := []
  declaredDoms  : List DomId := []
  updatedDoms   : List DomId := []
  coneDoms      : List DomId := []
  strataBatches : List (List (List DomId)) := []
  nextStrata    : List (List DomId) := []
  deriving Repr, Inhabited

/-- Per-scenario / end-state slice certificate for invariant checking (`#74`): pairs each
declared invariant with its own minimal read-closure domain list (~5–12 types each). -/
structure InvariantSlice where
  useFull : Bool := true
  perInv  : List (DomId × List DomId) := []
  deriving Repr, Inhabited

/-- Radix-indexed domain set (`O(1)` bucket lookup in the proof kernel, avoiding quadratic
`List.contains` `String` scans across 700-type specifications, `#74`). -/
abbrev DomSet := DomMap Unit

def DomSet.ofList (ds : List DomId) : DomSet :=
  ds.foldl (fun m d => m.insert d ()) .empty

def DomSet.has (m : DomSet) (d : DomId) : Bool :=
  (m.lookup d).isSome

/-- Restrict `s` to built-in carriers, finite enum carriers, and `doms` in `O(|s.decls|)` (`#74`). -/
def projectSpec (doms : List DomId) (s : Spec) : Spec :=
  let dset := DomSet.ofList ("int" :: "string" :: "actor" :: doms)
  let keep (d : DomId) (ts : TypeSpec) : Bool :=
    dset.has d ||
    (ts.derivation.isEmpty && match ts.domain with | .strings _ | .ints _ => true | _ => false)
  { s with
    decls := s.decls.filter (fun p => keep p.1 p.2)
    clauses := []
    scenarios := []
    temporalProperties := [] }

/-- Restrict `st.contents` to entries whose domain is in `doms` in `O(|st.contents|)` (`#74`). -/
def projectState (doms : List DomId) (st : State) : State :=
  let dset := DomSet.ofList doms
  { st with contents := st.contents.filter (fun p => dset.has p.1.2) }

/-- Remove only derived entries inside `coneDoms`, keeping derived entries outside `coneDoms` intact. -/
def rebaseCone (coneDoms : List DomId) (st : State) : State :=
  let cset := DomSet.ofList coneDoms
  { st with contents := st.contents.filter (fun p => !p.2.fromSat || !(cset.has p.1.2)) }

/-- Merge updated `slicedNext` entries inside `coneDoms` with `prevFull`'s untouched frame outside `coneDoms`. -/
def reframeState (coneDoms : List DomId) (prevFull slicedNext : State) : State :=
  let cset := DomSet.ofList coneDoms
  { contents := slicedNext.contents.filter (fun p => cset.has p.1.2) ++
                prevFull.contents.filter (fun p => !(cset.has p.1.2))
    time := slicedNext.time
    step := slicedNext.step }

/-! ## Constructive Zero-Axiom Framing Theorems (`Law 10`)
All proofs below avoid `simp`, `by_cases`, and `funext` so `#print axioms` carries `[]`. -/

private theorem dom_beq_false_of_pred_mismatch (inCone : DomId → Bool) (d1 d2 : DomId)
    (h1 : inCone d1 = true) (h2 : inCone d2 = false) :
    (d1 == d2) = false := by
  cases heq : (d1 == d2)
  · rfl
  · have hd : d1 = d2 := beq_iff_eq.mp heq
    rw [hd] at h1
    rw [h1] at h2
    cases h2

private theorem tagged_beq_false_of_dom_ne (a b : Tagged) (hne : (a.2 == b.2) = false) :
    (a == b) = false := by
  show (a.2 == b.2 && Elem.beq a.1 b.1) = false
  rw [hne]
  rfl

private theorem find?_append_none {α : Type} (p : α → Bool) :
    ∀ (xs ys : List α), xs.find? p = none → (xs ++ ys).find? p = ys.find? p
  | [], _, _ => rfl
  | x :: xs, ys, h => by
    rw [List.find?_cons] at h
    cases hpx : p x
    · rw [hpx] at h
      rw [List.cons_append, List.find?_cons, hpx]
      exact find?_append_none p xs ys h
    · rw [hpx] at h
      cases h

private theorem find?_filter_cone_none (inCone : DomId → Bool) (te : Tagged)
    (hout : inCone te.2 = false) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => inCone p.1.2)).find? (·.1 == te) = none
  | [] => rfl
  | p :: xs => by
    rw [List.filter]
    cases hc : inCone p.1.2
    · exact find?_filter_cone_none inCone te hout xs
    · rw [List.find?_cons]
      have hdom := dom_beq_false_of_pred_mismatch inCone p.1.2 te.2 hc hout
      rw [tagged_beq_false_of_dom_ne p.1 te hdom]
      exact find?_filter_cone_none inCone te hout xs

private theorem find?_filter_outside_eq (inCone : DomId → Bool) (te : Tagged)
    (hout : inCone te.2 = false) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => !(inCone p.1.2))).find? (·.1 == te) = xs.find? (·.1 == te)
  | [] => rfl
  | p :: xs => by
    rw [List.filter, List.find?_cons]
    cases hc : inCone p.1.2
    · show ((p :: List.filter (fun p => !inCone p.1.2) xs).find? (·.1 == te)) = _
      rw [List.find?_cons]
      cases (p.1 == te)
      · exact find?_filter_outside_eq inCone te hout xs
      · rfl
    · show ((List.filter (fun p => !inCone p.1.2) xs).find? (·.1 == te)) = _
      have hdom := dom_beq_false_of_pred_mismatch inCone p.1.2 te.2 hc hout
      rw [tagged_beq_false_of_dom_ne p.1 te hdom]
      exact find?_filter_outside_eq inCone te hout xs

/-- **Framing Theorem 1 (Outside-Slice Frame Preservation, Zero Axioms):**
Every instance `te` outside `coneDoms` retains its exact `Info` (value, `fromSat`, `since`,
`expiry`, `origin`) from `prevFull` after `reframeState`. -/
theorem reframeState_lookup_outside (coneDoms : List DomId) (prevFull slicedNext : State) (te : Tagged)
    (hout : (DomSet.ofList coneDoms).has te.2 = false) :
    (reframeState coneDoms prevFull slicedNext).lookup te = prevFull.lookup te := by
  unfold reframeState State.lookup
  dsimp only
  rw [find?_append_none (fun (x : Tagged × Info) => x.1 == te) _ _
      (find?_filter_cone_none (DomSet.ofList coneDoms).has te hout slicedNext.contents)]
  rw [find?_filter_outside_eq (DomSet.ofList coneDoms).has te hout prevFull.contents]

private theorem find?_filter_cone_inside (inCone : DomId → Bool) (te : Tagged)
    (hin : inCone te.2 = true) :
    ∀ (xs : List (Tagged × Info)) (ys : List (Tagged × Info)),
      ys.find? (·.1 == te) = none →
      (xs.filter (fun p => inCone p.1.2) ++ ys).find? (·.1 == te) = xs.find? (·.1 == te)
  | [], ys, hys => hys
  | p :: xs, ys, hys => by
    rw [List.filter, List.find?_cons]
    cases hc : inCone p.1.2
    · have hdom : (p.1.2 == te.2) = false := by
        cases heq : (p.1.2 == te.2)
        · rfl
        · have hd : p.1.2 = te.2 := beq_iff_eq.mp heq
          rw [hd, hin] at hc
          cases hc
      rw [tagged_beq_false_of_dom_ne p.1 te hdom]
      exact find?_filter_cone_inside inCone te hin xs ys hys
    · rw [List.cons_append, List.find?_cons]
      cases (p.1 == te)
      · exact find?_filter_cone_inside inCone te hin xs ys hys
      · rfl

private theorem find?_filter_outside_none_of_in (inCone : DomId → Bool) (te : Tagged)
    (hin : inCone te.2 = true) :
    ∀ (xs : List (Tagged × Info)),
      (xs.filter (fun p => !(inCone p.1.2))).find? (·.1 == te) = none
  | [] => rfl
  | p :: xs => by
    rw [List.filter]
    cases hc : inCone p.1.2
    · show ((p :: List.filter (fun p => !inCone p.1.2) xs).find? (·.1 == te)) = none
      rw [List.find?_cons]
      have hdom : (p.1.2 == te.2) = false := by
        cases heq : (p.1.2 == te.2)
        · rfl
        · have hd : p.1.2 = te.2 := beq_iff_eq.mp heq
          rw [hd, hin] at hc
          cases hc
      rw [tagged_beq_false_of_dom_ne p.1 te hdom]
      exact find?_filter_outside_none_of_in inCone te hin xs
    · exact find?_filter_outside_none_of_in inCone te hin xs

/-- **Framing Theorem 2 (Inside-Slice Agreement, Zero Axioms):**
Every instance `te` inside `coneDoms` reads its exact updated `Info` from `slicedNext` after `reframeState`. -/
theorem reframeState_lookup_inside (coneDoms : List DomId) (prevFull slicedNext : State) (te : Tagged)
    (hin : (DomSet.ofList coneDoms).has te.2 = true) :
    (reframeState coneDoms prevFull slicedNext).lookup te = slicedNext.lookup te := by
  unfold reframeState State.lookup
  dsimp only
  rw [find?_filter_cone_inside (DomSet.ofList coneDoms).has te hin slicedNext.contents _
      (find?_filter_outside_none_of_in (DomSet.ofList coneDoms).has te hin prevFull.contents)]

/-- **Framing Theorem 3 (Saturation Frame Invariance Outside Cone, Zero Axioms):**
Deriving any instance `te'` inside `coneDoms` leaves every `te` outside `coneDoms` unchanged. -/
theorem deriveWithIdx_outside_cone (inCone : DomId → Bool) (st : State) (stIdx : State.StateIndex)
    (since : Int) (te' te : Tagged)
    (hin : inCone te'.2 = true) (hout : inCone te.2 = false) :
    (st.deriveWithIdx stIdx since te').1.lookup te = st.lookup te := by
  unfold State.deriveWithIdx
  cases ((stIdx.lookup te'.2).getD []).find? (·.1 == te')
  · show State.lookup { st with contents := (te', _) :: st.contents } te = st.lookup te
    unfold State.lookup
    rw [List.find?_cons]
    have hdom := dom_beq_false_of_pred_mismatch inCone te'.2 te.2 hin hout
    rw [tagged_beq_false_of_dom_ne te' te hdom]
  · rfl

theorem deriveAllWithIdx_outside_cone (inCone : DomId → Bool) (prevIdx : State.StateIndex) :
    ∀ (tes : List Tagged) (st : State) (stIdx : State.StateIndex) (te : Tagged),
      tes.all (fun te' => inCone te'.2) = true →
      inCone te.2 = false →
      (State.deriveAllWithIdx prevIdx st stIdx tes).1.lookup te = st.lookup te
  | [], _, _, _, _, _ => rfl
  | te' :: tes, st, stIdx, te, hall, hout => by
    rw [List.all_cons] at hall
    cases hc1 : inCone te'.2
    · rw [hc1] at hall; cases hall
    · rw [hc1, Bool.true_and] at hall
      unfold State.deriveAllWithIdx
      have h1 := deriveWithIdx_outside_cone inCone st stIdx (State.stampFromIdx prevIdx st.time te') te' te hc1 hout
      cases hd1 : st.deriveWithIdx stIdx (State.stampFromIdx prevIdx st.time te') te' with
      | mk s1 rest1 =>
        cases rest1 with
        | mk sIdx1 ch1 =>
          rw [hd1] at h1
          have h2 := deriveAllWithIdx_outside_cone inCone prevIdx tes s1 sIdx1 te hall hout
          cases hd2 : State.deriveAllWithIdx prevIdx s1 sIdx1 tes with
          | mk s2 rest2 =>
            cases rest2 with
            | mk sIdx2 ch2 =>
              dsimp only at h1 ⊢
              rw [hd2] at h2 ⊢
              dsimp only at h2 ⊢
              rw [h2, h1]

#print axioms reframeState_lookup_outside
#print axioms reframeState_lookup_inside
#print axioms deriveWithIdx_outside_cone
#print axioms deriveAllWithIdx_outside_cone

/-- **Framing Theorem 4 (Chunked Stratum Composition, Zero Axioms):**
Splitting `coneStrata = xs ++ ys` into bounded sub-passes composes identically in `Except`. -/
theorem foldlM_append_ok {ε α β : Type} (f : α → β → Except ε α) :
    ∀ (xs ys : List β) (a b c : α),
      xs.foldlM f a = .ok b →
      ys.foldlM f b = .ok c →
      (xs ++ ys).foldlM f a = .ok c
  | [], ys, a, b, c, h1, h2 => by
    injection h1 with hab
    rw [List.nil_append, hab]
    exact h2
  | x :: xs, ys, a, b, c, h1, h2 => by
    show (match f a x with | Except.error e => Except.error e | Except.ok a' => (xs ++ ys).foldlM f a') = Except.ok c
    have h1' : (match f a x with | Except.error e => Except.error e | Except.ok a' => xs.foldlM f a') = Except.ok b := h1
    cases hfx : f a x with
    | error e => rw [hfx] at h1'; cases h1'
    | ok a1 =>
      rw [hfx] at h1'
      exact foldlM_append_ok f xs ys a1 b c h1' h2

theorem foldlM_cons_ok {ε α β : Type} (f : α → β → Except ε α)
    {x : β} {xs : List β} {a b c : α}
    (h1 : f a x = Except.ok b) (h2 : xs.foldlM f b = Except.ok c) :
    (x :: xs).foldlM f a = Except.ok c := by
  show (match f a x with | Except.error e => Except.error e | Except.ok a' => xs.foldlM f a') = Except.ok c
  rw [h1]
  exact h2

theorem foldlM_nil_ok {ε α β : Type} (f : α → β → Except ε α) (a : α) :
    ([] : List β).foldlM f a = Except.ok a := rfl

#print axioms foldlM_append_ok
#print axioms foldlM_cons_ok
#print axioms foldlM_nil_ok

/-! ## Sliced Step & Scenario Execution (`#74`) -/

/-- Merge newly declared `declaredDoms` and modified `updatedDoms` from `resolvedSlice`
onto `prevFull` in `O(|declaredDoms|)` when `updatedDoms = []` (`#74`: avoids exponential
`lookupDecl` recursion across chained `reframeSpec` steps). -/
def reframeSpec (declaredDoms updatedDoms : List DomId) (prevFull resolvedSlice : Spec) : Spec :=
  let declSet := DomSet.ofList declaredDoms
  let updSet := DomSet.ofList updatedDoms
  let resIdx : DomMap TypeSpec := resolvedSlice.decls.foldl (fun m (d, ts) => m.insert d ts) .empty
  let brandNew := resolvedSlice.decls.filter fun (d, _) =>
    declSet.has d && !(updSet.has d)
  let baseDecls := if updatedDoms.isEmpty then prevFull.decls
    else prevFull.decls.map fun (d, oldTs) =>
      if updSet.has d then
        match resIdx.lookup d with
        | some newTs => (d, newTs)
        | none => (d, oldTs)
      else (d, oldTs)
  let mergedAliases := if resolvedSlice.aliases.isEmpty then prevFull.aliases
    else resolvedSlice.aliases.foldr (fun (a, t) acc => (a, t) :: acc.filter (·.1 != a)) prevFull.aliases
  let mergedDocs := if resolvedSlice.documents.isEmpty then prevFull.documents
    else resolvedSlice.documents.foldl (fun acc sd =>
      if acc.any (fun x => x.path == sd.path && x.id == sd.id) then acc else acc ++ [sd]) prevFull.documents
  let mergedClauses := if resolvedSlice.clauses.isEmpty then prevFull.clauses
    else resolvedSlice.clauses.foldl (fun acc c => acc.filter (·.id != c.id) ++ [c]) prevFull.clauses
  let mergedModules := if resolvedSlice.modules.isEmpty then prevFull.modules
    else resolvedSlice.modules.foldl (fun acc (mn, ps, bd) => (mn, ps, bd) :: acc.filter (·.1 != mn)) prevFull.modules
  let mergedTemporals := if resolvedSlice.temporalProperties.isEmpty then prevFull.temporalProperties
    else resolvedSlice.temporalProperties.foldl (fun acc tp => acc.filter (·.name != tp.name) ++ [tp]) prevFull.temporalProperties
  let mergedRegimes := if resolvedSlice.regimes.isEmpty then prevFull.regimes
    else resolvedSlice.regimes.foldl (fun acc r => acc.filter (·.name != r.name) ++ [r]) prevFull.regimes
  let mergedAmendBodies := if resolvedSlice.amendBodies.isEmpty then prevFull.amendBodies
    else resolvedSlice.amendBodies.foldl (fun acc (a, ds) => acc.filter (·.1 != a) ++ [(a, ds)]) prevFull.amendBodies
  let mergedAmendMigs := if resolvedSlice.amendMigrations.isEmpty then prevFull.amendMigrations
    else resolvedSlice.amendMigrations.foldl (fun acc (a, es) => acc.filter (·.1 != a) ++ [(a, es)]) prevFull.amendMigrations
  let mergedRankEdges := if resolvedSlice.rankEdges.isEmpty then prevFull.rankEdges
    else (prevFull.rankEdges ++ resolvedSlice.rankEdges).eraseDups
  { decls := brandNew ++ baseDecls
    aliases := mergedAliases
    clauses := mergedClauses
    document := resolvedSlice.document.orElse (fun _ => prevFull.document)
    documents := mergedDocs
    modules := mergedModules
    temporalProperties := mergedTemporals
    scenarios := prevFull.scenarios
    regimes := mergedRegimes
    amendBodies := mergedAmendBodies
    amendMigrations := mergedAmendMigs
    amendProcedure := if resolvedSlice.amendProcedure.isEmpty then prevFull.amendProcedure else resolvedSlice.amendProcedure
    tracksHistory := prevFull.tracksHistory || resolvedSlice.tracksHistory
    rankEdges := mergedRankEdges
    serviceInterfaceDeclared := prevFull.serviceInterfaceDeclared || resolvedSlice.serviceInterfaceDeclared
    exposedActs := if resolvedSlice.exposedActs.isEmpty then prevFull.exposedActs else (prevFull.exposedActs ++ resolvedSlice.exposedActs).eraseDups
    exposedInputs := if resolvedSlice.exposedInputs.isEmpty then prevFull.exposedInputs else (prevFull.exposedInputs ++ resolvedSlice.exposedInputs).eraseDups
    actorKeys := if resolvedSlice.actorKeys.isEmpty then prevFull.actorKeys else resolvedSlice.actorKeys.foldl (fun acc (a, pk) => acc.filter (·.1 != a) ++ [(a, pk)]) prevFull.actorKeys }

/-- One stratum step inside `runStrataBatch` (`#74`). -/
def satLayerStep (slicedSpec : Spec) (slicedIdx : Spec.SpecIndex)
    (prev : List (Tagged × Info)) (hasEp : Bool)
    (immDecls : List (DomId × TypeSpec × ImmunitySpec))
    (acc : State × State.StateIndex) (layer : List DomId) :
    Except RuntimeError (State × State.StateIndex) :=
  let (s, sIdx) := acc
  let basePrevIdx := State.indexList prev
  let seeds := Saturate.clockThresholdSeedsIdx slicedSpec slicedIdx hasEp immDecls s sIdx layer
  let prevIdx := if seeds.isEmpty then basePrevIdx else State.indexList (prev ++ seeds)
  let isRec := Saturate.layerNeedsLoop slicedSpec slicedIdx layer
  Saturate.saturateStratumIdx slicedSpec slicedIdx hasEp isRec immDecls prevIdx layer 100000 s sIdx

/-- Saturate one bounded batch of strata (`<= 18` layers) on `st` (`#74`). -/
def runStrataBatch (slicedSpec : Spec) (prev : List (Tagged × Info))
    (st : State) (layers : List (List DomId)) : Except RuntimeError State := do
  let slicedIdx := slicedSpec.buildIndex
  let hasEp := slicedSpec.hasEpistemicOrDefeasible
  let immDecls := slicedSpec.allImmunities
  let (sFin, _) ← layers.foldlM (satLayerStep slicedSpec slicedIdx prev hasEp immDecls) (st, st.buildIndex)
  return sFin

/-- Intermediate pre-saturation state for decomposed multi-batch checkpointing (`#74`). -/
structure SatSetup where
  workSpec     : Spec
  nextSpec     : Spec
  nextStrata   : List (List DomId)
  prevFacts    : List (Tagged × Info)
  s0           : State
  verdictDelta : List Bool
  deriving Repr, Inhabited

inductive StepPreOutcome where
  | done (res : Summary)
  | sat  (setup : SatSetup)
  deriving Repr

/-- Pre-saturation phase of `stepSummarySliced` (`#74`): resolves `p` against the narrow
`sl.resolveDoms` carrier slice, then projects `sl.readWriteDoms` for evaluation/saturation. -/
def stepSlicedPre (s : Summary) (sl : StepSlice) (p : Phrase) : StepPreOutcome :=
  if sl.useFull then
    .done (stepSummary s p)
  else if sl.isDeclSlice then
    let rDoms := if sl.resolveDoms.isEmpty then sl.readWriteDoms else sl.resolveDoms
    let priorResolveSlice := projectSpec rDoms s.cfg.spec
    match resolvePhrase priorResolveSlice p with
    | .error _ => .done s
    | .ok (resSlice, cp, _) =>
      match Stratify.strata resSlice with
      | .error _ => .done s
      | .ok _ =>
        let nextSpec := reframeSpec sl.declaredDoms sl.updatedDoms s.cfg.spec resSlice
        let evalSlice := projectSpec sl.readWriteDoms nextSpec
        let slicedIdx := evalSlice.buildIndex
        let slicedState0 := { (projectState sl.readWriteDoms s.cfg.state) with step := s.cfg.state.step + 1 }
        let (store?, outs) := Interp.semPhrase evalSlice slicedIdx slicedState0 1000 cp
        let vd := claimVerdicts p outs
        match store? with
        | none => .done { s with verdicts := s.verdicts ++ vd }
        | some store =>
          if store.isEmpty && sl.strataBatches.isEmpty then
            let nextState := { s.cfg.state with step := s.cfg.state.step + 1 }
            .done { s with cfg := { s.cfg with spec := nextSpec, strata := sl.nextStrata, state := nextState },
                           verdicts := s.verdicts ++ vd }
          else
            let state1 := State.makeAssignments evalSlice store slicedState0
            let prev := state1.derivedFacts
            let s0 := rebaseCone sl.coneDoms state1
            .sat { workSpec := evalSlice, nextSpec, nextStrata := sl.nextStrata, prevFacts := prev, s0, verdictDelta := vd }
  else
    let pDoms := if sl.resolveDoms.isEmpty then sl.readWriteDoms else sl.resolveDoms
    let phraseSpec := projectSpec pDoms s.cfg.spec
    match resolvePhrase phraseSpec p with
    | .error _ => .done s
    | .ok (_, cp, _) =>
      let pIdx := phraseSpec.buildIndex
      let basePhraseSt := projectState pDoms s.cfg.state
      match Interp.evalClockStep phraseSpec pIdx basePhraseSt cp with
      | .error _ => .done s
      | .ok newTime =>
        let phraseState0 := match newTime with
          | some t => { basePhraseSt with time := t, step := s.cfg.state.step + 1 }
          | none => { basePhraseSt with step := s.cfg.state.step + 1 }
        let (store?, outs0) := Interp.semPhrase phraseSpec pIdx phraseState0 1000 cp
        let outs := match newTime with | some t => Output.timeSet t :: outs0 | none => outs0
        let vd := claimVerdicts p outs
        match store? with
        | none => .done { s with verdicts := s.verdicts ++ vd }
        | some store =>
          if newTime.isNone && store.isEmpty then
            let nextFullState := { s.cfg.state with step := s.cfg.state.step + 1 }
            .done { s with cfg := { s.cfg with state := nextFullState }, verdicts := s.verdicts ++ vd }
          else
            let phraseSt1 := State.makeAssignments phraseSpec store phraseState0
            let rwBaseSt := { (projectState sl.readWriteDoms s.cfg.state) with time := phraseSt1.time, step := phraseSt1.step }
            let state1 := reframeState pDoms rwBaseSt phraseSt1
            let workSpec := projectSpec sl.readWriteDoms s.cfg.spec
            let prev := state1.derivedFacts
            let s0 := rebaseCone sl.coneDoms state1
            .sat { workSpec, nextSpec := s.cfg.spec, nextStrata := s.cfg.strata, prevFacts := prev, s0, verdictDelta := vd }

/-- Post-saturation reframing and cone duty check of `stepSummarySliced` (`#74`). -/
def stepSlicedPost (s : Summary) (sl : StepSlice) (setup : SatSetup) (slicedAfter : State) : Summary :=
  let cset := DomSet.ofList sl.coneDoms
  let reframed := reframeState sl.coneDoms s.cfg.state slicedAfter
  let slicedIdx := setup.workSpec.buildIndex
  let coneDuties := slicedAfter.holdsList.filter fun te =>
    cset.has te.2 &&
    match slicedIdx.lookup te.2 with
    | some ({ kind := .duty _, .. }, _, _) => true
    | _ => false
  let ctx' := Ctx.ofBothIdx setup.workSpec slicedIdx slicedAfter slicedAfter.buildIndex
    setup.workSpec.hasEpistemicOrDefeasible (some setup.workSpec.allImmunities)
  let coneViol := coneDuties.filter fun te =>
    let vconds := match slicedIdx.lookup te.2 with
      | some ({ kind := .duty ds, .. }, _, _) => some ds.violatedWhen
      | _ => none
    match (M.ignoreMissingInput (M.evalViolationCondition M.fuel te vconds)).run ctx' [] with
    | .ok bs => bs.any id
    | .error _ => false
  let keptViol := s.cfg.violatedDuties.filter fun te => !(cset.has te.2)
  let nextCfg : Config := {
    s.cfg with
    spec := setup.nextSpec
    strata := setup.nextStrata
    state := reframed
    violatedDuties := coneViol ++ keptViol
  }
  { s with cfg := nextCfg, verdicts := s.verdicts ++ setup.verdictDelta }

/-- Execute one phrase over its `StepSlice` (`#74`). -/
def stepSummarySliced (s : Summary) (sl : StepSlice) (p : Phrase) : Summary :=
  match stepSlicedPre s sl p with
  | .done res => res
  | .sat setup =>
    match sl.strataBatches.foldlM (runStrataBatch setup.workSpec setup.prevFacts) setup.s0 with
    | .error _ => { s with verdicts := s.verdicts ++ setup.verdictDelta }
    | .ok slicedAfter => stepSlicedPost s sl setup slicedAfter

/-- **Zero-Axiom Multi-Batch Step Composition Theorem (`#74`, `Law 10`):**
Combines `stepSlicedPre`, a chain of per-batch `runStrataBatch` theorems, and `stepSlicedPost`
into `stepSummarySliced s sl p = S_next` with zero axioms. -/
theorem stepSummarySliced_of_batches {s S_next : Summary} {sl : StepSlice} {p : Phrase}
    {setup : SatSetup} {sFin : State}
    (hpre : stepSlicedPre s sl p = .sat setup)
    (hsat : sl.strataBatches.foldlM (runStrataBatch setup.workSpec setup.prevFacts) setup.s0 = Except.ok sFin)
    (hpost : stepSlicedPost s sl setup sFin = S_next) :
    stepSummarySliced s sl p = S_next := by
  unfold stepSummarySliced
  rw [hpre]
  dsimp only
  rw [hsat]
  dsimp only
  exact hpost

#print axioms stepSummarySliced_of_batches

/-- Check invariants at a scenario/program end state using each invariant's own minimal read slice (`#74`). -/
def addViolatedSliced (isl : InvariantSlice) (s : Summary) : Summary :=
  if isl.useFull then
    addViolated s
  else
    let bad := isl.perInv.filterMap fun (invId, doms) =>
      if s.violated.contains invId then none
      else
        let slicedSpec := projectSpec doms s.cfg.spec
        let slicedState := projectState doms s.cfg.state
        let ctx := Ctx.of slicedSpec slicedState
        let term := Term.exists_ [⟨invId, ""⟩] (.present (.ref ⟨invId, ""⟩))
        match (M.ignoreMissingInput (M.checkFalse (M.eval M.fuel term))).run ctx [] with
        | .ok rs => if !rs.isEmpty then some invId else none
        | .error _ => none
    { s with violated := s.violated ++ bad }

/-- Annotated item tree pairing every phrase with its `StepSlice` and every scenario with its `InvariantSlice`. -/
inductive SlicedItem where
  | phrase (sl : StepSlice) (p : Phrase)
  | scenario (name : String) (steps : List (StepSlice × Phrase)) (isl : InvariantSlice)

def stepSlicedPair (s : Summary) (sp : StepSlice × Phrase) : Summary :=
  stepSummarySliced s sp.1 sp.2

def stepSlicedItem (s : Summary) : SlicedItem → Summary
  | .phrase sl p => stepSummarySliced s sl p
  | .scenario _ steps isl =>
    afterScenario s (addViolatedSliced isl (steps.foldl stepSlicedPair s))

def summarizeSliced (finIsl : InvariantSlice) (items : List SlicedItem) : Summary :=
  addViolatedSliced finIsl (items.foldl stepSlicedItem S0)

def summarySliced (finIsl : InvariantSlice) (items : List SlicedItem) : List Bool × List DomId :=
  let fin := summarizeSliced finIsl items
  (fin.verdicts, fin.violated)

/-! ### Zero-Axiom Chaining Lemmas for `summarizeSliced` (`Law 10`) -/

theorem foldl_step_sliced {s s' : Summary} {sl : StepSlice} {p : Phrase} {rest : List (StepSlice × Phrase)}
    (h : stepSummarySliced s sl p = s') :
    ((sl, p) :: rest).foldl stepSlicedPair s = rest.foldl stepSlicedPair s' := by
  rw [List.foldl_cons]
  show rest.foldl stepSlicedPair (stepSummarySliced s sl p) = _
  rw [h]

theorem foldl_phrase_sliced {s s' : Summary} {sl : StepSlice} {p : Phrase} {rest : List SlicedItem}
    (h : stepSummarySliced s sl p = s') :
    (SlicedItem.phrase sl p :: rest).foldl stepSlicedItem s = rest.foldl stepSlicedItem s' := by
  rw [List.foldl_cons]
  show rest.foldl stepSlicedItem (stepSummarySliced s sl p) = _
  rw [h]

theorem foldl_scenario_sliced {s s' s'' s₃ : Summary} {name : String}
    {steps : List (StepSlice × Phrase)} {isl : InvariantSlice} {rest : List SlicedItem}
    (h : steps.foldl stepSlicedPair s = s')
    (hv : addViolatedSliced isl s' = s'')
    (hc : afterScenario s s'' = s₃) :
    (SlicedItem.scenario name steps isl :: rest).foldl stepSlicedItem s = rest.foldl stepSlicedItem s₃ := by
  rw [List.foldl_cons]
  show rest.foldl stepSlicedItem (afterScenario s (addViolatedSliced isl (steps.foldl stepSlicedPair s))) = _
  rw [h, hv, hc]

#print axioms foldl_step_sliced
#print axioms foldl_phrase_sliced
#print axioms foldl_scenario_sliced

/-! ## Automatic Generation-Time Slice Synthesis & Equivalence Verification (`#74`) -/

mutual
def allTermDoms (spec : Spec) : Term → List DomId
  | .ref v => [spec.removeDecoration v, v.dom]
  | .project u fld => spec.removeDecoration fld :: fld.dom :: allTermDoms spec u
  | .tag u d => spec.chaseAlias d :: d :: allTermDoms spec u
  | .fnApp d k => spec.chaseAlias d :: d :: allTermDoms spec k
  | .app d (.pos ts) => spec.chaseAlias d :: d :: allTermListDoms spec ts
  | .app d (.named ms) =>
    spec.chaseAlias d :: d :: (ms.map fun (v, _) => spec.removeDecoration v) ++ allTermModDoms spec ms
  | .exists_ xs u | .forall_ xs u | .count xs u | .sum xs u | .max xs u | .min xs u =>
    xs.map spec.removeDecoration ++ xs.map (·.dom) ++ allTermDoms spec u
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .untag a | .doneAt a | .stampOf a | .overdueOf a | .calOp1 _ a =>
    allTermDoms spec a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b | .calOp2 _ a b =>
    allTermDoms spec a ++ allTermDoms spec b
  | .ite c t e | .mulDivRound c t e _ =>
    allTermDoms spec c ++ allTermDoms spec t ++ allTermDoms spec e
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime | .dimLit _ _ => []

def allTermListDoms (spec : Spec) : List Term → List DomId
  | [] => []
  | t :: ts => allTermDoms spec t ++ allTermListDoms spec ts

def allTermModDoms (spec : Spec) : List (Var × Term) → List DomId
  | [] => []
  | (v, t) :: ms => spec.removeDecoration v :: v.dom :: allTermDoms spec t ++ allTermModDoms spec ms
end

def allTypeSpecDoms (spec : Spec) (ts : TypeSpec) : List DomId :=
  let domDoms := match ts.domain with
    | .products xs => xs.map spec.removeDecoration ++ xs.map (·.dom)
    | _ => []
  let filtDoms := allTermDoms spec ts.domainConstraint
  let condDoms := allTermListDoms spec ts.conditions
  let derivDoms := ts.derivation.flatMap fun
    | .holdsWhen tm => allTermDoms spec tm
    | .dv ys tm => ys.map spec.removeDecoration ++ allTermDoms spec tm
    | .defeasibleDAG _ rs => rs.flatMap fun r =>
      r.freeVars.map spec.removeDecoration ++ allTermDoms spec r.cond ++
      (match r.conseq with | .holdsBool _ => [] | .yieldsVal vt => allTermDoms spec vt)
  let kindDoms := match ts.kind with
    | .act a =>
      allTermListDoms spec a.validWhen ++ a.exceptUnder ++ a.repeals ++ a.installedNames ++
      (a.syncs.flatMap fun sy => sy.xs.map spec.removeDecoration ++ allTermDoms spec sy.t) ++
      (a.effects.flatMap fun
        | .cAll ys tm dur? _ => ys.map spec.removeDecoration ++ allTermDoms spec tm ++ (dur?.map (allTermDoms spec) |>.getD [])
        | .tAll ys tm _ | .oAll ys tm _ | .evOp _ ys tm _ | .findingOp _ ys tm _ =>
          ys.map spec.removeDecoration ++ allTermDoms spec tm
        | .amendOp am => [am])
    | .duty du =>
      allTermListDoms spec (du.violatedWhen ++ du.excusedWhen ++ du.lateWhen) ++
      (du.dueDuration.map (allTermDoms spec) |>.getD []) ++
      du.overriddenBy ++ du.terminatingActs ++ du.creatingActs ++ du.enforcingActs
    | .event ev =>
      (ev.syncs.flatMap fun sy => sy.xs.map spec.removeDecoration ++ allTermDoms spec sy.t) ++
      (ev.effects.flatMap fun
        | .cAll ys tm dur? _ => ys.map spec.removeDecoration ++ allTermDoms spec tm ++ (dur?.map (allTermDoms spec) |>.getD [])
        | .tAll ys tm _ | .oAll ys tm _ | .evOp _ ys tm _ | .findingOp _ ys tm _ =>
          ys.map spec.removeDecoration ++ allTermDoms spec tm
        | .amendOp am => [am])
    | .immunity im =>
      allTermListDoms spec im.unlessConds
    | .fact _ => []
  (domDoms ++ filtDoms ++ condDoms ++ derivDoms ++ kindDoms).eraseDups

def allTemporalDoms (spec : Spec) : TemporalFormula → List DomId
  | .always a => allTermDoms spec a
  | .alwaysNext a b | .alwaysEventually a b | .until_ a b | .weakUntil a b =>
    allTermDoms spec a ++ allTermDoms spec b
  | .alwaysEventuallyWithin d a b =>
    allTermDoms spec d ++ allTermDoms spec a ++ allTermDoms spec b

/-- Close `seeds` only over product-domain component types and aliases (`#74`: minimal
slice required by `resolvePhrase` — typically 5–30 types instead of 150–770!). -/
def domainComponentClosure (spec : Spec) (seeds : List DomId) : List DomId := Id.run do
  let mut vis : List DomId := []
  let mut work : List DomId := (seeds.map spec.chaseAlias).eraseDups
  for _ in [0 : spec.decls.length * 4 + 256] do
    match work with
    | [] => break
    | d :: rest =>
      work := rest
      if !vis.contains d && d != "int" && d != "string" && d != "actor" && !d.isEmpty then
        vis := vis ++ [d]
        if let some ts := spec.findDecl d then
          let comps := match ts.domain with
            | .products xs => xs.map spec.removeDecoration ++ xs.map (fun (v : Var) => v.dom)
            | _ => []
          for nxt in comps.map spec.chaseAlias do
            if !vis.contains nxt then work := nxt :: work
  let aliasExtras := spec.aliases.filterMap fun (al, _) =>
    if vis.contains (spec.chaseAlias al) then some al else none
  let internalExtras := if spec.tracksHistory then ["$occ"] else []
  return (vis ++ aliasExtras ++ internalExtras).eraseDups

/-- Backward read-closure of `seeds` in `spec` (including all projection, product, effect,
sync, immunity, and duty dependencies). -/
def backwardReadClosure (spec : Spec) (seeds : List DomId) : List DomId := Id.run do
  let mut vis : List DomId := []
  let mut work : List DomId := (seeds.map spec.chaseAlias).eraseDups
  for _ in [0 : spec.decls.length * 4 + 256] do
    match work with
    | [] => break
    | d :: rest =>
      work := rest
      if !vis.contains d && d != "int" && d != "string" && d != "actor" && !d.isEmpty then
        vis := vis ++ [d]
        if let some ts := spec.findDecl d then
          let immDoms := (spec.immunitiesAgainst d ++ spec.protectionsFor d).map (·.1)
          for nxt in (allTypeSpecDoms spec ts ++ immDoms).map spec.chaseAlias do
            if !vis.contains nxt then work := nxt :: work
  let aliasExtras := spec.aliases.filterMap fun (al, _) =>
    if vis.contains (spec.chaseAlias al) then some al else none
  let internalExtras := if spec.tracksHistory then ["$occ"] else []
  let conflictExtras := if spec.hasEpistemicOrDefeasible then
      [defConflictDom, evSupportDom, evRebutDom, evFindingPosDom, evFindingNegDom]
    else []
  return (vis ++ aliasExtras ++ internalExtras ++ conflictExtras).eraseDups

/-- Forward dependency closure of `writtenSeeds` across `spec`'s derived types (`#74`). -/
def forwardDerivedCone (spec : Spec) (strata : List (List DomId)) (writtenSeeds : List DomId) :
    List DomId × List (List DomId) := Id.run do
  let allDerived := strata.flatten
  let depTable : List (DomId × List DomId) := allDerived.map fun d =>
    match spec.findDecl d with
    | some ts =>
      let immDoms := (spec.immunitiesAgainst d ++ spec.protectionsFor d).map (·.1)
      (d, ((allTypeSpecDoms spec ts ++ immDoms).map spec.chaseAlias).eraseDups)
    | none => (d, [])
  let mut cone : List DomId := (writtenSeeds.map spec.chaseAlias).eraseDups
  let mut changed := true
  for _ in [0 : allDerived.length + 2] do
    if changed then
      changed := false
      for (d, deps) in depTable do
        if !cone.contains d && deps.any cone.contains then
          cone := cone ++ [d]
          changed := true
  if spec.hasDefeasibleRules && !cone.contains defConflictDom then
    cone := cone ++ [defConflictDom]
  let coneStrata := strata.filterMap fun layer =>
    let sub := layer.filter cone.contains
    if sub.isEmpty then none else some sub
  -- If any part of a multi-type SCC is in `cone`, include the whole SCC layer!
  let fullConeStrata := strata.filter fun layer => layer.any cone.contains
  let fullCone := (cone ++ fullConeStrata.flatten).eraseDups
  let _ := coneStrata
  return (fullCone, fullConeStrata)

/-- Exact observable state-lookup & verdict equivalence check between sliced and unsliced `Summary`. -/
def summariesEquivalent (a b : Summary) : Bool :=
  a.verdicts == b.verdicts &&
  a.violated == b.violated &&
  a.cfg.lawVersion == b.cfg.lawVersion &&
  a.cfg.state.time == b.cfg.state.time &&
  a.cfg.state.step == b.cfg.state.step &&
  a.cfg.violatedDuties.length == b.cfg.violatedDuties.length &&
  a.cfg.violatedDuties.all b.cfg.violatedDuties.contains &&
  a.cfg.state.contents.all (fun (te, ia) =>
    match b.cfg.state.lookup te with
    | some ib =>
      ia.value == ib.value && ia.fromSat == ib.fromSat &&
      ia.since == ib.since && ia.expiry == ib.expiry
    | none => !ia.live a.cfg.state.time && !ia.fromSat && false) &&
  b.cfg.state.contents.all (fun (te, ib) =>
    match a.cfg.state.lookup te with
    | some ia =>
      ia.value == ib.value && ia.fromSat == ib.fromSat &&
      ia.since == ib.since && ia.expiry == ib.expiry
    | none => false)

/-- Extract all seed `DomId`s referenced by a compiled `CPhrase` (including `.par` blocks!). -/
partial def cpSeedsOf (spec : Spec) : CPhrase → List DomId
  | .query t => allTermDoms spec t ++ (Stratify.typeOf spec t).toList
  | .expect _ _ xs t => xs.map spec.removeDecoration ++ allTermDoms spec t ++ (Stratify.typeOf spec t).toList
  | .create xs t | .terminate xs t | .obfuscate xs t | .trigger xs t
  | .submitEvidence _ xs t _ | .retractEvidence xs t _ | .instQuery _ xs t | .why xs t =>
    xs.map spec.removeDecoration ++ allTermDoms spec t ++ (Stratify.typeOf spec t).toList
  | .onlyDecls st => (st.map (·.1.2)).eraseDups
  | .par ps => ps.flatMap (cpSeedsOf spec)
  | _ => []

/-- Partition `strata` into bounded sub-batches of at most `batchSz` layers (`#74`). -/
def groupStrataBatches (batchSz : Nat) (strata : List (List DomId)) : List (List (List DomId)) :=
  if strata.isEmpty then []
  else
    let rec go : Nat → List (List DomId) → List (List (List DomId))
      | 0, rem => if rem.isEmpty then [] else [rem]
      | _ + 1, [] => []
      | k + 1, rem => rem.take batchSz :: go k (rem.drop batchSz)
    go (strata.length + 1) strata

/-- Whether a `Term` directly mentions the institutional clock (`Current Time`, `Held for`, `Done at`, etc.). -/
partial def termReadsClock : Term → Bool
  | .currentTime => true
  | .heldFor _ _ | .doneAt _ | .stampOf _ | .overdueOf _ => true
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a
  | .untag a | .calOp1 _ a | .project a _ | .tag a _ | .fnApp _ a => termReadsClock a
  | .exists_ _ u | .forall_ _ u | .count _ u | .sum _ u | .max _ u | .min _ u => termReadsClock u
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .calOp2 _ a b => termReadsClock a || termReadsClock b
  | .ite c t e | .mulDivRound c t e _ => termReadsClock c || termReadsClock t || termReadsClock e
  | .app _ (.pos ts) => ts.any termReadsClock
  | .app _ (.named ms) => ms.any (fun (_, t) => termReadsClock t)
  | .ref _ | .boolLit _ | .intLit _ | .stringLit _ | .dimLit _ _ => false

def typeSpecReadsClock (ts : TypeSpec) : Bool :=
  termReadsClock ts.domainConstraint || ts.conditions.any termReadsClock ||
  ts.derivation.any (fun
    | .holdsWhen tm | .dv _ tm => termReadsClock tm
    | .defeasibleDAG _ rs => rs.any fun r =>
      termReadsClock r.cond || (match r.conseq with | .holdsBool _ => false | .yieldsVal vt => termReadsClock vt)) ||
  (match ts.kind with
   | .duty du => (du.violatedWhen ++ du.excusedWhen ++ du.lateWhen).any termReadsClock || du.dueDuration.isSome || du.everyPeriod.isSome
   | _ => false)

/-- Synthesize a verified `StepSlice` for `(cur, p)` (`#74`), including declaration and clock slices! -/
def computeVerifiedStepSlice (cur : Summary) (p : Phrase) : StepSlice × Summary := Id.run do
  let fullNext := stepSummary cur p
  if cur.cfg.lawVersion != fullNext.cfg.lawVersion then
    return ({ useFull := true }, fullNext)
  if p.hasDecls then
    let declChangedDoms := fullNext.cfg.spec.decls.filterMap fun (d, newTs) =>
      match cur.cfg.spec.lookupDecl d with
      | none => some d
      | some oldTs => if reprStr oldTs != reprStr newTs then some d else none
    let updatedDoms := declChangedDoms.filter fun d => (cur.cfg.spec.lookupDecl d).isSome
    let tempSeeds := fullNext.cfg.spec.temporalProperties.flatMap fun tp =>
      if cur.cfg.spec.temporalProperties.any (·.name == tp.name) then []
      else allTemporalDoms fullNext.cfg.spec tp.formula
    let exposeSeeds := fullNext.cfg.spec.exposedActs ++ fullNext.cfg.spec.exposedInputs
    let regimeSeeds := fullNext.cfg.spec.regimes.flatMap (fun r => r.params.map (·.1))
    let directRefs := declChangedDoms.flatMap fun d =>
      match fullNext.cfg.spec.lookupDecl d with
      | some ts =>
        let immDirect := match ts.kind with | .immunity im => im.against ++ im.protects | _ => []
        d :: immDirect ++ allTypeSpecDoms fullNext.cfg.spec ts
      | none => [d]
    let minResDoms := domainComponentClosure fullNext.cfg.spec (directRefs ++ tempSeeds ++ exposeSeeds ++ regimeSeeds)
    let seeds := backwardReadClosure fullNext.cfg.spec (declChangedDoms ++ tempSeeds ++ exposeSeeds ++ regimeSeeds)
    let written := declChangedDoms.filter fun d =>
      match fullNext.cfg.spec.lookupDecl d with
      | some ts => !ts.derivation.isEmpty || (match ts.kind with | .fact fs => fs.defaultVal.isSome | _ => false)
      | none => false
    let (coneDoms, coneStrata) := forwardDerivedCone fullNext.cfg.spec fullNext.cfg.strata written
    let rwDoms := backwardReadClosure fullNext.cfg.spec (seeds ++ coneDoms)
    let candMin : StepSlice := {
      useFull := false
      isDeclSlice := true
      resolveDoms := minResDoms
      readWriteDoms := rwDoms
      declaredDoms := declChangedDoms
      updatedDoms := updatedDoms
      coneDoms := (declChangedDoms ++ coneDoms).eraseDups
      strataBatches := groupStrataBatches 14 coneStrata
      nextStrata := fullNext.cfg.strata
    }
    let checkDeclCand (c : StepSlice) : Option (StepSlice × Summary) :=
      let sn := stepSummarySliced cur c p
      let dsOk :=
        sn.cfg.spec.decls.length == fullNext.cfg.spec.decls.length &&
        sn.cfg.spec.clauses.length == fullNext.cfg.spec.clauses.length &&
        sn.cfg.spec.decls.all (fun (d, ts) => reprStr (fullNext.cfg.spec.lookupDecl d) == reprStr (some ts))
      if summariesEquivalent sn fullNext && dsOk && sn.cfg.strata == fullNext.cfg.strata then some (c, sn)
      else none
    if let some hit := checkDeclCand candMin then
      return hit
    else if let some hit2 := checkDeclCand { candMin with resolveDoms := rwDoms } then
      return hit2
    else
      return ({ useFull := true }, fullNext)
  match resolvePhrase cur.cfg.spec p with
  | .error _ => return ({ useFull := true }, fullNext)
  | .ok (spec', cp, _) =>
    let specIdx := spec'.buildIndex
    let newTime? := match Interp.evalClockStep spec' specIdx cur.cfg.state cp with
      | .ok nt => nt
      | .error _ => none
    let state0 := match newTime? with
      | some t => { cur.cfg.state with time := t, step := cur.cfg.state.step + 1 }
      | none => { cur.cfg.state with step := cur.cfg.state.step + 1 }
    let (store?, _) := Interp.semPhrase spec' specIdx state0 1000 cp
    let cpSeeds := cpSeedsOf spec' cp
    let minResDoms := domainComponentClosure spec' cpSeeds
    match store? with
    | some [] =>
      if newTime?.isNone then
        let extraDutySeeds := match cp with
          | .expect .lawful .. =>
            let actWritten := backwardReadClosure spec' cpSeeds
            let (actCone, _) := forwardDerivedCone spec' cur.cfg.strata actWritten
            let dutyDoms := (cur.cfg.state.holdsList.filterMap fun te =>
              match spec'.findDecl te.2 with | some { kind := .duty _, .. } => some te.2 | _ => none).eraseDups
            actCone ++ dutyDoms
          | _ => []
        let rwDoms := backwardReadClosure spec' (cpSeeds ++ extraDutySeeds)
        let cand : StepSlice := { useFull := false, resolveDoms := minResDoms, readWriteDoms := rwDoms }
        let slicedNext := stepSummarySliced cur cand p
        if summariesEquivalent slicedNext fullNext then
          return (cand, slicedNext)
        else
          let cand2 := { cand with resolveDoms := rwDoms }
          let slicedNext2 := stepSummarySliced cur cand2 p
          if summariesEquivalent slicedNext2 fullNext then return (cand2, slicedNext2)
          else return ({ useFull := true }, fullNext)
      else
        -- Clock jump (`@ t` or `>> d`): seed with expiring state entries + clock-reading derived types!
        let expDoms := (cur.cfg.state.contents.filterMap fun (te, info) =>
          if info.expiry.isSome then some te.2 else none).eraseDups
        let clkDoms := spec'.decls.filterMap fun (d, ts) =>
          if typeSpecReadsClock ts then some d else none
        let dutyDoms := (cur.cfg.state.holdsList.filterMap fun te =>
          match spec'.findDecl te.2 with
          | some { kind := .duty _, .. } => some te.2
          | _ => none).eraseDups
        let written := (expDoms ++ clkDoms ++ dutyDoms).eraseDups
        let (coneDoms, coneStrata) := forwardDerivedCone spec' cur.cfg.strata written
        let rwDoms := backwardReadClosure spec' (cpSeeds ++ written ++ coneDoms)
        let cand : StepSlice := {
          useFull := false
          resolveDoms := minResDoms
          readWriteDoms := rwDoms
          coneDoms := (written ++ coneDoms).eraseDups
          strataBatches := groupStrataBatches 14 coneStrata
        }
        let slicedNext := stepSummarySliced cur cand p
        if summariesEquivalent slicedNext fullNext then
          return (cand, slicedNext)
        else
          return ({ useFull := true }, fullNext)
    | some store =>
      let written := (store.map (·.1.2)).eraseDups
      let phraseRwDoms := backwardReadClosure spec' (cpSeeds ++ written)
      let (coneDoms, coneStrata) := forwardDerivedCone spec' cur.cfg.strata written
      let rwDoms := backwardReadClosure spec' (cpSeeds ++ written ++ coneDoms)
      let cand : StepSlice := {
        useFull := false
        resolveDoms := phraseRwDoms
        readWriteDoms := rwDoms
        coneDoms := coneDoms
        strataBatches := groupStrataBatches 14 coneStrata
      }
      let slicedNext := stepSummarySliced cur cand p
      if summariesEquivalent slicedNext fullNext then
        return (cand, slicedNext)
      else
        -- Batched full-domain slice fallback with narrow `phraseRwDoms` (~76 types on Genesis!):
        let allDoms := spec'.decls.map (·.1) ++ [defConflictDom, evSupportDom, evRebutDom, evFindingPosDom, evFindingNegDom, "$occ"]
        let candBatched : StepSlice := {
          useFull := false
          resolveDoms := phraseRwDoms
          readWriteDoms := allDoms
          coneDoms := allDoms
          strataBatches := groupStrataBatches 14 cur.cfg.strata
        }
        let batchedNext := stepSummarySliced cur candBatched p
        if summariesEquivalent batchedNext fullNext then
          return (candBatched, batchedNext)
        else
          let candBatched2 := { candBatched with resolveDoms := allDoms }
          let batchedNext2 := stepSummarySliced cur candBatched2 p
          if summariesEquivalent batchedNext2 fullNext then return (candBatched2, batchedNext2)
          else return ({ useFull := true }, fullNext)
    | none =>
      return ({ useFull := true }, fullNext)

/-- Synthesize a verified per-invariant `InvariantSlice` (`#74`). -/
def computeVerifiedInvSlice (s : Summary) : InvariantSlice × Summary :=
  let fullV := addViolated s
  if s.cfg.spec.invariants.isEmpty then
    ({ useFull := false, perInv := [] }, s)
  else
    let perInv := s.cfg.spec.invariants.map fun invId =>
      (invId, backwardReadClosure s.cfg.spec [invId])
    let cand : InvariantSlice := { useFull := false, perInv }
    let slicedV := addViolatedSliced cand s
    if slicedV.violated == fullV.violated then (cand, slicedV)
    else ({ useFull := true }, fullV)

/-- Group consecutive surface `Decl`s belonging to the same `DomId` (e.g. `.typeDecl d` + `.typeExt d`),
and split large `.decls` blocks (or large `{ +f1. ... +fn. }` Genesis blocks) into verified
sub-items of bounded size so no single kernel step exceeds memory caps (`#74`). -/
partial def groupAtomicDecls : List Decl → List (List Decl)
  | [] => []
  | d :: rest =>
    let dName := d.name
    if dName.isEmpty then [d] :: groupAtomicDecls rest
    else
      let rec takeSame : List Decl → List Decl × List Decl
        | [] => ([], [])
        | x :: xs =>
          match x.stripPos with
          | .typeExt xName _ _ | .amendInstall xName _ | .amendMigrate xName _ =>
            if xName == dName then
              let (g, rem) := takeSame xs
              (x :: g, rem)
            else ([], x :: xs)
          | _ => ([], x :: xs)
      let (same, rem) := takeSame rest
      (d :: same) :: groupAtomicDecls rem

/-- Whether an atomic `Decl` group is a pure non-derived carrier `Fact`/`Function`/`Var`/`Param`
that `executeDecls` always inserts in Pass 1 before any rule/derivation/effect compilation. -/
def isPureCarrierGroup (grp : List Decl) : Bool :=
  match grp.map Decl.stripPos with
  | [.param ..] => true
  | [.typeDecl _ ts, .typeExt _ mcs _] =>
    (match ts.kind with | .fact fs => !fs.invariant | .duty _ | .event _ => true | _ => false) &&
    ts.derivation.isEmpty && ts.conditions.isEmpty && ts.domainConstraint.isTrueLit &&
    mcs.all (fun mc => match mc.stripPos with | .strings _ | .ints _ | .open | .close | .fromSpan _ _ => true | _ => false)
  | [.typeDecl _ ts] =>
    (match ts.kind with | .fact fs => !fs.invariant | .duty _ | .event _ => true | _ => false) &&
    ts.derivation.isEmpty && ts.conditions.isEmpty && ts.domainConstraint.isTrueLit
  | _ => false

/-- Extract pure initial `.typeDecl` skeletons for `Fact` and `Duty` declarations whose
`domain` has no constraint (`domainConstraint.isTrueLit`), leaving their `.typeExt` rule
clauses in place (`#74`: breaks forward references like `Power -> Duty` inside a block so
every rule group splits down to <= 3 rules and stays far below memory caps!). -/
def extractDutySkeletonSplit (ds : List Decl) : Option (List Decl × List Decl) :=
  let isDutySkel (rawD : Decl) : Bool :=
    match rawD.stripPos with
    | .typeDecl _ ts =>
      ts.derivation.isEmpty && ts.conditions.isEmpty && ts.domainConstraint.isTrueLit &&
      (match ts.kind with | .duty _ => true | _ => false)
    | _ => false
  let skeletons := ds.filter isDutySkel
  let remainder := ds.filter (fun d => !isDutySkel d)
  if skeletons.isEmpty || remainder.isEmpty then none else some (skeletons, remainder)

/-- Whether an atomic `Decl` group is a `Clause` or `Document` metadata item (zero types/saturation). -/
def isClauseOrDocGroup (grp : List Decl) : Bool :=
  grp.all fun d => match d.stripPos with | .clause _ | .document .. => true | _ => false

/-- Pure static declaration-block splitter (`#74`): splits `.decls ds` using `resolvePhrase` +
`Stratify.strata` only (zero state saturation during candidate probing!), trying clean atomic
prefix cuts first and hoisting `.duty` skeletons only as a fallback when a rule forward-references
a later `Duty` in the same block. -/
partial def splitDeclBlock (curSpec : Spec) (template : Item) (ds : List Decl) : Spec × List Item :=
  let rawGroups := groupAtomicDecls ds
  let isLight := (rawGroups.take 20).all (fun g => isPureCarrierGroup g || isClauseOrDocGroup g)
  let hasHugeAst := rawGroups.any (fun g => (reprStr g).length > 5500)
  let leafLimit := if isLight then 32 else if hasHugeAst then 2 else 9
  if rawGroups.length <= leafLimit then
    match resolvePhrase curSpec (.decls ds) with
    | .ok (sp', _, _) => (sp', [{ template with val := .inr (.decls ds) }])
    | .error _ => (curSpec, [{ template with val := .inr (.decls ds) }])
  else
    let fullSpec? := match resolvePhrase curSpec (.decls ds) with
      | .ok (sp', _, ws) => if ws.isEmpty then some sp' else none
      | .error _ => none
    match fullSpec? with
    | none => (curSpec, [{ template with val := .inr (.decls ds) }])
    | some fullSpec =>
      -- Also try hoisting pure carrier groups (`Fact`/`Function`/`Var`/`Param`) to the front first
      let (carriers, nonCarriers) := rawGroups.partition isPureCarrierGroup
      let groups :=
        if !carriers.isEmpty && !nonCarriers.isEmpty && reprStr (rawGroups.take carriers.length) != reprStr carriers then
          let reord := (carriers ++ nonCarriers).flatten
          match resolvePhrase curSpec (.decls reord) with
          | .ok (sp', _, ws) =>
            if ws.isEmpty && (Stratify.strata sp').isOk && sp'.decls.length == fullSpec.decls.length then
              carriers ++ nonCarriers
            else rawGroups
          | .error _ => rawGroups
        else rawGroups
      let headLight := (groups.take 20).all (fun g => isPureCarrierGroup g || isClauseOrDocGroup g)
      let headHuge := (groups.take 5).any (fun g => (reprStr g).length > 5500)
      let minCut := if headLight then min 28 (groups.length - 1) else if headHuge then 1 else min 8 (groups.length - 1)
      let maxCut := min groups.length (if headLight then minCut + 10 else minCut + 4)
      let splitK? : Option (Nat × Spec) := Id.run do
        let mut found : Option (Nat × Spec) := none
        for k in [minCut : maxCut] do
          if found.isNone then
            let preDecls := (groups.take k).flatten
            let sufDecls := (groups.drop k).flatten
            if !preDecls.isEmpty && !sufDecls.isEmpty then
              match resolvePhrase curSpec (.decls preDecls) with
              | .error _ => pure ()
              | .ok (midSpec, _, ws1) =>
                if ws1.isEmpty && (Stratify.strata midSpec).isOk then
                  match resolvePhrase midSpec (.decls sufDecls) with
                  | .ok (finSpec, _, ws2) =>
                    if ws2.isEmpty && (Stratify.strata finSpec).isOk &&
                       finSpec.decls.length == fullSpec.decls.length then
                      found := some (k, midSpec)
                  | .error _ => pure ()
        return found
      match splitK? with
      | some (k, midSpec) =>
        let preItem : Item := { template with val := .inr (.decls ((groups.take k).flatten)) }
        let (finSpec, sufItems) := splitDeclBlock midSpec template ((groups.drop k).flatten)
        (finSpec, preItem :: sufItems)
      | none =>
        -- Fallback when an early rule forward-references a later `Duty` in `groups` (`draw-sortition-panel -> decide-tier-due`)
        let flatGroups := groups.flatten
        match extractDutySkeletonSplit flatGroups with
        | none => (fullSpec, [{ template with val := .inr (.decls ds) }])
        | some (skels, rem) =>
          match resolvePhrase curSpec (.decls skels) with
          | .error _ => (fullSpec, [{ template with val := .inr (.decls ds) }])
          | .ok (midSpec, _, ws1) =>
            if !ws1.isEmpty || !(Stratify.strata midSpec).isOk then
              (fullSpec, [{ template with val := .inr (.decls ds) }])
            else match resolvePhrase midSpec (.decls rem) with
              | .ok (finSpec, _, ws2) =>
                if ws2.isEmpty && (Stratify.strata finSpec).isOk &&
                   finSpec.decls.length == fullSpec.decls.length then
                  let (ms, skelItems) := splitDeclBlock curSpec template skels
                  let (fs, remItems) := splitDeclBlock ms template rem
                  (fs, skelItems ++ remItems)
                else (fullSpec, [{ template with val := .inr (.decls ds) }])
              | .error _ => (fullSpec, [{ template with val := .inr (.decls ds) }])

partial def splitLargeItems (cur : Summary) : List Item → List Item
  | [] => []
  | it :: rest =>
    match it.val with
    | .inr (.decls ds) =>
      let (_, declItems) := splitDeclBlock cur.cfg.spec it ds
      let cur' := declItems.foldl stepItem cur
      declItems ++ splitLargeItems cur' rest
    | _ =>
      let nxt := stepItem cur it
      it :: splitLargeItems nxt rest

end Charter.Prove
