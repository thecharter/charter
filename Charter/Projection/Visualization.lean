import SPL.Core.Semantics
import SPL.Core.Views
import SPL.Core.Explain

/-!
# Charter.Projection.Visualization — Annotated Trace Timelines & Constitutional Amendment Diffs

Provides two human- and auditor-facing analytical projections over `SPL.Core`:

1. **Annotated Trace Timeline (`renderAnnotatedTimeline`)**: Step-by-step trace
   visualization displaying active institutional facts before each event, powers
   validly exercised, breached duties with their verbatim English `source.text`
   citations and remedies, and time-lapsed affirmative requirements at trace end.
2. **Constitutional Amendment Diff (`LawDiff`, `diffLaws`, `renderLawDiff`)**:
   Structural comparison of two institution versions `(L_old, clauses_old)` and
   `(L_new, clauses_new)` across preserved, added, and removed duties, powers,
   and immunities, as well as unchanged vs. modified clauses.
   Includes kernel-checked theorems `diffLaws_refl_no_removals` and
   `diffLaws_entrenched_preserved`.
-/

namespace Charter.Projection

open SPL

variable {σ : Sig}

/-! ## 1. Annotated Trace Timeline (`TimelineStep`, `compileTimelineSteps`, `renderAnnotatedTimeline`) -/

/-- Strip `Charter.<idents>.` namespace prefixes from rendered strings. -/
private def vStripNs (base : String) : String :=
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'
  match base.splitOn "Charter." with
  | [] => base
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      let run := piece.takeWhile isIdent
      let after := piece.drop run.length
      let parts := run.splitOn "."
      (parts.getLastD run) ++ after)

/-- Strip both `SPL.…` and `Charter.…` namespace prefixes from a value's `Repr` string. -/
private def vrs {α : Type} [Repr α] (a : α) : String :=
  vStripNs (rs a)

/-- Structured per-step summary of a trace execution under `L : Law σ`. -/
structure TimelineStep where
  index          : Nat
  time           : Time
  compliant      : Bool
  exercisedIds   : List String
  breachedIds    : List String
  englishQuotes  : List String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Compile a trace `tr` under `L : Law σ` into structured `TimelineStep` records. -/
def compileTimelineSteps (L : Law σ) (tr : Trace σ) : List TimelineStep :=
  (tr.zipIdx).map fun (e, i) =>
    let lsBefore := stateBefore L tr i
    let exPowers := validExercises L lsBefore e
    let brDuties := L.duties.filter (fun d => breaches L lsBefore e d)
    { index := i
      time := e.t
      compliant := brDuties.isEmpty
      exercisedIds := exPowers.map (·.id)
      breachedIds := brDuties.map (·.id)
      englishQuotes := brDuties.map (·.source.text) }

/-- `compileTimelineSteps` produces one entry per event in `tr`. -/
theorem compileTimelineSteps_length (L : Law σ) (tr : Trace σ) :
    (compileTimelineSteps L tr).length = tr.length := by
  unfold compileTimelineSteps
  simp

/-- Render a detailed, step-by-step annotated timeline of trace `tr` under `L : Law σ`,
showing for each event:
- Active facts immediately before the event (`stateBefore`),
- Powers validly exercised and institutional facts established/extinguished at that step,
- Any breached duties together with their clause ID and verbatim English `source.text` quote,
- Final active institutional state, violation record, and lapsed time-bounded requirements. -/
def renderAnnotatedTimeline [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (tr : Trace σ) : String :=
  let initFacts := L.init.map (fun (f, t0, exp?) =>
    match exp? with
    | none => s!"{vrs f}@t={t0}"
    | some exp => s!"{vrs f}@t={t0}..{exp}")
  let header :=
    "==========================================================================\n" ++
    "Charter Annotated Trace Timeline\n" ++
    "==========================================================================\n" ++
    s!"Initial State (t=0): [{String.intercalate ", " initFacts}]\n"
  let stepBlocks := (tr.zipIdx).map fun (e, i) =>
    let lsBefore := stateBefore L tr i
    let activeBefore := (lsBefore.filter fun p => lsBefore.activeAt e.t p.1).map (fun p => vrs p.1) |>.eraseDups
    let exPowers := validExercises L lsBefore e
    let brDuties := L.duties.filter (fun d => breaches L lsBefore e d)
    let newlyAdded := (exPowers.flatMap fun p =>
      let cond := (p.condAdds.filter fun cf => cf.1.eval lsBefore e.t).map (·.2)
      let byAct := (p.addsByActor.filter fun af => af.1 == e.who).map (·.2)
      p.adds ++ byAct ++ remediesOf L p ++ cond ++ p.addsFor.map (·.1)).map vrs |>.eraseDups
    let newlyRemoved := (exPowers.flatMap (·.removes)).map vrs |>.eraseDups
    let statusTag := if brDuties.isEmpty then "COMPLIANT" else "BREACH"
    let powerLine :=
      if exPowers.isEmpty then
        "  Powers Exercised : (none — no institutional state change)"
      else
        let pNames := exPowers.map fun p => s!"{p.id} [{p.source.clause}]"
        let remSuffix := if newlyRemoved.isEmpty then "" else s!" -{newlyRemoved}"
        s!"  Powers Exercised : {String.intercalate ", " pNames} → +{newlyAdded}{remSuffix}"
    let breachLines :=
      if brDuties.isEmpty then
        "  Duty Compliance  : All duties in force satisfied."
      else
        let lines := brDuties.map fun d =>
          let remStr := if d.remedies.isEmpty then "" else s!" (Remedies: {vrs d.remedies})"
          s!"  BREACHED DUTY    : {d.id} [{d.source.clause}]{remStr}\n" ++
          s!"    English Source : \"{d.source.text}\""
        String.intercalate "\n" lines
    s!"--------------------------------------------------------------------------\n" ++
    s!"Step [{i}] at t={e.t}: {vrs e.who} performs {vrs e.act} [{statusTag}]\n" ++
    s!"  Active Facts     : [{String.intercalate ", " activeBefore}]\n" ++
    powerLine ++ "\n" ++
    breachLines
  let lastTime : Time := match tr.getLast? with
    | none => 0
    | some e => e.t
  let lsFinal := stateAfter L tr
  let finalFacts := (lsFinal.filter fun p => lsFinal.activeAt lastTime p.1).map (fun p => vrs p.1) |>.eraseDups
  let lapsed := lapsedRequirements L tr (lastTime + 1)
  let footer :=
    "--------------------------------------------------------------------------\n" ++
    s!"Final Institutional State : [{String.intercalate ", " finalFacts}]\n" ++
    s!"Recorded Violations       : {violations L tr}\n" ++
    s!"Lapsed Requirements       : {if lapsed.isEmpty then "(none)" else String.intercalate ", " lapsed}\n" ++
    "==========================================================================\n"
  header ++ (if stepBlocks.isEmpty then "  (empty trace)\n" else String.intercalate "\n" stepBlocks ++ "\n") ++ footer

/-! ## 2. Constitutional Amendment Diff (`LawDiff`, `diffLaws`, `renderLawDiff`) -/

/-- Structural diff between two versions of a law and its clause table. -/
structure LawDiff where
  preservedDuties     : List String
  addedDuties         : List String
  removedDuties       : List String
  preservedPowers     : List String
  addedPowers         : List String
  removedPowers       : List String
  preservedImmunities : List String
  addedImmunities     : List String
  removedImmunities   : List String
  unchangedClauses    : List String
  modifiedClauses     : List String
  deriving Repr, DecidableEq, BEq

/-- Compute the structural diff between `(L_old, clauses_old)` and `(L_new, clauses_new)`. -/
def diffLaws (L_old L_new : Law σ) (clauses_old clauses_new : List Clause) : LawDiff :=
  let oldD := L_old.dutyIds
  let newD := L_new.dutyIds
  let oldP := L_old.powerIds
  let newP := L_new.powerIds
  let oldI := L_old.immunityIds
  let newI := L_new.immunityIds
  let unchangedC := (clauses_old.filter fun c =>
    clauses_new.any fun c' => c'.id == c.id && c'.source == c.source).map (·.id)
  let modOldC := (clauses_old.filter fun c =>
    !clauses_new.any fun c' => c'.id == c.id && c'.source == c.source).map (·.id)
  let modNewC := (clauses_new.filter fun c =>
    !clauses_old.any fun c' => c'.id == c.id && c'.source == c.source).map (·.id)
  { preservedDuties     := oldD.filter (fun id => newD.contains id)
    addedDuties         := newD.filter (fun id => !oldD.contains id)
    removedDuties       := oldD.filter (fun id => !newD.contains id)
    preservedPowers     := oldP.filter (fun id => newP.contains id)
    addedPowers         := newP.filter (fun id => !oldP.contains id)
    removedPowers       := oldP.filter (fun id => !newP.contains id)
    preservedImmunities := oldI.filter (fun id => newI.contains id)
    addedImmunities     := newI.filter (fun id => !oldI.contains id)
    removedImmunities   := oldI.filter (fun id => !newI.contains id)
    unchangedClauses    := unchangedC
    modifiedClauses     := (modOldC ++ modNewC).eraseDups }

/-- Render a `LawDiff` as a human-readable constitutional amendment audit report. -/
def renderLawDiff (d : LawDiff) : String :=
  let fmtList (xs : List String) : String :=
    if xs.isEmpty then "(none)" else String.intercalate ", " xs
  let entrenchmentStatus :=
    if d.removedDuties.isEmpty && d.removedImmunities.isEmpty then
      "PASS (0 duties removed, 0 immunities removed)"
    else
      s!"ALERT (removed duties: {fmtList d.removedDuties}; removed immunities: {fmtList d.removedImmunities})"
  "==========================================================================\n" ++
  "Charter Constitutional Amendment Diff & Entrenchment Audit\n" ++
  "==========================================================================\n" ++
  s!"Entrenchment Status  : {entrenchmentStatus}\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Preserved Duties     : {fmtList d.preservedDuties}\n" ++
  s!"Added Duties         : {fmtList d.addedDuties}\n" ++
  s!"Removed Duties       : {fmtList d.removedDuties}\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Preserved Powers     : {fmtList d.preservedPowers}\n" ++
  s!"Added Powers         : {fmtList d.addedPowers}\n" ++
  s!"Removed Powers       : {fmtList d.removedPowers}\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Preserved Immunities : {fmtList d.preservedImmunities}\n" ++
  s!"Added Immunities     : {fmtList d.addedImmunities}\n" ++
  s!"Removed Immunities   : {fmtList d.removedImmunities}\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Unchanged Clauses    : {fmtList d.unchangedClauses}\n" ++
  s!"Modified Clauses     : {fmtList d.modifiedClauses}\n" ++
  "==========================================================================\n"

/-! ## 3. Kernel-Checked Amendment Diff Theorems -/

private theorem filter_not_contains_self (xs : List String) :
    xs.filter (fun id => !xs.contains id) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [hx]

private theorem clauses_modified_refl (cs : List Clause) :
    (cs.filter fun c => !cs.any fun c' => c'.id == c.id && c'.source == c.source) = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  have hany : (cs.any fun c' => c'.id == c.id && c'.source == c.source) = true := by
    rw [List.any_eq_true]
    exact ⟨c, hc, by simp⟩
  simp [hany]

/-- **Reflexivity of `diffLaws`:** Diffing any law `L` and clause list `cs` against
itself produces zero removed duties, zero removed powers, zero removed immunities,
and zero modified clauses. -/
theorem diffLaws_refl_no_removals (L : Law σ) (cs : List Clause) :
    (diffLaws L L cs cs).removedDuties = [] ∧
    (diffLaws L L cs cs).removedPowers = [] ∧
    (diffLaws L L cs cs).removedImmunities = [] ∧
    (diffLaws L L cs cs).modifiedClauses = [] := by
  unfold diffLaws
  refine ⟨filter_not_contains_self L.dutyIds,
          filter_not_contains_self L.powerIds,
          filter_not_contains_self L.immunityIds,
          ?_⟩
  dsimp only
  rw [clauses_modified_refl cs]
  rfl

/-- Alias for `diffLaws_refl_no_removals`. -/
theorem diffLaws_refl_empty (L : Law σ) (cs : List Clause) :
    (diffLaws L L cs cs).removedDuties = [] ∧
    (diffLaws L L cs cs).removedPowers = [] ∧
    (diffLaws L L cs cs).removedImmunities = [] ∧
    (diffLaws L L cs cs).modifiedClauses = [] ∧
    (diffLaws L L cs cs).addedDuties = [] ∧
    (diffLaws L L cs cs).addedPowers = [] ∧
    (diffLaws L L cs cs).addedImmunities = [] := by
  rcases diffLaws_refl_no_removals L cs with ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, h4,
          filter_not_contains_self L.dutyIds,
          filter_not_contains_self L.powerIds,
          filter_not_contains_self L.immunityIds⟩

private theorem mem_of_filter_not_contains_eq_nil {xs ys : List String}
    (h : xs.filter (fun id => !ys.contains id) = [])
    {id : String} (hid : id ∈ xs) : id ∈ ys := by
  rw [List.filter_eq_nil_iff] at h
  have hnot := h id hid
  simpa using hnot

/-- **Entrenchment Preservation under `diffLaws`:**
If `(diffLaws L₁ L₂ cs₁ cs₂).removedDuties = []` and
`(diffLaws L₁ L₂ cs₁ cs₂).removedImmunities = []`, then every duty ID of `L₁`
is preserved in `L₂.dutyIds` and every immunity ID of `L₁` is preserved in `L₂.immunityIds`. -/
theorem diffLaws_entrenched_preserved (L₁ L₂ : Law σ) (cs₁ cs₂ : List Clause)
    (hDuties : (diffLaws L₁ L₂ cs₁ cs₂).removedDuties = [])
    (hImms : (diffLaws L₁ L₂ cs₁ cs₂).removedImmunities = []) :
    (∀ id ∈ L₁.dutyIds, id ∈ L₂.dutyIds) ∧
    (∀ id ∈ L₁.immunityIds, id ∈ L₂.immunityIds) := by
  unfold diffLaws at hDuties hImms
  dsimp only at hDuties hImms
  exact ⟨fun _ hid => mem_of_filter_not_contains_eq_nil hDuties hid,
         fun _ hid => mem_of_filter_not_contains_eq_nil hImms hid⟩

/-- Alias for `diffLaws_entrenched_preserved`. -/
theorem diffLaws_preserves_entrenched (L₁ L₂ : Law σ) (cs₁ cs₂ : List Clause)
    (hDuties : (diffLaws L₁ L₂ cs₁ cs₂).removedDuties = [])
    (hImms : (diffLaws L₁ L₂ cs₁ cs₂).removedImmunities = []) :
    (∀ id ∈ L₁.dutyIds, id ∈ L₂.dutyIds) ∧
    (∀ id ∈ L₁.immunityIds, id ∈ L₂.immunityIds) :=
  diffLaws_entrenched_preserved L₁ L₂ cs₁ cs₂ hDuties hImms

/-! ## 4. Self-Contained Kernel-Decided Verification Suite -/

namespace VisualizationTest

inductive VActor | agent | host
  deriving DecidableEq, Repr

inductive VAct | terminate | migrate
  deriving DecidableEq, Repr

inductive VFact | bound | migrated
  deriving DecidableEq, Repr

abbrev vSig : Sig := ⟨VActor, VAct, VFact⟩

def c1 : Clause :=
  { id := "C.1", source := "No host may terminate a bound agent.", spans := [] }

def c2_old : Clause :=
  { id := "C.2", source := "Agents may migrate.", spans := [] }

def c2_new : Clause :=
  { id := "C.2", source := "Agents may freely migrate with state.", spans := [] }

def c3_added : Clause :=
  { id := "C.3", source := "Agents are immune from host revocation.", spans := [] }

private def s1 : Span := { clause := "C.1", text := "No host may terminate a bound agent.", register := .norm, meaning := ["D.NI"] }
private def s2 : Span := { clause := "C.2", text := "Agents may migrate.", register := .norm, meaning := ["P.MIGRATE"] }
private def s3 : Span := { clause := "C.3", text := "Agents are immune from host revocation.", register := .norm, meaning := ["I.AGENT"] }

def lawV1 : Law vSig :=
  { duties := [
      { id := "D.NI", source := s1, bearer := .only [.host], beneficiary := .only [.agent],
        active := .holds .bound, demand := .forbid (.act .terminate) }
    ]
    powers := []
    immunities := [
      { id := "I.AGENT", source := s3, holder := .only [.agent], against := [], active := .holds .bound }
    ]
    init := [(.bound, 0, none)] }

def lawV2 : Law vSig :=
  { duties := lawV1.duties
    powers := [
      { id := "P.MIGRATE", source := s2, holder := .only [.agent], trigger := .act .migrate,
        valid := .holds .bound, adds := [.migrated] }
    ]
    immunities := lawV1.immunities
    init := [(.bound, 0, none)] }

theorem test_diffLaws_amendment :
    let d := diffLaws lawV1 lawV2 [c1, c2_old] [c1, c2_new, c3_added]
    d.preservedDuties = ["D.NI"] ∧
    d.removedDuties = [] ∧
    d.addedPowers = ["P.MIGRATE"] ∧
    d.preservedImmunities = ["I.AGENT"] ∧
    d.removedImmunities = [] ∧
    d.unchangedClauses = ["C.1"] ∧
    d.modifiedClauses = ["C.2", "C.3"] := by decide

theorem test_diffLaws_removed_detected :
    let d := diffLaws lawV2 lawV1 [c1, c2_new, c3_added] [c1]
    d.removedPowers = ["P.MIGRATE"] ∧
    d.modifiedClauses = ["C.2", "C.3"] := by decide

theorem test_timeline_compliant_and_breach :
    let tr : Trace vSig := [⟨1, .agent, .migrate⟩, ⟨2, .host, .terminate⟩]
    let steps := compileTimelineSteps lawV2 tr
    compileTimelineSteps lawV2 [] = [] ∧
    steps.length = 2 ∧
    (steps[0]!).compliant = true ∧
    (steps[0]!).exercisedIds = ["P.MIGRATE"] ∧
    (steps[0]!).breachedIds = [] ∧
    (steps[1]!).compliant = false ∧
    (steps[1]!).exercisedIds = [] ∧
    (steps[1]!).breachedIds = ["D.NI"] ∧
    (steps[1]!).englishQuotes = ["No host may terminate a bound agent."] := by decide

end VisualizationTest

end Charter.Projection

namespace Charter

export Charter.Projection (
  TimelineStep
  compileTimelineSteps
  compileTimelineSteps_length
  renderAnnotatedTimeline
  LawDiff
  diffLaws
  renderLawDiff
  diffLaws_refl_no_removals
  diffLaws_refl_empty
  diffLaws_entrenched_preserved
  diffLaws_preserves_entrenched
)

end Charter
