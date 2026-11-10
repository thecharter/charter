import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Artifact.Format
import Charter.Verify.Explorer

/-!
# Charter.Project.Diff — Three-View Semantic & Provenance Diff (`D11`, `D25`, `G3.5`, `T38`)

Compares two Charter programs (`old` vs. `new`) across three orthogonal views (`docs/rfc.md` §4.5):
1. **English & Provenance Diff**: added, removed, and text-drifted `Clause`s and `Document`s.
2. **`CIR` Rule & Priority Diff**: added, removed, and semantically modified declarations,
   specifically flagging **`REVIEW-REQUIRED (T38)`** whenever a rule's formal `CIR` definition
   changes while its grounding `Clause` English text remains unchanged!
3. **Differential Verdict & Entrenchment Check**: compares scenario outcomes, top-level
   transition judgments, and verifies whether any `Entrenched Invariant` or entrenchment
   `Immunity` of `old` was removed or modified in `new`.
-/

namespace Charter.Project

open Lean (Json)

structure ClauseDiffEntry where
  id     : ClauseId
  change : String -- "added" | "removed" | "modified"
  detail : String
  deriving Repr

structure RuleDiffEntry where
  id             : DomId
  kind           : String
  change         : String -- "added" | "removed" | "modified"
  reviewRequired : Bool   -- T38: formal semantics changed while English clause text stayed identical!
  clauses        : List ClauseId
  deriving Repr

structure ScenarioDiffEntry where
  name       : String
  oldVerdict : String
  newVerdict : String
  deriving Repr

/-- Concrete state/trace witness where `(lawful, valid)` or duty violation diverges (`charter diff --impact`, `D44`). -/
structure ImpactWitness where
  subject     : String
  kind        : String -- "act" | "duty"
  trace       : List String
  oldJudgment : String
  newJudgment : String
  deriving Repr

structure DiffReport where
  oldFile              : String
  newFile              : String
  clauseChanges        : List ClauseDiffEntry
  ruleChanges          : List RuleDiffEntry
  scenarioChanges      : List ScenarioDiffEntry
  impactWitnesses      : List ImpactWitness := []
  entrenchedViolations : List DomId
  reviewRequiredCount  : Nat
  deriving Repr

/-- Normalize a `TypeSpec` structurally for semantic comparison (ignoring `spans` so pure
provenance re-quoting is distinguished from `CIR` rule logic changes). -/
def semanticRepr (t : TypeSpec) : String :=
  reprStr { t with spans := [] }

def evalScenarioVerdicts (phrases : List Phrase) : Config × List (String × String) := Id.run do
  let mut cfg : Config := {}
  let mut scenResults : List (String × String) := []
  for p in phrases do
    match p with
    | .scenario name ps _ =>
      let mut scCfg := cfg
      let mut errs := 0
      let mut fails := 0
      let mut judgs : List String := []
      for sp in ps do
        let (c', outs) := runPhrase scCfg sp
        scCfg := c'
        for o in outs do
          match o with
          | .diag d => if d.isError then errs := errs + 1
          | .queryRes ok => if !ok then fails := fails + 1
          | .expectRes _ _ ok => if !ok then fails := fails + 1
          | .executed info => judgs := judgs ++ [s!"{info.tagged.2}:{info.lawfulTri.asString}/{info.validTri.asString}"]
          | _ => pure ()
      let summary := s!"errors={errs},failed={fails},steps=[{",".intercalate judgs}]"
      scenResults := scenResults ++ [(name, summary)]
    | _ =>
      let (c', _) := runPhrase cfg p
      cfg := c'
  return (cfg, scenResults)

/-- Compare act `(lawful, valid)` and duty `(holds, violated)` judgments at one synchronized `(oldCfg, newCfg)` pair. -/
def collectStateImpactWitnesses (trace : List String) (oldCfg newCfg : Config) : List ImpactWitness :=
  let oldCtx := Ctx.of oldCfg.spec oldCfg.state
  let newCtx := Ctx.of newCfg.spec newCfg.state
  let oldSteps := (Verify.candidateSteps .adversarial [( "duration", [.int 1] )] oldCfg).toOption.getD []
  let newSteps := (Verify.candidateSteps .adversarial [( "duration", [.int 1] )] newCfg).toOption.getD []
  let allActs : List Tagged := ((oldSteps ++ newSteps).filterMap fun
    | .trigger te => some te
    | _ => none).eraseDups
  let actWits : List ImpactWitness := allActs.filterMap fun te =>
    match oldCfg.spec.findDecl te.2, newCfg.spec.findDecl te.2 with
    | some { kind := .act _, .. }, some { kind := .act _, .. } =>
      let evalPair (ctx : Ctx) : String :=
        match (M.ignoreMissingInput (M.evalActTri M.fuel te)).run ctx [] with
        | .ok ((l, v, _) :: _) => s!"lawful={l.asString}, valid={v.asString}"
        | _ => "unavailable"
      let oj := evalPair oldCtx
      let nj := evalPair newCtx
      if oj == nj then none
      else some { subject := te.pp, kind := "act", trace, oldJudgment := oj, newJudgment := nj }
    | _, _ => none
  let allDuties : List Tagged :=
    ((oldCfg.state.holdsList ++ newCfg.state.holdsList).filter fun te =>
      match oldCfg.spec.findDecl te.2, newCfg.spec.findDecl te.2 with
      | some { kind := .duty _, .. }, _ | _, some { kind := .duty _, .. } => true
      | _, _ => false).eraseDups
  let dutyWits : List ImpactWitness := allDuties.filterMap fun te =>
    let dutyStatus (cfg : Config) : String :=
      let h := cfg.state.holds te
      let v := cfg.violatedDuties.contains te
      s!"holds={h}, violated={v}"
    let oj := dutyStatus oldCfg
    let nj := dutyStatus newCfg
    if oj == nj then none
    else some { subject := te.pp, kind := "duty", trace, oldJudgment := oj, newJudgment := nj }
  actWits ++ dutyWits

/-- Bounded breadth-first exploration synthesizing minimal concrete impact witnesses (`D44`). -/
def synthesizeImpactWitnesses (oldInit newInit : Config) (maxDepth : Nat := 2) (maxStates : Nat := 32) :
    List ImpactWitness := Id.run do
  let mut queue : List (List String × Config × Config) := [([], oldInit, newInit)]
  let mut visited : Nat := 0
  let mut found : List ImpactWitness := []
  while !queue.isEmpty && visited < maxStates && found.length < 16 do
    match queue with
    | [] => break
    | (tr, oc, nc) :: rest =>
      queue := rest
      visited := visited + 1
      let wits := collectStateImpactWitnesses tr oc nc
      for w in wits do
        if !found.any (·.subject == w.subject) && found.length < 16 then
          found := found ++ [w]
      if tr.length < maxDepth && visited < maxStates then
        let steps := ((Verify.candidateSteps .adversarial [( "duration", [.int 1] )] oc).toOption.getD []).take 8
        for st in steps do
          match Verify.stepConfig oc st, Verify.stepConfig nc st with
          | .ok oc', .ok nc' =>
            queue := queue ++ [(tr ++ [st.pp], oc', nc')]
          | _, _ => pure ()
  return found

def computeDiff (oldFile newFile : String) (oldPhrases newPhrases : List Phrase)
    (withImpact : Bool := false) : DiffReport :=
  let (oldCfg, oldScens) := evalScenarioVerdicts oldPhrases
  let (newCfg, newScens) := evalScenarioVerdicts newPhrases
  let oldSpec := oldCfg.spec
  let newSpec := newCfg.spec
  -- 1. English clause diff
  let oldClauses := oldSpec.clauses
  let newClauses := newSpec.clauses
  let addedClauses : List ClauseDiffEntry := newClauses.filterMap fun nc =>
    if oldClauses.any (·.id == nc.id) then none
    else some { id := nc.id, change := "added", detail := s!"sha256={Artifact.sha256String nc.source}" }
  let removedClauses : List ClauseDiffEntry := oldClauses.filterMap fun oc =>
    if newClauses.any (·.id == oc.id) then none
    else some { id := oc.id, change := "removed", detail := "clause deleted" }
  let modifiedClauses : List ClauseDiffEntry := newClauses.filterMap fun nc =>
    match oldClauses.find? (·.id == nc.id) with
    | some oc =>
      if oc.source == nc.source then none
      else some { id := nc.id, change := "modified", detail := "English prose changed" }
    | none => none
  let clauseChanges := addedClauses ++ removedClauses ++ modifiedClauses
  -- 2. CIR rule diff + T38 check (formal rule changed while bound Clause English stayed unchanged!)
  let builtins := ["int", "string", "actor"]
  let oldDecls := oldSpec.decls.filter fun (d, _) => !builtins.contains d
  let newDecls := newSpec.decls.filter fun (d, _) => !builtins.contains d
  let clausesForRule (s : Spec) (rid : DomId) (ts : TypeSpec) : List ClauseId :=
    let fromSpans := ts.spans.map (·.1)
    let fromClauses := s.clauses.filter (fun c => c.spans.any (fun sp => sp.meaning.contains rid)) |>.map (·.id)
    (fromSpans ++ fromClauses).eraseDups
  let addedRules : List RuleDiffEntry := newDecls.filterMap fun (d, nt) =>
    if oldDecls.any (·.1 == d) then none
    else some { id := d, kind := nt.kind.lowerName, change := "added", reviewRequired := false,
                clauses := clausesForRule newSpec d nt }
  let removedRules : List RuleDiffEntry := oldDecls.filterMap fun (d, ot) =>
    if newDecls.any (·.1 == d) then none
    else
      let cids := clausesForRule oldSpec d ot
      let unchangedEnglish := !cids.isEmpty && cids.all fun cid =>
        match oldClauses.find? (·.id == cid), newClauses.find? (·.id == cid) with
        | some oc, some nc => oc.source == nc.source
        | _, _ => false
      some { id := d, kind := ot.kind.lowerName, change := "removed", reviewRequired := unchangedEnglish, clauses := cids }
  let modifiedRules : List RuleDiffEntry := newDecls.filterMap fun (d, nt) =>
    match oldDecls.find? (·.1 == d) with
    | none => none
    | some (_, ot) =>
      if semanticRepr ot == semanticRepr nt then none
      else
        let cids := (clausesForRule oldSpec d ot ++ clausesForRule newSpec d nt).eraseDups
        let unchangedEnglish := cids.isEmpty || cids.any fun cid =>
          match oldClauses.find? (·.id == cid), newClauses.find? (·.id == cid) with
          | some oc, some nc => oc.source == nc.source
          | _, _ => false
        some { id := d, kind := nt.kind.lowerName, change := "modified", reviewRequired := unchangedEnglish, clauses := cids }
  let ruleChanges := addedRules ++ removedRules ++ modifiedRules
  -- 3. Differential scenario verdicts
  let scenChanges : List ScenarioDiffEntry := newScens.filterMap fun (name, newV) =>
    match oldScens.find? (·.1 == name) with
    | some (_, oldV) =>
      if oldV == newV then none
      else some { name, oldVerdict := oldV, newVerdict := newV }
    | none => none
  -- 4. Entrenchment check (Entrenched Invariants + Against Amend Immunities)
  let entrenchedIds := (oldSpec.entrenchedInvariants ++
    oldSpec.decls.filterMap fun (d, t) =>
      match t.kind with
      | .immunity im => if im.against.contains "Amend" || !im.protects.isEmpty then some d else none
      | _ => none).eraseDups
  let entrenchedViolations := entrenchedIds.filter fun eid =>
    match oldSpec.lookupDecl eid, newSpec.lookupDecl eid with
    | some ot, some nt => semanticRepr ot != semanticRepr nt
    | some _, none => true
    | _, _ => false
  let reviewReqCnt := (ruleChanges.filter (·.reviewRequired)).length
  let impactWits := if withImpact then synthesizeImpactWitnesses oldCfg newCfg else []
  { oldFile, newFile, clauseChanges, ruleChanges, scenarioChanges := scenChanges,
    impactWitnesses := impactWits, entrenchedViolations, reviewRequiredCount := reviewReqCnt }

def DiffReport.toJson (r : DiffReport) : Json :=
  Json.mkObj [
    ("kind", Json.str "diff"),
    ("oldFile", Json.str r.oldFile),
    ("newFile", Json.str r.newFile),
    ("reviewRequiredCount", Json.num r.reviewRequiredCount),
    ("entrenchedViolations", Json.arr (r.entrenchedViolations.map Json.str).toArray),
    ("clauseChanges", Json.arr (r.clauseChanges.map fun c =>
      Json.mkObj [("id", Json.str c.id), ("change", Json.str c.change), ("detail", Json.str c.detail)]).toArray),
    ("ruleChanges", Json.arr (r.ruleChanges.map fun rc =>
      Json.mkObj [("id", Json.str rc.id), ("kind", Json.str rc.kind), ("change", Json.str rc.change),
                  ("reviewRequired", Json.bool rc.reviewRequired),
                  ("clauses", Json.arr (rc.clauses.map Json.str).toArray)]).toArray),
    ("scenarioChanges", Json.arr (r.scenarioChanges.map fun sc =>
      Json.mkObj [("scenario", Json.str sc.name), ("old", Json.str sc.oldVerdict), ("new", Json.str sc.newVerdict)]).toArray),
    ("impactWitnesses", Json.arr (r.impactWitnesses.map fun w =>
      Json.mkObj [("subject", Json.str w.subject), ("kind", Json.str w.kind),
                  ("trace", Json.arr (w.trace.map Json.str).toArray),
                  ("old", Json.str w.oldJudgment), ("new", Json.str w.newJudgment)]).toArray)
  ]

def DiffReport.renderText (r : DiffReport) : String :=
  let hdr := s!"diff {r.oldFile} -> {r.newFile}: {r.clauseChanges.length} clause change(s), {r.ruleChanges.length} CIR rule change(s), {r.scenarioChanges.length} verdict change(s)"
  let cLines := r.clauseChanges.map fun c => s!"  [english:{c.change}] {c.id}: {c.detail}"
  let rLines := r.ruleChanges.map fun rc =>
    let rev := if rc.reviewRequired then " [REVIEW-REQUIRED: formal CIR changed under unchanged English (T38)]" else ""
    let cls := if rc.clauses.isEmpty then "" else s!" (clauses: {", ".intercalate rc.clauses})"
    s!"  [cir:{rc.change}] {rc.kind} {rc.id}{cls}{rev}"
  let sLines := r.scenarioChanges.map fun sc =>
    s!"  [verdict-changed] Scenario {sc.name}: {sc.oldVerdict} -> {sc.newVerdict}"
  let iLines := r.impactWitnesses.map fun w =>
    let trStr := if w.trace.isEmpty then "initial state" else " -> ".intercalate w.trace
    s!"  [impact:{w.kind}] {w.subject} @ ({trStr}): ({w.oldJudgment}) -> ({w.newJudgment})"
  let eLines := r.entrenchedViolations.map fun eid =>
    s!"  [ENTRENCHED-VIOLATION] entrenched protection `{eid}` modified or removed"
  "\n".intercalate (hdr :: (cLines ++ rLines ++ sLines ++ iLines ++ eLines))

end Charter.Project
