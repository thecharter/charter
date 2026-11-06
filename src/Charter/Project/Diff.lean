import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Artifact.Format

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

structure DiffReport where
  oldFile              : String
  newFile              : String
  clauseChanges        : List ClauseDiffEntry
  ruleChanges          : List RuleDiffEntry
  scenarioChanges      : List ScenarioDiffEntry
  entrenchedViolations : List DomId
  reviewRequiredCount  : Nat
  deriving Repr

/-- Normalize a `TypeSpec` structurally for semantic comparison (ignoring `spans` so pure
provenance re-quoting is distinguished from `CIR` rule logic changes). -/
def semanticRepr (t : TypeSpec) : String :=
  reprStr { t with spans := [] }

def evalScenarioVerdicts (phrases : List Phrase) : Spec × List (String × String) := Id.run do
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
  return (cfg.spec, scenResults)

def computeDiff (oldFile newFile : String) (oldPhrases newPhrases : List Phrase) : DiffReport :=
  let (oldSpec, oldScens) := evalScenarioVerdicts oldPhrases
  let (newSpec, newScens) := evalScenarioVerdicts newPhrases
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
  { oldFile, newFile, clauseChanges, ruleChanges, scenarioChanges := scenChanges,
    entrenchedViolations, reviewRequiredCount := reviewReqCnt }

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
      Json.mkObj [("scenario", Json.str sc.name), ("old", Json.str sc.oldVerdict), ("new", Json.str sc.newVerdict)]).toArray)
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
  let eLines := r.entrenchedViolations.map fun eid =>
    s!"  [ENTRENCHED-VIOLATION] entrenched protection `{eid}` modified or removed"
  "\n".intercalate (hdr :: (cLines ++ rLines ++ sLines ++ eLines))

end Charter.Project
