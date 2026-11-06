import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Core.Transition

/-!
# Charter.Cli.Explain — Structured `ReasonGraph` & Audience-Scoped Redaction (`D22`, `G3.2`, `T43`)

Implements `charter explain <expr> <file.charter> [--scenario <name>] [--audience <role>] [--out json]`:
1. Evaluates `<file.charter>` (and optional `--scenario <name>`) to obtain `(Spec, State)`.
2. Resolves `<expr>` and constructs a structured `ReasonGraph` DAG (`Core/Evidence.lean`) with:
   - rule ID and verbatim `From` English spans,
   - premise statuses and tendered `Evidence` / `Finding` chains,
   - active and `Unless`-defeated `Immunity` / `Except under` nodes,
   - hypothetically verified single-condition counterfactuals (`"what single condition flip changes lawful/valid?"`),
3. Applies `ReasonGraph.redactForAudience` (`redactForAudience_preserves_verdict`, `T43`).
-/

namespace Charter.Cli

open Lean (Json)

structure ExplainOpts where
  expr     : Option String := none
  file     : Option String := none
  scenario : Option String := none
  audience : Option String := none
  json     : Bool := false

def parseExplainArgs : List String → ExplainOpts → Except String ExplainOpts
  | [], o => .ok o
  | "--scenario" :: s :: rest, o => parseExplainArgs rest { o with scenario := some s }
  | ["--scenario"], _ => .error "--scenario needs a scenario name"
  | "--audience" :: a :: rest, o => parseExplainArgs rest { o with audience := some a }
  | ["--audience"], _ => .error "--audience needs a role/audience name"
  | "--out" :: "json" :: rest, o => parseExplainArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseExplainArgs rest { o with json := false }
  | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
  | ["--out"], _ => .error "--out needs json or text"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.expr.isNone then parseExplainArgs rest { o with expr := some a }
    else if o.file.isNone then parseExplainArgs rest { o with file := some a }
    else .error s!"unexpected extra argument {a}"

-- Collect all `(DomId, Args)` applications appearing inside a checked `Term`.
mutual
def collectTermApps : Term → List (DomId × Args)
  | .app d args => (d, args) :: collectArgsApps args
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .project a _ | .tag a _ | .untag a =>
    collectTermApps a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b =>
    collectTermApps a ++ collectTermApps b
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t =>
    collectTermApps t
  | .boolLit _ | .intLit _ | .stringLit _ | .ref _ | .currentTime => []

def collectArgsApps : Args → List (DomId × Args)
  | .pos ts => collectTermListApps ts
  | .named ms => collectModApps ms

def collectTermListApps : List Term → List (DomId × Args)
  | [] => []
  | t :: ts => collectTermApps t ++ collectTermListApps ts

def collectModApps : List (Var × Term) → List (DomId × Args)
  | [] => []
  | (_, t) :: ms => collectTermApps t ++ collectModApps ms
end

/-- Hypothetically flip a premise `pTe` to holding (`Established` / `true`) in `state` to test
whether flipping that single condition changes `lawful` or `valid` to `yes`. -/
def hypotheticalEstablish (spec : Spec) (state : State) (pTe : Tagged) : State :=
  match spec.findDecl pTe.2 with
  | some ts =>
    if ts.isEvidencedFact then
      let fEntry : Tagged := (.prod [pTe, (.str "hypothetical", "string")], evFindingPosDom)
      state.create fEntry none (.asserted (state.step + 1))
    else
      state.create pTe none (.asserted (state.step + 1))
  | none => state.create pTe none (.asserted (state.step + 1))

/-- Build an unredacted `ReasonGraph` for an evaluated instance `te` in `(spec, state)`. -/
def buildReasonGraph (spec : Spec) (state : State) (te : Tagged) : ReasonGraph :=
  let specIdx := spec.buildIndex
  let ctx := Ctx.ofIdx spec specIdx state
  let runM {α} (m : M α) (subs : Subs := []) : List α :=
    match m.run ctx subs with | .ok xs => xs | .error _ => []
  match spec.findDecl te.2 with
  | none =>
    { subject := te.pp, lawful := .no, valid := .no }
  | some tspec =>
    let binds := Tagged.bindings tspec.domain te
    match tspec.kind with
    | .act a =>
      let (lTri, vTri, unmetRaw) := (runM (M.evalActTri M.fuel te)).headD (.no, .no, [])
      let unmetMeta : List (String × EvidenceStatus × Bool × List String) :=
        unmetRaw.map fun (uTe, st) =>
          match spec.findDecl uTe.2 with
          | some { kind := .fact fs, .. } => (uTe.pp, st, fs.confidential, fs.audiences)
          | _ => (uTe.pp, st, false, [])
      let hwTerms := tspec.derivation.filterMap fun | .holdsWhen c => some c | _ => none
      let allGuardTerms := hwTerms ++ tspec.conditions ++ a.validWhen
      let rawApps := (allGuardTerms.flatMap collectTermApps).foldl
        (fun acc p => if acc.any (fun q => q.1 == p.1 && reprStr q.2 == reprStr p.2) then acc else acc ++ [p]) []
      let premiseInsts : List Tagged := rawApps.flatMap fun (d, args) =>
        runM (M.whenTagged (M.eval M.fuel (.app d args)) pure) binds
      let dedupPremises := premiseInsts.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []
      let premiseNodes : List ReasonNode := dedupPremises.filterMap fun pTe =>
        if pTe == te then none
        else match spec.findDecl pTe.2 with
          | none => none
          | some pts =>
            match pts.kind with
            | .fact fs =>
              if fs.evidenced then
                let st := state.evidenceStatus pTe
                let srcs := state.evidenceSources pTe
                let srcDetail := if srcs.isEmpty then "no tendered evidence"
                  else ", ".intercalate (srcs.map fun (k, s, n) =>
                    if s.isEmpty then s!"{k}@step{n}" else s!"{k} by {showString s} @step{n}")
                some {
                  id := pTe.pp
                  kind := "evidence"
                  status := st.asString
                  spans := pts.spans
                  confidential := fs.confidential
                  allowedAudiences := fs.audiences
                  detail := srcDetail
                }
              else
                let h := state.holds pTe
                let orig := match state.lookup pTe with
                  | some i => i.origin.render
                  | none => "unassigned closed fact"
                some {
                  id := pTe.pp
                  kind := "premise"
                  status := if h then "yes" else "no"
                  spans := pts.spans
                  confidential := fs.confidential
                  allowedAudiences := fs.audiences
                  detail := orig
                }
            | _ => none
      -- Inspect immunities (active blocks vs. `Unless`-defeated immunities)
      let (immNodes, defeated) : List ReasonNode × List String :=
        match tspec.domain, te.1, a.hasRecipient with
        | _, .prod (_ :: recipient :: _), true =>
          let entries := spec.immunitiesAgainst te.2
          entries.foldr (fun (imDom, imTs, imSpec) (accN, accD) =>
            let heldIms := state.holdsList.filter (fun q => q.2 == imDom)
            let matched := heldIms.filter fun imTe =>
              match imTe.1 with
              | .prod (holder :: _) => holder.1 == recipient.1
              | _ => false
            matched.foldr (fun imTe (nL, dL) =>
              let imBinds := Tagged.bindings imTs.domain imTe
              let unlessHeld := imSpec.unlessConds.any fun uc =>
                (runM (M.whenBool (M.eval M.fuel uc) pure) imBinds).any id
              if unlessHeld then
                ({ id := imTe.pp, kind := "defeated-exception", status := "defeated",
                   spans := imTs.spans, detail := s!"Immunity {imDom} defeated by Unless condition" } :: nL,
                 s!"Immunity {imTe.pp} defeated by Unless" :: dL)
              else
                ({ id := imTe.pp, kind := "immunity", status := "blocks-validity",
                   spans := imTs.spans, detail := s!"Immunity {imDom} protects recipient {Tagged.pp recipient}" } :: nL,
                 dL)) (accN, accD)) ([], [])
        | _, _, _ => ([], [])
      -- Single-condition counterfactuals verified by hypothetical re-evaluation
      let cfs : List Counterfactual := dedupPremises.filterMap fun pTe =>
        if pTe == te then none
        else
          let (conf, auds, curSt) := match spec.findDecl pTe.2 with
            | some { kind := .fact fs, .. } =>
              if fs.evidenced then (fs.confidential, fs.audiences, (state.evidenceStatus pTe).asString)
              else (fs.confidential, fs.audiences, if state.holds pTe then "yes" else "no")
            | _ => (false, [], if state.holds pTe then "yes" else "no")
          if curSt == "yes" || curSt == "established" then none
          else
            let sHyp := hypotheticalEstablish spec state pTe
            let ctxHyp := Ctx.ofIdx spec specIdx sHyp
            match (M.evalActTri M.fuel te).run ctxHyp [] with
            | .ok [(lH, vH, _)] =>
              if vTri != .yes && vH == .yes then
                some { condition := pTe.pp, currentStatus := curSt, neededStatus := "established",
                       changesJudgment := "valid", confidential := conf, allowedAudiences := auds }
              else if lTri != .yes && lH == .yes then
                some { condition := pTe.pp, currentStatus := curSt, neededStatus := "established",
                       changesJudgment := "lawful", confidential := conf, allowedAudiences := auds }
              else none
            | _ => none
      let ruleKind := if a.isFinding then "finding" else if a.isPower then "power" else "act"
      let childIds := premiseNodes.map (·.id) ++ immNodes.map (·.id)
      let ruleNode : ReasonNode := {
        id := te.2
        kind := ruleKind
        status := s!"lawful={lTri.asString}, valid={vTri.asString}"
        spans := tspec.spans
        detail := match a.finding with
          | some fs => s!"Finding standard={fs.standard}"
          | none => s!"{ruleKind} rule {te.2}"
        children := childIds
      }
      let decNode : ReasonNode := {
        id := te.pp
        kind := "decision"
        status := s!"lawful={lTri.asString}, valid={vTri.asString}"
        spans := tspec.spans
        detail := s!"evaluated at time={state.time}"
        children := [te.2]
      }
      { subject := te.pp
        occurred := "hypothetical"
        lawful := lTri
        valid := vTri
        unmetEvidence := unmetMeta
        defeatedExceptions := defeated
        counterfactuals := cfs
        nodes := decNode :: ruleNode :: (premiseNodes ++ immNodes) }
    | .fact fs =>
      if fs.evidenced then
        let st := state.evidenceStatus te
        let tri := TriBool.ofEvidenceStatus st
        let srcs := state.evidenceSources te
        let detail := if srcs.isEmpty then "no tendered evidence"
          else ", ".intercalate (srcs.map fun (k, s, n) => s!"{k} by {showString s} @step{n}")
        let node : ReasonNode := {
          id := te.pp, kind := "evidence", status := st.asString, spans := tspec.spans,
          confidential := fs.confidential, allowedAudiences := fs.audiences, detail
        }
        { subject := te.pp, lawful := tri, valid := tri,
          unmetEvidence := if tri == .undetermined then [(te.pp, st, fs.confidential, fs.audiences)] else [],
          nodes := [node] }
      else
        let h := (runM (M.isHolds M.fuel te)).headD false
        let tri := TriBool.ofBool h
        let orig := match state.lookup te with | some i => i.origin.render | none => "not holding"
        { subject := te.pp, lawful := tri, valid := tri,
          nodes := [{ id := te.pp, kind := "fact", status := tri.asString, spans := tspec.spans,
                      confidential := fs.confidential, allowedAudiences := fs.audiences, detail := orig }] }
    | _ =>
      let h := (runM (M.isHolds M.fuel te)).headD false
      let tri := TriBool.ofBool h
      { subject := te.pp, lawful := tri, valid := tri,
        nodes := [{ id := te.pp, kind := tspec.kind.lowerName, status := tri.asString, spans := tspec.spans }] }

def ReasonNode.toJson (n : ReasonNode) : Json :=
  Json.mkObj [
    ("id", Json.str n.id),
    ("kind", Json.str n.kind),
    ("status", Json.str n.status),
    ("confidential", Json.bool n.confidential),
    ("detail", Json.str n.detail),
    ("spans", Json.arr (n.spans.map fun (c, s) => Json.mkObj [("clause", Json.str c), ("text", Json.str s)]).toArray),
    ("children", Json.arr (n.children.map Json.str).toArray)
  ]

def Counterfactual.toJson (cf : Counterfactual) : Json :=
  Json.mkObj [
    ("condition", Json.str cf.condition),
    ("currentStatus", Json.str cf.currentStatus),
    ("neededStatus", Json.str cf.neededStatus),
    ("changesJudgment", Json.str cf.changesJudgment)
  ]

def ReasonGraph.toJson (rg : ReasonGraph) : Json :=
  Json.mkObj [
    ("kind", Json.str "reason-graph"),
    ("subject", Json.str rg.subject),
    ("occurred", Json.str rg.occurred),
    ("lawful", Json.str rg.lawful.asString),
    ("valid", Json.str rg.valid.asString),
    ("redactedCount", Json.num rg.redactedCount),
    ("unmetEvidence", Json.arr (rg.unmetEvidence.map fun (lbl, st, _, _) =>
      Json.mkObj [("fact", Json.str lbl), ("status", Json.str st.asString)]).toArray),
    ("defeatedExceptions", Json.arr (rg.defeatedExceptions.map Json.str).toArray),
    ("counterfactuals", Json.arr (rg.counterfactuals.map Counterfactual.toJson).toArray),
    ("nodes", Json.arr (rg.nodes.map ReasonNode.toJson).toArray)
  ]

def ReasonGraph.renderText (rg : ReasonGraph) : String :=
  let hdr := s!"explain {rg.subject}: occurred={rg.occurred}  lawful={rg.lawful.asString}  valid={rg.valid.asString}" ++
    (if rg.redactedCount > 0 then s!"  (redacted={rg.redactedCount})" else "")
  let unmetLines := if rg.unmetEvidence.isEmpty then []
    else ["  unmet evidence: " ++ ", ".intercalate (rg.unmetEvidence.map fun (l, st, _, _) => s!"{l} ({st.asString})")]
  let defLines := rg.defeatedExceptions.map (fun d => s!"  defeated exception: {d}")
  let cfLines := rg.counterfactuals.map fun cf =>
    s!"  counterfactual: if {cf.condition} were {cf.neededStatus} (currently {cf.currentStatus}), `{cf.changesJudgment}` becomes yes"
  let nodeLines := rg.nodes.map fun n =>
    let sp := if n.spans.isEmpty then "" else " [" ++ ", ".intercalate (n.spans.map (·.1)) ++ "]"
    s!"  [{n.kind}] {n.id} => {n.status}{sp}: {n.detail}"
  "\n".intercalate (hdr :: (unmetLines ++ defLines ++ cfLines ++ nodeLines))

/-- Run `items` to reach the target state (either top-level end state or end of `scenario?`). -/
def evalToExplainState (items : List Located) (scenario? : Option String) : Except String Config := Id.run do
  let mut cfg : Config := {}
  let mut foundScenario : Option Config := none
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario name ps _) =>
      if scenario? == some name then
        let mut scCfg := cfg
        for p in ps do
          let (c', _) := runPhrase scCfg p
          scCfg := c'
        foundScenario := some scCfg
    | .inr p =>
      let (c', _) := runPhrase cfg p
      cfg := c'
  match scenario? with
  | none => .ok cfg
  | some want =>
    match foundScenario with
    | some sc => .ok sc
    | none => .error s!"unknown scenario `{want}`"

/-- `charter explain <expr> <file.charter> [--scenario <name>] [--audience <role>] [--out json]` -/
def explainCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter explain <expr> <file.charter> [--scenario <name>] [--audience <role>] [--out json]"
  let opts ← match parseExplainArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter explain: {e}\n{usage}"; return 2
  let (exprSrc, file) ← match opts.expr, opts.file with
    | some e, some f => pure (e, f)
    | _, _ => IO.eprintln usage; return 2
  let (items, loadDiags) ← loadProgram file
  let mut hasErr := false
  for d in loadDiags do
    if d.isError then
      IO.eprintln d.render
      hasErr := true
  if hasErr then return 1
  let cfg ← match evalToExplainState items opts.scenario with
    | .ok c => pure c
    | .error e => IO.eprintln s!"charter explain: {e}"; return 1
  let rawTerm ← match parseSource (exprSrc ++ ".") with
    | .ok [it] =>
      match it.val with
      | .inr (.trigger _ t _) => pure t
      | .inr (.query t) => pure t
      | _ => IO.eprintln s!"charter explain: `{exprSrc}` is not an instance expression"; return 2
    | _ => IO.eprintln s!"charter explain: could not parse `{exprSrc}`"; return 2
  let (_, cp, _) ← match resolvePhrase cfg.spec (.why rawTerm) with
    | .ok r => pure r
    | .error ds =>
      for d in ds do IO.eprintln d.render
      return 1
  let tes ← match cp with
    | .why xs t' =>
      let ctx := Ctx.of cfg.spec cfg.state
      match (M.foreach M.fuel xs (M.whenTagged (M.eval M.fuel t') pure)).run ctx [] with
      | .ok vss => pure vss.flatten
      | .error e => IO.eprintln s!"charter explain: {e.message}"; return 1
    | _ => return 1
  match tes with
  | [] =>
    IO.eprintln s!"charter explain: `{exprSrc}` produced no instance"
    return 1
  | _ =>
    for te in tes do
      let rawRg := buildReasonGraph cfg.spec cfg.state te
      let rg := rawRg.redactForAudience opts.audience
      if opts.json then IO.println (ReasonGraph.toJson rg).compress
      else IO.println (ReasonGraph.renderText rg)
    return 0

end Charter.Cli
