import Charter.Cli.Load
import Charter.Cli.Provenance
import Charter.Eval.Interpreter
import Charter.Surface.Pretty
import Lean.Data.Json

/-!
# Charter.Cli.Doc — Institutional Rulebook & Legal Reader's View (`G5.4`, `#64`)

`charter doc <file.charter> [--view rulebook|legal] [--format markdown|html] [--scenario <name>] [-o <out>] [--out json]`
generates either:
- `rulebook` (default): consolidated `Clause` prose, `Default`/`Exception` decision tables,
  Hohfeldian `Power`/`Duty`/`Immunity` standing matrices, and invariants; or
- `legal` (`#64`): authoritative clauses in document order paired directly with the formal
  declarations that cite each passage, with computational completions collapsed — available in
  Markdown or as a 3-pane side-by-side HTML reader (Document | Specification | Scenario Trace).
-/

namespace Charter.Cli

open Lean (Json)

structure DocCliOpts where
  input    : Option String := none
  output   : Option String := none
  view     : String := "rulebook"
  format   : Option String := none
  scenario : Option String := none
  json     : Bool := false

def parseDocArgs : List String → DocCliOpts → Except String DocCliOpts
  | [], o => .ok o
  | "-o" :: p :: rest, o => parseDocArgs rest { o with output := some p }
  | ["-o"], _ => .error "-o needs an output file path"
  | "--view" :: v :: rest, o =>
    if v == "legal" || v == "rulebook" then parseDocArgs rest { o with view := v }
    else .error s!"--view takes `legal` or `rulebook`, not `{v}`"
  | ["--view"], _ => .error "--view needs `legal` or `rulebook`"
  | "--format" :: fmt :: rest, o =>
    if fmt == "markdown" || fmt == "md" || fmt == "html" then parseDocArgs rest { o with format := some fmt }
    else .error s!"--format takes `markdown` or `html`, not `{fmt}`"
  | ["--format"], _ => .error "--format needs `markdown` or `html`"
  | "--scenario" :: sc :: rest, o => parseDocArgs rest { o with scenario := some sc }
  | ["--scenario"], _ => .error "--scenario needs a scenario name"
  | "--out" :: "json" :: rest, o => parseDocArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseDocArgs rest { o with json := false }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.input.isNone then parseDocArgs rest { o with input := some a }
    else .error s!"unexpected extra input {a}"

def htmlEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | _   => acc.push c) ""

/-- Extract formatted surface declaration snippets keyed by declared/extended `DomId`. -/
def collectSurfaceDeclSnippets (items : List Located) : List (DomId × List String) := Id.run do
  let mut out : List (DomId × List String) := []
  let addFor (d : DomId) (snip : String) (acc : List (DomId × List String)) : List (DomId × List String) :=
    match acc.find? (·.1 == d) with
    | some (_, prev) =>
      let merged := if prev.contains snip then prev else prev ++ [snip]
      acc.map fun (k, vs) => if k == d then (k, merged) else (k, vs)
    | none => acc ++ [(d, [snip])]
  for l in items do
    match l.item.val with
    | .inr (.decls ds) =>
      for rawD in ds do
        let dClean := rawD.stripPos
        match dClean with
        | .typeDecl d _ =>
          let rendered := "\n".intercalate (Pretty.fmtDecls "" 1000 [dClean])
          if !rendered.isEmpty then out := addFor d rendered out
        | .typeExt d mcs _ =>
          let isCaseAtomsOnly := mcs.all isCaseAllowedMod
          if !isCaseAtomsOnly then
            let rendered := "\n".intercalate (Pretty.fmtDecls "" 1000 [dClean])
            if !rendered.isEmpty then out := addFor d rendered out
        | .placeholder f t =>
          out := addFor f s!"Placeholder {f} For {t}" out
        | _ => pure ()
    | _ => pure ()
  return out

/-- Map a rule/defeasible-rule citation `m` back to its owning top-level `DomId`. -/
def ownerDomOfCitation (spec : Spec) (m : String) : Option DomId :=
  if (spec.findDecl m).isSome then some (spec.chaseAlias m)
  else
    spec.decls.findSome? fun (ty, ts) =>
      if ts.defeasibleRules.any (fun r => r.id == m || s!"{ty}.{r.id}" == m) then some ty
      else none

/-- Declarations citing clause `c` (via `Clause ... => id` or `From <cid>`), in declaration order. -/
def declsCitingClause (spec : Spec) (c : Clause) : List DomId :=
  let fromSpanIds := (c.spans.flatMap (·.meaning)).filterMap (ownerDomOfCitation spec)
  let fromAttrIds := spec.decls.reverse.filterMap fun (d, ts) =>
    if ts.spans.any (·.1 == c.id) then some d else none
  (fromSpanIds ++ fromAttrIds).eraseDups

structure ScenarioStepTrace where
  phraseText : String
  verdict    : Option (Bool × String) := none
  clock      : Option Int := none
  deltas     : List String := []

structure ScenarioTrace where
  name  : String
  steps : List ScenarioStepTrace

/-- Execute scenarios in `items` to collect step-by-step traces for `--view legal --format html` (`#64`). -/
def collectScenarioTraces (items : List Located) (scenFilter : Option String) : List ScenarioTrace := Id.run do
  let mut baseCfg : Config := {}
  let mut specIdx : Spec.SpecIndex := baseCfg.spec.buildIndex
  let mut scens : List (String × List Phrase) := []
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario name ps spans) =>
      baseCfg := { baseCfg with spec := baseCfg.spec.insertScenario name spans }
      if scenFilter.all (· == name) then
        scens := scens ++ [(name, ps)]
    | .inr p =>
      let (cfg', nextIdx, _) := runPhraseCached baseCfg specIdx true p
      baseCfg := cfg'
      specIdx := nextIdx
  let stateDiff (before after : State) : List String :=
    let bHolds := before.holdsList
    let aHolds := after.holdsList
    let added := (aHolds.filter (!bHolds.contains ·)).map (fun te => s!"+{te.pp}")
    let removed := (bHolds.filter (!aHolds.contains ·)).map (fun te => s!"-{te.pp}")
    added ++ removed
  let mut traces : List ScenarioTrace := []
  for (name, ps) in scens do
    let mut cfg := baseCfg
    let mut sIdx := specIdx
    let mut steps : List ScenarioStepTrace := []
    for p in ps do
      let pTxt := Pretty.fmtPhrase "" 1000 p
      let (cfg', sIdx', outs) := runPhraseCached cfg sIdx true p
      let verdict? := outs.findSome? fun
        | .queryRes ok => some (ok, if ok then "holds" else "FAILED")
        | .expectRes w neg ok => some (ok, s!"{if neg then "not " else ""}{w.name}: {if ok then "ok" else "FAILED"}")
        | .diag d => if d.isError then some (false, s!"{d.code}: {d.message}") else none
        | _ => none
      let clk? := outs.findSome? fun | .timeSet t => some t | _ => none
      let deltas := stateDiff cfg.state cfg'.state
      steps := steps ++ [{ phraseText := pTxt, verdict := verdict?, clock := clk?, deltas }]
      cfg := cfg'
      sIdx := sIdx'
    traces := traces ++ [{ name, steps }]
  return traces

/-- Render `#64` Legal Reader's View in Markdown (document order, completions collapsed). -/
def renderLegalMarkdown (file : String) (spec : Spec) (locks : List ClauseLockEntry)
    (cov : ProvenanceCoverage) (items : List Located) : String × Json :=
  let snippets := collectSurfaceDeclSnippets items
  let lookupSnip (d : DomId) : String :=
    match snippets.find? (·.1 == d) with
    | some (_, ss) => "\n\n".intercalate ss
    | none =>
      match spec.findDecl d with
      | some t => Pretty.fmtTypeDeclAndExt "" d t []
      | none => d
  let isClauseApproved (c : Clause) : Bool :=
    let curSha := Artifact.sha256String c.source
    let curRules := clauseRulesDigest spec c
    if c.approvedHash == 0 && c.approvedSha256.isNone then
      match locks.find? (·.id == c.id) with
      | some le => le.textSha256 == curSha && le.rulesSha256.all (· == curRules)
      | none => false
    else !c.stale
  let comps := computationalCompletions spec
  let groundedCount := (spec.decls.length - 3) - comps.length
  let clauseBlocks := if spec.clauses.isEmpty then "_No clauses declared._"
    else "\n\n---\n\n".intercalate (spec.clauses.map fun c =>
      let st := if isClauseApproved c then "Approved" else "Unapproved / Stale"
      let cited := declsCitingClause spec c
      let regs := (c.spans.map (fun s => Pretty.fmtRegister s.register)).eraseDups
      let regTag := if regs.isEmpty then "" else s!" · {", ".intercalate regs}"
      let declBlock := if cited.isEmpty then "_No formal rules required (commentary / acceptance)._"
        else "```charter\n" ++ "\n\n".intercalate (cited.map lookupSnip) ++ "\n```"
      s!"### Clause `{c.id}` ({st}{regTag})\n\n> {c.source}\n\n{declBlock}")
  let compBlock := if comps.isEmpty then ""
    else
      let compCode := "\n\n".intercalate (comps.map lookupSnip)
      s!"\n\n---\n\n<details>\n<summary><strong>Computational Completions ({comps.length} declaration(s) citing no passage)</strong></summary>\n\n```charter\n{compCode}\n```\n\n</details>\n"
  let md :=
    s!"# Legal Reader's View — `{file}`\n\n" ++
    s!"- **Provenance Coverage**: `{cov.asString}`\n" ++
    s!"- **Clauses (document order)**: {spec.clauses.length}  |  **Grounded Declarations**: {groundedCount}  |  **Computational Completions**: {comps.length}\n\n" ++
    clauseBlocks ++ compBlock ++ "\n"
  let j := Json.mkObj [
    ("kind", Json.str "legal-view"),
    ("file", Json.str file),
    ("coverage", Json.str cov.asString),
    ("clauses", Json.num spec.clauses.length),
    ("groundedDeclarations", Json.num groundedCount),
    ("completions", Json.arr (comps.map Json.str).toArray),
    ("markdown", Json.str md)
  ]
  (md, j)

/-- Render `#64` side-by-side HTML Legal Reader's View (Document | Specification | Scenario Trace). -/
def renderLegalHtml (file : String) (spec : Spec) (locks : List ClauseLockEntry)
    (cov : ProvenanceCoverage) (items : List Located) (scenFilter : Option String) : String :=
  let snippets := collectSurfaceDeclSnippets items
  let lookupSnip (d : DomId) : String :=
    match snippets.find? (·.1 == d) with
    | some (_, ss) => "\n\n".intercalate ss
    | none =>
      match spec.findDecl d with
      | some t => Pretty.fmtTypeDeclAndExt "" d t []
      | none => d
  let isClauseApproved (c : Clause) : Bool :=
    let curSha := Artifact.sha256String c.source
    let curRules := clauseRulesDigest spec c
    if c.approvedHash == 0 && c.approvedSha256.isNone then
      match locks.find? (·.id == c.id) with
      | some le => le.textSha256 == curSha && le.rulesSha256.all (· == curRules)
      | none => false
    else !c.stale
  let comps := computationalCompletions spec
  let traces := collectScenarioTraces items scenFilter
  let rowsHtml := "\n".intercalate (spec.clauses.map fun c =>
    let stBadge := if isClauseApproved c then "<span class=\"badge ok\">Approved</span>"
                   else "<span class=\"badge warn\">Unapproved</span>"
    let regs := (c.spans.map (fun s => s!"<span class=\"badge reg\">{htmlEscape (Pretty.fmtRegister s.register)}</span>"))
    let cited := declsCitingClause spec c
    let codeCell := if cited.isEmpty then "<div class=\"muted\">Commentary / no formal rule</div>"
      else "<pre><code>" ++ htmlEscape ("\n\n".intercalate (cited.map lookupSnip)) ++ "</code></pre>"
    s!"<div class=\"clause-pair\" id=\"clause-{htmlEscape c.id}\">" ++
      s!"<div class=\"prose-col\"><div class=\"clause-hdr\"><strong>Clause {htmlEscape c.id}</strong> {stBadge} {" ".intercalate regs}</div>" ++
      s!"<blockquote>{htmlEscape c.source}</blockquote></div>" ++
      s!"<div class=\"spec-col\">{codeCell}</div></div>")
  let compHtml := if comps.isEmpty then ""
    else
      s!"<details class=\"completions\"><summary>Computational Completions ({comps.length} declaration(s) citing no passage)</summary>" ++
      s!"<pre><code>{htmlEscape ("\n\n".intercalate (comps.map lookupSnip))}</code></pre></details>"
  let traceHtml := if traces.isEmpty then "<p class=\"muted\">No scenarios in this file (pass a case file or root with scenarios to display live execution traces alongside the text).</p>"
    else "\n".intercalate (traces.map fun tr =>
      let stepItems := "\n".intercalate (tr.steps.map fun st =>
        let vHtml := match st.verdict with
          | some (true, msg) => s!" <span class=\"badge ok\">{htmlEscape msg}</span>"
          | some (false, msg) => s!" <span class=\"badge fail\">{htmlEscape msg}</span>"
          | none => ""
        let cHtml := match st.clock with
          | some t => s!" <span class=\"badge reg\">clock = {t}</span>"
          | none => ""
        let dHtml := if st.deltas.isEmpty then ""
          else s!"<div class=\"deltas\">{htmlEscape (", ".intercalate st.deltas)}</div>"
        s!"<li class=\"trace-step\"><code>{htmlEscape st.phraseText}</code>{vHtml}{cHtml}{dHtml}</li>")
      s!"<div class=\"scenario-card\"><h3>Scenario <code>{htmlEscape tr.name}</code></h3><ol class=\"trace-list\">{stepItems}</ol></div>")
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  s!"<title>Charter Legal Reader — {htmlEscape file}</title>\n" ++
  "<style>\n" ++
  ":root{--bg:#faf9f6;--surface:#ffffff;--ink:#1b1b1f;--muted:#5c5f66;--border:#e2e0d8;--code-bg:#f3f2ec;--ok:#1b6e3c;--ok-bg:#e5f5ec;--warn:#8a5200;--warn-bg:#fff3db;--fail:#9e1c1c;--fail-bg:#fde8e8;}\n" ++
  "@media(prefers-color-scheme:dark){:root{--bg:#141518;--surface:#1d1f24;--ink:#ececf0;--muted:#9aa0aa;--border:#2e323b;--code-bg:#17191d;--ok:#6ee7a0;--ok-bg:#143524;--warn:#fbbf24;--warn-bg:#382a10;--fail:#f87171;--fail-bg:#3b1818;}}\n" ++
  "*{box-sizing:border-box}body{margin:0;padding:16px 24px;background:var(--bg);color:var(--ink);font:15px/1.55 ui-sans-serif,system-ui,-apple-system,sans-serif}\n" ++
  "header{border-bottom:1px solid var(--border);padding-bottom:12px;margin-bottom:18px}\n" ++
  "h1{font-size:1.3rem;margin:0 0 6px 0}.meta{color:var(--muted);font-size:0.9rem}\n" ++
  ".layout{display:grid;grid-template-columns:minmax(0,2fr) minmax(0,1fr);gap:20px;align-items:start}\n" ++
  "@media(max-width:960px){.layout{grid-template-columns:1fr}}\n" ++
  ".clause-pair{display:grid;grid-template-columns:1fr 1fr;gap:16px;background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:14px;margin-bottom:12px}\n" ++
  "@media(max-width:720px){.clause-pair{grid-template-columns:1fr}}\n" ++
  "blockquote{margin:8px 0 0 0;padding-left:12px;border-left:3px solid var(--border);font-family:Georgia,serif;line-height:1.6}\n" ++
  "pre{margin:0;padding:10px 12px;background:var(--code-bg);border-radius:6px;overflow-x:auto;font-size:0.83rem;line-height:1.45}\n" ++
  ".badge{display:inline-block;padding:1px 7px;border-radius:999px;font-size:0.75rem;font-weight:600}\n" ++
  ".badge.ok{color:var(--ok);background:var(--ok-bg)}.badge.warn{color:var(--warn);background:var(--warn-bg)}\n" ++
  ".badge.fail{color:var(--fail);background:var(--fail-bg)}.badge.reg{color:var(--muted);border:1px solid var(--border)}\n" ++
  ".completions{margin-top:16px;background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:12px}\n" ++
  ".completions summary{cursor:pointer;font-weight:600;margin-bottom:8px}\n" ++
  ".trace-pane{background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:14px;position:sticky;top:16px;max-height:calc(100vh - 32px);overflow-y:auto}\n" ++
  ".trace-pane h2{font-size:1.05rem;margin:0 0 12px 0}.scenario-card{border-top:1px solid var(--border);padding-top:10px;margin-top:10px}\n" ++
  ".scenario-card h3{font-size:0.95rem;margin:0 0 8px 0}.trace-list{margin:0;padding-left:20px;font-size:0.85rem}\n" ++
  ".trace-step{margin-bottom:6px}.deltas{color:var(--muted);font-family:ui-monospace,monospace;font-size:0.78rem;margin-top:2px}\n" ++
  ".muted{color:var(--muted);font-style:italic;font-size:0.88rem}\n" ++
  "</style>\n</head>\n<body>\n" ++
  s!"<header><h1>Legal Reader's View — <code>{htmlEscape file}</code></h1>" ++
  s!"<div class=\"meta\">Provenance coverage: <strong>{htmlEscape cov.asString}</strong> · Clauses: {spec.clauses.length} · Computational completions: {comps.length}</div></header>\n" ++
  s!"<div class=\"layout\"><main>{rowsHtml}{compHtml}</main>" ++
  s!"<aside class=\"trace-pane\"><h2>Scenario Execution Trace</h2>{traceHtml}</aside></div>\n" ++
  "</body>\n</html>\n"

def renderRulebook (file : String) (spec : Spec) (cov : ProvenanceCoverage) : String × Json :=
  let clauseSec := if spec.clauses.isEmpty then "_No clauses declared._\n"
    else "\n\n".intercalate (spec.clauses.map fun c =>
      let st := if c.stale then "STALE" else "Approved"
      let spanRows := c.spans.map fun s =>
        let rids := if s.meaning.isEmpty then "_(commentary/definition)_" else ", ".intercalate (s.meaning.map fun m => s!"`{m}`")
        s!"| `{Pretty.fmtRegister s.register}` | {s.text} | {rids} |"
      s!"### Clause `{c.id}` ({st})\n\n> {c.source}\n\n| Register | Verbatim Span | Formal Rules |\n|---|---|---|\n" ++
      "\n".intercalate spanRows)
  let powers := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .act a =>
      let kind := if a.isFinding then "Finding" else if a.isAmend then "Amend" else if a.isPower then "Power" else if a.physical then "Physical" else "Act"
      let comps := ", ".intercalate ((spec.components d).map toString)
      let sps := if t.spans.isEmpty then "—" else ", ".intercalate (t.spans.map (·.1))
      some s!"| `{d}` | {kind} | `{comps}` | {sps} |"
    | _ => none
  let duties := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .duty du =>
      let comps := ", ".intercalate ((spec.components d).map toString)
      let ov := if du.overriddenBy.isEmpty then "—" else ", ".intercalate du.overriddenBy
      let sps := if t.spans.isEmpty then "—" else ", ".intercalate (t.spans.map (·.1))
      some s!"| `{d}` | `{comps}` | {ov} | {sps} |"
    | _ => none
  let immunities := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .immunity im =>
      let ag := ", ".intercalate im.against
      let pr := if im.protects.isEmpty then "—" else ", ".intercalate im.protects
      some s!"| `{d}` | `{ag}` | `{pr}` |"
    | _ => none
  let defTables := spec.decls.filterMap fun (d, t) =>
    if t.defeasibleRules.isEmpty then none
    else
      let rows := t.defeasibleRules.map fun r =>
        let kind := if r.isDefault then "Default" else s!"Exception (overrides {", ".intercalate r.overrides})"
        let csq := match r.conseq with
          | .holdsBool true => "Holds"
          | .holdsBool false => "Rejects"
          | .yieldsVal v => s!"Yields `{v.pp}`"
        s!"| `{r.id}` | {kind} | `{r.cond.pp}` | {csq} |"
      let rEdges := (spec.rankEdges.filter (·.1 == d)).map (·.2)
      let rankNote := if rEdges.isEmpty then ""
        else "\n\n**Document-Rank Priorities (`lex superior`):**\n" ++
          "\n".intercalate (rEdges.map fun e =>
            s!"- `{e.higherRule}` (`{e.higherDoc}`, Rank {e.higherRank}) prevails over `{e.lowerRule}` (`{e.lowerDoc}`, Rank {e.lowerRank})")
      some (s!"### Decision Table: `{d}`\n\n| Rule ID | Tier / Overrides | Condition | Consequence |\n|---|---|---|---|\n" ++ "\n".intercalate rows ++ rankNote)
  let md :=
    s!"# Institutional Rulebook — `{file}`\n\n" ++
    s!"- **Provenance Coverage**: `{cov.asString}`\n" ++
    s!"- **Clauses**: {spec.clauses.length}  |  **Normative Rules**: {spec.ruleIds.length}  |  **Invariants**: {spec.invariants.length}  |  **Temporal Properties**: {spec.temporalProperties.length}\n\n" ++
    "## 1. Consolidated Source Clauses & Formal Mappings\n\n" ++ clauseSec ++ "\n\n" ++
    "## 2. Actions, Powers, Findings, and Amendments\n\n" ++
    "| Identifier | Kind | Parameters | Clauses |\n|---|---|---|---|\n" ++ "\n".intercalate powers ++ "\n\n" ++
    "## 3. Duties & Precedence\n\n" ++
    (if duties.isEmpty then "_None._\n\n" else "| Duty | Holder / Claimant / Scope | Overridden By | Clauses |\n|---|---|---|---|\n" ++ "\n".intercalate duties ++ "\n\n") ++
    "## 4. Immunities & Entrenchment\n\n" ++
    (if immunities.isEmpty then "_None._\n\n" else "| Immunity | Against | Protects |\n|---|---|---|\n" ++ "\n".intercalate immunities ++ "\n\n") ++
    (if defTables.isEmpty then "" else "## 5. Statutory Default / Exception Decision Tables\n\n" ++ "\n\n".intercalate defTables ++ "\n\n") ++
    "## 6. Invariants & Temporal Properties\n\n" ++
    (if spec.invariants.isEmpty && spec.temporalProperties.isEmpty then "_None._\n"
     else "\n".intercalate ((spec.invariants.map fun i => s!"- `Invariant {i}`") ++
                            (spec.temporalProperties.map fun tp => s!"- `Property {tp.name}`"))) ++ "\n"
  let j := Json.mkObj [
    ("kind", Json.str "rulebook"),
    ("file", Json.str file),
    ("coverage", Json.str cov.asString),
    ("clauses", Json.num spec.clauses.length),
    ("rules", Json.num spec.ruleIds.length),
    ("invariants", Json.arr (spec.invariants.map Json.str).toArray),
    ("markdown", Json.str md)
  ]
  (md, j)

def docCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter doc <file.charter> [--view rulebook|legal] [--format markdown|html] [--scenario <name>] [-o <out>] [--out json]"
  let opts ← match parseDocArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter doc: {e}\n{usage}"; return 2
  let some f := opts.input | do IO.eprintln usage; return 2
  let (items, loadDiags) ← loadProgram f
  for d in loadDiags do
    if d.isError then IO.eprintln d.render; return 1
  let mut spec := emptySpec
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario name _ spans) => spec := spec.insertScenario name spans
    | .inr p =>
      match resolvePhrase spec p with
      | .ok (s', _, _) => spec := s'
      | .error ds => for d in ds do IO.eprintln d.render; return 1
  let dir := (System.FilePath.mk f).parent.getD "."
  let loaded ← readDocuments spec dir
  let locks ← readClauseLocks dir
  spec := hydrateClausesFromDocs spec loaded
  let claims := if spec.clauses.isEmpty && spec.document.isNone && spec.documents.isEmpty then []
                else provenanceReportDocs spec loaded locks
  let cov := computeProvenanceCoverage spec loaded claims
  let wantHtml := opts.format == some "html" || opts.output.any (·.endsWith ".html")
  let outStr :=
    if wantHtml then
      renderLegalHtml f spec locks cov items opts.scenario
    else if opts.view == "legal" then
      let (md, j) := renderLegalMarkdown f spec locks cov items
      if opts.json then j.pretty ++ "\n" else md
    else
      let (md, j) := renderRulebook f spec cov
      if opts.json then j.pretty ++ "\n" else md
  match opts.output with
  | some outP =>
    let p := System.FilePath.mk outP
    if let some parent := p.parent then IO.FS.createDirAll parent
    IO.FS.writeFile p outStr
    IO.println s!"wrote {outP} (coverage={cov.asString})"
  | none =>
    IO.print outStr
  return 0

end Charter.Cli
