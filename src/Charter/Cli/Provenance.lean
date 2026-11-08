import Charter.Core.Spec
import Lean.Data.Json

/-!
# Charter.Cli.Provenance — The checks of Law 8 as claims

Every norm carries its English, and the English leads (Law 8). For a program with
`Clause` declarations and a `Document`, these checks are run by `charter check`
and at the end of `charter test`, each a *claim* (tagged *checked*, about
*provenance*) that passes or fails:

- **covered**: a clause's spans, concatenated in order, reproduce its text;
- **interpreted**: every `Norm` span names at least one formal target (or a rule names it via `From`);
- **declared**: every id a span names is a declared type, parameter, event, rule, or `Default`/`Exception` rule ID (`D34`, `#36`), and every `Invariant` span names a declared `Invariant`;
- **named**: every declared rule is named by some span, in a clause or by its own `From CLAUSE ["span"]`, and every `From` names a declared clause (whose text contains the span when quoted);
- **verbatim**: the clause's text occurs verbatim in the document (or its template expansion, `D34`, `#59`);
- **approved**: the clause's text (and rule signature when locked in `charter.lock`, `D34`, `#23`, `#35`) matches its approval; otherwise the clause is STALE.

Each check is data (plan §3); the CLI renders it as text or JSON.
-/

namespace Charter.Cli

open Lean (Json)

structure ProvClaim where
  ok     : Bool
  /-- `covered`, `interpreted`, `declared`, `named`, `verbatim`, `approved`. -/
  check  : String
  clause : String := ""
  text   : String
  /-- A warning rather than a failure (the document could not be read). -/
  warn   : Bool := false

def ProvClaim.render (c : ProvClaim) : String :=
  let tag := if c.warn then "WARN" else if c.ok then "ok  " else "FAIL"
  s!"{tag} {c.text}"

def ProvClaim.json (c : ProvClaim) : Json :=
  Json.mkObj [("kind", "claim"), ("tag", "checked"), ("assurance", "checked"), ("about", "provenance"),
    ("scope", Json.mkObj [("kind", "concrete-trace")]),
    ("completion", Json.str (if c.warn then "inconclusive" else "complete")),
    ("check", Json.str c.check), ("clause", Json.str c.clause),
    ("result", Json.bool c.ok), ("warning", Json.bool c.warn), ("text", Json.str c.text)]

/-- Per-clause approval record stored in `charter.lock` (`D34`, `#23`, `#32`, `#35`). -/
structure ClauseLockEntry where
  id          : ClauseId
  textSha256  : String
  rulesSha256 : Option String := none
  deriving Repr, Inhabited

/-- Whether `needle` occurs in `hay`. -/
def occursIn (hay needle : String) : Bool :=
  !needle.isEmpty && (hay.splitOn needle).length > 1

/-- Loaded document records: `(docSpec, Either errorMsg fileContent)`. -/
abbrev LoadedDocs := List (SourceDoc × Except String String)

/-- Effective document manifest of a `Spec` (handling legacy single `spec.document`). -/
def effectiveDocs (spec : Spec) : List SourceDoc :=
  if !spec.documents.isEmpty then spec.documents
  else match spec.document with
    | some p => [{ id := none, path := p, expectedSha256 := none }]
    | none => []

/-- Read every document named by `spec`, relative to the program's directory. -/
def readDocuments (spec : Spec) (programDir : System.FilePath) : IO LoadedDocs := do
  let docs := effectiveDocs spec
  let mut out : LoadedDocs := []
  for sd in docs do
    let f := programDir / sd.path
    let res ← try
      let txt ← IO.FS.readFile f
      pure (.ok txt)
    catch e => pure (.error (toString e))
    out := out ++ [(sd, res)]
  return out

/-- Read `clauses` lock entries from `charter.lock` in `programDir` (or its parent for `cases/`). -/
def readClauseLocks (programDir : System.FilePath) : IO (List ClauseLockEntry) := do
  let p1 := programDir / "charter.lock"
  let p2 := programDir / ".." / "charter.lock"
  let path? ← if ← p1.pathExists then pure (some p1)
              else if ← p2.pathExists then pure (some p2)
              else pure none
  match path? with
  | none => return []
  | some p =>
    let raw ← try IO.FS.readFile p catch _ => pure ""
    match (do let j ← Json.parse raw; j.getObjValAs? (Array Json) "clauses") with
    | .error _ => return []
    | .ok arr =>
      let mut out : List ClauseLockEntry := []
      for item in arr do
        match item.getObjValAs? String "id", item.getObjValAs? String "textSha256" with
        | .ok id, .ok tsha =>
          let rsha := (item.getObjValAs? String "rulesSha256").toOption
          out := out ++ [{ id, textSha256 := tsha, rulesSha256 := rsha }]
        | _, _ => pure ()
      return out

/-- Legacy single-document reader kept for callers expecting one optional text. -/
def readDocument (spec : Spec) (programDir : System.FilePath) : IO (Option (Except String String)) := do
  match spec.document with
  | none => return none
  | some path =>
    let f := programDir / path
    try
      let txt ← IO.FS.readFile f
      return some (.ok txt)
    catch e => return some (.error (toString e))

/-! ## Template Blanks (`#59`) & Heading/Paragraph Extraction (`#35`) -/

/-- Collect `{name} -> value` substitutions from declared `Param`s and singleton `Fact`s (`D34`, `#59`). -/
def templateBindings (spec : Spec) : List (String × String) :=
  spec.decls.filterMap fun (d, ts) =>
    match ts.kind with
    | .fact fs =>
      match fs.defaultVal with
      | some v => some (d, toString v)
      | none =>
        match ts.domain with
        | .strings [s] => some (d, s)
        | .ints [n] => some (d, toString n)
        | _ => none
    | _ => none

/-- Substitute `{param}` placeholders in `txt` with concrete values from `bindings`. -/
def applyTemplateBindings (bindings : List (String × String)) (txt : String) : String :=
  bindings.foldl (fun acc (k, v) => String.intercalate v (acc.splitOn ("{" ++ k ++ "}"))) txt

/-- Whether `rest` after `cid` in a heading or numbered line marks a boundary (`1.1` vs `1.10`). -/
def isCidBoundary (rest : String) : Bool :=
  match rest.toList with
  | [] => true
  | c :: _ => c.isWhitespace || c == ':' || c == '.' || c == ')' || c == '—' || c == '-'

/-- Split a paragraph into trimmed sentences (`1.2/1`, `1.2/2`), preserving trailing periods. -/
def splitSentences (para : String) : List String :=
  let parts := para.trim.splitOn ". "
  let rec build : List String → List String
    | [] => []
    | [last] =>
      let t := last.trim
      if t.isEmpty then [] else [t]
    | p :: rest =>
      let t := p.trim
      let s := if t.endsWith "." then t else t ++ "."
      (if t.isEmpty then [] else [s]) ++ build rest
  build parts

/-- Strip leading `#` characters and whitespace from a Markdown heading line. -/
def stripHeadingHashes (line : String) : Option String :=
  let t := line.trimLeft
  if !t.startsWith "#" then none
  else
    let rest := String.mk (t.toList.dropWhile (· == '#'))
    some rest.trimLeft

/-- Check if stripped heading title `h` identifies `baseCid` (`1.1`, `Clause 1.1`, `Article 1.1`, `Section 1.1`). -/
def headingMatchesCid (baseCid : String) (h : String) : Bool :=
  let prefixes := [baseCid, "Clause " ++ baseCid, "Article " ++ baseCid, "Section " ++ baseCid]
  prefixes.any fun pfx =>
    h.startsWith pfx && isCidBoundary (h.drop pfx.length)

/-- Extract the body text for `cid` (or `<baseCid>/<sentenceIdx>`) from `docText` (`D34`, `#35`). -/
def extractClauseByHeading (docText : String) (cid : ClauseId) : Option String :=
  let (baseCid, sentIdx?) : String × Option Nat :=
    match cid.splitOn "/" with
    | [b, idxS] => (b, idxS.toNat?)
    | _ => (cid, none)
  let lines := docText.splitOn "\n"
  -- 1. Try Markdown `#` headings first
  let rec collectUnderHeading : List String → List String → List String
    | [], acc => acc.reverse
    | l :: ls, acc =>
      let tl := l.trimLeft
      if tl.startsWith "#" then acc.reverse
      else collectUnderHeading ls (l :: acc)
  let rec findHeading : List String → Option String
    | [] => none
    | l :: ls =>
      match stripHeadingHashes l with
      | some h =>
        if headingMatchesCid baseCid h then
          let body := ("\n".intercalate (collectUnderHeading ls [])).trim
          if body.isEmpty then none else some body
        else findHeading ls
      | none => findHeading ls
  -- 2. Fallback: numbered body paragraph (`1.1 Text...` or `**1.1** Text...`)
  let extractNumberedLine (l : String) : Option String :=
    let tl := l.trimLeft
    let candidates := [baseCid ++ " ", baseCid ++ ". ", "**" ++ baseCid ++ "** ", "**" ++ baseCid ++ ".** "]
    candidates.findSome? fun pfx =>
      if tl.startsWith pfx then some (tl.drop pfx.length).trimLeft else none
  let rec collectParaCont : List String → List String → List String
    | [], acc => acc.reverse
    | l :: ls, acc =>
      let tl := l.trim
      if tl.isEmpty || tl.startsWith "#" then acc.reverse
      else
        -- stop if next line begins another numbered item like `1.2 `
        let startsNum := match tl.toList with | d :: _ => d.isDigit | [] => false
        if startsNum && (tl.splitOn " ").head?.any (fun tok => (tok.splitOn ".").length >= 2) then acc.reverse
        else collectParaCont ls (tl :: acc)
  let rec findNumbered : List String → Option String
    | [] => none
    | l :: ls =>
      match extractNumberedLine l with
      | some firstRest =>
        let cont := collectParaCont ls []
        some (" ".intercalate (firstRest.trimRight :: cont)).trim
      | none => findNumbered ls
  let fullOpt := (findHeading lines).orElse (fun _ => findNumbered lines)
  match fullOpt, sentIdx? with
  | none, _ => none
  | some full, none => some full
  | some _, some 0 => none
  | some full, some (k + 1) => (splitSentences full)[k]?

/-- Hydrate any `byRef` clauses in `spec` using the loaded Markdown documents (with template
bindings applied when present, `D34`, `#35`, `#59`). -/
def hydrateClausesFromDocs (spec : Spec) (loaded : LoadedDocs) : Spec :=
  if loaded.isEmpty || !spec.clauses.any (·.byRef) then spec
  else
    let bindings := templateBindings spec
    let findDocText (c : Clause) : Option String :=
      let entry? := match c.docId with
        | some wantId => loaded.find? (fun (p : SourceDoc × Except String String) => p.1.id == some wantId)
        | none => loaded.head?
      match entry? with
      | some (_, .ok rawDoc) => some (applyTemplateBindings bindings rawDoc)
      | _ => none
    let hydrated := spec.clauses.map fun c =>
      if !c.byRef || !c.source.isEmpty then c
      else
        match findDocText c >>= fun doc => extractClauseByHeading doc c.id with
        | none => c
        | some extracted =>
          let sps := match c.spans with
            | [s] => [{ s with text := extracted }]
            | other => other
          { c with source := extracted, spans := sps }
    { spec with clauses := hydrated }

/-- Compute the SHA-256 fingerprint of a clause's formal mapping and referenced rule records (`D34`, `#23`). -/
def clauseRulesDigest (spec : Spec) (c : Clause) : String :=
  let spanPart := c.spans.map fun s => s!"{reprStr s.register}:{",".intercalate s.meaning}"
  let targets := (c.spans.flatMap (·.meaning)).eraseDups
  let targetDefs := targets.map fun m =>
    match spec.findDecl m with
    | some ts => s!"decl:{m}={reprStr { ts with spans := [] }}"
    | none =>
      let defMatches := spec.decls.filterMap fun (ty, ts) =>
        ts.defeasibleRules.find? (fun r => r.id == m || s!"{ty}.{r.id}" == m) |>.map fun r =>
          s!"def:{ty}.{r.id}={reprStr r}"
      "|".intercalate defMatches
  Artifact.sha256String ("\n".intercalate (spanPart ++ targetDefs))

/-- Multi-document, template-aware, & lockfile-backed SHA-256 provenance report (`012`, `D34`). -/
def provenanceReportDocs (spec0 : Spec) (loaded : LoadedDocs) (locks : List ClauseLockEntry := []) : List ProvClaim :=
  let spec := hydrateClausesFromDocs spec0 loaded
  let bindings := templateBindings spec
  let rules := spec.ruleIds
  let citeable := spec.citeableIds
  let scenarioNames := spec.scenarios.map (·.1) ++ spec.temporalProperties.map (·.name)
  let knownIds := (citeable ++ scenarioNames).eraseDups
  let invariants := spec.invariants
  let fromSpans : List Span := spec.decls.flatMap fun (p : DomId × TypeSpec) =>
    p.2.spans.map fun sp => ⟨sp.1, sp.2, .norm, [p.1]⟩
  let hasFromForClause (cid : ClauseId) : Bool :=
    fromSpans.any (·.clause == cid)
  let perClause := spec.clauses.flatMap fun c =>
    let unknown := (c.spans.flatMap (fun s =>
      let allowed := if s.register == .invariant then rules else if s.register == .norm then citeable else knownIds
      s.meaning.filter (fun i => !allowed.contains i))).eraseDups
    let badInv := c.spans.filter (fun s => s.register == .invariant && s.meaning.any (fun i => !invariants.contains i))
    let interpOk := c.normsInterpreted || hasFromForClause c.id
    [ { ok := c.covered && (!c.byRef || !c.source.isEmpty || loaded.isEmpty), check := "covered", clause := c.id,
        text := if !c.byRef || !c.source.isEmpty || loaded.isEmpty then s!"{c.id}: spans reproduce the clause text exactly"
                else s!"{c.id}: heading or numbered paragraph `{c.id}` not found in Document" },
      { ok := interpOk, check := "interpreted", clause := c.id, text := s!"{c.id}: every Norm span names a rule" },
      { ok := unknown.isEmpty && badInv.isEmpty, check := "declared", clause := c.id,
        text := if unknown.isEmpty && badInv.isEmpty then s!"{c.id}: every id its spans name is declared"
          else if !unknown.isEmpty then s!"{c.id}: spans name undeclared identifiers: {", ".intercalate unknown}"
          else s!"{c.id}: an Invariant span must name a declared Invariant" } ]
  let named : ProvClaim :=
    let unnamed := rules.filter fun i => !(reverseProvenanceWith spec.clauses fromSpans [i])
    { ok := unnamed.isEmpty, check := "named",
      text := if unnamed.isEmpty then "every act, duty, immunity, and invariant is named by some span"
        else s!"rules with no English: {", ".intercalate unnamed} (add a Norm span or a From clause)" }
  let checkFrom (owner : String) (sp : ClauseId × String) : ProvClaim :=
    let cid := sp.1
    let quoted := sp.2
    match spec.clauses.find? (·.id == cid) with
    | none => { ok := false, check := "named", clause := cid, text := s!"{owner}: From {cid} names no declared clause" }
    | some c =>
      let ok := quoted.isEmpty || occursIn c.source quoted
      let msg := if ok then s!"{owner}: From {cid} quotes the clause" else s!"{owner}: From {cid} quotes text that is not in the clause"
      { ok := ok, check := "named", clause := cid, text := msg }
  let fromChecks :=
    (spec.decls.flatMap fun (p : DomId × TypeSpec) => p.2.spans.map (checkFrom p.1)) ++
    (spec.scenarios.flatMap fun (name, sps) => sps.map (checkFrom s!"Scenario {name}")) ++
    (spec.temporalProperties.flatMap fun tp => tp.spans.map (checkFrom s!"Property {tp.name}"))
  let docShaChecks : List ProvClaim := loaded.filterMap fun (sd, res) =>
    match sd.expectedSha256, res with
    | none, _ => none
    | some _, .error e =>
      some { ok := false, check := "sha256", text := s!"{sd.path}: could not read document to verify SHA256 ({e})" }
    | some wantHex, .ok txt =>
      let actual := Artifact.sha256String txt
      if actual == wantHex then
        some { ok := true, check := "sha256", text := s!"{sd.path}: SHA-256 content digest matches" }
      else
        some { ok := false, check := "sha256", text := s!"STALE {sd.path}: SHA-256 digest mismatch (expected {wantHex}, actual {actual})" }
  let findDocForClause (c : Clause) : Option (SourceDoc × Except String String) :=
    match c.docId with
    | some wantId => loaded.find? (fun (sd, _) => sd.id == some wantId)
    | none => loaded.head?
  let verbatim : List ProvClaim :=
    if loaded.isEmpty then []
    else spec.clauses.map fun c =>
      match c.docId, findDocForClause c with
      | some wantId, none =>
        { ok := false, check := "verbatim", clause := c.id, text := s!"{c.id}: In {wantId} names no declared Document" }
      | _, none =>
        { ok := true, warn := true, check := "verbatim", clause := c.id, text := s!"{c.id}: no Document loaded; verbatim check skipped" }
      | _, some (sd, .error e) =>
        { ok := true, warn := true, check := "verbatim", clause := c.id, text := s!"{sd.path} could not be read ({e}); verbatim check skipped" }
      | _, some (sd, .ok doc) =>
        let expandedDoc := applyTemplateBindings bindings doc
        let ok := occursIn doc c.source || occursIn expandedDoc c.source
        { ok := ok, check := "verbatim", clause := c.id, text := s!"{c.id}: text occurs verbatim in {sd.path}" }
  let approved := spec.clauses.map fun c =>
    let curSha := Artifact.sha256String c.source
    let curRulesSha := clauseRulesDigest spec c
    let lockEntry? := locks.find? (·.id == c.id)
    let inlineUnset := c.approvedHash == 0 && c.approvedSha256.isNone
    match inlineUnset, lockEntry? with
    | true, some le =>
      if le.textSha256 != curSha then
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: text differs from charter.lock approval (current sha256 \"{curSha}\")" }
      else if le.rulesSha256.any (· != curRulesSha) then
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: formal rule mapping or rule body changed since charter.lock approval (run `charter approve --lock --restamp`)" }
      else
        { ok := true, check := "approved", clause := c.id, text := s!"{c.id}: approved mapping current" }
    | _, _ =>
      let ruleDrifted := match lockEntry? with
        | some le => le.rulesSha256.any (· != curRulesSha)
        | none => false
      if c.stale then
        if inlineUnset then
          { ok := false, check := "approved", clause := c.id,
            text := s!"STALE {c.id}: not yet approved; once reviewed, run `charter approve` or declare `Approved \"{curSha}\"` (or legacy `Approved {c.source.hash}`). Unapproved: {", ".intercalate c.invalidated}" }
        else
          { ok := false, check := "approved", clause := c.id,
            text := s!"STALE {c.id}: text differs from the approved text (current sha256 \"{curSha}\", hash {c.source.hash}); review invalidated for {", ".intercalate c.invalidated}" }
      else if ruleDrifted then
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: formal rule mapping or rule body changed since charter.lock approval (run `charter approve --lock --restamp`)" }
      else { ok := true, check := "approved", clause := c.id, text := s!"{c.id}: approved mapping current" }
  perClause ++ [named] ++ fromChecks ++ docShaChecks ++ verbatim ++ approved

/-- Classify provenance completeness (`docs/rfc.md` §4.5, `G3.1`, `T08`). -/
def computeProvenanceCoverage (spec : Spec) (loaded : LoadedDocs) (claims : List ProvClaim) : ProvenanceCoverage :=
  if spec.documents.isEmpty && spec.document.isNone && spec.clauses.isEmpty then
    if spec.ruleIds.isEmpty then .complete else .illustrative
  else
    let allDocsRead := !loaded.isEmpty && loaded.all fun (_, r) =>
      match r with | .ok _ => true | .error _ => false
    let allClaimsClean := claims.all fun c => c.ok && !c.warn
    let rulesCovered := spec.ruleIds.isEmpty || !spec.clauses.isEmpty
    if allDocsRead && allClaimsClean && rulesCovered then .complete else .partialCov

/-- Single-document wrapper retained for compatibility (`Cli/Build`). -/
def provenanceReport (spec : Spec) (doc? : Option (Except String String)) : List ProvClaim :=
  let loaded : LoadedDocs := match spec.document, doc? with
    | some p, some r => [({ path := p }, r)]
    | some p, none => [({ path := p }, .error "not read")]
    | none, _ => []
  provenanceReportDocs spec loaded

/-- The span table of one clause (`charter trace <clause>`). -/
def traceTable (c : Clause) : String :=
  let reg : Register → String
    | .norm => "norm" | .definition => "definition" | .invariant => "invariant" | .acceptance => "acceptance" | .commentary => "commentary"
  let rows := c.spans.map fun s =>
    s!"  {reg s.register}  {showString s.text}  => {if s.meaning.isEmpty then "(no rule)" else ", ".intercalate s.meaning}"
  let docTag := match c.docId with | some d => s!" in {d};" | none => ""
  let sha := Artifact.sha256String c.source
  s!"{c.id}  ({docTag} approved: {!c.stale}; sha256 {sha}; fnv64 {c.source.hash})\n" ++ "\n".intercalate rows

end Charter.Cli
