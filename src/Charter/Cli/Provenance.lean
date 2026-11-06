import Charter.Core.Spec
import Lean.Data.Json

/-!
# Charter.Cli.Provenance — The checks of Law 8 as claims

Every norm carries its English, and the English leads (Law 8). For a program with
`Clause` declarations and a `Document`, these checks are run by `charter check`
and at the end of `charter test`, each a *claim* (tagged *checked*, about
*provenance*) that passes or fails:

- **covered**: a clause's spans, concatenated in order, reproduce its text;
- **interpreted**: every `Norm` span names at least one rule;
- **declared**: every id a span names is a declared rule (act, duty, immunity,
  invariant), and every `Invariant` span names a declared `Invariant`;
- **named**: every declared rule is named by some span, in a clause or by its own
  `From CLAUSE "span"`, and every `From` names a declared clause whose text
  contains the span;
- **verbatim**: the clause's text occurs verbatim in the document (a missing
  document is a warning, not a failure);
- **approved**: the clause's text hashes to its `Approved` value; otherwise the
  clause is STALE and the rules it names lose their reviewed status until it is
  re-approved with the hash the report prints.

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

/-- Whether `needle` occurs in `hay`. -/
def occursIn (hay needle : String) : Bool := (hay.splitOn needle).length > 1

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

/-- Multi-document & SHA-256 provenance report (`012`, `G3.1`, `T37`, `T39`). -/
def provenanceReportDocs (spec : Spec) (loaded : LoadedDocs) : List ProvClaim :=
  let rules := spec.ruleIds
  let scenarioNames := spec.scenarios.map (·.1) ++ spec.temporalProperties.map (·.name)
  let knownIds := rules ++ scenarioNames
  let invariants := spec.invariants
  let fromSpans : List Span := spec.decls.flatMap fun (p : DomId × TypeSpec) =>
    p.2.spans.map fun sp => ⟨sp.1, sp.2, .norm, [p.1]⟩
  let perClause := spec.clauses.flatMap fun c =>
    let unknown := (c.spans.flatMap (fun s =>
      let allowed := if s.register == .norm || s.register == .invariant then rules else knownIds
      s.meaning.filter (fun i => !allowed.contains i))).eraseDups
    let badInv := c.spans.filter (fun s => s.register == .invariant && s.meaning.any (fun i => !invariants.contains i))
    [ { ok := c.covered, check := "covered", clause := c.id, text := s!"{c.id}: spans reproduce the clause text exactly" },
      { ok := c.normsInterpreted, check := "interpreted", clause := c.id, text := s!"{c.id}: every Norm span names a rule" },
      { ok := unknown.isEmpty && badInv.isEmpty, check := "declared", clause := c.id,
        text := if unknown.isEmpty && badInv.isEmpty then s!"{c.id}: every id its spans name is declared"
          else if !unknown.isEmpty then s!"{c.id}: spans name undeclared rules: {", ".intercalate unknown}"
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
      let ok := occursIn c.source quoted
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
        { ok := occursIn doc c.source, check := "verbatim", clause := c.id, text := s!"{c.id}: text occurs verbatim in {sd.path}" }
  let approved := spec.clauses.map fun c =>
    if c.stale then
      let curSha := Artifact.sha256String c.source
      if c.approvedHash == 0 && c.approvedSha256.isNone then
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: not yet approved; once reviewed, declare `Approved \"{curSha}\"` (or legacy `Approved {c.source.hash}`). Unapproved: {", ".intercalate c.invalidated}" }
      else
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: text differs from the approved text (current sha256 \"{curSha}\", hash {c.source.hash}); review invalidated for {", ".intercalate c.invalidated}" }
    else { ok := true, check := "approved", clause := c.id, text := s!"{c.id}: approved mapping current" }
  perClause ++ [named] ++ fromChecks ++ docShaChecks ++ verbatim ++ approved

/-- Classify provenance completeness (`docs/rfc.md` §4.5, `G3.1`, `T08`):
- `complete`: every normative rule is grounded, at least one `Document` is readable (whenever rules
  or clauses exist), every declared `Document` was read and passed any `SHA256` pin, and every
  `ProvClaim` passed without warnings;
- `partialCov` (`"partial"`): some provenance is declared, or some rule/clause/document is missing or `STALE`;
- `illustrative`: neither `Document` nor `Clause` is declared for the program's rules. -/
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
