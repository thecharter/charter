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
  Json.mkObj [("kind", "claim"), ("tag", "checked"), ("about", "provenance"), ("check", Json.str c.check),
    ("clause", Json.str c.clause), ("result", Json.bool c.ok), ("warning", Json.bool c.warn), ("text", Json.str c.text)]

/-- Whether `needle` occurs in `hay`. -/
def occursIn (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The provenance report of a resolved program. `doc?` is the document's text if
`Document` names one and it could be read. -/
def provenanceReport (spec : Spec) (doc? : Option (Except String String)) : List ProvClaim :=
  let rules := spec.ruleIds
  let invariants := spec.invariants
  let fromSpans : List Span := spec.decls.flatMap fun (p : DomId × TypeSpec) =>
    p.2.spans.map fun sp => ⟨sp.1, sp.2, .norm, [p.1]⟩
  let perClause := spec.clauses.flatMap fun c =>
    let unknown := (c.spans.flatMap (·.meaning)).filter (fun i => !rules.contains i) |>.eraseDups
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
  let fromChecks := spec.decls.flatMap fun (p : DomId × TypeSpec) => p.2.spans.map fun sp =>
    let cid := sp.1
    let quoted := sp.2
    match spec.clauses.find? (·.id == cid) with
    | none => { ok := false, check := "named", clause := cid, text := s!"{p.1}: From {cid} names no declared clause" }
    | some c =>
      let ok := occursIn c.source quoted
      let msg := if ok then s!"{p.1}: From {cid} quotes the clause" else s!"{p.1}: From {cid} quotes text that is not in the clause"
      { ok := ok, check := "named", clause := cid, text := msg }
  let verbatim := match spec.document, doc? with
    | none, _ => []
    | some path, none => [{ ok := true, warn := true, check := "verbatim", text := s!"{path} was not read; verbatim check skipped" }]
    | some path, some (.error e) => [{ ok := true, warn := true, check := "verbatim", text := s!"{path} could not be read ({e}); verbatim check skipped" }]
    | some path, some (.ok doc) => spec.clauses.map fun c =>
      { ok := occursIn doc c.source, check := "verbatim", clause := c.id, text := s!"{c.id}: text occurs verbatim in {path}" }
  let approved := spec.clauses.map fun c =>
    if c.stale then
      if c.approvedHash == 0 then
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: not yet approved; once reviewed, declare `Approved {c.source.hash}`. Unapproved: {", ".intercalate c.invalidated}" }
      else
        { ok := false, check := "approved", clause := c.id,
          text := s!"STALE {c.id}: text differs from the approved text (current hash {c.source.hash}); review invalidated for {", ".intercalate c.invalidated}" }
    else { ok := true, check := "approved", clause := c.id, text := s!"{c.id}: approved mapping current" }
  perClause ++ [named] ++ fromChecks ++ verbatim ++ approved

/-- Read the document named by the spec, relative to the program's directory. -/
def readDocument (spec : Spec) (programDir : System.FilePath) : IO (Option (Except String String)) := do
  match spec.document with
  | none => return none
  | some path =>
    let f := programDir / path
    try
      let txt ← IO.FS.readFile f
      return some (.ok txt)
    catch e => return some (.error (toString e))

/-- The span table of one clause (`charter trace <clause>`). -/
def traceTable (c : Clause) : String :=
  let reg : Register → String
    | .norm => "norm" | .definition => "definition" | .invariant => "invariant" | .acceptance => "acceptance" | .commentary => "commentary"
  let rows := c.spans.map fun s =>
    s!"  {reg s.register}  {showString s.text}  => {if s.meaning.isEmpty then "(no rule)" else ", ".intercalate s.meaning}"
  s!"{c.id}  (approved: {!c.stale}; hash {c.source.hash})\n" ++ "\n".intercalate rows

end Charter.Cli
