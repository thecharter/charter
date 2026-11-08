import Charter.Cli.Load
import Charter.Cli.Provenance
import Charter.Resolve.Static
import Charter.Surface.Pretty
import Lean.Data.Json

/-!
# Charter.Cli.Doc — Lawyer & Policy-Author Institutional Rulebook (`G5.4`, `docs/rfc.md` §10.3)

`charter doc <file.charter> [-o <out.md>] [--out json]` generates:
1. Side-by-side consolidated authoritative `Clause` prose + formal `CIR` rules & approval status;
2. `Default` / `Exception` / `Priority` statutory decision tables;
3. Hohfeldian `Power` / `Duty` / `Immunity` standing matrices;
4. Invariant, Temporal `Property`, and provenance coverage summary.
-/

namespace Charter.Cli

open Lean (Json)

structure DocCliOpts where
  input  : Option String := none
  output : Option String := none
  json   : Bool := false

def parseDocArgs : List String → DocCliOpts → Except String DocCliOpts
  | [], o => .ok o
  | "-o" :: p :: rest, o => parseDocArgs rest { o with output := some p }
  | ["-o"], _ => .error "-o needs an output file path"
  | "--out" :: "json" :: rest, o => parseDocArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseDocArgs rest { o with json := false }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.input.isNone then parseDocArgs rest { o with input := some a }
    else .error s!"unexpected extra input {a}"

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
  let usage := "usage: charter doc <file.charter> [-o <out.md>] [--out json]"
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
  let (md, j) := renderRulebook f spec cov
  let outStr := if opts.json then j.pretty ++ "\n" else md
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
