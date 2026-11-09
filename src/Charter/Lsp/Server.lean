import Charter.Cli.Load
import Charter.Cli.Fmt
import Charter.Cli.Provenance
import Charter.Resolve.Static
import Lean.Data.Json

/-!
# Charter.Lsp.Server — Language Server Protocol 3.17 Implementation (`G5.3`)

Implements `charter lsp` over standard `Content-Length: <N>\r\n\r\n<json>` stdio framing:
1. Live `CHR` static + Law 8 provenance diagnostics (`textDocument/publishDiagnostics` on
   `didOpen`, `didChange`, `didSave`);
2. Canonical document formatting (`textDocument/formatting` via `Surface.Pretty`);
3. Rich hover cards (`textDocument/hover`: declared kind, inferred domain/scale, verbatim
   `From` English spans, and `Clause` approval status);
4. Go-to-definition (`textDocument/definition`: jumps to rule declarations or directly to the
   1-indexed Markdown heading/line in `Document` via `locateClauseAnchor`).
-/

namespace Charter.Lsp

open Lean (Json)

structure DocEntry where
  uri     : String
  path    : String
  content : String
  spec    : Spec := emptySpec

def uriToPath (uri : String) : String :=
  if uri.startsWith "file://" then uri.drop 7 else uri

def sendLspMessage (stdout : IO.FS.Stream) (msg : Json) : IO Unit := do
  let body := msg.compress
  let byteLen := body.utf8ByteSize
  stdout.putStr s!"Content-Length: {byteLen}\r\n\r\n{body}"
  stdout.flush

partial def readContentLength (stdin : IO.FS.Stream) (len? : Option Nat := none) : IO (Option Nat) := do
  let line ← stdin.getLine
  if line.isEmpty then return none
  let trimmed := line.trim
  if trimmed.isEmpty then return len?
  else if trimmed.startsWith "Content-Length:" then
    let n? := (trimmed.drop 15).trim.toNat?
    readContentLength stdin n?
  else
    readContentLength stdin len?

def readLspPayload (stdin : IO.FS.Stream) : IO (Option Json) := do
  let some n ← readContentLength stdin none | return none
  let bytes ← stdin.read n.toUSize
  if bytes.isEmpty then return none
  match String.fromUTF8? bytes with
  | none => return none
  | some txt =>
    match Json.parse txt with
    | .ok j => return some j
    | .error _ => return none

/-- Analyze `content` for `uri`, returning `(resolvedSpec, lspDiagnosticsArray)`. -/
def analyzeDocument (uri content : String) : IO (Spec × Array Json) := do
  let path := uriToPath uri
  let mut lspDiags : Array Json := #[]
  let mkLspDiag (line col : Nat) (sev : Nat) (code msg : String) : Json :=
    let l0 := if line > 0 then line - 1 else 0
    let c0 := if col > 0 then col - 1 else 0
    let pos := Json.mkObj [("line", Json.num l0), ("character", Json.num c0)]
    Json.mkObj [
      ("range", Json.mkObj [("start", pos), ("end", pos)]),
      ("severity", Json.num sev),
      ("code", Json.str code),
      ("source", Json.str "charter"),
      ("message", Json.str msg)
    ]
  match parseSource content with
  | .error d =>
    lspDiags := lspDiags.push (mkLspDiag d.pos.line d.pos.col 1 d.code d.message)
    return (emptySpec, lspDiags)
  | .ok items =>
    let mut spec := emptySpec
    for it in items do
      match it.val with
      | .inl _ => pure ()
      | .inr p =>
        match resolvePhrase spec p with
        | .error ds =>
          spec := recoverPhraseDecls spec p
          for d in ds do
            let dp := (d.withPos it.pos).pos
            lspDiags := lspDiags.push (mkLspDiag dp.line dp.col 1 d.code d.message)
        | .ok (spec', _, ws) =>
          spec := spec'
          for w in ws do
            let wp := (w.withPos it.pos).pos
            lspDiags := lspDiags.push (mkLspDiag wp.line wp.col 2 w.code w.message)
    if !spec.clauses.isEmpty || spec.document.isSome || !spec.documents.isEmpty then
      let dir := (System.FilePath.mk path).parent.getD "."
      let loaded ← Cli.readDocuments spec dir
      let locks ← Cli.readClauseLocks dir
      spec := Cli.hydrateClausesFromDocs spec loaded
      let claims := Cli.provenanceReportDocs spec loaded locks
      for c in claims do
        if !c.ok then
          lspDiags := lspDiags.push (mkLspDiag 1 1 1 "LAW8" c.text)
    return (spec, lspDiags)

/-- Extract `(identifier, optionalCallArgs)` under `(line0, char0)` in `content` (`#72`). -/
def callAtPosition (content : String) (line0 char0 : Nat) : String × Option String := Id.run do
  let lines := content.splitOn "\n"
  match lines[line0]? with
  | none => return ("", none)
  | some ln =>
    let cs := ln.toList.toArray
    if char0 ≥ cs.size then return ("", none)
    else
      let isTokChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '\''
      let mut start := char0
      while start > 0 && isTokChar cs[start - 1]! do
        start := start - 1
      let mut stop := char0
      while stop < cs.size && isTokChar cs[stop]! do
        stop := stop + 1
      let tok := String.mk ((cs.extract start stop).toList)
      if tok.isEmpty then return ("", none)
      else if stop < cs.size && cs[stop]! == '(' then
        let mut idx := stop + 1
        let mut depth : Nat := 1
        let mut argChars : List Char := []
        while idx < cs.size && depth > 0 do
          let ch := cs[idx]!
          if ch == '(' then
            depth := depth + 1
            argChars := argChars ++ [ch]
          else if ch == ')' then
            depth := depth - 1
            if depth > 0 then argChars := argChars ++ [ch]
          else
            argChars := argChars ++ [ch]
          idx := idx + 1
        if depth == 0 then return (tok, some (String.mk argChars))
        else return (tok, none)
      else return (tok, none)

/-- Extract the identifier/clause token under `(line0, char0)` in `content`. -/
def wordAtPosition (content : String) (line0 char0 : Nat) : String :=
  (callAtPosition content line0 char0).1

/-- Split top-level comma-separated call arguments without splitting nested parentheses. -/
def splitTopLevelArgs (raw : String) : List String := Id.run do
  if raw.trim.isEmpty then return []
  let mut parts : List String := []
  let mut cur : List Char := []
  let mut depth : Nat := 0
  for ch in raw.toList do
    if ch == '(' then
      depth := depth + 1
      cur := cur ++ [ch]
    else if ch == ')' then
      if depth > 0 then depth := depth - 1
      cur := cur ++ [ch]
    else if ch == ',' && depth == 0 then
      parts := parts ++ [(String.mk cur).trim]
      cur := []
    else
      cur := cur ++ [ch]
  let last := (String.mk cur).trim
  if !last.isEmpty then parts := parts ++ [last]
  return parts

/-- Expand implicit constructor arguments (`#72`): e.g. `signed()` ->
`signed(grantor = grantor, grantee = grantee, parcel = parcel)`. -/
def expandConstructorCall (tok : String) (t : TypeSpec) (rawArgs? : Option String) : Option String :=
  match t.domain with
  | .products xs =>
    if xs.isEmpty then none
    else
      let fullTemplate := s!"{tok}(" ++ ", ".intercalate (xs.map fun x => s!"{x} = {x}") ++ ")"
      match rawArgs? with
      | none => some fullTemplate
      | some raw =>
        let given := splitTopLevelArgs raw
        if given.isEmpty then some fullTemplate
        else
          let hasNamed := given.any fun g => (g.splitOn "=").length == 2
          if hasNamed then
            let namedPairs : List (String × String) := given.filterMap fun g =>
              match g.splitOn "=" with
              | [k, v] => some (k.trim, v.trim)
              | _ => none
            let expanded := xs.map fun x =>
              let xsName := toString x
              match namedPairs.find? (·.1 == xsName) with
              | some (_, rhs) => s!"{xsName} = {rhs}"
              | none => s!"{xsName} = {xsName}"
            some (s!"{tok}(" ++ ", ".intercalate expanded ++ ")")
          else
            let expanded := (List.range xs.length).map fun idx =>
              let xName := toString xs[idx]!
              match given[idx]? with
              | some rhs => s!"{xName} = {rhs}"
              | none => s!"{xName} = {xName}"
            some (s!"{tok}(" ++ ", ".intercalate expanded ++ ")")
  | _ => none

/-- Render `Default` / `Exception` rules in topological priority order (`#72`: highest priority first). -/
def formatDefeasibleRuleOrder (spec : Spec) (tok : String) (t : TypeSpec) : String := Id.run do
  if t.defeasibleRules.isEmpty then return ""
  let normId (rid : String) : String :=
    if rid.startsWith (tok ++ ".") then rid.drop (tok.length + 1) else rid
  let rankPairs : List (String × String) :=
    (spec.rankEdges.filter (·.1 == tok)).map fun (_, e) => (normId e.higherRule, normId e.lowerRule)
  let overridesDirect (hi lo : DefeasibleRule) : Bool :=
    let nhi := normId hi.id
    let nlo := normId lo.id
    hi.overrides.any (fun ov => normId ov == nlo) ||
    rankPairs.any (fun (a, b) => a == nhi && b == nlo)
  -- Topological sort: emit rules that no remaining rule overrides first (highest priority first)
  let mut remaining := t.defeasibleRules
  let mut ordered : List DefeasibleRule := []
  for _ in [0 : t.defeasibleRules.length] do
    if !remaining.isEmpty then
      let pick? := remaining.find? fun cand =>
        !remaining.any (fun other => other.id != cand.id && overridesDirect other cand)
      let chosen := pick?.getD remaining.head!
      ordered := ordered ++ [chosen]
      remaining := remaining.filter (·.id != chosen.id)
  let mut lines : List String := []
  let mut rankIdx := 1
  for r in ordered do
    let tier := if r.isDefault then "Default" else "Exception"
    let ovStr := if r.overrides.isEmpty then "" else s!" *(overrides {", ".intercalate r.overrides})*"
    let csq := match r.conseq with
      | .holdsBool true => "Holds"
      | .holdsBool false => "Rejects"
      | .yieldsVal v => s!"Yields `{Pretty.fmtTerm v}`"
    lines := lines ++ [s!"{rankIdx}. **{tier} `{r.id}`**{ovStr}: {csq} `When {Pretty.fmtTerm r.cond}`"]
    rankIdx := rankIdx + 1
  return "\n\n**Defeasible Rule Order (highest priority first):**\n" ++ "\n".intercalate lines

def hoverMarkdownFor (spec : Spec) (tok : String) (rawArgs? : Option String := none) : Option String :=
  if tok.isEmpty then none
  else if let some c := spec.clauses.find? (·.id == tok) then
    let st := if c.stale then "STALE (re-approval required)" else "Approved & current"
    some s!"**Clause `{c.id}`** — *{st}*\n\n> {c.source}"
  else if let some t := spec.findDecl tok then
    let kindLabel := match t.kind with
      | .act a => if a.isFinding then "Finding" else if a.isAmend then "Amend" else if a.isPower then "Power" else if a.physical then "Physical Act" else "Act"
      | .fact fs => if fs.invariant then (if fs.entrenched then "Entrenched Invariant" else "Invariant")
                    else if fs.evidenced then "Evidenced Fact (4-valued)" else "Fact"
      | .duty _ => "Duty"
      | .immunity im => if im.isProtection then "Protection" else "Immunity"
      | .event _ => "Event"
    let domStr := Pretty.fmtDomain t.domain
    let ctorBlock := match expandConstructorCall tok t rawArgs? with
      | some exp =>
        let hdr := if rawArgs?.isSome then "Expanded Application" else "Constructor"
        s!"\n\n{hdr}: `{exp}`"
      | none => ""
    let defBlock := formatDefeasibleRuleOrder spec tok t
    let spanLines := t.spans.map fun (cid, q) =>
      let st := match spec.clauses.find? (·.id == cid) with
        | some cl => if cl.stale then " *(STALE)*" else " *(approved)*"
        | none => ""
      s!"- **`{cid}`**{st}: \"{q}\""
    let provBlock := if spanLines.isEmpty then "" else "\n\n**English Provenance:**\n" ++ "\n".intercalate spanLines
    some s!"**`{tok}`** — `{kindLabel}`\n\nDomain: `{domStr}`{ctorBlock}{defBlock}{provBlock}"
  else none

/-- Compute LSP 3.17 `textDocument/inlayHint` hints expanding elided `tok()` constructor arguments (`#72`). -/
def inlayHintsForRange (entry : DocEntry) (startLine endLine : Nat) : Array Json := Id.run do
  let lines := entry.content.splitOn "\n"
  let isTokChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '\''
  let mut hints : Array Json := #[]
  let hi := min lines.length (endLine + 1)
  for l0 in [startLine : hi] do
    let cs := (lines[l0]!).toList.toArray
    let mut i := 0
    while i + 1 < cs.size do
      if cs[i]! == '(' && cs[i + 1]! == ')' && i > 0 && isTokChar cs[i - 1]! then
        let mut s := i
        while s > 0 && isTokChar cs[s - 1]! do
          s := s - 1
        let tok := String.mk ((cs.extract s i).toList)
        if let some t := entry.spec.findDecl tok then
          match t.domain with
          | .products xs =>
            if !xs.isEmpty then
              let lbl := ", ".intercalate (xs.map fun x => s!"{x} = {x}")
              hints := hints.push (Json.mkObj [
                ("position", Json.mkObj [("line", Json.num l0), ("character", Json.num ((i + 1 : Nat)))]),
                ("label", Json.str lbl),
                ("kind", Json.num 2)
              ])
          | _ => pure ()
        i := i + 2
      else
        i := i + 1
  return hints

def definitionLocationFor (entry : DocEntry) (tok : String) : IO Json := do
  if tok.isEmpty then return Json.null
  let dir := (System.FilePath.mk entry.path).parent.getD "."
  -- 1. If `tok` is a Clause ID (or a rule grounded in a Clause with a readable Document), jump to Markdown line!
  let targetClause? : Option Clause :=
    match entry.spec.clauses.find? (·.id == tok) with
    | some c => some c
    | none =>
      match entry.spec.findDecl tok with
      | some t =>
        match t.spans.head? with
        | some (cid, _) => entry.spec.clauses.find? (·.id == cid)
        | none => none
      | none => none
  if let some c := targetClause? then
    let loaded ← Cli.readDocuments entry.spec dir
    let docHit? := match c.docId with
      | some did => loaded.find? (fun (p : SourceDoc × Except String String) => p.1.id == some did)
      | none => loaded.head?
    if let some (sd, .ok docTxt) := docHit? then
      if let some anc := locateClauseAnchor docTxt c.source then
        let mdPath := (dir / sd.path).toString
        let l0 := if anc.line > 0 then anc.line - 1 else 0
        let pos := Json.mkObj [("line", Json.num l0), ("character", Json.num 0)]
        return Json.mkObj [
          ("uri", Json.str ("file://" ++ mdPath)),
          ("range", Json.mkObj [("start", pos), ("end", pos)])
        ]
  -- 2. Otherwise jump to declaration line inside current `.charter` document
  let lines := entry.content.splitOn "\n"
  let mut foundLine : Option Nat := none
  for idx in [0 : lines.length] do
    let ln := lines[idx]!.trim
    if foundLine.isNone && (Cli.occursIn ln s!" {tok} " || ln.endsWith s!" {tok}" || ln.endsWith s!" {tok}.") then
      foundLine := some idx
  match foundLine with
  | some l0 =>
    let pos := Json.mkObj [("line", Json.num l0), ("character", Json.num 0)]
    return Json.mkObj [("uri", Json.str entry.uri), ("range", Json.mkObj [("start", pos), ("end", pos)])]
  | none => return Json.null

partial def lspLoop (stdin stdout : IO.FS.Stream) (docs : List DocEntry) : IO UInt32 := do
  let some msg ← readLspPayload stdin | return 0
  let method := (msg.getObjValAs? String "method").toOption.getD ""
  let idOpt := (msg.getObjVal? "id").toOption
  let params := (msg.getObjVal? "params").toOption.getD (Json.mkObj [])
  match method with
  | "initialize" =>
    let caps := Json.mkObj [
      ("textDocumentSync", Json.num 1),
      ("hoverProvider", Json.bool true),
      ("inlayHintProvider", Json.bool true),
      ("definitionProvider", Json.bool true),
      ("documentFormattingProvider", Json.bool true)
    ]
    let resp := Json.mkObj [
      ("jsonrpc", Json.str "2.0"),
      ("id", idOpt.getD (Json.num 0)),
      ("result", Json.mkObj [
        ("capabilities", caps),
        ("serverInfo", Json.mkObj [("name", Json.str "charter-lsp"), ("version", Json.str "1.0.0")])
      ])
    ]
    sendLspMessage stdout resp
    lspLoop stdin stdout docs
  | "shutdown" =>
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", Json.null)])
    lspLoop stdin stdout docs
  | "exit" =>
    return 0
  | "textDocument/didOpen" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let text := (td.getObjValAs? String "text").toOption.getD ""
    let (spec, diags) ← analyzeDocument uri text
    let notif := Json.mkObj [
      ("jsonrpc", Json.str "2.0"),
      ("method", Json.str "textDocument/publishDiagnostics"),
      ("params", Json.mkObj [("uri", Json.str uri), ("diagnostics", Json.arr diags)])
    ]
    sendLspMessage stdout notif
    let docs' := { uri, path := uriToPath uri, content := text, spec } :: docs.filter (·.uri != uri)
    lspLoop stdin stdout docs'
  | "textDocument/didChange" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let changes := (params.getObjValAs? (Array Json) "contentChanges").toOption.getD #[]
    let text := match changes[0]? with
      | some c => (c.getObjValAs? String "text").toOption.getD ""
      | none => ""
    let (spec, diags) ← analyzeDocument uri text
    let notif := Json.mkObj [
      ("jsonrpc", Json.str "2.0"),
      ("method", Json.str "textDocument/publishDiagnostics"),
      ("params", Json.mkObj [("uri", Json.str uri), ("diagnostics", Json.arr diags)])
    ]
    sendLspMessage stdout notif
    let docs' := { uri, path := uriToPath uri, content := text, spec } :: docs.filter (·.uri != uri)
    lspLoop stdin stdout docs'
  | "textDocument/hover" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let pos := (params.getObjVal? "position").toOption.getD (Json.mkObj [])
    let l0 := (pos.getObjValAs? Nat "line").toOption.getD 0
    let c0 := (pos.getObjValAs? Nat "character").toOption.getD 0
    let resJson := match docs.find? (·.uri == uri) with
      | none => Json.null
      | some entry =>
        let (tok, rawArgs?) := callAtPosition entry.content l0 c0
        match hoverMarkdownFor entry.spec tok rawArgs? with
        | none => Json.null
        | some md =>
          Json.mkObj [("contents", Json.mkObj [("kind", Json.str "markdown"), ("value", Json.str md)])]
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", resJson)])
    lspLoop stdin stdout docs
  | "textDocument/inlayHint" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let rng := (params.getObjVal? "range").toOption.getD (Json.mkObj [])
    let sPos := (rng.getObjVal? "start").toOption.getD (Json.mkObj [])
    let ePos := (rng.getObjVal? "end").toOption.getD (Json.mkObj [])
    let sLine := (sPos.getObjValAs? Nat "line").toOption.getD 0
    let eLine := (ePos.getObjValAs? Nat "line").toOption.getD 10000
    let hintsJson := match docs.find? (·.uri == uri) with
      | none => Json.arr #[]
      | some entry => Json.arr (inlayHintsForRange entry sLine eLine)
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", hintsJson)])
    lspLoop stdin stdout docs
  | "textDocument/definition" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let pos := (params.getObjVal? "position").toOption.getD (Json.mkObj [])
    let l0 := (pos.getObjValAs? Nat "line").toOption.getD 0
    let c0 := (pos.getObjValAs? Nat "character").toOption.getD 0
    let locJson ← match docs.find? (·.uri == uri) with
      | none => pure Json.null
      | some entry => definitionLocationFor entry (wordAtPosition entry.content l0 c0)
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", locJson)])
    lspLoop stdin stdout docs
  | "textDocument/formatting" =>
    let td := (params.getObjVal? "textDocument").toOption.getD (Json.mkObj [])
    let uri := (td.getObjValAs? String "uri").toOption.getD ""
    let editsJson : Json := match docs.find? (·.uri == uri) with
      | none => Json.arr #[]
      | some entry =>
        match Pretty.formatAndVerify entry.content with
        | .error _ => Json.arr #[]
        | .ok formatted =>
          let nLines := (entry.content.splitOn "\n").length + 1
          let range := Json.mkObj [
            ("start", Json.mkObj [("line", Json.num 0), ("character", Json.num 0)]),
            ("end", Json.mkObj [("line", Json.num nLines), ("character", Json.num 0)])
          ]
          Json.arr #[Json.mkObj [("range", range), ("newText", Json.str formatted)]]
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", editsJson)])
    lspLoop stdin stdout docs
  | _ =>
    if let some reqId := idOpt then
      sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", reqId), ("result", Json.null)])
    lspLoop stdin stdout docs

def lspCommand (_args : List String) : IO UInt32 := do
  lspLoop (← IO.getStdin) (← IO.getStdout) []

end Charter.Lsp
