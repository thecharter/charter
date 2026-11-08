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
          for d in ds do
            lspDiags := lspDiags.push (mkLspDiag it.pos.line it.pos.col 1 d.code d.message)
        | .ok (spec', _, ws) =>
          spec := spec'
          for w in ws do
            lspDiags := lspDiags.push (mkLspDiag it.pos.line it.pos.col 2 w.code w.message)
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

/-- Extract the identifier/clause token under `(line0, char0)` in `content`. -/
def wordAtPosition (content : String) (line0 char0 : Nat) : String := Id.run do
  let lines := content.splitOn "\n"
  match lines[line0]? with
  | none => return ""
  | some ln =>
    let cs := ln.toList.toArray
    if char0 ≥ cs.size then return ""
    else
      let isTokChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.'
      let mut start := char0
      while start > 0 && isTokChar cs[start - 1]! do
        start := start - 1
      let mut stop := char0
      while stop < cs.size && isTokChar cs[stop]! do
        stop := stop + 1
      return String.mk ((cs.extract start stop).toList)

def hoverMarkdownFor (spec : Spec) (tok : String) : Option String :=
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
      | .immunity _ => "Immunity"
      | .event _ => "Event"
    let domStr := Pretty.fmtDomain t.domain
    let spanLines := t.spans.map fun (cid, q) =>
      let st := match spec.clauses.find? (·.id == cid) with
        | some cl => if cl.stale then " *(STALE)*" else " *(approved)*"
        | none => ""
      s!"- **`{cid}`**{st}: \"{q}\""
    let provBlock := if spanLines.isEmpty then "" else "\n\n**English Provenance:**\n" ++ "\n".intercalate spanLines
    some s!"**`{tok}`** — `{kindLabel}`\n\nDomain: `{domStr}`{provBlock}"
  else none

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
        let tok := wordAtPosition entry.content l0 c0
        match hoverMarkdownFor entry.spec tok with
        | none => Json.null
        | some md =>
          Json.mkObj [("contents", Json.mkObj [("kind", Json.str "markdown"), ("value", Json.str md)])]
    sendLspMessage stdout (Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", idOpt.getD Json.null), ("result", resJson)])
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
