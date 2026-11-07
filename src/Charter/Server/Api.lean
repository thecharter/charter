import Charter.Server.Protocol

/-!
# Charter.Server.Api — Operator-Blind JSON/stdio & MCP Service Dispatcher (`G4.5`, `D27`)

Exposes all canonical `charter-server` operations (`docs/rfc.md` §8.2) over newline-delimited
JSON (and MCP `tools/list` / `tools/call` envelopes), persisting every committed transition
synchronously to the hash-chained durable log and optional checkpoint snapshot.
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

structure InstitutionRuntime where
  institutionId : String
  lawHash       : String
  certificate   : Artifact.ArtifactCertificate
  config        : Config
  seqNo         : Nat := 0
  lastEntryHash : String := "GENESIS"
  reservations  : ReservationTable := {}
  vault         : List VaultRecord := []
  clockPolicy   : ClockPolicy := {}
  logPath       : Option System.FilePath := none
  snapshotPath  : Option System.FilePath := none
  secretKey     : String := Artifact.defaultDevSigningKey

def parseElemArg (j : Json) : Except String Elem :=
  match j with
  | .str s => .ok (.str s)
  | .num n => .ok (.int n.mantissa)
  | _ => fromJson? (α := Elem) j

def parseElemArgs (j : Json) : Except String (List Elem) := do
  match j.getObjValAs? (Array Json) "args" with
  | .ok arr => arr.toList.mapM parseElemArg
  | .error _ => .ok []

def reasonGraphJson (rg : ReasonGraph) : Json :=
  Json.mkObj [
    ("subject", Json.str rg.subject),
    ("lawful", Json.str rg.lawful.asString),
    ("valid", Json.str rg.valid.asString),
    ("redactedCount", Json.num rg.redactedCount),
    ("unmetEvidence", Json.arr (rg.unmetEvidence.map fun (f, st, _, _) =>
      Json.mkObj [("fact", Json.str f), ("status", Json.str st.asString)]).toArray),
    ("nodes", Json.arr (rg.nodes.map fun n =>
      Json.mkObj [("id", Json.str n.id), ("kind", Json.str n.kind),
                  ("status", Json.str n.status), ("detail", Json.str n.detail)]).toArray)
  ]

/-- Append one committed `LogEntry` to disk (when `rt.logPath` is configured) and update `rt`. -/
def commitTransition (rt : InstitutionRuntime) (ev : ServerEvent)
    (nextCfg : Config) (outcome : String) (lawful valid : TriBool) : IO (InstitutionRuntime × LogEntry) := do
  let rootAfter := computeStateRoot rt.lawHash nextCfg
  let entry := mkSignedLogEntry rt.secretKey rt.institutionId rt.seqNo
    rt.lastEntryHash rt.lawHash nextCfg.lawVersion ev
    outcome lawful.asString valid.asString rootAfter
  if let some lp := rt.logPath then
    if let some parent := lp.parent then IO.FS.createDirAll parent
    let line := (toJson entry).compress ++ "\n"
    let existing ← try IO.FS.readFile lp catch _ => pure ""
    IO.FS.writeFile lp (existing ++ line)
  let rt' : InstitutionRuntime := {
    rt with
    config := nextCfg
    seqNo := rt.seqNo + 1
    lastEntryHash := entry.entryHash
  }
  if let some sp := rt'.snapshotPath then
    if let some parent := sp.parent then IO.FS.createDirAll parent
    let snap := mkSignedSnapshot rt'.secretKey rt'.institutionId rt'.seqNo rt'.lastEntryHash rt'.lawHash rt'.config
    IO.FS.writeFile sp ((toJson snap).pretty ++ "\n")
  return (rt', entry)

def envelopeOk (rt : InstitutionRuntime) (op : String) (extra : List (String × Json)) : Json :=
  let root := computeStateRoot rt.lawHash rt.config
  let sig := Artifact.hmacSha256 rt.secretKey s!"resp:{rt.institutionId}:{rt.lawHash}:{rt.seqNo}:{root}:{op}"
  Json.mkObj ([
    ("ok", Json.bool true),
    ("op", Json.str op),
    ("institutionId", Json.str rt.institutionId),
    ("lawHash", Json.str rt.lawHash),
    ("lawVersion", Json.num rt.config.lawVersion),
    ("stateVersion", Json.num rt.seqNo),
    ("stateRoot", Json.str root),
    ("time", Json.num rt.config.state.time),
    ("assurance", Json.str "checked"),
    ("serverSignature", Json.str sig)
  ] ++ extra)

def envelopeErr (rt : InstitutionRuntime) (op msg : String) : Json :=
  Json.mkObj [
    ("ok", Json.bool false),
    ("op", Json.str op),
    ("institutionId", Json.str rt.institutionId),
    ("lawHash", Json.str rt.lawHash),
    ("stateVersion", Json.num rt.seqNo),
    ("error", Json.str msg)
  ]

/-- Handle one parsed JSON request (supporting both direct `{"op": ...}` and MCP `tools/list` / `tools/call`). -/
def handleRequest (rt : InstitutionRuntime) (req : Json) : IO (InstitutionRuntime × Json) := do
  -- MCP envelope support (`method: "tools/list"` or `"tools/call"`)
  if let .ok mcpMethod := req.getObjValAs? String "method" then
    let reqId := (req.getObjVal? "id").toOption.getD Json.null
    if mcpMethod == "tools/list" then
      let tools := #["GetLaw", "GetState", "GetCoverageManifest", "Evaluate", "Reserve",
                     "Authorize", "ConfirmExecution", "ReconcileExecution", "ExercisePower",
                     "ObserveExternal", "SubmitEvidence", "AdvanceClock", "Explain", "AmendLaw"]
      let resp := Json.mkObj [
        ("jsonrpc", Json.str "2.0"), ("id", reqId),
        ("result", Json.mkObj [("tools", Json.arr (tools.map fun t => Json.mkObj [("name", Json.str t)]))])
      ]
      return (rt, resp)
    else if mcpMethod == "tools/call" then
      match (do
        let params ← req.getObjVal? "params"
        let toolName ← params.getObjValAs? String "name"
        let argsObj := (params.getObjVal? "arguments").toOption.getD (Json.mkObj [])
        match argsObj with
        | .obj kvs => .ok (Json.mkObj (("op", Json.str toolName) :: kvs.toList))
        | _ => .ok (Json.mkObj [("op", Json.str toolName)])) with
      | .error e =>
        return (rt, Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", reqId), ("error", Json.str e)])
      | .ok innerReq =>
        let (rt', innerResp) ← handleDirectRequest rt innerReq
        return (rt', Json.mkObj [("jsonrpc", Json.str "2.0"), ("id", reqId), ("result", innerResp)])
  handleDirectRequest rt req
where
  handleDirectRequest (rt : InstitutionRuntime) (req : Json) : IO (InstitutionRuntime × Json) := do
    let op := (req.getObjValAs? String "op").toOption.getD ""
    -- Optional tenant isolation check when client specifies `institutionId`
    if let .ok reqInst := req.getObjValAs? String "institutionId" then
      if reqInst != rt.institutionId then
        return (rt, envelopeErr rt op s!"cross-tenant request rejected: server hosts `{rt.institutionId}`, request named `{reqInst}`")
    match op with
    | "GetLaw" =>
      return (rt, envelopeOk rt op [
        ("certificate", toJson rt.certificate),
        ("declaredRules", Json.arr (rt.config.spec.ruleIds.map Json.str).toArray),
        ("invariants", Json.arr (rt.config.spec.invariants.map Json.str).toArray)
      ])
    | "GetState" =>
      let held := rt.config.state.holdsList.filter (fun te => !isInternalEvDom te.2 && te.2 != defConflictDom)
      return (rt, envelopeOk rt op [
        ("holdingFacts", Json.arr (held.map (Json.str ∘ Tagged.pp)).toArray),
        ("activeReservations", Json.num (rt.reservations.records.filter (·.status.locksCapacity)).length)
      ])
    | "GetCoverageManifest" =>
      return (rt, envelopeOk rt op [("coverageManifest", coverageManifestJson rt.institutionId rt.lawHash rt.config.spec)])
    | "Evaluate" =>
      match (do
        let act ← req.getObjValAs? String "action"
        let args ← parseElemArgs req
        evaluateServerEvent rt.config (.triggerAct act args) false) with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok dec =>
        return (rt, envelopeOk rt op [
          ("outcome", Json.str dec.outcome),
          ("occurred", Json.str dec.occurred),
          ("lawful", Json.str dec.lawful.asString),
          ("valid", Json.str dec.valid.asString),
          ("unmetEvidence", Json.arr (dec.unmetEvidence.map fun (f, st) =>
            Json.mkObj [("fact", Json.str f), ("status", Json.str st.asString)]).toArray),
          ("reason", Json.str dec.reasonSummary)
        ])
    | "Reserve" =>
      let intentId := (req.getObjValAs? String "intentId").toOption.getD ""
      let actor := (req.getObjValAs? String "actor").toOption.getD ""
      let action := (req.getObjValAs? String "action").toOption.getD ""
      let resKey := (req.getObjValAs? String "resource").toOption.getD ""
      let amount := (req.getObjValAs? Int "amount").toOption.getD 0
      let cap? := (req.getObjValAs? Int "resourceCap").toOption
      let expVer? := (req.getObjValAs? Nat "expectedStateVersion").toOption
      let ttl := (req.getObjValAs? Int "ttl").toOption.getD 10
      match parseElemArgs req with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok args =>
        -- Check legal prerequisites via hypothetical Evaluate first (§8.3 step 2)
        match evaluateServerEvent rt.config (.triggerAct action args) false with
        | .error e => return (rt, envelopeErr rt op e)
        | .ok dec =>
          if dec.outcome != "Allow" then
            return (rt, envelopeOk rt op [
              ("outcome", Json.str dec.outcome),
              ("lawful", Json.str dec.lawful.asString),
              ("valid", Json.str dec.valid.asString),
              ("reason", Json.str dec.reasonSummary)
            ])
          else
            match reserveIntent rt.reservations rt.institutionId rt.config.state.time
                    rt.seqNo expVer? intentId actor action args resKey amount cap? ttl with
            | .error e => return (rt, envelopeErr rt op e)
            | .ok (tbl', recOut) =>
              let rt' := { rt with reservations := tbl' }
              return (rt', envelopeOk rt' op [
                ("outcome", Json.str "Reserved"),
                ("reservation", toJson recOut)
              ])
    | "Authorize" =>
      let intentId := (req.getObjValAs? String "intentId").toOption.getD ""
      match authorizeReservation rt.secretKey rt.reservations rt.institutionId rt.lawHash
              rt.config.state.time rt.seqNo intentId with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok (tbl', tok) =>
        let rt' := { rt with reservations := tbl' }
        return (rt', envelopeOk rt' op [
          ("outcome", Json.str "Allow"),
          ("token", toJson tok)
        ])
    | "ConfirmExecution" =>
      let statusStr := (req.getObjValAs? String "status").toOption.getD "confirmed"
      let receipt? := (req.getObjValAs? String "receiptRef").toOption
      match (do let tj ← req.getObjVal? "token"; fromJson? (α := AuthorizationToken) tj) with
      | .error e => return (rt, envelopeErr rt op s!"invalid token payload: {e}")
      | .ok tok =>
        match confirmExecution rt.secretKey rt.reservations rt.institutionId rt.lawHash
                rt.config.state.time tok statusStr receipt? with
        | .error e => return (rt, envelopeErr rt op e)
        | .ok (tbl', sagaSt, recUpdated) =>
          if sagaSt == .executedConfirmed then
            let ev := ServerEvent.triggerAct recUpdated.action recUpdated.args recUpdated.intentId
            match evaluateServerEvent rt.config ev true with
            | .error e => return (rt, envelopeErr rt op e)
            | .ok dec =>
              let rtPre := { rt with reservations := tbl' }
              let (rt', logEntry) ← commitTransition rtPre ev dec.nextConfig dec.outcome dec.lawful dec.valid
              return (rt', envelopeOk rt' op [
                ("sagaStatus", Json.str sagaSt.asString),
                ("logEntryHash", Json.str logEntry.entryHash)
              ])
          else
            -- `ExecutedUnknown` (`T35`): lock held, token consumed, legal state NOT optimistically settled!
            let rt' := { rt with reservations := tbl' }
            return (rt', envelopeOk rt' op [
              ("sagaStatus", Json.str sagaSt.asString),
              ("pendingReconciliation", Json.bool true)
            ])
    | "ReconcileExecution" =>
      let intentId := (req.getObjValAs? String "intentId").toOption.getD ""
      let observed := (req.getObjValAs? Bool "observedExecuted").toOption.getD false
      let receipt := (req.getObjValAs? String "receiptRef").toOption.getD "reconcile"
      match reconcileUnknown rt.reservations intentId observed receipt with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok (tbl', recResolved) =>
        let rtPre := { rt with reservations := tbl' }
        if observed then
          let ev := ServerEvent.triggerAct recResolved.action recResolved.args recResolved.intentId
          match evaluateServerEvent rtPre.config ev true with
          | .error e => return (rt, envelopeErr rt op e)
          | .ok dec =>
            let (rt', logEntry) ← commitTransition rtPre ev dec.nextConfig dec.outcome dec.lawful dec.valid
            return (rt', envelopeOk rt' op [
              ("sagaStatus", Json.str recResolved.status.asString),
              ("logEntryHash", Json.str logEntry.entryHash)
            ])
        else
          return (rtPre, envelopeOk rtPre op [("sagaStatus", Json.str recResolved.status.asString)])
    | "ExercisePower" =>
      match (do
        let act ← req.getObjValAs? String "action"
        let args ← parseElemArgs req
        let intentId := (req.getObjValAs? String "intentId").toOption.getD ""
        let ev := ServerEvent.triggerAct act args intentId
        let dec ← evaluateServerEvent rt.config ev true
        .ok (ev, dec)) with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok (ev, dec) =>
        let (rt', logEntry) ← commitTransition rt ev dec.nextConfig dec.outcome dec.lawful dec.valid
        return (rt', envelopeOk rt' op [
          ("outcome", Json.str dec.outcome),
          ("lawful", Json.str dec.lawful.asString),
          ("valid", Json.str dec.valid.asString),
          ("logEntryHash", Json.str logEntry.entryHash)
        ])
    | "ObserveExternal" =>
      match (do
        let act ← req.getObjValAs? String "action"
        let args ← parseElemArgs req
        let evTime := (req.getObjValAs? Int "eventTime").toOption.getD rt.config.state.time
        let obsTime := (req.getObjValAs? Int "observedTime").toOption.getD rt.config.state.time
        let ev := ServerEvent.observeExternal act args evTime obsTime
        let dec ← evaluateServerEvent rt.config ev true
        .ok (ev, dec)) with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok (ev, dec) =>
        let (rt', logEntry) ← commitTransition rt ev dec.nextConfig dec.outcome dec.lawful dec.valid
        return (rt', envelopeOk rt' op [
          ("outcome", Json.str dec.outcome),
          ("lawful", Json.str dec.lawful.asString),
          ("valid", Json.str dec.valid.asString),
          ("logEntryHash", Json.str logEntry.entryHash)
        ])
    | "SubmitEvidence" =>
      match (do
        let fact ← req.getObjValAs? String "fact"
        let args ← parseElemArgs req
        let pol := (req.getObjValAs? Bool "polarity").toOption.getD true
        let issuer := (req.getObjValAs? String "issuer").toOption.getD "external"
        let acl := (req.getObjValAs? (List String) "aclAudiences").toOption.getD []
        let sup? := (req.getObjValAs? String "supersedes").toOption
        let ev := ServerEvent.submitEvidence fact args pol issuer acl sup?
        let dec ← evaluateServerEvent rt.config ev true
        .ok (fact, args, pol, issuer, acl, sup?, ev, dec)) with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok (fact, args, pol, issuer, acl, sup?, ev, dec) =>
        let vrec := mkVaultRecord fact args pol issuer rt.config.state.time acl sup?
        let rtVault := { rt with vault := rt.vault ++ [vrec] }
        let (rt', logEntry) ← commitTransition rtVault ev dec.nextConfig dec.outcome dec.lawful dec.valid
        return (rt', envelopeOk rt' op [
          ("evidenceId", Json.str vrec.evidenceId),
          ("logEntryHash", Json.str logEntry.entryHash)
        ])
    | "AdvanceClock" =>
      match req.getObjValAs? Int "newTime" with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok newTime =>
        match validateClockAdvance rt.clockPolicy rt.config.state.time newTime with
        | .error e => return (rt, envelopeErr rt op e)
        | .ok () =>
          let ev := ServerEvent.advanceClock newTime
          match evaluateServerEvent rt.config ev true with
          | .error e => return (rt, envelopeErr rt op e)
          | .ok dec =>
            let rtExp := { rt with reservations := expireStaleReservations newTime rt.reservations }
            let (rt', logEntry) ← commitTransition rtExp ev dec.nextConfig dec.outcome dec.lawful dec.valid
            return (rt', envelopeOk rt' op [("logEntryHash", Json.str logEntry.entryHash)])
    | "Explain" =>
      let target := (req.getObjValAs? String "target").toOption.getD ""
      let aud? := (req.getObjValAs? String "audience").toOption
      match parseElemArgs req with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok args =>
        match explainInstance rt.config target args aud? with
        | .error e => return (rt, envelopeErr rt op e)
        | .ok rg =>
          return (rt, envelopeOk rt op [("reasonGraph", reasonGraphJson rg)])
    | "AmendLaw" =>
      let amendAct := (req.getObjValAs? String "amendAct").toOption.getD ""
      let artifactPath := (req.getObjValAs? String "successorArtifact").toOption.getD ""
      match parseElemArgs req with
      | .error e => return (rt, envelopeErr rt op e)
      | .ok args =>
        let rawNew : Except String String ← try
          let txt ← IO.FS.readFile artifactPath
          pure (Except.ok txt)
        catch e => pure (Except.error (toString e))
        match rawNew with
        | .error e => return (rt, envelopeErr rt op s!"could not read successor artifact `{artifactPath}`: {e}")
        | .ok rawTxt =>
          match installCertifiedAmendment rt.secretKey rt.config amendAct args rawTxt with
          | .error e => return (rt, envelopeErr rt op e)
          | .ok (verNew, nextCfg) =>
            let rtLaw := { rt with lawHash := verNew.artifactSha256, certificate := verNew.certificate }
            let ev := ServerEvent.amendLaw amendAct args verNew.artifactSha256
            let (rt', logEntry) ← commitTransition rtLaw ev nextCfg "Allow" .yes .yes
            return (rt', envelopeOk rt' op [
              ("outcome", Json.str "Allow"),
              ("newLawHash", Json.str verNew.artifactSha256),
              ("logEntryHash", Json.str logEntry.entryHash)
            ])
    | other =>
      return (rt, envelopeErr rt other s!"unknown operation `{other}`")

end Charter.Server
