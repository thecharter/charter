import Charter.Artifact.Runtime

/-!
# Charter.Server.StateStore — Durable Hash-Chained Event Log, State Roots, & Offline `Replay` (`G4.2`, `T36`)

Implements Charter's operator-blind durable storage contract (`docs/rfc.md` §8.6, `D27`):
1. Canonical SHA-256 `computeStateRoot` over sorted `(Tagged, Info)` entries, `time`, `step`,
   `lawVersion`, and `lawHash` (independent of internal bucket or insertion order).
2. Content-addressed `EvidenceVault` with audience ACLs and supersession links.
3. Typed `ServerEvent` compilation directly into `CPhrase` against `Spec` (zero source parser!).
4. Strictly monotonic `(institutionId, seqNo)` hash-chained JSONL `LogEntry` records +
   periodic `Snapshot` checkpoints, verified end-to-end by offline `replayLog` (`T36`).
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Canonical SHA-256 Merkle/state root over `cfg`, independent of list order in `state.contents`. -/
def computeStateRoot (lawHash : String) (cfg : Config) : String :=
  let entries := cfg.state.contents.map fun (te, i) =>
    let expStr := match i.expiry with | some u => toString u | none => "none"
    s!"{te.pp}={i.value}:{i.fromSat}:{i.since}:{expStr}:{reprStr i.origin}"
  let sorted := (entries.toArray.qsort (· < ·)).toList
  let canonical := s!"v1|law:{lawHash}|ver:{cfg.lawVersion}|time:{cfg.state.time}|step:{cfg.state.step}|" ++
    ";".intercalate sorted
  Artifact.sha256String canonical

theorem computeStateRoot_congr (lawHash : String) (c₁ c₂ : Config) (h : c₁ = c₂) :
    computeStateRoot lawHash c₁ = computeStateRoot lawHash c₂ := by
  rw [h]

/-- Content-addressed evidence vault record (`docs/rfc.md` §8.6). -/
structure VaultRecord where
  evidenceId   : String
  factName     : DomId
  args         : List Elem
  polarity     : Bool
  issuer       : String
  acquiredAt   : Int
  aclAudiences : List String := []
  supersedes   : Option String := none
  deriving Repr, ToJson, FromJson

def mkVaultRecord (factName : DomId) (args : List Elem) (polarity : Bool)
    (issuer : String) (acquiredAt : Int)
    (aclAudiences : List String := []) (supersedes : Option String := none) : VaultRecord :=
  let body := s!"{factName}|{reprStr args}|{polarity}|{issuer}|{acquiredAt}|{",".intercalate aclAudiences}|{supersedes.getD ""}"
  { evidenceId := "ev:" ++ (Artifact.sha256String body).take 32
    factName, args, polarity, issuer, acquiredAt, aclAudiences, supersedes }

/-- Typed runtime event executed by `charter-server` (`docs/rfc.md` §8.2, zero source text). -/
inductive ServerEvent where
  | triggerAct (actName : DomId) (args : List Elem) (intentId : String := "")
  | observeExternal (actName : DomId) (args : List Elem) (eventTime : Int) (observedTime : Int)
  | submitEvidence (factName : DomId) (args : List Elem) (polarity : Bool) (issuer : String)
      (aclAudiences : List String := []) (supersedes : Option String := none)
  | retractEvidence (factName : DomId) (args : List Elem) (issuer : String)
  | advanceClock (newTime : Int)
  | amendLaw (amendActName : DomId) (amendArgs : List Elem) (newArtifactSha256 : String)
  deriving Repr, ToJson, FromJson

/-- Convert a primitive `Elem` into a checked `Term` tagged with component domain `compDom`. -/
def elemToTaggedTerm (spec : Spec) (compDom : DomId) (e : Elem) : Except String Term :=
  let target := spec.chaseAlias compDom
  match e with
  | .str s => .ok (.tag (.stringLit s) target)
  | .int n => .ok (.tag (.intLit n) target)
  | .prod _ => .error s!"nested product element not supported as flat scalar argument for `{compDom}`"

/-- Build a checked instance `Term` `d(args...)` directly from `spec` without invoking `Surface` or `Resolve`. -/
def buildInstanceTerm (spec : Spec) (d : DomId) (args : List Elem) : Except String Term := do
  let realDom := spec.chaseAlias d
  match spec.findDecl realDom with
  | none => .error s!"undeclared rule or fact `{d}` in compiled artifact"
  | some tspec =>
    match tspec.domain with
    | .products xs =>
      if xs.length != args.length then
        .error s!"`{d}` expects {xs.length} argument(s), got {args.length}"
      let mods ← (xs.zip args).mapM fun (v, e) => do
        let tm ← elemToTaggedTerm spec (spec.removeDecoration v) e
        return (v, tm)
      .ok (.app realDom (.named mods))
    | _ =>
      match args with
      | [e] => elemToTaggedTerm spec realDom e
      | _ => .error s!"primitive type `{d}` expects 1 argument, got {args.length}"

/-- Result of executing or hypothetically evaluating one `ServerEvent`. -/
structure StepDecision where
  nextConfig    : Config
  outcome       : String -- "Allow" | "Deny" | "NeedEvidence" | "ReferForFinding" | "Conflict" | "Observed"
  occurred      : String -- "observed" | "hypothetical"
  lawful        : TriBool
  valid         : TriBool
  unmetEvidence : List (String × EvidenceStatus) := []
  reasonSummary : String := ""
  deriving Repr

/-- Deterministic service outcome mapping (`docs/rfc.md` §8.4 — lawful-action entitlement). -/
def classifyActOutcome (_spec : Spec) (state : State) (lTri vTri : TriBool)
    (unmet : List (Tagged × EvidenceStatus)) : String :=
  -- Check whether any active normative conflict exists in `State`
  let hasNormConflict := state.contents.any fun (te, i) => te.2 == defConflictDom && i.live state.time
  if hasNormConflict && (lTri == .undetermined || vTri == .undetermined) then "Conflict"
  else if lTri == .yes && vTri == .yes then "Allow"
  else if lTri == .undetermined || vTri == .undetermined then
    if unmet.any (fun (_, st) => st == .conflicted) then "ReferForFinding"
    else "NeedEvidence"
  else "Deny"

/-- Evaluate a `ServerEvent` against `cfg` (`commit := false` for pure hypothetical `Evaluate`). -/
def evaluateServerEvent (cfg : Config) (ev : ServerEvent) (commit : Bool := true) : Except String StepDecision := do
  match ev with
  | .advanceClock newTime =>
    if newTime < cfg.state.time then
      .error s!"CHR106: AdvanceClock {newTime} precedes current server clock {cfg.state.time}"
    let (cfg', outs) := evalCompiledStep cfg (.setTime (.intLit newTime)) true
    for o in outs do
      match o with
      | .diag d => if d.isError then .error s!"{d.code}: {d.message}"
      | _ => pure ()
    .ok {
      nextConfig := if commit then cfg' else cfg
      outcome := "Allow"
      occurred := if commit then "observed" else "hypothetical"
      lawful := .yes
      valid := .yes
      reasonSummary := s!"clock advanced to {newTime}"
    }
  | .submitEvidence factName args pol issuer _ _ =>
    let tm ← buildInstanceTerm cfg.spec factName args
    let (cfg', outs) := evalCompiledStep cfg (.submitEvidence pol [] tm issuer) true
    for o in outs do
      match o with
      | .diag d => if d.isError then .error s!"{d.code}: {d.message}"
      | _ => pure ()
    .ok {
      nextConfig := if commit then cfg' else cfg
      outcome := "Allow"
      occurred := if commit then "observed" else "hypothetical"
      lawful := .yes
      valid := .yes
      reasonSummary := s!"evidence ({if pol then "support" else "rebut"}) tendered by `{issuer}` on `{factName}`"
    }
  | .retractEvidence factName args issuer =>
    let tm ← buildInstanceTerm cfg.spec factName args
    let (cfg', outs) := evalCompiledStep cfg (.retractEvidence [] tm issuer) true
    for o in outs do
      match o with
      | .diag d => if d.isError then .error s!"{d.code}: {d.message}"
      | _ => pure ()
    .ok {
      nextConfig := if commit then cfg' else cfg
      outcome := "Allow"
      occurred := if commit then "observed" else "hypothetical"
      lawful := .yes
      valid := .yes
      reasonSummary := s!"evidence retracted by `{issuer}` on `{factName}`"
    }
  | .triggerAct actName args _ | .amendLaw actName args _ =>
    let tm ← buildInstanceTerm cfg.spec actName args
    let (cfg', outs) := evalCompiledStep cfg (.trigger [] tm) false
    for o in outs do
      match o with
      | .diag d => if d.isError then .error s!"{d.code}: {d.message}"
      | _ => pure ()
    let info? := outs.findSome? fun | .executed i => some i | _ => none
    match info? with
    | none => .error s!"`{actName}` produced no transition instance"
    | some info =>
      let outcome := classifyActOutcome cfg.spec cfg.state info.lawfulTri info.validTri info.unmetEvidence
      let unmetStrs := info.unmetEvidence.map fun (uTe, st) => (uTe.pp, st)
      let nextCfg := if commit && outcome == "Allow" then cfg' else cfg
      .ok {
        nextConfig := nextCfg
        outcome
        occurred := if commit && outcome == "Allow" then "observed" else "hypothetical"
        lawful := info.lawfulTri
        valid := info.validTri
        unmetEvidence := unmetStrs
        reasonSummary := s!"rule `{actName}` judged lawful={info.lawfulTri.asString}, valid={info.validTri.asString}"
      }
  | .observeExternal actName args evTime obsTime =>
    -- External physical/contractor observation (`Law 1`, `Law 2`, `docs/rfc.md` §8.5):
    -- always recorded in state even when unlawful or void!
    let tm ← buildInstanceTerm cfg.spec actName args
    let (cfg', outs) := evalCompiledStep cfg (.trigger [] tm) true
    for o in outs do
      match o with
      | .diag d => if d.isError then .error s!"{d.code}: {d.message}"
      | _ => pure ()
    let info? := outs.findSome? fun | .executed i => some i | _ => none
    let (lTri, vTri, unmet) := match info? with
      | some i => (i.lawfulTri, i.validTri, i.unmetEvidence.map fun (u, st) => (u.pp, st))
      | none   => (.no, .no, [])
    .ok {
      nextConfig := if commit then cfg' else cfg
      outcome := "Observed"
      occurred := "observed"
      lawful := lTri
      valid := vTri
      unmetEvidence := unmet
      reasonSummary := s!"external event `{actName}` observed (eventTime={evTime}, observedTime={obsTime}, adjudicationTime={cfg.state.time})"
    }

/-! ## Hash-Chained Append-Only Log & Snapshot Records (`G4.2`, `T36`) -/

structure LogEntry where
  institutionId  : String
  seqNo          : Nat
  prevEntryHash  : String
  lawHash        : String
  lawVersion     : Nat
  event          : ServerEvent
  outcome        : String
  lawful         : String
  valid          : String
  stateRootAfter : String
  entryHash      : String
  signatureHex   : String
  deriving Repr, ToJson, FromJson

def computeLogEntryHash (institutionId : String) (seqNo : Nat) (prevEntryHash lawHash : String)
    (lawVersion : Nat) (ev : ServerEvent) (outcome lawful valid stateRootAfter : String) : String :=
  let payload := s!"{institutionId}|{seqNo}|{prevEntryHash}|{lawHash}|{lawVersion}|{(toJson ev).compress}|{outcome}|{lawful}|{valid}|{stateRootAfter}"
  Artifact.sha256String payload

def mkSignedLogEntry (secretKey : String) (institutionId : String) (seqNo : Nat)
    (prevEntryHash lawHash : String) (lawVersion : Nat) (ev : ServerEvent)
    (outcome lawful valid stateRootAfter : String) : LogEntry :=
  let eh := computeLogEntryHash institutionId seqNo prevEntryHash lawHash lawVersion ev outcome lawful valid stateRootAfter
  let sig := Artifact.hmacSha256 secretKey s!"charter-log-v1:{eh}"
  { institutionId, seqNo, prevEntryHash, lawHash, lawVersion, event := ev,
    outcome, lawful, valid, stateRootAfter, entryHash := eh, signatureHex := sig }

def verifyLogEntryIntegrity (secretKey : String) (expectedPrevHash : String) (expectedSeq : Nat) (e : LogEntry) : Except String Unit := do
  if e.seqNo != expectedSeq then
    .error s!"log sequence gap/out-of-order: expected seqNo={expectedSeq}, found seqNo={e.seqNo}"
  if e.prevEntryHash != expectedPrevHash then
    .error s!"log hash-chain broken at seqNo={e.seqNo}: expected prev={expectedPrevHash}, found prev={e.prevEntryHash}"
  let wantHash := computeLogEntryHash e.institutionId e.seqNo e.prevEntryHash e.lawHash e.lawVersion e.event e.outcome e.lawful e.valid e.stateRootAfter
  if e.entryHash != wantHash then
    .error s!"log entry payload tampered at seqNo={e.seqNo}: expected entryHash={wantHash}, found={e.entryHash}"
  let wantSig := Artifact.hmacSha256 secretKey s!"charter-log-v1:{wantHash}"
  if e.signatureHex != wantSig then
    .error s!"log entry signature invalid at seqNo={e.seqNo}"
  .ok ()

/-- Materialized checkpoint snapshot (`T36`). -/
structure Snapshot where
  institutionId : String
  nextSeqNo     : Nat
  lastEntryHash : String
  lawHash       : String
  config        : Config
  stateRoot     : String
  signatureHex  : String
  deriving Repr, ToJson, FromJson

def mkSignedSnapshot (secretKey institutionId : String) (nextSeqNo : Nat)
    (lastEntryHash lawHash : String) (cfg : Config) : Snapshot :=
  let root := computeStateRoot lawHash cfg
  let sig := Artifact.hmacSha256 secretKey s!"charter-snap-v1:{institutionId}:{nextSeqNo}:{lastEntryHash}:{lawHash}:{root}"
  { institutionId, nextSeqNo, lastEntryHash, lawHash, config := cfg, stateRoot := root, signatureHex := sig }

def verifySnapshot (secretKey : String) (snap : Snapshot) : Except String Unit := do
  let actualRoot := computeStateRoot snap.lawHash snap.config
  if actualRoot != snap.stateRoot then
    .error s!"snapshot stateRoot mismatch: claimed={snap.stateRoot}, actual={actualRoot}"
  let wantSig := Artifact.hmacSha256 secretKey s!"charter-snap-v1:{snap.institutionId}:{snap.nextSeqNo}:{snap.lastEntryHash}:{snap.lawHash}:{actualRoot}"
  if snap.signatureHex != wantSig then
    .error "snapshot signature verification failed"
  .ok ()

/-- Parse newline-delimited JSONL `LogEntry` records. -/
def parseLogLines (txt : String) : Except String (List LogEntry) := do
  let lines := txt.splitOn "\n" |>.map String.trim |>.filter (!·.isEmpty)
  lines.mapM fun line => do
    let j ← Json.parse line
    fromJson? (α := LogEntry) j

/-- Offline deterministic replay (`charter-server replay`, `T36`, `test/gates/replay.sh`):
recomputes every transition from `startCfg` (genesis or verified snapshot) and verifies
every hash-chain link, HMAC signature, verdict, and `stateRootAfter` byte-for-byte. -/
def replayEntries (secretKey : String) (lawHash : String) (startCfg : Config)
    (startSeq : Nat := 0) (startPrevHash : String := "GENESIS")
    (entries : List LogEntry) : Except String (Config × String × String) := do
  let mut cfg := startCfg
  let mut expectedSeq := startSeq
  let mut prevHash := startPrevHash
  for e in entries do
    if e.seqNo < startSeq then
      pure () -- already covered by verified snapshot prefix
    else
      verifyLogEntryIntegrity secretKey prevHash expectedSeq e
      let commitEvent := e.outcome == "Allow" || e.outcome == "Observed"
      let dec ← evaluateServerEvent cfg e.event commitEvent
      if dec.outcome != e.outcome || dec.lawful.asString != e.lawful || dec.valid.asString != e.valid then
        .error s!"replay verdict divergence at seqNo={e.seqNo}: log=({e.outcome},{e.lawful},{e.valid}) vs eval=({dec.outcome},{dec.lawful.asString},{dec.valid.asString})"
      cfg := dec.nextConfig
      let rootAfter := computeStateRoot e.lawHash cfg
      if rootAfter != e.stateRootAfter then
        .error s!"replay stateRoot divergence at seqNo={e.seqNo}: log={e.stateRootAfter} vs eval={rootAfter}"
      prevHash := e.entryHash
      expectedSeq := expectedSeq + 1
  let finalRoot := computeStateRoot lawHash cfg
  return (cfg, finalRoot, prevHash)

end Charter.Server
