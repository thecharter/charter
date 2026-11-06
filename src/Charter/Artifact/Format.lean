import Charter.Resolve.ElaborateCIR
import Lean.Data.Json

/-!
# Charter.Artifact.Format — Content-Addressed Canonical `Artifact` Bundle (`D18`)

Packages an elaborated `CIR.Program` together with its authoritative `SourceManifest`
(including SHA-256 content digests of the governing `Document` and every `Clause`) into a
canonical, deterministically serialized JSON bundle committed under one SHA-256 `artifactHash`
(`docs/plans/2026-10-22-redesign.md` §3a; `docs/rfc.md` §3.2).
-/

namespace Charter.Artifact

open Lean (Json)

structure DocManifest where
  id             : Option String
  path           : String
  contentSha256  : Option String
  expectedSha256 : Option String
  rank           : Option Int
  deriving Repr

structure ClauseManifest where
  id             : ClauseId
  docId          : Option String
  textSha256     : String
  approvedSha256 : Option String
  approvedFnv    : UInt64
  stale          : Bool
  anchor         : Option ClauseAnchor
  deriving Repr

structure SourceManifest where
  coverage       : String
  documentPath   : Option String
  documentSha256 : Option String
  documents      : List DocManifest
  clauses        : List ClauseManifest
  deriving Repr

structure Bundle where
  formatVersion  : Nat := 1
  languageVersion : String := "0.4.0"
  sourceManifest : SourceManifest
  epochHashes    : List (Nat × String)
  cirDigest      : String
  artifactSha256 : String
  deriving Repr

def buildSourceManifestDocs (spec : Spec) (docs : List (SourceDoc × Option String)) (coverage : String := "illustrative") : SourceManifest :=
  let primaryContent? := docs.head?.bind (·.2)
  let docManifests : List DocManifest := docs.map fun (sd, txt?) =>
    { id := sd.id
      path := sd.path
      contentSha256 := txt?.map sha256String
      expectedSha256 := sd.expectedSha256
      rank := sd.rank }
  let findDocText (c : Clause) : Option String :=
    match c.docId with
    | some wantId => (docs.find? (fun (sd, _) => sd.id == some wantId)).bind (·.2)
    | none => primaryContent?
  { coverage
    documentPath := spec.document
    documentSha256 := primaryContent?.map sha256String
    documents := docManifests
    clauses := spec.clauses.map fun c =>
      { id := c.id
        docId := c.docId
        textSha256 := sha256String c.source
        approvedSha256 := c.approvedSha256
        approvedFnv := c.approvedHash
        stale := c.stale
        anchor := (findDocText c).bind (fun docTxt => locateClauseAnchor docTxt c.source) } }

def buildSourceManifest (spec : Spec) (docContent? : Option String) : SourceManifest :=
  let docs := match spec.document with
    | some p => [({ path := p : SourceDoc }, docContent?)]
    | none => []
  let cov := if spec.clauses.isEmpty && spec.document.isNone then
      (if spec.ruleIds.isEmpty then "complete" else "illustrative")
    else if docContent?.isSome && spec.clauses.all (fun c => !c.stale && c.covered && c.normsInterpreted) then "complete"
    else "partial"
  buildSourceManifestDocs spec docs cov

def DocManifest.toJson (dm : DocManifest) : Json :=
  Json.mkObj [
    ("id", match dm.id with | some i => Json.str i | none => Json.null),
    ("path", Json.str dm.path),
    ("contentSha256", match dm.contentSha256 with | some h => Json.str h | none => Json.null),
    ("expectedSha256", match dm.expectedSha256 with | some h => Json.str h | none => Json.null),
    ("rank", match dm.rank with | some r => Json.num r | none => Json.null)
  ]

def ClauseAnchor.toJson (ca : ClauseAnchor) : Json :=
  Json.mkObj [
    ("heading", match ca.heading with | some h => Json.str h | none => Json.null),
    ("line", Json.num ca.line),
    ("contextSha256", Json.str ca.contextSha256)
  ]

def ClauseManifest.toJson (cm : ClauseManifest) : Json :=
  Json.mkObj [
    ("id", Json.str cm.id),
    ("docId", match cm.docId with | some d => Json.str d | none => Json.null),
    ("textSha256", Json.str cm.textSha256),
    ("approvedSha256", match cm.approvedSha256 with | some h => Json.str h | none => Json.null),
    ("approvedFnv", Json.num cm.approvedFnv.toNat),
    ("stale", Json.bool cm.stale),
    ("anchor", match cm.anchor with | some a => ClauseAnchor.toJson a | none => Json.null)
  ]

def SourceManifest.toJson (sm : SourceManifest) : Json :=
  Json.mkObj [
    ("coverage", Json.str sm.coverage),
    ("documentPath", match sm.documentPath with | some p => Json.str p | none => Json.null),
    ("documentSha256", match sm.documentSha256 with | some h => Json.str h | none => Json.null),
    ("documents", Json.arr (sm.documents.map DocManifest.toJson).toArray),
    ("clauses", Json.arr (sm.clauses.map ClauseManifest.toJson).toArray)
  ]

def Bundle.payloadJson (sm : SourceManifest) (epochHashes : List (Nat × String)) (cirDigest : String) : Json :=
  Json.mkObj [
    ("formatVersion", Json.num 1),
    ("languageVersion", Json.str "0.4.0"),
    ("sourceManifest", sm.toJson),
    ("epochs", Json.arr (epochHashes.map fun (v, h) =>
      Json.mkObj [("version", Json.num v), ("specSha256", Json.str h)]).toArray),
    ("cirDigest", Json.str cirDigest)
  ]

/-- Assemble a content-addressed `Artifact.Bundle` from an elaborated `CIR.Program` and multi-document manifest. -/
def buildBundleDocs (prog : CIR.Program) (docs : List (SourceDoc × Option String)) (coverage : String := "illustrative") : Bundle :=
  let finalSpec := (prog.epochs.getLast?.map (·.spec)).getD emptySpec
  let sm := buildSourceManifestDocs finalSpec docs coverage
  let epochHashes := prog.epochs.map fun ep => (ep.version, ep.specSha256)
  let cirDigest := sha256String (reprStr prog.epochs)
  let payload := (Bundle.payloadJson sm epochHashes cirDigest).compress
  let artifactSha256 := sha256String payload
  { sourceManifest := sm, epochHashes, cirDigest, artifactSha256 }

/-- Assemble a content-addressed `Artifact.Bundle` from an elaborated `CIR.Program`. -/
def buildBundle (prog : CIR.Program) (docContent? : Option String) : Bundle :=
  let finalSpec := (prog.epochs.getLast?.map (·.spec)).getD emptySpec
  let sm := buildSourceManifest finalSpec docContent?
  let epochHashes := prog.epochs.map fun ep => (ep.version, ep.specSha256)
  let cirDigest := sha256String (reprStr prog.epochs)
  let payload := (Bundle.payloadJson sm epochHashes cirDigest).compress
  let artifactSha256 := sha256String payload
  { sourceManifest := sm, epochHashes, cirDigest, artifactSha256 }

def Bundle.toJson (b : Bundle) : Json :=
  Json.mkObj [
    ("artifactSha256", Json.str b.artifactSha256),
    ("payload", Bundle.payloadJson b.sourceManifest b.epochHashes b.cirDigest)
  ]

end Charter.Artifact
