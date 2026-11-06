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

structure ClauseManifest where
  id           : ClauseId
  textSha256   : String
  approvedFnv  : UInt64
  stale        : Bool
  deriving Repr

structure SourceManifest where
  documentPath   : Option String
  documentSha256 : Option String
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

def buildSourceManifest (spec : Spec) (docContent? : Option String) : SourceManifest :=
  { documentPath := spec.document
    documentSha256 := docContent?.map sha256String
    clauses := spec.clauses.map fun c =>
      { id := c.id
        textSha256 := sha256String c.source
        approvedFnv := c.approvedHash
        stale := c.stale } }

def ClauseManifest.toJson (cm : ClauseManifest) : Json :=
  Json.mkObj [
    ("id", Json.str cm.id),
    ("textSha256", Json.str cm.textSha256),
    ("approvedFnv", Json.num cm.approvedFnv.toNat),
    ("stale", Json.bool cm.stale)
  ]

def SourceManifest.toJson (sm : SourceManifest) : Json :=
  Json.mkObj [
    ("documentPath", match sm.documentPath with | some p => Json.str p | none => Json.null),
    ("documentSha256", match sm.documentSha256 with | some h => Json.str h | none => Json.null),
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
