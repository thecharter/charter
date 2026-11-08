import Charter.Eval.Step
import Charter.Artifact.Hash
import Charter.Artifact.Cert
import Lean.Data.Json

/-!
# Charter.Artifact.Runtime — Operator-Blind `CIR` Serialization & Certificate Verification (`G4.1`, `D27`)

Serializes and deserializes compiled `CIR` (`Spec`, `State`, `CPhrase`, `Config`) and verifies
cryptographic `Artifact` certificates (`sha256` payload integrity + RFC 2104 HMAC-SHA256
signature + `Spec.checkWellFormed` + `Stratify.strata`) with **zero** imports from
`Charter.Surface.*`, `Charter.Resolve.*`, or `Charter.Prove.*`.
-/

namespace Charter

open Lean (Json ToJson FromJson toJson fromJson?)

deriving instance ToJson, FromJson for Var
deriving instance ToJson, FromJson for EvidenceStatus
deriving instance ToJson, FromJson for TriBool
deriving instance ToJson, FromJson for EvidenceOp
deriving instance ToJson, FromJson for RoundingMode
deriving instance ToJson, FromJson for Domain

-- Mutual/nested `Elem`, `Term`, `Args` JSON codecs
mutual
partial def elemToJson : Elem → Json
  | .str s => Json.mkObj [("s", Json.str s)]
  | .int i => Json.mkObj [("i", Json.num i)]
  | .prod xs => Json.mkObj [("p", Json.arr (xs.map elemArgToJson).toArray)]
partial def elemArgToJson : (Elem × DomId) → Json
  | (e, d) => Json.arr #[elemToJson e, Json.str d]
end

mutual
partial def elemFromJson (j : Json) : Except String Elem :=
  if let .ok s := j.getObjValAs? String "s" then .ok (.str s)
  else if let .ok i := j.getObjValAs? Int "i" then .ok (.int i)
  else do
    let arr ← j.getObjValAs? (Array Json) "p"
    let xs ← arr.toList.mapM elemArgFromJson
    .ok (.prod xs)
partial def elemArgFromJson (j : Json) : Except String (Elem × DomId) := do
  let arr ← fromJson? (α := Array Json) j
  if arr.size == 2 then
    let e ← elemFromJson arr[0]!
    let d ← fromJson? (α := String) arr[1]!
    .ok (e, d)
  else .error "expected [Elem, DomId] pair"
end

instance : ToJson Elem := ⟨elemToJson⟩
instance : FromJson Elem := ⟨elemFromJson⟩

mutual
partial def termToJson : Term → Json
  | .not t => Json.mkObj [("op", "not"), ("a", termToJson t)]
  | .and a b => Json.mkObj [("op", "and"), ("a", termToJson a), ("b", termToJson b)]
  | .or a b => Json.mkObj [("op", "or"), ("a", termToJson a), ("b", termToJson b)]
  | .boolLit b => Json.mkObj [("op", "bool"), ("v", Json.bool b)]
  | .leq a b => Json.mkObj [("op", "leq"), ("a", termToJson a), ("b", termToJson b)]
  | .geq a b => Json.mkObj [("op", "geq"), ("a", termToJson a), ("b", termToJson b)]
  | .ge a b => Json.mkObj [("op", "ge"), ("a", termToJson a), ("b", termToJson b)]
  | .le a b => Json.mkObj [("op", "le"), ("a", termToJson a), ("b", termToJson b)]
  | .sub a b => Json.mkObj [("op", "sub"), ("a", termToJson a), ("b", termToJson b)]
  | .add a b => Json.mkObj [("op", "add"), ("a", termToJson a), ("b", termToJson b)]
  | .mult a b => Json.mkObj [("op", "mult"), ("a", termToJson a), ("b", termToJson b)]
  | .mod a b => Json.mkObj [("op", "mod"), ("a", termToJson a), ("b", termToJson b)]
  | .div a b => Json.mkObj [("op", "div"), ("a", termToJson a), ("b", termToJson b)]
  | .intLit i => Json.mkObj [("op", "int"), ("v", Json.num i)]
  | .stringLit s => Json.mkObj [("op", "str"), ("v", Json.str s)]
  | .eq a b => Json.mkObj [("op", "eq"), ("a", termToJson a), ("b", termToJson b)]
  | .neq a b => Json.mkObj [("op", "neq"), ("a", termToJson a), ("b", termToJson b)]
  | .exists_ xs t => Json.mkObj [("op", "exists"), ("xs", toJson xs), ("a", termToJson t)]
  | .forall_ xs t => Json.mkObj [("op", "forall"), ("xs", toJson xs), ("a", termToJson t)]
  | .count xs t => Json.mkObj [("op", "count"), ("xs", toJson xs), ("a", termToJson t)]
  | .sum xs t => Json.mkObj [("op", "sum"), ("xs", toJson xs), ("a", termToJson t)]
  | .max xs t => Json.mkObj [("op", "max"), ("xs", toJson xs), ("a", termToJson t)]
  | .min xs t => Json.mkObj [("op", "min"), ("xs", toJson xs), ("a", termToJson t)]
  | .when t c => Json.mkObj [("op", "when"), ("a", termToJson t), ("b", termToJson c)]
  | .present t => Json.mkObj [("op", "present"), ("a", termToJson t)]
  | .violated t => Json.mkObj [("op", "violated"), ("a", termToJson t)]
  | .enabled t => Json.mkObj [("op", "enabled"), ("a", termToJson t)]
  | .project t x => Json.mkObj [("op", "project"), ("a", termToJson t), ("x", toJson x)]
  | .tag t d => Json.mkObj [("op", "tag"), ("a", termToJson t), ("d", Json.str d)]
  | .untag t => Json.mkObj [("op", "untag"), ("a", termToJson t)]
  | .ref x => Json.mkObj [("op", "ref"), ("x", toJson x)]
  | .app d args => Json.mkObj [("op", "app"), ("d", Json.str d), ("args", argsToJson args)]
  | .currentTime => Json.mkObj [("op", "now")]
  | .heldFor t d => Json.mkObj [("op", "heldFor"), ("a", termToJson t), ("b", termToJson d)]
  | .evStatus w t => Json.mkObj [("op", "evStatus"), ("w", toJson w), ("a", termToJson t)]
  | .hasConflict t => Json.mkObj [("op", "hasConflict"), ("a", termToJson t)]
  | .mulDivRound x n d m => Json.mkObj [("op", "mdr"), ("x", termToJson x), ("n", termToJson n), ("d", termToJson d), ("m", toJson m)]

partial def argsToJson : Args → Json
  | .pos ts => Json.mkObj [("pos", Json.arr (ts.map termToJson).toArray)]
  | .named ms => Json.mkObj [("named", Json.arr (ms.map fun (v, t) => Json.arr #[toJson v, termToJson t]).toArray)]
end

mutual
partial def termFromJson (j : Json) : Except String Term := do
  let op ← j.getObjValAs? String "op"
  let ga (k : String) := do let sub ← j.getObjVal? k; termFromJson sub
  match op with
  | "not" => .not <$> ga "a"
  | "and" => .and <$> ga "a" <*> ga "b"
  | "or" => .or <$> ga "a" <*> ga "b"
  | "bool" => .boolLit <$> j.getObjValAs? Bool "v"
  | "leq" => .leq <$> ga "a" <*> ga "b"
  | "geq" => .geq <$> ga "a" <*> ga "b"
  | "ge" => .ge <$> ga "a" <*> ga "b"
  | "le" => .le <$> ga "a" <*> ga "b"
  | "sub" => .sub <$> ga "a" <*> ga "b"
  | "add" => .add <$> ga "a" <*> ga "b"
  | "mult" => .mult <$> ga "a" <*> ga "b"
  | "mod" => .mod <$> ga "a" <*> ga "b"
  | "div" => .div <$> ga "a" <*> ga "b"
  | "int" => .intLit <$> j.getObjValAs? Int "v"
  | "str" => .stringLit <$> j.getObjValAs? String "v"
  | "eq" => .eq <$> ga "a" <*> ga "b"
  | "neq" => .neq <$> ga "a" <*> ga "b"
  | "exists" => .exists_ <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "forall" => .forall_ <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "count" => .count <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "sum" => .sum <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "max" => .max <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "min" => .min <$> j.getObjValAs? (List Var) "xs" <*> ga "a"
  | "when" => .when <$> ga "a" <*> ga "b"
  | "present" => .present <$> ga "a"
  | "violated" => .violated <$> ga "a"
  | "enabled" => .enabled <$> ga "a"
  | "project" => .project <$> ga "a" <*> j.getObjValAs? Var "x"
  | "tag" => .tag <$> ga "a" <*> j.getObjValAs? String "d"
  | "untag" => .untag <$> ga "a"
  | "ref" => .ref <$> j.getObjValAs? Var "x"
  | "app" => do
    let d ← j.getObjValAs? String "d"
    let sub ← j.getObjVal? "args"
    .app d <$> argsFromJson sub
  | "now" => .ok .currentTime
  | "heldFor" => .heldFor <$> ga "a" <*> ga "b"
  | "evStatus" => .evStatus <$> j.getObjValAs? EvidenceStatus "w" <*> ga "a"
  | "hasConflict" => .hasConflict <$> ga "a"
  | "mdr" => .mulDivRound <$> ga "x" <*> ga "n" <*> ga "d" <*> j.getObjValAs? RoundingMode "m"
  | other => .error s!"unknown Term op `{other}`"

partial def argsFromJson (j : Json) : Except String Args :=
  if let .ok arr := j.getObjValAs? (Array Json) "pos" then
    .pos <$> arr.toList.mapM termFromJson
  else do
    let arr ← j.getObjValAs? (Array Json) "named"
    let ms ← arr.toList.mapM fun pair => do
      let p ← fromJson? (α := Array Json) pair
      if p.size == 2 then
        let v ← fromJson? (α := Var) p[0]!
        let t ← termFromJson p[1]!
        .ok (v, t)
      else .error "expected [Var, Term]"
    .ok (.named ms)
end

instance : ToJson Term := ⟨termToJson⟩
instance : FromJson Term := ⟨termFromJson⟩
instance : ToJson Args := ⟨argsToJson⟩
instance : FromJson Args := ⟨argsFromJson⟩

deriving instance ToJson, FromJson for Register
deriving instance ToJson, FromJson for Span
deriving instance ToJson, FromJson for SourceDoc
deriving instance ToJson, FromJson for Clause
deriving instance ToJson, FromJson for Expect
deriving instance ToJson, FromJson for Restriction
deriving instance ToJson, FromJson for DefeasibleConseq
deriving instance ToJson, FromJson for DefeasibleRule
deriving instance ToJson, FromJson for CompiledRuleNode
deriving instance ToJson, FromJson for Derivation
deriving instance ToJson, FromJson for EvSource
deriving instance ToJson, FromJson for Effect
deriving instance ToJson, FromJson for Sync
deriving instance ToJson, FromJson for FactSpec
deriving instance ToJson, FromJson for FindingSpec
deriving instance ToJson, FromJson for ActSpec
deriving instance ToJson, FromJson for ImmunitySpec
deriving instance ToJson, FromJson for DutySpec
deriving instance ToJson, FromJson for EventSpec
deriving instance ToJson, FromJson for Kind
deriving instance ToJson, FromJson for TypeSpec
deriving instance ToJson, FromJson for ModClause
deriving instance ToJson, FromJson for TemporalFormula
deriving instance ToJson, FromJson for TemporalSpec
deriving instance ToJson, FromJson for RegimeSpec

partial def declToJson : Decl → Json
  | .typeDecl d t => Json.mkObj [("k", "td"), ("d", Json.str d), ("t", toJson t)]
  | .typeExt d cs ek => Json.mkObj [("k", "te"), ("d", Json.str d), ("cs", toJson cs), ("ek", Json.str ek)]
  | .placeholder f t => Json.mkObj [("k", "ph"), ("f", Json.str f), ("t", Json.str t)]
  | .clause c => Json.mkObj [("k", "cl"), ("c", toJson c)]
  | .document p id? sha? rk? => Json.mkObj [("k", "doc"), ("p", Json.str p), ("id", toJson id?), ("sha", toJson sha?), ("rk", toJson rk?)]
  | .param n dom v => Json.mkObj [("k", "pa"), ("n", Json.str n), ("dom", toJson dom), ("v", Json.num v)]
  | .module n ps body => Json.mkObj [("k", "mod"), ("n", Json.str n), ("ps", toJson ps), ("b", Json.arr (body.map declToJson).toArray)]
  | .use n args pre => Json.mkObj [("k", "use"), ("n", Json.str n), ("args", toJson args), ("pre", toJson pre)]
  | .property tp => Json.mkObj [("k", "prop"), ("tp", toJson tp)]
  | .amendInstall a body => Json.mkObj [("k", "ai"), ("a", Json.str a), ("b", Json.arr (body.map declToJson).toArray)]
  | .regime r => Json.mkObj [("k", "reg"), ("r", toJson r)]

partial def declFromJson (j : Json) : Except String Decl := do
  let k ← j.getObjValAs? String "k"
  match k with
  | "td" => .typeDecl <$> j.getObjValAs? String "d" <*> j.getObjValAs? TypeSpec "t"
  | "te" => do
    let d ← j.getObjValAs? String "d"
    let cs ← j.getObjValAs? (List ModClause) "cs"
    let ek ← j.getObjValAs? String "ek"
    .ok (.typeExt d cs ek)
  | "ph" => .placeholder <$> j.getObjValAs? String "f" <*> j.getObjValAs? String "t"
  | "cl" => .clause <$> j.getObjValAs? Clause "c"
  | "doc" => do
    let p ← j.getObjValAs? String "p"
    let id? ← j.getObjValAs? (Option String) "id"
    let sha? ← j.getObjValAs? (Option String) "sha"
    let rk? ← j.getObjValAs? (Option Int) "rk"
    .ok (.document p id? sha? rk?)
  | "pa" => .param <$> j.getObjValAs? String "n" <*> j.getObjValAs? Domain "dom" <*> j.getObjValAs? Int "v"
  | "mod" => do
    let arr ← j.getObjValAs? (Array Json) "b"
    .module <$> j.getObjValAs? String "n" <*> j.getObjValAs? (List DomId) "ps" <*> arr.toList.mapM declFromJson
  | "use" => .use <$> j.getObjValAs? String "n" <*> j.getObjValAs? (List DomId) "args" <*> j.getObjValAs? (Option String) "pre"
  | "prop" => .property <$> j.getObjValAs? TemporalSpec "tp"
  | "ai" => do
    let arr ← j.getObjValAs? (Array Json) "b"
    .amendInstall <$> j.getObjValAs? String "a" <*> arr.toList.mapM declFromJson
  | "reg" => .regime <$> j.getObjValAs? RegimeSpec "r"
  | other => .error s!"unknown Decl kind `{other}`"

instance : ToJson Decl := ⟨declToJson⟩
instance : FromJson Decl := ⟨declFromJson⟩

deriving instance ToJson, FromJson for Spec
deriving instance ToJson, FromJson for Origin
deriving instance ToJson, FromJson for Info
deriving instance ToJson, FromJson for State
deriving instance ToJson, FromJson for Assignment
deriving instance ToJson, FromJson for Config

partial def cphraseToJson : CPhrase → Json
  | .trigger xs t => Json.mkObj [("p", "trig"), ("xs", toJson xs), ("t", toJson t)]
  | .create xs t => Json.mkObj [("p", "add"), ("xs", toJson xs), ("t", toJson t)]
  | .terminate xs t => Json.mkObj [("p", "rem"), ("xs", toJson xs), ("t", toJson t)]
  | .obfuscate xs t => Json.mkObj [("p", "obf"), ("xs", toJson xs), ("t", toJson t)]
  | .query t => Json.mkObj [("p", "qry"), ("t", toJson t)]
  | .instQuery b xs t => Json.mkObj [("p", "iqry"), ("b", Json.bool b), ("xs", toJson xs), ("t", toJson t)]
  | .onlyDecls init => Json.mkObj [("p", "decls"), ("init", toJson init)]
  | .par ps => Json.mkObj [("p", "par"), ("ps", Json.arr (ps.map cphraseToJson).toArray)]
  | .scenario n sps => Json.mkObj [("p", "scen"), ("n", Json.str n), ("sps", toJson sps)]
  | .expect w neg xs t => Json.mkObj [("p", "exp"), ("w", toJson w), ("neg", Json.bool neg), ("xs", toJson xs), ("t", toJson t)]
  | .setTime t => Json.mkObj [("p", "time"), ("t", toJson t)]
  | .tick => Json.mkObj [("p", "tick")]
  | .why xs t => Json.mkObj [("p", "why"), ("xs", toJson xs), ("t", toJson t)]
  | .submitEvidence pol xs t src => Json.mkObj [("p", "subEv"), ("pol", Json.bool pol), ("xs", toJson xs), ("t", toJson t), ("src", Json.str src)]
  | .retractEvidence xs t src => Json.mkObj [("p", "retEv"), ("xs", toJson xs), ("t", toJson t), ("src", Json.str src)]

partial def cphraseFromJson (j : Json) : Except String CPhrase := do
  let p ← j.getObjValAs? String "p"
  match p with
  | "trig" => .trigger <$> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "add" => .create <$> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "rem" => .terminate <$> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "obf" => .obfuscate <$> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "qry" => .query <$> j.getObjValAs? Term "t"
  | "iqry" => .instQuery <$> j.getObjValAs? Bool "b" <*> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "decls" => do
    let init ← j.getObjValAs? Store "init"
    .ok (.onlyDecls init)
  | "par" => do
    let arr ← j.getObjValAs? (Array Json) "ps"
    .par <$> arr.toList.mapM cphraseFromJson
  | "scen" => do
    let n ← j.getObjValAs? String "n"
    let sps ← j.getObjValAs? (List (ClauseId × String)) "sps"
    .ok (.scenario n sps)
  | "exp" => .expect <$> j.getObjValAs? Expect "w" <*> j.getObjValAs? Bool "neg" <*> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "time" => .setTime <$> j.getObjValAs? Term "t"
  | "tick" => .ok .tick
  | "why" => .why <$> j.getObjValAs? (List Var) "xs" <*> j.getObjValAs? Term "t"
  | "subEv" => do
    let pol ← j.getObjValAs? Bool "pol"
    let xs ← j.getObjValAs? (List Var) "xs"
    let t ← j.getObjValAs? Term "t"
    let src ← j.getObjValAs? String "src"
    .ok (.submitEvidence pol xs t src)
  | "retEv" => do
    let xs ← j.getObjValAs? (List Var) "xs"
    let t ← j.getObjValAs? Term "t"
    let src ← j.getObjValAs? String "src"
    .ok (.retractEvidence xs t src)
  | other => .error s!"unknown CPhrase `{other}`"

instance : ToJson CPhrase := ⟨cphraseToJson⟩
instance : FromJson CPhrase := ⟨cphraseFromJson⟩

namespace Artifact

/-- Default development/local signing key used when `--sign-key` / `--key` is omitted in local runs. -/
def defaultDevSigningKey : String := "charter-local-artifact-key-v1"

/-- Cryptographic certificate attached to an `Artifact` (`B10`, `D27`, `certificate-at-office`). -/
structure ArtifactCertificate where
  keyId        : String := "local-dev"
  scheme       : String := "hmac-sha256"
  signatureHex : String
  wellFormed   : Bool := true
  coverage     : String := "illustrative"
  deriving Repr, DecidableEq, ToJson, FromJson

/-- Loaded, verified runtime artifact ready for `charter-server`. -/
structure VerifiedArtifact where
  artifactSha256 : String
  certificate    : ArtifactCertificate
  genesisConfig  : Config
  deriving Repr

/-- Sign `artifactSha256` with `(keyId, secretKey)` using pure-Lean RFC 2104 HMAC-SHA256. -/
def signArtifactDigest (artifactSha256 : String) (secretKey : String)
    (keyId : String := "local-dev") (coverage : String := "illustrative") : ArtifactCertificate :=
  let msg := s!"charter-artifact-v1:{keyId}:{coverage}:{artifactSha256}"
  { keyId, scheme := "hmac-sha256", signatureHex := hmacSha256 secretKey msg, wellFormed := true, coverage }

/-- Verify an `Artifact` JSON file (`certificate-at-office`, `B10`, `D27`):
1. Recomputes `sha256String payload.compress` and rejects any mismatch, naming both hashes;
2. Verifies the `ArtifactCertificate` HMAC-SHA256 signature under `secretKey`;
3. Deserializes `genesisConfig : Config` and verifies `Spec.checkWellFormed` + `Stratify.strata`. -/
def verifyArtifactJson (rawText : String) (secretKey : String := defaultDevSigningKey) : Except String VerifiedArtifact := do
  let top ← Json.parse rawText
  let claimedSha ← top.getObjValAs? String "artifactSha256"
  let payload ← top.getObjVal? "payload"
  let actualSha := sha256String payload.compress
  if actualSha != claimedSha then
    .error s!"artifact hash mismatch (tampered payload): claimed sha256:{claimedSha}, actual sha256:{actualSha}"
  let cert ← match top.getObjValAs? ArtifactCertificate "certificate" with
    | .ok c => .ok c
    | .error _ => .error s!"artifact sha256:{claimedSha} has no valid `certificate` (`certificate-at-office` refused)"
  if cert.scheme != "hmac-sha256" then
    .error s!"unsupported certificate signature scheme `{cert.scheme}`"
  let expectedSig := hmacSha256 secretKey s!"charter-artifact-v1:{cert.keyId}:{cert.coverage}:{claimedSha}"
  if cert.signatureHex != expectedSig then
    .error s!"certificate signature verification failed for artifact sha256:{claimedSha} (keyId={cert.keyId})"
  let runtimeObj ← payload.getObjVal? "runtimeCIR"
  let cfg ← fromJson? (α := Config) runtimeObj
  if !cfg.spec.checkWellFormed then
    .error s!"artifact sha256:{claimedSha} failed runtime CIR well-formedness check"
  match Stratify.strata cfg.spec with
  | .error cyc => .error s!"artifact sha256:{claimedSha} failed stratification: {", ".intercalate cyc}"
  | .ok strata =>
    .ok { artifactSha256 := claimedSha, certificate := cert, genesisConfig := { cfg with strata } }

end Artifact

end Charter
