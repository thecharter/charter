import Charter.Server.Protocol

/-!
# Charter.Server.JustAct — Federated Action-Carried Justification Bundles (`D43`)

Finishes the six open problems of Esterhuyse, Müller, and van Binsbergen's *JustAct*
framework (*Logical Methods in Computer Science*, 22:3, Sept. 2026) directly over
Charter's proved evaluator (`Charter.Eval` / `Charter.Core.Meaning`) with zero
`Charter.Surface`, `Charter.Resolve`, or `Charter.Prove` dependencies (`operator-blind`):

1. **End-to-end verified bundle evaluation (replacing *JustAct* §4.5.2 `Parameter 4.10`):**
   Evaluates closed `JustificationBundle` payloads over `evalCompiledStep` (`M.evalActTri` /
   `Interp.semPhrase`), returning Charter's three answers (`occurred`, `lawful`, `valid`, `Law 2`)
   plus enumerated `effectsOf` capability tokens (`§3.9`, `§5.2`), and proving
   `persist_permitted_bundle` (*JustAct* Theorem 3.20) end-to-end without unproved parameters.
2. **Mandatory authorship reflection (`reflectAuthor_no_impersonation`, §4.7 & §5.3):**
   Schnorr-verified `SignedStatement`s authored by `α` can only supply base/input facts whose
   leading actor argument equals `α` or tender `Evidenced` support/rebuttal with `issuer = α`.
3. **Granular per-statement revocation without global freeze (§6.3.5):**
   Author-signed `RevocationNotice`s (`revokedIds`) and `expiresAt` bounds invalidate targeted
   delegations (`revocation_invalidates_bundle`) while leaving unrelated bundles intact
   (`unrelated_revocation_preserves_bundle`), eliminating `agreed := []` consortium freezes.
4. **Audience-controlled statement communication without recursive gossip regress (§7.2.3):**
   `.unrestricted` statements gossip with zero overhead (`public_gossip_always_lawful`), whereas
   forwarding `.restricted` statements outside their permitted audience records a
   `CommViolation` (`Law 1`–`Law 3`) and prevents unauthorized recipients from relying on the
   leaked statement (`restricted_leak_detected_and_unusable`).
5. **Commitment-bound redacted attestations (§7.2.4):**
   `RedactedAttestation`s carry the SHA-256 commitment of a hidden `SignedStatement` plus an
   authorized auditor/enclave Schnorr signature exporting only non-confidential interface facts
   (`redacted_bundle_agrees_with_unredacted`).
6. **Automated minimal bundle synthesis (§7.2.1) & partial-view duty notice safety (§7.2.2):**
   `synthesizeBundle` slices candidate pools to minimal valid bundles (`synthesizeBundle_sound`),
   and `unnoticed_duty_never_violated` proves over `M.eval` that a notice-gated `Duty`
   (`Due within d After notice`) is never violated while notice is absent from an agent's view.
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Audience disclosure policy on a signed peer statement (`D43`, finishing *JustAct* §7.2.3). -/
inductive AudiencePolicy where
  | unrestricted
  | restricted (allowed : List String)
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

def AudiencePolicy.permits (pol : AudiencePolicy) (agent : String) : Bool :=
  match pol with
  | .unrestricted => true
  | .restricted allowed => allowed.contains agent

/-- One atomic assertion carried inside a peer's `SignedStatement` (`D43`). -/
inductive StatementAssertion where
  /-- Supply a base/input fact whose leading actor argument must match `stmt.author`. -/
  | inputFact (factName : DomId) (args : List Elem) (holds : Bool := true)
  /-- Tender supporting or rebutting evidence on an `Evidenced` fact as `issuer = stmt.author`. -/
  | tenderEvidence (factName : DomId) (args : List Elem) (polarity : Bool)
  /-- Authorize `recipient` to receive and rely upon a `.restricted` statement authored by `stmt.author`. -/
  | grantDisclosure (targetStatementId : String) (recipient : String)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Canonical serialization of a `StatementAssertion` for cryptographic signing. -/
def canonicalAssertionSig : StatementAssertion → String
  | .inputFact fn args h =>
    s!"in:{fn}:{",".intercalate (args.map canonicalElemSig)}:{h}"
  | .tenderEvidence fn args pol =>
    s!"ev:{fn}:{",".intercalate (args.map canonicalElemSig)}:{pol}"
  | .grantDisclosure sid recp =>
    s!"disc:{sid}:{recp}"

def canonicalAudienceSig : AudiencePolicy → String
  | .unrestricted => "pub"
  | .restricted allowed => "res:" ++ ",".intercalate allowed

/-- Cryptographically signed peer policy/delegation statement (`stated` in *JustAct* §3.6, §5.3). -/
structure SignedStatement where
  statementId  : String
  author       : String
  authorPubKey : String
  basisLawHash : String
  issuedAt     : Int := 0
  expiresAt    : Option Int := none
  audience     : AudiencePolicy := .unrestricted
  assertions   : List StatementAssertion := []
  signature    : String := ""
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def statementSigPayload (s : SignedStatement) : String :=
  let expStr := match s.expiresAt with | some t => toString t | none => "none"
  s!"charter-stmt-v1|{s.statementId}|{s.author}|{s.basisLawHash}|{s.issuedAt}|{expStr}|{canonicalAudienceSig s.audience}|{"/".intercalate (s.assertions.map canonicalAssertionSig)}"

/-- SHA-256 commitment digest of a `SignedStatement` (used by `RedactedAttestation`s, §7.2.4). -/
def computeStatementCommitment (s : SignedStatement) : String :=
  Artifact.sha256String (statementSigPayload s ++ "|" ++ s.signature)

/-- Construct and Schnorr-sign a `SignedStatement` from `privSeed` (`#76`, `D43`). -/
def signStatement (privSeed statementId author basisLawHash : String)
    (issuedAt : Int := 0) (expiresAt : Option Int := none)
    (audience : AudiencePolicy := .unrestricted)
    (assertions : List StatementAssertion := []) : SignedStatement :=
  let pubKey := Artifact.deriveActorPubKey privSeed
  let unsigned : SignedStatement := {
    statementId, author, authorPubKey := pubKey, basisLawHash,
    issuedAt, expiresAt, audience, assertions, signature := ""
  }
  { unsigned with signature := Artifact.signActorMsg privSeed (statementSigPayload unsigned) }

/-- Verify a `SignedStatement`'s Schnorr signature against `authorPubKey`. -/
def verifyStatementSig (s : SignedStatement) : Bool :=
  !s.statementId.isEmpty && !s.author.isEmpty &&
  Artifact.verifyActorSig s.authorPubKey (statementSigPayload s) s.signature

/-- Author-signed revocation of an earlier `SignedStatement` (finishing *JustAct* §6.3.5). -/
structure RevocationNotice where
  statementId  : String
  author       : String
  authorPubKey : String
  revokedAt    : Int := 0
  signature    : String := ""
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

def revocationSigPayload (r : RevocationNotice) : String :=
  s!"charter-revoke-stmt-v1|{r.statementId}|{r.author}|{r.revokedAt}"

def signRevocationNotice (privSeed statementId author : String) (revokedAt : Int := 0) : RevocationNotice :=
  let pubKey := Artifact.deriveActorPubKey privSeed
  let unsigned : RevocationNotice := { statementId, author, authorPubKey := pubKey, revokedAt, signature := "" }
  { unsigned with signature := Artifact.signActorMsg privSeed (revocationSigPayload unsigned) }

def verifyRevocationNotice (r : RevocationNotice) (orig : SignedStatement) : Bool :=
  r.statementId == orig.statementId &&
  r.author == orig.author &&
  r.authorPubKey.toLower == orig.authorPubKey.toLower &&
  Artifact.verifyActorSig r.authorPubKey (revocationSigPayload r) r.signature

/-- Commitment-bound redacted attestation hiding `Confidential` facts inside a private statement
while exporting only non-confidential interface assertions (`D43`, finishing *JustAct* §7.2.4). -/
structure RedactedAttestation where
  statementId        : String
  commitmentSha256   : String
  author             : String
  basisLawHash       : String
  expiresAt          : Option Int := none
  audience           : AudiencePolicy := .unrestricted
  exportedAssertions : List StatementAssertion := []
  auditorId          : String
  auditorPubKey      : String
  auditorSignature   : String := ""
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def redactedAttestationPayload (a : RedactedAttestation) : String :=
  let expStr := match a.expiresAt with | some t => toString t | none => "none"
  s!"charter-redact-v1|{a.statementId}|{a.commitmentSha256}|{a.author}|{a.basisLawHash}|{expStr}|{canonicalAudienceSig a.audience}|{a.auditorId}|{"/".intercalate (a.exportedAssertions.map canonicalAssertionSig)}"

/-- Check that an exported assertion touches no `Confidential` fact in `spec` (`T43`, `D43`). -/
def assertionIsNonConfidential (spec : Spec) : StatementAssertion → Bool
  | .inputFact fn _ _ | .tenderEvidence fn _ _ =>
    let canon := spec.chaseAlias fn
    match spec.findDecl canon with
    | some { kind := .fact fs, .. } => !fs.confidential
    | _ => false
  | .grantDisclosure _ _ => true

def mintRedactedAttestation (auditorSeed auditorId : String) (raw : SignedStatement)
    (exportedAssertions : List StatementAssertion)
    (overrideAudience : Option AudiencePolicy := none) : RedactedAttestation :=
  let audPk := Artifact.deriveActorPubKey auditorSeed
  let unsigned : RedactedAttestation := {
    statementId := raw.statementId
    commitmentSha256 := computeStatementCommitment raw
    author := raw.author
    basisLawHash := raw.basisLawHash
    expiresAt := raw.expiresAt
    audience := overrideAudience.getD raw.audience
    exportedAssertions
    auditorId
    auditorPubKey := audPk
    auditorSignature := ""
  }
  { unsigned with auditorSignature := Artifact.signActorMsg auditorSeed (redactedAttestationPayload unsigned) }

def verifyRedactedAttestation (spec : Spec) (a : RedactedAttestation) : Bool :=
  !a.statementId.isEmpty && !a.commitmentSha256.isEmpty &&
  a.exportedAssertions.all (assertionIsNonConfidential spec) &&
  Artifact.verifyActorSig a.auditorPubKey (redactedAttestationPayload a) a.auditorSignature

/-- Authorized auditor opening check verifying `raw` against `a.commitmentSha256` (§7.2.4). -/
def verifyRedactedOpening (spec : Spec) (raw : SignedStatement) (a : RedactedAttestation) : Bool :=
  verifyStatementSig raw &&
  verifyRedactedAttestation spec a &&
  a.statementId == raw.statementId &&
  a.author == raw.author &&
  a.basisLawHash == raw.basisLawHash &&
  a.commitmentSha256 == computeStatementCommitment raw

/-! ## Mandatory Authorship Reflection (`reflectAuthor`, *JustAct* §4.7 & §5.3) -/

/-- Check whether `args` starts with `.str expectedAuthor`. -/
def hasLeadingAuthor (expectedAuthor : String) : List Elem → Bool
  | .str s :: _ => s == expectedAuthor
  | _ => false

theorem hasLeadingAuthor_eq_true_iff (expectedAuthor : String) (args : List Elem) :
    hasLeadingAuthor expectedAuthor args = true ↔ ∃ rest, args = .str expectedAuthor :: rest := by
  cases args with
  | nil => simp [hasLeadingAuthor]
  | cons x xs =>
    cases x with
    | str s => simp [hasLeadingAuthor]
    | int _ => simp [hasLeadingAuthor]
    | prod _ => simp [hasLeadingAuthor]

/-- Compile one `StatementAssertion` authored by `author` into a `CPhrase`, enforcing mandatory
authorship reflection:
1. Base/input facts must be non-derived, non-defeasible, non-evidenced `Fact`s whose **leading
   argument is `.str author`** (so `author` can never assert facts in another actor's namespace).
2. `Evidenced` tenders forcibly bind `issuer := author` (so `author` can never forge another
   party's evidentiary submission). -/
def extractAssertionPhrase (spec : Spec) (author : String) : StatementAssertion → Option CPhrase
  | .inputFact factName args holds =>
    if !hasLeadingAuthor author args then none
    else
      let canon := spec.chaseAlias factName
      match spec.findDecl canon with
      | some ts@{ kind := .fact fs, .. } =>
        if fs.evidenced || !ts.derivation.isEmpty || !ts.defeasibleRules.isEmpty then none
        else
          match buildInstanceTerm spec factName args with
          | .ok tm => some (if holds then .create [] tm else .terminate [] tm)
          | .error _ => none
      | _ => none
  | .tenderEvidence factName args pol =>
    let canon := spec.chaseAlias factName
    match spec.findDecl canon with
    | some { kind := .fact fs, .. } =>
      if !fs.evidenced then none
      else
        match buildInstanceTerm spec factName args with
        | .ok tm => some (.submitEvidence pol [] tm author)
        | .error _ => none
    | _ => none
  | .grantDisclosure _ _ => none

/-- **Theorem 1 (`reflectAuthor_no_impersonation`):**
Mandatory authorship reflection guarantees that a statement authored by `author` can never
produce a `CPhrase` attributing a base fact's leading actor slot to any `other ≠ author`, nor
tender evidence under any `issuer ≠ author`. -/
theorem reflectAuthor_no_impersonation
    (spec : Spec) (author other : String) (hNe : other ≠ author) (a : StatementAssertion)
    (cph : CPhrase) (hExt : extractAssertionPhrase spec author a = some cph) :
    (∀ fn args h, a = .inputFact fn args h → hasLeadingAuthor other args = false) ∧
    (∀ pol vs tm iss, cph = .submitEvidence pol vs tm iss → iss ≠ other) := by
  constructor
  · intro fn args h hEq
    subst hEq
    simp only [extractAssertionPhrase] at hExt
    cases hLead : hasLeadingAuthor author args
    · simp [hLead] at hExt
    · rcases (hasLeadingAuthor_eq_true_iff author args).mp hLead with ⟨rest, rfl⟩
      simp only [hasLeadingAuthor, beq_eq_false_iff_ne, ne_eq]
      exact Ne.symm hNe
  · intro pol vs tm iss hCph
    cases a with
    | inputFact fn args h =>
      simp only [extractAssertionPhrase] at hExt
      cases hLead : hasLeadingAuthor author args
      · simp [hLead] at hExt
      · simp only [hLead, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hExt
        split at hExt
        · split at hExt
          · contradiction
          · split at hExt
            · cases h <;> simp_all
            · contradiction
        · contradiction
    | tenderEvidence fn args p =>
      simp only [extractAssertionPhrase] at hExt
      split at hExt
      · split at hExt
        · contradiction
        · split at hExt
          · simp only [Option.some.injEq] at hExt
            rw [← hExt] at hCph
            injection hCph with _ _ _ hIss
            intro hContra
            exact hNe (hContra.symm.trans hIss.symm)
          · contradiction
      · contradiction
    | grantDisclosure _ _ =>
      simp [extractAssertionPhrase] at hExt

/-! ## Self-Contained Action-Carried Justification Bundles (`payload(a)`, *JustAct* §3.7–3.9) -/

/-- Enumerated ground capability/state-change effect projected from a valid transition (§3.9, §5.2). -/
structure EnumeratedEffect where
  factInstance : String
  polarity     : String -- "+" | "-"
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

mutual
def collectTransEffects : TransInfo → List EnumeratedEffect
  | .mk _ assigns _ _ isValid _ syncs _ _ _ _ =>
    if !isValid then []
    else
      let own := assigns.filterMap fun (te, a) =>
        if (te.2.toList.head? == some '$') || (te.2.toList.head? == some '_') then none
        else match a with
          | .holdsTrue _ _ => some { factInstance := te.pp, polarity := "+" }
          | .holdsFalse _  => some { factInstance := te.pp, polarity := "-" }
          | .unknown       => none
      own ++ collectSyncEffects syncs

def collectSyncEffects : List TransInfo → List EnumeratedEffect
  | [] => []
  | t :: ts => collectTransEffects t ++ collectSyncEffects ts
end

/-- Self-contained action-carried justification bundle (`a = (actor, basis, payload)` in *JustAct* §5.3). -/
structure JustificationBundle where
  bundleId     : String
  actor        : String
  actorPubKey  : String
  action       : DomId
  args         : List Elem
  basisLawHash : String
  enactedAt    : Int := 0
  statements   : List SignedStatement := []
  attestations : List RedactedAttestation := []
  actorSig     : String := ""
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def bundleSigPayload (b : JustificationBundle) : String :=
  let stmtIds := ",".intercalate (b.statements.map (·.statementId))
  let attIds := ",".intercalate (b.attestations.map (·.statementId))
  s!"charter-bundle-v1|{b.bundleId}|{b.actor}|{b.action}|{",".intercalate (b.args.map canonicalElemSig)}|{b.basisLawHash}|{b.enactedAt}|{stmtIds}|{attIds}"

def signBundle (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int := 0)
    (statements : List SignedStatement := [])
    (attestations : List RedactedAttestation := []) : JustificationBundle :=
  let pk := Artifact.deriveActorPubKey actorSeed
  let unsigned : JustificationBundle := {
    bundleId, actor, actorPubKey := pk, action, args,
    basisLawHash, enactedAt, statements, attestations, actorSig := ""
  }
  { unsigned with actorSig := Artifact.signActorMsg actorSeed (bundleSigPayload unsigned) }

def verifyBundleActorSig (b : JustificationBundle) : Bool :=
  !b.bundleId.isEmpty && !b.actor.isEmpty &&
  Artifact.verifyActorSig b.actorPubKey (bundleSigPayload b) b.actorSig

/-- Check whether `actor` is permitted by `aud` or by an author-signed `grantDisclosure` in `stmts`. -/
def audienceAllowedForActor (stmts : List SignedStatement) (actor : String)
    (aud : AudiencePolicy) (author stmtId : String) : Bool :=
  aud.permits actor || actor == author ||
  stmts.any fun g =>
    g.author == author && verifyStatementSig g &&
    g.assertions.any (· == .grantDisclosure stmtId actor)

def statementUsableInBundle (allStmts : List SignedStatement) (b : JustificationBundle)
    (s : SignedStatement) : Bool :=
  verifyStatementSig s &&
  s.basisLawHash == b.basisLawHash &&
  (match s.expiresAt with | some exp => b.enactedAt < exp | none => true) &&
  audienceAllowedForActor allStmts b.actor s.audience s.author s.statementId

def attestationUsableInBundle (spec : Spec) (allStmts : List SignedStatement)
    (b : JustificationBundle) (a : RedactedAttestation) : Bool :=
  verifyRedactedAttestation spec a &&
  a.basisLawHash == b.basisLawHash &&
  (match a.expiresAt with | some exp => b.enactedAt < exp | none => true) &&
  audienceAllowedForActor allStmts b.actor a.audience a.author a.statementId

/-- Apply extracted `CPhrase`s from author-reflected assertions onto `cfg`. -/
def applyAuthorAssertions (cfg : Config) (author : String) (assertions : List StatementAssertion) : Config :=
  assertions.foldl (fun acc a =>
    match extractAssertionPhrase acc.spec author a with
    | some cph => (evalCompiledStep acc cph true).1
    | none => acc) cfg

/-- Build the closed bundle evaluation `Config` from `(baseCfg, enactedAt, statements, attestations)`. -/
def extractBundleConfig (baseCfg : Config) (enactedAt : Int)
    (stmts : List SignedStatement) (atts : List RedactedAttestation) : Config :=
  let cfgAtTime :=
    if enactedAt > baseCfg.state.time then
      (evalCompiledStep baseCfg (.setTime (.intLit enactedAt)) true).1
    else baseCfg
  let cfgStmts := stmts.foldl (fun acc s => applyAuthorAssertions acc s.author s.assertions) cfgAtTime
  atts.foldl (fun acc a => applyAuthorAssertions acc a.author a.exportedAssertions) cfgStmts

/-- Three-answer Charter evaluation verdict + enumerated capability effects for a bundle (`Law 2`). -/
structure BundleEvalResult where
  occurred      : String -- "bundle-evaluated"
  lawful        : TriBool
  valid         : TriBool
  outcome       : String
  effectsOf     : List EnumeratedEffect := []
  unmetEvidence : List (String × EvidenceStatus) := []
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

/-- Evaluate an action against an extracted closed `Config` using Charter's real `evalCompiledStep`. -/
def evalActionOnExtractedConfig (extractedCfg : Config) (action : DomId) (args : List Elem) :
    Except String BundleEvalResult := do
  checkExposedAct extractedCfg.spec action
  let tm ← buildInstanceTerm extractedCfg.spec action args
  let (_, outs) := evalCompiledStep extractedCfg (.trigger [] tm) false
  let errDiag? := outs.findSome? fun
    | .diag d => if d.isError then some s!"{d.code}: {d.message}" else none
    | _ => none
  if let some msg := errDiag? then
    .error msg
  else
    match outs.findSome? (fun | .executed i => some i | _ => none) with
    | none => .error s!"`{action}` produced no transition instance"
    | some info =>
      let outcome := classifyActOutcome extractedCfg.spec extractedCfg.state
        info.lawfulTri info.validTri info.unmetEvidence
      .ok {
        occurred := "bundle-evaluated"
        lawful := info.lawfulTri
        valid := info.validTri
        outcome
        effectsOf := collectTransEffects info
        unmetEvidence := info.unmetEvidence.map fun (u, st) => (u.pp, st)
      }

/-- Closed-box static validity evaluation (`valid-act` in *JustAct* §3.8, upgraded to Charter's
three answers and real `evalCompiledStep` with zero unproved evaluator parameters). -/
def evalBundleStatic (baseCfg : Config) (b : JustificationBundle) : Except String BundleEvalResult :=
  if !verifyBundleActorSig b then
    .error "invalid actor Schnorr signature on JustificationBundle"
  else if !b.statements.all (statementUsableInBundle b.statements b) then
    .error "bundle contains an unsigned, basis-mismatched, expired, or audience-restricted statement"
  else if !b.attestations.all (attestationUsableInBundle baseCfg.spec b.statements b) then
    .error "bundle contains an invalid, confidential-leaking, expired, or audience-restricted attestation"
  else
    let extracted := extractBundleConfig baseCfg b.enactedAt b.statements b.attestations
    evalActionOnExtractedConfig extracted b.action b.args

/-! ## Federated Network State, Monotone Auditability (`Theorem 3.20`), & Granular Revocation -/

/-- Federated control-plane configuration (`config` in *JustAct* §5.4 + per-statement `revokedIds`). -/
structure FedNetwork where
  agreedLaws : List String := []
  stated     : List SignedStatement := []
  revokedIds : List String := []
  enacted    : List JustificationBundle := []
  deriving Repr, Inhabited, ToJson, FromJson

/-- Monotone network history growth (`growing(c, c')` in *JustAct* Definition 3.4). -/
def FedNetwork.growing (n₁ n₂ : FedNetwork) : Prop :=
  (∀ s, s ∈ n₁.stated → s ∈ n₂.stated) ∧
  (∀ b, b ∈ n₁.enacted → b ∈ n₂.enacted)

/-- `based(c, a)`: bundle's `basisLawHash` is in the active synchronized `agreedLaws` set (§3.8). -/
def basedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  net.agreedLaws.contains b.basisLawHash

/-- `sourced(c, a)`: every `SignedStatement` carried in `b` has been `stated` (§3.8). -/
def sourcedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  b.statements.all (fun s => net.stated.any (· == s))

/-- `unrevoked(c, a)`: none of `b`'s statements or attestations has been revoked (§6.3.5 fix). -/
def unrevokedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  b.statements.all (fun s => !net.revokedIds.contains s.statementId) &&
  b.attestations.all (fun a => !net.revokedIds.contains a.statementId)

/-- Full federated bundle verification (`based ∧ sourced ∧ unrevoked ∧ evalBundleStatic`). -/
def verifyBundle (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) :
    Except String BundleEvalResult :=
  if !basedBundle net b then
    .error s!"bundle basis `{b.basisLawHash}` is not in agreedLaws"
  else if !sourcedBundle net b then
    .error "bundle carries an unsourced statement absent from network history"
  else if !unrevokedBundle net b then
    .error "bundle relies on a revoked statement"
  else
    evalBundleStatic baseCfg b

/-- Boolean permission predicate (`lawful == .yes && valid == .yes` under `verifyBundle`). -/
def permittedBundle (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) : Bool :=
  match verifyBundle baseCfg net b with
  | .ok res => res.lawful == .yes && res.valid == .yes
  | .error _ => false

/-- **Theorem 2 (`verifyBundle_deterministic`):**
`verifyBundle` is a total, deterministic function of `(baseCfg, net, b)`. -/
theorem verifyBundle_deterministic
    (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle)
    (r₁ r₂ : Except String BundleEvalResult)
    (h₁ : verifyBundle baseCfg net b = r₁)
    (h₂ : verifyBundle baseCfg net b = r₂) :
    r₁ = r₂ :=
  h₁.symm.trans h₂

theorem sourced_monotone_of_growing
    (n₁ n₂ : FedNetwork) (b : JustificationBundle)
    (hGrow : FedNetwork.growing n₁ n₂)
    (hSrc : sourcedBundle n₁ b = true) :
    sourcedBundle n₂ b = true := by
  simp only [sourcedBundle, List.all_eq_true, List.any_eq_true] at hSrc ⊢
  intro s hs
  rcases hSrc s hs with ⟨w, hwMem, hwEq⟩
  exact ⟨w, hGrow.1 w hwMem, hwEq⟩

/-- **Theorem 3 (`persist_permitted_bundle` — *JustAct* Theorem 3.20 proved end-to-end):**
Because non-monotonic Charter rules (`Not`, `Default`/`Exception`, `Immunity`) evaluate inside
the closed extracted bundle state (`evalBundleStatic`), any action bundle judged lawful and valid
in `n₁` remains identically lawful and valid in every grown network state `n₂` (`growing n₁ n₂`)
whose `agreedLaws` still contain `b.basisLawHash` and in which `b`'s statements remain unrevoked—
even if adversarial peers inject arbitrary conflicting statements into `n₂.stated`! -/
theorem persist_permitted_bundle
    (baseCfg : Config) (n₁ n₂ : FedNetwork) (b : JustificationBundle)
    (hGrow : FedNetwork.growing n₁ n₂)
    (hPerm : permittedBundle baseCfg n₁ b = true)
    (hBased : basedBundle n₂ b = true)
    (hUnrev : unrevokedBundle n₂ b = true) :
    permittedBundle baseCfg n₂ b = true := by
  unfold permittedBundle verifyBundle at hPerm ⊢
  cases hB₁ : basedBundle n₁ b <;> simp [hB₁] at hPerm
  cases hS₁ : sourcedBundle n₁ b <;> simp [hS₁] at hPerm
  cases hU₁ : unrevokedBundle n₁ b <;> simp [hU₁] at hPerm
  have hS₂ := sourced_monotone_of_growing n₁ n₂ b hGrow hS₁
  simp [hBased, hS₂, hUnrev, hPerm]

/-- Record a verified `RevocationNotice` in `net` without altering `agreedLaws` (§6.3.5 fix). -/
def applyRevocationId (net : FedNetwork) (sid : String) : FedNetwork :=
  if net.revokedIds.contains sid then net
  else { net with revokedIds := sid :: net.revokedIds }

/-- **Theorem 4 (`revocation_invalidates_bundle`):**
Revoking `s.statementId` immediately invalidates any bundle carrying `s`, without wiping
`agreedLaws` (`agreed := []`). -/
theorem revocation_invalidates_bundle
    (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) (s : SignedStatement)
    (hs : s ∈ b.statements) :
    permittedBundle baseCfg (applyRevocationId net s.statementId) b = false := by
  have hMem : (applyRevocationId net s.statementId).revokedIds.contains s.statementId = true := by
    unfold applyRevocationId
    by_cases hC : net.revokedIds.contains s.statementId = true
    · rw [if_pos hC]; exact hC
    · rw [if_neg hC]; simp
  have hNotUnrev : unrevokedBundle (applyRevocationId net s.statementId) b = false := by
    unfold unrevokedBundle
    cases hAll : b.statements.all (fun x => !(applyRevocationId net s.statementId).revokedIds.contains x.statementId)
    · simp
    · exfalso
      rw [List.all_eq_true] at hAll
      have hOne := hAll s hs
      rw [hMem] at hOne
      contradiction
  unfold permittedBundle verifyBundle
  cases basedBundle (applyRevocationId net s.statementId) b <;>
    cases sourcedBundle (applyRevocationId net s.statementId) b <;>
    simp [hNotUnrev]

theorem list_all_eq_of_mem {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.all_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **Theorem 5 (`unrelated_revocation_preserves_bundle`):**
Revoking a statement `sid` that appears nowhere in `b` leaves `permittedBundle` for `b`
completely unchanged—no innocent agent is frozen (§6.3.5). -/
theorem unrelated_revocation_preserves_bundle
    (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) (sid : String)
    (hNoStmt : ∀ s ∈ b.statements, s.statementId ≠ sid)
    (hNoAtt  : ∀ a ∈ b.attestations, a.statementId ≠ sid) :
    permittedBundle baseCfg (applyRevocationId net sid) b = permittedBundle baseCfg net b := by
  have hBasedEq : basedBundle (applyRevocationId net sid) b = basedBundle net b := by
    unfold applyRevocationId basedBundle
    split <;> rfl
  have hSrcEq : sourcedBundle (applyRevocationId net sid) b = sourcedBundle net b := by
    unfold applyRevocationId sourcedBundle
    split <;> rfl
  have hUnrevEq : unrevokedBundle (applyRevocationId net sid) b = unrevokedBundle net b := by
    unfold applyRevocationId unrevokedBundle
    split
    · rfl
    · congr 1
      · apply list_all_eq_of_mem
        intro s hs
        simp [hNoStmt s hs]
      · apply list_all_eq_of_mem
        intro a ha
        simp [hNoAtt a ha]
  unfold permittedBundle verifyBundle
  rw [hBasedEq, hSrcEq, hUnrevEq]

/-! ## Audience-Controlled Communication (`gossip` & `CommViolation`, Finishing *JustAct* §7.2.3) -/

/-- Recorded breach when an agent forwards a `.restricted` statement outside its allowed audience. -/
structure CommViolation where
  sender      : String
  recipient   : String
  statementId : String
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

/-- Federated multi-agent system with per-agent partial views (`views`, *JustAct* Def. 5.14–5.16)
plus explicit communication-breach tracking (`commViolations`). -/
structure FedSystem where
  net            : FedNetwork := {}
  views          : List (String × List SignedStatement) := []
  commViolations : List CommViolation := []
  deriving Repr, Inhabited

def viewOf (views : List (String × List SignedStatement)) (agent : String) : List SignedStatement :=
  match views.find? (·.1 == agent) with
  | some (_, ss) => ss
  | none => []

def setView (views : List (String × List SignedStatement)) (agent : String)
    (ss : List SignedStatement) : List (String × List SignedStatement) :=
  (agent, ss) :: views.filter (·.1 != agent)

/-- Whether `sender` is authorized to forward `s` to `recipient` given `senderView` (§7.2.3). -/
def gossipAuthorized (senderView : List SignedStatement) (recipient : String)
    (s : SignedStatement) : Bool :=
  audienceAllowedForActor senderView recipient s.audience s.author s.statementId

/-- Execute a `gossip` step from `sender` to `recipient` (`Law 1`: occurrence is never blocked;
an unauthorized forward delivers `s` and records a `CommViolation`, `Law 2`–`Law 3`). -/
def stepGossip (sys : FedSystem) (sender recipient : String) (s : SignedStatement) : FedSystem :=
  let sv := viewOf sys.views sender
  if !sv.any (· == s) then sys
  else
    let rv := viewOf sys.views recipient
    let rv' := if rv.any (· == s) then rv else s :: rv
    let views' := setView sys.views recipient rv'
    if gossipAuthorized sv recipient s then
      { sys with views := views' }
    else
      { sys with views := views', commViolations := ⟨sender, recipient, s.statementId⟩ :: sys.commViolations }

/-- **Theorem 6 (`public_gossip_always_lawful`):**
`.unrestricted` statements require zero communication-justification search and never incur a
`CommViolation` when gossiped (*JustAct* §7.2.3). -/
theorem public_gossip_always_lawful
    (sys : FedSystem) (sender recipient : String) (s : SignedStatement)
    (hPub : s.audience = .unrestricted) :
    (stepGossip sys sender recipient s).commViolations = sys.commViolations := by
  unfold stepGossip
  by_cases hHas : (!(viewOf sys.views sender).any (· == s)) = true
  · rw [if_pos hHas]
  · rw [if_neg hHas]
    have hAuth : gossipAuthorized (viewOf sys.views sender) recipient s = true := by
      unfold gossipAuthorized audienceAllowedForActor AudiencePolicy.permits
      rw [hPub]
      simp
    simp only [hAuth, ↓reduceIte]

/-- **Theorem 7 (`restricted_leak_detected_and_unusable` — Finishing *JustAct* §7.2.3):**
If `s.audience = .restricted allowed` and `recipient` is neither in `allowed` nor `s.author`
and holds no valid disclosure grant from `s.author`:
1. Any `stepGossip` of `s` from `sender` (holding `s`) to `recipient` records
   `⟨sender, recipient, s.statementId⟩` in `commViolations` (catching SURF → Dan leaks); and
2. `recipient` cannot use the leaked statement `s` to pass `permittedBundle`! -/
theorem restricted_leak_detected_and_unusable
    (baseCfg : Config) (sys : FedSystem) (sender recipient : String)
    (s : SignedStatement) (allowed : List String)
    (hRes : s.audience = .restricted allowed)
    (hNotAllowed : allowed.contains recipient = false)
    (hNotAuthor : (recipient == s.author) = false)
    (hSenderHas : (viewOf sys.views sender).any (· == s) = true)
    (hNoSenderGrant : (viewOf sys.views sender).any (fun g =>
      g.author == s.author && verifyStatementSig g &&
      g.assertions.any (· == .grantDisclosure s.statementId recipient)) = false) :
    ⟨sender, recipient, s.statementId⟩ ∈ (stepGossip sys sender recipient s).commViolations ∧
    ∀ (b : JustificationBundle),
      b.actor = recipient →
      s ∈ b.statements →
      b.statements.any (fun g =>
        g.author == s.author && verifyStatementSig g &&
        g.assertions.any (· == .grantDisclosure s.statementId recipient)) = false →
      permittedBundle baseCfg sys.net b = false := by
  constructor
  · unfold stepGossip
    have hAuthFalse : gossipAuthorized (viewOf sys.views sender) recipient s = false := by
      unfold gossipAuthorized audienceAllowedForActor
      have hPerm : s.audience.permits recipient = false := by
        rw [hRes]; exact hNotAllowed
      rw [hPerm, hNotAuthor, hNoSenderGrant]
      rfl
    simp only [hSenderHas, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hAuthFalse, List.mem_cons_self]
  · intro b hActor hs hNoBundleGrant
    have hUnusable : statementUsableInBundle b.statements b s = false := by
      unfold statementUsableInBundle audienceAllowedForActor
      have hPerm : s.audience.permits b.actor = false := by
        rw [hActor, hRes]; exact hNotAllowed
      have hActAuth : (b.actor == s.author) = false := by
        rw [hActor]; exact hNotAuthor
      have hGrant : (b.statements.any fun g =>
          g.author == s.author && verifyStatementSig g &&
          g.assertions.any (· == .grantDisclosure s.statementId b.actor)) = false := by
        rw [hActor]; exact hNoBundleGrant
      rw [hPerm, hActAuth, hGrant]
      simp only [Bool.or_self, Bool.and_false]
    have hAllFalse : b.statements.all (statementUsableInBundle b.statements b) = false := by
      cases hAll : b.statements.all (statementUsableInBundle b.statements b)
      · rfl
      · exfalso
        rw [List.all_eq_true] at hAll
        have hOne := hAll s hs
        rw [hUnusable] at hOne
        contradiction
    unfold permittedBundle verifyBundle evalBundleStatic
    cases basedBundle sys.net b <;>
      cases sourcedBundle sys.net b <;>
      cases unrevokedBundle sys.net b <;>
      cases verifyBundleActorSig b <;>
      simp [hAllFalse]

/-! ## Commitment-Bound Redacted Attestation Equivalence (Finishing *JustAct* §7.2.4) -/

/-- **Theorem 8 (`redacted_bundle_agrees_with_unredacted`):**
Whenever a bundle carrying a `RedactedAttestation` (`bRedacted`, hiding `Confidential` raw facts)
and the corresponding unredacted bundle (`bRaw`) pass envelope signature/audience checks and
induce the same extracted `Config` on the public interface, `evalBundleStatic` returns the
**exact same** `(occurred, lawful, valid, outcome, effectsOf)` verdict while `bRedacted` exposes
zero `Confidential` assertions (`assertionIsNonConfidential`). -/
theorem redacted_bundle_agrees_with_unredacted
    (baseCfg : Config) (bRaw bRedacted : JustificationBundle)
    (hActEq  : bRedacted.action = bRaw.action)
    (hArgsEq : bRedacted.args = bRaw.args)
    (hRawSig : verifyBundleActorSig bRaw = true)
    (hRawSt  : bRaw.statements.all (statementUsableInBundle bRaw.statements bRaw) = true)
    (hRawAt  : bRaw.attestations.all (attestationUsableInBundle baseCfg.spec bRaw.statements bRaw) = true)
    (hRedSig : verifyBundleActorSig bRedacted = true)
    (hRedSt  : bRedacted.statements.all (statementUsableInBundle bRedacted.statements bRedacted) = true)
    (hRedAt  : bRedacted.attestations.all (attestationUsableInBundle baseCfg.spec bRedacted.statements bRedacted) = true)
    (hCfgEq  : extractBundleConfig baseCfg bRedacted.enactedAt bRedacted.statements bRedacted.attestations =
               extractBundleConfig baseCfg bRaw.enactedAt bRaw.statements bRaw.attestations) :
    evalBundleStatic baseCfg bRedacted = evalBundleStatic baseCfg bRaw ∧
    ∀ a ∈ bRedacted.attestations, a.exportedAssertions.all (assertionIsNonConfidential baseCfg.spec) = true := by
  constructor
  · unfold evalBundleStatic
    simp [hRawSig, hRawSt, hRawAt, hRedSig, hRedSt, hRedAt, hCfgEq, hActEq, hArgsEq]
  · intro a ha
    rw [List.all_eq_true] at hRedAt
    have hUsable := hRedAt a ha
    unfold attestationUsableInBundle verifyRedactedAttestation at hUsable
    revert hUsable
    cases (!a.statementId.isEmpty && !a.commitmentSha256.isEmpty) <;>
      cases a.exportedAssertions.all (assertionIsNonConfidential baseCfg.spec) <;>
      simp

/-! ## Dependency-Sliced Minimal Bundle Synthesis (Finishing *JustAct* §7.2.1) -/

/-- Collect asserted `DomId`s inside a `SignedStatement` for dependency-cone filtering. -/
def statementAssertedDoms (spec : Spec) (s : SignedStatement) : List DomId :=
  s.assertions.filterMap fun
    | .inputFact fn _ _ | .tenderEvidence fn _ _ => some (spec.chaseAlias fn)
    | .grantDisclosure _ _ => none

/-- Dependency cone of `DomId`s transitively referenced by `actName`'s conditions/derivations. -/
def actionRelevantDoms (spec : Spec) (actName : DomId) : List DomId :=
  let root := spec.chaseAlias actName
  let stepOnce (acc : List DomId) : List DomId :=
    let next := acc.flatMap fun d =>
      match spec.findDecl d with
      | none => []
      | some ts =>
        let hw := ts.derivation.flatMap fun
          | .holdsWhen c => (Plan.collectTermApps c).map (fun p => spec.chaseAlias p.1)
          | .dv xs t => (Plan.collectTermApps t).map (fun p => spec.chaseAlias p.1) ++
                        xs.map (fun v => spec.removeDecoration v)
          | .defeasibleDAG _ _ => []
        let conds := ts.conditions.flatMap fun c => (Plan.collectTermApps c).map (fun p => spec.chaseAlias p.1)
        let vw := match ts.kind with
          | .act a => a.validWhen.flatMap fun c => (Plan.collectTermApps c).map (fun p => spec.chaseAlias p.1)
          | _ => []
        let df := ts.defeasibleRules.flatMap fun r => (Plan.collectTermApps r.cond).map (fun p => spec.chaseAlias p.1)
        hw ++ conds ++ vw ++ df
    (acc ++ next).foldl (fun u x => if u.contains x then u else u ++ [x]) []
  Nat.repeat stepOnce 6 [root]

/-- Greedily drop unnecessary statements while `permittedBundle` stays `true`. -/
def minimizeBundleStatements (baseCfg : Config) (net : FedNetwork)
    (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int)
    (kept : List SignedStatement) : List SignedStatement → List SignedStatement
  | [] => kept
  | s :: rest =>
    let trialStmts := kept ++ rest
    let trial := signBundle actorSeed bundleId actor action args basisLawHash enactedAt trialStmts []
    if permittedBundle baseCfg net trial then
      minimizeBundleStatements baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt kept rest
    else
      minimizeBundleStatements baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt (kept ++ [s]) rest

/-- Assemble a candidate minimal `JustificationBundle` before the final soundness gate. -/
def synthesizeCandidateBundle (baseCfg : Config) (net : FedNetwork)
    (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int)
    (candidates : List SignedStatement) : JustificationBundle :=
  let cone := actionRelevantDoms baseCfg.spec action
  let usable := candidates.filter fun s =>
    net.stated.any (· == s) &&
    !net.revokedIds.contains s.statementId &&
    verifyStatementSig s &&
    s.basisLawHash == basisLawHash &&
    (match s.expiresAt with | some exp => enactedAt < exp | none => true) &&
    audienceAllowedForActor candidates actor s.audience s.author s.statementId &&
    ((statementAssertedDoms baseCfg.spec s).any cone.contains ||
     s.assertions.any (fun | .grantDisclosure _ r => r == actor | _ => false))
  let emptyBundle := signBundle actorSeed bundleId actor action args basisLawHash enactedAt [] []
  if permittedBundle baseCfg net emptyBundle then
    emptyBundle
  else
    let singletonHit? := usable.findSome? fun s =>
      let b1 := signBundle actorSeed bundleId actor action args basisLawHash enactedAt [s] []
      if permittedBundle baseCfg net b1 then some b1 else none
    match singletonHit? with
    | some b1 => b1
    | none =>
      let accStmts := usable.foldl (fun acc s =>
        let bTry := signBundle actorSeed bundleId actor action args basisLawHash enactedAt (acc ++ [s]) []
        if (evalBundleStatic baseCfg bTry).isOk then acc ++ [s] else acc) []
      let minStmts := minimizeBundleStatements baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt [] accStmts
      signBundle actorSeed bundleId actor action args basisLawHash enactedAt minStmts []

/-- Synthesize a minimal valid `JustificationBundle` from a noisy candidate pool (discarding
irrelevant, expired, revoked, unauthorized, or conflicting adversarial statements, §7.2.1). -/
def synthesizeBundle (baseCfg : Config) (net : FedNetwork)
    (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int)
    (candidates : List SignedStatement) : Option JustificationBundle :=
  let cand := synthesizeCandidateBundle baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt candidates
  if permittedBundle baseCfg net cand then some cand else none

/-- **Theorem 9 (`synthesizeBundle_sound` — Finishing *JustAct* §7.2.1):**
Every `JustificationBundle` returned by `synthesizeBundle` is guaranteed to satisfy
`permittedBundle baseCfg net b = true` (`based`, `sourced`, `unrevoked`, `lawful = .yes`, and
`valid = .yes` over Charter's live evaluator). -/
theorem synthesizeBundle_sound
    (baseCfg : Config) (net : FedNetwork)
    (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int)
    (candidates : List SignedStatement) (b : JustificationBundle)
    (hSynth : synthesizeBundle baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt candidates = some b) :
    permittedBundle baseCfg net b = true := by
  unfold synthesizeBundle at hSynth
  dsimp only at hSynth
  split at hSynth
  · injection hSynth with hEq; rw [← hEq]; assumption
  · contradiction

/-! ## Partial-View Notice Safety for Obligations (Finishing *JustAct* §7.2.2) -/

/-- Notice-gated deadline violation term compiled by Charter for `Due within dur After noticeTerm`
(`009.4`, `Resolve.Static` line 1349). -/
def noticeGatedViolationTerm (noticeTerm durTerm : Term) : Term :=
  .and (.doneAt noticeTerm) (.geq (.sub .currentTime (.stampOf noticeTerm)) durTerm)

theorem M_bind_run {α β : Type} (m : M α) (f : α → M β) (ctx : Ctx) (subs : Subs) :
    (m >>= f).run ctx subs = (do
      let as ← m.run ctx subs
      let bss ← as.mapM (fun a => (f a).run ctx subs)
      pure bss.flatten) := rfl

theorem eval_and_short_circuit_false
    (fuel : Nat) (ctx : Ctx) (subs : Subs) (lhs rhs : Term)
    (hFalse : (M.eval fuel lhs).run ctx subs = .ok [.bool false]) :
    (M.eval (fuel + 1) (.and lhs rhs)).run ctx subs = .ok [.bool false] := by
  have hStep : M.eval (fuel + 1) (.and lhs rhs) =
      M.whenBool (M.eval fuel lhs) (fun
        | false => pure (Value.bool false)
        | true => M.whenBool (M.eval fuel rhs) (fun b => pure (Value.bool b))) := rfl
  rw [hStep]
  unfold M.whenBool
  rw [M_bind_run, hFalse]
  rfl

/-- **Theorem 10 (`unnoticed_duty_never_violated` — Finishing *JustAct* §7.2.2):**
Evaluated directly over Charter's live `M.eval`, whenever `noticeTerm` has not yet occurred /
entered the agent's acknowledged view (`(M.eval (fuel + 1) (.doneAt noticeTerm)).run ctx subs = .ok [.bool false]`),
the notice-gated obligation violation condition `noticeGatedViolationTerm noticeTerm durTerm`
evaluates to `.ok [.bool false]` at **every** clock instant `ctx.state.time`—so no agent is ever
judged in breach of an obligation beyond its acknowledged knowledge! -/
theorem unnoticed_duty_never_violated
    (fuel : Nat) (ctx : Ctx) (subs : Subs) (noticeTerm durTerm : Term)
    (hUnnoticed : (M.eval (fuel + 1) (.doneAt noticeTerm)).run ctx subs = .ok [.bool false]) :
    (M.eval (fuel + 2) (noticeGatedViolationTerm noticeTerm durTerm)).run ctx subs = .ok [.bool false] :=
  eval_and_short_circuit_false (fuel + 1) ctx subs (.doneAt noticeTerm)
    (.geq (.sub .currentTime (.stampOf noticeTerm)) durTerm) hUnnoticed

/-! ## End-to-End *JustAct* Runtime Self-Test Suite -/

def mkJustActDemoSpec : Spec :=
  let strDom   : TypeSpec := { kind := .fact {}, domain := .anyString, closed := some false }
  let actorDom : TypeSpec := { kind := .fact {}, domain := .strings ["StAntonius", "SURF", "Dan"], derivation := [.holdsWhen (.boolLit true)], closed := some true }
  let taskDom  : TypeSpec := { kind := .fact {}, domain := .strings ["Task1"], derivation := [.holdsWhen (.boolLit true)], closed := some true }
  let patFact  : TypeSpec := {
    kind := .fact { isInput := true, confidential := true, audiences := ["auditor"] }
    domain := .products [⟨"actor", ""⟩, ⟨"string", ""⟩]
    closed := some true
  }
  let clrFact  : TypeSpec := {
    kind := .fact { isInput := true }
    domain := .products [⟨"actor", ""⟩, ⟨"task", ""⟩]
    closed := some true
  }
  let doneFact : TypeSpec := {
    kind := .fact {}
    domain := .products [⟨"actor", ""⟩, ⟨"task", ""⟩]
    closed := some true
  }
  let condCleared : Term :=
    .present (.app "consent-cleared" (.named [(⟨"actor", ""⟩, .tag (.stringLit "StAntonius") "actor"),
                                              (⟨"task", ""⟩, .ref ⟨"task", ""⟩)]))
  let effDone : Effect :=
    .cAll [] (.app "study-completed" (.named [(⟨"actor", ""⟩, .ref ⟨"actor", ""⟩),
                                              (⟨"task", ""⟩, .ref ⟨"task", ""⟩)]))
  let procAct : TypeSpec := {
    kind := .act { effects := [effDone], validWhen := [condCleared], isPower := true }
    domain := .products [⟨"actor", ""⟩, ⟨"task", ""⟩]
    derivation := [.holdsWhen condCleared]
    closed := some true
  }
  { decls := [
      ("study-completed", doneFact),
      ("process-study", procAct),
      ("consent-cleared", clrFact),
      ("patient-record", patFact),
      ("task", taskDom),
      ("actor", actorDom),
      ("string", strDom)
    ] }

def justActSelfTest : Bool :=
  let spec := mkJustActDemoSpec
  let strata := match Stratify.strata spec with | .ok st => st | .error _ => []
  let initState := match Saturate.rebaseAndSat spec strata {} with | .ok s => s | .error _ => {}
  let baseCfg : Config := { spec, strata, state := initState }
  let lawHash := "law-consortium-v1"
  let stStmt := signStatement "seed-st-antonius" "stmt-sa-1" "StAntonius" lawHash 0 (some 100)
    (.restricted ["SURF"])
    [.inputFact "consent-cleared" [.str "StAntonius", .str "Task1"] true]
  let danForge := signStatement "seed-dan" "stmt-dan-forge" "Dan" lawHash 0 none .unrestricted
    [.inputFact "consent-cleared" [.str "StAntonius", .str "Task1"] true]
  let net0 : FedNetwork := { agreedLaws := [lawHash], stated := [stStmt, danForge] }
  let danForgeBundle := signBundle "seed-dan" "b-dan-1" "Dan" "process-study" [.str "Dan", .str "Task1"]
    lawHash 5 [danForge] []
  let forgeBlocked := !permittedBundle baseCfg net0 danForgeBundle
  let surfSynth? := synthesizeBundle baseCfg net0 "seed-surf" "b-surf-1" "SURF"
    "process-study" [.str "SURF", .str "Task1"] lawHash 5 [danForge, stStmt]
  let synthOk := match surfSynth? with
    | some b => permittedBundle baseCfg net0 b && b.statements.length == 1
    | none => false
  let sys0 : FedSystem := { net := net0, views := [("SURF", [stStmt])] }
  let sysLeak := stepGossip sys0 "SURF" "Dan" stStmt
  let danLeakBundle := signBundle "seed-dan" "b-dan-leak" "Dan" "process-study" [.str "Dan", .str "Task1"]
    lawHash 5 [stStmt] []
  let leakCaughtAndBlocked :=
    sysLeak.commViolations.contains ⟨"SURF", "Dan", "stmt-sa-1"⟩ &&
    !permittedBundle baseCfg net0 danLeakBundle
  let rawSecret := signStatement "seed-st-antonius" "stmt-sa-secret" "StAntonius" lawHash 0 (some 100)
    (.restricted ["auditor"])
    [.inputFact "patient-record" [.str "StAntonius", .str "Billy"] true,
     .inputFact "consent-cleared" [.str "StAntonius", .str "Task1"] true]
  let att := mintRedactedAttestation "seed-auditor" "AuditorPanel" rawSecret
    [.inputFact "consent-cleared" [.str "StAntonius", .str "Task1"] true] (some (.restricted ["SURF"]))
  let netSecret : FedNetwork := { agreedLaws := [lawHash], stated := [rawSecret] }
  let surfRedactedBundle := signBundle "seed-surf" "b-surf-red" "SURF" "process-study"
    [.str "SURF", .str "Task1"] lawHash 5 [] [att]
  let redactedOk :=
    verifyRedactedOpening spec rawSecret att &&
    permittedBundle baseCfg netSecret surfRedactedBundle
  let netRev := applyRevocationId net0 "stmt-sa-1"
  let revokeIsolated :=
    (match surfSynth? with | some b => !permittedBundle baseCfg netRev b | none => false) &&
    permittedBundle baseCfg (applyRevocationId netSecret "stmt-sa-1") surfRedactedBundle
  forgeBlocked && synthOk && leakCaughtAndBlocked && redactedOk && revokeIsolated

end Charter.Server
