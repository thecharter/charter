import Charter.Server.Protocol

/-!
# Charter.Server.Bundles — Federated Action-Carried Justification Bundles (`D43`)

Extends Charter's operator-blind runtime (`Charter.Eval` / `Charter.Core.Meaning`) to
inter-organizational settings where participants hold partial views of peer state and carry
self-contained cryptographic proof bundles alongside actions, with zero `Charter.Surface`,
`Charter.Resolve`, or `Charter.Prove` dependencies (`operator-blind`).

Inspired by the action-carried justification model of Esterhuyse, Müller, and van Binsbergen
(*Logical Methods in Computer Science*, 22:3, 2026), integrated with Charter's verified
evaluator, stateful duties, audience-scoped confidentiality, and per-statement revocation:

1. **Verified closed-bundle evaluation (`persist_permitted_bundle`):**
   Evaluates closed `JustificationBundle` payloads directly over `evalCompiledStep`
   (`M.evalActTri` / `Interp.semPhrase`), returning Charter's three institutional answers
   (`occurred`, `lawful`, `valid`, `Law 2`) plus enumerated `effectsOf` capability tokens, and
   proving monotone auditability across growing network histories over the live evaluator.
2. **Mandatory authorship reflection (`reflectAuthor_no_impersonation`):**
   Schnorr-verified `SignedStatement`s authored by `α` may only supply base/input facts whose
   leading actor argument equals `α` or tender `Evidenced` support/rebuttal with `issuer = α`.
3. **Per-statement revocation & expiry (`revocation_invalidates_bundle`, `unrelated_revocation_preserves_bundle`):**
   Author-signed `RevocationNotice`s (`revokedIds`) and `expiresAt` stamps retire individual
   delegations without disturbing active agreements or unrelated bundles.
4. **Audience-bounded statement sharing (`public_gossip_always_lawful`, `restricted_leak_detected_and_unusable`):**
   `.unrestricted` statements propagate freely with zero communication overhead, whereas
   forwarding `.restricted` statements outside their permitted audience records a
   `CommViolation` (`Law 1`–`Law 3`) and confers no standing in `verifyBundle`.
5. **Commitment-bound redacted attestations (`redacted_bundle_agrees_with_unredacted`):**
   `RedactedAttestation`s bind the SHA-256 commitment of a private `SignedStatement` to an
   auditor/enclave Schnorr attestation exporting only non-confidential interface facts.
6. **Minimal bundle synthesis (`synthesizeBundle_sound`) & notice-gated obligation safety (`unnoticed_duty_never_violated`):**
   Dependency-cone slicing synthesizes minimal valid bundles from candidate statement pools,
   and `unnoticed_duty_never_violated` proves over `M.eval` that a notice-gated `Duty`
   (`Due within d After notice`) is never violated before notice is established in state.
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Audience disclosure policy on a signed peer statement (`D43`). -/
inductive AudiencePolicy where
  | unrestricted
  | restricted (allowed : List String)
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

def AudiencePolicy.permits (pol : AudiencePolicy) (agent : String) : Bool :=
  match pol with
  | .unrestricted => true
  | .restricted allowed => allowed.contains agent

/-- Positive ground guard fact required by a scoped conditional delegation (`D44`). -/
structure GuardAtom where
  factName : DomId
  args     : List Elem
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- One assertion carried inside a peer's `SignedStatement` (`D43`, `D44`). -/
inductive StatementAssertion where
  /-- Supply a base/input fact whose leading actor argument must match `stmt.author`. -/
  | inputFact (factName : DomId) (args : List Elem) (holds : Bool := true)
  /-- Tender supporting or rebutting evidence on an `Evidenced` fact as `issuer = stmt.author`. -/
  | tenderEvidence (factName : DomId) (args : List Elem) (polarity : Bool)
  /-- Authorize `recipient` to receive and rely upon a `.restricted` statement authored by `stmt.author`. -/
  | grantDisclosure (targetStatementId : String) (recipient : String)
  /-- Scoped conditional delegation (`D44`): assert `factName(args)` (whose leading argument must
  equal `stmt.author`) whenever all positive `guards` hold in the extracted bundle state. -/
  | delegateWhen (factName : DomId) (args : List Elem) (guards : List GuardAtom)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Canonical serialization of a `StatementAssertion` for cryptographic signing. -/
def canonicalAssertionSig : StatementAssertion → String
  | .inputFact fn args h =>
    s!"in:{fn}:{",".intercalate (args.map canonicalElemSig)}:{h}"
  | .tenderEvidence fn args pol =>
    s!"ev:{fn}:{",".intercalate (args.map canonicalElemSig)}:{pol}"
  | .grantDisclosure sid recp =>
    s!"disc:{sid}:{recp}"
  | .delegateWhen fn args gs =>
    let gStr := "&".intercalate (gs.map fun g => s!"{g.factName}({",".intercalate (g.args.map canonicalElemSig)})")
    s!"del:{fn}:{",".intercalate (args.map canonicalElemSig)}:when:{gStr}"

def canonicalAudienceSig : AudiencePolicy → String
  | .unrestricted => "pub"
  | .restricted allowed => "res:" ++ ",".intercalate allowed

/-- Cryptographically signed peer policy or delegation statement (`D43`). -/
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

/-- SHA-256 commitment digest of a `SignedStatement` (bound by `RedactedAttestation`s). -/
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

/-- Author-signed revocation of an earlier `SignedStatement` (`D43`). -/
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
while exporting only non-confidential interface assertions (`D43`, `T43`). -/
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

/-- Check that an exported assertion touches no `Confidential` fact in `spec` (`T43`, `D43`, `D44`). -/
def assertionIsNonConfidential (spec : Spec) : StatementAssertion → Bool
  | .inputFact fn _ _ | .tenderEvidence fn _ _ =>
    let canon := spec.chaseAlias fn
    match spec.findDecl canon with
    | some { kind := .fact fs, .. } => !fs.confidential
    | _ => false
  | .delegateWhen fn _ gs =>
    let okFact (d : DomId) : Bool :=
      match spec.findDecl (spec.chaseAlias d) with
      | some { kind := .fact fs, .. } => !fs.confidential
      | _ => false
    okFact fn && gs.all (fun g => okFact g.factName)
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

/-- Authorized auditor opening check verifying `raw` against `a.commitmentSha256`. -/
def verifyRedactedOpening (spec : Spec) (raw : SignedStatement) (a : RedactedAttestation) : Bool :=
  verifyStatementSig raw &&
  verifyRedactedAttestation spec a &&
  a.statementId == raw.statementId &&
  a.author == raw.author &&
  a.basisLawHash == raw.basisLawHash &&
  a.commitmentSha256 == computeStatementCommitment raw

/-! ## Mandatory Authorship Reflection -/

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
  | .delegateWhen _ _ _ => none

/-- Check whether a positive `GuardAtom` currently holds in `cfg` (`D44`). -/
def guardAtomHolds (cfg : Config) (g : GuardAtom) : Bool :=
  match buildInstanceTerm cfg.spec g.factName g.args with
  | .error _ => false
  | .ok tm =>
    let ctx := Ctx.of cfg.spec cfg.state
    match (M.whenTagged (M.eval M.fuel tm) pure).run ctx [] with
    | .ok (te :: _) => cfg.state.holds te
    | _ => false

/-- Compile a `delegateWhen` assertion into a `CPhrase` once all positive `guards` hold in `cfg`,
enforcing the exact same mandatory authorship reflection (`hasLeadingAuthor author args`) as `inputFact`. -/
def extractConditionalPhrase (cfg : Config) (author : String) : StatementAssertion → Option CPhrase
  | .delegateWhen fn args gs =>
    if gs.all (guardAtomHolds cfg) then
      extractAssertionPhrase cfg.spec author (.inputFact fn args true)
    else none
  | _ => none

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
    | delegateWhen _ _ _ =>
      simp [extractAssertionPhrase] at hExt

/-- **Theorem 1b (`delegateWhen_no_impersonation`, `D44`):**
A scoped conditional delegation `delegateWhen fn args gs` signed by `author` can never fire to
assert a fact whose leading actor argument belongs to any `other ≠ author`. -/
theorem delegateWhen_no_impersonation
    (cfg : Config) (author other : String) (hNe : other ≠ author)
    (fn : DomId) (args : List Elem) (gs : List GuardAtom) (cph : CPhrase)
    (hCond : extractConditionalPhrase cfg author (.delegateWhen fn args gs) = some cph) :
    hasLeadingAuthor other args = false := by
  unfold extractConditionalPhrase at hCond
  cases hG : gs.all (guardAtomHolds cfg)
  · simp [hG] at hCond
  · simp [hG] at hCond
    exact (reflectAuthor_no_impersonation cfg.spec author other hNe (.inputFact fn args true) cph hCond).1
      fn args true rfl

/-! ## Self-Contained Action-Carried Justification Bundles -/

/-- Enumerated ground capability/state-change effect projected from a valid transition. -/
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

/-- Self-contained action-carried justification bundle (`D43`). -/
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

/-- Apply extracted ground `CPhrase`s from author-reflected assertions onto `cfg`. -/
def applyAuthorAssertions (cfg : Config) (author : String) (assertions : List StatementAssertion) : Config :=
  assertions.foldl (fun acc a =>
    match extractAssertionPhrase acc.spec author a with
    | some cph => (evalCompiledStep acc cph true).1
    | none => acc) cfg

/-- Apply one pass of scoped conditional delegations (`delegateWhen`, `D44`) whose positive guards hold. -/
def applyConditionalPass (cfg : Config) (items : List (String × StatementAssertion)) : Config :=
  items.foldl (fun acc (author, a) =>
    match extractConditionalPhrase acc author a with
    | some cph => (evalCompiledStep acc cph true).1
    | none => acc) cfg

/-- Evaluate bounded positive conditional delegations up to a structural fixpoint (`D44`). -/
def saturateConditionalAssertions : Nat → Config → List (String × StatementAssertion) → Config
  | 0, cfg, _ => cfg
  | fuel + 1, cfg, items =>
    let cfg' := applyConditionalPass cfg items
    saturateConditionalAssertions fuel cfg' items

/-- Build the closed bundle evaluation `Config` from `(baseCfg, enactedAt, statements, attestations)`. -/
def extractBundleConfig (baseCfg : Config) (enactedAt : Int)
    (stmts : List SignedStatement) (atts : List RedactedAttestation) : Config :=
  let cfgAtTime :=
    if enactedAt > baseCfg.state.time then
      (evalCompiledStep baseCfg (.setTime (.intLit enactedAt)) true).1
    else baseCfg
  let cfgStmts := stmts.foldl (fun acc s => applyAuthorAssertions acc s.author s.assertions) cfgAtTime
  let cfgGround := atts.foldl (fun acc a => applyAuthorAssertions acc a.author a.exportedAssertions) cfgStmts
  let condItems : List (String × StatementAssertion) :=
    (stmts.flatMap fun s => s.assertions.filterMap fun
      | d@(.delegateWhen _ _ _) => some (s.author, d) | _ => none) ++
    (atts.flatMap fun a => a.exportedAssertions.filterMap fun
      | d@(.delegateWhen _ _ _) => some (a.author, d) | _ => none)
  if condItems.isEmpty then cfgGround
  else saturateConditionalAssertions condItems.length cfgGround condItems

/-- Three-answer Charter evaluation verdict + enumerated capability effects for a bundle (`Law 2`). -/
structure BundleEvalResult where
  occurred      : String -- "bundle-evaluated"
  lawful        : TriBool
  valid         : TriBool
  outcome       : String
  effectsOf     : List EnumeratedEffect := []
  unmetEvidence : List (String × EvidenceStatus) := []
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

/-- Evaluate an action against an extracted closed `Config` using Charter's `evalCompiledStep`. -/
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

/-- Closed-box static evaluation over `(baseCfg, b)` returning Charter's three answers. -/
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

/-! ## Federated Network State, Monotone Auditability, & Per-Statement Revocation -/

/-- Federated control-plane configuration tracking active `agreedLaws`, retired historical
`supersededLaws` (`D44`), peer `stated` messages, per-statement `revokedIds`, and `enacted` bundles (`D43`). -/
structure FedNetwork where
  agreedLaws     : List String := []
  supersededLaws : List String := []
  stated         : List SignedStatement := []
  revokedIds     : List String := []
  enacted        : List JustificationBundle := []
  deriving Repr, Inhabited, ToJson, FromJson

/-- Monotone network history growth (`stated` and `enacted` grow monotonically). -/
def FedNetwork.growing (n₁ n₂ : FedNetwork) : Prop :=
  (∀ s, s ∈ n₁.stated → s ∈ n₂.stated) ∧
  (∀ b, b ∈ n₁.enacted → b ∈ n₂.enacted)

/-- `basedBundle`: bundle's `basisLawHash` is in the active synchronized `agreedLaws` set. -/
def basedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  net.agreedLaws.contains b.basisLawHash

/-- `historicallyBasedBundle` (`D44`): bundle's `basisLawHash` is either currently active in
`agreedLaws`, or was active in `supersededLaws` when `b` was already `enacted`. -/
def historicallyBasedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  net.agreedLaws.contains b.basisLawHash ||
  (net.supersededLaws.contains b.basisLawHash && net.enacted.any (·.bundleId == b.bundleId))

/-- `freshBundle` (`D44`): `b.bundleId` has not already been enacted (blocks bundle replay). -/
def freshBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  !net.enacted.any (·.bundleId == b.bundleId)

/-- Retire `oldLaw` into `supersededLaws` and activate `newLaw` in `agreedLaws` (`D44`). -/
def supersedeLawEpoch (net : FedNetwork) (oldLaw newLaw : String) : FedNetwork :=
  let keptActive := net.agreedLaws.filter (· != oldLaw)
  let active' := if keptActive.contains newLaw then keptActive else newLaw :: keptActive
  let sup' := if oldLaw == newLaw || net.supersededLaws.contains oldLaw then net.supersededLaws
              else oldLaw :: net.supersededLaws
  { net with agreedLaws := active', supersededLaws := sup' }

/-- Static parallel commutativity check between two federated actions (`D44`, `Footprint.actsFootprintCommute`). -/
def actionsCommute (spec : Spec) (actA actB : DomId) : Bool :=
  Footprint.actsFootprintCommute spec actA actB

/-- Static parallel commutativity check between two `JustificationBundle`s (`D44`). -/
def bundlesCommute (spec : Spec) (b₁ b₂ : JustificationBundle) : Bool :=
  b₁.bundleId != b₂.bundleId && actionsCommute spec b₁.action b₂.action

/-- `sourcedBundle`: every `SignedStatement` carried in `b` has been `stated`. -/
def sourcedBundle (net : FedNetwork) (b : JustificationBundle) : Bool :=
  b.statements.all (fun s => net.stated.any (· == s))

/-- `unrevokedBundle`: none of `b`'s statements or attestations has been revoked. -/
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

/-- Replay-safe live enactment verification (`freshBundle ∧ verifyBundle`, `D44`). -/
def enactableBundle (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) :
    Except String BundleEvalResult :=
  if !freshBundle net b then
    .error s!"bundle replay rejected: bundleId `{b.bundleId}` was already enacted"
  else
    verifyBundle baseCfg net b

/-- Cross-epoch audit verification (`historicallyBasedBundle ∧ sourced ∧ unrevoked ∧ evalBundleStatic`, `D44`). -/
def verifyBundleAudit (epochCfg : Config) (net : FedNetwork) (b : JustificationBundle) :
    Except String BundleEvalResult :=
  if !historicallyBasedBundle net b then
    .error s!"bundle basis `{b.basisLawHash}` is neither in agreedLaws nor an enacted historical epoch"
  else if !sourcedBundle net b then
    .error "bundle carries an unsourced statement absent from network history"
  else if !unrevokedBundle net b then
    .error "bundle relies on a revoked statement"
  else
    evalBundleStatic epochCfg b

/-- Boolean permission predicate (`lawful == .yes && valid == .yes` under `verifyBundle`). -/
def permittedBundle (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle) : Bool :=
  match verifyBundle baseCfg net b with
  | .ok res => res.lawful == .yes && res.valid == .yes
  | .error _ => false

/-- **Theorem 2b (`replay_bundle_rejected`, `D44`):**
Any bundle `b` whose `bundleId` already appears in `net.enacted` is rejected by `enactableBundle`. -/
theorem replay_bundle_rejected
    (baseCfg : Config) (net : FedNetwork) (b : JustificationBundle)
    (hEnacted : net.enacted.any (·.bundleId == b.bundleId) = true) :
    (enactableBundle baseCfg net b).isOk = false := by
  unfold enactableBundle freshBundle
  rw [hEnacted]
  rfl

theorem list_contains_filter_self_false (xs : List String) (x : String) :
    (xs.filter (· != x)).contains x = false := by
  simp

/-- **Theorem 2c (`superseded_law_cannot_enact_new`, `D44`):**
Once `oldLaw` is superseded by `newLaw` (`oldLaw ≠ newLaw`), no bundle `b` carrying
`b.basisLawHash = oldLaw` can pass `permittedBundle` or `enactableBundle` in the new epoch. -/
theorem superseded_law_cannot_enact_new
    (baseCfg : Config) (net : FedNetwork) (oldLaw newLaw : String) (b : JustificationBundle)
    (hNe : oldLaw ≠ newLaw)
    (hOld : b.basisLawHash = oldLaw) :
    permittedBundle baseCfg (supersedeLawEpoch net oldLaw newLaw) b = false ∧
    (enactableBundle baseCfg (supersedeLawEpoch net oldLaw newLaw) b).isOk = false := by
  have hNotBased : basedBundle (supersedeLawEpoch net oldLaw newLaw) b = false := by
    unfold basedBundle supersedeLawEpoch
    rw [hOld]
    dsimp only
    by_cases hHasNew : (net.agreedLaws.filter (· != oldLaw)).contains newLaw = true
    · rw [if_pos hHasNew]
      exact list_contains_filter_self_false net.agreedLaws oldLaw
    · rw [if_neg hHasNew, List.contains_cons]
      have hBeqFalse : (oldLaw == newLaw) = false := beq_false_of_ne hNe
      rw [hBeqFalse, Bool.false_or]
      exact list_contains_filter_self_false net.agreedLaws oldLaw
  constructor
  · unfold permittedBundle verifyBundle
    rw [hNotBased]
    rfl
  · unfold enactableBundle verifyBundle
    cases freshBundle (supersedeLawEpoch net oldLaw newLaw) b
    · rfl
    · rw [hNotBased]; rfl

/-- **Theorem 2d (`historical_audit_preserves_enacted`, `D44`):**
Any bundle `b` already enacted (`net.enacted.any (·.bundleId == b.bundleId) = true`) that was
valid under `verifyBundle epochCfg net b = .ok res` continues to validate identically under
`verifyBundleAudit` after `b.basisLawHash` is superseded by `newLaw`. -/
theorem historical_audit_preserves_enacted
    (epochCfg : Config) (net : FedNetwork) (newLaw : String)
    (b : JustificationBundle) (res : BundleEvalResult)
    (hEnacted : net.enacted.any (·.bundleId == b.bundleId) = true)
    (hVer : verifyBundle epochCfg net b = .ok res) :
    verifyBundleAudit epochCfg (supersedeLawEpoch net b.basisLawHash newLaw) b = .ok res := by
  unfold verifyBundle at hVer
  cases hB : basedBundle net b <;> simp [hB] at hVer
  cases hS : sourcedBundle net b <;> simp [hS] at hVer
  cases hU : unrevokedBundle net b <;> simp [hU] at hVer
  have hHist : historicallyBasedBundle (supersedeLawEpoch net b.basisLawHash newLaw) b = true := by
    unfold historicallyBasedBundle supersedeLawEpoch
    dsimp only
    by_cases hSame : b.basisLawHash = newLaw
    · rw [hSame]
      have hInActive : (if (net.agreedLaws.filter (· != newLaw)).contains newLaw then
          net.agreedLaws.filter (· != newLaw) else newLaw :: net.agreedLaws.filter (· != newLaw)).contains newLaw = true := by
        by_cases hC : (net.agreedLaws.filter (· != newLaw)).contains newLaw = true
        · rw [if_pos hC]; exact hC
        · rw [if_neg hC, List.contains_cons]; simp
      rw [hInActive]; rfl
    · have hBeqFalse : (b.basisLawHash == newLaw) = false := beq_false_of_ne hSame
      have hInSup : (if b.basisLawHash == newLaw || net.supersededLaws.contains b.basisLawHash then
          net.supersededLaws else b.basisLawHash :: net.supersededLaws).contains b.basisLawHash = true := by
        rw [hBeqFalse, Bool.false_or]
        by_cases hSup : net.supersededLaws.contains b.basisLawHash = true
        · rw [if_pos hSup]; exact hSup
        · rw [if_neg hSup, List.contains_cons]; simp
      rw [hInSup, hEnacted]; simp
  have hS' : sourcedBundle (supersedeLawEpoch net b.basisLawHash newLaw) b = true := by
    unfold sourcedBundle supersedeLawEpoch; exact hS
  have hU' : unrevokedBundle (supersedeLawEpoch net b.basisLawHash newLaw) b = true := by
    unfold unrevokedBundle supersedeLawEpoch; exact hU
  unfold verifyBundleAudit
  simp [hHist, hS', hU', hVer]

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

/-- **Theorem 3 (`persist_permitted_bundle`):**
Because non-monotonic Charter rules (`Not`, `Default`/`Exception`, `Immunity`) evaluate inside
the closed extracted bundle state (`evalBundleStatic`), any action bundle judged lawful and valid
in `n₁` remains identically lawful and valid in every grown network state `n₂` (`growing n₁ n₂`)
whose `agreedLaws` still contain `b.basisLawHash` and in which `b`'s statements remain unrevoked,
regardless of additional statements published to `n₂.stated`. -/
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

/-- Record a verified `RevocationNotice` in `net` without altering `agreedLaws`. -/
def applyRevocationId (net : FedNetwork) (sid : String) : FedNetwork :=
  if net.revokedIds.contains sid then net
  else { net with revokedIds := sid :: net.revokedIds }

/-- **Theorem 4 (`revocation_invalidates_bundle`):**
Revoking `s.statementId` immediately invalidates any bundle carrying `s`, without altering
`agreedLaws`. -/
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
unchanged. -/
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

/-! ## Audience-Bounded Communication (`stepGossip` & `CommViolation`) -/

/-- Recorded breach when an agent forwards a `.restricted` statement outside its allowed audience. -/
structure CommViolation where
  sender      : String
  recipient   : String
  statementId : String
  deriving Repr, DecidableEq, BEq, Inhabited, ToJson, FromJson

/-- Federated multi-agent system with per-agent partial views plus communication-breach tracking. -/
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

/-- Whether `sender` is authorized to forward `s` to `recipient` given `senderView`. -/
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
`CommViolation` when gossiped. -/
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

/-- **Theorem 7 (`restricted_leak_detected_and_unusable`):**
If `s.audience = .restricted allowed` and `recipient` is neither in `allowed` nor `s.author`
and holds no valid disclosure grant from `s.author`:
1. Any `stepGossip` of `s` from `sender` (holding `s`) to `recipient` records
   `⟨sender, recipient, s.statementId⟩` in `commViolations`; and
2. `recipient` cannot use the leaked statement `s` to pass `permittedBundle`. -/
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

/-! ## Commitment-Bound Redacted Attestation Equivalence -/

/-- **Theorem 8 (`redacted_bundle_agrees_with_unredacted`):**
Whenever a bundle carrying a `RedactedAttestation` (`bRedacted`, hiding `Confidential` raw facts)
and the corresponding unredacted bundle (`bRaw`) pass envelope signature/audience checks and
induce the same extracted `Config` on the public interface, `evalBundleStatic` returns the
exact same `(occurred, lawful, valid, outcome, effectsOf)` verdict while `bRedacted` exposes
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

/-! ## Dependency-Sliced Minimal Bundle Synthesis -/

/-- Collect asserted or guard-referenced `DomId`s inside a `SignedStatement` for dependency-cone filtering. -/
def statementAssertedDoms (spec : Spec) (s : SignedStatement) : List DomId :=
  s.assertions.flatMap fun
    | .inputFact fn _ _ | .tenderEvidence fn _ _ => [spec.chaseAlias fn]
    | .delegateWhen fn _ gs => spec.chaseAlias fn :: gs.map (fun g => spec.chaseAlias g.factName)
    | .grantDisclosure _ _ => []

/-- Dependency cone of `DomId`s transitively referenced by `actName`'s conditions/derivations
and any candidate `delegateWhen` guard atoms (`D43`, `D44`). -/
def actionRelevantDoms (spec : Spec) (actName : DomId) (candidates : List SignedStatement := []) : List DomId :=
  let root := spec.chaseAlias actName
  let delEdges : List (DomId × List DomId) := candidates.flatMap fun s =>
    s.assertions.filterMap fun
      | .delegateWhen fn _ gs => some (spec.chaseAlias fn, gs.map (fun g => spec.chaseAlias g.factName))
      | _ => none
  let stepOnce (acc : List DomId) : List DomId :=
    let next := acc.flatMap fun d =>
      let fromDel := (delEdges.filter (·.1 == d)).flatMap (·.2)
      let fromSpec := match spec.findDecl d with
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
      fromSpec ++ fromDel
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
  let cone := actionRelevantDoms baseCfg.spec action candidates
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

/-- Synthesize a minimal valid `JustificationBundle` from a candidate pool (discarding
irrelevant, expired, revoked, unauthorized, or conflicting statements). -/
def synthesizeBundle (baseCfg : Config) (net : FedNetwork)
    (actorSeed bundleId actor : String) (action : DomId) (args : List Elem)
    (basisLawHash : String) (enactedAt : Int)
    (candidates : List SignedStatement) : Option JustificationBundle :=
  let cand := synthesizeCandidateBundle baseCfg net actorSeed bundleId actor action args basisLawHash enactedAt candidates
  if permittedBundle baseCfg net cand then some cand else none

/-- **Theorem 9 (`synthesizeBundle_sound`):**
Every `JustificationBundle` returned by `synthesizeBundle` satisfies `permittedBundle baseCfg net b = true`
over Charter's live evaluator. -/
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

/-! ## Partial-View Notice Safety for Obligations -/

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

/-- **Theorem 10 (`unnoticed_duty_never_violated`):**
Evaluated directly over Charter's live `M.eval`, whenever `noticeTerm` has not yet occurred in
state (`(M.eval (fuel + 1) (.doneAt noticeTerm)).run ctx subs = .ok [.bool false]`), the
notice-gated obligation violation condition `noticeGatedViolationTerm noticeTerm durTerm`
evaluates to `.ok [.bool false]` at every clock instant `ctx.state.time`. -/
theorem unnoticed_duty_never_violated
    (fuel : Nat) (ctx : Ctx) (subs : Subs) (noticeTerm durTerm : Term)
    (hUnnoticed : (M.eval (fuel + 1) (.doneAt noticeTerm)).run ctx subs = .ok [.bool false]) :
    (M.eval (fuel + 2) (noticeGatedViolationTerm noticeTerm durTerm)).run ctx subs = .ok [.bool false] :=
  eval_and_short_circuit_false (fuel + 1) ctx subs (.doneAt noticeTerm)
    (.geq (.sub .currentTime (.stampOf noticeTerm)) durTerm) hUnnoticed

/-! ## End-to-End Federated Bundle Self-Test Suite -/

def mkBundleDemoSpec : Spec :=
  let strDom   : TypeSpec := { kind := .fact {}, domain := .anyString, closed := some false }
  let actorDom : TypeSpec := { kind := .fact {}, domain := .strings ["ClinicA", "PartnerLab", "ThirdParty"], derivation := [.holdsWhen (.boolLit true)], closed := some true }
  let taskDom  : TypeSpec := { kind := .fact {}, domain := .strings ["Study1"], derivation := [.holdsWhen (.boolLit true)], closed := some true }
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
  let trFact   : TypeSpec := {
    kind := .fact { isInput := true }
    domain := .products [⟨"actor", ""⟩]
    closed := some true
  }
  let noteFact : TypeSpec := {
    kind := .fact {}
    domain := .products [⟨"actor", ""⟩]
    closed := some true
  }
  let doneFact : TypeSpec := {
    kind := .fact {}
    domain := .products [⟨"actor", ""⟩, ⟨"task", ""⟩]
    closed := some true
  }
  let condCleared : Term :=
    .present (.app "consent-cleared" (.named [(⟨"actor", ""⟩, .tag (.stringLit "ClinicA") "actor"),
                                              (⟨"task", ""⟩, .ref ⟨"task", ""⟩)]))
  let effDone : Effect :=
    .cAll [] (.app "study-completed" (.named [(⟨"actor", ""⟩, .ref ⟨"actor", ""⟩),
                                              (⟨"task", ""⟩, .ref ⟨"task", ""⟩)]))
  let effNote : Effect :=
    .cAll [] (.app "audit-note" (.named [(⟨"actor", ""⟩, .ref ⟨"actor", ""⟩)]))
  let procAct : TypeSpec := {
    kind := .act { effects := [effDone], validWhen := [condCleared], isPower := true }
    domain := .products [⟨"actor", ""⟩, ⟨"task", ""⟩]
    derivation := [.holdsWhen condCleared]
    closed := some true
  }
  let noteAct : TypeSpec := {
    kind := .act { effects := [effNote], validWhen := [.boolLit true], isPower := true }
    domain := .products [⟨"actor", ""⟩]
    derivation := [.holdsWhen (.boolLit true)]
    closed := some true
  }
  { decls := [
      ("audit-note", noteFact),
      ("log-note", noteAct),
      ("lab-trusted", trFact),
      ("study-completed", doneFact),
      ("process-study", procAct),
      ("consent-cleared", clrFact),
      ("patient-record", patFact),
      ("task", taskDom),
      ("actor", actorDom),
      ("string", strDom)
    ] }

def bundleSelfTest : Bool :=
  let spec := mkBundleDemoSpec
  let strata := match Stratify.strata spec with | .ok st => st | .error _ => []
  let initState := match Saturate.rebaseAndSat spec strata {} with | .ok s => s | .error _ => {}
  let baseCfg : Config := { spec, strata, state := initState }
  let lawHash := "law-federation-v1"
  let clinicStmt := signStatement "seed-clinic-a" "stmt-ca-1" "ClinicA" lawHash 0 (some 100)
    (.restricted ["PartnerLab"])
    [.inputFact "consent-cleared" [.str "ClinicA", .str "Study1"] true]
  let outsiderForge := signStatement "seed-outsider" "stmt-forge" "ThirdParty" lawHash 0 none .unrestricted
    [.inputFact "consent-cleared" [.str "ClinicA", .str "Study1"] true]
  let net0 : FedNetwork := { agreedLaws := [lawHash], stated := [clinicStmt, outsiderForge] }
  let forgeBundle := signBundle "seed-outsider" "b-forge-1" "ThirdParty" "process-study" [.str "ThirdParty", .str "Study1"]
    lawHash 5 [outsiderForge] []
  let forgeBlocked := !permittedBundle baseCfg net0 forgeBundle
  let labSynth? := synthesizeBundle baseCfg net0 "seed-lab" "b-lab-1" "PartnerLab"
    "process-study" [.str "PartnerLab", .str "Study1"] lawHash 5 [outsiderForge, clinicStmt]
  let synthOk := match labSynth? with
    | some b => permittedBundle baseCfg net0 b && b.statements.length == 1
    | none => false
  let sys0 : FedSystem := { net := net0, views := [("PartnerLab", [clinicStmt])] }
  let sysLeak := stepGossip sys0 "PartnerLab" "ThirdParty" clinicStmt
  let leakBundle := signBundle "seed-outsider" "b-leak-1" "ThirdParty" "process-study" [.str "ThirdParty", .str "Study1"]
    lawHash 5 [clinicStmt] []
  let leakCaughtAndBlocked :=
    sysLeak.commViolations.contains ⟨"PartnerLab", "ThirdParty", "stmt-ca-1"⟩ &&
    !permittedBundle baseCfg net0 leakBundle
  let rawSecret := signStatement "seed-clinic-a" "stmt-ca-secret" "ClinicA" lawHash 0 (some 100)
    (.restricted ["auditor"])
    [.inputFact "patient-record" [.str "ClinicA", .str "Patient42"] true,
     .inputFact "consent-cleared" [.str "ClinicA", .str "Study1"] true]
  let att := mintRedactedAttestation "seed-auditor" "AuditorPanel" rawSecret
    [.inputFact "consent-cleared" [.str "ClinicA", .str "Study1"] true] (some (.restricted ["PartnerLab"]))
  let netSecret : FedNetwork := { agreedLaws := [lawHash], stated := [rawSecret] }
  let redactedBundle := signBundle "seed-lab" "b-lab-red" "PartnerLab" "process-study"
    [.str "PartnerLab", .str "Study1"] lawHash 5 [] [att]
  let redactedOk :=
    verifyRedactedOpening spec rawSecret att &&
    permittedBundle baseCfg netSecret redactedBundle
  let netRev := applyRevocationId net0 "stmt-ca-1"
  let revokeIsolated :=
    (match labSynth? with | some b => !permittedBundle baseCfg netRev b | none => false) &&
    permittedBundle baseCfg (applyRevocationId netSecret "stmt-ca-1") redactedBundle
  -- D44 checks: delegateWhen standing mandate, replay rejection, epoch supersession, & commutativity
  let standingDel := signStatement "seed-clinic-a" "stmt-del-standing" "ClinicA" lawHash 0 none .unrestricted
    [.delegateWhen "consent-cleared" [.str "ClinicA", .str "Study1"] [⟨"lab-trusted", [.str "PartnerLab"]⟩]]
  let labTrustStmt := signStatement "seed-lab" "stmt-lab-trust" "PartnerLab" lawHash 0 none .unrestricted
    [.inputFact "lab-trusted" [.str "PartnerLab"] true]
  let netDel : FedNetwork := { agreedLaws := [lawHash], stated := [standingDel, labTrustStmt] }
  let delSynth? := synthesizeBundle baseCfg netDel "seed-lab" "b-del-1" "PartnerLab"
    "process-study" [.str "PartnerLab", .str "Study1"] lawHash 5 [standingDel, labTrustStmt]
  let delOk := match delSynth? with
    | some bd =>
      let netEnacted := { netDel with enacted := [bd] }
      let replayBlocked := !(enactableBundle baseCfg netEnacted bd).isOk
      let netEpoch2 := supersedeLawEpoch netEnacted lawHash "law-federation-v2"
      let newUnderOldBlocked := !permittedBundle baseCfg netEpoch2 bd
      let histAuditPreserved := (verifyBundleAudit baseCfg netEpoch2 bd).isOk
      permittedBundle baseCfg netDel bd && replayBlocked && newUnderOldBlocked && histAuditPreserved
    | none => false
  let commuteOk :=
    actionsCommute spec "process-study" "log-note" &&
    !actionsCommute spec "process-study" "process-study"
  forgeBlocked && synthOk && leakCaughtAndBlocked && redactedOk && revokeIsolated && delOk && commuteOk

end Charter.Server
