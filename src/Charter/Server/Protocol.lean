import Charter.Server.Reservations
import Charter.Eval.Plan

/-!
# Charter.Server.Protocol — Audience-Scoped `ReasonGraph`, `ClockPolicy`, & `certificate-at-office` (`G4.4`)

Implements the operator-blind server protocol layer (`docs/rfc.md` §8.1–§8.8):
1. `ClockPolicy` enforcement (`monotonic` + `maxSkew` bounds on `AdvanceClock`).
2. Operator-blind `ReasonGraph` construction + `redactForAudience` (`T43`, zero `Surface/` imports).
3. `installCertifiedAmendment` (`certificate-at-office`, `2026-10-22-redesign.md` §3a & §5.5):
   verifies the active law's `Amend` act (`Allow`), verifies the successor `Artifact`'s
   cryptographic certificate and `WellFormed` check, and verifies that no `Entrenched Invariant`
   or entrenchment `Immunity` of the active law was weakened (`T24`).
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Server clock policy (`docs/rfc.md` §6.1). -/
structure ClockPolicy where
  monotonic : Bool := true
  maxSkew   : Option Int := none
  deriving Repr, ToJson, FromJson

def validateClockAdvance (pol : ClockPolicy) (curTime newTime : Int) : Except String Unit := do
  if pol.monotonic && newTime < curTime then
    .error s!"ClockPolicy violation: newTime={newTime} < current={curTime}"
  if let some skew := pol.maxSkew then
    if newTime - curTime > skew then
      .error s!"ClockPolicy violation: jump {newTime - curTime} exceeds maxSkew={skew}"
  .ok ()

-- Collect `(DomId, Args)` applications inside a `Term` (operator-blind mirror of `Explain`).
mutual
def collectApps : Term → List (DomId × Args)
  | .app d args => (d, args) :: collectArgs args
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .project a _ | .tag a _ | .untag a =>
    collectApps a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b =>
    collectApps a ++ collectApps b
  | .mulDivRound x n d _ =>
    collectApps x ++ collectApps n ++ collectApps d
  | .fnApp _ k => collectApps k
  | .dimLit _ _ => []
  | .ite c t e => collectApps c ++ collectApps t ++ collectApps e
  | .doneAt t | .stampOf t | .overdueOf t => collectApps t
  | .calOp1 _ t => collectApps t
  | .calOp2 _ t a => collectApps t ++ collectApps a
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t =>
    collectApps t
  | .boolLit _ | .intLit _ | .stringLit _ | .ref _ | .currentTime => []

def collectArgs : Args → List (DomId × Args)
  | .pos ts => collectTermList ts
  | .named ms => collectModList ms

def collectTermList : List Term → List (DomId × Args)
  | [] => []
  | t :: ts => collectApps t ++ collectTermList ts

def collectModList : List (Var × Term) → List (DomId × Args)
  | [] => []
  | (_, t) :: ms => collectApps t ++ collectModList ms
end

/-- Build and audience-redact a `ReasonGraph` for `d(args...)` directly inside `charter-server` (`T43`). -/
def explainInstance (cfg : Config) (d : DomId) (args : List Elem) (audience? : Option String) :
    Except String ReasonGraph := do
  let tm ← buildInstanceTerm cfg.spec d args
  let ctx := Ctx.of cfg.spec cfg.state
  let tes ← match (M.whenTagged (M.eval M.fuel tm) pure).run ctx [] with
    | .ok xs => .ok xs
    | .error e => .error e.message
  let te ← match tes with
    | x :: _ => .ok x
    | [] => .error s!"`{d}` produced no instance"
  let spec := cfg.spec
  let state := cfg.state
  let runM {α} (m : M α) (subs : Subs := []) : List α :=
    match m.run ctx subs with | .ok xs => xs | .error _ => []
  let rawRg : ReasonGraph := match spec.findDecl te.2 with
    | none => { subject := te.pp, lawful := .no, valid := .no }
    | some tspec =>
      let binds := Tagged.bindings tspec.domain te
      match tspec.kind with
      | .act a =>
        let (lTri, vTri, unmetRaw) := (runM (M.evalActTri M.fuel te)).headD (.no, .no, [])
        let unmetMeta := unmetRaw.map fun (uTe, st) =>
          match spec.findDecl uTe.2 with
          | some { kind := .fact fs, .. } => (uTe.pp, st, fs.confidential, fs.audiences)
          | _ => (uTe.pp, st, false, [])
        let hwTerms := tspec.derivation.filterMap fun | .holdsWhen c => some c | _ => none
        let allTerms := hwTerms ++ tspec.conditions ++ a.validWhen
        let apps := (allTerms.flatMap collectApps).foldl
          (fun acc p => if acc.any (fun q => q.1 == p.1 && reprStr q.2 == reprStr p.2) then acc else acc ++ [p]) []
        let pInsts := (apps.flatMap fun (pd, pargs) =>
          runM (M.whenTagged (M.eval M.fuel (.app pd pargs)) pure) binds).foldl
          (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []
        let pNodes : List ReasonNode := pInsts.filterMap fun pTe =>
          if pTe == te then none
          else match spec.findDecl pTe.2 with
            | some { kind := .fact fs, spans, .. } =>
              if fs.evidenced then
                let st := state.evidenceStatus pTe
                let srcs := state.evidenceSources pTe
                let det := if srcs.isEmpty then "no tendered evidence"
                  else ", ".intercalate (srcs.map fun (k, s, n) => s!"{k} by {showString s} @step{n}")
                some { id := pTe.pp, kind := "evidence", status := st.asString, spans,
                       confidential := fs.confidential, allowedAudiences := fs.audiences, detail := det }
              else
                let h := state.holds pTe
                some { id := pTe.pp, kind := "premise", status := if h then "yes" else "no", spans,
                       confidential := fs.confidential, allowedAudiences := fs.audiences,
                       detail := if h then "holds" else "does not hold" }
            | _ => none
        let decNode : ReasonNode := {
          id := te.pp, kind := "decision", status := s!"lawful={lTri.asString}, valid={vTri.asString}",
          spans := tspec.spans, detail := s!"server-evaluated at time={state.time}",
          children := pNodes.map (·.id)
        }
        { subject := te.pp, lawful := lTri, valid := vTri, unmetEvidence := unmetMeta, nodes := decNode :: pNodes }
      | .fact fs =>
        let st := if fs.evidenced then state.evidenceStatus te
                  else if state.holds te then .established else .refuted
        let tri := TriBool.ofEvidenceStatus st
        let srcs := state.evidenceSources te
        let det := if srcs.isEmpty then "state lookup"
          else ", ".intercalate (srcs.map fun (k, s, n) => s!"{k} by {showString s} @step{n}")
        { subject := te.pp, lawful := tri, valid := tri,
          nodes := [{ id := te.pp, kind := if fs.evidenced then "evidence" else "fact",
                      status := st.asString, spans := tspec.spans,
                      confidential := fs.confidential, allowedAudiences := fs.audiences, detail := det }] }
      | _ =>
        let h := state.holds te
        { subject := te.pp, lawful := TriBool.ofBool h, valid := TriBool.ofBool h }
  .ok (rawRg.redactForAudience audience?)

/-- `certificate-at-office` (`2026-10-22-redesign.md` §3a & §5.5, `D11`, `D27`, `T24`):
Installs a successor `Artifact` via an `Amend` act ONLY if:
1. The successor `Artifact` passes `verifyArtifactJson` (SHA-256 + HMAC certificate + `WellFormed`);
2. Executing `amendActName(amendArgs)` under the **current** law yields `Allow` (`lawful = yes, valid = yes`,
   respecting quorums, timelocks, and active reflexive `Immunity ... Against Amend` ratchets);
3. Every `Entrenched Invariant` and entrenchment `Immunity` of the current law is preserved
   intact in the successor `Spec` (preserving already-accrued non-derived state entries, `T23`). -/
def installCertifiedAmendment (secretKey : String) (curCfg : Config)
    (amendActName : DomId) (amendArgs : List Elem) (successorArtifactRaw : String) :
    Except String (Artifact.VerifiedArtifact × Config) := do
  -- 1. Verify successor artifact certificate & SHA-256 BEFORE taking office!
  let verifiedNew ← Artifact.verifyArtifactJson successorArtifactRaw secretKey
  -- 2. Verify `amendActName` is a declared `Amend` act and evaluates to `Allow` under current law
  match curCfg.spec.findDecl amendActName with
  | some { kind := .act a, .. } =>
    if !a.isAmend then
      .error s!"`{amendActName}` is not an `Amend` act"
  | _ => .error s!"undeclared `Amend` act `{amendActName}`"
  let dec ← evaluateServerEvent curCfg (.triggerAct amendActName amendArgs) false
  if dec.outcome != "Allow" then
    .error s!"Amend `{amendActName}` refused under current law: outcome={dec.outcome} (lawful={dec.lawful.asString}, valid={dec.valid.asString})"
  -- 3. Verify successor `Spec` preserves all entrenched invariants and entrenchment immunities (`T24`)
  let newSpec := verifiedNew.genesisConfig.spec
  let entrenchedIds := (curCfg.spec.entrenchedInvariants ++
    curCfg.spec.decls.filterMap fun (d, t) =>
      match t.kind with
      | .immunity im => if im.against.contains "Amend" || !im.protects.isEmpty then some d else none
      | _ => none).eraseDups
  for eid in entrenchedIds do
    match curCfg.spec.lookupDecl eid, newSpec.lookupDecl eid with
    | some ot, some nt =>
      if reprStr { ot with spans := [] } != reprStr { nt with spans := [] } then
        .error s!"certificate-at-office refused: successor artifact sha256:{verifiedNew.artifactSha256} modifies entrenched protection `{eid}`"
    | some _, none =>
      .error s!"certificate-at-office refused: successor artifact sha256:{verifiedNew.artifactSha256} removes entrenched protection `{eid}`"
    | _, _ => pure ()
  -- 4. Preserve already-accrued non-derived state (`T23`), run any `Migrates` effects (`#71`),
  --    and verify all `Entrenched Invariant`s on the migrated state before committing!
  let newStrata := verifiedNew.genesisConfig.strata
  let newSpecIdx := newSpec.buildIndex
  let stateRebased := { curCfg.state with step := curCfg.state.step + 1 }.rebase
  let migEffs := ((curCfg.spec.amendMigrations.find? (·.1 == amendActName)).map (·.2) |>.getD []) ++
                 ((newSpec.amendMigrations.find? (·.1 == amendActName)).map (·.2) |>.getD [])
  let stateMigrated ← match Interp.runAmendMigrations newSpec newSpecIdx migEffs stateRebased with
    | .ok st => .ok st
    | .error e => .error s!"amendment migration failed: {e.message}"
  let nextState ← match Saturate.rebaseAndSatWithIdx newSpec newSpecIdx newStrata stateMigrated with
    | .ok st => .ok st
    | .error e => .error s!"successor saturation failed: {e.message}"
  match Interp.checkInvariants newSpec newSpecIdx nextState with
  | .error e => .error s!"successor invariant evaluation failed: {e.message}"
  | .ok invViol =>
    if let some badInv := invViol.find? newSpec.entrenchedInvariants.contains then
      .error s!"CHR051: amendment migration violated entrenched invariant `{badInv}`; amendment rejected"
  let nextCfg : Config := {
    spec := newSpec
    strata := newStrata
    state := nextState
    violatedDuties := curCfg.violatedDuties
    lawVersion := curCfg.lawVersion + 1
  }
  .ok (verifiedNew, nextCfg)

/-- Enforcement coverage manifest (`docs/rfc.md` §8.7): discloses mediated powers vs. physical acts. -/
def coverageManifestJson (institutionId lawHash : String) (spec : Spec) : Json :=
  let powers := spec.decls.filterMap fun (d, t) =>
    match t.kind with | .act a => (if a.isPower && !a.physical then some d else none) | _ => none
  let physicalActs := spec.decls.filterMap fun (d, t) =>
    match t.kind with | .act a => (if a.physical then some d else none) | _ => none
  let evidencedFacts := spec.decls.filterMap fun (d, t) =>
    if t.isEvidencedFact then some d else none
  Json.mkObj [
    ("institutionId", Json.str institutionId),
    ("lawHash", Json.str lawHash),
    ("mediatedPowers", Json.arr (powers.map Json.str).toArray),
    ("observedPhysicalActs", Json.arr (physicalActs.map Json.str).toArray),
    ("evidencedExternalFacts", Json.arr (evidencedFacts.map Json.str).toArray),
    ("trustQualifications", Json.arr #[
      Json.str "Physical/unmediated external conduct cannot be prevented a priori; it is recorded via ObserveExternal and governed by reporting duties and findings.",
      Json.str "Side-effecting capabilities require gateway enforcement of short-lived AuthorizationTokens."
    ])
  ]

/-- Evaluate an instance `d(args)` into `Tagged` inside `charter-server` without source parsing. -/
def evalServerInstance (cfg : Config) (d : DomId) (args : List Elem) : Except String Tagged := do
  let tm ← buildInstanceTerm cfg.spec d args
  let ctx := Ctx.of cfg.spec cfg.state
  match (M.whenTagged (M.eval M.fuel tm) pure).run ctx [] with
  | .ok (te :: _) => .ok te
  | .ok [] => .error s!"`{d}` produced no instance"
  | .error e => .error e.message

def serverInputSchemaJson (spec : Spec) : Json :=
  let schemas := Plan.extractInputSchemas spec
  Json.arr (schemas.map fun s =>
    Json.mkObj [
      ("name", Json.str s.name),
      ("inputKind", Json.str s.inputKind),
      ("confidential", Json.bool s.confidential),
      ("audiences", Json.arr (s.audiences.map Json.str).toArray),
      ("components", Json.arr (s.components.map fun c =>
        Json.mkObj [
          ("param", Json.str c.paramName),
          ("domain", Json.str c.domName),
          ("kind", Json.str c.domKind),
          ("choices", Json.arr (c.choices.map Json.str).toArray)
        ]).toArray)
    ]).toArray

def serverInspectInputsJson (cfg : Config) (action : DomId) (args : List Elem) : Except String Plan.MissingActInputs := do
  checkExposedAct cfg.spec action
  let te ← evalServerInstance cfg action args
  .ok (Plan.inspectMissingInputs cfg te)

def serverPlanJson (cfg : Config) (action : DomId) (args : List Elem) (maxDepth : Nat) : Except String Json := do
  checkExposedAct cfg.spec action
  let te ← evalServerInstance cfg action args
  let res := Plan.findShortestPlan cfg te maxDepth 600 []
  let stepToJson : Plan.PlanStep → Json
    | .act actor sTe =>
      Json.mkObj [("kind", Json.str "act"), ("actor", Json.str actor), ("instance", Json.str sTe.pp)]
    | .wait t dlt =>
      Json.mkObj [("kind", Json.str "wait"), ("targetTime", Json.num t), ("delta", Json.num dlt)]
  match res with
  | .alreadyEnabled =>
    .ok (Json.mkObj [
      ("target", Json.str te.pp),
      ("status", Json.str "AlreadyEnabled"),
      ("planFound", Json.bool true),
      ("steps", Json.arr #[]),
      ("visitedStates", Json.num 1)
    ])
  | .found steps vis =>
    .ok (Json.mkObj [
      ("target", Json.str te.pp),
      ("status", Json.str "PlanFound"),
      ("planFound", Json.bool true),
      ("steps", Json.arr (steps.map stepToJson).toArray),
      ("visitedStates", Json.num vis)
    ])
  | .unreachable vis bnd =>
    .ok (Json.mkObj [
      ("target", Json.str te.pp),
      ("status", Json.str "Unreachable"),
      ("planFound", Json.bool false),
      ("steps", Json.arr #[]),
      ("visitedStates", Json.num vis),
      ("maxDepth", Json.num bnd)
    ])

end Charter.Server
