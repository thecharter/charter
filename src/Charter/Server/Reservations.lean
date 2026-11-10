import Charter.Server.StateStore

/-!
# Charter.Server.Reservations — `Reserve` → `Authorize` → `ConfirmExecution` / `ExecutedUnknown` Saga (`G4.3`, `T09`, `T34`, `T35`)

Implements Charter's two-phase external side-effect enforcement saga (`docs/rfc.md` §8.3, §11.4):
```
Proposed -> Evaluated -> Reserved -> Authorized ->
  {ExecutedConfirmed, ExecutedUnknown, ExpiredUnused, Rejected}
```
1. **Serializable `Reserve` (`T09`)**: locks `(resourceKey, amount)` against `cap` with mandatory
   `expiresAt`, keyed idempotently by `(institutionId, intentId)`.
2. **Idempotent `Authorize` + short-lived HMAC `AuthorizationToken` (`T34`)**: binds
   `(institutionId, lawHash, stateVersion, reservationId, intentId, actor, action, argsDigest, maxAmount, nonce, expiresAt)`;
   re-issuing on the same active `intentId` returns the existing token without minting a second
   capability; stale `stateVersion`, expired tokens, and consumed nonces are rejected.
3. **`ExecutedUnknown` crash/timeout safety (`T35`)**: when external gateway execution times out
   or crashes before receipt (`"timeout_unknown"`), the reservation enters `ExecutedUnknown`
   (`PendingExternalOutcome`): reserved collateral/capacity is **NOT** automatically released,
   and duplicate `Authorize` / repeat payment is **blocked** until explicit `ReconcileExecution`.
-/

namespace Charter.Server

open Lean (Json ToJson FromJson toJson fromJson?)

inductive SagaStatus where
  | reserved
  | authorized
  | executedConfirmed
  | executedUnknown
  | expiredUnused
  | rejected
  deriving Repr, DecidableEq, BEq, ToJson, FromJson

def SagaStatus.asString : SagaStatus → String
  | .reserved          => "Reserved"
  | .authorized        => "Authorized"
  | .executedConfirmed => "ExecutedConfirmed"
  | .executedUnknown   => "ExecutedUnknown"
  | .expiredUnused     => "ExpiredUnused"
  | .rejected          => "Rejected"

/-- Whether a reservation still holds locked capacity (`Reserved`, `Authorized`, or `ExecutedUnknown`!). -/
def SagaStatus.locksCapacity : SagaStatus → Bool
  | .reserved | .authorized | .executedUnknown => true
  | .executedConfirmed | .expiredUnused | .rejected => false

/-- Short-lived least-privilege execution capability token (`docs/rfc.md` §8.3, `T34`). -/
structure AuthorizationToken where
  institutionId : String
  lawHash       : String
  stateVersion  : Nat
  reservationId : String
  intentId      : String
  actor         : String
  action        : DomId
  argsDigest    : String
  maxAmount     : Int
  nonce         : String
  expiresAt     : Int
  signatureHex  : String
  deriving Repr, DecidableEq, ToJson, FromJson

def computeTokenSig (secretKey : String) (tok : AuthorizationToken) : String :=
  let msg := s!"charter-tok-v1|{tok.institutionId}|{tok.lawHash}|{tok.stateVersion}|{tok.reservationId}|{tok.intentId}|{tok.actor}|{tok.action}|{tok.argsDigest}|{tok.maxAmount}|{tok.nonce}|{tok.expiresAt}"
  Artifact.hmacSha256 secretKey msg

def mintToken (secretKey : String) (institutionId lawHash : String) (stateVersion : Nat)
    (reservationId intentId actor : String) (action : DomId) (args : List Elem)
    (maxAmount expiresAt : Int) : AuthorizationToken :=
  let argsDigest := Artifact.sha256String (toJson args).compress
  let nonce := "nonce:" ++ (Artifact.sha256String s!"{institutionId}:{intentId}:{reservationId}:{stateVersion}").take 24
  let unsigned : AuthorizationToken := {
    institutionId, lawHash, stateVersion, reservationId, intentId,
    actor, action, argsDigest, maxAmount, nonce, expiresAt, signatureHex := ""
  }
  { unsigned with signatureHex := computeTokenSig secretKey unsigned }

structure ReservationRecord where
  reservationId : String
  intentId      : String
  actor         : String
  action        : DomId
  args          : List Elem
  resourceKey   : String
  amount        : Int
  createdAt     : Int
  expiresAt     : Int
  stateVersion  : Nat
  status        : SagaStatus
  token         : Option AuthorizationToken := none
  receiptRef    : Option String := none
  deriving Repr, ToJson, FromJson

structure ReservationTable where
  records        : List ReservationRecord := []
  consumedNonces : List String := []
  committedDraws : List (String × Int) := [] -- `(resourceKey, settledAmount)`
  deriving Repr, ToJson, FromJson

/-- Expire `Reserved` or `Authorized` locks whose `expiresAt ≤ now`, while NEVER auto-expiring
`ExecutedUnknown` (`T35`: uncertain external side effects stay locked until reconciled!). -/
def expireStaleReservations (now : Int) (tbl : ReservationTable) : ReservationTable :=
  let recs' := tbl.records.map fun r =>
    match r.status with
    | .reserved | .authorized =>
      if r.expiresAt ≤ now then { r with status := .expiredUnused } else r
    | _ => r
  { tbl with records := recs' }

/-- Currently locked + committed draw total against `resourceKey` (`T09`). -/
def usedResourceCapacity (tbl : ReservationTable) (resourceKey : String) : Int :=
  let locked := (tbl.records.filter fun r => r.resourceKey == resourceKey && r.status.locksCapacity)
    |>.foldl (fun acc r => acc + r.amount) 0
  let settled := (tbl.committedDraws.filter (·.1 == resourceKey))
    |>.foldl (fun acc p => acc + p.2) 0
  locked + settled

/-- `T35` theorem: `expireStaleReservations` never changes an `.executedUnknown` record's status
or releases its locked capacity. -/
theorem executedUnknown_never_auto_released (now : Int) (r : ReservationRecord)
    (hUnk : r.status = .executedUnknown) :
    (match r.status with
     | .reserved | .authorized => if r.expiresAt ≤ now then { r with status := .expiredUnused } else r
     | _ => r).status.locksCapacity = true := by
  cases h : r.status <;> rw [h] at hUnk <;> cases hUnk
  dsimp only
  rw [h]
  rfl

/-- `Reserve`: idempotent on `intentId`; serializes concurrent draws against `resourceCap?` (`T09`). -/
def reserveIntent (tbl0 : ReservationTable) (institutionId : String) (now : Int)
    (stateVersion : Nat) (expectedVersion? : Option Nat)
    (intentId actor : String) (action : DomId) (args : List Elem)
    (resourceKey : String) (amount : Int) (resourceCap? : Option Int)
    (ttl : Int) : Except String (ReservationTable × ReservationRecord) := do
  if ttl ≤ 0 then
    .error "provisional hold / reservation requires a positive expiry TTL (§8.4)"
  let tbl := expireStaleReservations now tbl0
  if let some wantVer := expectedVersion? then
    if wantVer != stateVersion then
      .error s!"stateVersion CAS conflict: expected {wantVer}, current {stateVersion}"
  -- Idempotent lookup by `intentId`
  match tbl.records.find? (·.intentId == intentId) with
  | some existing =>
    match existing.status with
    | .reserved | .authorized => .ok (tbl, existing)
    | .executedConfirmed => .error s!"intent `{intentId}` is already ExecutedConfirmed (duplicate execution refused)"
    | .executedUnknown => .error s!"intent `{intentId}` is in ExecutedUnknown (PendingExternalOutcome; reconcile before retrying, T35)"
    | .expiredUnused | .rejected => .error s!"intent `{intentId}` expired or was rejected; submit a fresh intentId"
  | none =>
    if let some cap := resourceCap? then
      let used := usedResourceCapacity tbl resourceKey
      if used + amount > cap then
        .error s!"Deny: insufficient unreserved capacity on `{resourceKey}` (used/locked={used}, requested={amount}, cap={cap}, T09)"
    let resId := "res:" ++ (Artifact.sha256String s!"{institutionId}:{intentId}:{now}:{tbl.records.length}").take 20
    let recNew : ReservationRecord := {
      reservationId := resId, intentId, actor, action, args,
      resourceKey, amount, createdAt := now, expiresAt := now + ttl,
      stateVersion, status := .reserved
    }
    .ok ({ tbl with records := tbl.records ++ [recNew] }, recNew)

/-- `Authorize`: mints (or idempotently returns) a short-lived capability token after verifying
`Allow` under the active law (`T34`). -/
def authorizeReservation (secretKey : String) (tbl0 : ReservationTable)
    (institutionId lawHash : String) (now : Int) (curStateVersion : Nat)
    (intentId : String) : Except String (ReservationTable × AuthorizationToken) := do
  let tbl := expireStaleReservations now tbl0
  match tbl.records.find? (·.intentId == intentId) with
  | none => .error s!"no active reservation for intentId `{intentId}`"
  | some r =>
    match r.status with
    | .authorized =>
      match r.token with
      | some tok =>
        if tbl.consumedNonces.contains tok.nonce then
          .error s!"token nonce `{tok.nonce}` already consumed (T34)"
        else .ok (tbl, tok)
      | none => .error "internal error: Authorized record missing token"
    | .executedUnknown =>
      .error s!"intent `{intentId}` is in ExecutedUnknown (PendingExternalOutcome); duplicate authorization refused (T35)"
    | .executedConfirmed =>
      .error s!"intent `{intentId}` already ExecutedConfirmed; replay refused (T34)"
    | .expiredUnused =>
      .error s!"reservation `{r.reservationId}` expired at {r.expiresAt}; stale authorization refused (T34)"
    | .rejected =>
      .error s!"reservation `{r.reservationId}` was rejected"
    | .reserved =>
      if r.stateVersion != curStateVersion then
        .error s!"stale reservation version ({r.stateVersion} != current {curStateVersion}); re-evaluate and reserve against current state (T34)"
      let tok := mintToken secretKey institutionId lawHash curStateVersion
        r.reservationId r.intentId r.actor r.action r.args r.amount r.expiresAt
      let recs' := tbl.records.map fun q =>
        if q.intentId == intentId then { q with status := .authorized, token := some tok } else q
      .ok ({ tbl with records := recs' }, tok)

/-- Reject an unconfirmed reservation mid-saga when an ongoing `UCON` precondition ceases to hold (`D44`). -/
def rejectReservation (tbl : ReservationTable) (intentId : String) : ReservationTable :=
  { tbl with records := tbl.records.map fun q =>
      if q.intentId == intentId && (q.status == .reserved || q.status == .authorized) then
        { q with status := .rejected, token := none }
      else q }

/-- Verify a presented `AuthorizationToken` before settling or confirming execution (`T34`). -/
def verifyPresentedToken (secretKey : String) (tbl : ReservationTable)
    (institutionId lawHash : String) (now : Int) (tok : AuthorizationToken) : Except String ReservationRecord := do
  let wantSig := computeTokenSig secretKey tok
  if tok.signatureHex != wantSig then
    .error "authorization token HMAC signature invalid"
  if tok.institutionId != institutionId then
    .error s!"cross-tenant token rejected: token institution `{tok.institutionId}` != `{institutionId}`"
  if tok.lawHash != lawHash then
    .error s!"stale lawHash on authorization token (`{tok.lawHash}` != active `{lawHash}`)"
  if tok.expiresAt ≤ now then
    .error s!"authorization token expired at {tok.expiresAt} (now={now}, T34)"
  if tbl.consumedNonces.contains tok.nonce then
    .error s!"replay rejected: authorization token nonce `{tok.nonce}` already consumed (T34)"
  match tbl.records.find? (·.intentId == tok.intentId) with
  | none => .error s!"unknown intentId `{tok.intentId}`"
  | some r =>
    if r.status != .authorized then
      .error s!"reservation `{r.reservationId}` is in state `{r.status.asString}`, expected `Authorized`"
    .ok r

/-- `ConfirmExecution`: either commits external execution (`"confirmed"`) or enters
`ExecutedUnknown` (`"timeout_unknown"`) on gateway/network crash (`T35`). -/
def confirmExecution (secretKey : String) (tbl0 : ReservationTable)
    (institutionId lawHash : String) (now : Int)
    (tok : AuthorizationToken) (executionStatus : String) (receiptRef : Option String := none) :
    Except String (ReservationTable × SagaStatus × ReservationRecord) := do
  let tbl := expireStaleReservations now tbl0
  let r ← verifyPresentedToken secretKey tbl institutionId lawHash now tok
  match executionStatus with
  | "confirmed" =>
    let recs' := tbl.records.map fun q =>
      if q.intentId == tok.intentId then { q with status := .executedConfirmed, receiptRef } else q
    let draws' := if !r.resourceKey.isEmpty && r.amount > 0 then tbl.committedDraws ++ [(r.resourceKey, r.amount)]
                  else tbl.committedDraws
    let tbl' : ReservationTable := {
      records := recs'
      consumedNonces := tbl.consumedNonces ++ [tok.nonce]
      committedDraws := draws'
    }
    .ok (tbl', .executedConfirmed, { r with status := .executedConfirmed, receiptRef })
  | "timeout_unknown" =>
    -- Crash / network timeout after gateway dispatch (`T35`): consume nonce so token cannot be
    -- re-submitted blindly, keep capacity LOCKED under `.executedUnknown`, and require reconciliation!
    let recs' := tbl.records.map fun q =>
      if q.intentId == tok.intentId then { q with status := .executedUnknown, receiptRef } else q
    let tbl' : ReservationTable := {
      tbl with
      records := recs'
      consumedNonces := tbl.consumedNonces ++ [tok.nonce]
    }
    .ok (tbl', .executedUnknown, { r with status := .executedUnknown, receiptRef })
  | other =>
    .error s!"unknown ConfirmExecution status `{other}` (expected `confirmed` or `timeout_unknown`)"

/-- Explicit replay-safe reconciliation of an `ExecutedUnknown` saga (`T35`):
- `observedExecuted = true` -> commits the draw and settles to `ExecutedConfirmed`;
- `observedExecuted = false` -> verified non-execution receipt releases the locked capacity (`Rejected`). -/
def reconcileUnknown (tbl : ReservationTable) (intentId : String)
    (observedExecuted : Bool) (receiptRef : String) : Except String (ReservationTable × ReservationRecord) := do
  match tbl.records.find? (·.intentId == intentId) with
  | none => .error s!"unknown intentId `{intentId}`"
  | some r =>
    if r.status != .executedUnknown then
      .error s!"intent `{intentId}` has status `{r.status.asString}`; ReconcileExecution applies only to `ExecutedUnknown`"
    let nextStatus : SagaStatus := if observedExecuted then .executedConfirmed else .rejected
    let recs' := tbl.records.map fun q =>
      if q.intentId == intentId then { q with status := nextStatus, receiptRef := some receiptRef } else q
    let draws' := if observedExecuted && !r.resourceKey.isEmpty && r.amount > 0 then
                    tbl.committedDraws ++ [(r.resourceKey, r.amount)]
                  else tbl.committedDraws
    .ok ({ tbl with records := recs', committedDraws := draws' }, { r with status := nextStatus, receiptRef := some receiptRef })

end Charter.Server
