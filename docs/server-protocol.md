# Charter Server & Enforcement Protocol Specification (`G4`, `D27`)

`charter-server` is Charter's durable, **operator-blind** institutional runtime (`docs/plans/2026-10-22-redesign.md` §3a; `docs/rfc.md` §8). It links `Charter.Core`, `Charter.Eval`, `Charter.Artifact`, and `Charter.Server` **only** — never `Surface/`, `Resolve/`, or `Prove/` (enforced by `test/gates/operator-blind.sh`).

---

## 1. CLI Commands

```
charter-server verify <file.artifact> [--key <secret>]
charter-server replay <file.artifact> <file.log> [--key <secret>]
charter-server serve  <file.artifact> [--log <file.log>] [--snapshot <file.snap>] [--key <secret>] [--institution <id>]
```

---

## 2. Certified `Artifact` Format & `certificate-at-office`

1. `charter build <file.charter> -o <file.artifact> [--sign-key <secret>] [--key-id <id>]` emits:
   - `artifactSha256`: SHA-256 hex digest over canonical compressed `payload` JSON;
   - `certificate`: `{keyId, scheme: "hmac-sha256", signatureHex, wellFormed: true, coverage}`;
   - `payload`: `{formatVersion, languageVersion, sourceManifest, epochs, cirDigest, runtimeCIR}`.
2. Neither initial institution creation nor runtime `AmendLaw` takes office unless:
   - `sha256(payload) == artifactSha256`,
   - `certificate.signatureHex` verifies under the configured signing key,
   - `Spec.checkWellFormed` and `Stratify.strata` succeed on the deserialized `Spec`, and
   - (for `AmendLaw`) the active law's `Amend` act evaluates to `lawful = yes, valid = yes` and all entrenched protections of the predecessor law remain intact (`test/gates/certificate-at-office.sh`).

---

## 3. Preflight-to-Execution Saga & Decision Outcomes

### 3.1 Service Decision Mapping (`docs/rfc.md` §8.4)
Every `Evaluate` and `Authorize` response carries a deterministic service outcome:
- `Allow` — `lawful == yes && valid == yes`, all required evidence established, and reservation capacity available (lawful-action entitlement: never discretionary censorship);
- `Deny` — `lawful == no || valid == no` or insufficient unreserved balance;
- `NeedEvidence` — guard `undetermined` due to `Unresolved` `Evidenced` premise(s);
- `ReferForFinding` — guard `undetermined` due to `Conflicted` `Evidenced` premise(s);
- `Conflict` — active normative conflict between unranked `Default`/`Exception` rules;
- `Unavailable` — operational clock/lock limit reached.

### 3.2 Saga Lifecycle (`T09`, `T34`, `T35`)
```
Proposed -> Evaluated -> Reserved -> Authorized ->
  {ExecutedConfirmed, ExecutedUnknown, ExpiredUnused, Rejected}
```
1. **`Reserve`**: acquires a serializable lock keyed by `(institutionId, intentId)` against `stateVersion` and optional `(resource, amount, cap)` with mandatory `expiresAt` (`T09`).
2. **`Authorize`**: mints a signed, short-lived `AuthorizationToken` bound to `(institutionId, lawHash, stateVersion, reservationId, intentId, actor, action, argsDigest, maxAmount, nonce, expiresAt)`. Retrying `Authorize` with the same `intentId` returns the existing active token idempotently; stale `stateVersion`, expired tokens, or consumed nonces are rejected (`T34`).
3. **`ConfirmExecution`**:
   - `"confirmed"` commits the legal transition to `State` and appends to the hash-chained durable log (`ExecutedConfirmed`).
   - `"timeout_unknown"` transitions the reservation to **`ExecutedUnknown`** (`PendingExternalOutcome`): reserved collateral/capacity stays locked and duplicate authorization is refused until `ReconcileExecution` (`T35`).

---

## 4. JSON-RPC / stdio & MCP Operations (`docs/rfc.md` §8.2)

`charter-server serve` accepts newline-delimited JSON requests (both direct `{"op": "..."}` and MCP `tools/list` / `tools/call` envelopes):
- `GetLaw`, `GetState`, `GetCoverageManifest`
- `Evaluate`, `Reserve`, `Authorize`, `ConfirmExecution`, `ReconcileExecution`
- `ExercisePower`, `ObserveExternal`, `SubmitEvidence`, `AdvanceClock`
- `Explain` (audience-redacted `ReasonGraph`, `T43`), `AmendLaw`, `Replay`
