# Charter Security Model, Threat Matrix, and Enforcement Boundaries (`G4`, `D27`)

This document enumerates the threats, controls, and explicit residual risks of `charter` and `charter-server` (`docs/rfc.md` §8.7, `docs/trust.md`).

---

## 1. Security Boundaries

1. **Operator-Blind Runtime (`test/gates/operator-blind.sh`)**:
   - `charter-server` never parses or compiles `.charter` source code. Its binary contains zero symbols from `Charter.Surface`, `Charter.Resolve`, or `Charter.Prove`.
   - Operators receive only content-addressed, signed `.artifact` bundles (`artifactSha256`).
2. **Cryptographic Integrity & `certificate-at-office` (`test/gates/certificate-at-office.sh`)**:
   - Every `.artifact` bundle is verified by SHA-256 content hash, RFC 2104 HMAC-SHA256 certificate authentication, and runtime `Spec.checkWellFormed` + `Stratify.strata` validation before taking office at genesis or via `AmendLaw`.
3. **Tamper-Evident Hash-Chained Event Log & Offline `Replay` (`test/gates/replay.sh`)**:
   - Every state-mutating server operation appends a `LogEntry` linking `prevEntryHash -> entryHash` with `stateRootAfter` (canonical SHA-256 digest over sorted `State` entries, `time`, `step`, `lawVersion`, and `specSha256`).
   - Any third party can audit a server via `charter-server replay <artifact> <log>` and detect log truncation, insertion, reordering, or verdict tampering (`T36`).

---

## 2. Threat & Mitigation Matrix

| Threat | Prevention & Detection Control | Residual / Declared Qualification |
|---|---|---|
| Tampered or uncertified `.artifact` | SHA-256 payload check + certificate signature check + `checkWellFormed` (`certificate-at-office` gate) | Compromise of offline signing key requires key rotation |
| Concurrent double-draw (`T09`) | Single-writer serializable `Reserve` lock against `balance - reserved` | Applies only to channels mediated by the execution gateway |
| Replay / stale capability token (`T34`) | `AuthorizationToken` binds `(lawHash, stateVersion, intentId, argsDigest, nonce, expiresAt)`; consumed nonces tracked durably | Gateway adapters MUST verify token HMAC and expiry |
| Crash after external transfer (`T35`) | `ExecutedUnknown` (`PendingExternalOutcome`) locks capacity and blocks duplicate authorization until `ReconcileExecution` | Requires external receipt or human/panel reconciliation |
| Confidential evidence leak (`T43`) | Audience-scoped `ReasonGraph.redactForAudience` (`redactForAudience_preserves_verdict`) | Callers must authenticate their audience role to API gateway |
| Unobserved out-of-band physical act | `ObserveExternal` records distinct `(eventTime, observationTime, adjudicationTime)`; reporting duties (`Due within`) detect missing filings | Charter cannot physically prevent unmediated off-system conduct; `GetCoverageManifest` discloses mediated vs. unmediated action classes |
