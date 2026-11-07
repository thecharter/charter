# D27 — Signed content-addressed `Artifact` bundles (`B10`), operator-blind `charter-server`, and `ExecutedUnknown` saga (`T09`, `T34`–`T36`)

**Laws:** 1, 2, 6, 7, 9, 10, 11, 14 (`docs/mission.md`). Resolves Brief `B10`.
**Date:** 2026-11-06
**Status:** ruled (Eric, `2026-10-22-redesign.md` §3a, `docs/rfc.md` §8, §18.3)

## Ruling
1. **Operator-blind `Artifact` & `B10` certificate verification (`G4.1`)**:
   - `charter build <file.charter> -o <file.artifact> [--sign-key <key>] [--key-id <id>]` serializes the elaborated `CIR` (`Spec` + genesis `CPhrase`s), multi-document `SourceManifest`, and assurance summary into canonical JSON committed under `artifactSha256`, signed with pure-Lean RFC 2104 HMAC-SHA256 (`ArtifactSignature`, verified against RFC 4231 test vectors via `rfl` in `Artifact/Hash.lean`).
   - `charter-server` (`src/Server.lean`) links `Charter.Core.*`, `Charter.Eval.{Eval,Step}`, `Charter.Artifact.{Hash,Cert,Runtime}`, and `Charter.Server.*` **only** — zero modules from `Surface/`, `Resolve/`, or `Prove/` (`test/gates/operator-blind.sh`).
   - On startup (`verify`, `replay`, `serve`) and on every runtime `AmendLaw` transition (`test/gates/certificate-at-office.sh`), `charter-server` recomputes `artifactSha256`, verifies the cryptographic signature against its configured key policy, and runs `Spec.checkWellFormed` + `Stratify.strata` before any law version takes office.
2. **Hash-chained durable log, canonical state roots, & offline `Replay` (`G4.2`, `T36`)**:
   - Every committed server transition appends a hash-chained JSONL `LogEntry` (`seqNo`, `prevEntryHash`, `lawHash`, `lawVersion`, `event`, `outcome`, `lawful`, `valid`, `stateRootAfter`, `entryHash`, `signature`).
   - `charter-server replay <artifact> <log>` recomputes every transition from genesis through the single proved `Charter.Eval` engine and verifies byte-identical verdicts and `stateRootAfter` digests (`test/gates/replay.sh`).
3. **Two-phase `Reserve` → `Authorize` → `ConfirmExecution` / `ExecutedUnknown` saga (`G4.3`–`G4.5`, `T09`, `T34`, `T35`)**:
   - `Reserve` acquires a serializable capacity/intent lock with mandatory expiry (`T09`).
   - `Authorize` issues a short-lived signed capability token bound to `(institutionId, lawHash, stateVersion, reservationId, intentId, actor, action, argsDigest, maxAmount, nonce, expiresAt)`, idempotent on `intentId` and rejecting stale or replayed tokens (`T34`).
   - Network/gateway timeouts transition the reservation to `ExecutedUnknown` (`PendingExternalOutcome`), holding reserved capacity and blocking duplicate authorization until explicit `ReconcileExecution` (`T35`).

## Context
Resolves open brief `B10` (`2026-10-23-briefs-for-ruling.md`) and implements `2026-10-22-redesign.md` §3a and `docs/rfc.md` §8.

## Mission fit
`Law 9` (compiler and `charter-server` execute the exact same `Eval` definitions), `Law 10` (pure-Lean kernel-verified SHA-256 and HMAC-SHA256 in TCB), `Law 11` (zero engine names in server protocol or CLI), `Law 14` (`operator-blind`, `replay`, `certificate-at-office` gates).

## Cost accepted
Compiled `CIR` (`Spec` + `CPhrase`s) is serialized structurally inside `.artifact` bundles so `charter-server` never parses `.charter` source text.

## Reopens if
Hardware HSM PKCS#11 / detached multi-party threshold Ed25519 cosigning is added for federated multi-operator consensus.
