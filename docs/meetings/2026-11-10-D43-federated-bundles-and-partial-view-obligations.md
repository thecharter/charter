# D43 — Federated Action-Carried Justification Bundles, Audience-Bounded Sharing, Redacted Attestations, and Partial-View Obligation Safety

**Laws:** 1, 2, 3, 6, 7, 9, 10, 11, 13, 14 (`docs/mission.md`). Brief `B30` (`2026-11-10-briefs-for-ruling.md`).
**Date:** 2026-11-10
**Status:** ruled as predicted (Eric, 2026-11-10)

## Context

In inter-organizational settings where independent parties cannot synchronize all institutional state globally or publish confidential sub-policies onto a shared ledger, actors need a way to carry self-contained proof bundles with their actions while keeping underlying obligations, deadlines, revocations, and confidentiality protections intact. Esterhuyse, Müller, and van Binsbergen's *JustAct* framework (*Logical Methods in Computer Science*, 22:3, Sept. 2026) demonstrates how separating synchronized agreements (`agreed`) from peer-authored statements (`stated`) carried inside closed action payloads (`payload(a)`) yields monotone auditability as network history grows, while highlighting natural directions for further work around verified policy evaluation, dynamic obligations under partial views, confidential statement forwarding, payload redaction, and automated justification synthesis.

## Ruling (`D43`, `018.2`, `018.5`)

1. **Zero duplicate surface syntax (`Law 13`):** No new `.charter` keywords are introduced. Actor-scoped open/input facts, `Evidenced` + `Confidential To` propositions (`D22`), Schnorr per-actor signatures (`#76`), and `Due within d After ev` notice-gated deadlines (`009.4`, `D38`) already express the institutional rules.
2. **Operator-blind federated bundle layer (`src/Charter/Server/Bundles.lean`):** Integrated directly over `Charter.Eval` (`M.evalActTri` / `semPhrase`, proved sound and complete against `Charter.Core.Meaning` in `D41`) with zero `Surface/`, `Resolve/`, or `Prove/` dependencies (`test/gates/operator-blind.sh`), providing:
   - **Authorship reflection (`reflectAuthor_no_impersonation`):** A Schnorr-verified `SignedStatement` authored by `α` may only supply open/input facts whose leading actor component equals `α` or tender `Evidenced` items with `issuer = α`, never impersonating another actor or overriding closed constitutional rules.
   - **End-to-end monotone auditability (`persist_permitted_bundle`):** Evaluates Charter's three answers (`occurred`, `lawful`, `valid`, `Law 2`) plus enumerated `effectsOf` capability tokens on the closed bundle state and proves over the live evaluator that any valid, unrevoked bundle remains identically permitted across growing network histories (`net₁.stated ⊆ net₂.stated`, `net₁.enacted ⊆ net₂.enacted`).
   - **Per-statement revocation (`revocation_invalidates_bundle`, `unrelated_revocation_preserves_bundle`):** Author-signed revocations (`revokedIds`) and `expiresAt` bounds retire individual delegations without disturbing active agreements or unrelated bundles.
   - **Audience-bounded sharing (`public_gossip_always_lawful`, `restricted_leak_detected_and_unusable`):** `.unrestricted` statements propagate freely with zero communication overhead; forwarding `.restricted` statements outside their permitted audience (absent an author disclosure grant) still occurs (`Law 1`), records an explicit `CommViolation` (`Law 2`, `Law 3`), and confers no standing in `verifyBundle`.
   - **Commitment-bound redacted attestations (`redacted_bundle_agrees_with_unredacted`):** `RedactedAttestation`s carry the SHA-256 commitment of a private `SignedStatement` plus an authorized auditor/enclave Schnorr signature exporting only non-confidential interface facts, preserving identical `(lawful, valid)` verdicts on non-confidential acts without exposing `Confidential` facts.
   - **Dependency-sliced bundle synthesis (`synthesizeBundle_sound`):** Selects a minimal valid statement subset from a candidate pool, discarding irrelevant or conflicting statements.
   - **Partial-view obligation safety (`unnoticed_duty_never_violated`):** Proves directly over `M.eval` that an unacknowledged notice-gated `Duty` (`Due within d After notice`) evaluates to `false` at every clock instant until notice is established.
3. **CLI, server, and standard library (`src/Charter/Cli/Bundle.lean`, `src/Charter/Server/Api.lean`, `lib/federated_mandate.charter`):** Exposed via `charter bundle <sign|verify|synthesize|inspect|self-test>`, `charter-server` (`SignStatement`, `RevokeStatement`, `SynthesizeBundle`, `VerifyBundle`, `EnactBundle`), and reusable module `lib/federated_mandate.charter` (`test/lib/federated_mandate_test.charter`).

## Cost Accepted & Reopens If

- **Cost accepted:** Redacted bundle privacy relies on an authorized auditor/enclave Schnorr attestation over the SHA-256 statement commitment rather than an embedded SNARK circuit; cryptographic zero-knowledge proving of `M.eval` remains external substrate territory.
- **Reopens if:** Inter-institution federation requires peer statements to carry non-ground rule schemas rather than actor-attributed ground facts, delegations, and evidence tenders.
