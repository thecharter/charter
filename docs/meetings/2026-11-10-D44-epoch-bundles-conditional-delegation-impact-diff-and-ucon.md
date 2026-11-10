# D44 — Epoch-Versioned & Replay-Safe Bundles, Scoped Conditional Delegations, Change-Impact Diffing, Stakeholder Duty Deltas, `UCON` Mid-Saga Re-Verification, and Branching `repl`

**Laws:** 1, 2, 3, 5, 6, 8, 9, 10, 11, 12, 13, 14 (`docs/mission.md`). Brief `B32` (`2026-11-10-briefs-for-ruling.md`). Sharpens `D25`, `D27`, and `D43`.
**Date:** 2026-11-10
**Status:** ruled as predicted (Eric, 2026-11-10)

## Context

A comprehensive pass across the three Amsterdam normative-systems papers (`eflint.pdf` GPCE 2020, `eflint-reflections.pdf` 2022, and `justact.pdf` LMCS Sept. 2026) surfaced six cohesive extensions where Charter's runtime, tooling, and federated bundle layer could complete remaining institutional design gaps without introducing a single duplicate `.charter` surface keyword (`Law 13`):
1. Across `AmendLaw` transitions (`justact.pdf` §6.3.5, Theorem 3.19), active law hashes required for *new* `EnactBundle` transitions must be separated from superseded historical law hashes accepted for retroactive `VerifyBundle` audits, while duplicate `bundleId` replays must be rejected and commuting vs. write-conflicting parallel bundles distinguished (`justact.pdf` §8.1);
2. Standing peer delegations (`justact.pdf` §6.3.4–6.3.5) require positive conditional delegation assertions usable while the delegator is offline, without risking Slick's unbounded recursion;
3. Constitutional amendment review (`eflint.pdf` §6, citing *Margrave*) benefits from concrete witness traces showing where `(lawful, valid, violated)` flips between two versions of a program;
4. Ex-ante compliance with positive obligations and actor capability projection (`eflint.pdf` §3.1, `eflint-reflections.pdf` §3.3) benefit from structured holder/claimant `dutyDeltas` on server transitions and an audience-redacted `GetActorBrief` query;
5. Usage Control (`UCON`, `eflint-reflections.pdf` §1, `justact.pdf` §§1–2) requires re-verifying live `Allow` at `Authorize` whenever institutional state has advanced since `Reserve` (e.g., an intervening suspension, revocation, or immunity); and
6. `charter repl` (`Repl.lean`, `.reference/eflint/src/REPL.hs`) deferred interactive history backtracking (`:revert`, `:jump`) and enabled-action/duty listing (`:options`, `:duties`).

## Ruling (`D44`, `018.2`, `018.5`)

1. **Law-epoch separation, replay prevention, & commutativity (`src/Charter/Server/Bundles.lean`, `src/Charter/Core/Derivation.lean`):**
   - `FedNetwork` tracks `agreedLaws` (currently active law bases accepted for new enactments) separately from `supersededLaws` (historical law bases retired by `AmendLaw`, accepted by `verifyBundleAudit` / `VerifyBundle` with `auditHistorical: true`, rejected by `EnactBundle`: `superseded_law_cannot_enact_new`, `historical_audit_preserves_enacted`).
   - `freshBundle` rejects duplicate `bundleId` replays (`replay_bundle_rejected`).
   - `bundlesCommute` reuses `Charter.Stratify`'s single-owner static read/write footprint analysis (`actReadTypes`, `actWriteTypes`) to report when two bundles commute safely for parallel federated enactment.
2. **Scoped conditional delegation (`StatementAssertion.delegateWhen`):**
   - Allows `author` to sign a positive conditional assertion `delegateWhen headFact headArgs guardFacts` whose `headArgs` enforces mandatory leading-author reflection (`hasLeadingAuthor author headArgs`) and whose `guardFacts` must all hold in the extracted bundle configuration before `headFact(headArgs)` is asserted, preserving `reflectAuthor_no_impersonation` and structural termination.
3. **Counterexample-generating change-impact analysis (`charter diff --impact`, `src/Charter/Project/Diff.lean`):**
   - Explores reachable configurations over the cone-of-influence of modified declarations (`Prove.Slice` + `Verify.Explorer`) and emits minimal witness traces where `(lawful, valid, violated)` differs between `old` and `new`.
4. **Stakeholder `dutyDeltas` & `GetActorBrief` (`src/Charter/Server/Protocol.lean`, `src/Charter/Server/Api.lean`):**
   - Every state-advancing `charter-server` transition computes and emits structured `dutyDeltas` (`created`, `late`, `fulfilled`, `violated`, naming `duty`, `holder`, `claimant`, and `dueAt`), and `GetActorBrief` returns an audience-redacted capability/obligation snapshot for any named actor.
5. **Ongoing `UCON` guard re-verification on `Authorize` (`src/Charter/Server/Api.lean`):**
   - Whenever `rt.seqNo > r.stateVersion` on an un-authorized reservation, `Authorize` re-evaluates `evaluateServerEvent rt.config (.triggerAct r.action r.args) false` and rejects token minting (marking the reservation `.rejected`) if an intervening state transition rendered the reserved act non-`Allow`.
6. **Branching exploration in `charter repl` (`src/Charter/Cli/Repl.lean`):**
   - Maintains the indexed `[Config]` history stack and supports `:options` (`:o`), `:duties`, `:history`, `:revert` (`:r`), and `:jump <n>` (`:j <n>`).

## Cost Accepted & Reopens If

- **Cost accepted:** `delegateWhen` guards are ground positive fact conjunctions rather than arbitrary open variables or negated rule schemas, keeping termination trivial and avoiding unstratified peer-injected cycles.
- **Reopens if:** Federated standing mandates require bounded schematic quantification over finite closed domains inside signed statements.
