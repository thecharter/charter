# Briefs for rulings, 2026-11-10 (`B30`–`B31`)

**Status:** both ruled as predicted by Eric on 2026-11-10 (`D43` + PSA Law 6 / Invariant 16 / Adversarial Test 23).

## B30. Federated action-carried justification bundles, authorship reflection, audience-controlled gossip, redacted attestations, and partial-view obligation safety (`D43`, `018.2`, `018.5`, `Law 1`, `Law 2`, `Law 6`, `Law 7`, `Law 9`, `Law 10`, `Law 13`)

- **Ruling (`A`, `D43`):** Add zero-axiom federated justification bundles (`src/Charter/Server/JustAct.lean`, `src/Charter/Cli/Bundle.lean`, `lib/federated_mandate.charter`) directly over Charter's proved evaluator with zero duplicate `.charter` surface syntax (`Law 13`) and zero `Surface/`/`Resolve/`/`Prove/` server dependencies (`operator-blind`):
  1. Schnorr-signed actor-attributed statements (`reflectAuthor_no_impersonation`) and closed-bundle evaluation returning all three institutional answers (`occurred`, `lawful`, `valid`) plus enumerated `effectsOf` capability tokens, proving monotone auditability (`persist_permitted_bundle`) end-to-end without unproved evaluator parameters;
  2. Author-signed per-statement revocation and expiry (`revocation_invalidates_bundle`, `unrelated_revocation_preserves_bundle`) without wiping global agreements;
  3. Audience-controlled statement communication (`public_gossip_always_lawful`, `restricted_leak_detected_and_unusable`) preventing unauthorized recipients from relying on leaked confidential statements without introducing recursive gossip justification overhead;
  4. Commitment-bound `RedactedAttestation`s (`redacted_bundle_agrees_with_unredacted`) hiding `Confidential` facts from counterparties and public verifiers while preserving opening verification for authorized auditors;
  5. Dependency-sliced minimal bundle synthesis (`synthesizeBundle_sound`); and
  6. Partial-view notice safety (`unnoticed_duty_never_violated`) over Charter's `Due within d After ev` (`009.4`).
- **References:** `docs/reference/justact.pdf` (§3.7–3.10, §4.5, §6.3.4–6.3.5, §7.2.1–7.2.4), `.reference/eflint/src/Language/EFLINT/{Spec.hs,Eval.hs}`, `.reference/eflint/src/Server.hs`, `test/eflint-corpus/examples/dex-dipg/scenario1.eflint`, `.reference/symboleo/ide/README.md:45`, `.reference/symboleo/ide/samples/MeatSaleContract.symboleo:33-39`, `.reference/catala/compiler/scopelang/`, `.reference/quint/quint/src/{simulation.ts,verify.ts}`.

## B31. Private mandate bundles, notice-gated procedural obligations, and confidential leak slashing in PSA (`psa.md`, `psa.charter`, `Goal 1`, `Law 3`, `Law 6`, `Law 7`, `Law 8`)

- **Ruling (`A`):** Amend PSA Law 6 (`LAW6.ENTITLE`, `LAW6.APPEAL`), Design Invariant 16, and Adversarial Test 23 in `psa.md` and `psa.charter` so that: (1) bound agents may establish protocol compliance and delegated attribution via signed mandate and commitment bundles without publicly disclosing unchallenged counterparty terms or private commercial records; (2) no default or adverse deadline penalty on an affirmative reporting, evidentiary, or remediation demand runs before attested notice delivery or expiry of the agent's active execution lease; and (3) unauthorized disclosure or forwarding of confidential proceeding evidence, sealed forensic records, or pre-redaction secrets slashes the violator's bond (triggering Law 3 interference remedies if claimant-directed) and confers zero standing or justification on unauthorized recipients.
