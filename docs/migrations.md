# Migration Guide: eFLINT 4.1, Legacy Approvals, and Versioned Amendments (`G5.5`)

---

## 1. Migrating Upstream eFLINT 4.1 Programs to Charter 1.0

Charter 1.0 maintains **one unified contextual grammar and semantics** (`D17`, `docs/spec/019_eflint_compatibility.md`):
- **Zero syntax edits required for stratified eFLINT 4.1**: `.eflint` files run directly under `charter check`, `charter run`, and `charter test` without `--eflint`. Unquoted atoms such as `Valid`, `Power`, `Document`, `Default`, `Exception`, `Money`, and `Duration` remain valid atoms everywhere.
- **Replacing cyclic self-negation (`CHR020`)**: Upstream eFLINT's unstratified self-negating default idiom (`Fact f Holds when !f ...`) is rejected by `CHR020` (`D6`). Replace it with Charter's stratified `Default` / `Exception` calculus (`004.12`, `007.6`):
  ```charter
  Fact eligible Identified by person
    Default r-base Holds when resident(person)
    Exception r-barred Overrides r-base Rejects when disqualified(person).
  ```
- **Upgrading `Act` to `Power` where validity is conditional**: Keep `Act` for physical or raw events whose factual effects hold even when unlawful (`D5`), and use `Power <name> ... Valid when <expr>` (`005.10`) for institutional competences whose legal effects must be void when unauthorized.

---

## 2. Migrating Legacy 64-bit FNV-1a `Approved` Hashes to SHA-256 (`D21`, `T39`)

- Legacy integer approvals (`Clause C.1 Approved 7561569358177147353`) remain accepted for backward compatibility.
- To upgrade a clause to collision-resistant SHA-256 (`T39`) and multi-document manifests:
  1. Run `.lake/build/bin/charter trace <CLAUSE_ID> <file.charter>` to inspect the current `sha256` digest of the reviewed clause text.
  2. Pin the document digest on `Document MAIN "path.md" SHA256 "<64-hex>"` and replace the integer approval with `Clause C.1 In MAIN Approved "<64-hex>"`.

---

## 3. Safe Law Upgrades & `AmendLaw` (`D11`, `D25`, `D27`, `T38`)

1. Run `.lake/build/bin/charter diff --require-approved old.charter new.charter` before approving any revision:
   - Flags **`REVIEW-REQUIRED (T38)`** whenever formal `CIR` rules or priorities changed while the bound `Clause` English remained unchanged;
   - Flags **`ENTRENCHED-VIOLATION`** if any `Entrenched Invariant` or `Immunity ... Against Amend` was weakened or removed.
2. Build and sign the successor artifact with `.lake/build/bin/charter build new.charter -o new.artifact --sign-key <key>`.
3. Submit `{"op": "AmendLaw", "amendAct": "...", "args": [...], "successorArtifact": "new.artifact"}` to `charter-server`, which enforces `certificate-at-office` and preserves already-accrued obligations (`T23`, `T24`).
