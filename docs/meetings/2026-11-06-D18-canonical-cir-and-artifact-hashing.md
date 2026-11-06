# D18 — Canonical `CIR` evolves from `Core.Spec` with `LawVersion` epochs and pure-Lean SHA-256 `Artifact` digests

**Laws:** 5, 9, 10, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §3.2, §3.4, §18.3)

## Ruling
1. Rather than introducing a second bloated AST alongside `Core.Spec`, Charter's Canonical Institutional IR (`CIR`) is a validated, epoch-segmented view over `Core.Spec` and `CPhrase`:
   - `Spec.checkWellFormed : Spec → Bool` and `Spec.WellFormed (s : Spec) : Prop` certify closed component domains, resolved placeholder aliases, valid `Against`/`Except under`/`Overridden by` targets, and successful topological stratification (`Stratify.strata`).
   - `CIR.Program` segments any resolved phrase stream into immutable `(version : Nat, spec : Spec, strata : List (List DomId), specSha256 : String, phrases : List CPhrase)` epochs whenever top-level declarations extend the law (`011.6`), with `elaborateProgram_epochs_wellFormed` proved in Lean.
2. Content-addressed `Artifact` digests (`src/Charter/Artifact/{Hash,Format}.lean`) use a pure-Lean, structural, kernel-reducible FIPS 180-4 SHA-256 implementation verified at compile time against single-block and multi-block NIST test vectors via `rfl` (zero external C/OpenSSL FFI in the proof TCB).

## Context
`docs/rfc.md` §3.2 and `docs/plans/2026-10-22-redesign.md` §3a require a content-addressed semantic representation (`CIR` / `Artifact`) shared between compiler, verifier, proof generator, and `charter-server`, while `charter prove` requires compact structural data types that reduce inside the Lean kernel.

## Alternatives weighed
- Separate high-level 20-field `CIR` AST distinct from `Core.Spec`: rejected — violates `Law 13` (duplicate representation of rules), bloats `charter prove` kernel terms, and forces an extra translation proof before `Eval`.
- External C/OpenSSL SHA-256 FFI: rejected for `Artifact/Hash.lean` — opaque `@[extern]` functions cannot reduce inside the kernel and expand the C TCB unnecessarily when SHA-256 is 120 lines of structural `UInt32` arithmetic.

## Mission fit
`Law 5` (rules remain inspectable data records), `Law 9` (one semantic representation evaluated by `Charter.Eval`), `Law 10` (zero axioms / FFI trust escapes; NIST vectors proved by `rfl`).

## Cost accepted
Pure-Lean SHA-256 hashes megabyte-scale files in milliseconds rather than hardware-intrinsics microseconds, which is negligible for source documents and compiled `.charter` artifacts.

## Reopens if
`Artifact` hashing is ever placed in a multi-gigabyte streaming hot path requiring hardware SHA extensions outside the kernel.
