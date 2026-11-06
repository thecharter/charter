# D21 — `Power` competence requirement (`CHR032`) and multi-document SHA-256 provenance (`T08`, `T37`, `T39`)

**Laws:** 2, 5, 8, 12, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §3.6, §4.1, §4.5, §18.3)

## Ruling
1. **Institutional `Power` vs. general `Act` (`005.10`)**:
   - `Act` retains `Valid when True` by default (`D5`, `Law 12`), so raw/physical eFLINT acts keep their state effects even when disabled/unlawful (`Law 1`, `Law 2`).
   - Contextual `Power <name> ... Valid when <expr> ...` declares an institutional power whose legal effects depend on explicit competence. Omitting `Valid when` on a `Power` is rejected statically with `CHR032`, and `Spec.WellFormed` enforces `!a.isPower || !a.validWhen.isEmpty` (`wellFormed_power_has_validWhen`). `Power` lowers to `ActSpec` with `isPower := true` so `Charter.Eval` remains minimal (`Law 9`).
2. **Multi-document SHA-256 provenance & coverage (`012.1`, `012.2`, `012.9`, `012.10`)**:
   - `Document [ID] "path" [SHA256 "hex"] [Rank n]` generalizes single-file `Document "path"` to multi-document manifests (`SourceDoc`), pinning collision-resistant SHA-256 content digests (`T39`) and optional integer authority ranks.
   - `Clause ID [In DOC_ID] [Approved ("sha256-hex" | fnv64)]` binds each clause to its source document and supports cryptographic SHA-256 approval digests while preserving backward-compatible legacy 64-bit FNV-1a approvals with SHA-256 migration guidance on `STALE` diagnostics (`T37`, `T39`).
   - `Artifact.SourceManifest` records line-shift-resilient Markdown heading anchors (`# ...`) and surrounding-context SHA-256 fingerprints (`locateClauseAnchor`), plus explicit three-valued provenance coverage (`complete | partial | illustrative`). Under `--require-provenance`, any non-`complete` coverage on a rule-bearing program fails with `CHR029` (`T08`).

## Context
Institutional powers (corporate authorizations, judicial orders, amendments) must never take legal effect by accidental omission of `Valid when`, whereas physical `Act`s must default to effective (`D5`). Meanwhile, 64-bit FNV-1a clause hashes are non-cryptographic (`T39`) and multi-instrument institutions cite multiple ranked source documents (`docs/rfc.md` §4.5).

## Mission fit
`Law 2` (separates physical occurrence/effect from institutional competence), `Law 5` (`isPower`, `SourceDoc`, `ClauseAnchor` are inspectable data records), `Law 8` (cryptographic SHA-256 provenance and explicit `complete | partial | illustrative` coverage), `Law 12` & `Law 13` (contextual keywords preserve 196/196 eFLINT compatibility with one canonical spelling).

## Cost accepted
`ActSpec` carries one boolean metadata flag (`isPower`) and `Spec` carries `documents : List SourceDoc` alongside primary `document : Option String`.

## Reopens if
Detached multi-approver Ed25519 signature rotation (`G4.1`) requires detached `.sig` files in addition to inline `SHA256` digests.
