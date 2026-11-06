# D25 — Rule-level `Amend` acts, reflexive `Immunity` entrenchment, `Regime` overlays, and 3-view `charter diff` (`D11`, `T23`, `T24`, `T38`)

**Laws:** 1, 2, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `D11`, `docs/rfc.md` §4.5, §4.7, §18.3)

## Ruling
1. **Rule-level `Amend` acts (`014.3`, `D11`)**:
   - Contextual `Amend <id> [Actor ...] ... [Repeals <id, ...>] [Installs { <decls> }] Valid when <expr>` declares an institutional amendment act (`isPower = true`, `isAmend = true`, requiring explicit `Valid when`, `CHR032`).
   - Every `Amend` is an event in the trace with an actor, timestamp, `lawful` judgment, and `valid` judgment (`Law 1`, `Law 2`).
   - When valid, `Amend` advances `Config.lawVersion` (`v -> v + 1`), applies its `AmendSpec` (`repeals` and `installs`) to `Config.spec`, recomputes `strata`, and preserves all already-accrued non-derived obligations and timestamps in `State` (`T23`: non-retroactive transition unless explicit effects modify state).
   - When void (`!valid`), `Amend` occurs (`occurred = true, valid = false`) and leaves `spec`, `lawVersion`, and `state` unchanged.
2. **Reflexive entrenchment (`Immunity ... Against Amend [Protects ...]`, `Entrenched Invariant`, `T24`)**:
   - An `Immunity` naming `Amend` (or a specific `Amend` act) in `Against`, with optional `Protects <id, ...>`, covers: (a) `Protects` targets ( plus all `Entrenched Invariant`s), (b) **itself** (`imId`), and (c) every type/rule read in `im`'s conditions or `Amend`'s `Valid when` (`reflexiveProtectedIds`).
   - Any `Amend` touching a rule in `reflexiveProtectedIds` while an un-lifted instance of `im` holds is **void** (`valid = false`), defeating both direct repeal and two-step "repeal the immunity, then repeal the floor" bypasses (`cir_ratchet_trajectory_preserves_entrenched`, `T24`).
3. **`Regime` initial-state overlays (`014.4`) & 3-view `charter diff` (`T38`)**:
   - `Regime <name> { <param> = <int>, ... }` declares named initial-parameter overlays selectable via `--regime <name>` in `charter explore` and `charter verify`.
   - `charter diff <old.charter> <new.charter> [--out json]` compares (1) English `Document`/`Clause` changes, (2) `CIR` rule/priority changes (flagging `REVIEW-REQUIRED` when formal rules change under unchanged approved English, `T38`), and (3) differential scenario verdicts and entrenchment preservation.

## Context
Completes `D11` and `docs/spec/014_parameters_and_regimes.md` (§14.3–14.5) over the live `Core.Spec` (`CIR`) pipeline without weakening `evalPhrase_sound` / `evalPhrase_complete`.

## Mission fit
`Law 1` & `Law 2` (weakening amendments occur and are void, never unperformable), `Law 4` (entrenchment is `Immunity ... Against Amend`), `Law 9` & `Law 10` (`cir_ratchet_trajectory_preserves_entrenched` proved over `Core.Spec`), `Law 12` (contextual keywords keep 196/196 eFLINT corpus green).

## Cost accepted
`Config` carries `lawVersion : Nat := 0`, and `Amend` commits pass through a transient internal store marker resolved cleanly inside `Interp.newContext`.

## Reopens if
Cross-artifact cryptographic `certificate-at-office` signature verification (`G4.3`) adds detached `Bundle` payloads to server-side `Amend` requests.
