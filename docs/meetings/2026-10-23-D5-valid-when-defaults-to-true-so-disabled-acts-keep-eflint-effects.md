# D5 — `Holds when` is lawful, `Valid when` is effective; `Valid when` defaults to true, so a disabled act keeps eFLINT's effects unless the program says otherwise

**Laws:** 1, 2, 12 (docs/mission.md). Brief: B2.
**Date:** 2026-10-23
**Status:** ruled (Eric), as predicted

## Ruling
An `Act` gains `Valid when e`. `Holds when` keeps eFLINT's meaning (enabled, lawful). Effects apply iff `Valid when` holds. An act with no `Valid when` is valid always, so every eFLINT program behaves exactly as in eFLINT (effects apply even when disabled, and a violation is reported). A disabled act is reported *occurred, unlawful, valid* or *occurred, unlawful, void*; the three judgments are always printed separately.

## Alternatives weighed
Charter-mode default "disabled implies void" (rejected: changes every eFLINT program's meaning, Law 12).

## Reopens if
Nearly every PSA act needs `Valid when` written; then a file-header mode may flip the default with the corpus pinned to the old one.
