# D7 — `Time` (instants) and `Duration` (differences) are distinct types over `Int`; calendars are deferred

**Laws:** 7, 13 (docs/mission.md). Brief: B4.
**Date:** 2026-10-23
**Status:** ruled (Eric), as predicted

## Ruling
`Time + Duration : Time`, `Time - Time : Duration`, no `Time + Time`. `Current Time : Time`. A literal coerces to either by demand. Every fact instance carries its establishment `Time` and optional expiry; `@ t.` and `tick.` are environment input, not events. Calendar dates are a later chapter and an extension, not a migration.

## What the references do
Catala: distinct `date`/`duration`, explicit rounding, suffixed operators. eFLINT: `Time` lexed, never advanced.

## Reopens if
The distinction produces casts in more than a handful of PSA places.
