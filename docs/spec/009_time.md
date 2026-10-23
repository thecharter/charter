# 009 — Time

**Status:** draft (2026-10-23). Phase 1 keeps eFLINT's non-advancing clock; D7's design is stated as pending. Implementation: compliant with 9.1; 9.2–9.5 pending.

**9.1 Phase 1.** `Current Time` is an integer expression equal to 0 and never advances; the `Time` domain enumerates `0..Current Time`. `test/spec/spec_009_1_time_is_zero.eflint`

**9.2 Types (D7, pending).** `Time` (instants) and `Duration` (differences) are distinct types over `Int`: `Time + Duration : Time`, `Time - Time : Duration`, no `Time + Time`; a literal coerces to either by demand.

**9.3 Time is state (Law 7, pending).** Every fact instance carries the time it was established and an optional expiry (`Creates e For d`). Deadlines, notice windows, pauses, and "held for" are conditions over those stamps: `held for d`, `count(e) >= n`, `Due within d`. Nothing in the history is a lapse event.

**9.4 The clock is input (Law 6, pending).** `@ t.` and `tick.` set the clock; they are environment input, not acts any party performed, and do not appear in the event history.

**9.5 Calendars.** A later chapter and an extension, not a migration (D7).
