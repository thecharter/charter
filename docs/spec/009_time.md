# 009 — Time

**Status:** draft (2026-10-23). Meaning fixed by D7 and Law 7; wording awaits Eric. Implementation: compliant (Phase 2's second slice, landed the same day); every statement has a passing conformance test. Calendars are not in scope (9.6).

**9.1 The clock.** `Current Time` is an instant. It starts at 0. The phrase `@ t.` sets it to the time `t`; `tick.` advances it by one. Both are environment input (Law 6): they are not acts, appear in no transition report, and leave no event in the history; like any phrase they recompute derived facts and violations (9.5). The clock never moves backwards: `@ t` with `t` before now is CHR106 and changes nothing. `test/spec/spec_009_1_clock.eflint`, `spec_009_1b_clock_never_backwards.eflint`

**9.2 Types (D7).** `Time` (instants) and `Duration` (differences) are distinct types over `Int`, and so are the domains `Identified by Time` and `Identified by Duration`. `Time + Duration : Time`, `Duration + Time : Time`, `Time - Duration : Time`, `Time - Time : Duration`, `Duration ± Duration : Duration`; `Time + Time` is CHR012. Comparisons relate two times, two durations, or two integers. A literal, or arithmetic over literals, coerces to `Time` or `Duration` by demand; an integer fact does not. `test/spec/spec_009_2_time_and_duration_types.eflint`, `spec_009_2b_no_time_plus_time.eflint`, `spec_009_2c_no_int_fact_as_duration.eflint`

**9.3 Time is state (Law 7).** Every assignment carries the time it was established; re-creating an instance that holds keeps its stamp, and a derived fact keeps its stamp while it stays derived. `Held(e) For d` holds when `e` holds and has held for at least the duration `d`: a condition over the stamp, never an event. `Creates e For d` stamps the created instances with the expiry `now + d`; from that time they no longer hold, with no event in the history. `test/spec/spec_009_3_held_for.eflint`, `spec_009_3b_stamp_kept_on_recreate.eflint`, `spec_009_3c_derived_keeps_stamp.eflint`, `spec_009_3d_expiry.eflint`

**9.4 Deadlines.** `Due within d` on a duty is `Violated when Held(d()) For d` (006.7): a requirement duty is breached once it has been held for `d` without the terminating act. `test/spec/spec_006_7_due_within.eflint`

**9.5 The clock is a step.** Setting the clock recomputes derived facts (a rule may read `Held`) and re-evaluates violations, so a deadline passing is noticed at the phrase that moves the clock, not by a synthetic lapse event. `test/spec/spec_009_4_clock_recomputes.eflint`

**9.6 Calendars.** A later chapter and an extension, not a migration (D7).

*Spellings this draft chose, for Eric:* `Held(e) For d` for the plan's "`held for d`"; `@ t.` and `tick.` as the plan writes them; `tick` is therefore a reserved word in Charter mode (not in `--eflint` mode).
