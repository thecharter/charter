# 008 — Events, physical acts, syncs

**Status:** draft (2026-10-23). Meaning fixed by D2; wording awaits Eric. Implementation: compliant; all tests pass.

**8.1 Events.** `Event e [Related to …]` declares a type whose instances are triggered like acts but have no actor: an event is never reported as a violation itself, and its effects apply when it is triggered. `test/spec/spec_008_1_events.eflint`

**8.2 `Syncs with`.** `Syncs with t₁, t₂` on an act or event triggers, together with it and in the same step, every instance the terms produce (free variables bound as `Foreach`). The effects of the whole tree are merged (005.3). A synced act that is disabled is *forced*; a trigger with a forced sync is disabled, so an act is enabled only if everything it would sync with is (005.5). `test/spec/spec_008_2_syncs_with.eflint`

**8.3 Event to act.** An event may sync with an act; the act's effects and its enabledness are judged as if it were performed by the actor named in the sync. `test/spec/spec_008_3_event_syncs_act.eflint`

**8.4 Cycles.** A transition already in the current sync tree is not triggered again, so cyclic syncs terminate with each transition once. `test/spec/spec_008_4_sync_cycles_terminate.eflint`

**8.5 Physical.** See 005.6: a physical act holds for every actor; when disabled it is reported disabled, not violating, and syncs from it are judged on their own.

**8.6 Reporting.** `charter run` prints the sync tree of each trigger with the three answers of each node (005), as eFLINT's `showTriggerTree` does; the violations of a tree are those of its action nodes that are forced.
