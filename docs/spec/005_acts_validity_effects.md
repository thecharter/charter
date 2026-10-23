# 005 — Acts, validity, effects

**Status:** draft (2026-10-23). Meaning fixed by D2 and D5; wording awaits Eric. Implementation: compliant for the eFLINT core; `Valid when` (D5) is Phase 2 and is stated here as the design, marked *pending*.

An act is a type whose instances are performed. Performing one is an event in the history and is judged by three independent answers (Law 2): it *occurred* (always, once performed: Law 1), it was *lawful* (eFLINT's *enabled*: the instance holds, its conditions hold, and nothing it syncs with is forced), and it was *valid* (it had institutional effect). In the eFLINT core every performed act is valid, so a disabled act still has its effects and the violation is reported, not enforced (D5).

**5.1 Effects.** `Creates e`, `Terminates e`, `Obfuscates e` make the instances `e` produces hold, not hold, or lose their assignment, for every binding of the act's components and of a `(Foreach xs: e)`. An effect `e When c` applies only where `c` holds. `test/spec/spec_005_1_act_effects.eflint`, `spec_005_4_foreach_effects.eflint`

**5.2 Disabled acts keep their effects (D5).** An act performed while not enabled has its effects and is reported as a violation (`charter run`: *lawful: no*). `test/spec/spec_005_2_disabled_act_keeps_effects.eflint`

**5.3 Create beats terminate.** The effects of one step (one trigger with everything it syncs with, or one parallel block) are merged with the precedence create > terminate > obfuscate, so an instance both created and terminated in a step holds. `test/spec/spec_005_3_create_beats_terminate.eflint`; proved: `Charter.Store.create_beats_terminate` (`src/Charter/Eval/Properties.lean`)

**5.4 Binding.** Components of the act are bound to the performed instance's arguments while its effects, conditions, and syncs are evaluated; further free variables of an effect are bound to every valid instance (as `Foreach`). `test/spec/spec_005_4_foreach_effects.eflint`

**5.5 Enabled.** An act instance is enabled when it holds (acts are facts: an act with no `Holds when` and no assignment is not enabled), its `Conditioned by` conditions hold, and no transition it syncs with is forced (008.2). `test/spec/spec_005_5_act_is_enabled_when_it_holds.eflint`

**5.6 `Physical`.** A `Physical` act holds for every actor without being created (`Holds when True`), may be conditioned, and when performed while disabled is reported disabled but not violating. `test/spec/spec_005_6_physical_acts_hold.eflint`

**5.7 Components.** An act's components are its `Actor` (default `actor`), then its `Recipient` if any, then its `Related to` objects, in that order; a duty's are `Holder`, `Claimant`, then `Related to`. `test/spec/spec_005_7_component_order.eflint`

**5.8 Triggering.** A trigger phrase names an act or event; a fact or duty is CHR103. `test/spec/spec_005_8_trigger_non_act.eflint`

**5.9 `Valid when` (Phase 2, pending).** `Act x … Valid when e`: effects apply iff `e` holds at performance; absent, `Valid when True`. A disabled act is reported *occurred, unlawful, valid* unless `Valid when` fails, then *occurred, unlawful, void*. Authority exceptions `Except under a₁, a₂` (plan §2.2.4) land with it.
