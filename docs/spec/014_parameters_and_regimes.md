# 014 — Parameters and regimes

**Status:** draft (2026-10-23). Meaning fixed by D11 and D7; wording awaits Eric. Implementation: 14.1–14.2 compliant (Phase 2's fourth slice); 14.3–14.5 are Phase 3 and Phase 4, stated as pending.

**14.1 Parameters are facts (D11).** `Param name [: Int | Time | Duration] = n` declares a `Var` fact over the named domain (`Int` by default) whose initial instance is `n`. Any position of that type may name it as a variable (`notice-window + 1`), binding to the instance that holds. An act may `Creates name(m)`; the `Var` restriction makes the new instance the only one, and the program judges that amendment like any event: it occurs, it is lawful or not, it is valid or not. `test/spec/spec_014_1_param.eflint`, `spec_014_1b_param_typed.eflint`, `spec_014_1c_param_as_duration.eflint` (a `Duration` parameter as the `For d` of `Creates e For d`)

**14.2 A parameter is a declaration.** It is introduced with the declaration block it appears in (011.6); its initial instance is assigned by that block, with the origin *asserted* (004.10).

**14.3 Rule amendment (Phase 3, pending).** `Amend` is an act whose `Creates`/`Terminates` target rule records (a duty, a power, an immunity, a clause binding); every rule change then has an actor, a stamp, a validity answer, and an effect answer (D11). Entrenchment is `Immunity I Holder … Against Amend`, reflexive. `Extend` stays eFLINT's declaration-time mechanism and never changes rules at run time.

**14.4 Regimes (Phase 4, pending).** `Regime "label" { name = n }` is an alternative initial state for `charter explore`, nothing more.

**14.5 Entrenched invariants (Phase 3, pending).** The universal ratchet theorem: every valid `Amend` trajectory preserves every `Invariant` tagged `Entrenched`.
