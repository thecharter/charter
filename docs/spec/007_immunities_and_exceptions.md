# 007 — Immunities and exceptions

**Status:** draft (2026-10-23). 7.1–7.4 are implemented and tested (7.3 `Overridden by` landed 2026-10-25). The holder-is-recipient rule of 7.4 is this draft's reading of plan §2.2.2 ("not valid against the holder") and awaits Eric's wording.

Law 4 names four mechanisms with four spellings, and forbids writing one as another:

**7.1 Scope conditions.** A `Conditioned by` or `Holds when` on an act says when it is lawful (005.5). This is eFLINT's mechanism and the only one in Phase 1.

**7.2 Authority exceptions.** `Act x … Except under a₁, a₂`: performing an instance of `x` is lawful when and only when some instance of a named act, sharing the components they have in common (its other components bound to every instance), is enabled and valid. `x`'s own `Holds when` and `Conditioned by` are not consulted. The named acts must be acts (CHR022). `test/spec/spec_007_2_except_under.eflint`, `spec_007_4c_against_non_act.eflint`

**7.3 Duty-over-duty precedence.** `Duty d … Overridden by d₁, d₂` declares that the named duties take precedence over `d`: an instance of `d` is not violated (006.2) while an instance of a named duty holds that shares the components the two duties have in common, by name (as `Except under` shares them, 7.2); the named duty's other components range over every instance. Precedence is declared, never inferred, and one level deep: the overriding duty's own `Overridden by` is not consulted (the v0.3 field `overriddenBy`, whose reading this is). The named types must be duties (CHR026). `Violated(d(…))` answers accordingly, so a report of `d`'s violation (6.5) is withheld while it is overridden and made when the overriding instance ends. This draft's lift of v0.3's state-level precedence to instances (shared components) awaits Eric's wording; the protocol rewrite (Phase 3) is its first user. `test/spec/spec_007_3_overridden_by.eflint`, `spec_007_3b_overridden_non_duty.eflint`

**7.4 Immunities.** `Immunity name Holder v [Related to …] Against a₁, a₂ [Holds when e] [Unless e]` declares a type whose instances hold like facts (asserted or derived). While an instance holds, an act named in `Against` whose `Recipient` is the instance's holder is not valid (005.9); it still occurs and is judged lawful or not on its own. `Unless e₁, e₂`, over the immunity's components, lifts the protection while one holds. An act without a `Recipient` is not affected (this draft's rule). The named acts must be acts (CHR022). The immunity is a record, so the protection-over-power edge is data for every projection (Law 5); entrenchment is an immunity against `Amend` (D11, Phase 3). `test/spec/spec_007_4_immunity.eflint`, `spec_007_4b_immunity_unless.eflint`

**7.5 Remedies are not exceptions.** A breach's consequences are remedies of a finding (006.6), never a change to what is lawful.
