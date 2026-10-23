# 007 — Immunities and exceptions

**Status:** draft (2026-10-23). 7.1, 7.2, and 7.4 are implemented (Phase 2's first slice, landed the same day) and tested; 7.3 is pending. The holder-is-recipient rule of 7.4 is this draft's reading of plan §2.2.2 ("not valid against the holder") and awaits Eric's wording.

Law 4 names four mechanisms with four spellings, and forbids writing one as another:

**7.1 Scope conditions.** A `Conditioned by` or `Holds when` on an act says when it is lawful (005.5). This is eFLINT's mechanism and the only one in Phase 1.

**7.2 Authority exceptions.** `Act x … Except under a₁, a₂`: performing an instance of `x` is lawful when and only when some instance of a named act, sharing the components they have in common (its other components bound to every instance), is enabled and valid. `x`'s own `Holds when` and `Conditioned by` are not consulted. The named acts must be acts (CHR022). `test/spec/spec_007_2_except_under.eflint`, `spec_007_4c_against_non_act.eflint`

**7.3 Duty-over-duty precedence (Phase 2).** Stated with the protocol rewrite; the v0.3 field `overriddenBy` is its target.

**7.4 Immunities.** `Immunity name Holder v [Related to …] Against a₁, a₂ [Holds when e] [Unless e]` declares a type whose instances hold like facts (asserted or derived). While an instance holds, an act named in `Against` whose `Recipient` is the instance's holder is not valid (005.9); it still occurs and is judged lawful or not on its own. `Unless e₁, e₂`, over the immunity's components, lifts the protection while one holds. An act without a `Recipient` is not affected (this draft's rule). The named acts must be acts (CHR022). The immunity is a record, so the protection-over-power edge is data for every projection (Law 5); entrenchment is an immunity against `Amend` (D11, Phase 3). `test/spec/spec_007_4_immunity.eflint`, `spec_007_4b_immunity_unless.eflint`

**7.5 Remedies are not exceptions.** A breach's consequences are remedies of a finding (006.6), never a change to what is lawful.
