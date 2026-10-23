# 007 — Immunities and exceptions

**Status:** draft (2026-10-23); Phase 2 constructs, stated as design, pending. In the eFLINT core (Phase 1) the only exception mechanism is a condition, and this chapter has no conformance tests yet.

Law 4 names four mechanisms with four spellings, and forbids writing one as another:

**7.1 Scope conditions.** A `Conditioned by` or `Holds when` on an act says when it is lawful (005.5). This is eFLINT's mechanism and the only one in Phase 1.

**7.2 Authority exceptions (Phase 2).** `Act x … Except under a₁, a₂`: performing `x` is lawful when and only when it is also a valid exercise of one of the named acts (plan §2.2.4).

**7.3 Duty-over-duty precedence (Phase 2).** Stated with the protocol rewrite; the v0.3 field `overriddenBy` is its target.

**7.4 Immunities (Phase 2).** `Immunity name Holder v Against a₁, a₂ [Holds when e] [Unless e]`: while it holds, the named acts are not valid against the holder. A record, not a condition, so the protection-over-power edge is data for every projection (Law 5). Entrenchment is an immunity against `Amend` (D11).

**7.5 Remedies are not exceptions.** A breach's consequences are remedies of a finding (006.6), never a change to what is lawful.
