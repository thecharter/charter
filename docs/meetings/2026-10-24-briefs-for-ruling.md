# Briefs for rulings, 2026-10-24

Written while turning the eight `Charter/Modules/*.lean` patterns into `lib/*.eflint`
modules (D8, spec 015.5). Both briefs are about semantics, so neither is delegated; the
modules are written so that they pass under today's semantics and would need only the
edits named below under either ruling.

## B11. An act that names an amount is never lawful by derivation (blocks nothing today; decide before the PSA rewrite, Phase 3)

**Ruled 2026-10-24: (B), with two sharpenings (what binders see is a warning, CHR025; the exploration menu is a test directive with a loud default); acts only. See D15.**

**Finding.** `Act transfer Actor member Recipient member' Related to int Holds when (Exists
basis: basis.member == member && basis.int >= int)` is never enabled. `Holds when` is a
derivation over the act's domain (005.5, 004.1); `Int` is not enumerable, so a binder over
it ranges over the instances of `int` that hold (004.7), and none do. eFLINT behaves the
same (`Saturation.hs`: `derive xs (When (App d []) t)` over `every_valid_subs`), and its own
idiom is a finite menu: `buyer_seller.eflint` declares `Fact amount Identified by 1..10`;
`tests/syncs/enabled.eflint` declares `Fact int Identified by 1,2` for the same reason.

**Measured** (`lib/entity_group`, three members, two amount-carrying acts, `charter test`):
amounts `0..1000`: killed after 120 s with no result; `0..50`: 4 s; `0..12` with
`//! explore: 2`: 181 s; with `//! explore: 1`: 3 s. Saturation re-derives every instance of
every act's domain at every phrase, and exploration re-enumerates it at every state.

**What the modules do today.** `entity-group(group, member, stakeholder, amount)` takes the
amounts an act may name as a type parameter; the using program declares it as a range
(`Fact units Identified by 0..12`). Ledgers stay `Int` facts, so quantifiers over them range
over what holds and cost nothing. The other seven modules need no amount in any act: per
D10 valuations, inflows, claims, bonds and draws are environment facts, and the acts act on
them by name (`settle-inflow Actor oracle Related to asset`).

**Options.**
- (A) Keep eFLINT's rule. Amounts an actor chooses are finite menus. Cost: a reader of the
  institution does not think "transfers come in twelve denominations" says anything; it is
  ceremony (AGENTS.md), and the cost grows with the menu.
- (B) Lawfulness is asked of an instance. For an act whose domain is not enumerable,
  `Holds when` is evaluated for the instance asked about (`Enabled`, `?lawful`, a
  performance) with its components bound, instead of being materialised by saturation.
  Law 2 says the three answers are about *any event*: the event is given, so deciding
  whether it was lawful should not require enumerating every event. Facts keep 004.7
  unchanged (`?!valid(5)` in `spec_004_7` still holds before `duedate(5)` does). D2 safety
  is decidable by the corpus baseline: it differs from eFLINT only where eFLINT silently
  never enables such an act. `explore` then has no candidates for such an act unless given
  a menu, so (B) needs a companion: a `Regime`-style menu for exploration (014.4), or
  exploring amounts that occur in the state.
- (C) An amount is never a component of an act: the actor first asserts a request fact
  (`+transfer-request(Ann, Ben, 40)`) and the act acts on it by name. Honest under today's
  rules and what seven modules do, but for an actor's own choice it is one more phrase that
  says nothing (ceremony).

**Prediction:** (B) with the exploration companion, 70%. Not delegated: it is semantics.

**Edit under (B):** drop the `amount` parameter of `entity-group`, write `Related to int`
again, and add `Regime`/menu lines to `test/lib/entity_group_test.eflint` for exploration.

## B12. `Duration * Int` (blocks nothing; a D7 spelling)

**Ruled 2026-10-24: allow `Duration * Int`, `Int * Duration`, `Duration / Int`; refuse the rest. See D16.**

**Finding.** `Charter/Modules/CollateralPool.lean` scales an observation window
multiplicatively, `base * max 1 domainMultiplier * max 1 irreversibilityMultiplier`. In
Charter `base-observation-window * 2` is CHR012 (`cannot use an instance of base where an
integer is needed`); `Duration + Duration` is fine. `lib/collateral_pool.eflint` therefore
adds one extension per risk class (`base + risk-extension`, `base + irreversibility-extension`)
and says so in its header.

**Options.** Allow `Duration * Int`, `Int * Duration`, `Duration / Int` (a `Duration`
results; `Duration * Duration` stays an error), or keep durations additive only.

**Prediction:** allow, 90%. Not delegated: it is a D7 spelling. **Edit when allowed:**
multipliers as `Int` facts and one `commit` act instead of three.

## Notes that are not briefs (recorded in the handoff and the spec)

- A binder over a type whose components are all enumerable ranges over the whole domain
  (003.2), so in a rule `(Exists frozen: frozen.member == member)` is true for every member
  while any `frozen` element exists in the domain; the body must say the instance holds
  (`frozen && …`, or the application form `frozen(member, initiator)`). Over a type with an
  `Int` component the same binder ranges over what holds. Both are eFLINT's rules; the first
  bit this session four times before it was learned. Now a sentence in 004.7.
- A derived fact is stamped when it is first derived (009.3), which is the phrase that
  observed the clock, not the instant its condition became true: a scenario that jumps the
  clock from 0 to 9 stamps a fact due at 5 with 9. `test/lib/exit_and_voice_test.eflint`
  steps through 5 and says why.
- Frame properties (an act leaves a fact unchanged) are properties of acts, not of states,
  so they are not `Invariant`s; `lib/attested_lease.eflint` names them for `prove` (013.4).
