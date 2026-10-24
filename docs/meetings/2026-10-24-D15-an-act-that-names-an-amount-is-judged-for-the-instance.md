# D15 — An act whose domain is not enumerable is judged for the instance asked about: `Holds when` is read with the components bound, never materialised (fifth eFLINT tolerance)

**Laws:** 2, 8, 9, 12 (docs/mission.md).
**Date:** 2026-10-24
**Status:** ruled by Eric (brief B11, `2026-10-24-briefs-for-ruling.md`, option (B) with two sharpenings). Spec wording below is the agent's rendering of the ruling; Eric's normative wording of 004.1, 004.7 and 005.5 replaces it when written.

## Ruling
1. **Lawfulness is asked of an instance.** For an act whose domain is not enumerable (a component over `Int`, `String`, `Time`, `Duration`, or a product containing one), `Holds when e` is evaluated for the instance asked about (`Enabled(a(…))`, `?lawful a(…)`, a performance `a(…).`) with its components bound, instead of being materialised by saturation. An assignment (`+a(…)`, `-a(…)`) still beats the rule (004.3). Facts are unchanged: 004.7 still ranges a rule over the instances that hold (`?!valid(5)` before `duedate(5)` in `spec_004_7`). *Scope: acts only, for now* (see "Reopens if").
2. **Sharpening 1, what binders see.** Such an act is never materialised, so a binder over it (`Exists transfer: …`, `Foreach transfer: …`, a free `transfer` in a rule, `?-transfer()`) ranges over its assigned instances only, which is almost never what the author meant. Resolve warns **CHR025** at every such binder. Silence here would trade one silent gap for another.
3. **Sharpening 2, the exploration menu is a search bound, not a program line.** `charter test --explore N` needs candidates for the non-enumerable components of such an act. They come from the test file's directive `//! explore-domain: <type> = v, a..b, "s"` (or the flag `--explore-domain "<type> = …"`), never from the institution's declarations. The default is loud: an exploration that meets such an act with no menu for a component reports the act as **unexplored**, tries the values of that kind that occur in the state as a named heuristic (*state-values*, reported in the output), and makes **no passing claim**: in test mode it is a failed claim. "Visited 400 states, found nothing" over a space that never tried a transfer is the silent pass Phase 2's exit refuses. `Regime` (014.4) stays what it is, an initial state.

## Context
`Act transfer Actor member Recipient member' Related to int Holds when (Exists basis: basis.member == member && basis.int >= int)` was never enabled: saturation derives over the act's domain, `Int` is not enumerable, so the binder ranged over held `int` instances, of which there are none. eFLINT behaves the same (`Saturation.hs`, `every_valid_subs`); its idiom is a finite menu (`Fact amount Identified by 1..10` in `buyer_seller.eflint`). Under that idiom `lib/entity_group` took an `amount` type parameter and measured: amounts `0..1000`, killed after 120 s; `0..12` with `//! explore: 2`, 181 s. With this ruling `test/lib/entity_group_test.eflint` runs in 0.2 s with `//! explore-domain: int = 0..12`.

## Why (B), in Eric's words
Spec 4.1 already states the declarative meaning: a type with `Holds when e` holds for every instance whose components satisfy `e`. Nothing in that sentence requires enumerating the domain. Saturation is the evaluation strategy, and it fails on infinite domains; eFLINT's `every_valid_subs` is the implementation limit, not the semantics. So (B) is not a change of meaning; it is the evaluator finally agreeing with 4.1 where eFLINT silently did not (Law 9). It sits where D6(a) sits: Charter right where eFLINT is wrong, recorded as a Law 12 tolerance with the corpus baseline naming the files that change. Law 2 is decisive on its own: the event is given, so judging it cannot require enumerating all events.

## Alternatives weighed
- **(A) Keep eFLINT's rule; amounts are finite menus.** Rejected: fails the ceremony test and would make the PSA rewrite dishonest at scale (every transfer, bond, buyout and draw becomes a denomination list).
- **(C) An amount is never a component of an act; the actor first asserts a request fact.** Rejected: splits one event into two phrases, blurs the "three answers about one event" framing, and puts the actor's choice into an asserted fact rather than the act that is that choice.

## What the references do
Catala: scopes are functions of their inputs; a condition is evaluated for the given arguments, never enumerated. Symboleo: obligations are instantiated per event with the event's parameters bound. Quint: actions are evaluated for chosen values (`nondet x = oneOf(S)`), and the simulator needs an explicit set to draw from, which is this ruling's menu.

## Mission fit
Law 2 (an event is judged, not enumerated), Law 8 (a transfer of forty is what the English says, not a denomination list), Law 9 (the evaluator matches the stated meaning), Law 12 (an eFLINT limit fixed under a decision and listed in `test/eflint-corpus/tolerances.md`).

## Cost accepted
- The evaluator's agreement proof now has two paths, materialised and membership, which `prove` (013.4) must both cover.
- A binder over such an act is a warning, not a value: a program that needs "every transfer so far" records them (`Creates transferred(member, member', int)`).
- Exploration needs a menu per non-enumerable component type, in the test file.

## Implementation
`Spec.judgedAct`, `Eval.isHolds` (membership path), `Interpreter` `?why` text, `Resolve.warnJudgedBinders` (CHR025), `Explore.scopeJudged`/`coverage`/`Menu`, `charter run|test --explore-domain`, directive `//! explore-domain:`. Fixtures: `spec_005_5b_act_with_int_component_judged_per_instance`, `spec_004_7b_binder_over_judged_act_warns`, `spec_013_2d_explore_menu`, `spec_013_2e_explore_without_menu_is_not_a_pass`; `spec_004_7` unchanged.

## Corpus baseline
`charter test test/eflint-corpus/tests test/eflint-corpus/examples --eflint --expect eflint-outcomes.txt --tolerate tolerances.md` after the change: 196 passed, 0 failed (164 agree, 32 tolerated, all pre-existing). **No corpus file's outcome changes** and CHR025 fires in none: every corpus act over a non-enumerable type is either assigned or never asked about. The tolerance row therefore names no files.

## Reopens if
A PSA clause needs `Holds when` on an `Int`-carrying **fact** with a time condition over it. A derived fact carries a stamp (009.3, stamped when first derived) that `Held … For` reads; an intensional fact has no derivation event, so its stamp is undefined. That is a design question, not a lift. Acts are judged at performance, so the stamp problem does not arise for them.
