# D29 — A spelling that is accepted and gives a wrong answer is fixed where it is a bug and refused where it is not

**Laws:** 12, 13, and `AGENTS.md` "No silent fallbacks".
**Date:** 2026-11-07
**Status:** delegated (Eric directed the fixes, 2026-11-07; the spec sentences below are drafted and await his review)

## Context
Writing twenty worked examples (`docs/plans/2026-11-07-example-friction/`) found eleven cases
where a natural spelling is accepted and gives a wrong answer (issues #2 to #12). Four are
settled here. Each has a fixture that was seen failing first.

## Rulings

1. **`Held(e) For d` is a read of `e`** (004.6, 009.3; #5). Stratification did not count it, so a
   rule using it could be derived before the rule deriving `e` and stay false. A bug: one line in
   `Charter.Core.Derivation.deps`. Fixture `spec_004_6d_held_is_a_read.charter`.
2. **A component named twice is one value; two different arguments for it are CHR036** (003.3; #2).
   `Fact yes Identified by person * person` with `yes(Iris, Wren)` ran as `yes(Iris, Iris)`.
   The declaration is kept, because `Duty d Holder actor Claimant actor` is a deliberate idiom
   for a duty with one party (six fixtures under `test/spec/` use it). The application is refused.
   Fixture `spec_003_3c_repeated_component.charter`.
3. **A phrase triggers, creates, or terminates an instance; a bare literal is CHR012** (011.2; #7).
   `= 10000.00.` is the integer `10000`, a terminator, and a phrase `00.` that was accepted and
   did nothing, so ten thousand dollars was read as one hundred. Fixture
   `spec_011_2b_bare_literal_is_not_a_phrase.charter`.
4. **`Installs` declares rules, not state; a `Param` inside it is CHR037** (014.1, 014.3; #10). It
   was valid and changed nothing. Fixture `spec_014_3c_amend_cannot_install_param.charter`.

## Alternatives weighed
- For 2, refusing the declaration (rejected: it removes the one-party idiom and broke seven
  fixtures); a warning (rejected: the wrong answer stays).
- For 3, refusing digits, a dot, and digits in the lexer (rejected: `Clause 1.1` is exactly that;
  it broke thirteen of the twenty examples).
- For 4, making `Installs { Param … }` assign the value (rejected for now: 014.3 says an amendment
  leaves state intact, and 014.1 already gives the spelling, `Creates name(v)`).

## What the references do
eFLINT 4.1.0.1 accepts 2 and 3 silently. The 196-file corpus contains neither a repeated
component given two arguments nor a bare-literal phrase; its outcomes are unchanged (164 agree,
32 tolerated).

## Cost accepted
Two new static errors (CHR036, CHR037) and one wider use of CHR012. A program that relied on a
dropped argument or a no-op phrase is now refused.

## Reopens if
An eFLINT program in the wild uses a repeated component with two arguments on purpose, or the
remaining defects of the eleven (#3, #4, #6, #8, #9, #11, #12) are ruled in a way that changes
what "an instance" means here.
