# Prenup

Files: `Examples/Prenup/prenup.md`, `prenup.charter`, `cases/vargas-reed.charter` (8 scenarios).
`charter check --require-provenance --deny-warnings prenup.charter` ends
`ok   Examples/Prenup/prenup.charter: 1 phrase(s) resolve (29 declared types, 6 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/vargas-reed.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp/cf-pre/mut`, `?awarded(Elena, 750000)` changed to `750001` gave
`cases/vargas-reed.charter [scenario an-odd-cent-goes-to-neither, phrase 10]:105: query failed: ?awarded("Elena", 750001)`.

## Size

English sentences: 11. Charter lines outside clause blocks and comments: 55. Clause-block lines: 15.
Case lines: 106. Declarations no sentence of the text refers to: 4 (`usd`; `worth`, because the
text never mentions value but "divided equally" needs one; `governed`, a latch that records whether
the agreement was in force on the day of the divorce; `kept`, the record that `keep` had effect).

Known issues, counted in this example:

- A span cannot name a fact, rule or event: 5 of 8 spans. This example is the worst case, because
  N.2, N.3 and N.4 are classification rules and nothing else. The program has a named rule for
  each sentence (`owned-before`, `gift-or-inheritance`, `acquired-during`, `mixing`), and the spans
  have to name `keep` and `take-half` instead. N.1 "It is void if …" and N.6 "lapses" both mean
  the fact `in-force`; they name `sign, keep, take-half` and `keep, take-half`.
- `Holds when True`: 1 (`sign`).
- Money in cents: 18 literals in the case file. `pool.usd` to read a money fact: 1.
  `pool(Sum(…))` to write one: 1.
- A failed claim reported the scenario's first line: every time.
- `Power` whose `Valid when` repeats `Holds when`: 0 exactly, but `owner(asset, person) && Not(marital())`
  is in both conditions of `keep`.
- `person == X`: 0 after I replaced `signed(Elena) && signed(Tomas)` with `(Forall person: signed(person))`.
- `Created by`, `Document` before `#require`, "at least two of": 0.

No calendar, and what it distorted:

- "Ten years" is `Param term : Duration = 3650`. Ten years is 3652 or 3653 days. The program
  lapses the agreement two or three days before the tenth anniversary.
- "A divorce after that" needs the state of the agreement on the day of the divorce. Time is
  state, so a condition read later sees the later time. See "What was hard" 6.

## What was hard

The first version resolved and passed its first scenario at the first attempt. Everything below
was found by writing the next scenario or by trying the spelling I would have guessed.

1. **Summing the marital property, natural spelling.**

   ```
   Creates awarded(person, MulDivRound(Sum(Foreach asset, usd: usd When worth(asset, usd) && marital(asset)), 1, 2, Floor))
   ```

   No diagnostic. `query failed: ?awarded(Elena, 750000)`; the listing showed
   `awarded(person("Elena"),usd(0))`. Each spouse was awarded nothing. A binder over the money type
   ranges over nothing (the same defect as PowerOfAttorney, Tool defects 2). What works:
   `Sum(Foreach worth: worth.usd When marital(worth.asset))`.

2. **`worth` is declared `Function` and cannot be applied.**
   `Sum(Foreach asset: worth(asset) When marital(asset))` gives
   `./e.charter:2:0: error CHR011: worth has 2 component(s), 1 given` (line 2, column 0; the
   expression is on line 63).

3. **Giving the total a name took three attempts.**
   `Fact pool Identified by usd Derived from Sum(…)`:
   `./d.charter:2:0: error CHR012: cannot use Money(USD, 2) where an instance of pool is needed`.
   Then `Derived from pool(Sum(…))` with `MulDivRound(pool, 1, 2, Floor)`:
   `./d.charter:2:0: error CHR012: cannot use an instance of pool where an integer is needed`.
   Then `MulDivRound(pool.usd, 1, 2, Floor)`: passes. Spec 010.4 promises both conversions for
   integer types; they are not made for a `Money` type.

4. **An asset nobody owns was marital.** `Default acquired-during Holds when Not(premarital())`
   holds for every element of the `asset` domain, owned or not:
   `[scenario divided-as-written, phrase 13]:7: query failed: ?!marital("Car")`. It needed
   `&& (Exists person: owner())`.

5. **The concealment rule depends on the case file.**
   `concealed(person) When (Exists asset: owner(asset, person) && Not(listed(asset)))` works because
   the case file says `Extend Fact asset Identified by Flat, Boat, …`. With assets left as strings
   (`acquires(Tomas, "boat", 4000000). sign(Tomas).`) the same rule never fires:
   `ts.charter:4: query failed: ?concealed(Tomas)`, no diagnostic. A binder over a type means
   "every element" if a later file enumerated the type and "every held instance of the type
   itself" (none) if not. I kept the natural spelling; the example is correct only with its cases.

6. **Lapse needs a latch.** Written first: `Valid when in-force() && …` on `keep` and `take-half`.
   A divorce on day 3649 followed by a claim on day 5000 was void:
   `[scenario a-divorce-inside-the-term-stays-governed, phrase 10]:95: claim failed: ?valid keep("Elena", "Flat")`.
   The fix is a second flag set by the event: `Bool governed` and
   `Event divorce Creates divorced(), governed() When in-force()`.

7. **Missing one name in `Overrides` is silent until a scenario hits it.** With
   `Exception mixing Overrides gift-or-inheritance` (forgetting `owned-before`), a premarital boat
   put in the joint account is neither marital nor separate:
   `query failed: ?marital("Boat")` and then `?awarded("Tomas", 4500000)` fails. That is the
   documented conflict behaviour and it is the right behaviour; `check` could say "rules
   `owned-before` and `mixing` can both apply and are unranked".

**Did the listed features help?** `Default`/`Exception`: yes, clearly. Four sentences became four
named rules in the order of the text, and the override list is the only place the author thinks
about precedence. This is the best fit of a feature to a text in my four examples. `MulDivRound`:
it works, and `Sum(…) / 2` gives the same number with less to read. I kept `MulDivRound` because
`Floor` at least shows that a cent is lost; neither form tells the author that "divided equally"
left a cent unassigned. Time: `Held(wed()) For term` is one line and exact, apart from the latch.

## Improvements (most valuable first)

### 1. A span that names the rule it states

Today:

```
Fact marital Identified by asset
  Default owned-before Rejects when premarital()
  Default acquired-during Holds when Not(premarital()) && (Exists person: owner())
  Exception gift-or-inheritance Overrides acquired-during Rejects when by-gift()
  Exception mixing Overrides owned-before, gift-or-inheritance Holds when mixed()
…
Clause N.2 …
  Norm "Property a party owns when the parties marry is that party's separate property. A gift or inheritance one party receives during the marriage is that party's separate property." => keep
Clause N.3 …
  Norm "All other property either party acquires during the marriage is marital property." => take-half
```

Proposed, does not parse today:

```
Clause N.2 …
  Definition "Property a party owns when the parties marry is that party's separate property." => owned-before
  Definition " A gift or inheritance one party receives during the marriage is that party's separate property." => gift-or-inheritance
Clause N.3 …
  Definition "All other property either party acquires during the marriage is marital property." => acquired-during
Clause N.4 …
  Definition "Separate property that a party puts into the parties' joint account becomes marital property." => mixing, put-in-joint-account
```

and `check` requires every named `Default` and `Exception` to be named by a span, as it does for
acts. Saves nothing in lines. It makes the provenance true: today `charter trace N.3` says N.3
means `take-half`, which is N.5. Occurs in 5 of 8 spans here.

### 2. A function you can apply, and a sum over it

Today:

```
Function worth Identified by asset * usd
Var pool Identified by usd
  Derived from pool(Sum(Foreach worth: worth.usd When marital(worth.asset)))
… MulDivRound(pool.usd, 1, 2, Floor)
```

Proposed, does not parse today:

```
Function worth Identified by asset * usd
Amount pool Is Sum(Foreach asset: worth(asset) When marital(asset))
… MulDivRound(pool, 1, 2, Floor)
```

`worth(asset)` is the value; a named amount is its value wherever a number is wanted. Saves the
`pool(…)` wrapper, `.usd` at each use, and three failed attempts (items 1 to 3). It also removes the
spelling that silently sums to zero. Occurs once here; `LivingTrust` has `fund.usd` five times.

### 3. Equal division that accounts for every cent

Today:

```
Power take-half Actor person
  Holds when divorced()
  Valid when governed()
  Creates awarded(person, MulDivRound(pool.usd, 1, 2, Floor))
```

With a pool of $15,000.01 each party is awarded $7,500.00 and one cent belongs to nobody; nothing
reports it. Proposed, does not parse today:

```
  Creates awarded(person, Share(pool Among person Remainder To Elena))
```

`Share(x Among t Remainder To a)` is `x` divided by the number of `t`, with the remainder added to
`a`'s share; leaving out `Remainder` is an error, so the author is asked the question the English
forgot. Saves the `1, 2` (which is "the number of parties" written as a literal) and a silent loss.
Occurs once.

### 4. A condition as of the moment something happened

Today:

```
Bool in-force
  Holds when (Forall person: signed(person)) && Not(Exists person: concealed(person))
          && Not(Held(wed()) For term)
Bool governed
Event divorce
  Creates divorced(), governed() When in-force()
Power take-half Actor person
  Holds when divorced()
  Valid when governed()
```

Proposed, does not parse today:

```
Event divorce
Power take-half Actor person
  Holds when Done(divorce)
  Valid when in-force() At divorce
```

`c At e` is the value `c` had when `e` occurred. Saves the `governed` flag, the `divorced` flag and
the event's effect line (3 lines), and the error of item 6, which any author will make first.
Occurs once here. `LastWill` W.6 ("survive me by thirty days") is the same shape.

### 5. Durations in the units the text uses

Today `Param term : Duration = 3650` for "ten years". Proposed, does not parse today:
`Param term : Duration = 10 years`, with `Held(wed()) For 10 years` true from the tenth
anniversary. Saves a wrong number (off by two or three days) and the arithmetic. Occurs once here,
and wherever a text says months or years.

### 6. One meaning for a binder

Today `(Exists asset: owner(asset, person) && Not(listed(asset)))` means two different things
depending on whether a later file enumerated `asset` (item 5), and `Foreach asset, usd: …` ranges
over nothing (item 1). Proposed: a binder over a type always ranges over the values that occur in
some held fact of the program, or `check` refuses a binder over a type with no enumeration and
says "bind the fact instead: `Exists owner: …`". Saves two silent wrong answers in this file alone.

### 7. Events that set a flag

Today `Bool wed` with `Event wedding Creates wed(), …` and `Bool divorced` with
`Event divorce Creates divorced(), …`. Proposed, does not parse today: `Done(wedding)`,
`Done(divorce)`, and `Since(wedding) >= term` for `Held(wed()) For term`. Saves 2 `Bool` lines and
2 effect items. Occurs twice.

## Tool defects

1. **A binder over a `Money` type silently yields nothing; here it awarded $0.** Reproduction in
   PowerOfAttorney, Tool defects 2. In this example:
   `Sum(Foreach asset, usd: usd When worth(asset, usd) && marital(asset))` is 0 whatever holds.
   Expected: the sum, or a diagnostic. Actual: 0, no warning. Workaround: `Foreach worth: worth.usd`.

2. **The same binder changes meaning when a case file enumerates the type.**

   ```
   Fact person Identified by Tomas
   Fact asset
   Fact owner Identified by asset * person
   Fact hidden Identified by person
     Holds when (Exists asset: owner(asset, person))
   .
   +owner("boat", Tomas).
   ?hidden(Tomas).
   ```

   Expected: holds. Actual: `query failed` (with `Fact asset Identified by Boat` and
   `+owner(Boat, Tomas)` it holds). No diagnostic in either case. Workaround: enumerate the type
   in every case file, or bind the fact (`Exists owner: owner && owner.person == person`).

3. **The conversions of spec 010.4 are not made for a `Money` type.**
   `Fact pool Identified by usd Derived from Sum(…)` → `CHR012: cannot use Money(USD, 2) where an
   instance of pool is needed`; `MulDivRound(pool, 1, 2, Floor)` → `CHR012: cannot use an instance
   of pool where an integer is needed`. With `Identified by Int` both are accepted by the spec's
   own wording ("an instance of an integer … type where that value is needed", "a value where an
   instance is needed"). Workaround: `pool(Sum(…))` and `pool.usd`.

4. **Diagnostics for a declaration block point at the block's first line**: CHR011 and CHR012
   above were reported at `2:0` for expressions on lines 53 to 64. (Known; it cost a search each
   time because the block is the whole program.)

## What a lay author would have guessed

- `Sum(Foreach asset, usd: usd When worth(asset, usd) && marital(asset))`. Accepted; always 0.
- `worth(asset)` for "what the asset is worth". Rejected, CHR011.
- `Fact pool Identified by usd Derived from Sum(…)` to name the total. Rejected, CHR012.
- `Valid when in-force()` for "has no effect on a divorce after that". Accepted; voids a claim made
  late on a divorce that was in time.
- `Default acquired-during Holds when Not(premarital())` for "all other property". Accepted; makes
  property nobody owns marital.
- `3650` for ten years.
- `… / 2` for "divided equally". Accepted, floors silently.
