# OperatingAgreement

Files: `Examples/OperatingAgreement/agreement.md`, `agreement.charter` (root), `1-members.charter`,
`2-decisions.charter`, `3-distributions.charter`, `4-sale.charter`, `5-withdrawal.charter`,
`6-dissolution.charter`, `7-amendment.charter`, `A-first-amendment.charter`, `cases/tidewater.charter`
(11 scenarios).

Final lines:
- `charter check --require-provenance --deny-warnings agreement.charter` ->
  `ok   agreement.charter: 15 phrase(s) resolve (53 declared types, 20 clauses, coverage complete, 0 warning(s))`
- `charter test --deny-warnings cases/tidewater.charter` -> `1 passed, 0 failed, 1 total`
- Mutation (copy under `/tmp/cf-oa/mut`): four claims changed (`?cash(9899999)`, `?valid sell-outside(Kemal, Wren, 2499999)`,
  `?buyout-due(Tidewater, Jonah, 5400000)` after the amendment, `?lawful wind-up(Tidewater)` before the debts) ->
  `FAIL cases/tidewater.charter: 0 error(s), 4 failed claim(s)`.

## Size

English sentences: 28. Charter lines outside clause blocks and comments: 153. Clause-block lines: 44.
Case lines: 119. Declarations no sentence of the text refers to: 13
(`usd`; `total-capital`; `candidate`; `matter`; `amendment`; and eight facts the `poll` module derives that no
power reads: `payout-three-quarters`, `payout-unanimous`, `admission-majority`, `admission-three-quarters`,
`matter-majority`, `matter-three-quarters`, `amendment-majority`, `amendment-unanimous`).

Ratio: 5.5 lines of Charter (153) per English sentence (28), before the clause blocks.

Known issues, how often each bit:
- Clause span cannot name a fact or derived fact: 6 spans (1.1 the members, 1.2 the contributions, 1.3 percentage
  interest, 2.2 "more than half", 2.1's weighting, 6.1 "or when only one member remains"). 2.2 is a `Definition` with no
  rule although it is the sentence that decides every ordinary decision.
- `Approved`: 20 stamps; `tools/approve-clauses` had to be run on each of the 8 article files (the root stamps nothing).
- `Holds when True`: 8.
- `Power` needs `Valid when`: 9 powers. One repeats its `Holds when` word for word (`accept-offer`); eight are
  `Holds when True` because only validity matters, so the pair is always one real condition and one filler.
- Money ceremony: `Fact usd`, `cash.usd`, `book-value.usd`; and see "Money cannot be a ratio" below.
- `Created by`: unusable once (`buyout-due` carries a computed price the creating act `buy-out` does not carry), so
  the duty is created by an explicit `Creates buyout-due(company, person, MulDivRound(…))`. `Terminated by` worked.
- `Document "x.md".` before `#require`: 1.
- Diagnostics at the first line of the block: every resolve error I got (5 probes) said `:1:0`.
- Time in days: 3 places; see distortions.

Distortions from "no calendar, executed instance":
- 5.2 "When the notice period ends, the company buys" is not an act anyone performs; it happens by lapse of time.
  I had to write a power `buy-out` that someone triggers on or after day 90. 5.3's sixty days then run from that
  trigger, not from the end of the notice period as the text says. If `buy-out` is performed on day 120, the
  program gives the company until day 180; the text says day 150.
- 4.2 does not say when the purchase closes; the rule closes it at day 30 even if both members accepted on day 1.
- "Book value" and "cash the company holds" are asserted numbers in the case file.
- 1.2 states contributions in dollars; the program stores them as bare integers (see hard item 1).

## The article split

| File | `#require`s | Why | Checks alone (`check --deny-warnings`) |
|---|---|---|---|
| `1-members` | none | | yes, `coverage partial` |
| `2-decisions` | 1 | `person`, `member`, `capital`, `total-capital` | yes |
| `3-distributions` | 2 | the `poll` module, `cash` | yes |
| `4-sale` | 1 | `person`, `member`, `capital`, `usd` | yes |
| `5-withdrawal` | 1 | `company`, `capital`, `cash`, `usd` | yes |
| `6-dissolution` | 3 | `paid`, `distribute` (extends it), and through it `matter` and the poll | yes |
| `7-amendment` | 2 | the `poll` module | **no**: `FAIL 7.1: spans name undeclared rules: first-amendment` |
| `A-first-amendment` | 5, 7 | repeals `buy-out`; needs the `amendment` poll | yes |

- No article can pass `--require-provenance` alone: `error CHR029: normative rules declared with provenance coverage
  partial`, because only the root has `Document`. Same for the pilot (`LivingTrust/4-duties.charter`). So "can be
  checked alone" means "resolves alone"; verbatim and coverage are only checked from the root.
- Where shared declarations ended up: everything two articles need sank into Article 1, whether or not Article 1's
  text mentions it. `cash` (first mentioned in 3.1), `usd`, `company` and the helper `total-capital` are in
  `1-members.charter` because 3, 4, 5 and 6 all need them. Article 1's file is 12 declaration lines of which 4 belong to
  Article 1's sentences.
- Article needing a later article, three cases:
  1. 6.2 "After dissolution the company makes no other distribution" restricts an act of Article 3. This one went
     well: `Extend Act distribute Valid when Not(dissolved())` in `6-dissolution.charter` adds the condition from the
     article that says it, and Article 3 does not need to know Article 6 exists. (I verified `Extend … Valid when`
     is conjunctive.) Same for `Extend Fact matter Identified by Dissolve`.
  2. 2.4 "A decision made without the vote this agreement requires has no effect" is about `distribute` (Art. 3),
     `dissolve` (Art. 6) and `first-amendment` (Sched. A), all of which `#require` Article 2. Its span names only
     `admit` and `sell-business`, the two powers that happen to live in Article 2. A general sentence in an early
     article cannot name the later rules it governs without a `#require` cycle.
  3. 7.1 "An amendment made without that vote has no effect" has no rule in Article 7 at all; its only meaning is the
     `Valid when` of each `Amend`, and the one `Amend` lives in Schedule A, which requires Article 7. The root accepts
     the forward name; the article alone fails. I tried the mutual `#require` (7 requires A after its declarations, A
     requires 7): the file named on the command line is loaded twice, giving six `CHR019 … is declared again`
     warnings (tool defect 3). I left 7 not checkable alone rather than invent an `adopt` act and an `adopted`
     fact whose only job is to carry the threshold from Article 7 to the schedule.
- The module `poll` is declared in Article 2 and instantiated in 2 (twice), 3 and 7. That worked without friction.
- An `Extend Fact person Identified by Wren` in the case file reaches every article. Fine.

## What was hard

In order. Probes are under `/tmp/cf-oa/`.

1. Pro-rata by capital, capital in dollars. First attempt (`t3.charter`):
   `Function capital Identified by member * usd` and
   `Creates (Foreach capital: paid(capital.member, MulDivRound(usd, capital.usd, Sum(Foreach capital': capital'.usd), Floor)))`.
   Diagnostic: `t3.charter:1:0: error CHR012: cannot use an instance of usd where an integer is needed`
   (line 1 for an expression on line 7; it does not say which argument). Then `(capital.usd * 10000) / Sum(…)`:
   `error CHR012: cannot divide Money(USD, 2) by Money(USD, 2) in /`. Then `MulDivRound(capital.usd, 10000, Sum(…), Floor)`:
   `error CHR012: cannot use Money(USD, 2) where an integer is needed`. There is no way to form the ratio of two
   money amounts, so 1.2's dollars became `Function capital Identified by person * int`.
2. "Carried" as a derived fact over the amount voted on (`t2.charter`):
   `Fact carried Identified by usd Holds when Sum(Foreach capital: capital.usd When in-favour(capital.member, usd)) * 2 > Sum(Foreach capital: capital.usd)`.
   No diagnostic. `?carried(7)` simply fails: `t2.charter:9: query failed`. Cause is 004.7 (a free variable over a
   non-enumerable type ranges over held instances of that type, and no `usd(7)` holds). Working form:
   `Derived from majority(yes.subject) When …`.
3. `Derived from yes.subject` (the natural form of the fix): 
   `m1.charter:1:0: error CHR012: cannot use an instance of usd where an instance of payout-majority is needed`.
   Needs `Derived from majority(yes.subject)`. The one real error was followed by 18
   `error CHR010: undeclared type or placeholder …` lines, one for every later phrase.
4. A member's capital as a value. `capital(Iris) > 10`: `error CHR011: capital has 2 component(s), 1 given`.
   `(Exists int: capital(member, int) && int * 2 > …)`: no diagnostic, always false. `capital(member, int) && int * 2 > …`:
   no diagnostic, always false. `capital() && capital.int * 2 > …`: no diagnostic, always false. Working forms:
   `(Exists capital: capital.person == person && …)` for a condition and
   `Sum(Foreach capital: capital.int When capital.person == seller)` for the value.
5. A name ending in a digit: `Fact holds-most2 …` -> `t9.charter:4:16: error CHR004: expected . to end the phrase but found integer 2`.
   (002.1: a digit ends an identifier. The message does not say so.)
6. `Use poll(person) As admission` so members can vote on a person. Accepted with no diagnostic; it means
   something else (tool defect 1). Working form needs `Placeholder candidate For person` and `Use poll(candidate)`.
7. The amendment clause (see article split, case 3).

Everything else resolved and passed on the first run, including the pro-rata purchase, `Amend … Repeals … Installs`,
the module with four instantiations, and `Extend Act … Valid when`.

## Improvements (most valuable first)

### 1. A vote is a clause of the act it decides, not a module, four `Use`s, and a hand-cleared fact

Today (`2-decisions.charter`, `3-distributions.charter`; 17 + 1 + 3 lines, and the same again for each kind of decision):

```
Module poll(subject) {
  Fact yes Identified by person * subject
  Act vote Actor person Related to subject
    Holds when member(person)
    Creates yes()
  Fact majority Identified by subject
    Derived from majority(yes.subject)
      When Sum(Foreach capital: capital.int When yes(capital.person, yes.subject)) * 2 > total-capital.int
  Fact three-quarters Identified by subject
    Derived from three-quarters(yes.subject)
      When Sum(Foreach capital: capital.int When yes(capital.person, yes.subject)) * 4 >= total-capital.int * 3
  Fact unanimous Identified by subject
    Derived from unanimous(yes.subject)
      When Not(Exists person: member(person) && Not(yes(person, yes.subject)))
}
Use poll(usd) As payout
Power distribute Actor company Related to usd
  Holds when True
  Valid when payout-majority(usd) && usd <= cash.usd
  …
  Terminates (Foreach person: payout-yes(person, usd))
```

Proposed, does not parse today:

```
Power distribute Actor company Related to usd
  Decided by member Weighted by capital More than 1/2
  Valid when usd <= cash.usd
Power admit Actor company Recipient candidate
  Decided by Every member
Amend first-amendment Actor company
  Decided by member Weighted by capital At least 3/4
```

with the scenario phrase `Iris approves distribute(Tidewater, 100001).` (a vote names the act instance it approves),
and the approval consumed when the act takes effect.

Saves: the 16-line module, 4 `Use` lines, the types `matter`, `amendment`, `candidate` and their atoms, 8 unused derived
facts, the `Terminates (Foreach person: payout-yes(…))` line, and four names per decision (`payout-yes`, `payout-vote`,
`payout-majority`, …) that the reader must connect to `distribute` by convention. Concepts no longer needed: modules,
`Derived from` versus `Holds when` over a non-enumerable type (hard item 2), `Sum(Foreach … When …)`. Occurrences: 5
decided acts (`distribute`, `admit`, `sell-business`, `dissolve`, `first-amendment`), 4 polls. It also makes 2.2, 2.3
and 7.1 nameable from the article that states them: the threshold is a clause of the act.

### 2. Reading a `Function` at a key: `capital(seller)`

Today (`4-sale.charter`, `5-withdrawal.charter`, `A-first-amendment.charter`):

```
Creates capital(buyer, Sum(Foreach capital: capital.int When capital.person == seller)), capital(seller, 0)
Valid when (Exists offered: offered.seller == seller && Held(offered) For 30 && usd >= offered.usd)
```

Proposed, does not parse today:

```
Creates capital(buyer, capital(seller)), capital(seller, 0)
Valid when Held(offered(seller)) For 30 && usd >= offered(seller)
```

A `Function` applied to its first component alone is its value (and, as a condition, "has a value"). Saves about 45
characters per use and the idea that a lookup is a `Sum` over one row. Occurrences: 4 `Sum(… When … == x)` lookups and
4 `Exists offered: offered.seller == seller && …`. Three natural spellings are accepted today and are silently false
(hard item 4).

### 3. Pro rata as one word, with the remainder

Today (`3-distributions.charter`; the same pair again in `6-dissolution.charter`, plus `Var total-capital … Derived from`
in Article 1 to make it bearable):

```
Creates (Foreach capital: paid(capital.person, MulDivRound(usd, capital.int, total-capital.int, Floor)))
      , cash(cash.usd - Sum(Foreach capital: MulDivRound(usd, capital.int, total-capital.int, Floor)))
```

Proposed, does not parse today:

```
Creates paid(person, ProRata(usd, capital, Floor)), cash(cash - ProRata.total)
```

or, smaller: `ProRata(usd, capital, Floor)` as a term meaning `MulDivRound(usd, capital(person), Sum(capital), Floor)`
for the `person` in scope. Saves one of every two lines, the helper `total-capital` (2 lines), and the reader no longer
has to check that numerator and denominator are the same thing in all six places. Occurrences of
`MulDivRound(x, capital.int, total-capital.int, Floor)`: 6, plus 2 in the buy-out price.

### 4. Money as the weight of a ratio

Today (`1-members.charter`), because of hard item 1:

```
Function capital Identified by person * int
+capital(Iris, 50000). +capital(Jonah, 30000). +capital(Kemal, 20000).
```

Proposed, rejected today with CHR012:

```
Function capital Identified by person * usd
… MulDivRound(usd, capital.usd, total-capital.usd, Floor)
```

`MulDivRound(x, num, den, r)` should accept `num` and `den` of the same dimension (the ratio is dimensionless), and
`Money / Money` of one currency should be an `Int`. Saves nothing in lines; it removes a lie (the contributions are
dollars) and a unit trap (capital is in whole dollars, everything else in cents). Occurrences: 1 type, every formula.

### 5. An `Amend` that changes one clause of a rule says only that clause

Today (`A-first-amendment.charter`): the amendment deletes "less ten percent", and the program restates the power.

```
Amend first-amendment Actor company
  Repeals buy-out
  Installs {
    Power buy-out Actor company Recipient person
      Holds when True
      Valid when Held(withdrawing(person)) For 90
      Creates buyout-due(company, person, MulDivRound(book-value.usd,
                  Sum(Foreach capital: capital.int When capital.person == person), total-capital.int, Floor))
            , capital(person, 0)
      Terminates member(person), withdrawing(person)
  }
  Holds when True
  Valid when amendment-three-quarters(FirstAmendment)
```

Proposed, does not parse today:

```
Amend first-amendment Actor company
  Replaces 5.2 "less ten percent" In buy-out
    Creates buyout-due(company, person, ProRata(book-value, capital, Floor))
```

i.e. `Replaces <rule> <clause…>` keeps every clause of the rule not restated. Saves 6 of 13 lines here and, more to the
point, the reader no longer diffs two nine-line powers by eye to find what changed. Occurrences: 1 (every `Amend` that
is not a pure repeal). Related defect: the installed rule is not checked for provenance (tool defect 2).

### 6. The amendment procedure is stated once, for every `Amend`

Today: 7.1 has no rule in `7-amendment.charter`; each `Amend` carries
`Valid when amendment-three-quarters(FirstAmendment)` and must remember to. A second amendment that forgot the line
would be valid on anyone's say-so and `check` would pass.

Proposed, does not parse today (in `7-amendment.charter`):

```
Every Amend Decided by member Weighted by capital At least 3/4
```

Saves one line per `Amend`, lets Clause 7.1 name a rule in its own article (the article then checks alone), and makes
"an amendment made without that vote has no effect" true of amendments nobody has written yet. Occurrences: 1 `Amend`,
1 unnameable clause.

### 7. A consequence that happens when a period ends

Today (`5-withdrawal.charter`):

```
Power buy-out Actor company Recipient person
  Holds when True
  Valid when Held(withdrawing(person)) For 90
  Creates buyout-due(company, person, MulDivRound(…)), capital(person, 0)
  Terminates member(person), withdrawing(person)
```

Proposed, does not parse today:

```
After 90 of withdrawing(person)
  Creates buyout-due(company, person, …), capital(person, 0)
  Terminates member(person), withdrawing(person)
```

A rule that takes effect by lapse of time, stamped at the lapse. Saves the invented actor, `Holds when True`, and
fixes the sixty-day deadline, which today runs from whenever someone remembers to trigger `buy-out`. Occurrences: 1
here (also 4.2's closing at day 30).

### 8. "Is not required to" has no spelling

Today (`1-members.charter`), for "No member is required to contribute more":

```
Power call-capital Actor company Recipient person Related to usd
  Holds when True
  Valid when False
```

An act invented so that it can be denied. Proposed, does not parse today: `No Duty contribute Holder member Claimant company`.
Occurrences: 1.

## Tool defects

1. **A product with the same component twice is accepted and collapses.** `/tmp/cf-oa/rep/dup.charter`:
   ```
   Fact person Identified by Iris, Jonah, Wren
   Fact yes Identified by person * person
   Act vote Actor person Related to person
     Holds when True
     Creates yes()
   .
   vote(Iris, Wren).
   ?yes(Iris, Wren).
   ?!yes(Iris, Iris).
   ```
   Expected: an error at `person * person` (and at `Actor person Related to person`) asking for a decoration.
   Actual: no diagnostic; `charter run` shows `occurred act vote(person("Iris"),person("Iris"))` and
   `+yes(person("Iris"),person("Iris"))`; `?yes(Iris, Wren)` "holds"; `?!yes(Iris, Iris)` fails. With
   `Use poll(person) As admission` in my real files, every scenario still passed while `admission-vote(Iris, Wren)`
   meant `admission-vote(Iris, Iris)`. Workaround: `Placeholder candidate For person`.
2. **A rule declared inside `Installs { }` escapes the "every rule is named by a span" check (012.6).**
   `/tmp/cf-oa/rep/r.charter`: `Amend change … Installs { Power stop Actor p Holds when True Valid when True Creates off() }`
   with no span naming `stop` -> `coverage complete`. The same `Power stop` at top level (`r2.charter`) ->
   `error CHR029: provenance coverage is partial`. Expected: the installed rule needs a span. Workaround: none needed;
   I named the amendment itself in A.1.
3. **`#require` is not once-per-file for the file given on the command line.** `/tmp/cf-oa/cyc/`: `a.charter` =
   `Fact x Identified by A.` then `#require "b.charter".`; `b.charter` = `#require "a.charter".` then
   `Fact y Identified by x.` `charter check --deny-warnings a.charter` ->
   `./a.charter:1:1: warning CHR019: x is declared again`; a root that requires both is clean. Expected (011.7): once.
   Consequence: two articles that name each other's rules cannot both be checked alone.
4. **Silence where a rule can never fire.** `Fact carried Identified by usd Holds when <condition>` and
   `(Exists int: capital(member, int) && …)` are accepted and never true, because nothing asserts `usd(7)` or `int(51)`
   (004.7). This is the specified meaning, but the author gets no warning; CHR025 exists for the analogous binder over
   an act. Expected: a warning that the variable ranges over a primitive type with no held instances and naming the
   fix (`Derived from`, or bind the fact that carries the value). Workaround: `Derived from majority(yes.subject)`.
5. **One error, nineteen diagnostics.** A CHR012 in a declaration block is followed by a CHR010 "undeclared type" for
   every later phrase and scenario phrase (`t1.charter`: 1 real error, 18 consequences). Expected: the consequences
   suppressed or summarised.
6. (Known, counted.) Every resolve error reported `:1:0`, the first line of the block; with one block per article
   file that is always line 1 or 2 of the file.

## What a lay author would have guessed

- `Function capital Identified by member * usd`, because 1.2 says dollars. Rejected two steps later, in the formula.
- `capital(Iris)` for Iris's capital. CHR011.
- `Fact carried Identified by usd Holds when …` ("a distribution of this amount is carried when…"). Accepted, never true.
- `(Exists int: capital(member, int) && int * 2 > …)`. Accepted, never true.
- `Derived from yes.subject`. CHR012 with a message about `payout-majority`.
- `Use poll(person)`, `Fact yes Identified by person * person`. Accepted, means something else.
- A name with a digit (`holds-most2`). CHR004 about a missing `.`.
- That 7.1 would be one rule in Article 7. It is a `Valid when` on each `Amend`, somewhere else.
- That "by ordinary decision" on `distribute` would be a property of `distribute`. It is three names in two files.
- That a decision, once used, is used up. It is not: without the `Terminates (Foreach person: payout-yes(person, usd))`
  line, one vote authorises the same distribution any number of times.
