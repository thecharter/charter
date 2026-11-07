# PromissoryNote
## Size
English sentences: 15. Charter lines outside clause blocks and comments: 58. Clause-block lines: 20.
Case lines: 90 (7 scenarios). Declarations no sentence of the text refers to: 4 (`usd`, the carrier
type for the amount of a payment; `charged`, a counter of the periods whose interest is already
booked; `interest`, the booked part of what the text calls "the interest owing", which the rules
read as `interest-owing`; `fees-paid`, the other half of "late fees owing").

Known issues, counted: a span that is really a fact 2 times, and they are the two money terms of
the note (2.1, all three sentences on interest, is an unlinked `Definition`; so is 4.1 "the
borrower owes a late fee of five percent"); `Approved` stamps 8; `Holds when True` once;
`Count(Foreach …)` 3 times; amounts in cents 2 in the root and 38 in the cases; a failed claim
reported on the scenario's first line every time (the worst case: "phrase 34" of the
twelve-month scenario, reported at line 5).

## What was hard
In the order I met them. The first four are the first four things I wrote.
1. **The k-th instalment falls due after k periods.**
   `Fact fallen-due Identified by instalment Holds when Held(lent()) For 30 * instalment` gives
   `error CHR012: cannot use an integer where a duration is needed`. With
   `Param period : Duration = 30` and `For period * instalment` it is accepted. A literal becomes a
   duration only when it stands alone.
2. **Interest for the days gone by.** The natural rule for "six percent a year" is principal × 6% ×
   days ÷ 365. `MulDivRound(principal.usd, 6 * (Current Time - started), 36000, Floor)` gives
   `error CHR012: cannot use a duration where an integer is needed`. There is no way from a
   duration or an instant to a number, so interest cannot be computed from elapsed time at all.
   Also tried: `Current Time / 30` gives `CHR012: cannot use an instant in `/` (D16: a time is
   never scaled)`; `Current Time >= 30 * instalment` gives `CHR012: cannot use an integer where a
   time is needed`.
3. **Something that happens every thirty days.** `Event add-interest Every period Creates …` gives
   `error CHR004: expected `.` to end the phrase but found atom `Every``. Nothing happens when the
   clock moves, so "at the end of every thirty days … is added" cannot be an event unless every
   scenario fires it by hand next to each `@`. I derived it instead: count the periods that have
   passed (`fallen-due`), subtract the periods already booked (`charged`), multiply by a period's
   interest on the present principal. It is exact only because principal changes only in `pay`,
   which books the interest at the same moment. Four declarations and two effect lines for one
   sentence, and the sentence itself stays an unlinked `Definition`.
4. **A derived amount.** `Fact dbl Identified by usd Derived from p.usd + p.usd` gives
   `error CHR012: cannot use Money(USD, 2) where an instance of dbl is needed`. The same line over
   `Int` is accepted. Workaround: name the type again, `Derived from dbl(p.usd + p.usd)`.
5. **`.usd`.** I began with `Var principal Identified by usd` and `principal.usd`, as LivingTrust
   does and as the brief says. Declaring the value over the domain, `Var principal Identified by
   Money(USD, 2)`, lets every rule say `principal`. The same holds for a derived fact. It removed
   20 `.usd` from the derived amounts in this file and 3 from HomePurchase. An act's amount still needs the named type:
   `Act pay … Related to Money(USD, 2)` gives `error CHR003: expected a type identifier (lowercase)
   but found atom `Money``.
6. **A late fee that survives payment.** First version: `Fact late Identified by instalment Holds
   when Violated(instalment-due())`. The fee appears on day 40 and disappears when the instalment
   is paid on day 45, because the duty is gone; `fees-owing` then goes to minus $43.03
   (`query failed: ?fees-owing(0)`, `query failed: ?late(1)`, `query failed: ?owing(0)`). Nothing
   can be made to happen when a deadline passes, so the only place to record "this one was late"
   is the next act anyone performs. `pay` now carries
   `(Foreach instalment: late(instalment) When Violated(instalment-due()))`.
7. **The grace period counted from the wrong day.** With `Due within grace` on the derived duty,
   `@ 30. @ 45.` gives the fee and `@ 45.` alone does not: the duty is stamped when a phrase first
   derives it, so a scenario that does not stop on day 30 starts the ten days on day 45
   (`[scenario paid-off-in-one-go, phrase 2]:67: query failed: ?owing(1009303)`). I replaced it
   with `Violated when Held(lent()) For period * instalment + grace`, which counts from the loan.
   `lib/README.md` says "Stamps are per derivation"; it does not say that the verdict then depends
   on which days the scenario happens to mention.
8. **`Held` of a derived fact inside a derivation is always false.** See Tool defects 1. I met it
   trying `Bool late Holds when Held(due()) For 10`.
9. **Application of payments.** "Applied first to late fees, then to interest, and then to
   principal" is one sentence and six conditional effects, because there is no `min`.
   `Creates fees(fees - Min(usd, fees))` gives `error CHR003: expected `Foreach` but found
   identifier `usd``.

Where the lack of a calendar hurt, every place:
- "Monthly" became "every thirty days". A real note says "on the first of each month".
- "Six percent a year" became a twelfth of 6% per thirty days: a 360-day year, and twelve periods
  end five days before the anniversary. Interest on actual days cannot be written (2 above).
- Interest "added at the end of every thirty days" has no event to hang on (3 above).
- Periods must be an enumerated type, `Fact instalment Identified by 1..12`, so the program stops
  charging interest after day 360. With no payments at all: `@ 390. ?interest-owing(65000).`
  fails; it is still 60000. The text says "every thirty days", without end. I could not fix this
  without an unbounded count of periods, which needs a number from the clock.
- A late fee cannot attach when the grace period ends (6 above).
- `Due within` on a duty derived from the clock depends on the scenario's steps (7 above).
- "Within ten days after it falls due" is breached at `@ 40`, so a payment on the tenth day is
  late (as in HomePurchase).
- The twelve payment days in the case file (30, 60, … 360) are worked out by hand; there is no
  "one period later" and no loop.
- No business days: an instalment due on a Sunday is due on the Sunday.

## Improvements (most valuable first)
1. **Apply a payment to a list of balances in order.** As written:
   ```
   , fees-paid(fees-paid + usd)                   When usd <= fees-owing
   , fees-paid(fees-paid + fees-owing)            When usd >  fees-owing
   , interest(interest-owing)                     When usd <= fees-owing
   , interest(fees-owing + interest-owing - usd)  When usd >  fees-owing && usd <= fees-owing + interest-owing
   , interest(0)                                  When usd >  fees-owing + interest-owing
   , principal(owing - usd)                       When usd >  fees-owing + interest-owing
   ```
   Proposed, does not parse today:
   ```
   Act pay Actor borrower Recipient lender Related to usd
     Holds when lent() && usd <= owing
     Applies usd To fees, interest, principal
   ```
   Saves 5 lines and all the case analysis; the reader sees the order the clause states. Failing
   that, a two-argument `Min(a, b)` and `Max(a, b)` would bring it to three lines. Occurs once
   here; `lib/oracle_feed.charter` writes the same thing as two `Derived from` per tier.
2. **A balance that grows with time.** As written:
   ```
   Fact fallen-due Identified by instalment
     Holds when Held(lent()) For period * instalment
   Var interest Identified by Money(USD, 2)
   Var charged Identified by Int
   Fact interest-owing Identified by Money(USD, 2)
     Derived from interest-owing(interest + MulDivRound(principal, 6, 1200, NearestEven)
                    * (Count(Foreach instalment: instalment When fallen-due(instalment)) - charged))
   ```
   plus `charged(Count(…))` and three `interest(…)` effects in `pay`. Proposed, does not parse
   today:
   ```
   Var interest : Money(USD, 2) = 0
   Every period Since lent()
     Creates interest(interest + MulDivRound(principal, 6, 1200, NearestEven))
   ```
   a rule the clock itself applies, once per period, in order, before the next phrase is judged.
   Saves 6 lines and the `charged` counter, removes the day-360 bug above, and gives clause 2.1 a
   rule to name. Occurs once here; Tenancy (`rent-falls-due`) and LivingTrust (`year-ends`) each
   fire a hand-made event for the same reason.
3. **A consequence of a missed deadline.** As written:
   ```
   Fact late Identified by instalment
     Holds when Violated(instalment-due())
   …
   , (Foreach instalment: late(instalment) When Violated(instalment-due()))     (in pay)
   ```
   Proposed, does not parse today:
   ```
   Duty instalment-due Holder borrower Claimant lender Related to instalment
     …
     On breach Creates late()
   ```
   Saves the effect smuggled into `pay` and the knowledge that a derived fact vanishes with its
   ground. Occurs once here; any agreement with a late fee, default interest or liquidated damages
   needs it.
4. **A deadline counted from a schedule, not from when the duty was first noticed.** As written:
   `Violated when Held(lent()) For period * instalment + grace` and
   `Held(lent()) For period * instalment + default-after`. Proposed, does not parse today:
   ```
   Duty instalment-due Holder borrower Claimant lender Related to instalment
     Falls due period * instalment After lent()
     Due within grace
   ```
   with `Due within` counted from the stated due time. Saves repeating the schedule in three
   places (it is in `fallen-due`, in `Violated when` and in `call-in`) and removes the step-
   dependent stamp. Occurs 3 times.
5. **Money and rates written as the text writes them.** As written:
   `Param loan : Money(USD, 2) = 1000000`, `Param regular : Money(USD, 2) = 86066`,
   `MulDivRound(principal, 6, 1200, NearestEven)`, `MulDivRound(regular, 5, 100, NearestEven)`,
   `pay(Elena, Marcus, 86066)`. Proposed, does not parse today:
   ```
   Param loan = $10,000.00
   Param regular = $860.66
   … 6% Of principal / 12 …        … 5% Of regular …
   pay(Elena, Marcus, $860.66).
   ```
   with one rounding rule declared once (`Rounding NearestEven`). Saves counting digits in 40
   places and reading `6, 1200` as "six percent, a twelfth". See Tool defects 2 for what the
   obvious spelling does today.
6. **A scenario step that repeats.** As written, ten lines of
   `@ 90. pay(Elena, Marcus, 86066).` … `@ 330. pay(Elena, Marcus, 86066).` Proposed, does not
   parse today: `Each 30 From 90 To 330 { pay(Elena, Marcus, $860.66). }`. Saves 9 lines.
7. **A prohibition.** As written: `Act charge-for-early-payment Actor lender Recipient borrower
   Holds when False`. Proposed, does not parse today:
   `Forbidden charge-for-early-payment Actor lender Recipient borrower`. Same length; it says what
   it is. Occurs once here and once in LivingTrust.

## Tool defects
1. `Held(e) For d` is always false inside a `Holds when` of a fact when `e` is itself derived.
   ```
   Bool lent
   Bool due Holds when Held(lent()) For 30
   Bool late Holds when Held(due()) For 10
   .
   +lent().
   @ 30.
   ?due().
   @ 40.
   ?Held(due()) For 10.
   ?late().
   @ 41.
   ?late().
   ```
   Expected: both `?late()` hold, since the query `?Held(due()) For 10` on the line before holds.
   Actual: `t9.charter:10: query failed: ?late().` and `t9.charter:12: query failed: ?late().`
   The same condition in an act's `Holds when` is judged correctly. Workaround: count from the
   base fact (`Held(lent()) For 40`).
2. A decimal amount is accepted and silently means a hundredth of it.
   ```
   Param loan : Money(USD, 2) = 10000.00
   .
   ?loan(10000).
   ?loan(1000000).
   ```
   Expected: an error, or ten thousand dollars. Actual: no diagnostic; `charter run` shows
   `+loan(10000)`, that is $100.00, and `check` reports "4 phrase(s) resolve": the `.` ended the
   declaration and `00` was accepted as a phrase of its own. Workaround: write cents.
3. A `Money` value does not convert to an instance of a `Money` type in `Derived from`, where an
   `Int` value does.
   ```
   Var n Identified by Int
   Fact twice Identified by Int Derived from n + n
   Fact usd Identified by Money(USD, 2)
   Var p Identified by usd
   Fact dbl Identified by usd Derived from p.usd + p.usd
   .
   ```
   Expected: accepted (010.4, "a value where an instance is needed meaning the instance of that
   value"). Actual: `m2.charter:1:0: error CHR012: cannot use Money(USD, 2) where an instance of
   dbl is needed`, reported at line 1 for a fault on line 5. Workaround: `Derived from dbl(…)`.
4. A duty derived from the clock with `Due within d` gives a verdict that depends on the phrases
   of the scenario, not on the history (What was hard 7). Reproduction: in `note.charter` replace
   the `Violated when` line with `Due within grace`; then `lend(Marcus, Elena). @ 30. @ 45.
   ?fees-owing(4303).` holds and `lend(Marcus, Elena). @ 45. ?fees-owing(4303).` fails. This is
   documented behaviour of stamps, so it may be a design defect and not a tool defect.
5. With several claims on one top-level line, a failure prints the whole line as the failed query
   (`t9.charter:7: query failed: @ 30. ?due(). @ 40. ?Held(due()) For 10. ?lawful mark("x").
   ?late().`), so the reader cannot tell which claim failed. Workaround: one claim per line.

## What a lay author would have guessed
- `Param loan : Money(USD, 2) = 10000.00`: accepted, and wrong by a factor of 100 (defect 2).
  `= $10,000.00` gives `error CHR001: unexpected character `$``.
- `Derived from fee(5% of regular)`: `error CHR010: undeclared type or placeholder `of regular``.
  `%` is the remainder operator and `of regular` is read as one two-word name.
- `Held(lent()) For 30 * instalment`: `CHR012`, as above.
- `Event add-interest Every period`: `CHR004`, as above.
- `Min(usd, fees)`: `CHR003: expected `Foreach``, as above.
- `Due within grace` for "within ten days after it falls due": accepted, and counts from the first
  day the scenario looks at, as above.
- `Fact late … Holds when Violated(instalment-due())` for "is late": accepted, and stops being
  true when the instalment is paid.
- `Fact fee2 …`: `error CHR004: expected `.` to end the phrase but found integer 2`. A name cannot
  end in a digit; the message does not say so.
