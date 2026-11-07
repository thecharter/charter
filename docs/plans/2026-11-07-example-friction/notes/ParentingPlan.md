# ParentingPlan

Files: `Examples/ParentingPlan/plan.md`, `plan.charter` (root), `1-schedule.charter`,
`2-holidays.charter`, `3-missed-time.charter`, `4-support.charter`, `5-relocation.charter`,
`6-changes.charter`, `cases/first-year.charter` (9 scenarios).
`charter check --require-provenance --deny-warnings plan.charter` ends
`ok   Examples/ParentingPlan/plan.charter: 10 phrase(s) resolve (30 declared types, 9 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/first-year.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp/cf-pp/mut`, `?!violated support-due(Daniel, Rosa, 1)` on day 7 flipped to `?violated` gave
`cases/first-year.charter [scenario support-is-due-by-the-fifth-with-three-days-of-grace, phrase 4]:68: claim failed: ?violated support-due("Daniel", "Rosa", 1)`.

## Size

English sentences: 15. Charter lines outside clause blocks and comments: 75. Clause-block lines: 25.
Case lines: 109. Declarations no sentence of the text refers to: 6 (`start`, a `Time` parameter
that exists so the clock can be turned into a number of days; `handover-day` and `rosa-week`, the
calendar done by hand; `month`, a number for each month so two unpaid months are two debts;
`resuming`, a one-day flag after a holiday; `usd`).

Known issues, counted in this example:

- A span cannot name a fact or event: 3 of 11 spans. 1.1 "The first week is Rosa's" is `rosa-week`
  and `+with(Rosa)`; 2.1 is two `+holiday-parent(…)` facts and two events; 4.1 "for each month" is
  the event `month-begins`.
- `Created by` could not be used either time it was wanted: `support-due` is created by an event
  that has no `parent` component (so the event says `Creates support-due(Daniel, Rosa, month)`),
  and `make-up-due` is created only when the handover is late. `Terminated by` worked twice.
- `Holds when True`: 3 (`give-move-notice`, `agree-to-change`, `order-support`).
- `parent == Daniel && other == Rosa` and the like: 5 comparisons, 1 literal pair in an effect.
- Clauses stamped per file: 6 runs of `tools/approve-clauses` for 9 clauses.
- An article file cannot pass `check --require-provenance` alone (`CHR029 … coverage partial`),
  because `Document` is in the root. Same in the `LivingTrust` pilot.
- Money in cents: 1 parameter, 15 literals in the case file.
- Diagnostics at the wrong line: `1-schedule.charter:2:1` for an `Overridden by` on line 13.
- `Power` whose `Valid when` repeats `Holds when`: 0 of 1.

### Every place the lack of a calendar hurt

1. **Alternating weeks.** `Holds when (Current Time - start) - ((Current Time - start) / 14) * 14 < 7`.
   There are no weeks and no remainder on a duration, so "which week is it" is long division by
   hand. It also needs `Param start : Time = 0`, because `Current Time - 0` is a time, not a
   number of days.
2. **The first day of a week.** The same expression again with 7 and `< 1`.
3. **"Sunday" could not be said.** The text I wrote says "the first day of a parent's week"
   because nothing in the language names a day. Day 0 being a handover day is a comment in the
   case file.
4. **Months.** "For each month" is `Event month-begins Related to month`, fired by the scenario
   by hand at day 0 and day 30, with the month number supplied by hand. Nothing ties the event to
   the clock: a scenario that fires it on day 3 moves the due date, and one that forgets it makes
   Daniel owe nothing.
5. **"The fifth day of the month"** is `Due within 5` and is right only if `month-begins` is
   fired on the first. The grace period is `5 + grace`; the text's two dates (the fifth, and three
   days later) are one number in the program, so "late but not in breach" cannot be asked.
6. **Holidays have no dates.** "The winter holiday" is whatever lies between `holiday-begins(Winter)`
   and `holiday-ends(Winter)` in a scenario. A real plan gives dates, and alternates holidays by
   even and odd years; I did not write that sentence because it cannot be said.
7. **The day a holiday ends** needed `Creates resuming() For 1`, a flag that expires, so that
   handing Mia back that day is not late.
8. **Counting missed days.** A real plan says make-up time is "the same number of days". There
   is `Held(f) For d` to test a length of time and nothing to read one, so the days a duty stayed
   violated cannot be counted. My 3.1 says only "owes make-up time"; that is a distortion of the
   agreement caused by the language.
9. **A scenario that skips a day gets a different answer** when a duty derived from the clock
   uses `Held` (Tool defects 2). 7 phrases of the 109 case lines exist only to fire calendar events.

## What was hard

1. **Whose week it is, from the clock.** First `Holds when ((Current Time - 0) / 7) % 2 == 0`:
   `a2.charter:1:0: error CHR012: cannot use an instant in `/` (D16: a time is never scaled)`.
   Then with `Param start : Time = 0`, `((Current Time - start) / 7) % 2 == 0`:
   `a6.charter:1:0: error CHR012: cannot use a duration where an integer is needed`.
   Third attempt, no `%`: `(Current Time - start) - ((Current Time - start) / 14) * 14 < 7`. Passes.

2. **The override declared in the article that states it.** `Overridden by holiday-time` on the
   article 1 duty: `1-schedule.charter:2:1: error CHR010: undeclared type holiday-time in `Overridden by``
   followed by 8 cascading `CHR010` in the other articles. The text says "the holiday schedule
   overrides the regular schedule" in article 2; the language wants it written on the overridden
   duty, in article 1, which cannot see article 2. `Extend Duty regular-week Overridden by
   holiday-time` in article 2 works.

3. **A duty derived from the clock, with a one-day tolerance.**
   `Violated when with(parent) && Held(regular-week()) For 1`. Passed when the scenario stopped
   at day 7 and failed when it went straight to day 9:
   `[scenario a-skipped-clock, phrase 2]:18: claim failed: ?violated regular-week("Rosa", "Daniel")`.
   The duty is stamped when first observed, not when it became true. I replaced `Held` with the
   clock arithmetic of `handover-day`.

4. **`Overridden by` matches by component name.** Written first:
   `Duty holiday-time Holder parent Claimant other` ("`parent` hands Mia to `other`, whose holiday
   it is"), the same shape as `regular-week`. Daniel's holiday then did not excuse Daniel in Rosa's
   week: `[scenario the-holiday-overrides-the-regular-week, phrase 8]:39: claim failed: ?!violated regular-week("Daniel", "Rosa")`.
   The two duties run in opposite directions, so the override matched `holiday-time(Daniel, Rosa)`,
   which is Rosa's holiday. The fix is to declare the second duty with the names swapped,
   `Duty holiday-time Holder other Claimant parent`. No diagnostic; a reader has to notice the swap.

5. **Two unpaid months were one debt.** With `Event month-begins Creates support-due(Daniel, Rosa)`,
   a second month re-creates an instance that already holds, and one payment clears both:
   `[scenario two-months-unpaid-are-two-debts, phrase 5]:79: query failed: ?support-due("Daniel", "Rosa")`.
   Fix: `Fact month Identified by Int` threaded through the event, the duty, the payment and every
   scenario line.

6. **Handing Mia back on the day a holiday ends created a make-up debt.** The overridden duty is
   violated the instant the override ends. Fix: `Creates resuming() For 1` and, because `Extend`
   can only add an alternative to `Violated when`, `Conditioned by Not(resuming())`, which removes
   the duty for that day when I only wanted to excuse it.

7. **The court order as a `Finding`.** `Finding order-support Actor court Related to usd … Creates
   support(usd)` with no `Resolves` parses and behaves exactly as a `Power`. With a `Resolves` it
   needs an `Evidenced` fact, and then the parents' agreement alone establishes it
   (`/tmp/cf-pp/b1.charter`: after one `agree-change … Supports approved(usd)`,
   `claim failed: ?!valid change-support(Rosa, 50000)`). "Established" by unopposed evidence and
   "ordered by the court" are the same status, so "only by order of the court" cannot be written
   with a finding. I used a `Power`. Honest verdict: `Finding` did not fit an order; it fits a
   disputed fact (HealthcareDirective).

8. **"A parent is not the court."** `Power order-support Actor court … Valid when True` let Rosa
   order a change (Tool defects 1). Workaround: `Valid when court == FamilyCourt`.

`Overridden by`, once the names matched, is one line and does what 2.2 says, including reporting
the violation again when the holiday ends. Deadlines (`Due within 60`, `Due within 5 + grace`,
`Held(noticed-move(parent)) For 60`) each worked at the first attempt.

## Improvements (most valuable first)

### 1. A recurring duty

Today:

```
Fact month Identified by Int
Event month-begins Related to month
  Creates support-due(Daniel, Rosa, month)
Duty support-due Holder parent Claimant other Related to month
  Due within 5 + grace
  Terminated by pay-support
Act pay-support Actor parent Recipient other Related to month, usd
  Valid when usd == support
```

and in every scenario `month-begins(1).` … `@ 30. month-begins(2).` … `pay-support(Daniel, Rosa, 1, 65000).`

Proposed, does not parse today:

```
Duty support-due Holder Daniel Claimant Rosa
  Every 30
  Due within 5 + grace
  Terminated by pay-support
Act pay-support Actor parent Recipient other Related to usd
  Valid when usd == support
```

`Every d` creates a new instance each period from the clock, keeps instances of different periods
apart, and discharges the oldest first. Saves the `month` type, the event and its effect (3 lines),
the `month` argument in 3 declarations and 19 scenario lines, 4 hand-fired events, and the two
silent failures (one debt for two months; a due date that moves with the scenario). With a
calendar it would read `Every month`. Occurs once here; `Tenancy` T.1 and `LivingTrust` 4.2 are the
same.

### 2. Taking turns

Today:

```
Param start : Time = 0
Bool rosa-week
  Holds when (Current Time - start) - ((Current Time - start) / 14) * 14 < 7
Bool handover-day
  Holds when (Current Time - start) - ((Current Time - start) / 7) * 7 < 1
Duty regular-week Holder parent Claimant other
  Holds when rosa-week() && parent == Daniel && other == Rosa
           , Not(rosa-week()) && parent == Rosa && other == Daniel
  Violated when with(parent) && Not(handover-day())
```

Proposed, does not parse today:

```
Duty regular-week Holder parent Claimant other
  Turns Rosa, Daniel Every 7
  Violated when with(parent) && Held(regular-week()) For 1
```

`Turns a, b Every d` makes the duty hold with each listed claimant in turn for `d`, every other
party holding it, stamped at the turn's first instant. Saves 7 lines, the `start` parameter, two
long divisions, and four name comparisons. The smaller step, if this is too much: allow `%` on a
duration and give the days since genesis a name, so the line is `Elapsed % 14 < 7`. Occurs twice
(the week, the handover day).

### 3. An override written on the overriding rule, by instance

Today (the names on the second duty are swapped so that matching by name comes out right, and the
override sits in an `Extend` of the other duty):

```
Duty regular-week Holder parent Claimant other
Duty holiday-time Holder other Claimant parent
Extend Duty regular-week
  Overridden by holiday-time
```

Proposed, does not parse today:

```
Duty holiday-time Holder parent Claimant other
  Overrides regular-week(other, parent)
```

The override is stated where the text states it ("the holiday schedule overrides the regular
schedule"), and says which instance it excuses. Saves the `Extend`, the swapped declaration, and
the failure of item 4, which gives no diagnostic. Occurs once.

### 4. How long something has lasted, as a value

Today the make-up duty has no amount:

```
Extend Act hand-over
  Creates make-up-due(parent, other) When Violated(regular-week(parent, other)) || Violated(holiday-time(parent, other))
```

Proposed, does not parse today:

```
Duty make-up-due Holder parent Claimant other Related to duration
Extend Act hand-over
  Creates make-up-due(parent, other, Overdue(regular-week(parent, other)))
```

`Overdue(d)` is how long the duty `d` has been violated; `Age(f)` how long `f` has held. Saves
nothing in lines; it lets the sentence "the same number of days" be written at all. Occurs once.

### 5. Excusing, not removing, from another article

Today:

```
Extend Duty regular-week
  Overridden by holiday-time
  Conditioned by Not(resuming())
```

Proposed, does not parse today:

```
Extend Duty regular-week
  Excused when resuming()
```

`Excused when c`: the duty holds and is not violated while `c`. Today `Extend … Violated when`
only adds an alternative, so a later article can make a duty stricter and never more lenient;
`Conditioned by` makes the duty disappear, so `?regular-week(Daniel, Rosa)` is false on a day in
Rosa's week. Occurs once.

### 6. A due date and a breach date

Today `Due within 5 + grace` for "due by the fifth; a payment within three more days is not a
breach". Proposed, does not parse today:

```
Duty support-due …
  Due within 5
  Grace 3
```

with `?late support-due(…)` true from day 5 and `?violated` from day 8. Saves no lines; restores
a distinction the text makes and the sum erases. Occurs once.

### 7. A named party where a role is fixed

Today `Creates support-due(Daniel, Rosa, month)` inside an event, and
`parent == Daniel && other == Rosa` twice. Proposed, does not parse today:
`Duty support-due Holder Daniel Claimant Rosa`. Saves the literal pair in the effect and lets
`Created by` work. Occurs 3 times.

## Tool defects

1. **An actor outside the declared type performs the act validly.**

   ```
   Fact court Identified by FamilyCourt
   Bool ordered
   Power order Actor court
     Holds when True
     Valid when True
     Creates ordered()
   .
   ?valid order(Nobody).
   order(Nobody).
   ?ordered().
   ```

   Expected: an error that `Nobody` is not a `court`, or at least `valid: no`. Actual:
   `occurred act order(court("Nobody"))   lawful: no   valid: yes`, then `+ordered()`; both claims
   hold; `check --deny-warnings` reports 0 warnings. Spec 003.8: "an element outside the constraint
   is not an instance". (`/tmp/cf-pp/a3.charter`.) Workaround: `Valid when court == FamilyCourt`.

2. **A derived fact is stamped when first observed, so `Held` depends on which days the scenario
   visits.**

   ```
   Param start : Time = 0
   Bool second-week
     Holds when Current Time - start >= 7
   Bool a-day-into-it
     Holds when Held(second-week()) For 1
   .
   @ 9.
   ?second-week().
   ?a-day-into-it().
   ```

   Expected: both hold on day 9. Actual: the second query fails; with `@ 7.` before `@ 9.` it
   holds. No diagnostic. `lib/README.md` mentions it as a convention ("must observe the clock
   when `f` becomes true"); for a deadline it is a wrong answer. (`/tmp/cf-pp/s1.charter`.)
   Workaround: compare the clock directly; never `Held` on a fact derived from time.

3. **`Finding` with no `Resolves` is accepted** and is then a `Power` under another name
   (`/tmp/cf-pp/a1.charter`). Spec 005.11 gives `Resolves` as part of the form. Expected: an error
   or a warning. Minor.

4. **A forward reference in `Overridden by` is reported at line `2:1`** of the file (the duty's
   clause is on line 13) and produces 8 follow-on `CHR010` errors in files that only `#require` it.

5. **Re-creating a duty that already holds is silent.** `month-begins()` twice creates one
   `support-due(Daniel, Rosa)`; the run shows no effect line for the second event and no warning
   that an obligation was dropped. Expected: at least a note in `run`, or a warning from `check`
   that a `Created by`/`Creates` duty has no component to tell two occurrences apart.

## What a lay author would have guessed

- `((Current Time) / 7) % 2 == 0` for "alternating weeks". Rejected twice, for two different reasons.
- `Overridden by holiday-time` on the regular duty in article 1. Rejected: article 2 is not visible.
- Two duties with the same shape, `Holder parent Claimant other`, and `Overridden by`. Accepted;
  excuses the wrong parent.
- `Held(regular-week()) For 1` for "more than a day into the other parent's time". Accepted;
  right or wrong depending on whether the scenario stops on day 7.
- `Event month-begins Creates support-due(Daniel, Rosa)` for "each month". Accepted; two months
  owed look like one.
- `Finding` for a court order. Accepted without `Resolves`; means nothing more than `Power`.
- `Actor court` as enough to say "only the court". Accepted; anyone can order.
- `Due within 5` for "by the fifth". Right only by the convention that the event fires on the first.
