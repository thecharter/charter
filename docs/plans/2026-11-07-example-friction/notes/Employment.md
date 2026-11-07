# Employment
## Size
English sentences: 17. Charter lines outside clause blocks and comments: 79. Clause-block lines: 27.
Case lines: 113 (10 scenarios, 48 claims; every claim was flipped in a `/tmp` copy and every flip failed).
Declarations no sentence of the text refers to: 4 (`party`, `usd`, `month`, `released-in-time`).

- `party` exists so that one `sign` act can have either side as its actor; both names are then
  declared a second time as `employer` and `employee`.
- `usd` exists so that an act can carry an amount.
- `month` exists because the salary duty needs a different instance for each month.
- `released-in-time` exists because "within twenty-one days after the termination" cannot be asked
  later; it has to be recorded at the moment of signing.

Known issues, counted: span cannot name a fact, parameter or event, 3 (2.1 salary, 3.1 cause, 3.3 the
exception); `Holds when True`, 2; `Valid when` repeating `Holds when`, 2; `Created by` needing
components by name, 1 (`month-ends`); diagnostic at the first line of the block, 1 (reported `1:0`
for line 86, then 21 follow-on CHR010); failed claim reported at the scenario's first line, 2;
no calendar, 2 ("each month", "twelve months").

## What was hard
1. **Signing by both sides.** First attempt, two acts of one name, one per role:
   `Act sign Actor employer Creates signed()` and `Act sign Actor employee Creates signed()`.
   `warning CHR019: sign is declared again; the new declaration replaces the earlier one`.
   Second attempt, a union: `Fact party Identified by employer, employee`.
   `3:34: error CHR004: expected `.` to end the phrase but found `,``. Third attempt, which stands:
   declare `party` with both names, then `employer` and `employee` again with one name each.
2. **`Not(staff())`.** `signed()`, `consented()` and `dismissed()` all take implicit arguments, so I
   wrote `staff()` for "is on the staff". `e1.charter:1:0: error CHR018: staff is a primitive type
   and takes exactly one positional argument`. The line was 86. The spelling that works is the bare
   variable, `Not(staff)`.
3. **"Within twenty-one days after the termination", attempt one.** I wrote the window into the
   derived fact: `Default released-in-time Holds when released() && Not(Held(dismissed()) For release-window)`.
   It passed every claim I had written, and was wrong: `Held` is asked now, so on day 21 the
   severance already earned stops being earned and the derived duty disappears unpaid. Nothing
   reported it. I found it by reading, then moved the test into the act's effect.
4. **Attempt two.** `Creates released(), released-in-time() When Not(Held(dismissed()) For release-window)`.
   `[scenario leaving-without-notice-…, phrase 8]:43: query failed: ?!severance-due("Harborlight", "Nadia")`.
   An employee who was never dismissed earned severance: `Held(x) For n` is false when `x` does not
   hold, so its negation is true. The line needs `dismissed() &&` in front.
5. **A span naming the exception.** `Norm "A termination for cause carries no severance." => for-cause`.
   `FAIL 3.3: spans name undeclared rules: for-cause`. `for-cause` is the `Exception` that says
   exactly this. The span now names `dismiss, severance-due`, which say it less directly.
6. **A salary every month.** `Event month-ends` with `Created by month-ends` on the duty:
   `error CHR027: `Created by month-ends` on salary-due: the component employer of salary-due is
   not a component of month-ends, so month-ends cannot bind it`. Worked round with an effect on
   the event, `Creates salary-due() When employed()`, which binds the parties as free variables.
   A second month while the first is unpaid re-creates the same instance, so the duty needed a
   `month` component and the event a serial number supplied by hand (`month-ends(1)`).

Things that worked first time and are worth knowing: a duty may be derived
(`Duty severance-due … Holds when severance-earned()`), its deadline runs from the first derivation,
and `Terminated by` discharges it. A short payment is void without any extra rule
(`Valid when usd == salary`).

## Improvements (most valuable first)

1. **Say "within N days of X" about an act.** Occurs 1 time here; 3 lines and one trap each.
   Today:
   ```
   Bool released-in-time
   Act sign-release Actor employee Recipient employer
     Holds when dismissed()
     Creates released(), released-in-time() When dismissed() && Not(Held(dismissed()) For release-window)
   Bool severance-earned
     Default timely-release Holds when released-in-time()
   ```
   Proposed, does not parse today:
   ```
   Act sign-release Actor employee Recipient employer
     Holds when dismissed()
     Creates released()
   Bool severance-earned
     Default timely-release Holds when released() Within release-window Of dismissed()
   ```
   `a Within d Of b` compares the two stamps: both hold and `a` was established less than `d` after
   `b`. Saves one declaration and one conditional effect, and removes both wrong versions above
   (items 3 and 4 of "What was hard"), neither of which the tool can catch.

2. **A clause should not be typed twice.** 11 clauses, 15 spans, 27 lines; every character of the
   English is retyped from `employment.md`, where each clause already begins with its number.
   Today:
   ```
   Clause 3.3 Approved "f405e0e4b1322771aaaed972d7603b4b5c513b169366ce46e268994c091a8c9a"
     Norm "A termination for cause carries no severance." => dismiss, severance-due
   ```
   Proposed, does not parse today:
   ```
   Clause 3.3 => dismiss, severance-due
   Clause 1.3 Sentence 1 => give-notice, leave
              Sentence 2 => leave
   ```
   The text is read from the paragraph numbered `3.3` in the document; the approval moves to a
   lock file that `charter approve` writes. Saves about 1,900 retyped characters and 11 digests
   (704 characters) in this file, and the author no longer needs to know about leading spaces in
   the second span (`" Leaving without…"`).

3. **A debt is the commonest duty and takes three declarations.** 3 times here (salary, severance,
   expenses). Today:
   ```
   Duty severance-due Holder employer Claimant employee
     Holds when severance-earned()
     Due within 10
     Terminated by pay-severance
   Act pay-severance Actor employer Recipient employee Related to usd
     Valid when usd == salary * 2
   ```
   Proposed, does not parse today:
   ```
   Duty severance-due Holder employer Claimant employee
     Holds when severance-earned()
     Owes salary * 2
     Due within 10
   ```
   `Owes` declares the amount; the discharging act is `pay severance-due(usd)`, valid when the
   amount is at least what is owed. Saves 2 lines and one name per debt, and the `usd` fact.

4. **A duty that recurs.** 1 time. Today:
   ```
   Fact month Identified by Int
   Event month-ends Related to month
     Creates salary-due() When employed()
   Duty salary-due Holder employer Claimant employee Related to month
     Due within 5
     Terminated by pay-salary
   ```
   Proposed, does not parse today:
   ```
   Event month-ends
   Duty salary-due Holder employer Claimant employee
     Created by each month-ends When employed()
     Due within 5
     Terminated by pay-salary
   ```
   `each` makes a fresh instance per occurrence, numbered by the tool. Saves the `month` type and the
   serial number the author invents: `month = N` is written 12 times in the cases.

5. **A span should be able to name a `Default`, an `Exception`, a `Param` or a derived fact.**
   3 times. Today: `Norm "A termination for cause carries no severance." => dismiss, severance-due`
   and `Definition "The salary is six thousand dollars a month."` with no link at all, so changing
   `Param salary` invalidates no approval. Proposed, does not parse today:
   `Norm "A termination for cause carries no severance." => for-cause` and
   `Definition "The salary is six thousand dollars a month." => salary`.
   Without it `Default`/`Exception` loses its point: the reason to name the rule is to cite it.

6. **Name each party once.** Today:
   ```
   Fact party Identified by Harborlight, Nadia
   Fact employer Identified by Harborlight
   Fact employee Identified by Nadia
   ```
   Proposed, does not parse today: `Fact party Identified by Harborlight As employer, Nadia As employee`.
   Saves 2 lines and the same name written in two places. It is worth the three lines today:
   because each role has exactly one member, every rule and every case can leave the parties out
   (`dismiss().`, `?violated salary-due(month = 1).`). The first version of the cases wrote
   `Harborlight, Nadia` 49 times in 113 lines.

7. **Positional arguments after the implicit parties.** `pay-salary(1, 600000).` gives
   `error CHR011: pay-salary has 4 component(s), 2 given`, so leaving out the parties forces every
   remaining argument to be named: `pay-salary(month = 1, usd = 600000)`. Proposed, does not parse
   today: positional arguments fill the components that have more than one possible value, in
   order. 29 applications in the cases are written in the named form for this reason.

8. **`Valid when` that repeats `Holds when`.** 2 times (`dismiss`, `leave`). Today:
   ```
   Power dismiss Actor employer Recipient employee
     Holds when employed()
     Valid when employed()
   ```
   Proposed, does not parse today: `Power dismiss … Valid when employed()` alone, an act being
   lawful only if valid unless it says more. Saves 2 lines.

9. **Money written as money, durations with a unit.** `Param salary : Money(USD, 2) = 600000`,
   `usd = 1200000`, `Due within 5`. First guesses `Due within 5 days` and `= 12 months` both give
   `error CHR004: expected `.` to end the phrase but found identifier `days`` (`months`).
   Proposed, does not parse today: `Param salary = $6,000.00`, `Due within 5 days`,
   `Held(ended()) For 12 months`. 7 amounts and 6 durations in the rules and cases of this example.

10. **`staff()` for a string-domain fact**, as for every other fact. 1 time. Today `Not(staff)`.

## Where no calendar and no blanks distorted the agreement
- "Each month" is an event the world triggers and numbers; the month has no length, so a salary
  for part of a month cannot be said.
- "Twelve months" is 365 days.
- "Within five days" is breached at day 5 exactly and "within twenty-one days" excludes day 21,
  following the pilots. The English does not say which, and a lawyer would count day 21 as in time.
- The salary figure is in the rules, not a blank, so this is one employee's agreement.

## Tool defects
1. **An act performed by someone outside the actor's type is valid and takes effect.**
   ```
   Fact employer Identified by Harborlight
   Fact employee Identified by Nadia
   Bool ended
   Power dismiss Actor employer Recipient employee
     Holds when True
     Valid when True
     Creates ended()
   .
   ?valid dismiss(Mallory, Nobody).
   dismiss(Mallory, Nobody).
   ?ended().
   ```
   Expected: an error that `Mallory` is not an `employer` (it is in no declared enumeration), or at
   least `valid: no`. Actual: `occurred act dismiss(employer("Mallory"),employee("Nobody"))
   lawful: no   valid: yes`, `+ended()`, both claims pass. In the real file `dismiss(Nadia, Harborlight)`,
   the employee dismissing the employer, ends the employment. A misspelt party in a scenario is
   never reported. Workaround: none taken; guarding every power with `employer == Harborlight`
   would be the ceremony the brief says to raise. The pilots have the same hole
   (`LastWill`: `sign(Daniel)` is unlawful but valid and creates `signed()`).
2. **A transition's report prints an effect that did not happen.** With `Fact signed Identified by employee`
   and `Act sign Actor employee Holds when True Creates signed()`, `sign(Zebra).` prints
   `+signed(employee("Zebra"))` and then `?signed(Zebra).` fails. Expected: no `+` line, or a
   diagnostic. Workaround: none needed.
3. **`check` writes the CHR029 line to stderr in the middle of a stdout line** when both go to one
   pipe: `…declare `Approved "dd38532ef50e1255cad4/Users/…/employment.charter: error CHR029: …`.
   Expected: whole lines. Workaround: none needed.

## What a lay author would have guessed
- `Act sign Actor employer` and `Act sign Actor employee`: one act, two kinds of signer.
- `Fact party Identified by employer, employee`.
- `Duty salary-due … Created by month-ends` with a bare `Event month-ends`.
- `Due within 5 days`; `Param non-solicit-period : Duration = 12 months`.
- `Created by sign-release When dismissed()` (`error CHR004: expected `.` to end the phrase but found `When``).
- `Norm "A termination for cause carries no severance." => for-cause`.
- `Not(staff())`.
- `Holds when released() && Not(Held(dismissed()) For release-window)` for "signs within twenty-one
  days after": accepted, and wrong from day 21 on.
