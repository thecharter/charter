# Settlement
## Size
English sentences: 12. Charter lines outside clause blocks and comments: 58. Clause-block lines: 21.
Case lines: 87 (8 scenarios, 50 claims; every claim was flipped in a `/tmp` copy and every flip failed).
Declarations no sentence of the text refers to: 2 (`usd`, `paid-late`), and one phrase (`+paid(0).`).

- `usd` exists so that `pay` can carry an amount.
- `paid-late` records, at the moment of a payment, that the fourteen days had already run. It
  exists because of Tool defect 1 and because "paid in full within the fourteen days" compares
  two moments.
- `+paid(0).` gives the running total a starting value. Without it a payment of $18,000 is
  lawful, valid, and adds nothing (Tool defect 3).

Known issues, counted: span cannot name a fact, a derived fact or a parameter, 4 clauses (1.1 the
pending lawsuit, 2.1 the sum, 3.1 the release, 4.1 "treated as never having taken effect");
`Holds when True`, 1; `Valid when` repeating `Holds when`, 2 (`sue`, `rescind`); money in cents,
11 amounts; `Created by`/`Terminated by`, 0 (all four duties are derived and none needed them);
diagnostic at the first line of the block, 1 (`1:0` for one of five candidate lines); failed claim
reported at the scenario's first line, 7 in one run, all `:64`; no calendar, 0.

## The feature: an effect that depends on a condition
This was the easiest thing in the four examples, and the reason is worth keeping. The release is
a derived fact, not an effect of the payment:
```
Bool released
  Holds when in-effect() && paid-in-full()
```
"Until then no claim is released" needs no rule. "After rescission the release is treated as
never having taken effect" needs none either: `rescind` ends `in-effect` and the release stops
being derived. Three sentences, two lines. The same holds for the duties: `payment-due`,
`dismissal-due` and `return-due` are each `Duty … Holds when …`, and each ends when its ground ends,
with no discharging act wired to it. What the text loses is that none of the three sentences can
point at `released`: a span cannot name it.

## What was hard
1. **Reading the running total.** `Bool paid-in-full Holds when paid >= settlement-sum`, since
   `settlement-sum`, a `Param`, is read by its bare name. `s1.charter:1:0: error CHR012: cannot use
   an instance of paid where an integer is needed`, then 25 follow-on CHR010. The file had five
   uses of `paid` as a number and the diagnostic names none of them. All five became `paid.usd`.
2. **"Has not paid in full within the fourteen days."** Written as
   `Bool payment-late Holds when Held(in-effect()) For payment-window && Not(paid-in-time())`.
   Seven claims of one scenario failed, all reported at line 64, the first being
   `[scenario late-payment-…, phrase 6]:64: claim failed: ?valid rescind()`. Asked one at a time on
   day 14, `?Held(in-effect()) For payment-window.` holds and `?Not(paid-in-time()).` holds, and
   `?payment-late().` fails; `?why payment-late()` says `no assignment and not derived`. `Held` over
   a derived fact is false inside a rule (Tool defect 1). Rewritten as
   `Holds when Violated(payment-due()) || paid-late()`, with `paid-late()` set by a payment made
   after the window.
3. **The first payment vanished.** A probe without `+paid(0).`: `pay(usd = 1800000).` reports
   `lawful: yes   valid: yes` and no effect; `?released().` fails. No diagnostic.

## Improvements (most valuable first)

1. **A running total with a starting value, read by its name.** 4 reads, 2 writes, 1 genesis
   phrase. Today:
   ```
   Var paid Identified by usd
   Bool paid-in-full
     Holds when paid.usd >= settlement-sum
   Act pay Actor defendant Recipient claimant Related to usd
     Holds when in-effect()
     Creates paid(paid.usd + usd), paid-late() When Held(in-effect()) For payment-window
   …
   +paid(0).
   ```
   Proposed, does not parse today:
   ```
   Var paid : Money(USD, 2) = 0
   Bool paid-in-full
     Holds when paid >= settlement-sum
   Act pay Actor defendant Recipient claimant Related to usd
     Holds when in-effect()
     Creates paid(paid + usd)
   ```
   `Param` already has this declaration form and this bare-name reading; a `Var` that an act
   updates is the same thing under another keyword. Saves the genesis phrase, four `.usd`, and
   the payment that silently adds nothing.

2. **A span that names a derived fact.** The release is what this document is for. Today:
   ```
   Clause 3.1 Approved "…"
     Norm "When the defendant has paid in full, each party releases the other from every claim arising from the incident." => pay, sue
     Norm " Until then no claim is released." => sue
   ```
   Proposed, does not parse today: `=> released` on both spans. As it stands the rule
   `Holds when in-effect() && paid-in-full()` can be changed to `Holds when in-effect()` and no
   approval is invalidated. 4 clauses in this file hang on a neighbouring act for this reason.

3. **"Paid within N days of X."** 1 time; the third example of four that needs it. Today:
   ```
   Bool paid-late
   Act pay … Creates paid(paid.usd + usd), paid-late() When Held(in-effect()) For payment-window
   Bool payment-late
     Holds when Violated(payment-due()) || paid-late()
   ```
   Proposed, does not parse today:
   ```
   Bool payment-late
     Holds when Not(paid-in-full() Within payment-window Of in-effect())
   ```
   Saves one fact and one conditional effect, and states the sentence instead of two ways it
   can come about.

4. **Write a prohibition as a prohibition.** 2 times. Today:
   ```
   Power sue Actor party Recipient party' Related to matter
     Holds when Not(released() && matter == Incident)
     Valid when Not(released() && matter == Incident)
   Act disclose-terms Actor party
     Holds when compelled()
   ```
   Proposed, does not parse today:
   ```
   Power sue Actor party Recipient party' Related to matter
     Void when released() && matter == Incident
   Act disclose-terms Actor party
     Forbidden Unless compelled()
   ```
   `Void when c` makes the act both unlawful and without effect while `c` holds, which is what
   "a released claim" means and is today the same negated condition written twice. Saves 1 line
   and the two negations.

5. **A clause should not be typed twice.** 9 clauses, 12 spans, 21 lines retyped from
   `settlement.md`. Today `Clause 3.2 Approved "…"` / `Norm "Neither party brings a claim that it has released." => sue`.
   Proposed, does not parse today: `Clause 3.2 => sue`.

6. **Name each party once.** Today:
   ```
   Fact party Identified by Elena, Northgate
   Fact claimant Identified by Elena
   Fact defendant Identified by Northgate
   ```
   Proposed, does not parse today: `Fact party Identified by Elena As claimant, Northgate As defendant`.
   As in Employment, the three lines buy cases with no party arguments for the one-sided acts
   (`pay(usd = 1800000).`, `rescind().`, `?violated dismissal-due().`), while the mutual ones keep
   them (`sue(Northgate, Elena, Incident)`).

7. **A failed claim should say its own line.** One wrong rule produced seven failures, each
   printed as `…garage.charter [scenario late-payment-…, phrase N]:64:` with N from 6 to 16; the
   scenario is 20 lines long and has two claims on some lines, so the phrase number has to be
   counted by hand. Proposed output: `garage.charter:70: claim failed: ?valid rescind()`.

8. **Money as money.** `Param settlement-sum : Money(USD, 2) = 1800000` for eighteen thousand
   dollars; `pay(usd = 1000000)`. Proposed, does not parse today: `= $18,000.00`. 11 amounts.

## Where no calendar and no blanks distorted the agreement
- Nothing here needed a calendar: fourteen days and seven days are counted from events.
- A settlement would carry a date and a case number. The lawsuit is the fact
  `pending(Elena, Northgate, Incident)`, asserted at the foot of the rules.
- "Paid in full" needed partial payments, so the sum is a running total and not a single act.
- "No admission" is an invariant over a fact, `admission`, that nothing in the program creates.
  It says what the clause says, but see Tool defect 2.

## Tool defects
1. **`Held(e) For d` is false inside a `Holds when` when `e` is itself derived, and true
   everywhere else.**
   ```
   Fact p Identified by A
   Bool a
   Bool b Holds when a()
   Bool c Holds when Held(b()) For 5
   Act go Actor p Holds when Held(b()) For 5
   .
   +a().
   @ 5.
   ?Held(b()) For 5.
   ?c().
   ?lawful go(A).
   ```
   Expected: all three hold. Actual: the first holds; `query failed: ?c().`;
   `claim failed: ?lawful go(A).` The same expression is true as a query, in an effect's `When`,
   and as a derived duty's `Due within`. No diagnostic. Workaround: measure the age of an assigned
   fact, or use `Violated(duty)`; here `Violated(payment-due()) || paid-late()`.
2. **`charter test` passes a file in which an `Invariant` is violated.**
   ```
   #require "settlement.charter".
   sign(Elena). sign(Northgate).
   +admission(Northgate).
   sign(Elena).
   ```
   Expected: FAIL. Actual: `1 passed, 0 failed`. `charter run` prints
   `violation: invariant no-admission does not hold`, under the `sign(Elena)` phrase that follows the
   one that broke it. Workaround: a scenario claims `?no-admission().` explicitly.
3. **An effect that reads a `Var` with no instance does nothing, silently.** With `+paid(0).`
   removed, `pay(usd = 1800000).` prints `occurred act pay(…)   lawful: yes   valid: yes` and no
   `+paid(…)` line. Expected: an error that `paid` has no value. Workaround: `+paid(0).`.
4. **CHR012 at `1:0`** for an expression on one of lines 24, 28, 29, 56 or 59 (What was hard, 1).

## What a lay author would have guessed
- `paid >= settlement-sum` and `Creates paid(paid + usd)`.
- That a total starts at nothing without being told.
- `Holds when Held(in-effect()) For payment-window && Not(paid-in-time())`: each half true when asked,
  the rule false.
- `Norm "… each party releases the other …" => released`.
- That declaring `Invariant no-admission` means a test fails when it is broken.
