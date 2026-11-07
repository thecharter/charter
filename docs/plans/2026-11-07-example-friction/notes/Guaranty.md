# Guaranty
## Size
English sentences: 12. Charter lines outside clause blocks and comments: 54. Clause-block lines: 16.
Case lines: 90 (8 scenarios). Declarations no sentence of the text refers to: 1 (`usd`), plus the
genesis line `+balance(loan). +called(0). +unpaid(0). +claim(0).`, four assignments of which three
say only "starts at nothing".

Known issues, counted: `Valid when` repeating `Holds when` once (`demand`, four conjuncts, 78
characters typed twice); `Holds when True` 2 times; a span that is really a fact once (1.1
"guarantees … the loan" is an unlinked `Definition`; "in default" I could link only by naming the
duty `repay`); `Approved` stamps 6; amounts in cents 2 in the root and 28 in the cases; `Created
by` tried and abandoned (third example running); a name ending in a digit rejected twice (`fee2`,
`Scenario overlapping2`: `error CHR003: expected `{` but found integer 2`).

## What was hard
1. **A duty per demand.** First version, in the pilots' idiom:
   ```
   Power demand Actor lender Recipient guarantor Related to usd
     … Creates called(called + usd)
   Duty guaranty-due Holder guarantor Claimant lender Related to usd
     Due within 15
     Created by demand
     Terminated by pay-guaranty
   ```
   Accepted. Then `demand(Ines, Victor, 100000). demand(Ines, Victor, 100000).` leaves
   `called(200000)` and one duty `guaranty-due(Victor, Ines, 100000)`, which a single
   `pay-guaranty(Victor, Ines, 100000)` discharges. Two demands for the same amount are the same
   instance, and creating an instance that holds is a silent no-op. I replaced the keyed duty with a
   running total (`Var unpaid`) and a derived duty (`Holds when unpaid > 0`).
   That has its own distortion, which I ran: a second demand made on day 104, while the first
   (day 90) is unpaid, is "violated" on day 105. The fifteen days of 1.2 run from the first unpaid
   demand, not from each one. I know no spelling today that gives each demand its own fifteen days.
2. **Taking over a claim.** "Takes over the lender's claim against the borrower" wants the duty
   `repay(Dana, Ines)` to become, in part, `repay(Dana, Victor)`.
   With one type per role (`Fact lender Identified by Ines` …):
   `Creates repay(borrower, guarantor)` gives `s1.charter:1:0: error CHR012: cannot use an instance
   of guarantor where an instance of lender is needed`.
   With one `person` type and three placeholders it is accepted, and since `borrower` is not a
   component of `pay-guaranty` it means every person: after `pay-guaranty(Victor, Ines)` the state
   holds `repay(Ines, Victor)`, `repay(Dana, Victor)` and `repay(Victor, Victor)`. No diagnostic.
   I kept one type per role and wrote the claim as a second amount and a second duty
   (`Var claim`, `Duty reimburse`), moved by hand:
   `Creates unpaid(unpaid - usd), balance(balance - usd), claim(claim + usd)`.
3. **Thirty days after the default.** `Due within notice-window` on a duty derived from
   `in-default()` counts from the first phrase that sees the default (PromissoryNote, hard 7), so a
   scenario that goes straight to `@ 125.` would allow a notice 35 days late. I wrote
   `Violated when Held(repay()) For term + notice-window`: thirty days after default is said as
   120 days after the loan.

Nothing else was rejected; the first full draft resolved and all eight scenarios passed on the
first run. The `Immunity` was the easy part: see Improvements 6.

Where the lack of a calendar distorted the agreement: "within ninety days after the date of this
guaranty" stands in for a maturity date; "fifteen days after the demand" and "thirty days after
the default" would be counted from receipt of a notice on a date; the off-by-one of `Due within`
applies to all three (breach on day 90, 105 and 120).

## Improvements (most valuable first)
1. **A debt: a duty with an amount that payments reduce.** As written, three times over
   (the loan, the guarantor's liability, the guarantor's claim):
   ```
   Var unpaid Identified by Money(USD, 2)
   Duty guaranty-due Holder guarantor Claimant lender
     Holds when unpaid > 0
     Due within 15
   Act pay-guaranty Actor guarantor Recipient lender Related to usd
     Holds when usd <= unpaid
     Creates unpaid(unpaid - usd), …
   …
   +unpaid(0).
   ```
   Proposed, does not parse today:
   ```
   Debt guaranty-due Holder guarantor Claimant lender
     Raised by demand          // each valid demand adds its amount, with its own deadline
     Paid by pay-guaranty      // lawful up to what is owed; discharged at nothing
     Due within 15
   ```
   Saves 5 of 8 lines per debt (15 here), the `Var`, its genesis line, the `usd <=` guard and the
   subtraction; and it is the only form in which "fifteen days after the demand" would be right
   for a second demand. Occurs 3 times here, 2 in PromissoryNote, 1 in HomePurchase.
2. **Moving a claim from one creditor to another.** As written:
   ```
   Var claim Identified by Money(USD, 2)
   … Creates unpaid(unpaid - usd), balance(balance - usd), claim(claim + usd)
   Duty reimburse Holder borrower Claimant guarantor
     Holds when claim > 0
   ```
   Proposed, does not parse today, with `repay` a debt as above:
   ```
   Act pay-guaranty Actor guarantor Recipient lender Related to usd
     Pays guaranty-due
     Assigns usd Of repay To guarantor
   ```
   Saves `claim`, `reimburse`, `repay-guarantor` (7 lines) and lets clause 5.1 name the one rule it
   states. Subrogation, assignment and novation are all this.
3. **Say a power's condition once.** As written:
   ```
   Holds when in-default() && notified() && called + usd <= limit && unpaid + usd <= balance
   Valid when in-default() && notified() && called + usd <= limit && unpaid + usd <= balance
   ```
   The text says both things in one breath ("may not demand more …, and a demand for more has no
   effect"). Proposed, does not parse today:
   `Only when in-default() && notified() && called + usd <= limit && unpaid + usd <= balance`,
   meaning unlawful and void otherwise. Saves a line and the chance that the two drift apart.
4. **A role that is not bound is an error, not everyone.** As written, I avoided it. The accepted
   and wrong program is in hard 2. Proposed: in an effect, a role name that is not a component of
   the act must be written `(Foreach borrower: …)`; bare, it is an error. No new syntax. It costs
   me one `Foreach` in this file (`Creates released(guarantor)` in `change-terms`) and would have
   caught the three-debts result.
5. **"Was it done in time?"** As written:
   ```
   Bool notified
   Duty notice-due Holder lender Claimant guarantor
     Holds when in-default() && Not(notified())
     Violated when Held(repay()) For term + notice-window
   Power give-notice Actor lender Recipient guarantor
     Holds when True
     Valid when notice-due() && Not(Violated(notice-due()))
     Creates notified()
   ```
   Proposed, does not parse today:
   ```
   Duty notice-due Holder lender Claimant guarantor
     Holds when in-default()
     Due within notice-window After in-default()
     Met by give-notice
   Act give-notice Actor lender Recipient guarantor
   ```
   and `demand … Only when Met(notice-due()) && …`. `Met(d)` is true when the duty was discharged
   before it was breached. Saves 4 lines, the marker `notified`, and the power whose only purpose
   is to refuse a late notice.
6. **Let a span name what an immunity is called in the text.** This worked and is worth keeping:
   `Immunity released Holder guarantor Against demand` is one line, `demand` did not change, and
   "the guarantor is released" could name a rule. The alternative, a fact `released` and
   `&& Not(released())` in both conditions of `demand`, would have been longer and could not be
   named by the clause. One thing a reader has to be told: under the immunity the demand is still
   `lawful` and only `void`; with the fact in `Holds when` it would also be unlawful. The text
   ("no demand made after the change has any effect") happens to want the first. Proposed, does
   not parse today: `Immunity released Holder guarantor Against demand Unlawful too`, for texts
   that say "may not".
7. **Initial values.** `+balance(loan). +called(0). +unpaid(0). +claim(0).` Proposed, does not
   parse today: `Var called : Money(USD, 2) = 0` (HomePurchase 3). 4 here.

## Tool defects
1. A free role in an effect silently ranges over the whole type.
   ```
   Fact person Identified by Ines, Dana, Victor
   Placeholder lender For person
   Placeholder borrower For person
   Placeholder guarantor For person
   Duty repay Holder borrower Claimant lender
   Act pay-guaranty Actor guarantor Recipient lender
     Holds when True
     Creates repay(borrower, guarantor)
     Terminates repay(borrower, lender)
   .
   +repay(Dana, Ines).
   pay-guaranty(Victor, Ines).
   ?--repay.
   ```
   Expected: an error or warning that `borrower` is unbound. Actual: `repay(Ines, Victor)`,
   `repay(Dana, Victor)`, `repay(Victor, Victor)`; 0 errors. This is 005.4 as written ("further
   free variables of an effect are bound to every valid instance"), so it is a design defect.
   Workaround: one type per role.
2. A name may not end in a digit, and the message does not say so:
   `Scenario overlapping2 {` gives `g2.charter:11:21: error CHR003: expected `{` but found
   integer 2`. Expected: "a name cannot end in a digit". Workaround: `overlapping-b`.

## What a lay author would have guessed
- `Duty guaranty-due … Related to usd  Created by demand  Terminated by pay-guaranty`: accepted,
  and two equal demands are one debt (hard 1).
- `Creates repay(borrower, guarantor)` for "takes over the lender's claim": `CHR012` with role
  types, everyone with a shared type (hard 2).
- `Due within notice-window` for "within thirty days after the default": accepted, and counted
  from the first day the scenario looks (hard 3).
- `Immunity released Holder guarantor Against demand`, created by
  `Creates released(guarantor) When Not(consent())`: accepted and right the first time.
