# ReturnPolicy
## Size
English sentences: 7. Charter lines outside clause blocks and comments: 48. Clause-block lines: 13.
Case lines: 90 (8 scenarios, 39 claims; every claim was flipped in a `/tmp` copy and every flip failed).
Declarations no sentence of the text refers to: 2 (`usd`, `covered`).

- `usd` exists so that `sell` and `refund` can carry an amount.
- `covered` is a snapshot, taken when the defect is found, of "within one year after it was bought",
  because the warranty asks when the defect appeared and a condition can only ask about now.

Known issues, counted: span cannot name a fact, exception or event, 3 clauses (1.1 and 1.3 are
the `Default` and the `Exception` of `returnable`; 2.1 is the event `defect-found`);
`Holds when True`, 3 (`sell`, `return`, `bring-in`); `Valid when` repeating `Holds when`, 0 in the
final file, 2 in the first draft; money in cents, 7 amounts; `Created by` needing components by
name, 1 (`return` has no `shop`, so the duty is made by an effect); diagnostic at the first line of
the block, 1 (`1:0` for line 9, in a probe); no calendar, 1 ("one year" is 365 days).

## Did `Default`/`Exception` earn its place
Just. 1.1 and 1.3 are a rule and its exception, and the two lines match the two sentences:
```
Fact returnable Identified by customer * item
  Default bought-within-thirty-days Holds when bought() && Not(Held(bought()) For return-window)
  Exception sold-as-final-sale Overrides bought-within-thirty-days Rejects when final-sale()
```
The plain form is one line shorter and needs no rule names:
`Holds when bought() && Not(Held(bought()) For return-window) && Not(final-sale())`.
I kept the defeasible form because it reads in the order of the text. It would be clearly better
if clause 1.3 could name `sold-as-final-sale`; today the names are written and never used.
2.1 and 2.2 (repair, and a refund when the repair is late) looked like a second default and
exception but are not: they are two duties, the second arising from the breach of the first.

## What was hard
Nothing in the final file was rejected; the first run of the rules and the first run of the cases
both passed. Everything below was silent, found by a probe or by reading.

1. **When does "ten days after it becomes due" start?** The refund on a late repair is a derived
   duty, `Holds when Violated(repair-due())`, with `Due within 10`. Brought in on day 200, the
   repair is overdue on day 230 and the refund is late on day 240. A scenario that goes from
   `@ 200.` straight to `@ 300.` gets `?violated refund-due(Calloway, Tomas, Lamp)` **failed**, and
   `?why` says `holds since 300; derived … at phrase 8`. The duty is stamped when a phrase first
   sees it, not when it arose. The case therefore stops at `@ 230.` before going on. See Tool
   defects 1.
2. **A late repair cancelled the refund.** With the refund derived from the repair duty's breach,
   `repair` on day 231 ended the repair duty and with it the refund. Nothing reported it; I
   noticed `~refund-due(…)` in `charter run`. The text gives the customer a refund once thirty
   days have passed, so `repair` and `replace` each got `Valid when Not(Violated(repair-due()))`.
3. **The amount of the store credit.** "Store credit for the price": first
   `Creates store-credit(customer, price(item))`, `s2.charter:1:0: error CHR011: price has 2
   component(s), 1 given`. Then `Creates store-credit(customer, price.usd)`: accepted, and passes
   with one item in the shop; with two, Ines returning the helmet is credited with the price of
   the lamp as well, because `price` is a free variable over every price. Then
   `Creates store-credit() When price()`: accepted, creates nothing. The spelling that works is
   `(Foreach price: store-credit(customer, price.usd) When price.item == item)`. I did not use it:
   the file records `store-credit(customer, item)` and leaves the amount to be read off `price`.
   That is a distortion of the text made to avoid a line no reader would follow.
4. **`Power return` with `Holds when returnable()` and `Valid when returnable()`.** The first
   draft. It made a customer who brings back a jersey marked final sale a wrongdoer. A customer
   asking is not a breach; the return just does not happen. Changed to
   `Act return … Holds when True / Valid when returnable()`.

## Improvements (most valuable first)

1. **Apply a function.** `Function price Identified by item * usd` cannot be applied. 2 uses here.
   Today:
   ```
   Act refund Actor shop Recipient customer Related to item, usd
     Valid when price()
   ```
   which works only because the act happens to carry both an `item` and a `usd`, and, for an
   effect, `(Foreach price: store-credit(customer, price.usd) When price.item == item)`.
   Proposed, does not parse today (`CHR011: price has 2 component(s), 1 given`):
   ```
   Act refund Actor shop Recipient customer Related to item, usd
     Valid when usd == price(item)
   Act return …
     Creates store-credit(customer, price(item)) When proof == NoReceipt
   ```
   Saves the binder, the projection and the join, and the wrong spelling `price.usd`, which
   resolves and silently means every price.

2. **A deadline on a derived duty should run from when it arose.** 1 time; in Employment the
   derived `severance-due` is safe only because its ground is an act. As written:
   ```
   Duty refund-due Holder shop Claimant customer Related to item
     Holds when Violated(repair-due())
     Due within 10
   ```
   Proposed: the same text, with the stamp of a fact derived from `Held(x) For d` or from a
   deadline being the instant that condition became true (stamp of `x` plus `d`), which the tool
   can compute. Today the answer to "is the refund late on day 300" depends on whether some
   phrase happened to look on day 230.

3. **"Within N days of X", now.** 2 times (`returnable`, `covered`). Today:
   ```
   Default bought-within-thirty-days Holds when bought() && Not(Held(bought()) For return-window)
   Creates defective(), covered() When (Exists customer: bought() && Not(Held(bought()) For warranty))
   ```
   Proposed, does not parse today:
   ```
   Default bought-within-thirty-days Holds when Within return-window Of bought()
   Creates defective(), covered() When (Exists customer: Within warranty Of bought())
   ```
   `Within d Of x`: `x` holds and has held for less than `d`. Saves writing `x` twice and the
   mistake of leaving out the first `x`, which makes the condition true when `x` never happened
   (Employment, What was hard 4).

4. **An act that only ever fails to take effect.** 3 times. Today:
   ```
   Act return Actor customer Related to item, proof
     Holds when True
     Valid when returnable()
   ```
   Proposed, does not parse today as meant (without `Holds when` the act is unlawful every time):
   ```
   Act return Actor customer Related to item, proof
     Valid when returnable()
   ```
   An act with no `Holds when` is lawful. In a shop's policy nothing a customer does is a breach,
   so `Holds when True` is on every customer act and says nothing.

5. **The one shop, named on every line.** `Calloway` appears on 30 of 90 case lines
   (`refund-due(Calloway, Tomas, Lamp)`), though `Fact shop Identified by Calloway` has one member.
   Leaving it out works today only with every other argument named:
   `refund-due(customer = Tomas, item = Lamp)`. Proposed, does not parse today
   (`CHR011: refund-due has 3 component(s), 2 given`): `refund-due(Tomas, Lamp)`, positional
   arguments filling the components that have more than one possible value.

6. **A clause should not be typed twice.** 6 clauses, 7 spans, 13 lines retyped from `policy.md`.
   Today `Clause 1.3 Approved "…"` / `Norm "An item sold as final sale cannot be returned." => return`.
   Proposed, does not parse today: `Clause 1.3 => return`.

7. **A span that names the exception.** Proposed, does not parse today:
   `Clause 1.3 => sold-as-final-sale`. Today it names `return`, as do 1.1 and both spans of 1.2,
   so four sentences point at one act and none at the line that means it.

8. **A condition shared by the acts that discharge a duty.** 2 times, the same line:
   ```
   Act repair Actor shop Recipient customer Related to item
     Valid when Not(Violated(repair-due()))
   Act replace Actor shop Recipient customer Related to item
     Valid when Not(Violated(repair-due()))
   ```
   Proposed, does not parse today: `Duty repair-due … Due within 30 / Terminated in time by repair, replace`.
   Saves 2 lines and says "a late repair does not count" once, on the duty it is about.

9. **Money as money.** `sell(Calloway, Ines, Helmet, 4500)` is a sale for $45.00. Proposed, does
   not parse today: `sell(Calloway, Ines, Helmet, $45.00)`. 7 amounts.

10. **Duties that are derived are not in chapter 006.** `Duty … Holds when …` is in the grammar
    (`duty_clause ::= … | deriv_clause`) and is the natural way to say "a refund is due when the
    repair is overdue", but 006 describes duties only as created and terminated. I found it by
    reading 020.

## Where no calendar and no blanks distorted the agreement
- "One year" is 365 days.
- A policy is not an executed instance between named parties. The rules are written over open
  `customer` and `item` types and the case names the people and things; `charter check` on the
  policy alone passes while `returnable` can derive nothing until a case enumerates them.
- "Within thirty days after buying it" excludes day 30, following the pilots.
- "With its receipt" is an argument of the act (`Receipt`, `NoReceipt`); there is no receipt in
  the state.

## Tool defects
1. **The stamp of a derived fact is the first phrase that sees it, so a deadline depends on
   which days the trace visits.**
   ```
   Bool started
   Bool late Holds when Held(started()) For 30
   .
   +started().
   @ 100.
   ?Held(late()) For 10.
   ```
   Expected: holds (`late` has been true since day 30). Actual: `query failed`; `?why late()` says
   `holds since 100`. Inserting `@ 30.` before `@ 100.` makes the same claim pass. 009.3 says a
   derived fact "keeps its stamp while it stays derived" and `lib/README.md` warns that a program
   "must observe the clock when `f` becomes true". Workaround: the scenario visits day 230.
2. **`price.usd` with `price` free resolves and reads every price** (What was hard, 3). Expected:
   an error that `price` is unbound, or a join on the act's `item`. Actual: no diagnostic.
   Workaround: not used.
3. **CHR011 for `price(item)` is reported twice, both at `1:0`**; the line is 9.

## What a lay author would have guessed
- `Valid when usd == price(item)` and `Creates store-credit(customer, price(item))`.
- `Creates store-credit(customer, price.usd)`.
- `Power return … Holds when returnable() / Valid when returnable()` for "may return".
- `Duty refund-due … Created when Violated(repair-due())`; the working spelling is `Holds when`.
- That a refund ten days late is late whichever days the test looks at.
