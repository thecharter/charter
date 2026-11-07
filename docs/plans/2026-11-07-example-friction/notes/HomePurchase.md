# HomePurchase
## Size
English sentences: 20. Charter lines outside clause blocks and comments: 75. Clause-block lines: 33.
Case lines: 119 (11 scenarios). Declarations no sentence of the text refers to: 4 (`usd`, which exists
only so an act can take an amount; `open`, the text has no one word for "signed, not cancelled, not
closed"; `refundable` and `forfeited`, two flags that carry "who gets the earnest money" from the
cancelling power to the escrow agent's act), plus the genesis line `+paid(0).`.

Known issues, counted: `Holds when True` 8 times; a span that is really a fact 3 times (5.2 "title
to the house passes to the buyer", 7.1 "Until closing the risk of loss stays with the seller", 1.2
"the signing day"); `Approved` stamps 13; amounts in cents 2 in the root and 15 in the cases;
`Created by` rejected twice and then abandoned; `Document` without `.` before `#require` once;
a diagnostic on the first line of the block twice, and on the scenario's first line for each of
the 8 failed claims of the first run.

## What was hard
1. **A duty the cancellation creates for a third party.** First attempt, for "the earnest money is
   returned to the buyer":
   ```
   Duty refund-due Holder escrow-agent Claimant buyer
     Due within 5
     Created by cancel-on-inspection
   ```
   `hp1.charter:2:0: error CHR027: `Created by cancel-on-inspection` on refund-due: the component
   escrow-agent of refund-due is not a component of cancel-on-inspection, so cancel-on-inspection
   cannot bind it`. The buyer cancels by notice to the seller; the escrow agent is not a party to
   that act, and in this agreement there is exactly one escrow agent. The error is at line 2 (the
   first `Fact`), the declaration is at line 27, and the one bad duty took the whole block with it:
   ten further `CHR010: undeclared type or placeholder` errors for every act the scenario used.
2. **A duty that starts when the second of two people signs.** `Duty earnest-due Holder buyer
   Claimant seller Due within 3 Created by buyer-signs` gives `error CHR027: … the component seller
   of earnest-due is not a component of buyer-signs`. And `Created by` cannot be conditional ("only
   if the seller has signed already"). I gave up on `Created by`/`Terminated by` altogether and
   derived every duty: `Holds when open() && Not(in-escrow())`. That worked first time, the stamp
   starts when the condition first holds, and clause 8.1 ("neither party owes the other anything
   more") came for free because every duty reads `open()`. Nothing in 006 says a `Duty` may carry
   `Holds when`; I found it in the grammar (`duty_clause ::= … | deriv_clause`).
3. **A running total that silently never starts.** I wrote `Var paid Identified by usd` and
   `Creates paid(paid.usd + usd)`, as LivingTrust does with `fund`. With no value in `paid`:
   `balance-due` (`Holds when open() && paid.usd < price - earnest`) never arises, `closed` never
   holds, and `pay-price(Omar, Nora, 20000000)` creates nothing. No diagnostic; eight scenario
   claims failed, the first being `query failed: ?balance-due("Omar", "Nora")`. A five-line probe
   showed both `Holds when paid.usd < price` and `Holds when Not(paid.usd < price)` are false while
   `paid` is unset. Fix: `+paid(0).` after the declaration block.
   The natural spelling `Var paid Identified by usd = 0` gives `error CHR004: expected `.` to end
   the phrase but found `=``. (`Param paid : Money(USD, 2) = 0` does work, but it calls the buyer's
   payments a parameter.) Later, on the promissory note, I found that `Var paid Identified by
   Money(USD, 2)` is read as plain `paid` with no `.usd`; the file now uses that.
4. **`lib/contract_lifecycle`: tried, not used.** Three separate obstacles, each run:
   - Provenance. `Use contract-lifecycle(contract, party, obligation) As cl` and then
     `check --require-provenance`: `FAIL rules with no English: cl-remedy-survives-termination,
     cl-performed-non-negative, cl-remaining-non-negative, cl-novate-obligation, cl-assign-claim,
     cl-appoint-subcontractor, cl-record-breach, cl-perform-obligation, cl-terminate-for-breach,
     cl-open-dispute, cl-activate-contract, cl-accept-contract, cl-offer-contract`. Thirteen rules
     the agreement does not mention. The only ways through are to add English about novation and
     subcontracting, or to pin `From` spans on rules they do not mean.
   - Money. The module's amounts are `int`. `cl-perform-obligation(party, Balance, usd)` gives
     `error CHR012: cannot use an instance of usd where an instance of int is needed`;
     `+cl-remaining-debt(Balance, price)` gives `CHR012: cannot use an instance of price where an
     instance of int is needed`; `?cl-remaining-debt(Balance, price - earnest - 20000000)` gives
     `CHR012: cannot use Money(USD, 2) where an instance of int is needed`.
   - Meaning. These scenarios pass against the module and each contradicts the agreement: Omar
     alone runs `cl-offer-contract`, `cl-accept-contract`, `cl-activate-contract` and the contract
     is `InForce` (1.2 needs both signatures); Nora runs `cl-record-breach(Nora, Balance)` on day
     0 (the module has no deadlines, so "in time" cannot be said); Omar, the party in breach, runs
     `cl-terminate-for-breach(Omar, Sale, Balance)` and it is valid (6.2 gives that to the seller).
     It also needs six genesis assertions per obligation (`contract-of`, `obligor-of`,
     `claimant-of`, `remaining-debt`, `performed-total`, the status) and three steps to bind
     (offer, accept, activate) where the text has one ("both have signed").
   The plain version needs 5 lines for signing and 1 derived line per duty. The module would have
   added about 12 lines of setup and removed none of mine, since the deadlines, the cancellation
   grounds and the escrow are not in it.
5. **"Within three days" is one day short.** `Due within 3` is breached at `@ 3`. A person told
   "within three days after the signing day" pays on day 3 and is in time. To say that I would
   write `Due within 4`, a number that is not in the text. I followed the pilots (`Due within 3`,
   `For 10`, `For 30`, `Due within 45`) and the scenarios show the breach on day 3, 10, 30 and 45.

Where the lack of a calendar distorted the agreement: "Closing takes place within forty-five days
after the signing day" stands in for a closing date ("on 30 June"); the earnest money would
normally be "three business days"; the inspection and financing periods would end at a stated hour
("5 p.m. on the tenth day"); there is no way to say a period that ends on a weekend runs to Monday.

## Improvements (most valuable first)
1. **Say that an act happened, without a marker fact.** As written, five times:
   ```
   Bool seller-signed
   Bool buyer-signed
   Act seller-signs Actor seller Holds when True Creates seller-signed()
   Act buyer-signs Actor buyer Holds when True Creates buyer-signed()
   Bool signed Holds when seller-signed() && buyer-signed()
   ```
   and likewise `deed-delivered`, `loan-committed`, `destroyed`. Proposed, does not parse today:
   ```
   Act sign Actor seller | buyer
   Bool signed Holds when Done(sign(Nora)) && Done(sign(Omar))
   Duty deed-due Holder seller Claimant buyer Holds when open() && Not(Done(deliver-deed()))
   ```
   Saves one `Bool` and one `Creates` per act (10 lines here) and the concept "an act leaves no
   trace unless you declare one". The history already records every act (Law 1). Occurs 5 times.
2. **A window counted from an event, stated positively and inclusively.** As written:
   ```
   Valid when open() && Not(Held(signed()) For 10)
   Valid when open() && Not(loan-committed()) && Not(Held(signed()) For 30)
   ```
   Proposed, does not parse today:
   ```
   Valid when open() Within 10 days of signed()
   Valid when open() && Not(loan-committed()) Within 30 days of signed()
   ```
   with `Within n days of e` true through the end of day n, and `Due within 3 days` breached at
   the start of day 4. Saves the double negative, the knowledge that `Held … For` is the only
   clock test, and the off-by-one. Occurs 2 times as a window and 3 times as a deadline.
3. **A value that starts somewhere.** As written:
   ```
   Var paid Identified by Money(USD, 2)
   …
   +paid(0).
   ```
   Proposed, does not parse today: `Var paid : Money(USD, 2) = 0`. Saves a line and removes the
   silent failure in "What was hard" 3. Independently, a
   rule that reads a `Var` with no value should be a warning at `check`. Occurs once; cost the
   most time of anything in this example.
4. **Money written as money.** As written: `Param price : Money(USD, 2) = 40000000`,
   `pay-price(Omar, Nora, 39000000)`, `pay-earnest(Omar, HarborTitle, 1000000)`. Proposed, does
   not parse today: `Param price = $400,000.00`, `pay-price(Omar, Nora, $390,000.00)`. Saves the
   type annotation and, more to the point, lets a reader check the figure against "four hundred
   thousand dollars" without counting zeros. Occurs 17 times.
5. **A power needs no `Holds when True`.** As written, six times:
   ```
   Power cancel-on-inspection Actor buyer Recipient seller
     Holds when True
     Valid when open() && Not(Held(signed()) For 10)
     Creates cancelled(), refundable()
   ```
   Trying to cancel without the right is not a breach; 8.1 says it "has no effect". Proposed, does
   not parse today (it parses, but the power is then never lawful): the same without the
   `Holds when True` line; a `Power` with no `Holds when` is lawful to attempt. Saves 6 lines here
   (8 with the two signing acts) and the question "what is the difference between unlawful and
   void" at the moment the author least needs it.
6. **One power, several grounds.** The six cancellation powers differ only in their ground; four
   of them end in the same `Creates cancelled(), refundable()`, and clause 8.1 has to list all six
   by hand: `=> cancel-for-no-earnest, cancel-on-inspection, cancel-on-financing,
   cancel-for-no-deed, cancel-for-no-payment, cancel-on-loss`. Proposed, does not parse today:
   ```
   Power cancel Actor buyer Recipient seller
     Valid under inspection when open() Within 10 days of signed()
     Valid under financing  when open() && Not(loan-committed()) Within 30 days of signed()
     Valid under no-deed    when Violated(deed-due())
     Valid under loss       when open() && destroyed()
     Creates cancelled(), refundable()
   ```
   with spans naming `cancel.inspection` and 8.1 naming `cancel`. Saves 12 lines and the list.
7. **A comma means "or" after `Holds when` and "and" after `Valid when`.** Probe:
   `Act try Holds when a(), b() Valid when a(), b()` with only `a()` true is lawful and not valid.
   I did not use commas because of it. Proposed: reject the comma in both and require `&&`/`||`.
8. **`check` prints 67 lines to say yes.** Proposed: print failures and the last line; `--verbose`
   for the rest.

## Tool defects
1. A `Norm` span naming a declared fact is reported as undeclared.
   ```
   Document "e.md".
   Bool closed
   Act close Holds when True Creates closed()
   Clause 5.2
     Norm "The sale is closed." => close
     Norm " Title passes to the buyer." => closed
   .
   ```
   Expected: "closed is a fact; a span can name only acts, duties, immunities and invariants".
   Actual: `FAIL 5.2: spans name undeclared rules: closed`. Workaround: leave the span unlinked.
2. `check --require-provenance FILE 2>&1` interleaves the `CHR029` line (stderr) into the middle
   of a report line (stdout, block-buffered when piped). Seen as
   ``(or legacy `Approved 613932Examples/HomePurchase/purchase.charter: error CHR029: provenance
   coverage is `partial`, expected `complete` (--require-provenance)`` followed on the next line by
   `0391756295503`). Unapproved: …`. Expected: whole lines. Workaround: none needed.
3. One rejected declaration discards its whole block, so one `CHR027` is followed by a `CHR010`
   for every name the block declared (10 here). Expected: the one error.

## What a lay author would have guessed
- `Act sign Actor seller, buyer` for "both of them have signed it":
  `error CHR004: expected `.` to end the phrase but found `,``.
- `Valid when signed() within 10`: `error CHR004: expected `.` to end the phrase but found
  identifier `within``.
- `Valid when signed() && Current Time < 10`: accepted, and means day 10 of the clock, not ten
  days after signing. In a probe where signing happened on day 5 the cancellation on day 12 was
  void with no hint why.
- `Var paid Identified by usd = 0`: rejected as above. Without the `= 0`: accepted and inert.
- `Created by cancel-on-inspection` on the escrow agent's duty: `CHR027`, as above.
- `Norm "… title to the house passes to the buyer …" => closed`: "undeclared", as above.
