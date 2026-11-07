# BillOfSale
## Size
English sentences: 12. Charter lines outside clause blocks and comments: 54. Clause-block lines: 19.
Case lines: 89 (9 scenarios). Declarations no sentence of the text refers to: 1 (`usd`). The
reverse also occurs once: clause 3.2, the odometer statement, has no declaration at all; the figure
84,210 appears nowhere in the rules.

Known issues, counted: `Holds when True` 5 times (four acts and the immunity); a span that is
really a fact 2 times (3.2, a statement; 2.1 "ownership … passes", which I could link only to the
two acts that carry the effect); `Approved` stamps 8; amounts in cents 1 in the root and 11 in the
cases; `Created by`/`Terminated by` worked, twice, the only time in my four examples, because the
creating act carries `seller`, `buyer` and `car` under the duty's own role names; "the seller" as
one named person: the program never says Grace is the seller (see Improvements 2).

## What was hard
1. **A general rule and its exception.** First version, with the construct 004.12 gives for it:
   ```
   Fact answerable Identified by defect
     Default as-is Rejects when True
     Exception concealed Overrides as-is Holds when known(defect) && Not(disclosed(defect))
   Power demand-repair Actor buyer Recipient seller Related to defect
     Holds when True
     Valid when answerable(defect)
   …
   Clause 4.1
     Norm "The car is sold as is." => as-is, demand-repair, repair-due, pay-for-repair
     Norm " That does not protect a seller who knew." => concealed
   ```
   The scenarios passed. `check` said `FAIL 4.1: spans name undeclared rules: as-is, concealed`.
   The two rules have names, the names are the two sentences, and a span may not use them.
   Without the names the form is a longer way to write `Valid when known() && Not(disclosed())`.
   Second version:
   ```
   Immunity as-is Holder seller Related to defect Against demand-repair
     Holds when True
     Unless known() && Not(disclosed())
   ```
   Passed first time; `demand-repair` became a plain `Act`; both sentences name `as-is`. The text
   itself says "does not protect", which is the immunity's own word. This is the form in the file.
   `Default`/`Exception` made the program worse here and I say so as item 4 of "Done" asks.
2. **Ownership passes when the second of two things is done.** I tried deriving it:
   `Function owner Identified by car * person Holds when (Exists seller: paid(seller, person, car)
   && delivered(seller, person, car))` with `+owner(Corolla, Grace)` as the starting point. After
   payment and delivery `?!owner(Corolla, Grace)` fails: Grace and Leo both own the car. A
   `Function` keeps one value among assigned instances only. So the passing of ownership is an
   effect, and since either act may come second it is written in both:
   `owner(car, buyer) When delivered() && owner(car, seller)` in `pay` and
   `owner(car, buyer) When paid() && owner(car, seller)` in `deliver`.
3. **An immunity that protects no one.** Without the `Holds when True` line the immunity is
   accepted and never holds: `claim failed: ?!valid demand-repair("Leo", "Grace", "Corolla", "worn
   clutch")`. The "as is" clause would have been a dead letter with no diagnostic. I had written
   the line because acts had taught me to; I removed it to see.
4. **Facts about the world.** First version: `+lien(Corolla).`, `+known("cracked frame").`,
   `+knew-reading-wrong(Grace, Corolla).` in the scenarios, as Deed does. Then
   `Evidenced Fact known Identified by defect` and `SubmitEvidence known("cracked frame") By
   Mechanic.` It worked first time and it reads as what it is: who knew what is a matter of
   proof. With no evidence the demand is void, so the burden sits on the buyer, which is right.
   Two things I had to find by running: `?!valid cancel(…)` passes when the answer is
   `undetermined` (both `?!valid` and `?undetermined` hold for the same instance), and an
   immunity's `Unless` over an unresolved fact is a plain "no", not `undetermined`.
5. **Lines I wrote that did nothing.** `+defect("worn clutch").` before mentioning the defect. A
   `Fact defect` over strings needs no instance to be talked about; deleting the three lines
   changed no result.

Where the lack of a calendar distorted the agreement: a bill of sale is dated, and the three
periods (five, ten and thirty days) would be counted from that date or from a written demand. Here
they are counted from the act. `Due within 5` is breached at `@ 5`, so handing over the title on
the fifth day is late.

## Improvements (most valuable first)
1. **An effect that follows from a state, whoever brings it about.** As written:
   ```
   Act pay Actor buyer Recipient seller Related to car, usd
     …
     Creates paid(), owner(car, buyer) When delivered() && owner(car, seller)
   Act deliver Actor seller Recipient buyer Related to car
     …
     Creates delivered(), owner(car, buyer) When paid() && owner(car, seller)
   ```
   Proposed, does not parse today:
   ```
   Event ownership-passes Related to seller, buyer, car
     Occurs when paid() && delivered() && owner(car, seller)
     Creates owner(car, buyer)
   Duty title-due Holder seller Claimant buyer Related to car
     Due within 5
     Created by ownership-passes
     Terminated by hand-over-title
   ```
   Saves the duplicated condition, gives clause 2.1 one thing to name, and lets `title-due` use
   `Created by` (today it is derived, with four conjuncts, because two acts can complete it).
   Occurs once here and once in HomePurchase (`closed`).
2. **Name the parties of an executed instrument once.** As written, every fact is keyed by the
   pair (`Fact paid Identified by seller * buyer * car`, also `delivered`, `title-handed`,
   `cancelled`), and the case file repeats `Grace, Leo, Corolla` or `Leo, Grace, Corolla` 55 times
   in 89 lines. Nothing says Grace is the seller: `deliver(Leo, Grace, Corolla)` is as well-formed
   as the real one. Proposed, does not parse today:
   ```
   Fact person Identified by Grace, Leo
   Role seller Is Grace
   Role buyer Is Leo
   ```
   A role with one member may be left out of every application: `pay(650000).`, `deliver().`,
   `?title-due().`, `Bool paid`. Saves about 1,000 characters of the case file, three components
   on four facts, and the two `Placeholder` lines; `owner(car, person)` still ranges over people.
3. **Let a span name a `Default` or `Exception` rule.** As written (first version above):
   `Norm "…" => as-is` is refused though `Default as-is` is declared. Proposed: accept it. No new
   syntax; it parses today and fails `check`. Without it 004.12 cannot be used under
   `--require-provenance` for the purpose 007.6 describes.
4. **An immunity holds unless told otherwise.** As written:
   ```
   Immunity as-is Holder seller Related to defect Against demand-repair
     Holds when True
     Unless known() && Not(disclosed())
   ```
   Proposed, does not parse today (it parses and protects no one): the same without
   `Holds when True`. Saves a line and a silent failure. Same for acts (4 here).
5. **A scenario-local name for a long instance.**
   `repair-due(Grace, Leo, Corolla, "cracked frame")` is written 4 times in one scenario.
   Proposed, does not parse today: `Let d = repair-due(Grace, Leo, Corolla, "cracked frame").`
   then `?d. ?violated d. ?!d.` (Deed's notes ask for the same.)
6. **Paying a stated price.** As written: `Related to car, usd` and `Valid when usd == price`, so
   that the scenario can say `pay(Leo, Grace, Corolla, 650000)` and the rule can check it is the
   price. Proposed, does not parse today: `Act pay Actor buyer Recipient seller Related to car
   Pays price`, with a payment of any other amount void. Saves `usd`, the comparison and the
   literal in nine scenario lines.

## Tool defects
1. A span that names a declared `Default` or `Exception` rule is reported as undeclared:
   `FAIL 4.1: spans name undeclared rules: as-is, concealed` for the program in hard 1. Expected:
   accepted, or "as-is is a default rule; a span can name only …". Workaround: the immunity.
2. An `Immunity` with `Against` and `Unless` but no `Holds when` is accepted and never holds.
   Reproduction: delete `Holds when True` from `as-is` in `bill-of-sale.charter`; then
   `pay(Leo, Grace, Corolla, 650000). deliver(Grace, Leo, Corolla). ?!valid demand-repair(Leo,
   Grace, Corolla, "worn clutch").` fails. Expected: a warning that the immunity can never hold.
3. A derived instance of a `Function` coexists with an assigned one for the same key (hard 2).
   This follows 003.7 as written; it is silent, and "one owner per car" is what `Function` is for.

## What a lay author would have guessed
- `Default as-is … Exception concealed Overrides as-is …` and `=> as-is` / `=> concealed` in the
  clause: refused by `check` as above.
- `Function owner … Holds when paid && delivered`: accepted; two owners.
- `Immunity as-is … Against demand-repair Unless …` with no `Holds when`: accepted; protects no
  one.
- `+defect("worn clutch").` before using it: accepted; unnecessary.
- `Immunity … Unless known() && Not(disclosed())` for "does not protect a seller who knew of a
  defect and concealed it": accepted and right the first time.
