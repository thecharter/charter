# NonDisclosure
## Size
English sentences: 10. Charter lines outside clause blocks and comments: 44. Clause-block lines: 18.
Case lines: 77 (8 scenarios, 31 claims; every claim was flipped in a `/tmp` copy and every flip failed).
Declarations no sentence of the text refers to: 2 (`in-term`, `already-known`).

- `in-term` duplicates `handed-over`: one hand-over makes two facts, because the secrecy must
  expire after three years and the duty to return must not.
- `already-known` is a snapshot of `knew` taken at the hand-over, because "already knew before it
  was handed over" compares two moments and a condition can only ask about now.

Known issues, counted: span cannot name a fact, exception, event or parameter, 4 clauses (1.2 the
definition of confidential information, 3.1 the three exceptions, 3.2 the court order, 4.1 the term);
`Valid when` repeating `Holds when`, 1 (`request-return`); `Holds when True`, 0; no calendar, 1
("three years" is 1095 days); `Created by`/`Terminated by` binding by name, 2, both worked first time.

## Which read better: `Except under` or `Default`/`Exception`
`Default`/`Exception`, clearly, and it is what the file uses for 3.1. Both were written and run.

`Except under` (7.2) makes each exception an act. The base case, information never handed over,
must itself be an exception, and none of them can be shared with `use`:
```
Act disclose Actor recipient Related to discloser, item
  Except under disclose-outside-the-term, disclose-public, disclose-known, disclose-developed, disclose-under-order
Act disclose-outside-the-term Actor recipient Related to discloser, item
  Holds when Not(in-term())
Act disclose-public Actor recipient Related to discloser, item
  Holds when public()
… three more, then four again for `use`
```
That is 11 lines and 5 new acts for `disclose`, 9 more lines for `use`, and every one of the 9 acts
is something a party can perform and needs its own span. 3.1 is not about acts at all: it says what
information the clauses "do not apply to". As a defeasible fact it is 5 lines, read by both acts:
```
Fact confidential Identified by discloser * recipient * item
  Default handed-over-in-confidence Holds when in-term()
  Exception public-information Overrides handed-over-in-confidence Rejects when public()
  Exception known-before Overrides handed-over-in-confidence Rejects when already-known()
  Exception independently-developed Overrides handed-over-in-confidence Rejects when developed()
```
3.2, the court order, is a permission to do the act, which is what `Except under` is for. I did not
use it there either: an act with `Except under` ignores its own `Holds when` (see Tool defects 1), so
"lawful when not confidential, or under a court order" cannot mix the two. Two `Holds when` lines,
which are alternatives, say it in 2 lines.

## What was hard
1. **The derived fact derived nothing, silently.** With `Fact item` (a string) the first run gave
   `n1.charter:56: query failed: ?confidential(Tidewater, Juniper, "sensor design").` straight after
   `+in-term(party("Tidewater"),party("Juniper"),item("sensor design"))`. No diagnostic.
   `?why confidential(Juniper, "x")` prints `no assignment and not derived (closed type: does not
   hold)`. I reduced it to a plain `Holds when in-term() && Not(public())`, which also derives
   nothing: a rule over a string-domain component ranges only over strings that themselves hold as
   `item("…")` (004.7), and handing a thing over does not make it an `item`. Fixed by making the
   case file enumerate the items (`Extend Fact item Identified by SensorDesign, PricingModel, Roadmap.`),
   as the pilots do for people. Every lawfulness claim that depended on it failed in the permissive
   direction: disclosure of a secret was lawful.
2. **`Holds when` together with `Except under`.**
   `Act disclose … Holds when Not(confidential())` / `Except under compelled-disclosure`.
   No diagnostic; `n6.charter:61: claim failed: ?lawful disclose(Tidewater, Tidewater, SensorDesign).`
   The `Holds when` is not consulted.
3. **"Already knew before it was handed over."** First written as
   `Exception known-before … Rejects when knew()`. It passes until the recipient learns the thing
   elsewhere after the hand-over, which then frees it. Needed a second fact and a conditional
   effect on `hand-over` (`already-known() When knew()`).

Nothing else took more than one attempt. `Creates in-term() For term` did the three years in one
phrase and was right on the first run (unlawful on day 1094, lawful on day 1095).

## Improvements (most valuable first)

1. **Write a prohibition as a prohibition.** 2 times here (`disclose`, `use`); also `disclose` and
   `solicit` in Employment. The text says when the act is forbidden; the rule must say when it is
   permitted, so every condition is negated and every exception becomes a second alternative.
   Today:
   ```
   Act disclose Actor recipient Related to discloser, item
     Holds when Not(confidential())
     Holds when ordered() && notified()
   Act use Actor recipient Related to discloser, item, purpose
     Holds when Not(confidential()) || purpose == ConsideringTheVenture
   ```
   Proposed, does not parse today (`Forbidden when` gives `error CHR004: expected `.` to end the
   phrase but found atom `Forbidden``):
   ```
   Act disclose Actor recipient Related to discloser, item
     Forbidden when confidential()
     Unless ordered() && notified()
   Act use Actor recipient Related to discloser, item, purpose
     Forbidden when confidential()
     Unless purpose == ConsideringTheVenture
   ```
   Same line count. Saves the author the inversion, and each line now matches one sentence
   (2.1, 3.2; 2.2). An act with only `Forbidden when` is otherwise lawful, which also removes
   `Holds when True`.

2. **A rule over a string should range over the facts it reads.** 1 time, and it cost the most.
   As first written (resolves today, derives nothing, reports nothing):
   ```
   Fact item
   Fact confidential Identified by discloser * recipient * item
     Default handed-over-in-confidence Holds when in-term()
   ```
   Proposed: the same text, with `item` bound from the instances of `in-term` that hold; failing
   that, a warning at the declaration, `confidential is derived over item, which has no instances`.
   Saves a concept (enumerable against held domains) that no reader of an NDA has.

3. **A list of exceptions.** 3 exceptions here. Today each repeats the default's name and
   `Overrides … Rejects when` (the block quoted above; 3 × 48 characters of connective).
   Proposed, does not parse today (`error CHR004: expected `.` to end the phrase but found atom `Unless``):
   ```
   Fact confidential Identified by discloser * recipient * item
     Holds when in-term()
     Unless public(), already-known(), developed()
   ```
   `Unless` already has this meaning on `Immunity`. Saves 3 lines and 4 rule names that nothing can
   refer to (a span cannot name them; improvement 6).

4. **Compare two moments.** 1 time here (and "within twenty-one days after the termination" in
   Employment). Today:
   ```
   Fact already-known Identified by discloser * recipient * item
   Act hand-over Actor discloser Recipient recipient Related to item
     Holds when discloser != recipient
     Creates handed-over(), in-term() For term, already-known() When knew()
   …
     Exception known-before Overrides handed-over-in-confidence Rejects when already-known()
   ```
   Proposed, does not parse today:
   ```
     Exception known-before Overrides handed-over-in-confidence Rejects when knew() Before handed-over()
   ```
   Saves one fact and one conditional effect, and the wrong first version (What was hard, 3).

5. **World input declared once.** 4 times: `public`, `knew`, `developed`, `ordered`. Today a fact and
   an event that does nothing but create it:
   ```
   Fact public Identified by item
   Event publication Related to item Creates public()
   ```
   Proposed, does not parse today: `Input Fact public Identified by item`, asserted in a case as
   `+public(SensorDesign).` and distinguishable by `check` from a `+fact` that an act should have
   made. Saves 4 lines and 4 names.

6. **A span that names the exception.** Today
   `Norm "Clauses 2.1 and 2.2 do not apply to information that is public, … developed independently." => disclose, use, hand-over`.
   Proposed, does not parse today: `=> public-information, known-before, independently-developed`.
   As it stands, deleting an exception from `confidential` invalidates no approval.

7. **A clause should not be typed twice.** 8 clauses, 10 spans, 18 lines, all retyped from `nda.md`.
   Today:
   ```
   Clause 2.2 Approved "…64 hex…"
     Norm "The recipient uses the discloser's confidential information only for the purpose." => use
   ```
   Proposed, does not parse today: `Clause 2.2 => use`, the text read from the paragraph numbered
   2.2 in the document.

8. **Arguments by position among parties of one type.** 46 of 77 case lines name both parties, and
   the order differs by declaration: `hand-over(Tidewater, Juniper, SensorDesign)`,
   `?confidential(Tidewater, Juniper, SensorDesign)`, but `disclose(Juniper, Tidewater, SensorDesign)`
   and `return-due(Juniper, Tidewater, SensorDesign)`. Swapping two parties is never an error; it is
   a different, well-typed claim. Proposed, does not parse today: the actor in front,
   `Juniper: disclose(Tidewater, SensorDesign).`, so the remaining arguments are in the
   declaration's reading order and the one that matters cannot be misplaced.

9. **Three years.** `Param term : Duration = 1095`. Proposed, does not parse today: `= 3 years`.

## Where no calendar and no blanks distorted the agreement
- "Three years" is 1095 days.
- "Whatever a party marks as confidential" is the act `hand-over` itself; an unmarked hand-over
  cannot be said and is simply not in the program.
- The parties and the purpose are fixed atoms; `purpose` has a second atom, `AnythingElse`, only so
  that a use outside the purpose can be named.

## Tool defects
1. **`Holds when` on an act that also has `Except under` is ignored without a word.**
   ```
   Fact p Identified by A
   Bool free
   Act open Actor p Holds when False
   Act go Actor p
     Holds when free()
     Except under open
   .
   +free().
   ?lawful go(A).
   ```
   Expected: lawful, or a warning that `Holds when` has no effect beside `Except under` (007.2 says
   it is "not consulted"). Actual: claim fails, 0 warnings. Workaround: no `Except under`.
2. **A derived fact over a string-domain component derives nothing and `?why` does not say why.**
   Reproduction in What was hard, 1. Expected: a warning at the declaration, or `?why` naming the
   unbound component. Actual: `no assignment and not derived (closed type: does not hold)`.
   Workaround: enumerate the items in the case file.
3. **A `Default` with no name gets the wrong message.** `Default Holds when in-term()` gives
   `q3.charter:6:3: error CHR004: expected `.` to end the phrase but found atom `Default``.
   Expected: "`Default` needs a rule name". Workaround: name it.

## What a lay author would have guessed
- `Fact item` and things named in quotes, `hand-over(Tidewater, Juniper, "sensor design")`: accepted,
  and every derived fact about it empty.
- `Act disclose … Forbidden when confidential()`.
- `Holds when in-term()` / `Unless public()` on a fact.
- `Default Holds when …` without a name: the name is not used anywhere the author can see.
- `Exception known-before … Rejects when knew()` for "already knew before it was handed over".
- `Act disclose … Holds when Not(confidential())` plus `Except under compelled-disclosure`.
- A `Duty` of secrecy that lasts three years. It can be written (`Duty … Violated when disclosed()`
  created `For term`), but then a breach is a fact about a later state, not a judgment of the
  disclosure when it is made, and the exceptions have to be recorded at that moment too.
