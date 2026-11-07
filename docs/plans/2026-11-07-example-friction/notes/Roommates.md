# Roommates

Files: `Examples/Roommates/roommates.md`, `roommates.charter`, `cases/canal-street.charter` (9 scenarios).
`charter check --require-provenance --deny-warnings roommates.charter` ends
`ok   Examples/Roommates/roommates.charter: 8 phrase(s) resolve (35 declared types, 7 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/canal-street.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp`, `?share(Asha, 77777)` changed to `77778` gave
`[scenario rent-is-shared-by-floor-area-and-rounded-down, phrase 1]:5: query failed: ?share("Asha", 77778)` and `FAIL`.

## Size

English sentences: 14. Charter lines outside clause blocks and comments: 82. Clause-block lines: 20.
Case lines: 95. Declarations no sentence of the text refers to: 4 (`usd`, the money type;
`month-begins`, an event standing in for the calendar; `night-falls` and `morning-comes`, two events
standing in for "ten at night" and "seven in the morning").

Features asked for: all used. `MulDivRound` computes the floor-area shares (77,777 + 66,666 + 55,555
cents, two cents short of the rent) and the thirds of a utility bill. Duties: `share-due`, `rent-due`,
`utility-due`, and a derived `guest-leaves`. Unanimous consent appears twice and came out in two
different shapes: a `Forall … When` in the `Valid when` of `take-place`, and, for guests, a derived
duty owed to each roommate who has not consented, which needs no quantifier at all and is the nicer
of the two.

Standard library: tried `lib/exit_and_voice` for "thirty days' notice" (below, "What was hard" 8).
It does not fit and is not in the file.

Known issues, counted for this example:

- Clause span cannot name a fact: 3 spans. M.2's share rule points at `pay-share`; M.6 s1 (what quiet
  hours are) is a `Definition` naming nothing; M.5 s3 ("until then the leaving roommate remains a
  roommate") has no rule at all, because its meaning is that nothing ends `roommate` except
  `take-place`; it names `take-place`.
- `Holds when True`: 1 (`take-place`). Chosen over repeating the `Valid when` as `Holds when`; the cost
  is that an attempt nobody approved is reported lawful.
- `Created by` unusable: 3 duties (`rent-due` and `share-due` from `month-begins`, `utility-due` from
  `show-bill`), each needing a `Foreach` over the people the event does not carry. `Terminated by`
  worked for 2 duties and not for `rent-due`, where one payment discharges three duties.
- Diagnostic on the first line of the block: 4 (three CHR012, one CHR011, all `1:0`).
- Money in cents: 1 parameter, 15 case lines.
- No calendar, no clock: `month-begins` plus `Due within 1` for "by the first of the month" (the duty
  does not exist until the day it is already due); quiet hours "from ten at night to seven in the
  morning" are two events that a case triggers, so the hours in the text mean nothing to the program;
  "at most three nights" is `Due within 4` (below, 9).
- "The settlor" problem: 0 comparisons with a name. The equivalent here is membership: `roommate` is a
  status that changes, so it cannot be a type, and `roommate(person)` is written in 10 conditions
  (improvement 1).

## What was hard

In order.

1. Shares in proportion to floor area, with the areas as `Quantity(sqm)`:
   `MulDivRound(rent, room.area, Sum(Foreach room': room'.area), Floor)` gave
   `t.charter:1:0: error CHR012: cannot use an instance of area where an integer is needed`,
   followed by six `CHR010: undeclared type or placeholder` errors, one for each later phrase that
   mentions anything in the failed block. Fix: areas are bare `int`.
2. `Default by-floor-area Yields MulDivRound(rent, room(person), 36, Floor) When True`:
   `t.charter:1:0: error CHR011: room has 2 component(s), 1 given`. Fix: `Derived from` over `room`.
3. The guest duty, `Holds when staying(guest, person) && …`, with `host` doing `Creates staying()`:
   no diagnostic, and `query failed: ?guest-leaves(Mei, Asha, "Kenji")`. `guest` is a string type, so
   the rule ranges over guests that hold and none does. Fix: `Creates guest, staying()`. (I then added
   `Creates bill` to `show-bill` out of caution. It was not needed, because `utility-due` is created,
   not derived. Nothing tells the author which case they are in.)
4. "A roommate may give notice": `Act give-notice Actor roommate`, with `Fact roommate Identified by person`:
   `t.charter:9:0: error CHR012: cannot use a string where an instance of roommate is needed` on
   `give-notice(Asha)`. Fix: `Actor person` and `Holds when roommate(person)`, five times.
5. "Each of the others pays Asha", with `Var rent-payer Identified by person`:
   `share-due(person, rent-payer)` gave
   `t.charter:1:0: error CHR012: cannot use an instance of rent-payer where an instance of person is needed`.
6. So I wrote `share-due(person, rent-payer.person) When roommate(person) && person != rent-payer.person`,
   as the brief says a `Var` is read (`fund.usd`). It resolved, every scenario passed, and it was
   wrong: `person` is enumerable, so `rent-payer.person` ranges over every person whether or not they
   are the rent payer, and each roommate owed a share to each other roommate. I found it only because
   a scenario written later for a different sentence asserted an absence:
   `[scenario a-replacement-takes-the-place-of-the-leaver, phrase 8]:63: query failed: ?!share-due("Luis", "Asha")`.
   Fix: a second binder, `(Foreach person, person': share-due(person, person') When … rent-payer(person') …)`.
7. `Scenario a-replacement-takes-the-leaver's-place-in-the-agreement {`:
   `cases/canal-street.charter:63:40: error CHR003: expected \`{\` but found \`'\``. (Correct line and
   column; a quoted name would have worked.)
8. The library. `Use exit-and-voice(person, person, person) As leave`, then
   `+leave-cooling-off-window(30). leave-initiate-exit(Mei). @ 30. ?leave-exit-due(Mei).` works as a
   notice period. Under `--require-provenance` it fails:
   `FAIL rules with no English: leave-markers-keep-byte-length, leave-voice-within-budget, leave-one-exit-outcome, leave-exit-due-by-the-bound, leave-no-exit-before-cooling-off, leave-redact, leave-no-censorship, leave-inscribe-voice, leave-cancel-exit-by-default, leave-execute-exit-locally, leave-execute-exit, leave-withdraw-exit, leave-initiate-exit (add a Norm span or a From clause)`.
   One sentence of the agreement would have to be quoted for 13 rules, 11 of which it says nothing
   about; the module adds 34 declarations to replace 4 lines. No module in `lib/` is at the scale of a
   household agreement (a notice period, a split, consent of all).
9. "At most three nights". `Due within 3` is violated at `@ 3`, when the guest has slept exactly three
   nights: `[scenario a-guest-stays-three-nights-unless-everyone-consents, phrase 3]:95: claim failed: ?!violated guest-leaves("Mei", "Asha", "Kenji")`.
   The file says `Due within 4`, a number the text does not contain.

Worked the first time: the whole file resolved on the first `check`, and the first run of the cases
had no failed scenario claim. That is the dangerous part, given 6.

## Improvements (at least five, most valuable first)

### 1. A status as an actor

As written today (5 acts have this shape):

```
Act give-notice Actor person
  Holds when roommate(person)
  Creates leaving(person)
```

Proposed, does not parse today (today it resolves but demands `give-notice(roommate(Asha))`-typed
arguments, CHR012):

```
Act give-notice Actor roommate
  Creates leaving(roommate)
```

Where an `Actor`, `Holder` or binder names a one-component fact, it ranges over the instances that
hold and is written as the underlying value (`give-notice(Mei)`). Saves 5 lines here and 5 further
`roommate(person')` filters inside `Foreach`/`Forall`. Concepts removed: that a role which people can
enter and leave must be modelled as a type plus a fact plus a condition on every act; and, for these
five acts, the rule that an act with no `Holds when` is never enabled. Occurs 10 times.

### 2. A `Var` over names is its value

As written today:

```
        , (Foreach person, person': share-due(person, person')
             When roommate(person) && rent-payer(person') && person != person')
```

Proposed, does not resolve today (CHR012):

```
        , (Foreach person: share-due(person, rent-payer) When roommate(person) && person != rent-payer)
```

A `Param` already works this way (014.1) and a `Param` is a `Var`; extend it to every `Var`. Saves a
binder and a condition, and removes the trap in "What was hard" 6, where the documented reading
(`rent-payer.person`) silently means "any person". Occurs 1 time here (3 uses of `rent-payer`).

### 3. "Each of the others", "every other roommate"

As written today (4 occurrences: two effects, one `Forall`, one derived duty):

```
  Creates (Foreach person': utility-due(person', person, bill, MulDivRound(usd, 1, 3, Floor))
             When roommate(person') && person' != person)
…
    && (Forall person: approved(person, candidate) When roommate(person) && person != leaver)
```

Proposed, does not parse today (`expected ':' but found atom 'Except'`):

```
  Creates (Foreach roommate Except person: utility-due(roommate, person, bill, MulDivRound(usd, 1, 3, Floor)))
…
    && (Forall roommate Except leaver: approved(roommate, candidate))
```

Saves one condition line per occurrence (4 lines) with improvement 1, and the phrase in the program
is the phrase in the text. The text says "the others" or "every other" in 5 of its 14 sentences.

### 4. A duty several people owe jointly

As written today:

```
Duty rent-due Holder person Claimant landlord
  Due within 1
Act pay-rent Actor person Recipient landlord Related to usd
  Holds when rent-due()
  Valid when usd == rent
  Terminates (Foreach person': rent-due(person', landlord))
```

Proposed, does not parse today (`expected a type identifier (lowercase) but found atom 'Jointly'`):

```
Duty rent-due Holder Jointly roommate Claimant landlord
  Due within 1
  Terminated by pay-rent
Act pay-rent Actor roommate Recipient landlord Related to usd
  Valid when usd == rent
```

One duty with several holders: any holder may perform, performance discharges all, each is in breach
while it is late. Saves 1 line and the hand-written `Foreach` that is the whole meaning of M.3
("each roommate is liable for the whole rent"). Occurs once; joint liability is in most leases,
loans and partnerships.

### 5. Initial state where the thing is declared

As written today (declaration at lines 9, 14, 17; values at the last three lines of the file, after
the clause blocks):

```
Fact roommate Identified by person
Function room Identified by person * int
Var rent-payer Identified by person
…
+roommate(Asha). +roommate(Luis). +roommate(Mei).
+room(Asha, 14). +room(Luis, 12). +room(Mei, 10).
+rent-payer(Asha).
```

Proposed, does not parse today (`expected '.' to end the phrase but found '='`):

```
Fact roommate Identified by person = Asha, Luis, Mei
Function room Identified by person * int = Asha: 14, Luis: 12, Mei: 10
Var rent-payer Identified by person = Asha
```

`Param name = n` already does this for integers. Saves 3 lines and 7 `+` phrases; the sentence
"Asha's room is fourteen square metres" and its number end up on the same line as the function it
fills. Occurs 3 times.

### 6. A deadline that means what the text's number means

As written today: `Due within 4` for "at most three nights"; `Due within 14` (violated on day 14)
for "within fourteen days".
Proposed, does not parse today: `Due after 3` for "no longer than three" (violated when held more than
3), keeping `Due within 14` but with day 14 still in time. Saves no lines; removes a number that is
not in the text, and one silent off-by-one per deadline. Occurs 4 times (`Due within` ×4, one of them
knowingly adjusted).

### 7. Ratios of quantities

As written today: `Function room Identified by person * int`, `+room(Asha, 14).`
Proposed, rejected today with CHR012:

```
Fact area Identified by Quantity(sqm)
Function room Identified by person * area
… MulDivRound(rent, room.area, Sum(Foreach room': room'.area), Floor)
```

`MulDivRound`'s numerator and denominator should accept two values of one dimension. Saves nothing;
keeps the unit the text states. Occurs once.

### 8. A `Use` grounded by one span, and modules of this size

As tried today: `Use exit-and-voice(person, person, person) As leave` (13 rules with no English).
Proposed, does not parse today (`expected '.' to end the phrase but found atom 'From'`):

```
Use notice-period(roommate) As leaving From M.5 "A roommate who wants to leave gives the others thirty days' notice"
```

with small modules (`notice-period`, `consent-of-all`, `split`) whose rules are all grounded by the
`Use`. Would replace the 6 lines of `give-notice`/`move-out` and make the library usable in a
program that must pass `--require-provenance`.

## Tool defects

### 1. A `Var` over an enumerable type read by projection ranges over the whole domain, silently

```
Fact person Identified by Asha, Luis, Mei
Var rent-payer Identified by person
Fact owes Identified by person * person'
Event e Creates (Foreach person: owes(person, rent-payer.person) When person != rent-payer.person)
.
+rent-payer(Asha).
e().
?owes(Luis, Asha).
?!owes(Luis, Mei).
```

Expected: `owes(Luis, Asha)` and `owes(Mei, Asha)` only, or a warning. Actual:
`t.charter:9: query failed: ?!owes(Luis, Mei).`; six facts are created. 004.7 specifies it (a binder
over an enumerable type ranges over the domain whether or not the instance holds), so the evaluator
is doing what the chapter says; the defect is that the same spelling means "the current value" for
`Var fund Identified by usd` and "every value" for `Var rent-payer Identified by person`, and
neither CHR025 nor CHR028 fires. Workaround: `rent-payer(person')` with a second binder (adding
`rent-payer &&` to the condition also works).

### 2. One error in a declaration block produces an "undeclared" error for every later mention

Any of the CHR012/CHR011 cases above: the block is dropped, and every later phrase that names
anything from it reports `CHR010: undeclared type or placeholder`. Seven errors for one mistake,
six of them misleading, and the real one is reported at `1:0`. Expected: the one error, at its line.

### 3. `MulDivRound` rejects a ratio of two quantities of the same unit

`MulDivRound(rent, room.area, Sum(Foreach room': room'.area), Floor)` with
`Fact area Identified by Quantity(sqm)`: `CHR012: cannot use an instance of area where an integer is needed`.
010.12 says only that the result keeps `x`'s dimension, and does not say the other two must be bare
integers. Expected: accepted when numerator and denominator have the same dimension. Workaround: `int`.

### 4. Library modules cannot be used under `--require-provenance`

See "What was hard" 8. Expected: either a module's rules are grounded by the module, or `Use` can
carry a `From`. Workaround: not used.

## What a lay author would have guessed

- `Actor roommate`, because the text says "a roommate". Rejected at the first trigger (CHR012).
- `share-due(person, rent-payer)`. Rejected (CHR012). Then `rent-payer.person`: accepted, means
  "anybody".
- `room(person)` for "that person's room". Rejected (CHR011).
- Areas in square metres as a `Quantity`. Rejected inside `MulDivRound`.
- `Due within 3` for "at most three nights". Accepted, and a guest who stays exactly three nights is
  in breach.
- `Holds when staying(guest, person) && …` for the duty, without also creating the guest. Accepted,
  derives nothing.
- An apostrophe in a scenario name. Rejected.
- That quiet hours could be given as hours. There is no time of day; the program has two events and
  the numbers ten and seven appear nowhere in it.
- That "liable for the whole rent" would be one duty. It is three duties and a `Foreach` that ends
  them together.
