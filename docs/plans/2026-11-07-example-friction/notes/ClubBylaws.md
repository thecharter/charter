# ClubBylaws

Files: `Examples/ClubBylaws/bylaws.md`, `bylaws.charter` (root), `1-purpose.charter`, `2-members.charter`,
`3-meetings.charter`, `4-board.charter`, `5-amendment.charter`, `6-adoption.charter`,
`S-proposed-amendments.charter`, `cases/garden.charter` (9 scenarios).

Final lines:
- `charter check --require-provenance --deny-warnings bylaws.charter` ->
  `ok   bylaws.charter: 17 phrase(s) resolve (56 declared types, 19 clauses, coverage complete, 0 warning(s))`
- `charter test --deny-warnings cases/garden.charter` -> `1 passed, 0 failed, 1 total`
- Mutation (copy under `/tmp/cf-club/mut`): nine claims flipped, one per scenario ->
  `FAIL cases/garden.charter: 0 error(s), 9 failed claim(s)`.
- 5.2 makes a difference: with `-entrenched(GardenClub).` at the top of a scenario, `?valid repeal-no-profit(GardenClub)`
  holds and `pay-profit(GardenClub, Ada, 50000)` becomes lawful; with the immunity in place both are refused. With
  `Protects pay-profit` deleted the immunity still protects itself and nothing else.

## Size

English sentences: 25. Charter lines outside clause blocks and comments: 150. Clause-block lines: 42.
Case lines: 130. Declarations no sentence of the text refers to: 7
(`usd`; `in-session`; the event `meeting-ends`; `incumbent`; and three facts the `motion` module derives that nothing
reads: `dues-motion-two-thirds`, `motion-two-thirds`, `amendment-carried`).

Ratio: 6 lines of Charter per English sentence, before the clause blocks.

Known issues, how often each bit:
- Clause span cannot name a fact, derived fact, parameter or event: 7 spans. 1.1 (the purpose), 2.1 "The annual dues are
  thirty dollars" (a `Param`), 3.2 the definition of quorum (a `Bool`; I named `attend` there, which is the nearest
  act, not the meaning), 4.1 the three offices, 4.2 "receives the most votes" (the fact `leads`), 6.1 and 6.2.
  It also cut the other way once: see hard item 1.
- `Approved`: 19 stamps; `tools/approve-clauses` run on each of 7 files.
- `Holds when True`: 11 (5 of them on the three `Amend`s and the two rules they install).
- `Valid when` repeating `Holds when`: 3 written (`vote-aye`, `vote-nay`, `vote-for`), which the module expands to 9.
  Here the repetition is load-bearing: without `Valid when`, a non-member's vote is unlawful and still counted.
- Money ceremony: `Fact usd`, `Param dues : Money(USD, 2) = 3000`.
- `Created by` / `Terminated by`: unusable for `meeting-due` (the meeting ends every officer's duty, not the
  actor's, and `open-meeting` does not carry `club`), so one explicit `Creates (Foreach …)` and one `Terminates (Foreach …)`.
- `Document "x.md".` before `#require`: 1.
- Diagnostics at the first line of the block: did not bite; this example produced no resolve error at all.
- No "at least a third of": `Count(Foreach person: person When …)` written 10 times.

Distortions from "no calendar, executed instance":
- "one year" is 365 days three times (membership, term of office, the yearly meeting).
- 2.2: each membership runs from that member's own payment. A club year with dues falling due on a date cannot be said.
- 3.1 "at least once a year" became "within 365 days after the last meeting ended", and for the founding board
  "within 365 days of adoption".
- 3.1 "giving every member notice" is one `Bool called`; nobody in particular is notified, and what the notice says
  (5.1 in a real club would require the notice to set out the amendment) is not represented.
- The text never says a meeting ends. The program needs it (to clear the room and the ballots and restart the
  year), so there is an `Event meeting-ends` with no sentence behind it.
- 6.2: founding officers have no term; 4.3's year applies only to elected ones.

## The article split

| File | `#require`s | Why | Checks alone (`check --deny-warnings`) |
|---|---|---|---|
| `1-purpose` | none | | yes |
| `2-members` | 3 | 2.3 changes the dues "by a motion at a meeting": needs the `motion` module and `quorum` | yes |
| `3-meetings` | 1 | `member` for the quorum, `officer` for "the board calls" | yes |
| `4-board` | 3 | elections and removal happen at a meeting; extends `meeting-ends` | yes |
| `5-amendment` | 3 | the `motion` module; and Article 1's `pay-profit`, to protect it | yes |
| `6-adoption` | 2 | performs `pay-dues` for the founders; asserts `officer`, `meeting-due` | yes |
| `S-proposed-amendments` | 4, 5 | repeals `remove`, `pay-profit`, `entrenched`; uses the amendment ballot | yes |

All seven resolve alone (`coverage partial`); none passes `--require-provenance` alone (`CHR029`, no `Document`).

- **Two cycles in the English, both broken by hoisting.** Article 2 needs Article 3 (dues are changed by a motion)
  and Article 3 needs Article 2 (a quorum is a third of the *members*). Article 3 needs Article 4 (the *board* calls the
  meeting) and Article 4 needs Article 3 (officers are elected at a meeting). `#require` cannot express a cycle
  (and see OperatingAgreement tool defect 3), so `member`, `office` and `officer` are declared in `1-purpose.charter`.
  That file now has six shared declarations and one rule of its own; its header comment has to apologise for it.
  Bylaws define their terms where they use them and refer forwards and backwards freely; a file per article cannot.
- **Load order is not document order.** The root lists 1, 2, 3, …; because 2 requires 3, the declarations load as
  1, 3, 2, 4, 5, 6, S. Harmless here, but the root's "in the document's order" is only cosmetic.
- **A general sentence in an early article about later rules** (3.2 "A meeting without a quorum decides nothing").
  The decisions are `set-dues` (Art. 2), `elect`, `remove` (Art. 4) and the amendments (Schedule). Naming them from 3.2
  would make every file that requires Article 3 fail alone (`spans name undeclared rules`). Two things avoided it:
  `quorum()` is inside the module's derived facts, so every instance inherits it; and Article 3 got its own instance
  (`Use motion(question) As motion`, `Power resolve`) for free-text motions, so 3.2 and 3.3 have a rule to name in
  their own file. The second is defensible (3.3 does talk about "a motion") but I would not have written it if the
  clause had been allowed to name `quorum`.
- **A later article adding to an earlier rule** worked well with `Extend`: `4-board.charter` says
  `Extend Event meeting-ends Terminates (Foreach choice: choice)`, and the module body carries
  `Extend Event meeting-ends Terminates (Foreach aye: aye), (Foreach nay: nay)`, so each ballot clears itself.
- **5.1's rule is not in Article 5.** As in OperatingAgreement, the amendment threshold exists only as the
  `Valid when` of each `Amend` in the schedule. 5.1's span names the two vote acts.
- The module is declared in Article 3 and instantiated in 3, 2, 4 and 5. No friction.
- Genesis lives in `6-adoption.charter`: three acts performed at load (`pay-dues(Ada, 3000).` …) and six assertions.

## What was hard

Much less than OperatingAgreement, because the lessons carried over. In order:

1. The end of a meeting. First: `Act adjourn Actor person Holds when in-session() Creates … Terminates …`.
   Diagnostic, from every file: `FAIL rules with no English: adjourn (add a Norm span or a From clause)`.
   The diagnostic is right: no sentence mentions adjournment. The honest choices were to name `adjourn` under a
   sentence that does not mean it, or to respell it. `Event meeting-ends` with the same effects, including creating
   the officers' duties, needs no English and passes. (So the coverage rule is: effects need English if an actor
   causes them, and not otherwise.)
2. Votes at a meeting. Without `Valid when` on the vote acts, the scenario
   `only-members-present-vote-and-a-tie-does-not-carry` shows the absent member's and the non-member's votes
   counted (D5: an unlawful act keeps its effects). One attempt, but only because Tenancy had taught me.
3. Planning the files: the two cycles above. No diagnostic; the design had to change before a line was written.
4. "A meeting without a quorum decides nothing" had no rule in its own article (above).
5. Counting people. The natural spellings, tried afterwards in `/tmp/cf-club/g*.charter`:
   `Count(present)` -> `error CHR003: expected Foreach but found identifier present`;
   `Count(Foreach person: present(person))` -> accepted, and equals 3 when nobody is present (tool defect 2).

`For 365` (membership, term of office), `Param` as a threshold (`usd >= dues`), `Function officer … For 365`,
`Immunity … Against Amend Protects`, the three `Amend`s, and `Extend` inside a module all worked first time.

## Improvements (most valuable first)

### 1. A vote at a meeting is a clause of the act it decides

Today (`3-meetings.charter`, 22 lines, then one `Use` and one power per decision; `4-board.charter` shown):

```
Module motion(subject) {
  Fact aye Identified by person * subject
  Fact nay Identified by person * subject
  Act vote-aye Actor person Related to subject
    Holds when member(person) && present(person)
    Valid when member(person) && present(person)
    Creates aye()
    Terminates nay()
  Act vote-nay Actor person Related to subject
    Holds when member(person) && present(person)
    Valid when member(person) && present(person)
    Creates nay()
    Terminates aye()
  Fact carried Identified by subject
    Derived from carried(aye.subject)
      When quorum() && Count(Foreach person: person When aye(person, aye.subject))
                         > Count(Foreach person: person When nay(person, aye.subject))
  Fact two-thirds Identified by subject
    Derived from two-thirds(aye.subject)
      When quorum() && Count(Foreach person: person When aye(person, aye.subject)) * 3
                         >= (Count(Foreach person: person When aye(person, aye.subject))
                             + Count(Foreach person: person When nay(person, aye.subject))) * 2
  Extend Event meeting-ends Terminates (Foreach aye: aye), (Foreach nay: nay)
}
Placeholder incumbent For person
Use motion(incumbent) As removal
Power remove Actor club Recipient incumbent
  Holds when True
  Valid when removal-two-thirds(incumbent)
  Terminates (Foreach office: officer(office, incumbent))
```

Proposed, does not parse today:

```
Electorate meeting Of member When present(member) Quorum 1/3 Of member
Power remove Actor club Recipient officer
  Decided by meeting At least 2/3 Of voting
  Terminates officer(office, officer)
Power set-dues Actor club Related to usd
  Decided by meeting More for Than against
  Creates dues(usd)
```

with scenario phrases `Dev votes for remove(GardenClub, Carmen).` and `Ada votes against remove(GardenClub, Carmen).`

Saves: the module (22 lines), 4 `Use` lines, 2 placeholders, the types `question` and `amendment` and their atoms, 3
unused derived facts, the ballot-clearing `Extend`, 3 `Holds when True`. It removes 12 generated names
(`removal-vote-aye`, `removal-aye`, `removal-two-thirds`, …) that only convention ties to `remove`. It makes 3.2, 3.3,
4.4 and 5.1 each one nameable line. Occurrences: 4 ballots (`dues-motion`, `motion`, `removal`, `amendment`) deciding
7 acts. Same proposal as OperatingAgreement 1, where the electorate is `Weighted by capital`; the two examples
together are 9 ballots and 12 decided acts.

### 2. `Count` of a fact

Today (`3-meetings.charter`):

```
Bool quorum
  Holds when in-session()
    && Count(Foreach person: person When present(person) && member(person)) * 3
         >= Count(Foreach person: person When member(person))
```

Proposed, does not parse today (`Count(present)` is CHR003):

```
Bool quorum
  Holds when in-session() && Count(present && member) * 3 >= Count(member)
```

`Count(f)` is the number of instances of `f` that hold; `f && g` over a shared component is the intersection. Saves
about 30 characters per count and removes the trap in tool defect 2. Occurrences: 10 in this example, 1 in
OperatingAgreement (`dissolved`), 2 in the pilots (LastWill, LivingTrust).

### 3. Entrench what the text entrenches: clauses, not rule names

Today (`5-amendment.charter`), for "Article 1 cannot be amended, and neither can this clause":

```
Immunity entrenched Holder club
  Against Amend
  Protects pay-profit
  Holds when True
```

Proposed, does not parse today (`Protects 1.2` is `CHR003: expected a type identifier (lowercase) but found integer 1`):

```
Entrenched 1.1, 1.2, 5.2
```

Saves 3 of 4 lines, the meaningless `Holder club` and `Holds when True`, and a silent failure: today a second rule
grounded in Article 1 is unprotected unless someone remembers to add it to `Protects`, and `check` cannot notice
because it does not know that "Article 1" means "every rule a span of 1.x names". It also needs the author to know that
an entrenchment is spelled as an immunity with a holder. Occurrences: 1.

### 4. The amendment procedure once, for every `Amend`

Today (`S-proposed-amendments.charter`, three times, differing only in the atom):

```
  Holds when True
  Valid when amendment-two-thirds(RemovalByMotion) && Held(called()) For 14
```

plus `Extend Fact amendment Identified by RemovalByMotion, RepealNoProfit, RepealEntrenchment`, three atoms that
shadow the three `Amend` names. Proposed, does not parse today (in `5-amendment.charter`):

```
Every Amend Decided by meeting At least 2/3 Of voting
  Valid when Held(called()) For 14
```

Saves 2 lines per `Amend` and the parallel list of atoms; gives Clause 5.1 a rule to name in Article 5; and an `Amend`
written later cannot forget the procedure. Occurrences: 3 here, 1 in OperatingAgreement.

### 5. Facts that last as long as something else does

Today, across `3-meetings.charter` and `4-board.charter`:

```
Event meeting-ends
  Creates (Foreach office, person: meeting-due(person, club) When officer(office, person))
  Terminates in-session(), called(), (Foreach person: present(person))
  Extend Event meeting-ends Terminates (Foreach aye: aye), (Foreach nay: nay)     // inside the module
Extend Event meeting-ends Terminates (Foreach choice: choice)
```

Proposed, does not parse today:

```
Fact present Identified by person During in-session()
Fact choice Identified by person * office * candidate During in-session()
```

A fact declared `During c` stops holding when `c` does. Saves 3 termination lists in 3 places and the failure mode
where a ballot type added later is not cleared and last meeting's votes count at the next. Occurrences: 5 facts
(`present`, `called`, `aye`, `nay`, `choice`).

### 6. Repealing a prohibition

Today (`S-proposed-amendments.charter`), for "Clause 1.2 is repealed":

```
Amend repeal-no-profit Actor club
  Repeals pay-profit
  Installs {
    Act pay-profit Actor club Recipient person Related to usd
      Holds when True
  }
```

1.2 is a prohibition, which today is spelled as a narrow permission (`Act pay-profit … Holds when Not(member(person))`).
`Repeals pay-profit` alone therefore removes the permission and leaves the payment unlawful for everyone, the
opposite of the sentence; the amendment has to install the wide permission. Proposed, does not parse today:

```
Act pay-profit Actor club Recipient person Related to usd
  Forbidden when member(person)                 // in 1-purpose.charter
Amend repeal-no-profit Actor club
  Repeals 1.2                                   // removes what clause 1.2 grounds: the Forbidden when
```

Saves 4 lines and an inversion the reader has to work out. Occurrences: 1 prohibition here, 1 in LivingTrust
(`mix-with-own-property … Holds when False`).

### 7. "The most votes"

Today (`4-board.charter`):

```
Fact leads Identified by office * candidate
  Holds when Count(Foreach person: person When choice()) > 0
    && Not(Exists candidate': candidate' != candidate
             && Count(Foreach person: person When choice(candidate = candidate'))
                  >= Count(Foreach person: person When choice()))
```

Proposed, does not parse today:

```
Fact leads Identified by office * candidate
  Holds when Most(candidate By Count(choice()))
```

`Most(x By e)`: `x` is the one value with the strictly greatest `e`; nothing holds on a tie or when all are zero.
Saves 4 lines. Occurrences: 1.

### 8. A duty of a body, owed to no one, that recurs

Today (`3-meetings.charter`, `6-adoption.charter`):

```
Duty meeting-due Holder person Claimant club
  Due within 365
… Terminates (Foreach person': meeting-due(person', club))                                   // open-meeting
… Creates (Foreach office, person: meeting-due(person, club) When officer(office, person))   // meeting-ends
+meeting-due(Ada, GardenClub). +meeting-due(Bram, GardenClub). +meeting-due(Carmen, GardenClub).
```

Proposed, does not parse today:

```
Duty hold-meeting Holder officer Every 365 Discharged by open-meeting
```

The grammar requires a `Claimant`; the board's duty has none, so `club` stands in. A removed officer keeps a duty
instance until the next meeting. Saves 2 effect lines and 3 assertions. Occurrences: 1 (LivingTrust 4.2 is the same
shape).

## Tool defects

1. **An approval stays "current" when the rule it approves changes.** In a copy, delete the line
   `  Protects pay-profit` from `Immunity entrenched` in `5-amendment.charter` (so 5.2 no longer protects Article 1).
   `charter check --require-provenance --deny-warnings bylaws.charter` -> `ok … coverage complete`, including
   `ok   5.2: approved mapping current`; the hash `check` asks for is unchanged (`9b3c89d8…`). Expected: 5.2 STALE,
   since 012.8 calls the approval a record that "its spans and meanings were reviewed" and the meaning changed.
   Actual: the hash covers the English only. The scenario `article-one-cannot-be-amended` did fail, which is the only
   thing that caught it.
2. **`Count(Foreach person: present(person))` counts the domain.** `/tmp/cf-club/g9.charter`:
   ```
   Fact person Identified by Ada, Bram, Carmen
   Fact present Identified by person
   .
   ?Count(Foreach person: present(person)) == 0.
   ```
   Expected: holds, or a warning. Actual: `query failed`; the count is 3 with nobody present, and
   `Count(Foreach present: present)` is 3 too. It follows from 010.7 and 004.7, and CHR028 warns only when the body is
   a literal. A quorum written this way is always met. Workaround: `Count(Foreach person: person When present(person))`.
3. **Coverage depends on the keyword, not on what the rule does.** `Act adjourn … Creates meeting-due(…)` ->
   `FAIL rules with no English: adjourn`. `Event meeting-ends` with identical effects -> `coverage complete`. An event
   that creates duties and wipes ballots has as much need of English as an act. (The known issue "a span cannot name an
   event" seen from the other side: here it let me pass.)
4. **Same component twice** (OperatingAgreement defect 1) forced two placeholders here (`candidate`, `incumbent`).
5. **Outside a scenario, a failed query prints the whole source line.** With several phrases on one line
   (`+member(Ada). … ?!quorum(). +present(Ada). ?quorum().`) the message
   `g2.charter:7: query failed: +member(Ada). +member(Bram). …` does not say which query failed.
6. **`charter test` counts stale approvals as failed claims.** Before stamping, a case whose scenarios all passed
   reported `FAIL cases/garden.charter: 0 error(s), 19 failed claim(s)`. Specified (012: provenance checks are claims),
   but it reads as nineteen wrong scenarios.

Probes that found nothing wrong: an `Amend` that repeals the amendment ballot itself is valid (the text does not
entrench it); `Installs { Extend Act pay-profit Holds when True }` does not get round the immunity (void);
`Repeals entrenched` is void (reflexive, as 014.5 says).

## What a lay author would have guessed

- `Count(present)`. CHR003.
- `Count(Foreach person: present(person))`. Accepted; always the size of the domain.
- `Act adjourn` for the end of a meeting. Fails coverage; there is no sentence to hang it on.
- `Immunity entrenched Against Amend Protects pay-profit` with no holder:
  `error CHR003: expected Holder but found atom Against`.
- `Protects 1.2`, `Repeals 1.2`, `Protects Article 1`. `error CHR003: expected a type identifier (lowercase) but found integer 1`.
- `Repeals pay-profit` for "Clause 1.2 is repealed". Accepted; a repealed act is unlawful, so the prohibition gets
  wider, not narrower.
- `+member(Ada) For 365.` for a founder's first year. `error CHR004: expected . to end the phrase but found For`.
  (Performing `pay-dues(Ada, 3000).` at genesis is better anyway.)
- `Use motion(person) As removal`. Accepted, collapses (OperatingAgreement defect 1).
- That an unlawful vote does not count. It does, unless the act also says `Valid when`.
- That the quorum sentence could be written once, in Article 3, as a rule about meetings. It is a conjunct in two
  derived facts and in `elect`.
