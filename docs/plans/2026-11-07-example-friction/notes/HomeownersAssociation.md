# HomeownersAssociation

Files: `Examples/HomeownersAssociation/rules.md`, `rules.charter` (root), `1-association.charter`,
`2-assessments.charter`, `3-fines.charter`, `4-architecture.charter`, `5-amendment.charter`,
`A-proposed-amendment.charter`, `cases/larch-court.charter` (8 scenarios).
`charter check --require-provenance --deny-warnings rules.charter` ends
`ok   Examples/HomeownersAssociation/rules.charter: 7 phrase(s) resolve (37 declared types, 16 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/larch-court.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp`, `?late-fee(5000)` changed to `6000` gave
`[scenario two-thirds-of-the-owners-amend-the-late-fee, phrase 22]:98: query failed: ?late-fee(6000)` and `FAIL`.

## Size

English sentences: 19. Charter lines outside clause blocks and comments: 90. Clause-block lines: 35.
Case lines: 112. Declarations no sentence of the text refers to: 5 (`usd`, the money type; `month`
and `month-begins`, standing in for the calendar; `answer`, the `Yes`/`No` of the hearing;
`amendment`, whose one member `A1` is a second name for the amendment `late-fee-fifty`).

Features asked for: all used. The hearing is a `Finding` over an `Evidenced` fact, and it earns its
place: before the hearing `fine` is `undetermined`, after a "no" it is simply void, and I wrote
neither rule. Approval by silence is one derived fact,
`Holds when approved() || (Held(applied()) For 30 && Not(refused()))`, and was the easiest sentence in
the three examples. The supermajority is a `Count` comparison. The amendment itself uses `Amend`.
The split by article cost nothing beyond a `#require` line per file.

Known issues, counted for this example:

- Clause span cannot name a fact: 4 spans (2.2 `late`, 2.3 `lien`, 4.2 s2 `permitted`, 5.1 `carried`).
  "Unpaid assessments become a lien", the sentence the example was chosen for, is grounded on
  `assessment-due, pay-assessment`; the fact `lien` is named by nothing.
- `Holds when True`: 3 (`give-notice`, `apply`, `vote`).
- `Valid when` repeating `Holds when`: 3 (`hear`, `fine`, `late-fee-fifty`).
- `Created by` unusable: 2 (`month-begins` has no holder; `fine` has no `association`). Both became
  `Creates d()` with the missing components left free, which works because `association` has one
  member and, for assessments, because every owner should get one.
- `Document "x.md"` needing `.` before `#require`: 1.
- Diagnostic on the first line of the block: 2.
- Money in cents: 4 literals in the rules, 29 case lines.
- No calendar: `Fact month Identified by 1..12` and `month-begins(1)`, so that two months' unpaid
  assessments are two duties; `Due within 1` for "due on the first day". A late fee that "bears" on
  day fifteen cannot be recorded on day fifteen, because nothing happens when time passes; it is
  recomputed from today's `late-fee` whenever someone asks, so an amendment of the fee reaches back
  to assessments that were already late ("What was hard" 3).
- Fractions of a group: 1 (the two-thirds rule).
- One-member types written out in cases: `LarchCourt`, `Board`, `ArchitecturalCommittee` appear 53
  times in 112 case lines.

## What was hard

In order. This was the third example; most of its shape came from the first two, and the first
`check` and the first run of the cases had no failure other than the missing approvals.

1. The amendment, as I first wrote it:
   ```
   Amend late-fee-fifty
     Installs { Param late-fee : Money(USD, 2) = 5000 }
     Holds when carried(LateFeeFifty)
     Valid when carried(LateFeeFifty)
   ```
   No diagnostic. `charter run`: `occurred act late-fee-fifty(actor("anyone"))   lawful: yes   valid: yes`,
   then `query failed: ?late-fee(5000)`. The amendment is valid and changes nothing (defect 1).
   Fix: `Creates late-fee(5000)` on the `Amend`.
2. Trying to make the fee a rule with an exception, so that no one need "perform" the amendment:
   ```
   Fact fee Identified by Money(USD, 2)
   Var current-late-fee Identified by fee
     Default original Yields 2500 When True
     Exception amended Overrides original Yields 5000 When carried(LateFeeFifty)
   ```
   `t.charter:1:0: error CHR012: cannot use an integer where an instance of current-late-fee is needed`.
   With `Var v Identified by Int`: `error CHR020: derivation is not stratifiable: v depend on their own absence (through Not, Forall, or an aggregate)`.
   004.12 says a `Var` may declare `Default … Yields` (defect 2). Abandoned; the amendment is an act
   of the board, which the text does not mention.
3. Retroactivity, found by asking rather than by a failure. Farid's assessment is fifteen days late
   under a $25 fee; the amendment carries; `?!valid pay-assessment(Farid, LarchCourt, 1, 17500)` and
   `?valid pay-assessment(Farid, LarchCourt, 1, 20000)` both hold. The committed scenario avoids the
   question by using the next month.
4. `apply … Creates applied()` without `change`: no diagnostic,
   `claim failed: ?lawful make-change("Farid", "cedar fence")`. By now I expected it and had written
   `Creates change, applied()` and, wrongly, `Creates violation, notified()`, which turned out to be
   unnecessary. Across the three examples five string-named things appear in effects; three must
   also be created by hand (`loss`, `guest`, `change`) and two need not be (`bill`, `violation`), and
   I guessed wrong three times out of five.
5. Two thirds. I wrote the cross-multiplied form at once because I distrusted division. Checked
   afterwards what the natural spellings do: `>= 2 / 3 * Count(Foreach owner: owner)` is `>= 0`, so
   an amendment carries with no votes; `>= Count(Foreach owner: owner) * 2 / 3` carries with 3 of 5.
   Both resolve without a warning.

## Improvements (at least five, most valuable first)

### 1. A duty to pay an amount

As written today (7 lines):

```
Duty assessment-due Holder owner Claimant association Related to month
  Due within 1
  Terminated by pay-assessment
Fact late Identified by owner * month
  Holds when Held(assessment-due()) For 15
Act pay-assessment Actor owner Recipient association Related to month, usd
  Valid when (usd == assessment && Not(late())) || (usd == assessment + late-fee && late())
```

Proposed, does not parse today:

```
Duty assessment-due Holder owner Claimant association Related to month
  Owes assessment
  Owes late-fee When Held(assessment-due()) For 15
  Due within 1
```

performed as `pay assessment-due(Boris, LarchCourt, 1) 17500.` A duty that `Owes` is discharged by
payment of exactly what it owes at that moment; each `Owes` line is a rule a span can name, and its
amount is fixed when its condition first holds. Saves 3 of 7 lines here. Concepts removed: a
separate act per duty whose only content is "the amount must be right"; `Terminated by`; the
two-case `Valid when`. It occurs 7 times across my three examples (premium, claim, share, rent,
utility, assessment, fine), 14 declarations whose English is always "X pays Y". It also fixes the
retroactivity in "What was hard" 3.

### 2. An amendment that is what was voted on, and takes effect when carried

As written today (5 lines, plus `late-fee-fifty(Board).` in every case that uses it):

```
Extend Fact amendment Identified by A1
Amend late-fee-fifty Actor board
  Holds when carried(A1)
  Valid when carried(A1)
  Creates late-fee(5000)
```

Proposed, does not parse today:

```
Amend late-fee-fifty
  Effective when carried(late-fee-fifty)
  Installs { Param late-fee : Money(USD, 2) = 5000 }
```

with `vote(Dev, late-fee-fifty)`. An `Amend`'s name is a value owners can vote on; it is in force
from the first phrase at which `Effective when` holds, with no actor; installing a `Param` sets it.
Saves 2 lines and a case line. Removes: the second name (`A1`), an act by the board that Article 5
does not contain, the `Holds when`/`Valid when` pair, and the defect that the form I wrote first is
a silent no-op. Occurs once here; every agreement with an amendment clause has it.

### 3. A fraction of a group

As written today:

```
  Holds when Count(Foreach owner: owner When voted(owner, amendment)) * 3
               >= Count(Foreach owner: owner) * 2
```

Proposed, does not parse today:

```
  Holds when AtLeast(2 / 3, Foreach owner: voted(owner, amendment))
```

`AtLeast(n, Foreach xs: c)` for "at least n of", `AtLeast(n / d, Foreach xs: c)` for "at least that
fraction of", computed exactly. Saves 1 line and about 60 characters. Removes the cross-multiplication
the author must derive, and two spellings that resolve and are wrong (`2 / 3 * Count(…)` is zero).
Occurs once here; it is the same pattern as the known "at least two of".

### 4. A string-named thing exists once something is said about it

As written today:

```
Act apply Actor owner Recipient committee Related to change
  Holds when True
  Creates change, applied()
```

Proposed (parses today; derives nothing today):

```
Act apply Actor owner Recipient committee Related to change
  Holds when True
  Creates applied()
```

A rule over a `String` component should range over the values that occur in facts that hold.
Saves one token per act; removes a silent failure whose need the author cannot predict (3 needed,
2 not, across my examples; see "What was hard" 4).

### 5. Ask whether an act occurred, and whether it was lawful

As written today, the link between Article 4 and Article 3 is a string the case author invents:

```
  make-change(Farid, "cedar fence").                       // reported: occurred, unlawful
  give-notice(Board, Farid, "fence without approval").
```

Proposed, does not parse today:

```
Finding hear Actor board Recipient owner Related to change, answer
  …
  Holds when Occurred(make-change(owner, change)) && Held(notified()) For 10
```

and, more generally, `Unlawful(a(…))` beside the existing `Enabled`, `Violated` and `Holds`. The
tool already reports the three answers for every performed act; a rule cannot read them. "A
violation of these rules" (3.1) therefore has no referent in the program: the board can find
anything. Saves no lines; lets one article refer to a breach of another. Occurs once here.

### 6. A finding that answers a question (second occurrence)

The six lines of `hear` are, name for name, the six lines of `decide-cause` in RentersInsurance:
an `answer` type, two `Resolves` differing by a `!`, and a `Holds when` equal to the `Valid when`.
Proposed, does not parse today:

```
Finding hear Actor board Recipient owner Decides committed()
  When Held(notified()) For 10
```

Saves 4 of 6 lines. Writing the same workaround a second time is the report.

### 7. One-member types in cases (second occurrence)

As written today: `pay-assessment(Boris, LarchCourt, 1, 17500).`, `hear(Board, Elif, "boat on the lawn", Yes).`
Proposed, does not parse today: `pay-assessment(Boris, 1, 17500).`, `hear(Elif, "boat on the lawn", Yes).`
53 tokens in 112 case lines carry no information.

## Tool defects

### 1. `Amend … Installs { Param … }` is valid and has no effect

```
Param fee = 25
Amend raise
  Installs { Param fee = 50 }
  Holds when True
  Valid when True
.
raise("board").
?fee(50).
```

Expected: `fee(50)`, or a diagnostic that an `Installs` cannot set a parameter. Actual: the act is
reported lawful and valid and `t.charter:8: query failed: ?fee(50).` Workaround:
`Creates fee(50)` on the `Amend`.

### 2. A `Var` cannot have `Default … Yields`

```
Var v Identified by Int
  Default a Yields 1 When True
.
?v(1).
```

Expected: `v(1)` (004.12: "a `Function` or `Var` may declare `Default r Yields v When c`").
Actual: `t.charter:1:0: error CHR020: derivation is not stratifiable: v depend on their own absence (through Not, Forall, or an aggregate)`.
Over a `Money` fact type the same declaration gives
`CHR012: cannot use an integer where an instance of current-late-fee is needed`. The same two lines on
a `Function` over a one-member key work. Workaround: not used.

### 3. Silent non-derivation over a string component

`Fact permitted Identified by owner * change  Holds when approved() || (Held(applied()) For 30 && Not(refused()))`
never holds unless some act also `Creates change`. No warning. Specified by 004.7; reported because
it failed silently in each of my three examples.

### 4. An article file cannot pass `--require-provenance` by itself

`charter check --require-provenance 3-fines.charter`:
`error CHR029: normative rules declared with provenance coverage \`partial\``, because the `Document`
line is in the root. `Examples/README.md` says an article "can be checked alone"; that is true only
without the gate. The pilot `LivingTrust/4-duties.charter` behaves the same. Workaround: check the
root.

## What a lay author would have guessed

- `Installs { Param late-fee … = 5000 }` for "the late fee is amended to fifty dollars". Accepted,
  does nothing.
- That an amendment carried by the owners' votes is thereby in force. It is not until somebody
  performs it; the program has the board do so.
- That a late fee incurred at $25 stays $25 when the fee is later raised. It does not.
- `>= 2 / 3 * Count(Foreach owner: owner)` for two thirds. Accepted, always true.
- `Creates applied()` without `Creates change`. Accepted, and the application can never be approved
  by silence.
- That "the board" could be three directors without a page of voting rules. I made the board, the
  committee and the association one-member types; the English was written to match and says
  nothing about how those bodies decide.
- That a fine for "a violation of these rules" would have to point at a rule that was broken. It
  points at a string.
