# What twenty ordinary agreements cost to write in Charter

**Date:** 2026-11-07. **Status:** findings and proposals for ruling. Nothing here is decided.

Twenty agreements a person might actually sign were written in Charter 1.0.1, each with its
English, its specification and cases: `Examples/` (index in `Examples/README.md`). The purpose
was documentation, and, more than that, to find where the language gets in the way. The
standard: these agreements should be dreadfully easy to write.

All twenty pass `charter check --require-provenance --deny-warnings` with complete coverage, and
their 166 scenarios pass (`tools/examples-check`). They were not easy to write. This file says
why, ranks what would fix it, and lists the defects found on the way.

- `notes/<Example>.md`: one file per example. What was hard, in order, with the diagnostics;
  five to ten improvements each, with the lines as written and the lines as wished; tool
  defects; what a lay author would have guessed first.
- `reproductions/`: eighteen defects as runnable files. Each passes today because its claims
  state the wrong answer; when a defect is fixed its file fails.
- `brief.md`: the brief the example writers worked from.
- `tools/examples-metrics`: the counts below, recomputed on demand.

Three examples (will, trust, deed) were written first to fix the pattern. The other seventeen
were written by five agents new to the language, so their first guesses are a newcomer's.
The proposed spellings are sketches. None parses today, and several touch a law or a ruled
decision; those are marked.

## The numbers

Across the twenty examples (5,542 words of English, 191 clauses):

| Measure | Count |
|---|---:|
| Lines of rules and declarations | 1,323 |
| Lines of `Clause` blocks | 453 (26% of every specification) |
| English retyped inside `Clause` blocks | 24,814 characters |
| `Approved` digests | 191, 14,325 characters |
| Declarations a clause can name (acts, duties, immunities, invariants) | 219 |
| Declarations a clause cannot name (facts, derived facts, events, parameters) | 372 |
| Spans that name nothing | 33 |
| `Power`s | 51, of which 20 repeat a condition in `Holds when` and `Valid when` |
| `Holds when True` | 53 |
| `x == Name` comparisons to say who a party is | 54 |
| `Count(Foreach …)` | 18 |
| Empty applications `f()` | 414 |
| Lines of cases | 1,885 |

The per-example table is at the end.

## What to change, most valuable first

### 1. Cite a passage; do not retype it

Every clause of every agreement is typed twice, once in the Markdown and once in a `Clause`
block, and then stamped with a 64-character digest. That is a quarter of each file, and it is
the part an author is most likely to get wrong by a comma.

Today (`Examples/Employment/employment.charter`):

```
Clause 1.3 Approved "9d1c0b921eafc5f2bb3427732cefa5dc39973ae67120b186e60d329a4bffc9c9"
  Norm "The employee gives the employer fourteen days' notice before she leaves." => give-notice, leave
  Norm " Leaving without that notice is a breach of this agreement, but it still ends the employment." => leave
```

Proposed:

```
Clause 1.3 => give-notice, leave
```

The checker reads the text of 1.3 from the document, under its number or heading. A clause is
split into spans only where its sentences mean different rules, and then by sentence
(`Clause 1.3/1 => give-notice`). Approvals live in `charter.lock`, written by `charter approve`.
`tools/approve-clauses` exists only because that command does not.

This reopens D4. Its stated condition is "authors find `Clause` blocks unreadable beside the
Markdown". Six notes raise it unprompted and all twenty examples pay it.

### 2. Let a clause name a fact

A span can name an act, a duty, an immunity or an invariant. It cannot name a fact, a derived
fact, a named `Default` or `Exception`, a parameter or an event. Most of what these documents
say is exactly those things: a gift, who the executor is, what counts as marital property, what
a policy covers, when a release takes effect.

So the spans point at whichever act happens to read the fact. Six of the will's seven clauses
name `distribute`. Six of the insurance policy's fifteen normative spans name `pay-claim`. In the
prenup the program has a named rule for each sentence and cannot cite one of them:

```
Fact marital Identified by asset
  Default owned-before Rejects when premarital()
  Default acquired-during Holds when Not(premarital()) && (Exists person: owner())
  Exception gift-or-inheritance Overrides acquired-during Rejects when by-gift()
…
  Norm "All other property either party acquires during the marriage is marital property." => take-half
```

Proposed: `=> acquired-during`. And `check` requires every named `Default` and `Exception` to
be cited, as it does for acts.

This is the cheapest change on the list and it makes the provenance true. Today
`charter trace N.3` says clause N.3 means `take-half`, which is clause N.5. Sixteen of twenty
notes raise it.

A related silence: coverage depends on the keyword. `Act adjourn … Creates meeting-due(…)` must
be cited; `Event meeting-ends` with the same effects need not be.

### 3. Say a power's condition once

A `Power` must have a `Valid when`, and an act with no `Holds when` is never enabled. So the
common case, "may do this, and otherwise it has no effect", is written twice:

```
Power dismiss Actor person Related to agent
  Holds when person == Walter
  Valid when person == Walter
```

Twenty of fifty-one powers do this, and `Holds when True` appears fifty-three times. Proposed:
on a `Power`, a missing `Holds when` means "lawful exactly when valid", and a missing condition
on an act with effects means "anyone may".

```
Power dismiss Actor principal Related to agent
```

D5 says it reopens "if nearly every act needs `Valid when` written". The second half touches
Law 12: an eFLINT act with no `Holds when` is postulated, so the new default can apply only to
`Power`, or under a file-level mode.

It would also remove a trap that matches the spec: after `Holds when` a comma means "or", and
after `Valid when` it means "and" (`reproductions/10`).

### 4. Name each party once

There is no way to say that Marcus is the agent. Each rule compares: `agent == Marcus`, fifty-four
times. A rule that forgets the comparison lets a stranger act, and nothing warns. Worse, an atom
that is not even a member of the actor's type performs the act validly (`reproductions/03`).

Proposed:

```
Role principal Is Helen
Role agent Is Marcus
Power give Actor agent Recipient third Related to usd
  Valid when authority() && usd <= gift-limit
```

Three further cases of the same idea came up:

- **A status as an actor.** In the roommate agreement, who is a roommate changes, so it cannot
  be a type, and `roommate(person)` is written in ten conditions. Proposed: `Actor roommate`,
  where `roommate` is a fact about a person.
- **Succession.** "Daniel, or if he cannot act, Priya" took three default and exception rules
  in the will, the trust and the directive. Proposed: `Role executor Is Daniel Then Priya Unless declined() || deceased()`.
- **Cases.** When a role has one member, a case should not have to name it. Two examples found
  that this already works if each role is its own one-member type (`dismiss().`,
  `?violated salary-due(month = 1).`). The pilots did not use it; the others name both parties
  on 46 of 77 lines (NDA) and 30 of 90 (return policy).

### 5. Money written as money

```
Fact usd Identified by Money(USD, 2)
Param price : Money(USD, 2) = 40000000
Var paid Identified by usd
+paid(0).
```

for a price of $400,000 and a running total. The author must know cents, the carrier type, that
a variable needs a starting value asserted elsewhere, and whether to write `paid` or `paid.usd`.
Proposed:

```
Param price = $400,000.00
Var paid : USD = $0
```

Three defects make this worse than verbose. `10000.00` is accepted and means one hundred
dollars (`reproductions/06`). A variable with no starting value swallows the first payment
(`reproductions/11`). A binder over a money type is silently empty, so
`Sum(Foreach asset, usd: …)` awarded each spouse $0 (`reproductions/07`).

### 6. Compare two moments

Twelve notes needed "within N days of X" and each built it by hand, usually wrongly first.
`Held(f) For n` asks how long a fact has held now. It cannot ask whether one thing happened
within a period of another, or what was true when something happened.

Today (will, "does not survive me by thirty days"):

```
Event death Related to person
  Creates deceased(person)
        , lapsed(person) When person != Margaret && Not(Held(deceased(Margaret)) For survivorship)
```

Proposed: `deceased(beneficiary) Within survivorship Of deceased(Margaret)`, with `Before`,
and `c At e` for "as it stood when e happened". The prenup needed a second flag for exactly
that; without it, a claim made late on a timely divorce was void.

Four defects sit under this:

- `Held(e) For d` is false inside a `Holds when` when `e` is derived, and true as a query
  (`reproductions/04`).
- A derived fact is stamped when a phrase first sees it, so a deadline depends on which days
  the scenario visits. `@ 30. @ 45.` produces a late fee; `@ 45.` alone does not. This matches
  009.3 and is a wrong answer.
- `Due within 3` is breached at `@ 3`. A person told "within three days" has until the end of
  day three.
- A due date and a breach date are one number (`Due within 5 + grace`), so "late but not in
  breach" cannot be asked.

### 7. A debt

The commonest duty in these documents is to pay an amount. It takes a duty, a pay act, a guard
on the amount, a variable for the balance and a subtraction; eight notes wrote that, some three
times in one file. Proposed:

```
Debt severance Holder employer Claimant employee Amount 2 * salary
  Raised by dismiss
  Due within 30
```

with payments reducing it and each demand keeping its own deadline. Today two unpaid months of
child support silently become one debt, because the second creation is the same instance.
"Fees, then interest, then principal" is one sentence and six conditional effects; proposed
`Applies usd To fees, interest, principal`.

### 8. Read a value by its name

`Function price Identified by item * usd` cannot be applied. Its value at an item is

```
Sum(Foreach price: price.usd When price.item == item)
```

and the natural spellings are accepted and wrong: `price.usd` with `price` free reads every
price; `Count(Foreach person: present(person))` counts everyone (`reproductions/02`).
Proposed: `price(item)`, `capital(seller)`, `Count(member)`, and a named total
(`Amount pool Is Sum(…)`) read as `pool`.

### 9. Rules the clock applies

Nothing can happen because time passed. A monthly duty needs an event fired by hand, with the
month number threaded through every declaration and scenario line; interest is reconstructed
on demand through a counter; a late fee has to be recorded by the next payment. Proposed:

```
Duty support-due Holder Daniel Claimant Rosa
  Every 30
  Due within 5
```

This touches Law 7 (time is state, not events). It can be met without synthetic events if each
period's instance is derived from the clock, but that is a design question, not a spelling.

With it comes the calendar, which 9.6 defers: "ten years" is `3650` and two or three days
short; "Sunday" cannot be said; alternating weeks is long division by hand. The parenting plan
lists nine places where this distorted the agreement, including one sentence its author did not
write because it could not be said.

### 10. Did it happen

Many facts in these files are markers set by one act and read elsewhere: `signed`,
`revoked`, `delivered`. Proposed: `Done(sign)`. It saves the fact and the effect, and the reader
no longer has to check that nothing else sets it.

### 11. Votes and fractions

Bylaws, the operating agreement and the association rules each built a ballot as a module of
16 to 22 lines, instantiated per decision, tied to the act it decides only by a naming
convention, and cleared by hand. Proposed, as a clause of the act:

```
Power admit-member …
  Decided by member Weighted by capital More than 1/2
```

and `AtLeast 2 witness: witnessed()` for the will and the trust.

### 12. Smaller, each raised by three to six examples

- **A prohibition written as one.** "May not" is `Act … Holds when False`, which cannot say who
  is forbidden. Proposed: `Forbidden when …`, `Void when …`.
- **Protection, the dual of `Immunity`.** "A third party without notice is protected" means an
  act that would be void stands. An immunity means the reverse, so its holder ends up being the
  party who loses. Power of attorney, deed, treasury mandate.
- **Evidence.** A presumption (`Evidenced Bool lacks-capacity Presumed False`); without it
  nobody may decide until someone questions capacity. One finding that can go either way, not
  two that differ by `!`.
- **Amendment.** The procedure stated once for every `Amend`; entrenchment by clause, not by
  rule name; an amendment that restates only what changes.
- **Initial values where the thing is declared**, and **world input declared as input**, so
  `check` can tell a fact the world supplies from one an act should have created.
- **Scenarios.** Start one from another; name a long instance locally; report the failing
  claim's own line.

## The standard library was tried three times and never used

`agency_mandate` (power of attorney), `contract_lifecycle` (home purchase) and `exit_and_voice`
(roommates) were each tried and dropped, for the same reasons:

- A module's rules have no English, so `--require-provenance` fails: ten to thirteen rules per
  module need a sentence the agreement does not contain.
- Amounts are `int`; `Money` is rejected.
- The shapes do not fit: a cumulative cap where the text caps each gift; a dealing as two acts
  with invented identifiers where the text has one; no deadlines; one party able to form the
  contract alone.

The two examples that use a module wrote their own (a ballot).

## Splitting by article

Five examples are split by the divisions of their text. It works, with these findings:

- The document's order is not a dependency order, even in two pages. The trust's revocation
  article needs incapacity, defined an article later.
- `Extend` is what makes the split workable: a later article adds a condition or an effect to
  an earlier rule.
- Shared declarations sink into the first article.
- No article passes `--require-provenance` alone, because only the root declares the document.
  An article checked alone has clauses that were compared with nothing, and says ok.
- A general sentence in an early article cannot name the later rules it governs.
- `#require` is not once-per-file for the file named on the command line, so two articles that
  name each other's rules cannot both be checked alone.

## Defects

One was fixed: a `Document` declared in a required file was looked up beside the requiring
file (`src/Charter/Cli/Load.lean`, fixture `spec_012_1b`).

The rest are open. The first group is the urgent one: a natural spelling is accepted and gives
a wrong answer, and several examples passed their tests on the wrong meaning before a later
scenario exposed it.

**Accepted and wrong** (reproduced; files in `reproductions/`)

| # | What happens |
|---|---|
| 01 | `Fact yes Identified by person * person` is accepted; the second argument is dropped |
| 02 | `Count(Foreach person: present(person))` counts everyone |
| 03 | An atom outside the actor's type performs the act validly |
| 04 | `Held(e) For d` is false inside `Holds when` when `e` is derived |
| 05 | `charter test` exits 0 with a violated `Invariant` |
| 06 | `10000.00` is read as one hundred dollars |
| 07 | A binder over a money, integer or string type is silently empty |
| 08 | An unresolved evidenced premise becomes "yes" through one derived fact |
| 09 | `Amend … Installs { Param … }` is valid and does nothing |
| 11 | An effect that reads an unset `Var` does nothing |
| 12 | `Retracts` in another act removes nothing; two physicians are one piece of evidence |
| 13 | `Holds when` beside `Except under` is ignored |
| 14 | A `Var` over an enumerated type, read by projection, ranges over the whole domain |
| 15 | An `Immunity` with no `Holds when` never holds |
| 16 | A derived fact is stamped when first seen, so a deadline depends on the days visited (matches 009.3) |
| 17 | Re-creating a duty that already holds is silent: two unpaid months are one debt |
| 18 | A `Finding` with no `Resolves` is accepted |

**Checks that say more than they checked**

- An approval covers only the clause text. Every rule of the will was rewritten and all seven
  clauses stayed "approved mapping current". Re-pointing a span at a different rule does the same.
- A rule declared inside `Installs { }` escapes the "every rule has its English" check.
- `charter check` passes a file that `charter test` rejects with CHR102 (a `Yields` that reads
  a parameter).

**Also confirmed, without a file here:** a `Var` cannot take `Default … Yields` although 004.12
allows it; the 010.4 conversions are not made for money and `MulDivRound` rejects a ratio of two
amounts; `#require` loads the command-line file twice under another spelling of its path.

**Reported in the notes, not re-run here:** a free role in an effect ranges over everyone; `run`
prints an effect that did not happen.

Every item is filed: tracking issue thecharter/charter#79.

**Diagnostics**

- An error is reported at the first line of its declaration block, often `1:0`, not at the fault.
- One bad name discards its block and reports every other name in it as undeclared: up to 21
  errors for one mistake.
- A failed claim reports the scenario's first line and a phrase number.
- Naming a declared fact in a span says it is "undeclared".
- `check` prints 67 lines to say yes.
- `charter fmt` deletes comments and blank lines and adds a third copy of every clause.

## What to do first

1. Fix the eleven accepted-and-wrong defects. They are bugs, not design, and they are why a
   passing example cannot yet be trusted without a mutation test.
2. Items 1, 2 and 3. They are changes to the checker and to two defaults; together they remove
   more than a quarter of every file, and item 2 costs almost nothing.
3. Items 4 and 5 (parties and money), which every example with a named person or a price pays.
4. Items 6 to 8 (moments, debts, values), which need design.

Each needs a ruling. Items 1 and 3 reopen D4 and D5 on the conditions those decisions set for
themselves; item 9 needs Law 7 read carefully; any new spelling must replace an old one (Law 13).

## Per example

Each line is the example's most valuable findings; the notes file has the rest.

| Example | Notes | Most valuable improvements |
|---|---|---|
| LastWill | `notes/LastWill.md` | spans that name facts (gifts are facts); cite passages; a named individual as a role; ordered substitutes; "at least two"; shared scenario openings |
| LivingTrust | `notes/LivingTrust.md` | power conditions once; money; roles that change hands; "every beneficiary"; recurring duties; prohibitions; ages and dates |
| Deed | `notes/Deed.md` | declare a role where it is used; no `Holds when True`; world input; local names in cases |
| PowerOfAttorney | `notes/PowerOfAttorney.md` | protection as the dual of immunity; `Done(act)`; name the person in a role; a fixed party in a duty; one declaration for acts that differ only in name; ledger entries |
| HealthcareDirective | `notes/HealthcareDirective.md` | a presumption on an evidenced fact; a finding that goes either way; evidence that belongs to whoever tendered it; an exception without a dummy default; succession |
| Prenup | `notes/Prenup.md` | a span that names the rule it states; a function you can apply; equal division that accounts for every cent; a condition as of a moment; durations in years |
| ParentingPlan | `notes/ParentingPlan.md` | a recurring duty; taking turns; an override written on the overriding rule; how long something lasted as a value; excusing without removing; a due date and a breach date |
| HomePurchase | `notes/HomePurchase.md` | say that an act happened without a marker; a window counted from an event, inclusive; a value that starts somewhere; money; one power with several grounds |
| PromissoryNote | `notes/PromissoryNote.md` | apply a payment to balances in order; a balance that grows with time; a consequence of a missed deadline; a deadline counted from a schedule; rates as written |
| Guaranty | `notes/Guaranty.md` | a debt that payments reduce; moving a claim between creditors; a power's condition once; an unbound role is an error; "was it done in time" |
| BillOfSale | `notes/BillOfSale.md` | an effect that follows from a state; name the parties of an executed instrument once; spans naming `Default` and `Exception`; an immunity that holds unless told otherwise |
| Employment | `notes/Employment.md` | "within N days of X"; cite clauses; a debt in one declaration; a duty that recurs; spans naming exceptions and parameters; name each party once |
| NonDisclosure | `notes/NonDisclosure.md` | a prohibition written as one; rules over strings; a list of exceptions; compare two moments; world input declared once |
| ReturnPolicy | `notes/ReturnPolicy.md` | apply a function; a deadline on a derived duty from when it arose; "within N days of X, now"; an act that only ever fails to take effect |
| Settlement | `notes/Settlement.md` | a running total with a starting value; a span that names the release; "paid within N days of X"; prohibitions; a failed claim's own line |
| RentersInsurance | `notes/RentersInsurance.md` | read a function as a value; undetermined evidence stays undetermined; a finding that answers a question; say which rule of a fact a span means; leave out one-member arguments |
| Roommates | `notes/Roommates.md` | a status as an actor; a variable over names is its value; "each of the others"; a duty owed jointly; initial state where declared |
| HomeownersAssociation | `notes/HomeownersAssociation.md` | a duty to pay an amount; an amendment that is what was voted on; a fraction of a group; ask whether an act occurred and was lawful |
| OperatingAgreement | `notes/OperatingAgreement.md` | a vote as a clause of the act it decides; reading a function at a key; pro rata with the remainder; money as the weight of a ratio; a partial amendment; the amendment procedure once |
| ClubBylaws | `notes/ClubBylaws.md` | a vote at a meeting as a clause; `Count` of a fact; entrench clauses, not rule names; facts that last as long as something else; repealing a prohibition; "the most votes" |

## Per-example counts

From `tools/examples-metrics`. Textual and approximate. "facts" are declarations a clause cannot
name; "rules" are those it can.

| Example | English words | rule lines | clause lines | English retyped (chars) | digests (chars) | case lines | scenarios | facts | rules | spans naming nothing | powers | powers repeating a condition | `Holds when True` | `x == Name` | `Count(Foreach` | `f()` | placeholders | `+fact` in scenarios |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| BillOfSale | 269 | 52 | 19 | 1143 | 600 | 89 | 9 | 14 | 12 | 1 | 1 | 0 | 5 | 0 | 0 | 17 | 2 | 1 |
| ClubBylaws | 393 | 128 | 42 | 1706 | 1425 | 130 | 9 | 17 | 15 | 4 | 5 | 0 | 11 | 0 | 10 | 21 | 2 | 0 |
| Deed | 126 | 37 | 11 | 469 | 375 | 52 | 6 | 10 | 6 | 1 | 1 | 1 | 1 | 0 | 0 | 14 | 2 | 4 |
| Employment | 285 | 77 | 27 | 1465 | 825 | 113 | 10 | 28 | 16 | 2 | 2 | 2 | 2 | 0 | 0 | 36 | 0 | 0 |
| Guaranty | 274 | 52 | 16 | 1246 | 450 | 90 | 8 | 15 | 12 | 1 | 2 | 1 | 2 | 0 | 0 | 15 | 0 | 0 |
| HealthcareDirective | 240 | 65 | 18 | 1104 | 450 | 96 | 10 | 16 | 11 | 1 | 3 | 3 | 2 | 11 | 0 | 36 | 1 | 0 |
| HomePurchase | 411 | 73 | 33 | 1892 | 975 | 119 | 11 | 21 | 16 | 3 | 6 | 0 | 8 | 0 | 0 | 48 | 0 | 0 |
| HomeownersAssociation | 390 | 72 | 35 | 1731 | 1200 | 112 | 8 | 24 | 13 | 2 | 2 | 1 | 3 | 2 | 2 | 23 | 0 | 0 |
| LastWill | 178 | 44 | 16 | 679 | 525 | 66 | 6 | 18 | 5 | 1 | 0 | 0 | 0 | 7 | 1 | 18 | 3 | 0 |
| LivingTrust | 245 | 63 | 23 | 1098 | 825 | 54 | 6 | 18 | 11 | 3 | 5 | 4 | 0 | 10 | 1 | 8 | 0 | 1 |
| NonDisclosure | 223 | 42 | 18 | 1091 | 600 | 77 | 8 | 17 | 7 | 2 | 1 | 1 | 0 | 1 | 0 | 20 | 2 | 0 |
| OperatingAgreement | 496 | 128 | 44 | 2384 | 1500 | 119 | 11 | 17 | 16 | 4 | 10 | 2 | 8 | 0 | 1 | 12 | 3 | 0 |
| ParentingPlan | 253 | 63 | 19 | 1044 | 675 | 109 | 9 | 19 | 11 | 1 | 1 | 0 | 3 | 5 | 0 | 6 | 1 | 0 |
| PowerOfAttorney | 248 | 58 | 19 | 1040 | 525 | 82 | 7 | 17 | 11 | 1 | 5 | 2 | 0 | 12 | 0 | 32 | 2 | 0 |
| Prenup | 183 | 54 | 14 | 799 | 450 | 106 | 8 | 24 | 5 | 0 | 2 | 0 | 1 | 0 | 0 | 17 | 0 | 0 |
| PromissoryNote | 295 | 56 | 20 | 1332 | 600 | 90 | 7 | 22 | 6 | 2 | 1 | 0 | 1 | 0 | 3 | 13 | 0 | 0 |
| RentersInsurance | 353 | 77 | 25 | 1574 | 675 | 109 | 8 | 22 | 11 | 1 | 1 | 1 | 1 | 2 | 0 | 22 | 0 | 0 |
| ReturnPolicy | 158 | 46 | 13 | 633 | 450 | 90 | 8 | 15 | 8 | 0 | 0 | 0 | 3 | 2 | 0 | 23 | 0 | 0 |
| Roommates | 296 | 80 | 20 | 1365 | 525 | 95 | 9 | 19 | 16 | 2 | 1 | 0 | 1 | 0 | 0 | 9 | 2 | 0 |
| Settlement | 226 | 56 | 21 | 1019 | 675 | 87 | 8 | 19 | 11 | 1 | 2 | 2 | 1 | 2 | 0 | 24 | 0 | 0 |
| **Total (20)** | **5542** | **1323** | **453** | **24814** | **14325** | **1885** | **166** | **372** | **219** | **33** | **51** | **20** | **53** | **54** | **18** | **414** | **20** | **6** |
