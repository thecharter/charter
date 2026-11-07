# RentersInsurance

Files: `Examples/RentersInsurance/policy.md`, `policy.charter`, `cases/flat4.charter` (8 scenarios).
`charter check --require-provenance --deny-warnings policy.charter` ends
`ok   Examples/RentersInsurance/policy.charter: 1 phrase(s) resolve (33 declared types, 9 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/flat4.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp`, `?payable("laptop", 70000)` changed to `120000` gave
`[scenario a-theft-is-paid-less-the-deductible, phrase 6]:4: query failed: ?payable("laptop", 120000)` and `FAIL`.

## Size

English sentences: 17. Charter lines outside clause blocks and comments: 79. Clause-block lines: 25.
Case lines: 109. Declarations no sentence of the text refers to: 4 (`party`, a second listing of the
two names already given as `insurer` and `insured`; `usd`, the money type; `answer`, the `Yes`/`No`
the adjuster's finding carries; `month-begins`, an event standing in for the calendar).

Features asked for: all used. Coverage is one `Default` with three `Exception`s for the listed
exclusions (plus two more exceptions the text also supports, late notice and a cause in dispute);
`caused-by` is `Evidenced` and the adjuster's decision is a `Finding`; amounts are `Money(USD, 2)`.
`Default`/`Exception` on the boolean fact was the best-fitting construct in the whole exercise: the
four lines read like R.3 and R.4. The same construct for the *amount* (`Yields`) could not be used
(defect 1) and the plainer `Derived from` is in the file instead.

Known issues, counted for this example:

- Clause span cannot name a fact: 6 spans (R.1 s2 `in-policy`, R.3 the default, R.4 the three
  exceptions, R.5 `payable`, R.6 s2 the `late-notice` exception, R.8 s3 the `cause-in-dispute`
  exception). All six point at `pay-claim` or `claim-due` instead, so `pay-claim` is named by six spans
  and its own text is one `Valid when payable()`. A reader of the clause table learns nothing from it.
- `Holds when True`: 1 (`state-cause`).
- `Power`/`Finding` whose `Valid when` repeats its `Holds when`: 2 (`give-cancellation-notice`,
  `decide-cause`).
- `Created by` unusable because the event lacks the duty's holder and claimant: 2 (`loss-happens`,
  `month-begins`); each got the diagnostic below and was rewritten as a `Creates` on the event.
- Diagnostic on the first line of the block rather than the offending line: 3 (two `1:0`, one on the
  scenario phrase instead of the declaration).
- Money in cents: 3 parameters and 19 case lines carry a cents literal.
- "The settlor" problem: avoided by making each role its own one-member type, at the cost of the
  `party` line (improvement 5).
- No calendar: "for each month, due on the first day of that month" became an event `month-begins()`
  that a case must trigger and `Due within 1`. "Within thirty days after it happens" is violated at
  `@ 30` exactly, so a notice on day 30 is already late; the text arguably allows day 30.

## What was hard

In order.

1. `Creates loss()` for the string-domain fact `loss` (I had just written `Creates notice-due()` and
   `Creates noticed()`, so the empty-parentheses form looked general):
   `t.charter:1:0: error CHR018: loss is a primitive type and takes exactly one positional argument`.
   The line is 1, the offending line was 8. Fix: `Creates loss`.
2. `Created by loss-happens` on `Duty notice-due Holder insured Claimant insurer Related to loss`, with
   `Event loss-happens Related to loss`:
   `t.charter:1:0: error CHR027: \`Created by loss-happens\` on notice-due: the component insured of notice-due is not a component of loss-happens, so loss-happens cannot bind it`.
   Fix: `Event loss-happens Related to loss Creates loss, notice-due()`. This works only because
   `insurer` and `insured` are one-member types, so the two unbound components have one value each.
   With `Placeholder insured For party` the same line created four duties (every pair of parties).
3. The amount payable, first attempt with `Default … Yields`:
   ```
   Function payable Identified by loss * usd
     Default value-less-deductible Yields value.usd - deductible When covered(loss) && value.loss == loss
     Exception capped Overrides value-less-deductible Yields limit When covered(loss) && value.loss == loss && value.usd - deductible > limit
   ```
   `p2.charter [scenario a, phrase 2]:48:0: error CHR102: variable value is not bound`.
   Second attempt, `Yields Sum(Foreach value: value.usd When value.loss == loss) - deductible When covered(loss)`:
   `t.charter:16:0: error CHR102: variable deductible is not bound`. A `Param` cannot be read in a
   `Yields` value at all (defect 1). Third attempt, `Yields usd When covered(loss) && value(loss, usd + deductible)`:
   no diagnostic, derives nothing. Fourth, `Derived from` with two hand-written disjoint cases: works.
4. "A claim is due when something is payable." First `Holds when payable(loss = loss)`, then
   `Holds when payable()`, then `(Exists usd: payable(loss, usd))`: all three resolve, none warns,
   none ever derives the duty (`query failed: ?claim-due("HarborMutual", "Nora", "laptop")`). `usd`
   ranges over the `usd` instances that hold, and none do. Only
   `(Exists payable: payable.loss == loss)` works.
5. A disputed exclusion. With `Exception flood … Rejects when caused-by(loss, Flood)` and Flood
   `Conflicted`, the loss was `covered`, a claim was due, and the deadline was running:
   `[scenario a-disputed-cause-waits-for-the-adjuster, phrase 10]:55: query failed: ?!claim-due("HarborMutual", "Nora", "sofa")`.
   A conflicted premise inside a derived fact is read as false (defect 3). Fix: a sixth rule,
   `Exception cause-in-dispute … Rejects when (Exists cause: Conflicted(caused-by(loss, cause)))`.
6. The adjuster "decides whether it was a cause". `Resolves [!]e` fixes the polarity in the
   declaration, so I first wrote two findings, `find-cause` and `find-not-cause`, four lines each and
   identical but for one `!`. Then tried `Resolves caused-by() When answer == Yes` and
   `Resolves !caused-by() When answer == No` in one `Finding`. It parses and works (verified for both
   answers and both clause orders). Chapter 005.11 does not say a `Resolves` may be conditional or
   repeated; I found it by reading the grammar (`'Resolves' '!'? expr`, and `expr` admits `When`).

Things that worked the first time and are worth keeping: `Supports caused-by()` / `Rebuts caused-by()`
with implicit arguments; a *derived* duty with `Due within` (R.7 and R.8 s3 together are
`Holds when (Exists payable: …)` plus `Due within 30`; the stamp restarts when the duty is derived
again after the finding, which is exactly "the thirty days run from the adjuster's finding");
`Terminated by` on that derived duty; `Held(cancellation-noticed()) For 10` for "ends ten days after
that notice".

## Improvements (at least five, most valuable first)

### 1. Read a `Function` as a value: `value(loss)`

As written today (7 lines, plus 1 in the duty):

```
Function payable Identified by loss * usd
  Derived from payable(value.loss, value.usd - deductible)
                 When covered(value.loss) && value.usd > deductible
                   && value.usd - deductible <= limit
             , payable(value.loss, limit)
                 When covered(value.loss) && value.usd - deductible > limit
…
  Holds when (Exists payable: payable.loss == loss)
```

Proposed, does not parse today:

```
Function payable Identified by loss * usd
  Default less-deductible Yields value(loss) - deductible When covered(loss) && value(loss) > deductible
  Exception limit-per-loss Overrides less-deductible Yields limit When value(loss) - deductible > limit
…
  Holds when payable(loss)
```

A `Function` applied to its key alone is its value in an expression and "it has a value" in a
condition. Saves 4 of 8 lines and about 170 characters. Concepts the author no longer needs: that the
head of a `Derived from` restates the type; that a binder ranges over the function's own instances
and is then filtered by key; that the two cases must be made disjoint by hand (the `<= limit` in the
first case exists only so the two rules never both fire); that a free `usd` ranges over nothing.
Occurs 3 times (two rules of `payable`, the duty's `Holds when`). It would also make R.5 quotable
rule by rule: "less a deductible" is the default, "never pays more than" is the exception.

### 2. Evidence that is undetermined stays undetermined through a derived fact

As written today:

```
  Exception cause-in-dispute Overrides theft-or-fire
    Rejects when (Exists cause: Conflicted(caused-by(loss, cause)))
```

Proposed, does not parse today as meaning this (the lines parse; the behaviour differs): delete the
two lines. `covered("sofa")` is neither derived nor rejected while a rule it depends on reads a
`Conflicted` fact, `?undetermined covered("sofa")` holds, and so does
`?undetermined pay-claim(HarborMutual, Nora, "sofa", 100000)`. Saves 2 lines, and removes a trap: an
author who lists the exclusions as R.4 lists them gets a policy in which disputing an exclusion
switches it off. Occurs once here; it will occur in every program that puts an `Evidenced` fact
under a `Default`/`Exception`.

### 3. A finding that answers a question

As written today (6 lines):

```
Fact answer Identified by Yes, No
Finding decide-cause Actor adjuster Related to loss, cause, answer
  Resolves caused-by() When answer == Yes
  Resolves !caused-by() When answer == No
  Holds when Conflicted(caused-by())
  Valid when Conflicted(caused-by())
```

Proposed, does not parse today:

```
Finding decide-cause Actor adjuster Decides caused-by()
  When Conflicted(caused-by())
```

performed as `decide-cause(Ines, "sofa", Flood, Yes)` or `… No)`. `Decides e` takes the fact's
components and a built-in yes/no; a single `When` on a `Finding` or `Power` is both its `Holds when`
and its `Valid when`. Saves 4 of 6 lines. Concepts removed: the polarity `!`, the hand-made `answer`
type, the lawful/valid pair for an act where the two never differ. Occurs once (the pair
`Holds when X` / `Valid when X` occurs twice, see the known-issue count).

### 4. Say which rule of a fact a span means

As written today:

```
Clause R.4 Approved "8d57…"
  Norm "The insurer does not cover a loss, even one by theft or fire, if flood contributed to it, if the insured caused it on purpose, or if it is ordinary wear." => pay-claim
```

Proposed, does not parse today:

```
Clause R.4
  Norm "The insurer does not cover a loss, even one by theft or fire, if flood contributed to it" => covered.flood
  Norm ", if the insured caused it on purpose" => covered.on-purpose
  Norm ", or if it is ordinary wear." => covered.ordinary-wear
```

`Default` and `Exception` rules already have names; let a span use them. This is the known
"cannot name a fact" issue, but the named-rule form is new and is where it hurts most: 6 of this
file's 15 `Norm` spans mean a named rule of `covered` or `payable` and all say `pay-claim`.
Saves nothing in lines; makes `check`'s "every rule has its English" true of the six rules that
carry the whole of R.3 to R.5.

### 5. A type made of other types

As written today:

```
Fact insurer Identified by HarborMutual
Fact insured Identified by Nora
Fact party Identified by HarborMutual, Nora
```

Proposed, does not parse today:

```
Fact insurer Identified by HarborMutual
Fact insured Identified by Nora
Fact party Identified by insurer, insured
```

One-member role types removed every `insured == Nora` from the file (zero occur; the shared-`person`
style of the pilots would need eight: six acts and two events) and let events create duties with
`Creates notice-due()`. The cost is that "either party" needs the names listed a second time. Saves
no lines; removes the same fact encoded in two places and the silent failure when someone extends
one list and not the other. Occurs once.

### 6. Leave out arguments that can only have one value

As written today (48 times in the case file):

```
  ?violated claim-due(HarborMutual, Nora, "laptop").
  give-notice(Nora, HarborMutual, "laptop").
```

Proposed, does not parse today:

```
  ?violated claim-due("laptop").
  give-notice("laptop").
```

When a component's type has exactly one member, a phrase may omit it. Saves about 20 characters on
each of 48 case lines (of 109). The rule file already enjoys this (`notice-due()`); the cases do not.

### 7. Money written as money

As written today: `Param limit : Money(USD, 2) = 2000000`, `prove-loss(Nora, HarborMutual, "sofa", Fire, 150000).`
Proposed, does not parse today: `Param limit = $20,000.00`, `prove-loss(Nora, HarborMutual, "sofa", Fire, $1,500.00).`
Saves the `: Money(USD, 2)` annotation three times and the mental multiplication 22 times (3
parameters, 19 case lines). I checked `2000000` against "twenty thousand dollars" by counting zeros.

## Tool defects

### 1. A `Yields` value cannot read a `Param` or any other fact (CHR102), and `check` passes it

```
Fact k Identified by A
Param d = 5
Function f Identified by k * int
  Default r Yields d When True
.
?f(A, 5).
```

Expected: `f(A, 5)` (014.1: "any position of that type may name it as a variable"). Actual:
`charter test`: `d1.charter:1:0: error CHR102: variable d is not bound` and then
`error CHR010: undeclared type or placeholder \`f\``; `charter check` on the same file prints
`ok … coverage complete, 0 warning(s)` and exits 0. CHR102 is documented as "internal; a resolution
gap". The same happens with a free fact variable (`Yields v.int When v.k == k`). `Yields d` works
when `d` appears only in the `When`. Inside a scenario the error is reported at the scenario's
phrase, not at the declaration. Workaround: `Derived from` with the cases made disjoint by hand
(`Yields Sum(Foreach v: v.int When v.k == k) - Sum(Foreach d: d) When True` also works, and is worse).

### 2. An atom outside an enumerated domain is accepted as the actor, and the act has its effects

```
Fact insured Identified by Nora
Bool noticed
Act give-notice Actor insured Holds when True Creates noticed()
.
give-notice(Mallory).
?noticed().
+insured(Zed).
?insured(Zed).
```

Expected: a diagnostic that `Mallory` is not an `insured` (and the same for `Zed`). Actual:
`charter run` prints `occurred act give-notice(insured("Mallory"))   lawful: no   valid: yes`,
`+noticed()`, `query holds`. The assignment `+insured(Zed)` is silently dropped (`query failed`),
with no diagnostic either. `charter check` reports 0 errors. So a typo in a party's name in a case
is an act by a stranger that is unlawful but fully effective. Workaround: none used; the cases use
only declared names.

### 3. A `Conflicted` or `Unresolved` premise is not propagated through a derived fact

```
Fact item Identified by A
Evidenced Fact excluded Identified by item
Fact covered Identified by item
  Default d Holds when True
  Exception x Overrides d Rejects when excluded(item)
Act pay Related to item Holds when covered(item)
Act pay-direct Related to item Holds when Not(excluded(item))
.
SubmitEvidence excluded(A) By "insurer".
?!covered(A).
SubmitEvidence !excluded(A) By "insured".
?Conflicted(excluded(A)).
?covered(A).
?lawful pay("x", A).
?!undetermined pay("x", A).
?undetermined pay-direct("x", A).
```

All six claims pass. Expected: `pay` is `undetermined`, as `pay-direct` is (004.11: an `Evidenced`
premise propagates "without inventing truth"). Actual: once the exclusion is contested the exception
stops firing, `covered(A)` is derived, and `pay` is lawful. The same two acts differ only in whether
the evidenced fact is read directly or through a derived fact. Workaround: an explicit exception that
rejects while any cause is `Conflicted`.

### 4. An approval survives re-pointing its span at a different rule

I stamped R.8 with its second span meaning `find-cause, find-not-cause`, then replaced those two
findings by `decide-cause` and changed the span to `=> decide-cause`. `check` still reports
`ok   R.8: approved mapping current`. 012.8 says the hash is of the clause's text, so this is as
specified, but the report line says "mapping", and the approval is described as a record that "its
spans and meanings were reviewed". Expected: STALE when the rules a span names change. Workaround:
none needed; noted because the stamp tool makes it invisible.

### 5. Silent non-derivation with a free component of a non-enumerable type

`Holds when payable()` in a duty over `loss`, where `payable` is `loss * usd`: resolves, no warning,
never true (see "What was hard" 4). 004.7 specifies it, so it is not wrong, but CHR025 and CHR028
warn about the two neighbouring cases and this one is silent. Expected: a warning that `usd` is
unbound and ranges over a type with no instances.

## What a lay author would have guessed

- `Creates loss()` to say "there is now a loss". Rejected (CHR018).
- `Created by loss-happens` on the duty to give notice. Rejected (CHR027): the event would have to be
  written `loss-happens(Nora, HarborMutual, "laptop")`, naming two people who did nothing.
- `Yields value.usd - deductible` for "the value less a deductible". Rejected (CHR102).
- `Holds when payable()` for "something is payable". Accepted, never true.
- Listing the exclusions as exceptions and expecting a disputed exclusion to hold up payment.
  Accepted, means the opposite: the disputed exclusion is ignored.
- Two findings, one for "it was the cause" and one for "it was not". Accepted; six lines of the eight
  were duplicates.
- `Placeholder insured For party`, then `Actor insured`, expecting only Nora to be able to give
  notice. Accepted; means any party.
- That the insurer "stating" a cause would need a decision before it counted. In fact one-sided
  `Supports` makes the fact `Established` at once: when Harbor Mutual says "she set the fire", the
  loss stops being covered until Nora disputes it. The text (R.8) is compatible with that, but I did
  not choose it; the evidence model did.
