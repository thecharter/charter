# HealthcareDirective

Files: `Examples/HealthcareDirective/directive.md`, `directive.charter`, `cases/ward.charter` (10 scenarios).
`charter check --require-provenance --deny-warnings directive.charter` ends
`ok   Examples/HealthcareDirective/directive.charter: 1 phrase(s) resolve (27 declared types, 6 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/ward.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp/cf-hcd/mut`, `?!valid decide(Grace, LifeSupport, Consent)` flipped to `?valid` gave
`cases/ward.charter [scenario the-instruction-overrides-the-agent, phrase 4]:62: claim failed: ?valid decide("Grace", "LifeSupport", "Consent")`.

## Size

English sentences: 13. Charter lines outside clause blocks and comments: 66. Clause-block lines: 19.
Case lines: 96. Declarations no sentence of the text refers to: 2 (`choice`, the type
`Consent, Refuse` that exists so "consent to or refuse" can be one act; `agent-chooses`, a default
that says `Holds when True` only so the exception has something to override).

Known issues, counted in this example:

- A span cannot name a fact or event: 4 of 12 spans. H.1 "I appoint Grace" (a `Definition` with
  nothing to point at); H.1 "Samuel is my agent in her place" (the derived `serving` and the event
  `becomes-unable`); H.3 "I am presumed to have capacity" (the evidenced fact); H.5 "This
  instruction overrides my agent's choice" (the rule `my-instruction`). Each names `decide` instead,
  so `decide` is named by six spans.
- `Valid when` repeating `Holds when` verbatim: 6 of 6 (`revoke`, `dismiss`, three findings, `decide`).
  For `decide` the repeated condition is two lines long.
- `person == Walter` and the like: 9 comparisons.
- `Holds when True`: 1 act (`decline`), 1 default (`agent-chooses`).
- A failed claim reported the scenario's first line: every time (7 failures over two runs).
- Money, `Created by`, `Document` before `#require`, "at least two of": 0.

No calendar: nothing was distorted. The text has no dates. "At any time" needed nothing.

## What was hard

1. **`Valid when a, b` is "a and b"; `Holds when a, b` is "a or b".** First written, as an
   experiment in `/tmp/cf-hcd/e1.charter`:

   ```
   Power consent Actor person
     Holds when person == Grace && lacks-capacity(), person == Walter && Not(lacks-capacity())
     Valid when person == Grace && lacks-capacity(), person == Walter && Not(lacks-capacity())
   ```

   No diagnostic. `claim failed: ?valid consent("Grace")` while `?lawful consent(Grace)` held. The
   spec says so (004.1 "alternatives", 005.9 "iff every eᵢ holds") but the two lines look identical
   and mean opposite things. I wrote `||` in both from then on.

2. **A stray component cost 21 errors.** `Finding decide Actor committee Related to bool` gave
   `e1.charter:1:0: error CHR010: undeclared type or placeholder `bool`` at line 1 column 0 (the
   finding was on line 15), then twenty more `CHR010: undeclared type or placeholder` for every name
   in the same block (`attending`, `consent`, `lacks-capacity`, …), all reported at the scenario's
   first line.

3. **The presumption of capacity.** Written first:

   ```
   Power decide Actor person Related to treatment, choice
     Holds when (person == Walter && Not(lacks-capacity()))
             || (serving(person) && lacks-capacity() && open-to-agent())
   ```

   With no evidence either way the fact is `Unresolved`, so both disjuncts are `undetermined` and
   nobody may decide, including Walter:
   `[scenario capacity-is-presumed, phrase 2]:8: claim failed: ?valid decide("Walter", "Surgery", "Consent")`
   and `phrase 4]:8: claim failed: ?!undetermined decide("Grace", "Surgery", "Consent")`.
   An `Evidenced` fact has no way to say which way it is presumed. The spelling that works adds a
   status test to each side: `Unresolved(lacks-capacity()) || Not(lacks-capacity())` for Walter and
   `Not(Unresolved(lacks-capacity())) && lacks-capacity()` for the agent. With `Holds when` and
   `Valid when` that is `lacks-capacity()` eight times in one power.

4. **Factoring the capacity test into a fact changes the answer.** I tried
   `Fact decides Identified by person Holds when person == Grace && lacks-capacity(), person == Walter && Not(lacks-capacity())`
   and `Holds when decides()`. No diagnostic. With the fact unresolved, `?undetermined consent(Walter)`
   failed and `?valid consent(Walter)` held. See Tool defects 1. The condition therefore has to stay
   inline in the act, which is why "consent" and "refuse" became one act `decide` with a `choice`
   argument: two acts would have meant four copies of the two-line condition.

5. **Withdrawing a determination.** Written first:

   ```
   Act withdraw-determination Actor physician
     Holds when attending()
     Retracts lacks-capacity()
   ```

   No diagnostic; the act is reported `lawful: yes   valid: yes` and changes nothing:
   `[scenario the-determination-is-withdrawn, phrase 4]:54: claim failed: ?valid decide("Walter", "Surgery", "Consent")`.
   See Tool defects 2. Workaround: the withdrawal is a `Finding … Resolves !lacks-capacity()` by the
   attending physician. That makes the status `Refuted`, not `Unresolved`, which happens to match
   "I have capacity again"; a new determination after it would be `Conflicted`, which is wrong, and
   the text does not go there.

6. **A finding goes one way.** "The committee decides the question" is two declarations,
   `find-incapacity` and `find-capacity`, eight lines that differ by one `!`.

7. **An exception needs a named default.** Tried the exception directly on the act:
   `f1.charter:8:3: error CHR004: expected `.` to end the phrase but found atom `Exception``.
   Tried it on a fact with no default:
   `f2.charter:4:28: error CHR003: expected `Overrides <rule-id>` after `Exception my-instruction``.
   Tried overriding the fact's own `Holds when True`:
   `f3.charter:1:0: error CHR010: open-to-agent: undeclared defeasible rule `open-to-agent` in `Overrides` / `Over``.
   What parses is a `Default agent-chooses Holds when True` written only to be overridden.

8. A scenario cannot be named `t2`: `e2.charter:44:11: error CHR003: expected `{` but found integer 2`.

**Did the listed features help?** `Evidenced` with `Finding`: yes for the dispute. "Determines",
"disagrees", "the committee decides" map one to one onto `Supports`, `Rebuts`, `Finding`, and
`?undetermined` says exactly what "neither my decisions nor my agent's are acted on" says. It cost
items 3 to 6. `Default`/`Exception` for the instruction: it reads like the text ("overrides"), so I
kept it, but it is four lines and a derived fact where the plain form is one conjunct,
`&& Not(treatment == LifeSupport && choice == Consent && terminal())`, and the rule name
`my-instruction` cannot be named by the H.5 span, which is the only reason to name it.

## Improvements (most valuable first)

### 1. A presumption on an evidenced fact

Today:

```
Evidenced Bool lacks-capacity
Power decide Actor person Related to treatment, choice
  Holds when (person == Walter && (Unresolved(lacks-capacity()) || Not(lacks-capacity())))
          || (serving(person) && Not(Unresolved(lacks-capacity())) && lacks-capacity() && open-to-agent())
  Valid when (person == Walter && (Unresolved(lacks-capacity()) || Not(lacks-capacity())))
          || (serving(person) && Not(Unresolved(lacks-capacity())) && lacks-capacity() && open-to-agent())
```

Proposed, does not parse today:

```
Evidenced Bool lacks-capacity Presumed False
Power decide Actor person Related to treatment, choice
  Only when (person == Walter && Not(lacks-capacity()))
         || (serving(person) && lacks-capacity() && open-to-agent())
```

`Presumed False` makes `Unresolved` read as "no" in a guard; `Conflicted` still reads as
`undetermined`. Saves four status tests here and lets the H.3 sentence "I am presumed to have
capacity" be one word in the program. Every legal fact of this kind has a presumption (capacity,
innocence, legitimacy, delivery); without it the first scenario anyone writes fails. Occurs 4 times
(2 tests × 2 conditions).

### 2. A finding that can go either way

Today:

```
Finding find-incapacity Actor committee
  Resolves lacks-capacity()
  Holds when Conflicted(lacks-capacity())
  Valid when Conflicted(lacks-capacity())
Finding find-capacity Actor committee
  Resolves !lacks-capacity()
  Holds when Conflicted(lacks-capacity())
  Valid when Conflicted(lacks-capacity())
```

Proposed, does not parse today:

```
Finding decide-capacity Actor committee
  Decides lacks-capacity()
  Only when Conflicted(lacks-capacity())
```

performed as `decide-capacity(EthicsCommittee, Yes)` or `decide-capacity(EthicsCommittee, No)`.
Saves 5 of 8 lines and one name per question; the span lists one rule. Occurs once (two findings);
a third finding, the workaround for withdrawal, is the same shape again.

### 3. Evidence belongs to whoever tendered it

Today the withdrawal is a second kind of finding because `Retracts` cannot reach the evidence:

```
Finding withdraw-determination Actor physician
  Resolves !lacks-capacity()
  Holds when attending()
  Valid when attending()
```

Proposed, does not parse today (it parses, and silently does nothing; see Tool defects 2):

```
Act withdraw-determination Actor physician
  Holds when attending()
  Retracts determine-incapacity
```

`Retracts a` removes the evidence this actor tendered by act `a`. Saves a line and a false
`Finding`; the status returns to what it was before the determination. Needs evidence keyed by
(act, actor), which would also make "two physicians concur" two pieces of evidence, not one.
Occurs once.

### 4. One condition for "may, and otherwise void"

Today, six times:

```
Power dismiss Actor person Related to agent
  Holds when person == Walter
  Valid when person == Walter
  Creates out()
```

Proposed, does not parse today:

```
Power dismiss Actor person Related to agent
  Only when person == Walter
  Creates out()
```

Saves 7 lines in this file (one per power or finding, two for `decide`) and removes item 1 of
"What was hard", because one keyword has one meaning for the comma. Occurs 6 of 6.

### 5. An exception without a dummy default, on the thing it limits

Today:

```
Fact open-to-agent Identified by treatment * choice
  Default agent-chooses Holds when True
  Exception my-instruction Overrides agent-chooses
    Rejects when treatment == LifeSupport && choice == Consent && terminal()
Power decide … Holds when … && open-to-agent()
```

Proposed, does not parse today:

```
Power decide Actor person Related to treatment, choice
  Only when …
  Exception my-instruction
    Void when serving(person) && treatment == LifeSupport && choice == Consent && terminal()
```

and the span `Norm " This instruction overrides my agent's choice: …" => my-instruction`. Saves the
fact, the default, and one conjunct in each condition (4 lines), and gives H.5 its own name to point
at. Occurs once.

### 6. Named people in a role, with an order of succession

Today:

```
Fact serving Identified by agent
  Holds when in-effect() && agent == Grace && Not(out(Grace))
           , in-effect() && agent == Samuel && out(Grace) && Not(out(Samuel))
```

Proposed, does not parse today:

```
Role agent Is Grace Then Samuel Unless out()
```

The first named person for whom `out` does not hold has the role. Saves 2 lines and the hand-built
"and not the one before" chain, which grows quadratically with a third alternate. The same shape is
`LastWill` W.3 (executor, substitute) and `LivingTrust` 3.2 (successor trustee). Occurs once.

### 7. A derived fact over evidence keeps the third value, or is refused

Today the capacity test cannot be given a name (see Tool defects 1), so it is written out in full
in every guard. Proposed: either `Bool capable Holds when Not(lacks-capacity())` is itself
three-valued, or `check` rejects it with "a derived fact over an `Evidenced` premise loses
`undetermined`; test `Established(…)` or `Refuted(…)`". Saves the choice between a wrong answer and
a two-line condition repeated in each act. Occurs once (it forced `consent` and `refuse` into one
act).

## Tool defects

1. **A derived fact turns "unresolved" into "yes".**

   ```
   Fact person Identified by Walter
   Evidenced Bool lacks-capacity
   Bool capable
     Holds when Not(lacks-capacity())
   Fact ok Identified by person
   Power direct Actor person
     Holds when Not(lacks-capacity())
     Valid when Not(lacks-capacity())
     Creates ok()
   Power factored Actor person
     Holds when capable()
     Valid when capable()
     Creates ok()
   .
   ?undetermined direct(Walter).
   ?undetermined factored(Walter).
   ?valid factored(Walter).
   ```

   Expected: the two powers agree (`undetermined`), or a diagnostic on `capable`. Actual:
   `?undetermined direct(Walter)` holds; `?undetermined factored(Walter)` fails; `?valid
   factored(Walter)` holds. `check --deny-warnings`: 0 warnings. Spec 004.11 says a bare evidenced
   premise "propagates … without inventing truth"; behind one derived fact it invents it.
   (`/tmp/cf-hcd/g1.charter`.) Workaround: keep the evidenced premise inline in the act.

2. **`Retracts` in an act retracts nothing another act tendered.**

   ```
   Fact physician Identified by DrAdler, DrBose
   Evidenced Bool lacks-capacity
   Act determine Actor physician
     Holds when True
     Supports lacks-capacity()
   Act withdraw Actor physician
     Holds when True
     Retracts lacks-capacity()
   .
   determine(DrAdler).
   ?Established(lacks-capacity()).
   withdraw(DrAdler).
   ?Unresolved(lacks-capacity()).
   ```

   Expected: the last query holds. Actual: it fails; `run` shows
   `+$ev_support(lacks-capacity(),string("determine"))` then
   `-$ev_support(lacks-capacity(),string("withdraw"))`. The evidence source is the act's name
   (`src/Charter/Eval/Eval.lean`, `evalEffect`, `.evOp .retract`), so a retraction only matches
   evidence from an act of the same name, and no warning says the effect is dead. For the same
   reason two physicians performing `determine` leave one piece of evidence, not two.
   (`/tmp/cf-hcd/f5.charter`.) Workaround: a negative `Finding`.

3. **One bad name in a declaration block reports every name in the block as undeclared**, at line
   `1:0` and then at each use (21 errors for one stray `Related to bool`).

4. `Scenario t2 {` is a parse error (`expected `{` but found integer 2`); a scenario name cannot end
   in a digit. Minor.

## What a lay author would have guessed

- `Valid when a, b` meaning "a or b", because `Holds when a, b` on the line above does.
- `Not(lacks-capacity())` meaning "has capacity" when nobody has questioned it. It means "cannot say".
- A fact `decides(person)` to name "who decides". Accepted; answers differently from the inline form.
- `Retracts lacks-capacity()` in a `withdraw` act. Accepted; does nothing.
- `Exception my-instruction Rejects when …` written on the act it limits. Parse error.
- One `Finding` for "the committee decides the question". It takes two.
