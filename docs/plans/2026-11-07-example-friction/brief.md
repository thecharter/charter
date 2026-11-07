# Brief: worked examples for Charter, and where the language gets in the way

Repo: /Users/eric/charter. Charter is a language for executable agreements, built on eFLINT.
You will write worked examples under `Examples/`. The task has two purposes. The first is
documentation. The second, which matters more, is to find where Charter makes an ordinary
agreement harder to write or read than it should be. The owner's standard is that these
agreements should be *dreadfully easy* to write. Your notes on what was not easy are the main
deliverable; passing examples are the evidence behind them.

## Read first

- `Examples/README.md` (layout and steps), then the three pilot examples, which set the style:
  `Examples/LastWill/`, `Examples/Deed/`, `Examples/LivingTrust/` (split by article).
- `docs/spec/cheatsheet.charter` (every construct in one passing file) and
  `Examples/Tenancy/tenancy.charter`.
- `docs/spec/` chapters as you need them: 003 types, 004 facts and derivation (4.11 evidenced
  facts, 4.12 `Default`/`Exception`), 005 acts, `Valid when`, `Power`, `Finding`, 006 duties and
  deadlines, 007 immunities and exceptions, 009 time, 010 expressions (money, `MulDivRound`),
  011 phrases and scenarios, 012 clauses, 014 parameters, 015 modules. `lib/README.md` lists
  the standard-library modules; try one where it fits naturally.
- `AGENTS.md`, section "Ceremony is a design defect, not an author error". It is the lens for
  your notes.

## Rules

- The binary is already built: `/Users/eric/charter/.lake/build/bin/charter`. Do not run
  `lake build`, `tools/battery`, `charter prove`, or `charter fmt` on a file in place.
- Create files only in your own example directories and your notes files. Do not edit `src/`,
  `tools/`, `docs/`, `lib/`, or any other example. Do not commit.
- Write the English yourself: original, plain, fictional parties, one to two pages, numbered
  clauses under headings, with the same disclaimer line the pilots use. Do not copy real forms.
  Never edit the English to make a rule pass; the rule is what is under review.
- The words "sorry", "axiom" and "native_decide" must not appear anywhere under `Examples/`
  (a repository gate greps for them).
- There is no calendar and no template text with blanks. Write an executed instance with named
  parties and count time in days. Note each place where that distorted the agreement.
- If the tool is wrong (accepts something it should reject, rejects something the spec allows,
  reports the wrong line, stays silent), do not quietly work around it. Record a minimal
  reproduction in your notes, then use the smallest workaround that lets you finish.
- Verify by running, not by reasoning. When unsure what a construct does, write a five-line
  file under `/tmp` and run it.

## Already known (do not rediscover; do count how often each one bit you)

- A clause span can name only acts, duties, immunities and invariants. It cannot name a fact,
  a derived fact, or an event, even though much legal content is exactly that.
- Every clause needs an `Approved "<64 hex>"`. Run `tools/approve-clauses FILE.charter` to stamp
  them (`--restamp` after you change the English). Clauses live in the file that declares them.
- An act with no `Holds when` is never enabled. Write `Holds when True` for "anyone may".
- A `Power` must have a `Valid when`. In practice it often repeats the `Holds when`.
- Money: `Fact usd Identified by Money(USD, 2)`, amounts in cents. A `Var fund Identified by usd`
  is read as `fund.usd`. Rounding is `MulDivRound(x, num, den, Floor)`.
- `Created by a` and `Terminated by a` on a duty work only when act `a` carries the duty's
  components under the same names. Role placeholders make that work (see `Deed/deed.charter`).
- `Document "x.md"` needs a `.` before a following `#require`.
- Diagnostics point at the first line of the declaration block, not the offending line.
  A failed scenario claim reports the scenario's first line and a phrase number.
- Time: integer days. `@ n.` sets the clock. `Due within n`, `Held(f) For n`, `Creates f For n`.
- There is no way to say "the settlor" for one named individual in a shared `person` type other
  than `person == Margaret`. There is no "at least two of" other than `Count(Foreach …) >= 2`.

## Done means, for each example

1. `<name>.md`, `<name>.charter` (plus article files when you split), and `cases/*.charter`
   with at least five scenarios. Each scenario shows a sentence of the text making a
   difference. Where the text has such sentences, include one act that occurs but is not lawful
   and one that occurs but has no effect.
2. `charter check --require-provenance --deny-warnings <root>` ends with `coverage complete`,
   and `charter test --deny-warnings <case>` passes for every case file.
3. You changed one claim to a wrong value in a copy under `/tmp` and saw the test fail.
4. Use the feature listed for the example when it fits the text. If it made the program worse
   than plain facts and acts would, use the plainer form and say so in the notes.
5. A notes file `/tmp/charter-friction/<Name>.md` in the format below.

## Notes format (one file per example)

```
# <Name>
## Size
English sentences: N. Charter lines outside clause blocks and comments: N. Clause-block lines: N.
Case lines: N. Declarations no sentence of the text refers to: N (list them).
## What was hard
In order: each thing that took more than one attempt, with the exact diagnostic you got.
## Improvements (at least five, most valuable first)
For each: a title; the lines as you wrote them today, quoted from your file; the same thing as
you wish you could write it, labelled "proposed, does not parse today"; what it saves (lines,
characters, concepts the author no longer needs to know); how many times the pattern occurs in
your file.
## Tool defects
Minimal reproduction, expected, actual, workaround.
## What a lay author would have guessed
The first thing you wrote because it seemed natural, when it was rejected or meant something else.
```

Write down the first thing you tried even when it was wrong. That is the most useful line.
Proposals must be concrete spellings, not wishes. Do not present a proposed spelling as working.

## Report back

A short message: the files you created; the final line of each `check` and `test`; your five
most valuable improvements across all your examples, one line each; any tool defects.
