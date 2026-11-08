# Briefs for rulings, 2026-11-07

Four of the eleven accepted-and-wrong defects found by the worked examples
(`docs/plans/2026-11-07-example-friction/`) change behaviour the spec states or leaves open.
All four are about semantics, so none is delegated. Five others were fixed under D29; two
(#3, #8) are warnings to add and need no ruling.

Each brief gives the finding, what was measured, what the references do, what the spec and
mission say, the options that pass the laws, and a committed prediction.

## B13. `charter test` passes a program whose invariant is violated (#6)

**Ruled 2026-11-07: (B) — always check end states (`D30`).** All 6 library tests with mid-genesis violations were inspected individually and confirmed to cure before genesis ends; 7 upstream eFLINT corpus files recorded as `D30` tolerances.

**Finding.** `Invariant never-bad When Not(bad()).` then `+bad().`: `charter test` prints
`1 passed` and exits 0. `charter run` prints `violation: invariant never-bad does not hold`,
and prints it under the *next* phrase, not under `+bad()`. With `//! explore: 1` in the file the
same program fails: `invariant never-bad violated after 0 step(s): (already in the end state)`.
So an end state is checked only when the file asks for exploration.

**Measured.**
- Invariants are violated during top-level setup in 6 of the 12 library tests, in
  `Examples/AutonomousCommons` (379 violation lines), and in 3 spec fixtures. These are states
  under construction: a module is instantiated, its `Var`s have no value yet, and an invariant
  over them is false until the genesis assigns them.
- Of every scenario in the repository, two violate an invariant inside the scenario
  (`commons :: group-carryover-forfeiture-and-subsidy`, `entity_group_test :: inflation-is-a-breach`),
  and the second does so on purpose.
- In the eFLINT corpus, 11 files violate an invariant at top level and 7 end with one violated
  (`tests/output/invariants/{contr-taut,taut-contr,two-invs}`, `tests/output/duties/duty-inv`,
  `tests/parallel-comp/violations`, `symboleo-meat-sales/v{1,2}/contract`). All pass upstream.
- `tools/examples-check` does not pass `--require-complete-explore`; the battery's older
  `examples` step does.

**What the references do.** eFLINT records an invariant violation as a `Violation` output
(`.reference/eflint/src/Language/EFLINT/Interpreter.hs:143`) and its test mode prints only
errors and query results (`.reference/eflint/src/REPL.hs:227`), so a violated invariant passes.
Quint's `run --invariant` "will try to find an invariant violation. If it finds one, it prints
the trace" (`.reference/quint/docs/content/docs/quint.md:444`): there a violation is the failure.

**What the spec and mission say.** 011.10: "`charter test` passes a file that produces no error
diagnostic and whose every claim holds (eFLINT's `--test-mode` criterion)". 013.1: "After every
phrase, every invariant that does not hold is reported as a violation". 013.2: exploration
"searches from the program's end state and from each scenario's end state … and reports the
shortest trace after which some invariant does not hold as a failed claim". `lib/README.md`:
every property is "checked after every phrase and explored from every end state by
`charter test`". CHR031 (`--require-complete-explore`) exists because a file with invariants and
no depth checks nothing. Law 3: violations are facts. `AGENTS.md`: a tool that stayed silent is
a bug.

**Not in question.** The violation is reported one phrase late. 013.1 says "after every phrase";
a mutating phrase does not report it and the next read does. That is a bug and is fixed
whatever the ruling.

**Options.**
- (A) *Keep the criterion.* A violation is a report. Pass `--require-complete-explore` in
  `tools/examples-check` and add `//! explore` to the examples. No language change; the default
  stays silent, and the author of the settlement example did not know to ask.
- (B) *End states are always checked.* The end state of the program and of each scenario must
  satisfy every invariant, with or without `//! explore`; a scenario that means to end in breach
  says so with `?!name().`. Mid-run violations stay reports, so setup under construction and a
  deliberate breach inside a scenario are untouched. Seven corpus files become tolerances
  ("passes upstream, fails in Charter"), under a decision that names eFLINT's test-mode
  criterion as the difference.
- (C) *As (B), for files that declare a `Scenario` or a `Clause`.* No corpus file does, so no
  tolerance; the criterion then depends on what a file contains.

**Mission fit.** (B) is what 013.2 and `lib/README.md` already describe; it removes the case
where the same program passes or fails according to a directive. (A) keeps Law 12 untouched and
leaves the silence. (C) avoids tolerances at the price of a second criterion (Law 13).

**Prediction.** (B), 60%. (A) with the gate turned on in the examples check, 30%.

## B14. An unresolved evidenced premise becomes "yes" through a derived fact (#9)

**Ruled 2026-11-07: (A), permanently for `Evidenced` (`CHR038`, `D31`); the `004.12` conflict leak is filed separately as #80 with the bounded taint-overlay route.**

**Finding.** `Evidenced Bool lacks-capacity`, nothing tendered. `Power direct … Valid when
Not(lacks-capacity())` is `undetermined`. `Bool capable Holds when Not(lacks-capacity())` and
`Power factored … Valid when capable()` is valid. The same condition changes its answer when it
is given a name. The mirror case was met in the insurance example: an exclusion whose cause is
contested, under `Exception … Rejects when caused-by(…)`, stops excluding, and the claim is paid.

**Measured.**
- A rule conflict behaves the same way. With two unranked defaults in conflict on `c`,
  `?Conflict(c(A))` holds, and `Fact d Holds when Not(c(p))` holds, and a power guarded by `d` is
  valid.
- An `Open` fact does not: `Fact d Holds when Not(o(p))` with `o` open and unassigned is
  `CHR100: missing input` at the declaration.
- Two programs read an evidenced fact bare in a derived fact: `Examples/RentersInsurance`
  (`covered`, five reads) and the PSA (`amendment-consent-complete` reads
  `substrate-assurance-verified`).

**What the references do.** eFLINT has no evidence; its unknown is the open type, which raises
missing input through a derivation unless explicitly ignored
(`.reference/eflint/src/Language/EFLINT/Eval.hs:26`, `ignoreMissingInput`, used only for
invariants and violation conditions). Catala raises a runtime `Conflict` error when two
exceptions apply (`.reference/catala/compiler/shared_ast/interpreter.ml:1006`); it never picks.

**What the spec and mission say.** 004.11: "a bare `Evidenced` premise in an act's `Holds when`
or `Valid when` propagates Kleene 3-valued `yes | no | undetermined` plus `unmetEvidence` without
inventing truth". It speaks of an act's conditions and is silent on derived facts. 004.12: on a
conflict "neither is derived … and dependent guards become `undetermined`". Law 6: "Charter never
invents a fact."

**Options.**
- (A) *Refuse.* A derived fact, `Default` or `Exception` that reads an evidenced fact must say
  which status it means (`Established`, `Refuted`, `Unresolved`, `Conflicted`); a bare read is an
  error. Small and loud. The author loses the ability to name a three-valued condition, which is
  why the healthcare directive merged two acts into one. Two programs change.
- (B) *Propagate.* A derived fact whose derivation depends on an unresolved or conflicted premise
  is itself undetermined, recorded as the rule conflicts are, and guards that read it are
  undetermined. This is what 004.12 already promises for conflicts and does not deliver through
  a derived fact. It touches saturation and the least-fixpoint theorems.
- (C) *Refuse now, propagate later.* (A) as the rule today; (B) lifts it when built.

**Mission fit.** Law 6 rules out the status quo. (B) is the one meaning; (A) is honest and
cheap; a derived fact that silently reads "unresolved" as "no" is exactly what `Open` refuses.

**Prediction.** (C), 65%: refuse bare reads of evidenced facts in derived facts now, and file
propagation (which also repairs the conflict case) as the design. (B) directly, 25%.

## B15. An effect that reads a `Var` with no value does nothing (#11)

**Ruled 2026-11-07: (A), scoped to `Var` and implicitly bound `Function` reads in effects, reported as missing input (`CHR100`, `D32`).** Zero new divergences on the 196-file eFLINT corpus.

**Finding.** `Var paid Identified by usd`, no `+paid(0).`, and
`Act pay … Creates paid(paid.usd + usd)`. `pay(A, 500)` is reported `lawful: yes valid: yes` and
no `paid` exists afterwards. A condition that reads the unset variable is false, and so is its
negation.

**Measured.** Met in three examples (settlement, home purchase, guaranty), each fixed with a
genesis line. The same unset state is why invariants are false during library setup (B13).
`Param name = n` already declares a `Var` with an initial instance (014.1); none of the three
authors reached for it, because a running total is not a parameter.

**What the references do.** eFLINT is the same: a `Var` is a fact type restricted to one
instance (`.reference/eflint/src/Language/EFLINT/Spec.hs`), and a free variable over it ranges
over the instances that hold, so an expression over an unset one produces no results and no
effect.

**What the spec and mission say.** 003.7: "When an instance of a `Var` type is created, every
other instance of the type is made false". 004.7: a free variable over a non-enumerable type
ranges over the instances that hold. 005.4: "further free variables of an effect are bound to
every valid instance (as `Foreach`)". So an effect with nothing to bind produces nothing, by
specification. `AGENTS.md`, No silent fallbacks.

**Options.**
- (A) *An effect that produces nothing because a `Var` it reads has no value is a runtime
  error* on that trigger, naming the variable. Conditions and invariants are unchanged, so
  setup under construction still works. An eFLINT program that relies on a silent no-op changes;
  the corpus has to be run to see whether any does.
- (B) *A starting value at the declaration*, `Var paid : Money(USD, 2) = 0`, and a `Var` with
  none is an error wherever it is read. Cleaner, larger, and it makes module setup atomic, which
  B13 would also like. It is issue #42's proposal and needs the eFLINT default kept for `.eflint`.
- (C) *A warning from `check`* when an effect reads a `Var` that no declaration initialises.
  Fires on every library module's totals.

**Mission fit.** (A) removes the silent loss with the smallest change and no new spelling.
(B) is where the language should end up and should not be decided inside a defect.

**Prediction.** (A), 65%, with (B) left to its own brief. (C), 15%.

## B16. `Retracts` cannot reach evidence another act tendered (#12)

**Ruled 2026-11-07: (A) + `By s`, `Retracts !e`, and `CHR109` warning on empty retraction (`D33`).**

**Finding.** `Act determine … Supports lacks()` and `Act withdraw … Retracts lacks()`.
`determine(DrAdler). withdraw(DrAdler).` leaves the fact `Established`. Evidence is stored as
`$ev_support(lacks(), "determine")`, keyed by the name of the act, and a retraction removes
the entry keyed `"withdraw"`, which does not exist. The act is reported valid.

**Measured.** Two physicians performing `determine` leave one piece of evidence, not two.
`RetractEvidence lacks() By "doubt".` as a phrase does remove what the act `doubt` tendered: the
source of a piece of evidence is a string, and for an act it is the act's name. The healthcare
directive worked around it with a negative `Finding`, which leaves the fact `Refuted` where the
text means "as it was before".

**What the references do.** None has evidence. The nearest is eFLINT's `Obfuscates`, which
removes an assignment whoever made it.

**What the spec and mission say.** 005.11: "Any act may also carry `Supports e`, `Rebuts e`, or
`Retracts e` to tender or retract evidence on an `Evidenced` fact when valid". 011.14:
"`SubmitEvidence [!]e [By s].` and `RetractEvidence e [By s].` tender or retract external
evidence". Neither says what identifies a piece of evidence. Law 6: the program can say where a
fact came from.

**Options.**
- (A) *Evidence belongs to whoever tendered it.* The source is the actor (with the act recorded
  for the explanation). `Retracts e` in any act removes what this actor tendered on `e`. Two
  physicians are two pieces of evidence. Explanations that print a source change from an act
  name to an actor.
- (B) *Name the source.* Keep the key; `Retracts e By determine` says which act's evidence is
  withdrawn. Smallest change; two physicians are still one piece of evidence, and one of them
  withdraws for both.
- (C) *Both.* Key by actor and act; `Retracts e` removes this actor's evidence from any act,
  `Retracts e By a` only what was tendered through `a`.

**Mission fit.** Law 6 asks where a fact came from, and an institution's answer is "who", not
"through which form". (A) gives that with no new spelling; (B) leaves the two-physicians
answer wrong.

**Prediction.** (A), 70%. (C), 20%.
