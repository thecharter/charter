# AGENTS.md — Charter

Rules for anyone, human or agent, who changes this repository. `CLAUDE.md` points
here. The mission and laws are `docs/mission.md`; decisions and their reasons are
`docs/meetings/README.md`; the plan for the current redesign is
`docs/plans/2026-10-22-redesign.md`. Read those three before the code.

## Mission

Charter is a language for institutions: a program is the English of a charter,
contract, or law, written so a machine can give the three answers about any event
(did it occur, was it lawful, did it take effect) and prove that every projection of
the program (the agreement people read, the guard a chain enforces, the brief an AI
acts under) is faithful to the same source. Lean is how Charter is right, never how
Charter is used. The goals, in precedence order, and the fourteen laws are in
`docs/mission.md`. Every decision is an instance of a law; a decision that needs a
new law writes the law first.

## Core principles

**We own every bug.** Nothing is "pre-existing". A failure is pre-existing only when
verified on the previous commit in a `git worktree` or a clone, never with
`git stash`, which is banned (it has destroyed uncommitted work; `pop` and `drop`
too).

**Root cause means the exact rule, phrase, or step.** A wrong transition is traced
to the rule that fired or failed to fire, the derivation step that produced the
fact, or the stage whose dump first shows the wrong record, and observed there.
Transition tables, scenario outcomes, and `grep` over views are hypotheses, not
proof; never propose a fix or a deferral from a characterization alone.

**Every bug has a route, and you state it.** Before the first edit, name the tools
you will use in order and run the first. By bug class:

- wrong lawful/valid/occurred answer: `charter explain <who> <act> [scenario]`, then
  the lowered `Law` for that rule (`--out json` at the Lower stage once it exists;
  today, `#eval` the rule in a scratch Lean file importing `Charter`);
- wrong or missing derived fact: `?why` / `charter why` (plan §2.2.11; until it
  exists, the stage dump and a minimal scenario);
- wrong provenance verdict (covered, interpreted, stale): `charter trace <clause>`
  and the clause's spans beside the document text;
- wrong projection: the projection's soundness theorem names what it promises; a
  divergence is a counterexample to that theorem or a bug in rendering, and you say
  which;
- a Lean build failure in an example: the first error, in the file that owns the
  fact (see "One owner per fact").

A fix commit cites the output that proves the exact line.

**A tool that stayed silent is a bug.** If `check` said ok while a span named an
invariant no theorem backs, if a scenario passed on a program whose rule was never
reachable, if a dump said nothing while the state was wrong, the tool is wrong and
is fixed or filed in the same batch as the bug.

**Three-action trip-wire.** If your last three actions were edit, build, read
output, and you cannot name the exact wrong rule or step, stop and switch to the
route's next tool: a smaller scenario, a stage dump, `#eval` on the record, the
decision log. Do not start a fourth.

**Tools are products.** When a hunt needs a capability that does not exist (a stage
dump, `why`, a scenario reducer), file it during the hunt and prefer building it
over a workaround. Before building, grep `Charter/` and `docs/` for what already
exists.

**Build is verification, not experimentation.** Before `lake build`, state the
question you are answering and what each outcome tells you. A full build with the
PSA companions takes minutes; `grep`, reading, a scratch `#eval`, or running the
installed `charter` on a small program usually answers first.

**One owner per fact.** Resolve decides names, types, and arities; Lower decides the
`Law` record; Eval decides state and the three answers; Project only reads records.
A downstream stage may propagate, materialize, and verify a fact; it never
reconstructs or overrides one from text or representation. Smell test: if deleting
a downstream heuristic could change which programs are accepted or what a transition
reports, the boundary is wrong. When you fix a bug, move its answer to the owner;
never add a second derivation. (Today's code has the v0.3 shape, `src/Charter/Surface`
→ `src/Charter/Core` → `src/Charter/Projection` → `src/Charter/Tooling`; the same rule applies.)

## Ceremony is a design defect, not an author error

A rule the author writes only to satisfy the checker, a fact asserted in a scenario
that no party's act explains, a condition that restates another, or an English span
pasted into several rules is evidence the language is wrong somewhere. Your job is
to notice and raise it, not write more of it.

**The test.** For any line of a `.charter` program: *would a reader of the
institution think it says something?* If it is there because the tool requires it,
it is ceremony.

**Signals that always trigger the test:** the same `Valid when` on most acts; a
`Conditioned by` that repeats a `Holds when`; a `+fact` in a scenario with no act
behind it; a `Clause` quoted twice; a `tagged` list written out by hand; an
`Approved` hash copied to silence `check`; a comment explaining a workaround for the
language; the same fact encoded in two places.

**What to do.** Stop and raise it before writing more in that pattern. Give: the
program as a reader sees it; why it exists (the rule or representation); which law
it violates; how many times the pattern occurs in `examples/` and `lib/` (count
it); what the program would look like if the language were right and what would
have to change. Never copy a ceremonial pattern from a neighbouring example because
it is local precedent; precedent measures how long the defect went unraised.
Writing the same workaround a second time is a report.

## No silent fallbacks

When the tool cannot do something correctly, fail loudly with a diagnostic and a
non-zero exit. Forbidden regardless of what tests say: a stub body or `sorry`; a
projection that drops a rule it cannot render; an importer that skips an eFLINT
construct and continues; a lowering that "simplifies" a condition into one that
behaves differently; a `TODO` in emitted output. **An importer that produces 30/30
files with silent gaps is worse than one that produces 0/30 with a loud error.**
Name the construct and location, return non-zero, leave the work visible. If a
helper has no error path, wire one.

## "Done" is a claim that requires evidence

Not done because `lake build` is green, the battery passed, the commit was
accepted, or output files exist. Done when the output is what a reader of the
institution would expect, the edge cases you noticed have fixtures or a comment
saying why not, and anything unsolved is filed or surfaced as a loud failure. Gut
check: *did I make the success condition true by doing the work, or by redefining
the success condition?* Especially: a scenario made to pass by editing a clause's
English or its `Approved` hash is not done; it is a Law 8 violation.

## Verify by running, not by reasoning

The semantics has corners where reasoning from a paper or a type signature goes
wrong: `Holds when` versus `Conditioned by` versus `Derived from`, create-beats-
terminate within a step, what a disabled act's effects do (D5), open versus closed
types, free-variable binding in conditions versus effects.

**Spell it and run it.** Before concluding a construct means something, write the
smallest `.charter` program that uses it and run it. For eFLINT questions, run the
Haskell in `.reference/eflint` as well as Charter and compare.

**Exhaust small answer spaces in one pass.** "How many ways can a duty end?" has an
enumerable answer; test all of them and write the matrix. Concluding and patching the
same question twice means stop and enumerate.

**Code settles facts; intent is the maintainer's call.** When eFLINT's paper and its
implementation disagree, or the spec and `src/Charter/Core/Semantics.lean` disagree,
settle the fact by running and surface the contradiction. Never assume which side is
canonical. Test the inconvenient premise first.

**Otherwise, keep moving.** Stop only for a decision genuinely Eric's: intent,
scope, a go/no-go on real risk, normative spec wording, an English document. On a
clear, self-scoped path, proceed and report.

## Anti-patterns

**Weakening the check.** If a check fails, make the code pass it or confirm with
Eric that the check is wrong. Never downgrade it, add an exemption, or route around
it.

**Editing a protected program to make it pass.** Protected: everything under
`examples/`, `uat/`, `test/eflint-corpus/`, the English documents
(`examples/*/*.md`), and every `Approved` hash. When a compiler, library, or spec
change breaks one, the change is what broke. Ruling pattern (from With, 2026-09-22):
a **spec change** that breaks an example updates the example in the same change,
under the ruling, and says so; a **compiler or library** change that breaks an
example is a defect in the change. The English is never edited to fit a rule; the
rule is the answer under review (Law 8).

**A user-visible Lean term.** No diagnostic, path, flag, help text, or document an
author can see names Lean, Lake, a tactic, `sorry`, or a theorem the author did not
ask for (Law 11). `test/gates/law11-no-engine-in-output.sh` enforces it on every output the binary
prints.

**"Pre-existing" without evidence.** See Core principles.

**"Good enough for now."** A 90% importer, a projection that handles most rules, a
checker that catches most drift: each is 0% done with a reporting problem. The bar is
correctness, not coverage.

**A second spelling.** Two ways to write one meaning is a defect (Law 13). When you
add the better route, delete the old one in the same change or file the deletion with
a date. Today's known second spellings and their scheduled deletions are in the plan
§2.3.

## The specification leads

`docs/spec/` is the spec (a skeleton today; the v0.3 architecture tour it replaces is
archived at `docs/completed/2026-10-18-charter-spec-v0.3.md`; plan §5.3). Two absolute rules:

**The spec leads the implementation.** A spec change is a ruling that the product is
NON-COMPLIANT until the implementation catches up. No "implement first, spec after";
no holding spec text until code lands; no reverting spec text to match code. When
they disagree the implementation is wrong, or the disagreement goes to Eric; it is
never resolved by quietly editing the spec.

**Spec changes are solemn.** Only Eric authors or blesses normative wording. An agent
may draft and propose; a direction, a mission statement, or an agreed plan is not
approval of specific words.

### "Do the thing": the decision procedure

Every spec change and most decisions go to Eric as one brief with four parts; then
wait for the ruling:

1. **What the references do.** eFLINT, Catala, Quint, Symboleo, checked in their
   trees under `.reference/`, with paths. Not from memory.
2. **What the spec and mission currently say.** Quote them. Check whether the
   question is already ruled (`docs/meetings/README.md`) before reopening it.
3. **Mission fit.** Which law the choice instances, and which option is most
   Charter-like.
4. **A committed prediction** of Eric's ruling with a confidence, derived from the
   decision record. Falsifiable, not a menu.

Never present an option that plainly fails a law (blocks an occurrence, collapses two
of the three answers, shows the author Lean, adds a second spelling). One clause
saying why it was dropped is enough.

**Delegated decisions.** A question that is not about semantics, trust (Law 10), the
English documents, or anything hard to reverse, and has a prediction at 75% or
higher, does not wait: implement the prediction, spec words included, and record the
full brief in the decision log as **delegated**. Eric vetoes afterwards; a veto is a
revert plus a new entry. Examples, UAT fixtures, the eFLINT corpus, the English, and
normative wording stay his.

## Filing bugs

If the spec says something should work and the tool disagrees, that is a tool bug;
never silently work around it. File with the spec section, a minimal `.charter`
reproduction, expected versus actual, and the workaround used, so the fix can remove
the workaround.

## Decision log

`docs/meetings/README.md`, newest first, one file per decision, named
`YYYY-MM-DD-D<N>-<slug>.md`. Record the ruling, the laws it instances, context,
alternatives, what the references do, mission fit, cost accepted, and **reopens if**.
Supersession is written in both entries. Consult it before reopening a settled
question. Terse: reasoning, not a changelog. The briefs that preceded a batch of
rulings sit beside them (`2026-10-22-briefs-for-ruling.md` is the model).

## Editing protocol

### Before editing

Read the relevant source. When you cannot find something, grep `Charter/`,
`Examples/`, `docs/`, and `.reference/eflint` before assuming it does not exist.
Never rely on memory.

### Code style

Match the surrounding code and the laws at the character level. In Lean: no
`sorry`, no `native_decide`, no new axioms (Law 10); a decided scenario is `decide`
with no axioms; every definition that reduces in the kernel is written with
structural recursion and explicit fuel, never `partial`, so `decide` can run it.
In `.charter`: eFLINT's spelling (D2); the least the institution needs to say.

### One logical change at a time

Do not batch unrelated changes. Small changes make debugging possible.

### Commit authorship

Every commit is authored by the human who drove the work, under their own name
and email. Agent-driven work is committed under the identity of the human who ran
the agent. Never add an AI assistant, model, tool, or vendor as author, co-author,
trailer, or credit; no `Co-Authored-By` for AI assistance (adopted 2026-10-23).

### Rebuild and verify (tiered; plan §5.4)

- **Fix tier**, every edit: `lake build` of the touched targets, plus running the
  installed `charter` on the fixtures you touched.
- **PR tier**: `tools/battery`: `lake build` (all targets, zero warnings), every
  gate under `test/gates/`, `charter check` on both examples with zero FAIL and
  zero STALE, `charter sim` 16/16 and 8/8, and the eFLINT corpus under
  `test/eflint-corpus/` with only the tolerated differences. Views are
  regenerated by hand and the `git diff` reviewed.
- **Release tier**: PR tier plus `charter prove` on both examples and the examples
  dashboard with `git diff --exit-code`.

### Working efficiently (agents)

- Run the fix tier on what you touched and show each new fixture **failing** before
  its fix.
- In a worktree, use absolute paths for every file you read or edit; a relative path
  silently resolves to the main checkout.
- Never run the full battery or `charter prove` on both examples on your own; the
  coordinator runs those once per stack.
- Never wrap commands in an opaque script (`sh -c`, `bash -c`, `eval`, `xargs
  <cmd>`, a heredoc that edits files in place): the permission checker cannot read
  inside them. Put multi-step logic in a script file under `tools/` and run that.
- Commit locally; do not push unless told. A pushed branch always has a PR.
- Re-read any file before editing it after ten or more messages; context compaction
  may have destroyed your knowledge of it and the edit will fail or, worse, succeed
  wrongly.

## Repository layout

Today (v0.3; the target layout is plan §4 and this section is updated as it lands):

| Path | What |
|---|---|
| `src/Charter.lean`, `src/Charter/` | the language: `Core/` (syntax, semantics, provenance, views, explain, composition, ratchet, population, refinement), `Modules/` and `Substrate/` (standard library and substrate theorems), `Projection/` (veil, prompt, abi, visualization), `Surface/` (`.charter` grammar, lowering, export, `charter_program`, the Lean macros scheduled for deletion), `Tooling/Cli.lean` |
| `Examples.lean`, `Examples/` | `SovereignAgency/` and `AutonomousCommons/`: each a `.charter` program, its English, scenarios, and a Lean companion with theorems and simulations (companions are deleted when their Charter replacements pass, D10) |
| `src/Main.lean` | the `charter` executable |
| `docs/mission.md`, `docs/meetings/`, `docs/plans/`, `docs/spec/`, `docs/completed/` | mission and laws, decisions, plans, the spec (skeleton) and its diagnostic-code registry, superseded documents |
| `test/eflint-corpus/` | the vendored eFLINT tests and examples (D2), protected; `tolerances.md` lists the only accepted differences |
| `test/gates/` | the Law 14 gates; one script per law so far |
| `tools/battery` | the PR-tier runner (build, gates, checks, sims, corpus) |
| `HANDOFF.md` | reverse-chronological session log (newest section first; verify every hash it names with `git log` before acting) |
| `.reference/` | eFLINT, Catala, Quint, Symboleo checkouts; untracked, ignored, read-only |
| `out/` | build output; ignored |

Build: `lake build` (Lean 4.24, no Mathlib). The binary is `.lake/build/bin/charter`.

## Common mistakes

- Guessing an API or a keyword; read `src/Charter/Surface/Dsl.lean` and
  `.reference/eflint/src/Language/EFLINT/Parse.hs`.
- Working around a semantics bug in a program instead of fixing the semantics.
- Treating eFLINT's paper as the implementation; run the Haskell.
- Using `lake build` as a debugging tool instead of a scratch `#eval`.
- A `.charter` file edited in a Lean module's directory without rebuilding the
  module that embeds it: Lake does not track `.charter` inputs.
- A `StringTable` built as closures inside one structure literal for a type with
  many constructors: the Lean 4.24 code generator miscompiles it (segfault in
  `mi_malloc`). Use the `charter_string_table` command, which emits top-level
  definitions.
- `git stash`.

## Success checklist

A change is acceptable only if, on a clean tree: `lake build` succeeds with zero
warnings; the trust grep (`sorry`, `native_decide`, `axiom`) over `src/Charter/`,
`Examples/`, `src/Main.lean` is empty; the leak grep over `src/Charter/` for any example
name is empty; `charter check` on both examples reports zero FAIL and zero STALE;
`charter sim` reports 16/16 and 8/8; every new fixture was seen failing before its
fix; the decision log records any judgment call a future maintainer might
re-litigate; and `HANDOFF.md` has a new section for the session. If any fails,
continue until it passes.

## Landing changes

Every change reaches `main` through a pull request. A PR is a draft until the PR
tier is green on the maintainer's machine with the pinned `lean-toolchain` and the
result is posted on the PR; GitHub lanes run nightly or on dispatch and are not a
merge signal. Dependent PRs are a `gh stack`, never hand-chained bases. Merge with a
squash. The `lean-toolchain` pin is bumped first, in its own change, when a feature
needs a newer toolchain; the surface is never reverted to appease an old pin.
