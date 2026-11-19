# D50 — `017.4` blessed; replay failures split by kind; three spec pointers reworded; dead flags deleted; the Law 14 gate runs in both directions

**Laws:** 10, 13, 14 (`docs/mission.md`). Briefs `B37`, `B38` (`2026-11-18-briefs-for-ruling.md`). Sharpens `D46`, `D48`, `D49`. Rewords spec `015.5`, `017.4`.
**Date:** 2026-11-18
**Status:** ruled (Eric, 2026-11-18), except item 6, which extends the `B38` ruling to a flag the brief misdescribed and is his to veto

## Ruling

1. **`017.4`, blessed with one change.** The draft stated only the violation direction; `D48` item 3 is a biconditional, and the scope limit belongs in the spec so the reader sees what the *checked* tag covers (`Law 10`). The spec carries Eric's words: the replay runs in the `--mode` the model was generated in, passes only when the evaluator's verdict at the end agrees with Quint's, does not compare intermediate states, and is *checked*, scope one trace. The trace does not record which invariant Quint ran against (`#meta` has `status`, no name), so the name is not compared.
2. **`CHR054` stays.** Two codes: an unreadable or mismatched `Document` (`CHR053`, `Load`, every command; fix: put the document there or fix the pin) and `partial` coverage at delivery (`CHR054`, `Provenance`, `build`/`generate`; fix: ground the rules or drop the `Document`). A code that needs its message to say which of two things happened defeats the point of a code.
3. **Replay exit status.** A replay that passes exits 0. A **finding** exits 1: the evaluator does not offer or cannot take a recorded step in the given mode, or the verdicts disagree. An **input** problem exits 2, like other usage errors: an unreadable or malformed trace, one recorded without `--mbt`, an action or a pick that is not the model's (another program's trace). Text lines begin `FAIL` and `INPUT`; `--out json` carries `"failure": "finding" | "input"`. (`Project.ReplayFailure`.)
4. **Names.** `thresholds` and `--replay` are confirmed.
5. **`B37`, A.** Three present-tense sentences are reworded; dated entries stay.
   - `015.5` carries Eric's words. The theorems in `src/Charter/Modules/` are the v0.3 Lean modules' theorems about their own Lean records; they are not proofs of the `.charter` modules' `Invariant`s by name, which is what `D8` promised. A module invariant is *checked*; *proved* arrives when `charter prove` discharges a theorem of that name. `015.5` names no directory for those proofs until one exists, which also settles `D8`'s `lib/lean/`.
   - `docs/spec/diagnostics.md` and `docs/spec/README.md`: the pointers to `test/diagnostics/` and `tools/spec-inventory` now name what exists (`//! expect-error:` fixtures under `test/spec/`, gates under `test/gates/`; `test/gates/spec-inventory.sh`). These two rewordings are an agent's, of pointers and not of the language; Eric's to correct.
   - The gate checks backticked paths in `docs/spec/` and skips history by structure, not by a date on the line: the `## Changelog` section of `docs/spec/README.md` and paragraphs that open with `*Finding (`.
6. **`B38`, A: deleted.** `charter verify` no longer accepts `--require-complete` or `--report-assumptions`; exit 3 and `--out json` already do what they pretended to. **Correction to the brief:** it said `--require-complete` was real on `explore`. It was not: `Explore.lean` parsed it into a field nothing read. It is deleted there as well, on the ruling's own reasoning (`explore` exits 3 on an inconclusive result). That deletion was not ruled on a true premise and is Eric's to veto.
7. **`docs/rfc.md` is marked a dated design record** in its header and is outside the gate. It shows `--backend smt`, `--require-complete`, and `--report-assumptions`; they are what was intended on 2026-11-06.
8. **The reverse gate.** `D49` checked spec → `src/`. Dead flags are `src/` → spec: every `--flag` a parser in `src/` accepts must be named in `018`. `018` gained a "Flags by command" list (35 flags it had not named, for `explore`, `verify`, `bundle`, `doc`, `approve`, `build`, `test`, `generate`, `analyze`, `plan`, and `charter-server`) and an exit-status sentence for 3 and for the replay.

## Evidence

- `test/gates/law14-sentences-resolve.sh`: 120 flags, 116 identifiers, and 192 paths in 23 documents resolve; 73 parsed flags are named in `018`; 25 CI scripts have no unconditional pass. Its self-check now also requires that a path naming nothing is caught once outside history and not inside it, and that a parsed flag `018` does not name is caught (with `--solver` against a chapter that mentions `--solver-kind`).
- `tools/verify-check`: 31 passed. Another program's trace, a file that is not a trace, and a missing trace exit 2; the wrong mode and an unreached verdict exit 1; `--require-complete` on `verify` and on `explore`, and `--report-assumptions`, exit 2 as unknown flags.

## Limits, stated

- The reverse gate shows a flag is *named*, not that it does something. Writing the list is what exposed item 6 and the entries of `B39`; the gate would not have.
- Paths containing `{…}`, `*`, or `<…>` are not checked.
- `lib/entity_group.charter` still says in a comment that its theorems "are to be reattached by name under `lib/lean/`"; `lib/` is outside the gate.

## Reopens if

A flag is found that is named in `018` and does nothing (then the gate needs a use check, not a mention check), or `B39` is ruled.
