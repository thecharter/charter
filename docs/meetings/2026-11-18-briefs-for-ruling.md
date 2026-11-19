# Briefs for rulings, 2026-11-18 (`B34`–`B36`)

**Status:** ruled (Eric, 2026-11-18) as `D46`–`D48`; each brief ends with its ruling. When written, nothing below was implemented. Each arose while fixing the red CI lane (`D45`); `B34` is also the first design point of an outside review of the repository received the same day.

## B34. A program that declares a `Document` it cannot read is checked as if it had none; `build` and `generate` deliver without asking about provenance (`012.7`, `012.10`, `017.1`, `018`, `Law 8`)

- **What happens today (run, not read).** `charter check` on a program whose `Document "x.md"` is missing and carries no `SHA256` prints `WARN missing.md could not be read …; verbatim check skipped` and then `ok … coverage partial, 0 warning(s)`, exit 0 (`src/Charter/Cli/Provenance.lean`). `charter build` refuses a failed or `STALE` claim but not a warned one, so it signs a bundle whose manifest says `partial`; its one-line summary does not print the coverage. `charter generate` runs no provenance check at all. `--require-provenance` exists on `check`, `run`, and `test` only.
- **What the references do.** Catala refuses a law text it cannot find (`.reference/catala/compiler/surface/parser_driver.ml:443`, "Included file '%s' is not a regular file or does not exist."). eFLINT has no source-text binding to compare (`.reference/eflint/src/Language/EFLINT/Options.hs:66-71` checks only its own includes).
- **What the spec and mission say.** `012.7`: "A document that cannot be read is a warning, not a failure, and the check is skipped." `012.10` makes `--require-provenance` the opt-in. `Law 8`: "a clause's text is checked verbatim against the authoritative document." `AGENTS.md`: "When the tool cannot do something correctly, fail loudly with a diagnostic and a non-zero exit." `docs/rfc.md` §4.5: "refuse an unqualified completeness claim unless … all referenced documents are approved and current."
- **Mission fit.** `Law 8`. A program that names its authoritative document and cannot produce it has not been checked against its English; saying `ok` is the tool staying silent. An author with no `Document` at all is a different case and is already named (`illustrative`).
- **Options.**
  - **A.** (1) A declared `Document` that cannot be read fails `check`, `run`, `test`, and `build` (`012.7` reworded). (2) `build` and `generate` refuse coverage `partial`; they accept `complete`, and accept `illustrative` while printing it in their summary line and stamping it in the output. (3) `--require-provenance` keeps its meaning (refuse `illustrative` too).
  - **B.** As A, and `build` / `generate` also refuse `illustrative` unless `--allow-ungrounded` is passed. Every `test/verify`, `test/prove`, and benchmark fixture that is built or generated needs the flag.
  - **C.** Leave `012.7`; print the coverage in `build`'s summary line only.
- **Prediction.** A, 80%. It closes the silent skip without making an author who is exploring write a `Document` first, and it adds no flag (`Law 13`). The reviewer argued for B; B's cost is a flag on every fixture, which is ceremony for programs that claim no document.
- **Needs from Eric.** The ruling, and the words of `012.7`.
- **Ruled (Eric, 2026-11-18): A, sharpened.** The classification is stamped into every output, and the warning counter is fixed. `D46`.

## B35. Spec `017.4` certifies Quint counterexamples by `importQuintTrace`; no such function exists (`017.4`, `D28`, `D45`, `Law 9`, `Law 10`)

- **What happens today.** After `D45` the model's step relation is checked against the evaluator, and CI has Quint's simulator confirm each verdict. A counterexample Quint finds is not read back. `017.4` and `D28` item 3 say it is ("counterexample traces (`importQuintTrace`) are certified by native replay through `Charter.Eval`"). `rg importQuintTrace src/` is empty and was empty before `D45`.
- **What the references do.** `quint run --out-itf` writes the trace in the Informal Trace Format, and `--mbt` adds the action taken and its nondeterministic picks to each state (`.reference/quint/quint/src/cli.ts`, `itf.ts`).
- **Mission fit.** `Law 9`: with an imported trace the check reads the emitted text; today it reads the model the text was printed from, and trusts the printer.
- **Options.** **A.** Implement it: `charter generate --target quint --replay-trace <itf.json>` maps each `mbt::actionTaken` and its picks to a phrase, replays it through the evaluator, and compares every state. One new flag in `017.1` and `018`. **B.** Reword `017.4` to what is checked.
- **Prediction.** A, 75%.
- **Needs from Eric.** The ruling; the flag's spelling if A.
- **Ruled (Eric, 2026-11-18): A, in two moves.** `017.4` is reworded first; the replay is `charter verify --replay <trace.itf.json>`, verdict agreement only, tagged `checked`. `D48`.

## B36. `charter verify --backend smt` runs the solver and does not read its answer; the emitted encoding constrains nothing (`D20`, `T30`, `Law 10`)

- **What happens today (run, not read).** `Verify.Smt.checkBounded` writes `TVIR.emitSmtLib2`, runs `z3` on it, and on any answer sets the label to `z3+native-replay` (`src/Charter/Verify/Smt.lean`, `| some _ => solverLabel := …`). The verdict comes from `Verify.search` over a threshold menu. The encoding for `test/verify/t30_smt_symbolic_int.charter` declares one `Bool` per type and asserts `(or (not (not true)))`: `z3` answers `sat` at depth 1, 2, and 3, while Charter reports safe at depth 1 and violated at 2 and 3. The CI step that "exercised" this ran a fixture that does not exist (`t30_smt_symbolic_threshold.charter`) under `|| true`; it now runs the real fixture and says in a comment what it does not check.
- **What the spec and claims say.** `docs/claims.json` (`project.emitted_targets_differential_checked`): "… and CI solc/Foundry + quint + z3 execution". Output label: `smt/z3+native-replay`.
- **Mission fit.** `Law 10`: the label tells the user a solver took part in the verdict. It did not.
- **Options.** **A.** Label the backend for what it is (threshold-menu search with native replay), stop invoking the solver, and keep `--emit-smt` off until the encoding means something. **B.** Write the bounded encoding over the guard IR (arrays for facts keyed by integers) and make the verdict the conjunction of the solver's answer and the replay.
- **Prediction.** A now, 70%; B is its own work package.
- **Needs from Eric.** The ruling.
- **Ruled (Eric, 2026-11-18): A, sharpened.** The backend is renamed `thresholds`, `--backend smt` is refused, and the solver code and flags are deleted; B has an exit criterion. `D47`.

---

# Briefs for rulings, 2026-11-18, second batch (`B37`–`B38`)

**Status:** awaiting ruling (Eric). Nothing below is implemented. Both were found while writing the `D49` gate.

## B37. Five paths named in `docs/spec/` name nothing in the tree (`Law 14`, `D49`)

- **What is there today (scanned, then read).**
  - `015.5`: a module's properties are "to be proved in `lib/lean/Modules/` by name … (D8; pending `prove`, 013.4)". There is no `lib/lean/`. The module proofs that exist are in `src/Charter/Modules/` (`ExitAndVoice.lean` and eight others).
  - `docs/spec/diagnostics.md`: "`test/diagnostics/` holds one fixture per code once the fixture format (plan §5.4) lands". There is no `test/diagnostics/`; diagnostics are tested by `//! expect-error:` fixtures under `test/spec/`.
  - `docs/spec/README.md`: the grammar chapter "is checked against the parser by `tools/spec-inventory` once it exists". It exists, as `test/gates/spec-inventory.sh`.
  - `docs/spec/README.md` changelog (2026-10-25) and the dated finding in `013`: `Examples/AutonomousCommons/commons.eflint` (now `commons.charter`) and `Examples/SovereignAgency/law3.eflint` (no longer in this repository). These are dated entries about what was true then.
- **What the references do.** Not a language question; none consulted.
- **What the spec and mission say.** `Law 14`: a claim that nothing checks is not yet true. `AGENTS.md`: "no reverting spec text to match code"; only Eric rewords the spec.
- **Mission fit.** `Law 14`. The first three are sentences about the present or the future that the tree contradicts or has overtaken. The dated two are history and honest as history.
- **Options.** **A.** Reword the first three to what is there (`src/Charter/Modules/`; `test/spec/` fixtures with `//! expect-error:`; `test/gates/spec-inventory.sh`), leave the dated entries, and extend the `D49` gate to backticked paths, skipping lines that carry a date. **B.** Leave the text; no path check.
- **Prediction.** A, 80%.
- **Needs from Eric.** The ruling and the words for `015.5`, where D8's `lib/lean/` and the tree disagree about where module proofs live.

## B38. `charter verify` accepts `--require-complete` and `--report-assumptions` and ignores them (`AGENTS.md` "No silent fallbacks", `Law 10`)

- **What happens today (read).** `src/Charter/Cli/Verify.lean`, `parseVerifyArgs`: both flags are consumed and change nothing. `charter explore --require-complete` is real (it sets `requireComplete`). `docs/rfc.md` (line 1401) shows `charter verify --backend smt --report-assumptions test/symbolic/`. Neither flag is in `docs/spec/`, so the `D49` gate does not see them.
- **What the references do.** Quint's CLI rejects unknown options (`.reference/quint/quint/src/cli.ts:488`, yargs `.strict()`).
- **What the spec and mission say.** `AGENTS.md`: "When the tool cannot do something correctly, fail loudly with a diagnostic and a non-zero exit."
- **Mission fit.** `Law 10`. A user who passes `--require-complete` to `verify` believes an inconclusive result will fail the command. It will not, beyond what `verify` already does.
- **Options.** **A.** Delete both from `verify`; passing either is `unknown flag` (exit 2). **B.** Implement them: `--require-complete` turns `INCONCLUSIVE` (exit 3) into a failure (exit 1); `--report-assumptions` prints each certificate's assumptions.
- **Prediction.** A, 75%: exit 3 already distinguishes inconclusive, and `--out json` already carries the assumptions.
- **Needs from Eric.** The ruling.

**`B37` and `B38` ruled (Eric, 2026-11-18): A and A.** `D50`. The `B38` brief was wrong that `--require-complete` is real on `explore`; see `D50` item 6.

---

# Briefs for rulings, 2026-11-18, third batch (`B39`)

**Status:** awaiting ruling (Eric). Nothing below is implemented. Found while listing every parsed flag in `018` for the `D50` gate.

## B39. Four more flags are second spellings or are read by only some of what accepts them (`Law 13`, `AGENTS.md` "No silent fallbacks")

- **What happens today (read in the parsers).**
  - `charter approve --reviewed` sets the same field as `--restamp` (`src/Charter/Cli/Approve.lean:26`). Nothing in `tools/`, `test/`, or `sdk/` passes it. `018` now lists it as "the same as `--restamp`".
  - `charter explore --minimize` sets `minimize := true`, which is the default (`Explore.lean`). Only `--no-minimize` changes anything.
  - `charter verify --invariant <name>` is read by `--backend inductive` only; `finite` and `thresholds` check every invariant and say nothing about the flag. `--time <S>` likewise reaches only the inductive backend's kernel run. `018` now says "`inductive` only" for both.
  - `charter test` has no unknown-flag error: `parseTestArgs` takes any other argument, `--anything` included, as a path (`Test.lean:72`), and reports it as a file it cannot read.
- **What the references do.** Quint's CLI rejects unknown options and has no aliases for these (`.reference/quint/quint/src/cli.ts:488`, `.strict()`).
- **What the spec and mission say.** `Law 13`: one spelling. `AGENTS.md`: "fail loudly with a diagnostic and a non-zero exit."
- **Mission fit.** `Law 13` for the first two; `Law 10` for `--invariant`, where a user who names one invariant under `finite` is told all of them were verified.
- **Options.** **A.** Delete `--reviewed` and `--minimize`; make `--invariant` restrict `finite` and `thresholds` to the named invariants as it does `inductive`, and make `--time` under a backend that has no clock a usage error; make an argument beginning `--` that `test` does not know a usage error. **B.** Delete the two aliases only. **C.** Leave as documented.
- **Prediction.** A, 75%.
- **Needs from Eric.** The ruling.
- **Ruled (Eric, 2026-11-18): A, as predicted.** `D51`.
