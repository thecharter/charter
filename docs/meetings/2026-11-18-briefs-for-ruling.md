# Briefs for rulings, 2026-11-18 (`B34`–`B36`)

**Status:** awaiting ruling (Eric). Nothing below is implemented. Each arose while fixing the red CI lane (`D45`); `B34` is also the first design point of an outside review of the repository received the same day.

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

## B36. `charter verify --backend smt` runs the solver and does not read its answer; the emitted encoding constrains nothing (`D20`, `T30`, `Law 10`)

- **What happens today (run, not read).** `Verify.Smt.checkBounded` writes `TVIR.emitSmtLib2`, runs `z3` on it, and on any answer sets the label to `z3+native-replay` (`src/Charter/Verify/Smt.lean`, `| some _ => solverLabel := …`). The verdict comes from `Verify.search` over a threshold menu. The encoding for `test/verify/t30_smt_symbolic_int.charter` declares one `Bool` per type and asserts `(or (not (not true)))`: `z3` answers `sat` at depth 1, 2, and 3, while Charter reports safe at depth 1 and violated at 2 and 3. The CI step that "exercised" this ran a fixture that does not exist (`t30_smt_symbolic_threshold.charter`) under `|| true`; it now runs the real fixture and says in a comment what it does not check.
- **What the spec and claims say.** `docs/claims.json` (`project.emitted_targets_differential_checked`): "… and CI solc/Foundry + quint + z3 execution". Output label: `smt/z3+native-replay`.
- **Mission fit.** `Law 10`: the label tells the user a solver took part in the verdict. It did not.
- **Options.** **A.** Label the backend for what it is (threshold-menu search with native replay), stop invoking the solver, and keep `--emit-smt` off until the encoding means something. **B.** Write the bounded encoding over the guard IR (arrays for facts keyed by integers) and make the verdict the conjunction of the solver's answer and the replay.
- **Prediction.** A now, 70%; B is its own work package.
- **Needs from Eric.** The ruling.
- **Ruled (Eric, 2026-11-18): A, sharpened.** The backend is renamed `thresholds`, `--backend smt` is refused, and the solver code and flags are deleted; B has an exit criterion. `D47`.
