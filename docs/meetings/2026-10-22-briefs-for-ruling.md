# Briefs for the eight decisions awaiting Eric's ruling

Date: 2026-10-22. Source: `docs/plans/2026-10-22-redesign.md` §9. Each brief follows the four-part procedure: what the references do (checked in `.reference/`), what the mission says, mission fit, and a committed prediction with confidence. Rulings become D4 onward in `docs/meetings/README.md`; a ruling that matches the prediction can be recorded by an agent, one that differs needs Eric's words.

---

## B1. Literate or code-first files (blocks Phase 1)

**Question.** Is a `.charter` program code that quotes its English (`Clause` blocks), or English that embeds its code (Markdown with fenced blocks)?

**References.** Catala is literate: a `.catala_en` file is Markdown, statute text is prose, code sits in fenced blocks, and article identifiers come from headings (`compiler/surface/lexer_common.ml:31-43`). eFLINT is code with comments; its examples put the contract's prose nowhere (`examples-corpus/`). Quint has an `lmt` extraction path for literate specs but every shipped example is code. Symboleo is code.

**Mission.** Law 8: every norm carries its English, the English leads, a rule with no span is a warning. Law 12: eFLINT programs are Charter programs unchanged. Goal 3: the program "reads as the agreement people sign".

**Fit.** Literate satisfies goal 3 directly and Law 8 most naturally, but breaks Law 12 at the file level (an eFLINT file is not Markdown). Code-first keeps Law 12 trivially and satisfies Law 8 through `Clause` blocks with verbatim checking against `Document "path"`, as v0.3 does. Goal 3's reading is then a projection (`charter render`), which is also what Law 9 wants: one source, projected.

**Prediction.** Code-first `.charter` with `Clause` blocks in Phase 1; a `.charter.md` literate form in Phase 5 that extracts fenced blocks and derives clause ids from headings (Catala's convention) so both spellings lower to the same `Doc`. Law 13 is satisfied because the literate form is a container, not a second grammar. Confidence 85%.

**Reopens if.** The PSA authors find `Clause` blocks unreadable beside the Markdown, or goal 3's signed document cannot be produced faithfully from the code-first form.

---

## B2. Effects of a disabled act (blocks Phase 1)

**Question.** When an act is performed while not enabled, do its effects apply?

**References.** eFLINT applies them and reports a violation; `tests/normative/exp_prohibition.eflint` says "it will still manifest its effects" and `Eval.hs` `consider_transinfos` unions the stores unconditionally. Symboleo's power lifecycle separates `inEffect` from exercise; a power not in effect cannot be exercised at all (`SymboleoPC-library.nuXmv`). Catala has no deontics. Charter v0.3: a power exercised without validity has no effect and the act may still breach a duty.

**Mission.** Law 1: occurrence is never blocked. Law 2: lawful and valid are independent and the tool never collapses them. Law 12: eFLINT semantics unchanged.

**Fit.** eFLINT has two judgments (enabled, effects); the mission wants three (occurred, lawful, valid). The proposal in the plan adds `Valid when` as the third and makes effects conditional on it; an act without `Valid when` is valid always, so eFLINT programs keep eFLINT's behaviour exactly, and Law 12 holds. The alternative (Charter mode defaults to "disabled implies void") makes every eFLINT program mean something different under Charter, which Law 12 forbids.

**Prediction.** `Holds when` = lawful (eFLINT's enabledness), `Valid when` = has effect, default `Valid when True`. A disabled act is reported *occurred, unlawful, valid* unless `Valid when` fails, in which case *occurred, unlawful, void*. Confidence 80%.

**Reopens if.** PSA authors find that nearly every act needs `Valid when` written, in which case the default may be reconsidered for a `Charter` file header mode, with the eFLINT corpus pinned to the old default.

---

## B3. Stratified negation (blocks Phase 1)

**Question.** eFLINT's derivation is an inflationary fixpoint that evaluates negation against intermediate states, so results can depend on the alphabetical order of types (`Saturation.hs`). Do we reject programs whose negation is not stratifiable, or adopt stable-model semantics and report multiple models?

**References.** eFLINT's own GPCE'25 paper moves to stable-model semantics with model checking of scenarios. InstAL (not vendored) is answer-set based and lives with multiple models. Catala's default calculus has explicit priorities and makes "conflict" and "empty" first-class errors rather than picking an order. Quint has no derivation.

**Mission.** Law 9: one definition, proved. Law 10: decided scenarios depend on no axioms. Law 6: the program can say where every fact came from.

**Fit.** A unique stratified fixpoint is provable in Lean with structural recursion and gives every derived fact one origin (Law 6). Stable models give a set of worlds, which Law 6's "where did this fact come from" cannot answer with one chain, and whose existence proofs are harder to make kernel-decidable. Rejection with a diagnostic is Catala's "fail loudly" shape.

**Prediction.** Stratify; reject unstratifiable negation with `CHR` diagnostic naming the cycle; document the difference from eFLINT 4 as the first entry in the tolerance file. Confidence 85%.

**Reopens if.** A PSA clause genuinely needs non-stratified negation, or the vendored corpus has more than a handful of programs that stop passing.

---

## B4. Time granularity (blocks Phase 2)

**Question.** Is time an `Int` tick, or distinct `Time` and `Duration` types over `Int`?

**References.** Catala has `date` and `duration` as distinct types with explicit rounding and type-suffixed operators (`+^`), and makes ambiguous date arithmetic a runtime error. eFLINT lexes `Time` as a type but never advances it (`State.time`, `increment_time` unused). Quint has no time; Symboleo has `TimeGranularity` and a `Timer` module.

**Mission.** Law 7: time is state; facts carry stamps; conditions compare stamps. Law 13: one spelling. Goal 1: every deadline in the PSA.

**Fit.** The PSA's windows are all integer ticks today, so `Int` suffices for goal 1 at v1. Distinct types cost nothing now and prevent `noticeWindow + agentId` from typechecking; they also leave a calendar chapter as an extension rather than a migration. Catala's experience is that mixing durations and instants silently is the common bug.

**Prediction.** `Time` (instants) and `Duration` (differences) as distinct types over `Int`; `Time + Duration : Time`, `Time - Time : Duration`, no `Time + Time`; `Current Time : Time`; literal `10` coerces to either by demand. Calendars deferred. Confidence 75%.

**Reopens if.** The distinction produces ceremony in the PSA (casts in more than a handful of places).

---

## B5. Who owns the standard-library module theorems (blocks Phase 2)

**Question.** The eight modules (`ResidualLedger` … `OracleFeed`) have kernel-proved invariants in Lean. When each becomes a `.charter` module under `lib/`, do its theorems stay in Lean under `lib/lean/`, or must every module property be an `Invariant` in the `.charter` file that `charter prove` discharges?

**References.** Catala's stdlib is Catala source with native escape hatches per backend (`stdlib/`, `> Module X external`); its proof plugin checks properties of user scopes, not library theorems. Quint's `builtin.qnt` is documented from source, with no proofs. Veil (not vendored) attaches theorems to actions in the same file.

**Mission.** Law 11: the author never sees Lean. Law 10: every claim carries a tag. Goal 2: nothing in the language names an institution. Law 9: no projection whose faithfulness is tested rather than proved.

**Fit.** Module authors are Charter maintainers, not program authors, so Law 11 does not forbid Lean in `lib/lean/`. But a library property the author cannot see in the `.charter` module is invisible to `check` and `prove`, and cannot be cited by a program's `Invariant`. The honest split: every module property is declared as an `Invariant` in the `.charter` module so it is data and visible (Law 5), and its proof lives in `lib/lean/` attached by name, reported as *proved* when the program uses the module. Properties `prove` can discharge by itself need no Lean file.

**Prediction.** Declared in `.charter`, proved in `lib/lean/` by name, tagged *proved*; `charter prove` on a program that `Use`s a module cites the module theorem rather than re-proving it. Confidence 80%.

**Reopens if.** The theorem-to-invariant name binding proves fragile across module parameterization.

---

## B6. Managed Lean toolchain for `prove` (blocks Phase 4, decide before Phase 3 planning)

**Question.** Does the `charter` binary download and manage its own Lean toolchain for `prove`, or require `elan` on PATH?

**References.** With carries Clang, lld, CMake, and a sysroot inside the compiler (`README.md` "Linking uses the lld inside the compiler"; Law 8 "the toolchain absorbs the environment"). Quint downloads a pinned Apalache and needs a JDK (`docs/content/docs/model-checkers.mdx`). Catala requires an opam switch.

**Mission.** Law 11: no path or flag shown to an author names Lean. Goal 2: a universal language cannot require a proof assistant of its authors.

**Fit.** "Install elan" is a Lean-named instruction, which Law 11 forbids. With's rule applies directly: the toolchain absorbs the environment within a boundary. The boundary here is: `prove` fetches a pinned toolchain into `~/.charter/toolchains/<digest>/` on first use, verified against `tools/pins.lock`, with an offline flag that fails loudly.

**Prediction.** Managed download, pinned by digest, first use only, `--offline` refuses rather than searches PATH. Confidence 85%.

**Reopens if.** Download size or first-use latency makes `prove` unusable in CI for program authors, in which case a `charter prove --toolchain <dir>` escape that still never names Lean in its help text.

---

## B7. Retention of the PSA world-state models (decide at end of Phase 3)

**Question.** The Lean companion has `ProtocolWorldState` (13 quantitative fields) and 16 adversarial simulations. After the PSA is rewritten with `Int` facts, which simulations remain Lean-only, and does goal 1 ("nothing of the protocol lives only in a proof assistant") tolerate any?

**References.** eFLINT models quantities as `Int` facts with aggregates (`auction/case-assessment.eflint`); nothing lives outside the program. Quint's state is all in the spec; the implementation is tested against it, never the reverse. Catala's `external` modules are the exception that proves the rule: an escape hatch, declared in the program.

**Mission.** Goal 1, verbatim. Law 10: a *proved* tag for things proved in Lean. Law 13: one spelling.

**Fit.** The strict reading of goal 1 is that a simulation only Lean can run is a defect, to be removed by making the language able to say it (goal 1 "is added and then generalized, not refused"). The practical reading is that `Int` facts plus aggregates cover ledgers, bonds, and fee pools, and the residue is likely the affiliation graph and sortition draws, which are substrate, not protocol.

**Prediction.** v1.0 ships only when all 16 run through the evaluator; any residue is a language feature request filed before Phase 3 ends, not a retained Lean model. Confidence 60%, the lowest here, because it is a scope commitment Eric may not want to make before seeing the residue.

**Reopens if.** The residue is a substrate assumption (SUB.01) rather than a protocol rule, in which case it is declared *assumed* in the program and the Lean proof is cited by name as in B5.

---

## B8. Rule amendment inside a program (blocks Phase 3)

**Question.** Parameter amendment is an act creating a new instance of a `Var` fact. Rule amendment (adding a duty, weakening a protection) is, in eFLINT, an `Extend` phrase in the scenario. Is `Extend` enough for the PSA's Law 7, whose bilateral ratchet says which rule changes are valid and which parties must consent, or does Charter need an `Amend` act whose effect is a rule change that the evaluator judges for validity like any other effect?

**References.** eFLINT: `Extend` is a scenario phrase, recompiled against the spec, with no actor, no validity, no violation (`StaticEval.compile_ext`); re-declaration silently replaces. Catala: no runtime amendment; versions are separate texts with `[archive]` headings. Quint: no amendment; instances are configurations. Symboleo: contract-level `sTermination`/`unsTermination`, no rule change.

**Mission.** Goal 1: "an amendment is an event the program judges like any other." Law 1: occurrence never blocked, so an invalid amendment must be performable and void. Law 2: its validity is a separate answer. Law 5: rules are data, so a rule change is a change to a record, which is representable.

**Fit.** `Extend` fails goal 1 three ways: it has no actor, it cannot be invalid, and it cannot be refused by an immunity. Law 5 makes the alternative natural: an `Amend` act whose `Creates`/`Terminates` operate on rule records (add duty D, remove power P, set parameter n), subject to `Valid when` (consent facts, timelock stamps) and to immunities (`I.NO_WEAKENING Against Amend`). `charter diff` then compares the rule set before and after the act. `Extend` stays as the scenario-time, environment-level mechanism it is in eFLINT (Law 12).

**Prediction.** Add `Amend` acts in Phase 3 with rule records as effect targets; keep `Extend` as environment input; ratchets are `Invariant`s over the rule set and parameter facts. The universal ratchet theorem (`Charter.Core.Ratchet`) is restated as: every valid `Amend` trajectory preserves every `Invariant` tagged `Entrenched`. Confidence 70%.

**Reopens if.** Rule records as effect targets make the evaluator's agreement proof (Law 9) materially harder, in which case v1 ships parameter amendment as acts and rule amendment as `Extend` with a decision naming the gap against goal 1.
