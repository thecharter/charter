# HANDOFF — Charter

Reverse-chronological. Newest section first. Verify every hash below with `git log`
before acting on it. The rules are `AGENTS.md`; read it before this file.

---

# Handoff — 2026-11-08 (2): remaining 10 bugs & diagnostics closed (`#80`, `#19`, `#20`, `#24`, `#27`–`#29`, `#31`, `#33`, `#34`) and all 20 worked `Examples/` rewritten in `D34`–`D38` Charter

## Where

- `main`, pushed in atomic, battery-green commits (`5a6b8a4`, `3939564`, `601338b`, plus the 20-example `D34`–`D38` rewrite).
- `tools/battery`: **PASS** across all 25 steps (zero build warnings across 187 jobs, 202/202 spec conformance fixtures, 13/13 stdlib suites, 4/4 zero-axiom `prove`, 14/14 `verify`, 196/196 eFLINT corpus, 20/20 worked examples, and `spec-inventory` checking all AST + comment-preserving `fmt` round-trips); `/Users/eric/psa/tools/verify-psa`: **PASS** across all 6 stages.
- Tracking issue `#79`: **62 closed / 16 open** (every bug, wrong-answer defect, diagnostic issue, language ergonomics proposal, and stdlib-provenance item is now closed; only layout/LSP views `#63`, `#64`, `#72`, proof/projection/service items `#65`–`#71`, `#73`, and PSA-scale items `#74`–`#78` remain).

## What landed

1. **Remaining wrong-answer, checker & loader fixes (`5a6b8a4` + `Derivation.lean` `Done`/`Since` stratification fix)**:
   - **`#80` (`spec_004_12b`)**: bounded Kleene conflict-taint overlay in `Eval.evalTermTri` and `Eval.evalActTri` (preserving two-valued `Saturate` and all fixpoint theorems untouched while propagating `undetermined` through intermediate derived facts reading conflicted `Default`/`Exception` premises positively or negatively; explicit assignments override per `004.3`).
   - **`#19` (`spec_004_12c`)**: `DefeasibleRule.freeVars` binds free `Param` and fact variables jointly across `Yields <val> When <cond>` on `Function` and `Var` (including 1-product `Var` domains and `Extend Var`/`Function`/`Bool`/`Role`), fixes non-product self-dependency in `Stratify.typeDeps`, and checks `Stratify.strata` (`CHR020`) in `charter check`.
   - **`#20` (`spec_011_7b`)**: canonicalizes `#require` paths via `IO.FS.realPath` so cyclic/back-referenced article files load at most once regardless of relative path spelling.
   - **`#24` (`spec_012_6b`)**: includes rules declared inside `Amend ... Installs { ... }` in `Spec.ruleIds`, `citeableIds`, `fromSpans`, and `clauseRulesDigest`.
   - **Compiler fixes uncovered by the 20-example rewrite**: `Decides <fact> When <cond>` parses `<fact>` at `orExpr` so `When` is not swallowed (`Parser.lean`), and `Stratify.deps` treats `Done(act)` / `Since(act)` on triggerable `Act`/`Event`s as state `$occ` lookups rather than derived-fact dependencies (`Derivation.lean`).
2. **Source spans, block recovery, claim locations & parser diagnostics (`3939564`)**:
   - **`#27`**: `Decl.atPos`, `ModClause.atPos`, and `Resolve.withPos` anchor resolve diagnostics to the exact offending declaration or clause `line:col` while stripping positions before `CIR` (`TypeSpec`).
   - **`#28`**: `recoverPhraseDecls` preserves sibling declarations across failed blocks in `check` and `lsp` and suppresses cascaded `CHR010`s in `test` and `run`.
   - **`#29`**: `Item.subPos` tracks per-phrase positions inside `Scenario` (including `Scenario ... After`), reporting each failing claim's own `line:col` and isolated claim text.
   - **`#34` (`spec_004_12d`, `spec_011_11c`)**: clear `CHR003` when `Default`/`Exception` omits its rule name, digit-suffixed `Scenario` names (`t1`, `t2`), and optional `.` after standalone `Document "..."` before `#require`/`#include`.
3. **`charter fmt` & `charter check` UX (`601338b`)**:
   - **`#31`**: `Pretty.formatSourceAndVerify` preserves `//` and `/* ... */` comments, single blank lines, end-of-line comment alignment, and author line breaks while normalizing spacing and verifying AST round-trips; `Pretty.fmtTermPrec` (`--canonical`) emits minimal precedence-aware parentheses with zero duplicate `Text` lines. `charter fmt --check` passes across all `Examples/`.
   - **`#33`**: `charter check` prints only failures/warnings and the summary line by default (`--verbose` prints all passing checks), flushes stdout/stderr to prevent mid-line interleaving, and `charter test` reports `failed provenance check(s)` separately from `failed claim(s)`.
4. **All 20 worked `Examples/` rewritten in idiomatic `D34`–`D38` Charter (`git diff Examples/*/*.md` empty)**:
   - Retyped clause English: `24,814` chars → **`0` chars** (`-100%`, heading/paragraph/sentence `Clause <ID>` extraction).
   - Inline `Approved` digests: `14,325` chars → **`0` chars** (`-100%`, rule-aware `charter.lock` via `charter approve --lock`).
   - Total spec lines (rules + clauses): `1,776` → **`1,470`** (`-306` lines, `-17.2%`); unlinked spans `33` → **`0`**; repeated `Power` conditions `20` → **`4`** (`-80%`); `x == Name` comparisons `54` → **`17`** (`-69%`, zero party checks); empty `f()` applications `414` → **`14`** (`-97%`).

---

# Handoff — 2026-11-08: all 27 ergonomics proposals (`#35`–`#61`) + stdlib provenance (`#62`) implemented (`D34`–`D38`)

## Where

- `main`, pushed across five atomic, battery-green commits (`D34`–`D38`).
- `tools/battery`: **PASS** across all 25 steps (195 spec conformance tests, 13 standard-library suites over 15 modules, 4/4 zero-axiom `prove`, 14/14 `verify`, 196/196 eFLINT corpus, 20/20 worked examples); `/Users/eric/psa/tools/verify-psa`: **PASS** across all 6 stages.
- All 18 runnable defect reproductions (`01`–`18`) and all 28 language ergonomics / stdlib-provenance issues (`#35`–`#62`) are now resolved and closed.

## What landed (`D34`–`D38`)

- **`D34` (`7795f8c`)**: `Clause <ID> => ...` heading/sentence extraction by reference (`#35`), `charter approve [--lock]` rule-aware `charter.lock` approvals (`#23`, `#31`, `#32`), spans citing `Fact`/`Param`/`Event`/`Default`/`Exception` + ground initializers (`#36`), template `{param}` blanks (`#59`), and `Use ... From <CLAUSE>` stdlib provenance + `lib/{debt,ballot,succession}.charter` (`#62`).
- **`D35` (`da95b30`)**: `Power` `Holds when` defaults to `Valid when` (`#37`), `Valid when` comma rejection (`#38`), `Prohibited`/`Forbidden when`/`Void when` (`#51`), `Protection` dual of `Immunity` (`#52`), `Presumed` & `Decides` (`#53`), `Amend Procedure` & `Protects Clause` (`#54`), `Input Fact` (`#55`), Duty `Overrides` & `Excused when` (`#57`), `Qualifies as` (`#60`), and `CHR032`/`CHR041`/`CHR042` (`#13`, `#15`, `#26`).
- **`D36` (`773ae72`)**: `Role`s (`Is`, `Where`, `First of ... Unless` succession, fixed claimants), status-fact actors, `(Forall|Exists) ... Except`, `Duration %` (`#39`, `#40`), `Var` enumeration fix (`#14`), `f(k)` `Function` lookup, `Count(pred)`, `Amount`, `Decided by` ballots, bare `Bool`, multi-name powers, single-party duties (`#46`, `#50`, `#61`), and `Scenario ... After` / `Let` / singleton `Role` elision (`#41`).
- **`D37` (`1679283`)**: `$10,000.00` money literals, `: USD`/`Rate` shorthands, `Var ... = init` (`#42`), `6%` & `bps` rates (`#58`), `010.4` dimensional ratios (`#22`), `Share` & `ProRata` with required `Remainder To` (`#56`), `If` & 2-arg `Min`/`Max`, `Debt` with independent per-raising deadlines (`#45`, `#17`), and `Applies ... To` waterfalls.
- **`D38` (`HEAD`)**: `Done(e)` & `?occurred` (`#49`), `Since`/`Age`/`Overdue`/`Before`/`Within ... Of`/`At` (`#43`), `Grace` & `?late` + `Due within ... After` (`#44`), exact clock-threshold stamps (`#16`), `Every <period>` recurring duties & `On breach Creates` (`#47`), and ISO `YYYY-MM-DD` civil calendar + `days`/`weeks` + `Year`/`Month`/`Day`/`Weekday`/`AddMonths`/`AddYears` (`#48`).

---

# Handoff — 2026-11-07 (3): remaining six of the eleven accepted-and-wrong defects fixed (`D30`–`D33`)

## Where

- `main`, pushed (`tools/battery`: PASS across all 25 steps; `/Users/eric/psa/tools/verify-psa`: PASS across all 6 stages).
- All eleven of the initial silent wrong-answer defects (`#2`–`#12`) are now fixed and closed.

## What landed (`D30`–`D33`, `B13`–`B16`)

- **`D30` (`B13`, #6)**: `charter test` now checks every declared `Invariant` at the end state of the program and of each `Scenario` (unless `?!inv().` claims the breach), aligning `test` with `explore` and `prove` (`011.10`, `spec_011_10b`). All 6 library tests with mid-genesis violations were verified individually to cure before genesis ends; 7 upstream eFLINT corpus files ending in breach are recorded in `tolerances.json` / `tolerances.md` (39 total tolerances).
- **`D31` (`B14`, #9)**: two-valued derivation, violation, and immunity rules may no longer read an `Evidenced` fact bare (`CHR038`, `004.11`, `spec_004_11b`, `spec_004_11c`); `RentersInsurance`, `BillOfSale`, and `psa.charter` updated to `Established(…)`. Separate `004.12` normative conflict leakage through intermediate derived facts filed as `#80` with the bounded taint-overlay route.
- **`D32` (`B15`, #11, plus #3 & #8)**: effects reading an unset `Var` (other than bare `Terminates v` / `Obfuscates v`) or an implicitly bound `Function` at an unassigned key argument halt with `CHR100` (`MissingInput.unassignedVar` / `unassignedFunction`, `005.4`, `spec_005_4b`, `spec_005_4c`, 0 eFLINT corpus divergences). Added `CHR039` warning on unfiltered `Count(Foreach x: f(x))` (`010.7`, `spec_010_7b`) and `CHR040` warning on binders over empty carrier types (`004.7`, `spec_004_7c`), which caught and fixed real vacuous binders in `Examples/Deed`, `Examples/TreasuryMandate`, `lib/monetary_estate.charter`, and `lib/agency_mandate.charter`.
- **`D33` (`B16`, #12)**: evidence is keyed by `(fact, polarity, source)` defaulting to the performing actor with `By s` override (`005.11`, `spec_005_11b`), `Retracts !e` withdraws contrary evidence, and retractions matching nothing emit warning `CHR109` (`spec_005_11c`).

---

# Handoff — 2026-11-07 (2): five of the eleven accepted-and-wrong defects fixed (D29)

## Where

- `main`, pushed: five fix commits and their docs. `tools/battery`: PASS (25 steps) at the
  head of the series; the intermediate commits were not run through it one by one.

## What landed

- **#5** `Held(e) For d` now counts as a read of `e` in stratification (`Core/Derivation.lean`,
  one line). Fixture `spec_004_6d`.
- **#2** An application that gives two different arguments to a component named twice is CHR036.
  The declaration stays legal: `Holder actor Claimant actor` is used on purpose. Fixture `spec_003_3c`.
- **#7** A bare literal is not a phrase (CHR012), which is what let `10000.00.` pass. Fixture `spec_011_2b`.
- **#10** A `Param` inside `Installs { }` is CHR037. Fixture `spec_014_3c`.
- **#4** An act performed by an element outside its domain is not valid, in both evaluators
  (`Eval/Eval.lean`). Fixture `spec_005_9d`. A `+fact(Outside)` is still dropped silently.
- Decision record `docs/meetings/2026-11-07-D29-…`; four spec sentences drafted (003.3, 004.6,
  005.9, 011.2, 014.3) for Eric's review.

## Two things learned the hard way

- Refusing digits-dot-digits in the lexer broke thirteen examples: `Clause 1.1` is that shape.
- A static check must be structural. `reprStr` in `compileArguments` made `charter prove`
  disagree with the evaluator, because the kernel re-runs resolution and cannot reduce `Repr`.

## Open (of the eleven)

#3 count of a constructor, #6 `test` passes with a violated invariant, #8 binder over a money
type, #9 evidence through a derived fact, #11 unset `Var`, #12 `Retracts`. #6, #9, #11 and #12
change specified behaviour and need a ruling; #3 and #8 are warnings to add.

---

# Handoff — 2026-11-07: twenty worked examples and what they cost to write

## Where

- `main`, pushed in three commits (the loader fix; the examples with their check; the findings).
  `tools/battery`: PASS, all steps, including the new `worked-examples` step (20 examples, 20 roots,
  20 case files).

## What changed

- **`Examples/`**: twenty new agreements in a root-and-cases layout (`Examples/README.md`): will,
  living trust, deed, power of attorney, healthcare directive, prenup, parenting plan, home
  purchase, promissory note, guaranty, bill of sale, employment, NDA, return policy, settlement,
  renters insurance, roommates, homeowners' association, LLC operating agreement, club bylaws.
  Five are split by article. 191 clauses, 166 scenarios. The English is original and fictional.
  The clause approvals were stamped by the authors of the examples and await Eric's review.
- **Loader fix** (`src/Charter/Cli/Load.lean`): a `Document` path is now resolved against the
  file that declares it, so `cases/x.charter` requiring `../root.charter` finds the document.
  Fixture `test/spec/spec_012_1b_document_relative_to_declaring_file.charter`, seen failing first.
  Spec 012.1 says "relative to the program's file"; the wording is Eric's to confirm.
- **Tools**: `tools/examples-check` (in the battery as step 13), `tools/examples-metrics`,
  `tools/approve-clauses` (stands in for a missing `charter approve`).
- **Findings**: `docs/plans/2026-11-07-example-friction/` (ranked proposals, per-example notes,
  twelve runnable defect reproductions). Nothing in it is ruled.

## Open

- Every finding is filed: 77 issues, tracked in thecharter/charter#79. The accepted-and-wrong
  defects have reproductions that pass today and fail when fixed
  (`docs/plans/2026-11-07-example-friction/reproductions/`).
- The proposals reopen D4 (clause blocks) and D5 (`Valid when` default) on those decisions' own
  "reopens if" conditions, and one touches Law 7. Each needs a brief and a ruling.
- `docs/reference/open-letter.{md,pdf}` (the letter to van Binsbergen) is deliberately not
  committed (Eric, 2026-11-07).

---

# Handoff — 2026-11-06 (2): Charter 1.0 Gates `G0`–`G5` Complete (`D17`–`D28`, `T01`–`T49`)

## Where

- `main`, pushed directly in atomic fast-forward commits (`05b6635` → `fa7d06a` + this `G5.3`–`G5.5` exit commit). `tools/battery`: PASS across all 23 steps (zero build warnings across 183 jobs, all 13 Law-14 gates green, 46 backed assurance claims, 196/196 unified eFLINT corpus without `--eflint`, 155/155 spec conformance tests, 12/12 standard-library modules, zero-axiom `charter prove`, `verify`, `server`, `projections`, `g5-product`, and 4 in-tree examples).

## What landed across Gates `G0`–`G5`

- **Gate `G0` (`efe5c01`–`5c8c6ff`, `D17`)**: retired Phase-0 linked Lean companions (`D10`, `g0-independence.sh`), unified `.charter`/`.eflint` contextual keyword parser (196/196 upstream eFLINT corpus passes without `--eflint`, `tolerances.json`), opt-in static assurance gates (`CHR029`–`CHR031`), `docs/trust.md`, `docs/assurance-levels.md`, and `docs/claims.json` (`claims-backed.sh`).
- **Gate `G1` (`0703f08`–`edec4ba`, `D18`–`D19`)**: normative grammar (`019`, `020`), `charter fmt` (`spec-inventory.sh`), `CIR` epochs + `Spec.WellFormed` + kernel-verified SHA-256, Tarski least pre-fixpoint (`saturateStratum_least_prefixpoint`), `DeclPhraseStep` correspondence (`evalPhrase_sound`, `evalPhrase_complete`, `replay_trace_deterministic`, `frame_preservation_unrestricted`, `mutant-eval-check.sh`), `SymbolTable` interning (`T42`), and structured `ClaimCertificate` (`T44`).
- **Gate `G2` (`a9ea89d`–`1aff3e3`, `D20`)**: `lawful`/`adversarial`/`mixed` native explorer + counterexample minimization + proved disjoint-store POR (`T28`, `T29`), temporal `Property` syntax + fairness-gated liveness (`T26`, `T27`, `T31`), `TVIR`/SMT bounded model checker with native `Eval` counterexample replay (`T30`), and `charter verify`.
- **Gate `G3` (`5f65ce9`–`32e340a`, `D21`–`D26`)**:
  - `G3.1`: `Power` competence check (`CHR032`, `wellFormed_power_has_validWhen`), multi-document `Document [ID] "path" [SHA256 "..."] [Rank n]`, SHA-256 clause approvals, Markdown anchors, and `complete | partial | illustrative` provenance coverage (`T08`, `T37`, `T39`).
  - `G3.2`: 4-valued `Evidenced` facts (`Established | Refuted | Unresolved | Conflicted`), institutional `Finding` acts (`Law 3`), Kleene 3-valued `TriBool` guard propagation (`T06`, `T07`), `charter explain` over `ReasonGraph` with proved verdict-preserving audience redaction (`redactForAudience_preserves_verdict`, `T43`), advisory `Note` irrelevance (`advisory_note_irrelevant`, `T04`), and `charter test --metamorphic` (`T05`).
  - `G3.3`: Catala-style `Default` / `Exception ... Overrides` / `Priority ... Over` calculus (`Fact`/`Bool` + `Yields ... When` on `Function`/`Var`), static cycle rejection (`CHR034`), explicit normative `Conflict` (`T21`), and proved `evalCompiledDAG_eq_spec` (`T22`).
  - `G3.4`: static dimensional `Money(CUR, SCALE)` & `Quantity(UNIT)` over exact `Int` minor units and proved `MulDivRound` (`Floor`, `Ceil`, `NearestEven`, `ExactOrReject`, `CHR108`, `T10`, `T11`).
  - `G3.5`: rule-level `Amend` (`Repeals` / `Installs`), reflexive `Immunity ... Against Amend` ratchet proof (`cir_ratchet_trajectory_preserves_entrenched`, `T23`, `T24`), `Regime` overlays, 3-view `charter diff` (`T38`), and `D11` gates (`amend-is-an-act`, `amend-reflexive`, `extend-never-at-runtime`).
  - `G3.6`–`G3.7`: standard-library `contract_lifecycle`, `agency_mandate`, `monetary_estate`, and `jurisdiction` modules (`D8`, `LegalOntologies.lean`), plus `Examples/TreasuryMandate` across Traces A–F (30/30 claims & invariants decided in the kernel with zero axioms).
- **Gate `G4` (`effc39f`, `D27`, resolves `B10`)**: pure-Lean RFC 2104 HMAC-SHA256 (`hmacSha256_rfc4231_vector`) signed `.artifact` bundles, standalone operator-blind `charter-server` executable (`operator-blind.sh` verifying zero `Surface`/`Resolve`/`Prove` modules or symbols), hash-chained durable JSONL log + canonical `computeStateRoot` + offline `replay` (`replay.sh`, `T36`), `certificate-at-office.sh`, and `Reserve` → `Authorize` → `ConfirmExecution` / `ExecutedUnknown` saga + MCP/JSON-RPC API (`T09`, `T34`, `T35`, `T43`).
- **Gate `G5` (`fa7d06a` + this commit, `D28`)**: live `CIR` `charter generate --target solidity|abi|quint|prompt` (`CHR035`, `cir_guard_step_correspondence`, `T32`, `T33`), `charter lsp` + Tree-sitter/VS Code grammars, `charter doc`, `charter init` (`charter.toml` + `charter.lock`), `charter doctor`, TypeScript/Python/Rust SDKs (`sdk/`), and the 9-institution competitive benchmark suite (`benchmarks/`, `docs/benchmarks.md`, `docs/migrations.md`).

---

# Handoff — 2026-11-06: Kernel-unfoldable radix indexing (`DomMap`), `--scenario` filtering, and `CHR028`

## Where

- `main`, pushed directly alongside `thecharter/psa` (`~/psa`: 98 clauses, 765 declared types, 16 `Invariant`s, 24 `Scenario`s). `tools/battery`: PASS (all 12 steps green; `spec-conformance` 131/131).

## What landed in `~/charter`

- **Pure-structural 8-bit radix indexing (`DomMap`) & saturation fast-paths** (`Core/Spec.lean`, `Core/State.lean`, `Eval/Eval.lean`, `Eval/Interpreter.lean`, `Eval/Properties.lean`): replaces linear scans of `Spec.decls` and `State.entries` in `Eval` and `Saturate` with transient structural radix tries (`SpecIndex` / `StateIndex`) inside `Eval.Ctx` (leaving `Spec` and `State` `Repr` output unchanged for `Prove.LeanGen`), linearizes `M.bind` via `mapM` + `List.flatten`, skips `withSubs` on `True` domain constraints and empty `conditions`, and evaluates `.holdsWhen` guards before constructing product tuples on unconstrained domains. Cuts full `charter test ~/psa/psa.charter` runtime from 222.6s to 75.7s (3.0x speedup) with zero new axioms in `Eval/Properties.lean`.
- **`--scenario <name>` filter on `charter run` and `charter test`** (`Cli/Run.lean`, `Cli/Test.lean`, `docs/spec/018_toolchain_and_cli.md`, `test/spec/spec_018_2_scenario_filter.charter`): repeatable `--scenario <name>` executes top-level declarations/genesis plus only the named scenario(s) (~3.8s on `psa.charter`), failing loudly with `CHR003` on unknown scenario names.
- **`CHR028` warning on vacuous enumerable quantifiers** (`Resolve/Static.lean`, `docs/spec/010_expressions.md`, `docs/spec/diagnostics.md`, `test/spec/spec_010_6b_vacuous_enumerable_exists.eflint`): warns when `(Exists x: True/False)` or `(Forall x: True/False)` binds an enumerable type, catching the Cartesian-domain vs. holding-instance trap (`Exists f: f`) statically.

---

# Handoff — 2026-11-04: Pure-Charter PSA separation (`~/psa/psa.charter`) and language fixes

## Where

- `main`, pushed directly alongside standalone protocol repository `thecharter/psa` (`~/psa`: `psa.md`, `psa.charter`, `README.md`). `tools/battery`: PASS (all 12 steps green; `spec-conformance` 129/129).
- `~/psa/psa.charter` formalizes the full Protocol of Sovereign Agency (78 clauses, Laws 1–7, 14 `Invariant`s, 17 `Scenario`s covering all 16 Adversarial Tests + Law 7 governance) in pure Charter with zero Lean shadow models; `charter check ~/psa/psa.charter` and `charter test ~/psa/psa.charter` both pass with 0 errors and 0 failed claims.

## What landed in `~/charter`

- **`.charter` source support & external-workspace CLI discovery** (`Cli/Load.lean`, `Cli/Test.lean`, `Cli/Prove.lean`, `Tooling/Cli.lean`, `docs/spec/018_toolchain_and_cli.md`, `test/spec/spec_018_1_charter_extension.charter`): eFLINT-superset `.charter` files work across `check`, `run`, `test`, `trace`, `prove`, and `repl` (keeping a header guard for the two legacy v0.3 `.charter` files); `locateCharterRoot` falls back to `IO.appPath` when invoked outside `~/charter`; `charter prove` passes `--root` to `lean` for external workspaces.
- **Verbatim `From` provenance on `Invariant`, `Predicate`, and `Scenario`** (`Surface/Ast.lean`, `Surface/Parser.lean`, `Resolve/Static.lean`, `Core/Spec.lean`, `Prove/Run.lean`, `Prove/LeanGen.lean`, `Cli/Provenance.lean`, `docs/spec/011_phrases_and_scenarios.md`, `docs/spec/012_clauses_and_provenance.md`, `test/spec/spec_012_3b_invariant_from.eflint`, `test/spec/spec_012_3c_scenario_from.eflint`): `Invariant`/`Predicate` declarations and `Scenario` headers accept `From CLAUSE "span"` checked verbatim against `Clause` `Invariant`/`Acceptance` spans, and `check` resolves `Scenario` bodies inside `withSpec`.
- **`Immunity ... Related to` scoping & judged non-enumerable immunities** (`Core/Spec.lean`, `Eval/Eval.lean`, `docs/spec/007_immunities_and_exceptions.md`, `test/spec/spec_007_4d_immunity_related_to.eflint`): `Spec.judgedRule` judges `Holds when` per instance for non-enumerable `Act`s and `Immunity`s without materializing infinite domains, and `immunityBlocks` matches shared `Related to` components between the immunity and the act.
- **Integer literal coercion for `Time`/`Duration` product components** (`Resolve/Static.lean`, `docs/spec/009_time.md`, `test/spec/spec_009_2h_product_time_literal.eflint`): `convertTerm` coerces integer literals to `.time`/`.duration`-backed domain wrappers inside product constructors (e.g. `lineage-sunset(Lin1, 100)`).
- **Interpreter & state lookup fast-paths** (`Core/State.lean`, `Eval/Eval.lean`, `Eval/Interpreter.lean`, `Cli/Run.lean`): `State.trueInstances` avoids dual-list filtering on closed non-enumerable domains; `runPhrase` skips `Stratify.strata` on non-declaration phrases and skips `Saturate.rebaseAndSat` on pure read/query phrases while still checking invariants; `testMode` suppresses clock-set noise and labels failed scenario queries clearly.

---

# Handoff — 2026-10-25 (2): Phase 2's exit criteria; Phase 1's remaining proofs

## Where

- `main`, pushed directly, one commit per slice: 007.3 (`bf08db6`), `Examples/Tenancy`
  (`51cfff5`), the commons in Charter (`ab30684`), then Law 3 and the evaluator proofs
  (this section's commit). `tools/battery`: PASS before every push; it now has twelve steps, the new
  one `examples` (`charter test` on the tenancy, the commons and Law 3).
- Eric's instruction: "complete phase 1 and 2". Phase 2's features and exit criteria are
  done (below); Phase 1's exit item, the evaluator's agreement proof with a declarative
  semantics, is **not**: the declarative semantics does not exist yet. What was provable
  without it landed in `Eval/Properties.lean` and is listed honestly as properties of the
  evaluator, not as that proof.

## What landed

- **007.3 duty precedence**: `Duty d … Overridden by d'`; an instance of `d` is not
  violated while an instance of `d'` holds that shares the components the two duties
  have in common (by name, as `Except under` shares them); declared, one level deep.
  CHR026 for a non-duty. `evalViolationCondition` consults it, so the query and the
  once-only report (D12) agree. This draft's lift of v0.3's state-level precedence to
  instances awaits Eric's wording (spec 007).
- **`Examples/Tenancy/`**: `tenancy.md` and `tenancy.eflint`, six clauses, one per Phase 2
  addition (provenance, `Param`, time, `Valid when`, `Immunity`, `Except under`,
  `Overridden by`, `Module`/`Use`, explored `Invariant`s, scenarios with the three claims,
  `?why`). `charter check` passes every provenance check; `charter test` every scenario;
  `charter prove` decides all 40 theorems (59 s, 1.2 GB).
- **`Examples/AutonomousCommons/commons.eflint`**: the commons over the eight `lib/`
  modules, its eight clauses with the texts the v0.3 companion approved (same hashes),
  every one of its ~140 rules named by a span, the commons' own rules in Charter, nine
  scenarios reproducing the eight Lean simulations' quantities, breaches and powers.
  `charter test` in 14 s with every invariant explored. The v0.3 `.charter` and Lean
  companion stay until Phase 3's deletions.
- **`Examples/SovereignAgency/law3.eflint`**: the fourteen LAW3 clauses (the plan says
  fifteen; the v0.3 program has fourteen) with their approved texts, all 68 rules the
  clauses name as acts, duties and one immunity, INV.8 `frozen-state` and INV.9
  `guaranteed-last-choice` as `Invariant`s, twelve scenarios. Reading of the v0.3
  records recorded in the file's header (a power's `valid` is the act's `Holds when`;
  `forbid act a` is a duty violated when the fact `a` records holds; "anyone" is the
  type `party` with roles as facts). Three spans naming theorems outside Law 3 are
  `Commentary` until Phase 3 (texts unchanged, approvals stand). `charter test` passes,
  every invariant explored. `charter prove --chunk 1 --memory 8192`: 122 of its 276 phrases decided in 56 minutes, then one phrase of the scenario at line 551 exceeded 8 GB on its own and the run stopped; INV.8 and INV.9 are therefore **not** discharged by `prove`, the one Phase 2 exit item still open besides Phase 1's proof. Each decided phrase took about 30 s. A rerun under the 16 GB maximum would take over an hour and may still fail on that phrase; option (b) is the remedy.
- **`Eval/Properties.lean`**: `Elem.beq_iff`/`Tagged.beq_iff` (the hand-written `==` is
  equality, by mutual structural induction on the nested inductive);
  `Saturate.rebaseAndSat_assigned` (004.3 in full: an assigned fact is exactly what the
  state holds after saturation, with stamp, expiry and origin);
  `isViolated_of_holds` (006.2 and 006.5 agree: for an instance that holds, the query is
  the violation condition the report evaluates). Standard axioms only; cited in specs 004
  and 006.

## Measured

- Law 3's phrases are expensive in the kernel: one assertion (`+bound(Ava).`) alone is
  36 s and 4.2 GB, because every phrase re-saturates a spec with 55 derived act types;
  the single declaration block of 68 rules passed 12 GB in 49 s. The block is now
  fifteen declaration phrases (one per section), each under the cap. This is the
  measured reopen condition for the per-phrase cost (013.4, option (b): interning type
  names to `Nat`, recomputing strata only on declaration phrases): a `lib/` program's
  phrase costs a second; a protocol law's costs forty.

## Dead ends, so nobody repeats them

- `Terminated by a` and `Created by a` bind the duty's components from the act's: a duty
  `Holder tenant Claimant landlord Terminated by pay` needs `pay` to carry both. The
  resolver does not catch the missing binding; it surfaces at run time as CHR102 on the
  declaration phrase and every later phrase then fails with CHR010. A static check is
  worth adding (Resolve, duty clauses).
- `Except under` shares components by name: `terminate-agent(party, agent) Except under
  revoke(agent)` made every termination lawful whenever the agent could revoke. The
  agent's own end is a separate act, not an exception on the interference.
- An exploration (`//! explore`) fails from a scenario end state where an invariant is
  already violated; a scenario that shows a breach must undo it before it ends.
- `Invariant d When e` takes no clauses; its `From` goes on `Extend Fact d From …`.
- `Document "…"` must be ended with `.` when a `#require` follows.
- The commons' `//! explore-domain: int = 0..3000` made `charter test` run past five
  minutes; a menu is a short list of the amounts the scenarios use.

## Next

1. Phase 1's exit: the declarative semantics (`Charter.Core.Meaning`, say): a relational
   meaning of terms, derivation as the least fixpoint, triggers and violations, and the
   evaluator proved sound and complete against it; leastness of 004.5 needs
   monotonicity, which needs it. Weeks, not a session.
2. 013.4 option (b), now measured as needed by Law 3.
3. 13.5 / D8: the `lib/lean/Modules/` proofs by invariant name, which need (1)'s
   reasoning principles over the evaluator; the binding mechanism in `prove` waits for a
   first honest theorem to attach.
4. Eric rules B9 and B10; the 7.3 wording; Phase 3's artifact format after B10.

---

# Handoff — 2026-10-25: the checkpointed chain; `charter prove` decides whole `lib/` tests

## Where

- `main`, pushed directly. One commit. `tools/battery`: PASS on this tree before the push.
- Eric ruled (a), the checkpointed chain, over (b), interning names: interning scales the
  constant and the asymptote was the problem (0.23 GB per phrase in one declaration);
  (a) lives in `Prove/` and touches nothing the pipeline depends on. (b) is reopened only
  when a single phrase exceeds the cap on its own, which the chain will name (013.4).

## What landed

- `Charter.Prove.Run`: `S0`, `Phrase.scenarioParts`, `afterScenario`, `stepPhrase`,
  `stepItem`; `summarize` is now `addViolated (items.foldl stepItem S0)`; the chaining
  lemmas `foldl_step`, `stepItem_phrase`, `stepPhrase_of_none`, `foldl_phrase`,
  `foldl_scenario`, proved by `rw`/`unfold`/`show` alone. `#print axioms`: none.
- `Charter.Prove.Kernel` (new, a separate root of the `Charter` library in
  `lakefile.toml`, so the executable never links the elaborator): the tactic
  `kernel_rfl`, which closes `a = b` with `Eq.refl b` added through `mkAuxLemma`, the way
  `decide +kernel` adds its `decide p = true`. The elaborator never compares the sides;
  no `DecidableEq` is needed (Lean cannot derive one for `Term`/`Elem`, nested inductives).
- `Charter.Prove.LeanGen`: per phrase `p_k`, `cfg_k`, `S_k` (the record, as the compiled
  evaluator produced it) and `theorem step_k : stepSummary S_{k-1} p_k = S_k := by
  kernel_rfl`; per scenario the sub-chain `step_k_j`, `scen_k` (rewriting with
  `foldl_step`), `viol_k` (`addViolated` at its end state, `kernel_rfl`), `after_k`
  (`afterScenario … = S_k := rfl`); `viol_final`; `run_decided : summarize items = S_fin`
  by one `rw` per item with `foldl_phrase step_k rfl` or `foldl_scenario scen_k viol_k
  after_k`; `program_decided` and the per-claim theorems as before. `Project.steps`
  records each checkpoint's block start and program line.
- The chain is split into modules of `--chunk` phrases (default 5), `<stem>_steps_n`,
  each importing the one before; the main file `<stem>` imports the last. Measured first
  in one process: the checker's resident size grows monotonically through the file (about
  30 MB/s, sampled every 2 s on the entity-group test; 10 GB for the 145-phrase sortition
  test), so the per-declaration bound did not bound the process. `Project.files` lists
  the modules; locations are `(module, line)`.
- `Charter.Cli.Prove`: writes every module, runs one checker process per module in order
  (`lean --memory … -o <module>.olean`, the project directory on `LEAN_PATH`), the time cap
  shared by the run and the memory cap applied to each process; stops at the first failing
  module. A failing step theorem is reported on every claim as "the kernel's run of the
  phrase at line L disagrees with the evaluator's (Law 9)"; a chain that fails for another
  reason says so and points at `--show-checker`. `--chunk N`.
- `Repr` derived for `Spec`, `State`, `Config`, `Summary` (the checkpoints are printed
  through it). `tools/prove-check` runs with `--show-checker` and fails on any
  `#print axioms` line naming `propext`, `Classical.choice`, or `Quot.sound`.
- Fixture `test/prove/scenario.eflint` (a scenario's sub-chain, its end state, the
  restored configuration). Spec 013.4 rewritten for the chain; 018.2; plan §3 and §6
  note the `--show-checker` spelling; AGENTS.md's kernel rule says what a `prove` cap
  hit now means (one phrase, not the program).

## Measured (`charter prove --show-checker`, one at a time, default 6144 MB cap)

| program | phrases | theorems | result |
|---|---|---|---|
| test/prove/three_phrase | 5 | 3 | 1.6 s, 0.5 GB |
| test/prove/module_use | 6 | 6 | 6 s, 1.3 GB |
| test/lib/entity_group_test | 70 | 40 | 68 s, 2.7 GB |
| test/lib/exit_and_voice_test | 92 | 52 | 155 s, 3.3 GB |
| test/lib/oracle_feed_test | 52 | 45 | 183 s, 4.1 GB |
| test/lib/attested_lease_test | 73 | 50 | 187 s, 5.7 GB |
| test/lib/circuit_breaker_test | 68 | 41 | 274 s, 3.6 GB |
| test/lib/collateral_pool_test | 89 | 59 | 478 s, 4.6 GB |
| test/lib/residual_ledger_test | 87 | 66 | 573 s, 4.6 GB |
| test/lib/sortition_court_test, one process | 145 | 70 | killed at the 6144 MB cap after 360 s; under a 12288 MB cap 1189 s, 10.1 GB |
| … in modules of 10 phrases, scenarios whole | 145 | 70 | 1277 s, 5.6 GB (7 modules) |
| … in modules of 10 phrases, scenarios split | 145 | 70 | 1493 s, 4.7 GB (resident size resets at every module) |

The rows above the sortition ones were measured in one process, before the module split.
Before the chain, the entity-group test's genesis prefix plus one scenario (28 phrases) was
killed at 12.5 GB; the whole file was out of reach. Every lib test now decides under the
default cap; `--time` must be raised above 300 s for the longer ones. Sampled every 2 s on
the entity-group test in one process, the checker's resident size rose monotonically,
about 30 MB/s, with no drop between theorems: the per-declaration bound did not bound
the process, hence the modules. The sortition test's phrases cost about 400 MB each
inside a module, so the default is 5 phrases per module (about 2.5 GB there), chosen from
the 10-phrase trace, not re-measured.

## Dead ends, so nobody repeats them

- `rfl` passed where a lemma's conclusion has an implicit the hypothesis should fix
  (`hc : afterScenario s s'' = s₃`) leaves `s₃` as the unevaluated application, and the
  next rewrite finds no `S_k`. Every such hypothesis is a named theorem in the generated
  file (`after_k : afterScenario S_{k-1} S_k_v = S_k := rfl`).
- `deriving DecidableEq` on `Elem`, `Term`, `Args`: "None of the deriving handlers
  applied" (nested inductives). Not needed with `kernel_rfl`; do not hand-write one.
- `simp` in a chaining lemma would close goals through `eq_self`, which carries
  `propext`; the lemmas use `rw` only, and the gate now catches a relapse.

## Next

1. The two things the chain makes possible, when a measured program asks for them: one
   module per step theorem, run as separate bounded processes in parallel; a cache keyed
   by the hash of `(S_{k-1}, p_k)` so an unchanged prefix is not re-decided.
2. Eric rules B9 and B10; Phase 3's artifact format after B10. `lib/lean/Modules/`
   proofs by invariant name (D8, 13.5).

---

# Handoff — 2026-10-24 (night, 2): `charter prove` lands as the generator; the kernel's memory limit measured

## Where

- `main`, pushed directly. One commit. `tools/battery`: PASS on all eleven steps on this
  tree before the push (the new step `prove` runs `tools/prove-check test/prove`).

## What landed

- `Charter.Prove.Run`: `Phrase.claimCount`/`claimTexts` (mutual structural blocks with
  their list helpers), `claimVerdicts`, `Summary`, `summarize`, `summary` (every claim's
  verdict in order; every invariant that does not hold at the program's end state or a
  scenario's), `claimLabels`.
- `Charter.Prove.LeanGen.generate`: the project text. Phrases embedded as data through
  the derived `Repr` (its output is Lean syntax for these records, on one line each);
  `theorem program_decided : Prove.summary items = (verdicts, violated) := by decide +kernel`
  with the literal the compiled evaluator produced; per claim
  `theorem claim_k : (Prove.summary items).1[k]? = some true := by rw [program_decided]; rfl`
  and per invariant `… .2.contains "d" = false`; `#print axioms` after every theorem.
- `Charter.Cli.Prove`: `charter prove <file.eflint> … [--dir] [--memory MB] [--time S]
  [--show-checker] [--emit-only] [--out json] [--eflint]`. Loads with the includes
  inlined, writes `.charter/prove/<stem>/<stem>.lean`, finds the repository root by
  its manifest, reads `PATH`/`LEAN_PATH` from `lake env printenv`, runs `lean --memory`
  directly with a `ps`-based resident-size watchdog and a time cap, maps the checker's
  error lines to theorems, treats an axiom dependence as failure (Law 10), prints one
  line per theorem and `prove: D decided, F failed`; exit 0/1/2. The plan's flag name
  `--show-lean` became `--show-checker`: the Law 11 gate greps the help text for
  `\blean\b` and `-` is a word boundary. Eric may want to rule on the name.
- Axiom hygiene: `showString` folds over `s.toList` (`String.foldl` carries `propext`);
  `Kind.lowerName` replaces `k.name.toLower.decapitalize` in two resolver messages.
  `#print axioms Charter.Prove.summary`: none. `String.splitOn`, `startsWith`, `trim`,
  `replace`, `endsWith`, `toNat?`, `dropWhile`, `any`, and `List.mergeSort` also carry
  axioms; none is reachable from the evaluator today. Keep it so.
- Fixtures `test/prove/three_phrase.eflint` (`//! prove-failed: 1`) and
  `test/prove/module_use.eflint`; `tools/prove-check`; battery step 9.
- `tools/kernel-probe` prints the peak resident size.

## Measured (through the probe, one at a time)

| program | theorems | result |
|---|---|---|
| three_phrase | 3 | under 1 s |
| module_use (entity-group instantiated, conserving genesis) | 6 | ~2 s, 1.8 GB |
| entity_group_test genesis prefix (19 phrases) | 9 | 21 s, 4.9 GB |
| … plus its first scenario (9 more phrases) | 18 | killed at 12.5 GB after 51 s |

Kernel memory grows with kernel time, about 230 MB/s, about a second per phrase of a
`lib/` program. The whole lib test (about 70 phrases) is out of reach under 16 GB.

## Dead ends, so nobody repeats them

- `Phrase.claimCount` as a plain recursive def over `.par ps` was compiled by WF
  recursion (`@[irreducible]`) and stalled the kernel at 6 GB in 5 s, exactly like the
  evaluator's block before. Any def the generator's statement reaches must be
  structural; check with `#print` for `@[irreducible]`.
- The invariant theorem as "never reported violated after any phrase" fails honest
  programs: genesis builds a state over several phrases. It is now about end states.

## Next (needs Eric's ruling between the two)

1. (a) Checkpointed chain: the generator writes the configuration after every phrase as
   data, one small theorem per phrase, a chaining lemma proved once in `Prove.Run`;
   bounded memory for any program length. Needs `Repr`/`DecidableEq` (or a `BEq`
   theorem form) on `Config`, `Spec`, `State`. (b) Intern type names to `Nat`, recompute
   strata only on declaration phrases; scales the constant only. Phase 3 needs (a).
2. Eric rules B9 and B10; Phase 3's artifact format after B10.

---

# Handoff — 2026-10-24 (late night): the create phrase's cost located; it was the elaborator, not the kernel

## Where

- `main`, pushed directly. One commit: spec 013.4's third finding, the checked-in probe
  `tools/probes/three_phrase_decides.lean`, this section. `tools/battery`: PASS on all ten
  steps on this tree before the push (numbers in the commit message).

## What was found

Bisected one capped probe at a time through `tools/kernel-probe` (never in parallel):

| probe (plain `by decide` unless marked) | result |
|---|---|
| `M.eval 40` on the compiled create term | ok, 1 s |
| `M.eval M.fuel` (100000) on the same term | ok, under 1 s |
| `M.evalEffect M.fuel (.cAll [] t)` | ok, under 1 s |
| `Store.unions` over that effect's stores | ok, under 1 s |
| `Interp.semPhrase … 5 cp` | killed, 6.2 GB after 6 s |
| `Interp.semPhrase … 1 cp` | killed, 6.2 GB after 5 s |
| `Interp.semPhrase … 5 cp` with `decide +kernel` | ok, under 1 s |
| three-phrase program, `decide +kernel` | ok, under 1 s (was ~200 s with plain `decide`) |

So fuel size, `Store.union` and `DomId` strings were not the cost. Plain `decide`
evaluates the `Decidable` instance in the elaborator first (`Meta.whnf`), and that
evaluation blows up on `semPhrase`'s frame; the kernel decides the same term at once.
`decide +kernel` skips the elaborator's evaluation and is still a kernel-checked proof.

## Consequences

- `Prove.LeanGen` emits `by decide +kernel` for every theorem; items embedded as data.
- Interning names to `Nat` is deferred: no measured program needs it yet.
- The probe is checked in as `tools/probes/three_phrase_decides.lean` with the
  measurements in its header; run it only through `tools/kernel-probe`.

## Next

1. `Prove.LeanGen`: embed items as data, one theorem per invariant and expectation,
   `decide +kernel`; measure on a lib module before calling it shipped (013.4).
2. Eric rules B9 and B10; Phase 3's artifact format after B10.

---

# Handoff — 2026-10-24 (night): guardrails for kernel experiments after a crash; the evaluator made structurally recursive, and the first kernel decision of a Charter program

## Where

- `main`, pushed directly. Two commits: `tools/kernel-probe` with the AGENTS.md rule, then
  the evaluator change with spec 013.4's finding and this section. `tools/battery`:
  PASS on all ten steps (build, three gates, check 280 ok, sim 16/16 and 8/8, corpus 196/196 with 32 tolerated, spec 121/121, standard library 8/8) on the maintainer machine with the pinned toolchain, on the tree of the second commit, before the push.

## The incident, and the guardrail

Five kernel-decision probes (`by decide` on the evaluator with `maxHeartbeats 4000000`,
`maxRecDepth 100000`, no memory limit) were run in parallel in the background; together
they took 128 GB and crashed Eric's machine. **Rule (AGENTS.md, "Working efficiently"):**
any ad-hoc `lean` run that may reduce an unbounded term goes through
`tools/kernel-probe FILE.lean [--mem MB] [--time S]`: Lean's own `--memory` cap plus a
resident-size watchdog over the whole process tree (`timeout` → `lake` → `lean`, polled
every 0.25 s), a wall-time cap, and a run lock so probes never overlap. Defaults 6 GB /
300 s, memory never above 16 GB. Verified: a held 2.3 GB allocation killed under a 512 MB
cap within a second; a kernel decision that reached 4.5 GB killed under a 4 GB cap; a
60 s sleep killed by a 5 s cap.

## What was found (the kernel finding of 013.4, cause located)

1. `Charter.M.eval` and its mutual block were compiled by **well-founded recursion**
   (`#print M.eval` showed `@[irreducible] … instantiateDomain._mutual`), which the kernel
   never unfolds, so `decide` got *stuck*, not slow. Cause: `foreach`/`scope` were
   polymorphic (`{α : Type}`) inside the block, which makes `brecOn`'s motive ill-typed.
   Fix: `scopeWith`/`foreachWith` outside the block, parameterised by the binder
   (`everyValidSubs fuel`); the block now carries `termination_by structural n => n` on
   every function and `#print M.eval` shows `Nat.brecOn`. `foreach`/`scope` remain as
   wrappers for the Interpreter. Spec 121/121 and lib 8/8 unchanged.
2. Measured (through the probe tool after the crash): parsing the three-phrase text in the
   kernel exceeds 180 s, so `prove`'s generator must embed **parsed items as data**, never
   text; resolving a declaration decides in 0.2 s; the create phrase's `semPhrase` is where
   the remaining time goes; the whole three-phrase program from parsed items decided in
   about 200 s of wall time (170 s CPU) with no error, the first kernel decision of a
   Charter program.

## Next

1. Locate the create phrase's kernel cost (candidates: `M.fuel = 100000` through
   `Nat.brecOn`, `Store.union`, string comparisons on `DomId`), one capped probe at a time;
   then interning names to `Nat` if strings dominate (013.4).
2. `Prove.LeanGen`: embed items as data, one theorem per invariant and expectation.
3. Eric rules B9 and B10; Phase 3's artifact format after B10.

---

# Handoff — 2026-10-24 (later): D15 and D16 ruled and implemented — acts over a non-enumerable domain are judged per instance, CHR025, the `explore-domain` menu; `Duration * Int`

## Where

- `main`, pushed directly (landing rule of 2026-10-23). Two commits: D16 (`compileScale`, four
  fixtures, the collateral pool's multiplied window), then D15 (the membership path, CHR025,
  the explore menu, four fixtures, `entity-group` back to `Related to int`, the decision
  entries, spec, tolerance ledger, this section). `tools/battery`: PASS on all ten steps (build, three gates, check 280 ok, sim 16/16 and 8/8, corpus 196/196 with 32 tolerated, spec 121/121, standard library 8/8) on the maintainer machine with the pinned toolchain, on the tree of the second commit, before the push.

## What was done

1. **D16, brief B12 (Eric: allow).** `Resolve.compileScale`: `Duration * Int`, `Int * Duration`,
   `Duration / Int` are durations; `Duration * Duration`, `Time * …`, `Int / Duration` are
   CHR012 with messages naming D16. Fixture `spec_009_2d_duration_times_int` seen failing
   (14 CHR012) before the change; `2e`–`2g` are the refusals. `lib/collateral_pool.eflint`:
   multipliers as `Param`s, `risk-factor`/`irreversibility-factor` derived per action (1 where
   the class does not apply or the multiplier is below 1, the Lean `max 1`), one `commit` act,
   `For base-observation-window * risk-factor.int * irreversibility-factor.int`. Spec 009.2,
   010.2.
2. **D15, brief B11 (Eric: (B) with two sharpenings, acts only).**
   - `Spec.judgedAct` names the acts concerned (non-enumerable domain, has `Holds when`);
     `Eval.isHolds` reads their clauses with the instance's components bound when no
     assignment exists (assignment still wins, 004.3); `?why` says which path answered.
     Fixture `spec_005_5b_act_with_int_component_judged_per_instance` (seen failing: 5 claims).
   - **CHR025** (warning) at every binder site in Resolve (`Exists`/`Forall`/aggregates,
     `Foreach` in effects and `Derived from`, free variables of a `Holds when`, `?-x()`): a binder
     over a judged act sees only its assigned instances. Fixture `spec_004_7b`.
   - **Explore menu.** `//! explore-domain: <type> = v, a..b, "s"` and `--explore-domain`
     supply the candidates for a judged act's primitive components (`Explore.scopeJudged`).
     Without a menu the search uses the values of that kind found in the state (*state-values*,
     named in the output) and reports the act **unexplored** as a failed claim (`tag:
     "unexplored"` in JSON). Fixtures `spec_013_2d_explore_menu` (the menu reaches the
     violation) and `spec_013_2e_explore_without_menu_is_not_a_pass`. `entity-group` dropped its
     `amount` parameter; its test carries `//! explore-domain: int = 0..12` and runs in 0.2 s
     (was 3.3 s with the finite menu in the institution).
   - Corpus baseline after the change: 196/196, 164 agree, 32 tolerated (all pre-existing);
     CHR025 fires in no corpus file. The D15 tolerance row therefore names no files.
   - Spec 004.1, 004.7, 005.5, 013.2, 018; `diagnostics.md` CHR025; `lib/README.md`.
3. Decision entries `docs/meetings/2026-10-24-D15-…` and `…-D16-…` carry Eric's reasoning;
   the briefs file marks both ruled; plan §9 and `docs/meetings/README.md` updated.

## Notes for `prove` (013.4)

The evaluator's agreement proof now has two paths for "holds": materialised (saturation) and
membership (`isHolds` on a judged act). Both have to be covered; the membership path is the
direct reading of 004.1 and is the easier of the two to state.

## Next

1. Eric rules B9 and B10.
2. The kernel-oriented Core for `prove` (013.4), then `lib/lean/Modules/` proofs attached by
   invariant name (D8).
3. Phase 3's artifact format after B10.
4. D15's reopen condition: a PSA clause needing `Holds when` on an `Int`-carrying fact with a
   time condition (the stamp of an intensional fact is undefined).

---

# Handoff — 2026-10-24: Phase 2's seventh slice, the eight `lib/` modules as Charter programs (D8); two Resolve fixes

## Where

- `main`, pushed directly (landing rule of 2026-10-23). Two commits: the Resolve and lexer
  fixes with their fixtures, then the library with its tests, battery step, spec updates,
  briefs B11–B12 and this section. `tools/battery`: PASS on all ten steps (build, three gates, check 280 ok, sim 16/16 and 8/8, corpus 196/196 with 32 tolerated, spec 113/113, standard library 8/8) on the maintainer machine with the pinned toolchain, before the push.

## What was done

1. **`lib/`** — `entity_group`, `oracle_feed`, `circuit_breaker`, `residual_ledger`,
   `collateral_pool`, `exit_and_voice`, `sortition_court`, `attested_lease`, each a
   `Module` with its Lean theorems as named `Invariant`s, and `lib/README.md` with the
   conventions. **`test/lib/`** — one program per module that `#require`s and `Use`s it,
   with scenarios and `//! explore: 1`; 8/8 pass in about 6 s; `tools/battery` step 8 runs
   them. Spec 015.5 and 013.5 updated; proofs under `lib/lean/` and the *proved* tag wait
   for `prove` (013.4).
2. **Resolve fix (spec 014.1):** a `Param` used as the `For d` of `Creates e For d` was
   CHR102 ("variable cb-preliminary-freeze-window is not bound"): `compileEffect` bound the
   effect's free variables but not the expiry's. Fixture `spec_014_1c_param_as_duration`
   (seen failing with that CHR102; passes after).
3. **Resolve diagnostic CHR024 (spec 003.7):** a `Function` whose domain is not a product of
   exactly two components. eFLINT's `function_assignment _ s = s` ignores every assignment to
   one silently, and Charter did the same (`+of-inflow(V1, 1000, 30)` on a three-component
   `Function` created nothing and `?--of-inflow` was empty); a silent tool is a bug. Every
   `Function` in the corpus has two components, so refusing is D2-safe. Fixture
   `spec_003_7b_function_arity`.
4. **Lexer (spec 002.1):** a run of primes is decoration (`int'''`); the old rule read `''`
   as the start of a character literal. Fixture `spec_002_8_prime_decorations`.
5. **Briefs for Eric** in `docs/meetings/2026-10-24-briefs-for-ruling.md`: **B11**, an act
   that names an amount is never lawful by derivation (eFLINT's rule; measured costs of the
   finite-menu workaround; recommendation: lawfulness is asked of the instance); **B12**,
   `Duration * Int`.

## Lessons that cost time (now in spec 004.7 and `lib/README.md`)

- A binder over a type whose components are all enumerable ranges over the whole domain, so
  in a rule `(Exists frozen: frozen.member == member)` is true for every member; say
  `frozen && …` or use the application form. Over a type with an `Int` component the binder
  ranges over what holds. I misread this as an evaluator bug three times (reductions in the
  scratchpad: `Forall worker: (Exists basis: basis.worker == worker)` was "true" with one
  basis instance because `basis(Ben, 0)` is a domain element).
- `Holds when` on an act with an `Int` component derives nothing (B11). `Min(Foreach int'': …)`
  over `int` is empty; write min/max as paired `Derived from` clauses.
- A derived fact is stamped at the phrase that first derived it (009.3); a scenario that
  jumps the clock past the instant a `Held … For` condition became true gets the later stamp.
- Exploration cost: with amount-carrying acts over `0..12` and three members, depth 2 took
  181 s and depth 1 takes 3 s; `enabledActs` re-enumerates every act domain per state. The
  library tests use depth 1. Exploration found three real modelling bugs in first drafts
  (a second proposal doubling a commitment's exposure; an invariant counting unfiled
  disputes; a lease holder's own restore counted as quarantined).
- `Function` with one or three components silently creates nothing (now CHR024).

## Next

1. Eric rules B9–B12; apply B11's edit to `entity-group` if (B) is chosen.
2. The kernel-oriented Core for `prove` (013.4), then `lib/lean/Modules/` proofs attached by
   invariant name (D8).
3. Phase 3's artifact format after B10.

---

# Handoff — 2026-10-23 (day): Phase 0 closed, Phase 1 eFLINT core running the corpus, plan amended for the server; branch `phase-0-1-eflint-core`

## Where

- Merged to `main` by fast-forward (PR #1, then direct pushes per the landing rule change of 2026-10-23). The branch carried eight commits
  (`496076d` move to `src/`, `ab88de7` D12/B9/spec skeleton, `51ee95b` corpus,
  `1a12f3f` gates and battery, `3dc5c3d` plan §3a server, `1651515` Phase 1 pipeline,
  `f1c5cc4` `test --expect`, plus this handoff). Every change goes to `main` through a
  PR; open one from this branch when the battery is green (see "Corpus baseline").
- Tree layout now: `src/Charter/` (the language; `Surface/`, `Core/`, `Resolve/`,
  `Eval/`, `Cli/` are the new pipeline, the rest is v0.3), `src/Main.lean`,
  `Examples/` unchanged, `docs/spec/` (skeleton), `docs/completed/` (the v0.3 spec),
  `test/eflint-corpus/`, `test/gates/`, `tools/battery`, `tools/corpus-baseline`.

## What was done

1. **Phase 0 closed** (plan §8): `docs/spec/README.md` chapter list with the
   NON-COMPLIANT marker and `docs/spec/diagnostics.md` (CHR001–CHR021, CHR100–CHR105
   allocated); `docs/charter-spec.md` archived; the eFLINT tests (116 files) and
   examples (80 files) vendored unchanged with provenance hashes; `test/gates/` for
   Laws 10, 11, 13; `tools/battery` (build, gates, `check`, `sim`, corpus). The Law 11
   gate found the `verify` ledger printing `psa_program_is_lean_law` and "the Lean
   law"; renamed to `*_program_is_companion_law` / "the companion law". The Law 13
   gate found `toNeutralReserveOrCommons` in `CollateralPool` (the handoff's "leak grep
   0" was wrong); renamed `…OrPool`.
2. **Decisions.** D12 (duty violations reported on transition) recorded as
   *delegated* at 80%. B9 (duplicate declarations) written as a **brief, not a
   decision**: `tests/truth/infinite_even.eflint` and
   `tests/parallel-comp/no_violations.eflint` deliberately redeclare a type and pass
   only under eFLINT's replacement, so it is semantics and Eric's call; the code
   replaces and warns (CHR019). B10 (who signs the artifact certificate) opened by the
   server work. All in `docs/meetings/2026-10-23-briefs-for-ruling.md`.
3. **Plan amended at Eric's direction** (commit `3dc5c3d`): §3a compiler/server split
   (`charter` produces an artifact: law, certificate, document, one hash;
   `charter-server` loads, verifies, evaluates, appends, replays, and links no parser),
   goal 3 restated as one artifact in three hosts, Phase 3 reordered (artifact format
   first, then `Amend` with the certificate check), Phase 3b (the server) added, gates
   `replay`, `certificate-at-office`, `operator-blind`. The mission-text changes this
   implies (goal 3 wording, a purpose sentence, an operator law, an amendment law, the
   sharpened *checked* tag) are **drafted in §3a and not applied**: `docs/mission.md`
   is untouched; Eric words them.
4. **Phase 1, the eFLINT core** (commit `1651515`): a complete pipeline for `.eflint`
   files in Lean with no `partial` and no `sorry`: `Surface/Lexer` (eFLINT's token
   classes, including bracketed `[Recht beschrijving]` and space-joined `other
   candidate` identifiers; one deterministic rule for the projection dot),
   `Surface/Parser` (recursive descent; its disambiguation choices are in the module
   header), `Core/{Term,Spec,State}` (records), `Resolve/Static` (eFLINT's static
   evaluation: types, arities, checked terms, duty-clause desugaring, CHR01x),
   `Eval/Eval` (the nondeterministic evaluator, fuel-bounded), `Eval/Interpreter`
   (stratified saturation per D6 with CHR020; phrase semantics; D12 reporting), and
   `charter run | test | check` on `.eflint` files. **All 116 of eFLINT's own tests
   pass** (`charter test test/eflint-corpus/tests`). Examples: 54/80 before the
   baseline (below).

## The corpus against the eFLINT oracle

The examples repository is not a test suite, so the Haskell eFLINT had to run to say
which differences are Charter bugs. No GHC was installed; I installed `ghc@9.4` and
`cabal-install` with Homebrew (reversible: `brew uninstall ghc@9.4 cabal-install`)
and built `eflint-repl` from a *copy* of `.reference/eflint` in the session scratchpad
(`.reference/` was not written to). The build needed `allow-newer: eflint:*`, the
macOS SDK `usr/lib` for `iconv`, `SDKROOT` for the Security framework, and
`gll-0.4.1.2` vendored with one added `liftA2` import (it assumes GHC ≥ 9.6). The
binary is copied to `out/eflint-repl` (ignored); rebuild it the same way if `out/` is
gone. `tools/corpus-baseline out/eflint-repl` produced
`test/eflint-corpus/eflint-outcomes.txt` (committed): **eFLINT 4.1.0.1 fails 10 of its
own 196 corpus files.** `charter test --expect … --tolerate …` compares file by file;
the result, all in `test/eflint-corpus/tolerances.md`:

- **Agree with eFLINT: 164 files**, including the two files eFLINT fails that Charter
  also fails (`smart-access/simple-scenario.eflint`, a fragment other files require;
  `school_policy/valid_dates.eflint`, a `Holds when` over a non-enumerable type with
  no held instances).
- **D6 (a), Charter right where eFLINT is order-dependent: 3 files.** eFLINT fails its
  own `deriv_sum1a`, `deriv_sum1b`, `from_not_enabled2` because its inflationary
  fixpoint evaluates `zz`/`aa` (and `prohibition`) before `y` (and `read`) are
  derived and keeps the first answer; the stratified fixpoint passes them.
- **D6 (b), Charter rejects a default rule eFLINT accepts: 24 files.** One program,
  `dex-archetypes/archetypes.eflint` lines 78–93, derives `algorithm-provider-for`
  (and two more) from `!(Exists algorithm-provider: algorithm-provider-for())`: a
  default whose only reading is its own absence. CHR020 names the three types; the
  23 scenarios and templates that include it fail with it. **This meets D6's reopen
  condition** ("more than a handful of corpus programs stop passing"): Eric decides
  whether a default rule gets a spelling (an explicit exception, as Catala has) or
  stays rejected.
- **D13 (delegated), placeholders: 1 file.** `tests/placeholders/with2.eflint`
  creates an instance through `Placeholder a For b`; eFLINT tags it `a` and fails its
  own test; Charter tags it `b` and passes.
- **D14 (delegated), `When` precedence: 4 files.** eFLINT's generalised parser reads
  `Terminates grounded When date + 1 == grounded.date` (caretaker contract) as
  `(grounded When date) + 1 …` and rejects the program as ill-typed; Charter's
  lowest-precedence `When` reads it as the author's comment says, and the four files
  pass.

`tools/battery` is green on this branch with the baseline and tolerances in place.

## Observations

- `tests/truth/dom_filter1.eflint` passes vacuously in eFLINT: in the phrase path
  (`StaticEval.hs`, `compile_phrase (PDeclBlock)`) a `TypeDecl`'s `Where` constraint is
  inserted uncompiled, so `x % 2` on a tagged value yields no result and every `?x(n)`
  succeeds over an empty result list. Charter compiles the constraint (`compileTypeSpec`),
  so the same queries pass non-vacuously. No outcome differs; the spec chapter 004
  should say the constraint is checked.
- eFLINT prints synced transitions in the order the clauses were *last* prepended
  (`c` before `b` in `tests/syncs/hierarchy.eflint`'s tree); the comment in that file
  shows `b` first. Charter prints as eFLINT's code does. Cosmetic; not in test mode.

## Later the same day: the rest of Phase 1's list (pushed to `main` directly, per the new landing rule)

- **`--out json`** on `run`, `test`, `check`: one record per line (`diagnostic`,
  `claim` tagged *checked* about *holds*, `transition` with the three answers,
  `violation`, `fact`, `summary`). **`charter repl [file]`** with `:display`, `:help`,
  `:quit`. **Fixture directives** `//! expect-error: CHRnnn`, `//! expect-warning:`,
  `//! known-issue:` read by `charter test` (plan §5.4).
- **Spec chapters 002–011 drafted** (`docs/spec/`), every normative statement with a
  conformance test: 72 files under `test/spec/` (`.eflint` until the `.charter`
  extension moves to this grammar), all passing; `tools/battery` step 7 runs them.
  Three test-authoring mistakes were found and fixed by the run (built-in types hold
  nothing until assigned; eFLINT's "cannot reopen" applies only to a type that was
  explicitly open then closed; declaration-order test lacked a declaration). The
  chapters are **drafts**: D2 fixes the meaning, Eric blesses the wording. 007 and 009
  state the Phase 2 designs as pending. Integer `/` and `%` now round toward negative
  infinity (`Int.fdiv`/`fmod`), matching Haskell's `div`/`mod`; the corpus had no
  negative divisor to catch it, `spec_010_2` does.
- **`Charter.Eval.Properties`**: the first proved properties, depending on `propext`
  at most: 005.3 create beats terminate (`Store.create_beats_terminate`), 004.3
  assignment beats derivation (`State.derive_assigned`, `deriveAll_unchanged`), and
  004.5's fixpoint half (`Saturate.saturateStratum_fixpoint`: the state the evaluator
  returns for a stratum is unchanged by one more pass). To make them provable,
  `State.deriveAll` and the saturation `pass` were restated as structural recursion
  (same order, same meaning; the corpus and spec runs are unchanged). The trust grep
  caught the words "sorry" and "axiom" in the module's own comment; reworded.

## Evening: Phase 2's first slice (pushed to `main` directly)

- **`Valid when` (D5)** on acts: effects apply iff every condition holds at performance;
  `charter run` prints *valid: yes/no* on every transition; `TransInfo.valid`.
- **`Except under a₁, a₂`** (plan §2.2.4): lawful iff some instance of a named act sharing
  the bound components is enabled and valid; the act's own `Holds when`/`Conditioned by`
  are not consulted.
- **`Immunity name Holder v [Related to …] Against a₁, a₂ [Holds when] [Unless e]`**: a new
  kind (`Kind.immunity`, `ImmunitySpec`); an act in `Against` whose **recipient** is the
  holder of a held instance is not valid unless an `Unless` condition holds. The
  holder-is-recipient rule is this draft's reading of "not valid against the holder"
  (spec 007.4) and is for Eric to confirm; acts without `Recipient` are unaffected.
- **`Scenario name { … }`** items, run by `charter test` from the configuration at that
  point and leaving it unchanged (`run` only notes them); **claim phrases** `?lawful`,
  `?valid`, `?violated` and their `?!` negations, labelled with the question they answer
  (Law 2). A claim keyword is one only when followed by whitespace, so `?valid(5)` still
  queries a fact named `valid`; found by a conformance test, fixed in the lexer.
- **`--eflint` mode** on `run`/`test`/`check`: Charter's keywords are not keywords; the
  battery runs the corpus with it (196/196 unchanged). CHR022 registered.
- Spec 002.9, 005.9, 007.2, 007.4, 011.10–11 updated; 9 new conformance tests (82 total).
- Not in this slice: time (D7), clauses and provenance (D4), `Param`, `Module`/`Use`,
  `?why`, `Invariant` exploration, the `lib/` modules, `prove`.

## Night: Phase 2's second slice, time (D7)

- **The clock.** `@ t.` sets it, `tick.` advances it; both are phrases that are
  environment input (Law 6): no transition, no event, `Output.timeSet` only; derived
  facts and violations are recomputed like after any phrase. `@ t` backwards is CHR106.
- **`Time` and `Duration`** as `Ty.time`/`Ty.duration` and domains `Identified by Time`
  / `Duration`: `Time ± Duration : Time`, `Time - Time : Duration`, `Duration ±
  Duration`; `Time + Time` and an integer fact as a duration are CHR012; a literal or
  literal arithmetic coerces by demand (`Resolve.literalArith`, `arithTy`,
  `compileCompare`, `compileArith`). `Current Time : Time`.
- **Stamps** (Law 7): `Info.since` on every assignment, kept when an instance that
  holds is re-created and when a derived fact is re-derived (`State.stampFrom` over the
  derived facts before rebasing; `deriveAll`/`pass`/`saturateStratum` take `prev`).
  `Info.expiry` from `Creates e For d`; `Info.live now` replaces `value` wherever
  holding is asked. `Held(e) For d` is the stamp condition; `Due within d` on a duty
  desugars to `Violated when Held(d()) For d`.
- Spelling choices for Eric (spec 009): `Held(e) For d`; `tick` is a reserved word in
  Charter mode.
- Spec 009 rewritten; 003, 006, 010, 011 updated; 11 time tests (92 total). The
  properties file's theorems were re-proved over the new signatures (still `propext`
  only). A regression caught by the corpus: my first comparison typing forgot that an
  integer fact instance is used as its value; fixed with `asNumber`.
## Late: Phase 2's third slice, clauses and provenance (D4, Law 8)

- Surface: `Document "path"`, `Clause ID [Approved HASH]` with `Text "…"` and register
  spans `Norm "…" => rules`, `Definition`, `Invariant`, `Acceptance`, `Commentary`;
  `From CLAUSE "span"` on acts, duties, immunities, and invariants (`TypeSpec.spans`).
  Records reused from v0.3's `Core/Provenance.lean` unchanged (`Clause`, `Span`,
  `Register`, `covered`, `normsInterpreted`, `reverseProvenanceWith`, `stale`).
- `Cli/Provenance.lean`: the six Law 8 checks as claims (covered, interpreted,
  declared, named, verbatim, approved), run by `charter check` and at the end of
  `charter test` (a failed check fails the file); `charter trace <clause> <file>`.
  `//! expect-failed-claims: N` directive for fixtures that pin a failing check.
- Spec chapter 012 drafted; 7 tests (99 total). The hash is `String.hash` as in v0.3.
## Late (2): Phase 2's fourth slice, `Param` (D11) and origins with `?why` (Law 6)

- `Param name [: Int|Time|Duration] = n`: a `Var` fact with an initial instance, assigned
  by the declaration block (`CPhrase.onlyDecls` now carries the block's initial store);
  any numeric position names it; an act may create a new instance (spec 014.1).
- `Info.origin` on every assignment: asserted by phrase n, supplied by the environment
  (open type), by an act (`Assignment` carries the act; `instantiateTrans` tags its own
  effects), derived by a type's rules (with the rules printed). `State.step` counts
  phrases. `?why e` prints it (spec 004.10, 011.13); a report, never a claim.
- A parser rule found by the `?why` test and now in spec 003.6: `Open`/`Closed` followed
  by a declaration keyword starts the next frame; before, `Fact p … Open Fact o` opened
  `p` (eFLINT's grammar has the same ambiguity; its corpus never hits it).
- Spec 014 drafted; 3 tests (102 total).
## Late (3): Phase 2's fifth slice, `Module`/`Use` (D8)

- `Module name(params) { declarations }` stores its body in `Spec.modules`; `Use
  name(args) [As prefix]` expands in `Resolve.expandUses` before a block is executed:
  parameters replaced by the argument types, every name the module declares renamed
  `prefix-name` (`Term.mapDom`, `Decl.mapDom`, `TypeSpec.mapDom` and friends in
  `Core/Term.lean` and `Core/Spec.lean`), nested `Use`s expanded recursively (fuel 32).
  CHR023 for an unknown module or wrong arity.
- Parser: `frame` and `moduleBody` are now mutually recursive on fuel. `Decl` and
  `ModClause` moved above `Spec` in `Spec.lean` because `Spec` now holds module bodies.
- Spec 015 drafted (the `-` join of the prefix is a spelling for Eric); 4 tests (106
  total).
## Late (4): Phase 2's sixth slice, invariant exploration (plan §2.2.7)

- `Explore` in `Eval/Interpreter.lean`: `enabledActs` (every enabled instance of every
  act type, enumerable components over their domain, others over held instances),
  `perform` (one act instance as a step), `violatedInvariants`, and `bfs` (breadth-first
  over enabled acts, deduplicating states by the sorted text of what holds, depth bound
  plus a cap of 5000 states, deterministic in declaration order). Lawful behaviour
  only: disabled acts are not explored.
- `charter test --explore N` and `charter run --explore N`, and the fixture directive
  `//! explore: N`; the search runs from the program's end state and each scenario's;
  a violation is a failed claim naming the invariant and the shortest trace.
- Spec 013 drafted (13.1–13.2 implemented; tags, `prove`, module properties pending);
  4 tests (110 total). One test-authoring lesson worth a line in the spec: a quantifier
  over an enumerable type ranges over the domain, over a non-enumerable one over what
  holds (004.7), so an invariant about "the counter" must be over `Int`.
## Late (5): chapter 018, `Prove.Run`, and the kernel-decision finding

- `Charter.Prove.Run`: `runText`/`runItems` run a program as a pure function (no IO).
- **Finding:** `theorem : (runText src).ok = true := by decide` on a three-phrase
  program ran ten minutes in the kernel and was killed out of memory (exit 137), no
  answer; the compiled evaluator takes 0.3 s. Strings as `List Char`, association
  lists, and the fuel-indexed monad are the cause. Recorded in spec 013.4: `prove`
  needs a kernel-oriented Core (interned names, sorted arrays) and an equality proof
  between the two evaluators; no `prove` command is shipped that cannot discharge.
- Spec 018 (toolchain and CLI, today's commands) drafted.
- Next for a fresh session: the eight `lib/` modules as Charter programs (each a real
  modelling task; `src/Charter/Modules/CircuitBreaker.lean` is the smallest), the
  kernel-oriented Core for `prove`, then Phase 3's artifact format after B10 is ruled.
  Three spellings await Eric: `Held(e) For d`, the `-` join of a module prefix, and
  the holder-is-recipient reading of immunities (spec 007.4).

## Known gaps against Phase 1's exit criteria

- The declarative semantics of `eval` and the evaluator's full agreement proof (Law 9):
  not started beyond `Properties.lean`. Today the evaluator is the only definition of
  `eval`, `isHolds`, `isEnabled`, `isViolated`; leastness of the fixpoint and the
  correctness of stratification are stated in 004.5–004.6 and tested, not proved.
- `--eflint` mode flag: nothing to toggle until Phase 2 adds a Charter construct.
- `find_transitions` (eFLINT's per-phrase enumeration of every possible trigger, used
  only by its REPL `:options`) is not computed; nothing in test mode depends on it.
- Time is fixed at 0 (`Current Time`, the `Time` domain); D7's time lands in Phase 2.
- `charter test` judges a file on its own when no baseline line exists for it.
- Chapter 007 has no tests (its constructs are Phase 2); chapters 001 and 012–020 are
  unwritten.

## Pitfalls found (also in AGENTS.md)

- A `for x in xs do` over a list of pairs inside a hand-written monad (`structure`
  wrapping a function) hits a Lean 4.24 code-generation defect: the interpreter says
  "incomplete case", the binary segfaults (exit 139). Bisected with `#eval`s on
  `Resolve.executeDecls`; `forM` works. Keep `for` to `IO`.
- Running `lean` outside the project directory used elan's default and downloaded Lean
  4.35.0 into `~/.elan/toolchains` (harmless; delete with `elan toolchain uninstall
  leanprover/lean4:v4.35.0`). Always run scratch files with `lake env lean` from the
  repository.
- The desktop shell drops a leading `cd` in some compound commands; a `git switch -c`
  once ran inside `.reference/eflint` (restored to `master` and the branch deleted
  before any file changed). Use `git -C <abs path>` and absolute paths.

## Next

1. Finish the oracle build, generate `eflint-outcomes.txt`, classify the 26 as above,
   update `tolerances.md`, run `tools/battery` to green, open the PR.
2. Take B9, B10, and the D6 reopen (default rules) to Eric; apply the mission-text
   drafts from plan §3a when he words them.
3. Phase 1's remaining exit criteria: spec chapters 002–011 with conformance tests;
   the declarative semantics and the evaluator's agreement proof.
4. Phase 2 per plan §8, starting with `Valid when` (D5) and time (D7).

---

# Handoff — 2026-10-23 (night): mission, decisions D1–D11, redesign plan, AGENTS.md; main at bc4d594

## Where

- Branch `main`, pushed through `bc4d594` ("Add mission, decision log (D1–D11), and the redesign plan"). History was rewritten on 2026-10-23 to drop AI co-author trailers: `003e2a3` → `4a6b106`, `1737ec0` → `bc4d594`. No commit on `main` carries one.
- **Uncommitted at handoff:** `AGENTS.md` (new, canonical rules), `CLAUDE.md` (new, a pointer to AGENTS.md), and edits to `docs/plans/2026-10-22-redesign.md` bringing its wording in line with D4–D11. Commit these three together first.
- `.reference/` (ignored) holds four read-only checkouts: `eflint` (Haskell reference implementation plus `examples-corpus/`), `catala`, `quint`, `symboleo` (`ide/`, `pc/`, identical trees). Nine other candidates were cloned and removed; the choice of four is in the session record, not a decision entry.

## What was done this session

1. **Reviewed `docs/charter-spec.md` and the four references.** Findings that drove everything after: the spec is an architecture tour, not a language reference; it claims `check` reports authorship questions (`AuthorshipQuestion` is dead code) and lists four registers (there are five); the 14 `invariant` spans in the PSA name `INV.*` ids nothing links to a theorem; the v0.3 DSL has no quantities, no individuals, no in-file tests, no time model beyond `Nat`, no modules reachable from a program. eFLINT is the one existing language on Charter's square and was adopted as the core (D2).
2. **`docs/mission.md`** (Eric): three goals in precedence order, fourteen laws with test questions.
3. **`docs/meetings/`**: D1–D11, index, and the briefs (`2026-10-22-briefs-for-ruling.md`). D10 and D11 are Eric's words verbatim and overruled the briefs' predictions.
4. **`docs/plans/2026-10-22-redesign.md`**: language (eFLINT core plus Charter additions), compiler pipeline, target repository layout, process borrowed from With, CLI, migration table, five phases with exit criteria. §9 records that all decisions are ruled.
5. **`AGENTS.md`** drafted in With's structure, translated to Charter; `CLAUDE.md` points to it.

## Design facts the next session must not relearn

- Lean-hosted binary, Lean-free output; `prove` is opt-in and fetches its own toolchain by digest (D1, D9). No author-visible text may name Lean (Law 11).
- `Holds when` = lawful, `Valid when` = effective, defaults to true, so eFLINT programs keep eFLINT's "disabled act still has effects" (D5).
- Derivation is stratified; unstratifiable negation is rejected (D6).
- `Time` and `Duration` are distinct types over `Int` (D7). Time is state on facts; `@ t.` and `tick.` are environment input, never trace events (Law 7).
- Module properties are `Invariant`s in the `.charter` module, proved in `lib/lean/` by name (D8).
- **No model of the protocol outside Charter** (D10): `ProtocolWorldState` and the 16 Lean simulations are deleted when their Charter scenarios pass; each simulation is a scenario naming its span in the protocol's Adversarial Tests section; substrate inputs are environment facts and substrate properties are `SUB.*` assumptions; every division states its rounding.
- **Rule amendment is the `Amend` act** over rule records; ratchets are reflexively entrenched `Immunity … Against Amend`, not invariants; `Extend` never changes rules at run time (D11). Consequence: `Core.Law` becomes part of evaluator state, addressable by rule id. Design the Phase 1 agreement proof with a mutable rule set from the start.
- Two eFLINT tolerances are still unruled and look delegable: report a duty's violation on transition only (not every phrase while it stays violated); error on duplicate declarations instead of silently replacing. Record each as a delegated decision before implementing.

## State of the code (unchanged since 4a6b106)

The v0.3 tree described in the next section still builds and passes: `lake build` 122 jobs clean, trust grep 0, leak grep 0, `charter check` on both `.charter` files 280 ok / 0 FAIL / 0 STALE, `charter sim` 16/16 and 8/8, `charter export` byte-identical to the shipped files. Nothing in the plan has been implemented yet; Phase 0 (process scaffolding) is partly done by the docs above and `AGENTS.md`, and `tools/battery`, `test/gates/`, and `docs/spec/` do not exist.

## Next

Phase 0's remainder, then Phase 1 (the eFLINT core), per the plan §8. First concrete tasks: commit the three uncommitted files; record the two delegated tolerance decisions; create `docs/spec/README.md` with the chapter list and move `docs/charter-spec.md` under `docs/completed/`; vendor `.reference/eflint/tests` and `examples-corpus` into `test/eflint-corpus/` as the Phase 1 target; write `test/gates/` for the trust grep, leak grep, and the Law 11 string check so the battery has something to run.

## Standing rules

`AGENTS.md`. In particular: no AI co-author trailer; never edit an English document or an `Approved` hash to make a check pass; `.reference/` is read-only; `git stash` is banned.

---

# Handoff — 2026-10-18: v0.3.0, the .charter DSL is the program format; main at 4a6b106

The sections below are the v0.3.0 handoff as written before the redesign. They describe the code as it still is; their process instructions are superseded by `AGENTS.md` and their forward-looking statements by `docs/plans/2026-10-22-redesign.md`.

### 1. What this project is

**Charter is a language, and a Charter program is a `.charter` file.** The repository is split into two Lake library targets with a strict dependency direction (`Examples → Charter`, never `Charter → Examples`):

1. **`Charter` (`Charter.lean` + `Charter/`) — The Charter Language, Compiler, Standard Library & CLI harness.**
   A domain-agnostic, formally verified institutional specification language in Lean 4 for specifying, composing, verifying, simulating, and projecting institutional rules across arbitrary signatures `σ : Sig`. `Charter` contains zero references to any specific constitution or protocol: its vocabulary is generic (groups, members, stakeholders, operators, arbiters), its substrate and module docstrings describe patterns rather than any one document, and its test suites use small self-contained toy charters (a residential tenancy, a lending library).
2. **`Examples` (`Examples.lean` + `Examples/`) — Programs Written in Charter (`import Charter`).**
   Each example lives in its own namespace and directory together with its authoritative English text, scenario files, generated views, and a `Cli.lean` that registers it with the harness:
   - **`psa` — *The Protocol of Sovereign Agency*** (`Examples/SovereignAgency.lean`, `Examples/SovereignAgency/*`, namespace `SovereignAgency`): a 61-clause constitution for self-owning AI agents across Definitions (`DEF.01`), Substrate (`SUB.01`), and Laws 1–7, with 14 Design Invariants (`INV.1`–`INV.14`), the Law 7 Meta-Theorem, and 16 adversarial multi-agent world simulations. This was the document the project originally set out to formalize; it is now one example among others.
   - **`commons` — *The Autonomous Compute & Treasury Commons*** (`Examples/AutonomousCommons.lean`, `Examples/AutonomousCommons/*`, namespace `AutonomousCommons`): an 8-clause multi-steward compute and treasury commons composed from all 8 reusable standard-library modules in `Charter/Modules/`.

Core architectural decisions (do not relitigate without the owner):

- **Strict dependency direction and namespace separation.** Nothing under `Charter/` may import, name, quote, or special-case an example. Examples never define anything in the `Charter` namespace (they used to re-export into it; that is gone). If a mechanism in an example turns out to be reusable, generalize it into `Charter/Modules/` or `Charter/Core/` under generic vocabulary first, then have the example instantiate it.
- **The semantics lives in Lean 4, as a deep embedding.** Duties, powers,
  and immunities are *data* (`Charter/Core/Syntax.lean`);
  one interpretation function gives them meaning (`Charter/Core/Semantics.lean`);
  views, explanations, AI prompts, smart-contract guards, and Veil 2.0 state machines
  are all pure projections generated from `Law σ`. Lean's kernel is the only trusted checker.
- **Polymorphic quantitative-to-normative refinement (`WorldSpec σ Q`).**
  `Charter/Core/Refinement.lean` separates quantitative multi-entity state (`Q`)
  from propositional Hohfeldian state (`LegalState σ`), proving step refinement,
  trace refinement, prefix-split authorization equivalence, and idempotent fact
  synchronization once for all signatures `σ` and state types `Q`.
- **Modular institutional composition (`Charter.Modules.*` & `Charter.Core.Composition`).**
  Reusable institutional mechanisms live in `Charter/Modules/` and are composed via
  vertical hierarchy (`L_sub ◁ L_super`), horizontal composition (`composeHorizontal`),
  and functorial signature embeddings (`SigEmbedding`, `Law.lift`).
- **The `.charter` language is the program format (`Charter.Surface.Dsl`, `Lower`, `Unlower`, `Program`).**
  `parseCharterText` → `validate` → `lower` turns a file into a `Law σ_dyn` over the dynamic signature (`Atom` actors/acts, `DynFact` facts with an optional role argument); the CLI runs every subcommand on `.charter` files given as arguments (`Program.ofLowered`). `charter_program "file"` embeds a file as a Lean term at elaboration time (the kernel sees data, never text), which is how each example proves `*_program_is_lean_law`: lowering the shipped `.charter` file equals the Lean law its theorems are about. `unlower` + sentinel parameters (`charter export`) is how those files were produced from the Lean formalizations; the files are now the programs and the Lean modules are their verified companions. The `charter_*` Lean macros (`Charter.Surface.Syntax`) remain for programs written directly in Lean. Lake does not track `.charter` files as dependencies of the Lean module embedding them: after editing one, rebuild the `Program.lean` that embeds it (touch it or `lake build` after removing its `.olean`).
- **`charter_string_table` is a command, not a term.** It emits three top-level definitions (`T.name`, `T.parse`, `T`). The Lean 4.24 code generator miscompiles a `StringTable` built as closures inside one structure literal once the type has ~140+ constructors (segfault in `mi_malloc` at first call); separate top-level `match` definitions are reliable and kernel-reducible.
- **Program-agnostic CLI (`Charter.Tooling.Cli`).** The harness knows nothing about any program. A program registers by building a `Charter.Cli.Program` descriptor (law, clauses, string tables, sample traces, parameter regimes, optional program-specific world simulator, verification ledger); `Main.lean` is a two-line list of registered programs. There is no default `--law`: with no flag, commands run over every registered program, `explain`/`prompt` resolve the program from the actor name, and `eval`/`sim` read the scenario's `"institution"` key.

### 2. The semantic commitments (do not break these)

1. **Three independent questions about every event**: occurrence (any
   event can occur; a `Trace` is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). A
   forbidden act may be valid; a lawful act may be void. Never make a
   forbidden event unreachable.
2. **Violations are facts in the record** (`violations L tr`), **findings
   are institutional events** (a panel's `Power` whose validity mentions
   claim + evidence, whose effect is exactly the breached duty's declared
   `remedies`). In `psa` the link from finding to fact is a named assumption
   (`SoundFindings`), refuted as a theorem by Scenario 7. Keep it that way.
3. **Exceptions come in distinct kinds**: scope (`unlessCond`), authority
   (`unlessPower`: the same act is lawful iff it is the valid exercise of
   a named power), duty-over-duty precedence (`overriddenBy`),
   protection-over-power precedence (`Immunity`). Breach consequences are
   remedies, never exceptions.
4. **The authorized machine is derived.** `Authorized L tr` := every event
   complies. Theorems like `terminate_only_by_power` (psa) and `commons_dissolve_only_by_power`
   are *about* it; it is never a modelling input.
5. **Every norm carries its English** (`Span`), with a `Register` so that
   invariants, acceptances and commentary are traced but never promoted
   to rules. Every clause has an `approvedHash`; `charter check` reports
   staleness and verbatim occurrence against each program's authoritative document.
6. **Trust discipline**: no `sorry`, no `native_decide`, no `axiom`.
   `grep -rn "sorry\|native_decide\|axiom " Charter/ Examples/ Main.lean Charter.lean Examples.lean`
   must be empty. General theorems may depend on `propext`, `Classical.choice`,
   `Quot.sound` only; decided scenarios depend on none (`{}`).

### 3. State of the work (v0.3.0: language/example separation complete)

Everything in `Charter` and `Examples` is implemented and kernel-verified (see `.lake/build/bin/charter verify` for the full ledger):

- **`Charter.Core` (`Charter/Core/`):**
  - `Provenance.lean`, `Syntax.lean`, `Semantics.lean`, `Views.lean` (`stripNamespaces`, `rs`), `Explain.lean`: Law-agnostic normative kernel.
  - `Graph.lean`: Generic affiliation / conflict-of-interest graph (`AffiliationEdge`, `AffiliationGraph`, `isRelated_symm`, `isRelated_ignores_attestation`) and `VerifiedBalanceSheet` (`netVerifiedResources_deducts_all_liabilities`).
  - `Population.lean`: Generic group/member/stakeholder/operator ontology (`GroupId`, `MemberId`, `StakeholderId`, `OperatorId`, `ArbiterId`, `GroupLedger`, `GroupState`, `MemberRecord`, `StakeholderShare`), role-parametric `ParamEntityRef Role`, and the conservation theorems (`transferMemberCarryover_conserves_basis_and_loss`, `attributeCrossGroupInflow_conserves_total`, `forfeitStakeholderInGroup_preserves_innocent_stakeholder`, `group_wide_amendment_requires_every_living_member`, `group_subsidy_bounded_by_budget_regardless_of_members`).
  - `Refinement.lean`: Polymorphic `WorldSpec σ Q` and `GenericWorldState σ Q` with `generic_worldStep_refines_legalStep`, `generic_worldTrace_refines_stateAfter`, `generic_worldAuthorized_iff_prefix_split`, `generic_syncFacts_sound_and_complete`, `generic_syncFacts_idempotent`, and `generic_syncFacts_preserves_unmanaged`.
  - `Composition.lean`: `LawInterface`, `interfaceCompatible`, `interfacesDisjoint`, `SigEmbedding`, functorial `Law.lift` (`Law.lift_id`, `Law.lift_comp`), vertical composition `composeVertical` (`L_sub ◁ L_super`) with `vertical_composition_preserves_super_prohibitions`, `vertical_composition_preserves_super_immunities`, `vertical_composition_preserves_super`, and horizontal composition `composeHorizontal` with `horizontal_frame_non_interference`.
  - `Ratchet.lean`: `RatchetSpec P σ`, `defaultEntrenchedCore`, `ValidAmendmentStep`, `ValidAmendmentTrajectory`, `universal_ratchet_preserves_entrenched_core`, `universal_ratchet_trajectory_safe`, `sweepParameterGrid`, `sweepParameterGrid_sound`, and `renderSweepTable`.
- **`Charter.Modules` (`Charter/Modules/`):**
  - All 8 self-contained standard-library modules (`ResidualLedger`, `CollateralPool`, `CircuitBreaker`, `EntityGroup`, `ExitAndVoice`, `SortitionCourt`, `AttestedLease`, `OracleFeed`) with quantitative state slices, parametric rule builders over arbitrary `σ : Sig`, `SigEmbedding` lift helpers, and kernel-checked module self-tests (`all_8_charter_modules_self_test_pass`). Vocabulary is generic (`ExitParams`, `TestimonyEntry`, `GroupLedgerState`, `groupServiceBudget`, `applyRuling`, …).
- **`Charter.Substrate` (`Charter/Substrate/`):**
  - `Attestation.lean`, `Sortition.lean`, `Settlement.lean`: Cryptographic lease attestation (`ExecutionLease.operatorId`, `quarantinedRestoreOperator`), Sybil-resistant sortition, and contestable valuation settlement (`rulingAmount`, `applyRuling`) primitives.
- **`Charter.Projection` (`Charter/Projection/`):**
  - `Veil.lean`: Veil 2.0 state-machine lowering & `veil_projection_sound_and_complete`.
  - `Prompt.lean`: `AlignmentCard` (`unalienableImmunities`, `institutionalPowers`, `hardProhibitions`, `positiveDeadlines`), `compileAlignmentCard`, `renderSystemPrompt`, `TrainingRow`, `evaluateTrainingRow`, `generateTrainingDataset`, `renderTrainingDatasetJson`, and `training_row_faithful_to_semantics`.
  - `ContractABI.lean`: `requireComplies`, `executePowerGuard`, `executeTraceGuard`, `ContractGuardSpec`, `renderContractJsonABI`, `renderSolidityGuard`, and `contract_guard_sound_and_complete`.
  - `Visualization.lean`: `TimelineStep`, `compileTimelineSteps`, `renderAnnotatedTimeline`, `LawDiff`, `diffLaws`, `renderLawDiff`, `diffLaws_refl_no_removals`, and `diffLaws_entrenched_preserved`.
- **`Charter.Surface`:**
  - `Dsl.lean`: the `.charter` grammar (documented in the module header), `Doc` AST (all `ToExpr`/`DecidableEq`), fuel-based tokenizer and parser (`parseCharterText`), `validate`, and `render` (inverse of parsing on valid documents).
  - `Lower.lean`: `σ_dyn`, `Env`/`Doc.regimeEnv`, `lowerLaw`/`lowerClauses`/`tables`, `Lowered`. `Unlower.lean`: `Naming`, `ExportSpec`, `sentinelValue` (powers of two, so sums of parameters decode), `unlower`, `embeddingOf`. `Program.lean`: the `charter_program` term elaborator. `DslSample.lean`: toy tenancy program decided in the kernel (`sample_render_roundtrip`, `sample_lowered_wellFormed`, `sample_scenario_breach`, ...).
  - `Syntax.lean`: Lean 4 macros (`charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_institution`, the `charter_string_table` command) with `charter_surface_roundtrip`, exercised on a toy tenancy charter (`Charter.Surface.Examples`).
- **`Charter.Tooling` (`Charter/Tooling/Cli.lean`):** `Charter.Cli.Program`, the generic subcommand implementations, `languageLedger`, flag parsing and target resolution, and `Charter.Cli.run`.
- **`Examples` (`Examples/` & `Examples.lean`):**
  - `Examples/SovereignAgency/protocol-of-sovereign-agency.charter` is the program (`Program.lean`: `psaDoc`, `psa_program_is_lean_law`, `psa_program_clauses`; `Export.lean`: `psaExportDoc`, `paramsEnv`, `sentinelParams`). `Examples/SovereignAgency.lean` + `Examples/SovereignAgency/*` (`psa`, namespace `SovereignAgency`) is its Lean companion: all 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01` (50 duties, 110 powers, 1 immunity), Design Invariants `INV.1`–`INV.14`, Law 7 Meta-Theorem, `psa_ratchet_trajectory_safe`, coupled `ProtocolWorldState` (`SovereignAgency.Simulation`), and 16/16 adversarial world simulations (`all_psa_simulations_pass`). `Cli.lean` supplies `psaSim` and `psaLedger`.
  - `Examples/AutonomousCommons/autonomous-commons.charter` is the program (`Program.lean`, `Export.lean` as above). `Examples/AutonomousCommons.lean` + `Examples/AutonomousCommons/*` (`commons`, namespace `AutonomousCommons`) is its Lean companion: distinct 5-role ontology `σ_commons` (`CommonsRole`, `CommonsAct`, `CommonsFact`), 8 verbatim clauses (`COM.LEDGER`–`COM.AMEND`), 13 duties, 20 powers, 1 immunity (`I.COM.EXIT_PROTECTED`), coupled `CommonsWorldState`, institutional invariants, `commons_generic_refinement`, `commons_ratchet_trajectory_safe`, `commons_sub_charter_respects_floor`, and 8/8 module world simulations (`all_commons_simulations_pass`). `Cli.lean` supplies `commonsSim`, the `.charter` path, and `commonsLedger`.

### 4. Verifying a cut

```bash
lake build
grep -rn "sorry\|native_decide\|axiom " Charter/ Examples/ Main.lean Charter.lean Examples.lean   # must be empty
grep -rniE "sovereign|\bpsa\b|commons" Charter/ Charter.lean | grep -viE "commons pool|commonsShare|commonsAllocated|toCommons|Autonomous_Commons"   # language layer names no example
.lake/build/bin/charter check Examples/SovereignAgency/protocol-of-sovereign-agency.charter Examples/AutonomousCommons/autonomous-commons.charter   # 280 ok, 0 FAIL, 0 STALE
for f in Examples/SovereignAgency/scenarios/*.json; do diff <(.lake/build/bin/charter eval --law psa $f) <(.lake/build/bin/charter eval $f Examples/SovereignAgency/protocol-of-sovereign-agency.charter); done   # Lean and .charter paths agree
.lake/build/bin/charter export --law psa | diff - Examples/SovereignAgency/protocol-of-sovereign-agency.charter   # shipped file is the export (empty diff)
.lake/build/bin/charter check                # the linked Lean programs: 0 FAIL, 0 STALE
.lake/build/bin/charter sim                  # 16/16 psa + 8/8 commons world simulations pass
.lake/build/bin/charter verify               # language ledger + both program ledgers
.lake/build/bin/charter prompt steward
.lake/build/bin/charter abi --law commons solidity
.lake/build/bin/charter diff --law psa
.lake/build/bin/charter explore
.lake/build/bin/charter dsl
.lake/build/bin/charter views --law psa > Examples/SovereignAgency/views.txt && git diff Examples/SovereignAgency/views.txt
```
