# D39–D42 — Duplicate-Declaration Refusal (`B9`), `Document Rank` *Lex Superior* (`#73`), Relational `Core.Meaning` (`#65`), and `SolidityIR` Guard Semantics (`#66`)

**Laws:** 4, 5, 8, 9, 10, 11, 12, 13, 14 (`docs/mission.md`). Briefs `B9`, `B27`–`B29`.
**Date:** 2026-11-08
**Status:** ruled as predicted (Eric, 2026-11-08)

## Rulings Implemented

### D39 (`B9`, `003.11`) — Duplicate type declarations are refused statically with `CHR019`
- **Ruling:** Redeclaring an already-declared type, `Param`, or `Amount` in the same specification is a static error (`CHR019`), deleting silent replacement in `Resolve.executeDecls`. Static additions use `Extend`; runtime rule replacement uses `Amend ... Repeals ... Installs` (`D11`), closing the non-`Amend` redeclaration bypass on entrenched rules.
- **Corpus impact:** 19 upstream eFLINT files across 8 root redeclarations (`infinite_even`, `no_violations`, `insurance_insurer`, `buyer_seller`, `help_with_homework`, `dex-dipg/*`, `smart-access/usage-control/*`, `symboleo-meat-sales/*`) are recorded in `tolerances.json` / `tolerances.md`.
- **Reopens if:** never for rules; template specialization uses `Extend` or `Param`s.

### D40 (`B29`, `#73`, `012.1`) — `Document ... Rank n` resolves unranked cross-document `Default`/`Exception` conflicts (*lex superior*)
- **Ruling:** Smaller `Rank` integers carry higher authority (`Rank 1` prevails over `Rank 2`). Whenever two `Default`/`Exception` rules on the same type have no explicit `Overrides`/`Priority` path between them and are grounded in clauses of `Document`s with distinct ranks `k₁ < k₂`, `Resolve` records a `RankPriorityEdge` on `Spec.rankEdges` and includes `(r₁, r₂)` in `TypeSpec.syncDefeasibleDAG`. Explicit `Overrides`/`Priority` edges supersede rank edges (allowing statutory delegation), same-rank rules still produce `Conflict` (`T21`), and `check --verbose`, `doc`, and `explain` surface every rank decision (`spec_012_9c`).
- **Reopens if:** a multi-document specification requires per-fact disabling of `Document Rank`.

### D41 (`B27`, `#65`, `Law 9`, `Law 10`) — Evaluator-independent relational semantics (`Charter.Core.Meaning`) and candid `claims.json`
- **Ruling:** `src/Charter/Core/Meaning.lean` (enforced by `spec-inventory.sh` to import zero `Charter.Eval.*` modules) defines fuel-free, cache-free inductive relations `DeclEval` and `DeclCPhraseMeaning`. `Charter.Eval.Properties` proves both directions (`declEval_implies_eval`, `eval_implies_declEval`, and `declCPhraseMeaning_agrees_with_step`), and `docs/claims.json` explicitly distinguishes `DeclPhraseStep` driver-structural claims from evaluator-independent semantic claims.
- **Reopens if:** nondeterministic quantifier/trigger steps are lifted into `DeclCPhraseMeaning` alongside `#74`'s slice framing theorem.

### D42 (`B28`, `#66`, `Goal 3`, `Law 9`, `Law 10`, `D28`) — Strict `Law 10` target tags, mechanized `SolidityIR`, and differential CI
- **Ruling:** All projection outputs, `docs/spec/017_projections.md`, and `docs/claims.json` use strictly `Law 10`'s four tags (`proved`, `decided`, `checked`, `assumed`, plus `advisoryOnly: true` on `prompt`). `src/Charter/Project/SolidityIR.lean` compiles finite/scalar `CIR` actions into typed `SolContract` functions with real on-chain predicate guards and half-open `[start, end)` storage mutations, proves `execSolStep_sound` and `compileScalarExpr_sound_for_declEval` in Lean, runs 3-way stateful differential parity (`SolidityIR` vs. `GuardIR` vs. `charter-server`), and adds `.github/workflows/differential-targets.yml` + `tools/differential-targets-check` (`solc`/Foundry, `quint`, `z3`).
- **Reopens if:** full Yul/EVM bytecode-level verification replaces `SolidityIR` pretty-printing.
