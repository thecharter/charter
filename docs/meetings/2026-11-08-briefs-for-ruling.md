# Briefs for rulings, 2026-11-08 (`B27`–`B29`, alongside `B9`)

**Status:** all four ruled as predicted by Eric on 2026-11-08 (`D39`–`D42`).

## B27. Independent declarative phrase-step semantics (`#65`, `Law 9`, `Law 10`)

- **Ruling (`A`, `D41`):** Tighten `docs/claims.json` immediately so driver-structural claims (`evalPhrase_sound`, `evalPhrase_complete` over `DeclPhraseStep`) are explicitly distinguished from evaluator-independent semantic theorems, and introduce `src/Charter/Core/Meaning.lean` (`DeclEval`, `DeclCPhraseMeaning`) with zero `Charter.Eval` imports, proving `M.eval` and `Interp.evalClockStep` / `Interp.semPhrase` sound and complete against them (`declEval_implies_eval`, `eval_implies_declEval`, `declCPhraseMeaning_agrees_with_step`).
- **References:** `.reference/eflint/src/Language/EFLINT/{Eval.hs,Interpreter.hs}`, `.reference/catala/compiler/{index.mld,dcalc/}`, `.reference/quint/evaluator/`.

## B28. Honesty boundary and target semantics for `solidity`, `quint`, and `prompt` (`#66`, `Goal 3`, `Law 9`, `Law 10`, `D28`)

- **Ruling (`A`, `D42`):** Enforce `Law 10`'s strict four-tag taxonomy (`proved`, `decided`, `checked`, `assumed`, plus `advisoryOnly: true` on `prompt`); introduce mechanized `SolidityIR` (`src/Charter/Project/SolidityIR.lean`) compiling real finite/scalar guard predicates and storage writes with proved soundness (`execSolStep_sound`, `compileScalarExpr_sound_for_declEval`); keep emitted `.sol`/`.qnt` surface texts tagged `checked` with 3-way stateful differential validation; and add `.github/workflows/differential-targets.yml` (`solc`/Foundry, `quint`, `z3`).
- **References:** `.reference/catala/compiler/index.mld`, `.reference/quint/quint/src/compileToTlaplus.ts`, `.reference/symboleo/ide/.../SymboleoGenerator.xtend`.

## B29. `Document ... Rank n` *lex superior* conflict resolution (`#73`, `012.1`, `Law 4`, `Law 5`, `Law 8`, `Law 13`)

- **Ruling (`A`, `D40`):** `Document ... Rank n` (`Rank 1 > Rank 2`, smaller integer = higher authority) automatically resolves otherwise-unranked cross-document `Default`/`Exception` conflicts at `Resolve` time (`Spec.rankEdges`), keeping `Core.Defeasible` and `evalCompiledDAG_eq_spec` unchanged, preserving explicit `Overrides`/`Priority` statutory delegation and same-rank `Conflict` (`T21`), and surfacing rank edges in `charter check --verbose`, `charter doc`, and `charter explain`.
- **References:** `test/eflint-corpus/examples/dex-dipg/gdpr_union.eflint`, `.reference/catala/compiler/shared_ast/interpreter.ml:1006`.
