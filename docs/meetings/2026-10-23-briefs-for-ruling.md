# Briefs for rulings, 2026-10-23

Source: `docs/plans/2026-10-22-redesign.md` §2.1 lists two eFLINT differences still unruled. D12 (duty violation reporting) was delegated and recorded; the brief below is the other one. It is not delegable: it decides what a program *means* when a type is declared twice, which is semantics, and the committed prediction is below 75%.

---

## B9. Duplicate declarations (blocks nothing in Phase 1; implementation keeps eFLINT's meaning with a warning until ruled)

**Question.** When a program declares a type a second time (`Fact x …` after an earlier `Fact x …`, not an `Extend`), does the second declaration replace the first (eFLINT), or is it an error?

**References.**
- eFLINT replaces: `Spec.hs` `decls_union old new = M.union new old` (right-biased) and `StaticEval.hs` `execute_decl (CTypeDecl ty tspec) = M.insert`. The earlier declaration's derivation rules, conditions, and domain are discarded. eFLINT's own test suite exercises this deliberately: `tests/truth/infinite_even.eflint` declares `even` over `int` with one derivation, queries it, then redeclares `even` over `1..10` with another and expects the second meaning; `tests/parallel-comp/no_violations.eflint` declares `bar Identified by String Holds when True` and then `bar Identified by Amy, Bob, Cho` (comment `// #1`), and its invariant `no-odd-bar` only holds because the `Holds when True` of the first declaration is gone. Both files pass in eFLINT only under replacement.
- Catala: redefining a scope variable is an error unless the redefinition is an exception with a label (`compiler/desugared/` "conflicting definitions").
- Quint: a second definition of a name in the same scope is a static error ("conflicting definitions").
- Symboleo: one contract, no redeclaration.

**Mission.** Law 12: every eFLINT program is a Charter program, and the vendored corpus is the test; two corpus files rely on replacement. Law 13: two ways to say one thing are a defect; `Extend` already says "add to this type", so a second `Fact x` that *replaces* is a second spelling of "define x", not of "extend x". Law 5: rules are data; a redeclaration silently discards records, which no reader of the program sees. Law 8 and the plan §3 "keep going after errors" favour a loud diagnostic in either case.

**Fit.** An error is the most Charter-like (one declaration per name; `Extend` for additions) and is what the plan's §2.1 text says ("we error"). But it makes two corpus tests fail, which D2 says must be listed as tolerated differences with this decision's number, and it contradicts eFLINT's tests, which treat redeclaration as a feature. Replacement with a warning keeps D2 literal and makes nothing silent.

**Prediction.** 60% that Eric rules **error** (CHR019 as an error; `tests/truth/infinite_even.eflint` and `tests/parallel-comp/no_violations.eflint` listed in `test/eflint-corpus/tolerances.md`), 40% replacement-with-warning. Below the delegation threshold, so the implementation keeps eFLINT's meaning (replacement) and emits CHR019 as a **warning** naming both declarations until the ruling. Moving to the predicted ruling is: raise CHR019 to an error, delete the replacement path in `Resolve`, add the two tolerance lines.

**Reopens if.** The PSA rewrite needs to restate a type (it should use `Extend` or `Amend`, D11).
