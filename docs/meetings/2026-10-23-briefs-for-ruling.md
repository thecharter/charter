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

---

## B10. Who signs the artifact's certificate, and what does the server check it against (blocks the artifact format, plan §3a; decide before Phase 3)

**Question.** Under the compiler/server split (plan §3a, 2026-10-23), a compiled law takes office in a server only with a verified certificate. Three ways to verify it: (a) the server embeds the kernel and re-checks the proofs (heavy; the server then carries the engine, against the spirit of the operator law); (b) a trusted compiler signs the artifact and the server checks the signature (reintroduces trust in whoever ran the compiler, one level up); (c) the artifact carries a proof certificate that the server verifies with a small checker, itself proved against the kernel once (the honest middle; what independent proof checkers for Lean's export format do).

**References.** eFLINT's server (`.reference/eflint/src/Server.hs`) loads source and compiles it at runtime: no artifact, no certificate, operator sees source. Catala compiles to a target language and ships no certificate; its proof plugin runs at development time. Quint ships ITF traces as artifacts, unsigned. Symboleo has no runtime.

**Mission.** Law 10 (one trusted checker; every claim tagged), Law 11 (the author never sees the engine), and the proposed operator law (the operator never sees source; replay is byte-identical). Goal 3 as restated in the plan: one artifact in three hosts.

**Fit.** (a) satisfies Law 10 directly but makes the server the engine's host; (b) fails Law 10's spirit (a signature is trust, not a check); (c) keeps the trusted base to one proved checker and one proved evaluator, both in the server, and lets anyone replay.

**Prediction.** (c) at 70%: a proof certificate in the artifact, verified by a checker that is proved sound against the kernel and shipped inside the server; the server's answers are then tagged *checked* under the sharpened definition the plan proposes for Law 10. Below the delegation threshold and about trust, so it waits for Eric. Nothing in Phases 1–2 depends on it; the artifact format (Phase 3's first step) does.

**Reopens if.** The certificate size or check time makes amendment impractical on-chain, in which case the guard host verifies off-chain and posts the artifact hash.
