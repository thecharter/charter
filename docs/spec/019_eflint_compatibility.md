# 019 — eFLINT compatibility

**Status:** draft (2026-11-06). Fixed by `D2`, `D5`–`D7`, `D12`–`D15`, `D17`, and `Mission Law 12`. Tested continuously by `test/eflint-corpus/` (196 upstream files) against `eflint-outcomes.txt` and `tolerances.json` / `tolerances.md`.

**19.1 Unified stratified-eFLINT superset (`Law 12`, `D2`, `D17`).** Charter is a strict syntactic and semantic superset of well-stratified eFLINT 4.1 (`docs/reference/eflint.pdf`). Every `.eflint` and `.charter` file is tokenized and parsed by one unified contextual front-end (`002.9`): multi-word additions (`Valid when`, `Except under`, `Due within`) cannot collide with single-word atoms; single-word uppercase Charter keywords (`Document`, `Clause`, `Approved`, `Text`, `Norm`, `Definition`, `Acceptance`, `Commentary`, `From`, `Immunity`, `Against`, `Unless`, `Duration`, `Held`, `Param`, `Module`, `Use`, `As`, `Scenario`) remain valid unquoted atoms in `Identified by` lists and expressions; and lowercase `tick` remains a valid event/act identifier, advancing the clock on a bare `tick.` phrase only when no type `tick` is declared in scope.

**19.2 Inherited semantics.** All core eFLINT 4.1 constructs retain their upstream spelling and transition semantics:
1. `Fact`, `Var`, `Function`, `Bool`, `Predicate`, `Invariant`, `Placeholder`, `Act`, `Physical`, `Event`, `Duty`, and `Extend` declarations (`003`–`008`);
2. `Closed` (default false) versus `Open` (missing input `CHR100`) world assumptions (`003.6`);
3. `Holds when` (domain derivation), `Derived from` (generative derivation), and `Conditioned by` (domain filter) (`004`);
4. Simultaneous effect merging with `create > terminate > obfuscate` precedence (`005.3`);
5. Default institutional validity `Valid when True` on `Act` so disabled actions apply their state effects as in eFLINT unless `Valid when` or an `Immunity` is explicitly declared (`005.2`, `005.9`, `D5`).

**19.3 Upstream defects fixed and well-foundedness boundary.** Every behavioral divergence from Haskell `eflint-4.1.0.1` on the 196-file vendored corpus is recorded in `test/eflint-corpus/tolerances.json` and `tolerances.md`. An unlisted divergence fails `charter test --expect ... --tolerate ...`, and a listed tolerance that ceases to differ also fails so stale tolerances are removed immediately:

| Decision | Upstream `eflint-4.1.0.1` behavior | Charter behavior | Corpus impact |
|---|---|---|---|
| `D6(a)` | Unstratified inflationary pass in alphabetical type-name order (`Saturation.hs`), reading sums/negations before dependencies are derived | Topological stratification (`Stratify.strata`), saturating each stratum to a fixpoint before higher strata | Upstream fails 3 of its own tests (`deriv_sum1a`, `deriv_sum1b`, `from_not_enabled2`); Charter passes |
| `D6(b)` | Cyclic self-negation (`p` derived from `!p` in `archetypes.eflint`) takes an imperative first-pass answer with no post-state equivalence | Rejected statically with `CHR020` naming the cycle (`004.6`) | Upstream passes, Charter rejects `archetypes.eflint` and the 23 files that include it (24 files) |
| `D12` | Violated duties re-emitted after every subsequent phrase while still violated | Reported on the transition edge into violation; `Violated(d)` unchanged (`006.2`) | 0 test-mode differences |
| `D13` | Creating `+a(...)` through `Placeholder a For b` tags the instance with `a`, hiding it from rules over `b` | Canonicalizes through `chaseAlias` to base type `b` (`003.9`) | Upstream fails `with2.eflint`; Charter passes |
| `D14` | GLL parser ambiguity on `e When c` with arithmetic comparison misparses `(e When d) + 1` | `When`/`Where` has lowest expression precedence (`010.5`) | Upstream fails 4 `caretaker_contract` files; Charter passes |
| `D15` | An `Act` over non-enumerable `Int` with `Holds when` enumerates empty held `Int`s and stays permanently disabled | Judges `Holds when` per queried/performed instance with components bound (`005.5`); warns `CHR025` on binders | 0 corpus differences |
| `B9` | Redeclaring a type silently replaces the prior declaration | Same runtime replacement plus warning `CHR019` (`003.11`) | 0 test-mode differences |
