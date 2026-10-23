# 013 — Invariants and proof

**Status:** draft (2026-10-23). Meaning fixed by plan §2.2.7, D8, D9, D10; wording awaits Eric. Implementation: 13.1–13.2 compliant (Phase 2's sixth slice); 13.3–13.5 pending.

**13.1 Invariants are checked.** `Invariant name When e` is a fact over no components that holds when `e` does (004.9). After every phrase, every invariant that does not hold is reported as a violation; `?name()` asks whether it holds. `test/spec/spec_013_1_invariant_checked.eflint`

**13.2 Exploration.** `charter test --explore N`, or the directive `//! explore: N` in a file, searches from the program's end state and from each scenario's end state: breadth-first over every enabled act instance (lawful behaviour; acts that are not enabled are not explored), up to `N` steps and a bound on distinct states, and reports the shortest trace after which some invariant does not hold as a failed claim naming the invariant and the acts. The search is deterministic: candidates are taken in declaration order, so the same program and depth always give the same trace. A search that finds nothing within its bound is a passing claim and says how many states it visited. `test/spec/spec_013_2_explore_finds_shortest.eflint`, `spec_013_2b_explore_safe.eflint`, `spec_013_2c_explore_lawful_only.eflint`

**13.3 Tags (Law 10, pending `prove`).** Every claim the tool prints carries one of *proved*, *decided*, *checked*, *assumed* and never a fifth. Today every claim of `run`, `test`, and `check` is *checked*: the evaluator judged it at run time. *Decided* and *proved* arrive with `charter prove`.

**13.4 `charter prove` (pending; D9).** A generator, not a mode: it writes a project containing the program plus one theorem per named invariant and expectation, runs the toolchain the binary fetches by digest, and reports per-theorem results through the diagnostic channel; the author sees theorem names and pass/fail, never the engine.

**13.5 Module properties (pending; D8).** A standard-library module's properties are `Invariant`s in its `.charter` file, proved in `lib/lean/` by name and reported as *proved* when a program `Use`s the module.

*Differences from eFLINT:* eFLINT checks invariants after every phrase (13.1 is unchanged); exploration is Charter's, after Quint's `run` simulations.
