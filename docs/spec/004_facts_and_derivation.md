# 004 — Facts and derivation

**Status:** draft (2026-10-23). Meaning fixed by D2 and D6; wording awaits Eric. Implementation: compliant (`src/Charter/Eval/Interpreter.lean`, `Stratify` and `Saturate`); all tests pass.

A *state* assigns truth values to instances. An assignment comes from a phrase (`+e`, `-e`), from an act's effects (005), or from derivation; a derived truth is recomputed after every phrase, an assigned one stays until changed. The three state questions of an instance are whether it holds, whether it is enabled (005.5), and whether it is violated (006.2).

**4.1 `Holds when`.** A type with `Holds when e` holds for every instance whose components satisfy `e`. Several conditions separated by commas, or several `Holds when` clauses, are alternatives. `test/spec/spec_004_1_holds_when.eflint`

**4.2 `Derived from`.** A type with `Derived from e` holds for every instance that `e` produces. Free variables of `e` are bound to every valid instance of their types, as are the variables of a `(Foreach xs: e)`. The produced value must be an instance of the type or convert to one (010.4). `test/spec/spec_004_2_derived_from.eflint`

**4.3 Assignment beats derivation.** An instance with an explicit assignment keeps it: `-a(A)` makes `a(A)` not hold even while a rule derives it; `~a(A)` removes the assignment and the rule applies again. `test/spec/spec_004_3_assignment_beats_derivation.eflint`; proved: `Charter.State.derive_assigned`, `derive_unchanged`, `deriveAll_unchanged` (`src/Charter/Eval/Properties.lean`)

**4.4 Derived facts are recomputed.** After every phrase all derived facts are discarded and re-derived from the assignments then in force. A derived fact whose ground is gone is gone. `test/spec/spec_004_4_recomputed_each_phrase.eflint`

**4.5 Fixpoint.** A rule may read the type it derives; derivation is the least fixpoint, so a transitive closure needs no bound. `test/spec/spec_004_5_fixpoint.eflint`; proved (the fixpoint half): `Charter.Saturate.saturateStratum_fixpoint`, the state the evaluator returns for a stratum is unchanged by one more pass (`src/Charter/Eval/Properties.lean`); leastness awaits the declarative semantics

**4.6 Stratification (D6).** A rule *reads* a type when it mentions one of its instances as a condition (`Holds`, an instance used as a boolean, `Enabled`, `Violated`), binds a variable of the type, or projects from it. A read under `Not`, under the body of `Forall`, or under the body of `Count`, `Sum`, `Max`, `Min` is *negative*. The derived types are ordered so that every type comes after the types it reads; types that read each other only positively form one stratum and are derived together to their least fixpoint; a negative read of a type that reads back, directly or indirectly, is rejected with CHR020 naming the types, before anything is evaluated. The result does not depend on the names of the types. `test/spec/spec_004_6_stratified_order_independent.eflint`, `spec_004_6b_negation_over_lower_stratum.eflint`, `spec_004_6c_negative_cycle_rejected.eflint`

**4.7 Non-enumerable types.** A free variable or binder over a type whose domain is not enumerable ranges over the instances that hold (for an open type, over the assigned instances, 003.6). A `Holds when` on such a type therefore derives nothing until some instance holds; in particular an act with an `Int` component is never enabled by `Holds when` (brief B11, `docs/meetings/2026-10-24-briefs-for-ruling.md`). Conversely a binder over a type whose components are all enumerable ranges over the whole domain, whether or not the instance holds (003.2): in a rule, `(Exists p: p.a == a)` is true whenever the domain has an element with that component, and the body must say `p` (010.4) or use the application form `p(a, b)` to mean the instance that holds. `test/spec/spec_004_7_non_enumerable_range_over_held.eflint`

**4.8 `Conditioned by`.** A type's `Conditioned by` conditions are preconditions over its components. An instance that fails them is not derived by the type's rules and is not enabled (005.5); its assigned truth is unaffected. `test/spec/spec_004_8_conditioned_by.eflint`

**4.10 Origins (Law 6).** Every assignment records where it came from: *asserted* by a phrase, *supplied by the environment* (an assignment to an open type), made *by an act* (its effects), or *derived* by a type's rules; derived facts carry the rules. `?why e` prints, for each instance of `e`, whether it holds and since when, and this origin. No evaluator path creates a fact without one. `test/spec/spec_004_10_why.eflint`

**4.9 Invariants and predicates. `Predicate p When e` is a fact over no components holding when `e` does; `Invariant i When e` is the same and is additionally checked after every phrase, a violation being reported when it does not hold (006.6 reports; Phase 2 adds `charter test --explore`).

*Differences from eFLINT:* 4.6. eFLINT's `Saturation.hs` is an inflationary fixpoint over types in alphabetical order that evaluates negation against intermediate states; three of its own tests fail under it and pass here (`test/eflint-corpus/tolerances.md`, D6 (a)), and one of its examples, a default rule, is rejected here (D6 (b); the reopen condition of D6 is met and is Eric's).
