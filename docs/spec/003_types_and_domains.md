# 003 — Types and domains

**Status:** draft (2026-10-23). Meaning fixed by D2 (eFLINT `Spec.hs`, `StaticEval.hs`), D7 (time types deferred to Phase 2), D13; wording awaits Eric. Implementation: compliant; all tests pass. Resolution owns names, types, and arities (`src/Charter/Resolve/Static.lean`).

**3.1 Kinds.** A type is a `Fact`, an `Act`, a `Duty`, or an `Event`; `Bool`, `Predicate`, `Invariant`, `Var`, `Function`, and `Physical` declare facts and acts with the restrictions below. A `Fact` with no `Identified by` has the string domain. `test/spec/spec_003_1_default_string_domain.eflint`

**3.2 Domains.** A domain is `String`, `Int`, an enumeration of atoms (`A, B`), of integers (`1, 2, 3` or `1..5`), of single-character strings (`'a'..'z'`), or a product of components (`a * b`). An enumeration is *enumerable*: `+x.` with `x` free creates every instance of the type; `String` and `Int` are not, and a free variable over them ranges over the instances that hold (004.7). `test/spec/spec_003_2_enumerations.eflint`

**3.3 Products and variables.** A product's components are variables: a type name with a decoration (`person1 * person2`). An application gives arguments positionally in component order or by name (`f(a = e, b = e')`); a component not given stays free and is bound by the surrounding construct. The wrong number of positional arguments is CHR011. `test/spec/spec_003_3_products.eflint`, `spec_003_3b_arity_error.eflint`

**3.4 Primitive application.** A type with a primitive domain is applied to exactly one positional argument of that domain (`x(5)`); anything else is CHR018. `test/spec/spec_003_4_primitive_application.eflint`

**3.5 Built-in types.** Every program declares `int` (`Int`), `string` (`String`), and `actor` (`String`, the actor type). An `Act` or `Physical` without `Actor` has the component `actor`. Instances of built-in types hold only when assigned, like any other. `test/spec/spec_003_5_builtins_and_default_actor.eflint`

**3.6 Open and closed.** A type is closed unless declared `Open`. An instance of a closed type with no assignment does not hold. An instance of an open type with no assignment is *missing input*: if the type has assigned instances, a free variable ranges over those that hold; a direct question about an unassigned instance is CHR100 (Law 6: the world is input). `Extend Fact x Closed` closes an open type for good: a later `Extend … Open` does not reopen it; a type that was closed by default may be opened. `test/spec/spec_003_6_closed_default_false.eflint`, `spec_003_6b_open_missing_input.eflint`, `spec_003_6c_open_with_assignments.eflint`

**3.7 `Var` and `Function`.** When an instance of a `Var` type is created, every other instance of the type is made false; of a `Function` type (a product of two components), every other instance with the same first component. `test/spec/spec_003_7_var_and_function.eflint`

**3.8 Domain constraints.** `Where e` (or `When e` on a `Fact`) restricts the instances of a type to those whose components satisfy `e`. An element outside the constraint is not an instance: it is never created, enumerated, or derived. `test/spec/spec_003_8_where_constraint.eflint`

**3.9 Placeholders.** `Placeholder a For b` makes `a` another name for `b`, usable wherever a type name is, including as a differently named component of a product. An instance named through a placeholder is an instance of the aliased type (D13). A placeholder may name a type declared later in the same declaration block. `test/spec/spec_003_9_placeholder.eflint`

**3.10 Extending a domain.** `Extend Fact x Identified by …` (or `Domain …`) adds atoms to a string enumeration or integers to an integer enumeration, and turns `String`/`Int` into an enumeration. On a product type, or on an act, duty, or event, it is CHR014. `test/spec/spec_003_10_extend_domain.eflint`, `spec_003_10b_extend_domain_error.eflint`

**3.11 Redeclaration.** Declaring a type a second time replaces the first declaration entirely and warns CHR019. (B9, awaiting ruling: whether this becomes an error.) `test/spec/spec_003_11_redeclaration_warns.eflint`

**3.12 Static types.** Resolution gives every term one of: string, integer, boolean, or instance of a named type, and inserts the conversions of 010.4. A value where another type is needed, with no conversion, is CHR012.

*Phase 2:* `Time` and `Duration` as distinct types over `Int` (D7); `Param` as a `Var` fact (D11).
