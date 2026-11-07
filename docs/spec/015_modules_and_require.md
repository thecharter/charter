# 015 — Modules and require

**Status:** approved (Eric, 2026-11-06; Charter 1.0.0). Fixed by D8 and D26. Implementation: compliant (`src/Charter/Resolve/Static.lean`, 12 modules under `lib/*.charter`, `src/Charter/Modules/`).

**15.1 `#require` and `#include`.** Files compose by `#require "f"` (once per file) and `#include "f"` (every time), as 011.7 says; this is eFLINT's mechanism and is unchanged.

**15.2 Modules.** `Module name(p₁, p₂) { declarations }` declares a parameterised block of declarations and introduces nothing by itself. Its body is any sequence of declaration frames (facts, acts, duties, immunities, invariants, placeholders, parameters, nested `Use`s), each block ended by `.` or by the next frame. The parameters are type names the body refers to. `test/spec/spec_015_1_module_use.eflint`

**15.3 Instantiation.** `Use name(a₁, a₂) [As prefix]` expands to the module's body with each parameter `pᵢ` replaced by the type `aᵢ` everywhere a type name occurs (domains, terms, effects, conditions, derivations, duty clauses, `Against`, `Except under`), and, when `As prefix` is given, every name the module declares (its facts, acts, duties, immunities, placeholders, parameters) renamed to `prefix-name`, in the body and in every reference to it. The expansion is then declared like any block, so two `Use`s with different prefixes instantiate a module twice (Quint's `import … as`). A `Use` may precede its `Module` in the same block; a module's own `Use`s expand with it. `test/spec/spec_015_1_module_use.eflint`, `spec_015_2_module_unprefixed.eflint`, `spec_015_4_module_rules_renamed.eflint`

**15.4 Errors.** A `Use` of an undeclared module, or with the wrong number of arguments, is CHR023. `test/spec/spec_015_3_use_errors.eflint`

**15.5 The standard library.** The eight patterns of `Charter/Modules/` (residual ledger, collateral pool, circuit breaker, entity group, exit and voice, sortition court, attested lease, oracle feed) are `.charter` modules under `lib/` (`.eflint` until the extension moves, 011.10); every property of a module is an `Invariant` declared in its file, checked after every phrase and explored by `charter test` (013.1–13.2), and is to be proved in `lib/lean/Modules/` by name and reported as *proved* when a program `Use`s the module (D8; pending `prove`, 013.4). Each module is exercised by a program under `test/lib/` that `#require`s it, `Use`s it with a prefix, and runs scenarios with `//! explore: 1`; `lib/README.md` states the conventions (environment inputs are facts, D10; an amount an act names is a type parameter, brief B11). `test/lib/*.eflint`

*Spelling:* the prefix joins with `-` (`a-balance`), since identifiers may contain `-` and `.` is projection.
