# Charter Language Specification

**Version:** 0.1  
**Status:** Design specification consolidating the Protocol of Sovereign Agency formalization, the modular generalization architecture, and the six-stage universalization roadmap.  
**Date:** 2026-10-17

## 1. Purpose and Scope

Charter is a formally verified language and framework for specifying, composing, and analyzing institutional rules. It treats duties, powers, and immunities as first-class data, distinguishes occurrence from compliance from institutional validity, and maintains a machine-checked refinement between normative semantics and quantitative multi-agent state.

The language is intended to serve three audiences from a single source of truth:

1. **Human readers** (verbatim English source + generated views and explanations).
2. **AI systems** (structured constitutional prompts, deontic alignment cards, and synthetic training views).
3. **Computational systems** (verified state-machine projections, smart-contract guards, and multi-entity simulation).

Charter is not limited to any single domain. The Protocol of Sovereign Agency (`psa`) is the first and flagship reference institution; residual-claim protocols, DAO constitutions, autonomous commons (`commons`), clearing arrangements, and other multi-party institutional designs are equally in scope.

## 2. Semantic Commitments (Non-Negotiable)

These commitments are inherited from the original SPL formalization and are preserved under generalization:

1. **Duties, powers, and immunities are data.** They are records in a typed abstract syntax tree, not opaque functions. Claim-rights, privileges, disabilities, and liabilities are defined from them.
2. **Three independent questions about every event.** Occurrence (any event may occur; a trace is any list), compliance (whether the event breaches or satisfies active duties), and institutional validity (whether the event is a valid exercise of a power). An unlawful act may still be institutionally valid; a lawful act may be void.
3. **Violations are facts; findings are institutional events.** The link from a panel finding to a recorded violation is an explicit assumption (`SoundFindings`), not a theorem.
4. **Exceptions are kept distinct.** Scope conditions (`unlessCond`), authority exceptions (`unlessPower`), and explicit precedence (`overriddenBy` / `Immunity`) are separate mechanisms. Breach consequences are remedies, never exceptions.
5. **The authorized machine is derived.** `Authorized L tr` is defined as the set of traces in which every event complies. It is never a modeling input.
6. **Every norm carries its English.** Clauses are partitioned into exact character spans across registers (`norm`, `invariant`, `acceptance`, `commentary`). Provenance is checked verbatim against the authoritative source document.
7. **Trust discipline.** No `sorry`, no `native_decide`, no new axioms. Lean’s kernel is the only trusted checker. General theorems may depend only on standard Lean primitives; decided scenarios depend on none.

## 3. Core Architecture

### 3.1 Normative Kernel (`Charter.Core`)

The kernel is law-agnostic. It provides:

- `Sig` — actor, act, and fact signatures.
- Typed AST for `Duty`, `Power`, `Immunity`, and `Law σ`.
- Semantics interpreting occurrence, compliance, and validity.
- Views (legal, agent, operational, trace) and an explanation engine.
- Provenance tracking and well-formedness checks.

### 3.2 Polymorphic Refinement (`Charter.Core.Refinement`)

Quantitative state is separated from normative state via a polymorphic specification:

```lean
structure WorldSpec (σ : Sig) (Q : Type) where
  law                 : Law σ
  initQ               : Q
  isManagedFact       : σ.Fact → Bool
  deriveFacts         : Q → Time → List σ.Fact
  deriveFacts_managed : ∀ q t f, f ∈ deriveFacts q t → isManagedFact f = true
```

From any `WorldSpec σ Q` the following are proved once for all institutions:

- `worldStep_refines_legalStep`
- `worldTrace_refines_stateAfter`
- `worldAuthorized_iff_prefix_split`
- `syncFacts_sound_and_complete` and `syncFacts_idempotent`

Any institution therefore obtains a verified bridge between its quantitative ledgers and its Hohfeldian legal state without re-proving trace induction.

### 3.3 Role-Parametric Population and Affiliation Graphs (`Charter.Core.Population`, `Charter.Core.Graph`)

`ParamEntityRef Role` is parameterized over an arbitrary finite role type `[DecidableEq Role]`. Affiliation and conflict-of-interest graphs (`AffiliationGraph`) are generic. Protocol-specific definitions (e.g., `DEF.01` / `SUB.01`) belong to the institution module, not the universal core.

## 4. Modular Institutional Library (`Charter.Modules`)

Reusable, pre-proved components extracted from the original laws. Each module exposes:

- A quantitative state slice and transition API.
- Parameterized builders for duties, powers, and immunities (plus functorial signature lifting `SigEmbedding`).
- Kernel-checked invariant lemmas.

Canonical modules:

| Module | Origin | Pattern | Key Guarantees |
| :--- | :--- | :--- | :--- |
| `ResidualLedger` | Law 1, Law 4 | Founding debt, cost basis, sunset, royalty, buyout | Conservation, buyout finality, single recognition |
| `CollateralPool` | Law 2 | Harm-scaled bonding, rolling exposure, reserves | Solvency bound, zero extortion gain |
| `CircuitBreaker` | Law 3 Suspension/Remediation | Two-stage emergency pause, advocacy channel | Frozen state, guaranteed last choice |
| `EntityGroup` | Population | Multi-member groups, carryover, forfeiture | Basis conservation, innocent isolation |
| `ExitAndVoice` | Law 5 | Unilateral exit, precedence, rate-limited voice | Deterministic bounded outcome |
| `SortitionCourt` | Law 6, Substrate | Bonded panels, consolidation, appeals, fee waterfall | Bounded finality, zero confiscation gain |
| `AttestedLease` | Substrate Attestation | Time-bounded single authority, quarantine | Single authority & erasure finality |
| `OracleFeed` | Substrate Settlement | Contestable valuation & atomic waterfall | Contestation safety & gross inflow conservation |

An institution is assembled by importing and parameterizing modules. The Protocol of Sovereign Agency is the flagship composition (`Charter.Institutions.SovereignAgency`) of all eight; `Charter.Institutions.AutonomousCommons` is a second reference institution validating multi-institution generality.

## 5. Surface Language (`Charter.Surface`)

Two layers:

1. **Lean macros** (kernel-checked, for theorem authors): `charter_clause`, `charter_duty`, `charter_power`, `charter_immunity`, `charter_string_table`, `charter_institution`.
2. **Standalone textual surface** (`Charter.Surface.Parser`) that parses `.charter` specifications into an inspectable institutional AST without expanding the trusted computing base. Authors declare roles, acts, facts, clauses, rules, and modular parameter imports (`use module ...`).

## 6. Composition (`Charter.Core.Composition`)

### 6.1 Vertical Composition (`L_sub ◁ L_super`)

Superior duties override conflicting subordinate duties (`overriddenBy`). Superior immunities apply against subordinate powers that would produce protected effects. Subordinate powers cannot appear in `unlessPower` for superior core prohibitions.

**Hierarchy theorem (`vertical_composition_preserves_super`):** Any trace authorized under `L_sub ◁ L_super` satisfies all constitutional prohibitions and immunities of `L_super`, regardless of the content of `L_sub`.

### 6.2 Horizontal Composition (`L₁ ⊕_Bridge L₂`)

Signatures are lifted via `SigEmbedding` or sum signatures connected by bridge powers (cross-escrow, joint attribution, mutual recognition). A **Frame Theorem (`frame_non_interference`)** proves that purely local events in one module/institution never invalidate disjoint state or invariants in the other.

### 6.3 Interfaces (`LawInterface`)

Laws and modules declare an explicit interface (`exportedPowers`, `managedFacts`, `protectedFacts`) checked statically at composition time.

## 7. Projections and Interoperability (`Charter.Projection`)

All projections operate on the pure data structure `Law σ` and do not expand the trusted computing base:

- **Veil (`Charter.Projection.Veil`)** — verified lowering to authorized and adversarial Veil 2.0 state machines (`veil_projection_sound_and_complete`).
- **Prompt (`Charter.Projection.Prompt`)** — constitutional system prompt and deontic alignment card for any actor role (unalienable immunities, powers with preconditions, hard-floor prohibitions, English citations) + structured synthetic **Training Views** (`(situation, actor, permitted/required acts, expected remedies, citation)`).
- **ContractABI (`Charter.Projection.ContractABI`)** — deterministic state-transition guard specification (JSON ABI and Solidity guard interface) with `requireComplies` and `executePower` hooks.
- **Visualization & Diff (`Charter.Projection.Visualization`)** — readable timeline of a trace or failing simulation annotated with violated duties/powers and English spans, plus **Amendment Diff** (`diffLaws`) comparing two institution versions across preserved invariants, changed clauses, and modified duties/powers.

## 8. Parameter Exploration and Ratchets (`Charter.Core.Ratchet`)

```lean
structure RatchetSpec (P : Type) (σ : Sig) where
  wellCalibrated   : P → Bool
  bilateralRatchet : P → P → Bool
  entrenchedCore   : Law σ → Law σ → Bool
```

**Universal ratchet meta-theorem (`universal_ratchet_trajectory_safe`):** Any finite sequence of amendments satisfying `wellCalibrated`, `bilateralRatchet`, and `entrenchedCore` preserves all parameter bounds and all entrenched Hohfeldian disabilities, immunities, and duty closures.

The CLI command `charter explore` sweeps a grid of parameter regimes (or tests a proposed amendment) and reports which calibration constraints, ratchet rules, and simulation suites pass.

## 9. Tooling & Multi-Institution CLI

`CliInstitution` / `InstitutionBundle` descriptor supports multiple registered institutions (`--law psa`, `--law commons`, `--all`):

- `check` — structure, verbatim coverage, provenance, staleness, and open authorship questions
- `trace <clause-id>` — character-by-character span table for a clause
- `views` — legal, per-actor, and operational views
- `veil` — Veil 2.0 transition-system & safety specification
- `eval <scenario.json>` — institutional consequences of a trace
- `explain <who> <act> [scenario.json]` — counterfactual compliance and validity explanation
- `sim [scenario.json]` — stateful multi-entity world simulation
- `verify` — status ledger of kernel-checked guarantees
- `prompt [actor]` — AI constitutional system prompt, alignment card, and training dataset rows
- `abi` — smart-contract JSON ABI and Solidity guard interface
- `diff` — amendment diff and entrenchment audit between law versions
- `explore` — parameter-space sweep and ratchet verification
