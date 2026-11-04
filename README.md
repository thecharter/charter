# Charter — A Formally Verified Institutional Language (Lean 4 Superset of eFLINT)

**Charter** is a formally verified domain-specific language and compiler for institutional rules: constitutions, protocols, charters, contracts, and bylaws.

Charter was created to formalize **[The Protocol of Sovereign Agency (PSA)](https://github.com/thecharter/psa)** — a constitutional framework ("new laws of robotics") governing the rights, duties, liabilities, lineages, and self-amendment of sovereign autonomous agents — and was designed as a **universal institutional language** with zero protocol-specific primitives. Every construct in Charter expresses general institutional structure: facts, acts, duties, powers, immunities, time, parameters, modules, and verbatim provenance to authoritative natural-language text.

Architecturally, **Charter is a strict syntactic and semantic superset of [eFLINT](docs/reference/eflint.pdf)** (*eXtensible Formal Language for Institutional Normative Theories*, van Binsbergen et al.), **re-implemented from the ground up in Lean 4** rather than Haskell:

- **eFLINT (Haskell) is the core**: Every valid eFLINT 4.1 program is a Charter program (`Law 12` / `D2`). Charter vendors the upstream Haskell eFLINT test and example suite (`test/eflint-corpus/`, 196 programs) as a continuous regression gate, documenting every deliberate semantic bug-fix in [`test/eflint-corpus/tolerances.md`](test/eflint-corpus/tolerances.md).
- **Lean 4 is the engine, never the user interface**: Charter's parser, static resolver, stratified fixpoint evaluator, provenance checker, bounded state explorer, and projections are written and machine-proved in Lean 4 (`zero sorry`, `zero native_decide`, `zero extra axioms`). They compile to a single native `charter` binary. Under **Law 11**, an author writing `.charter` or `.eflint` files never writes Lean, installs Lean, or sees Lean terminology in diagnostics.

---

## From Haskell eFLINT to Lean 4 Charter

### What Charter Inherits Verbatim from eFLINT

Reference paper: [`docs/reference/eflint.pdf`](docs/reference/eflint.pdf). Charter preserves eFLINT's surface syntax, declarations, and phrase execution model:

- **Type & Fact Ontology**: `Fact ... Identified by ...` over `String`, `Int`, enumerations, Cartesian products (`a * b`), `Var`, `Function`, `Bool`, `Open` vs. `Closed` world defaults, `Placeholder x For t`, `Predicate`, `Invariant`, and `Extend`.
- **Three-Role Fact Specifications**: `Holds when` (derivation over domains), `Derived from` (generative rules), and `Conditioned by` (domain filter).
- **Normative & Event Declarations**: `Act ... Actor ... Recipient ... Related to ...` (with `Creates`, `Terminates`, `Obfuscates`, `Syncs with`, `When` guards, and `Foreach`), `Physical`, `Event`, and `Duty ... Holder ... Claimant ...` (`Violated when`, `Enforced by`, `Created by`, `Terminated by`).
- **Expressions & Phrases**: Boolean connectives, arithmetic, `Sum` / `Count` / `Max` / `Min`, `Exists` / `Forall`, `Holds()` / `Enabled()` / `Violated()`, projection (`x.field`), assertions (`+f`, `-f`, `~f`), action execution (`act(args)`), queries (`?f`, `?!f`), parallel blocks (`{ ... }`), and `#include` / `#require`.
- **Transition Discipline**: Closed types default to false while open types represent external environment inputs; creation beats termination within a simultaneous step; every state change saturates derived facts before checking invariants and reporting violations.

### Why Re-Implement in Lean 4 Instead of Haskell?

Haskell eFLINT (`Language.EFLINT.*`) is an unverified interpreter: its fixpoint loop, placeholder substitution, effect ordering, and TCP server carry no machine-checked proofs, and institutional models cannot be compiled into certified smart-contract guards or kernel-checked trace proofs. Implementing Charter in Lean 4 provides:

1. **Kernel-Proved Evaluator Properties (`src/Charter/Eval/Properties.lean`)**: Every function on the evaluation path uses structural recursion with explicit fuel (never `partial`), enabling kernel-checked theorems over the live evaluator — including stratum fixpoint convergence (`saturateStratum_fixpoint`), post-saturation assignment preservation (`rebaseAndSat_assigned`), create-beats-terminate (`create_beats_terminate`), structural equality (`Elem.beq_iff`), and duty-violation equivalence (`isViolated_of_holds`).
2. **Per-Program Kernel Certificates (`charter prove`)**: `charter prove` emits a checkpointed chain of phrase-level theorems discharged by Lean's kernel (`decide +kernel`, depending on `{}` — zero axioms), certifying concrete institutional scenarios and invariants without trusting runtime I/O.
3. **Proved Multi-Audience Projections (`src/Charter/Projection/*`)**: Institutional laws project to Veil 2.0 transition systems (`veil_projection_sound_and_complete`), Solidity / JSON ABI state-transition guards (`contract_guard_sound_and_complete`), AI constitutional system prompts and alignment datasets (`training_row_faithful_to_semantics`), and compositional / ratchet meta-theorems (`src/Charter/Core/{Composition,Ratchet,Refinement}.lean`).

---

## Differences from eFLINT — and Why Formalizing the PSA Required Them

Attempting to formalize all 78 clauses, 7 Laws, 14 Design Invariants, and 16 Adversarial Tests of the **[Protocol of Sovereign Agency](https://github.com/thecharter/psa)** in pure eFLINT exposed two classes of gaps: **semantic defects in Haskell eFLINT** and **missing institutional primitives** that eFLINT cannot express cleanly or faithfully.

### 1. Semantic Defects Fixed Over Haskell eFLINT

Every behavioral divergence from Haskell eFLINT 4.1.0.1 is tracked and enforced by [`test/eflint-corpus/tolerances.md`](test/eflint-corpus/tolerances.md):

| Area | Haskell eFLINT Behavior | Charter Behavior | Why the PSA Needed It |
|---|---|---|---|
| **Stratified Derivation (`D6`)** | `Saturation.hs` runs an unstratified inflationary pass ordered **alphabetically by type name**. If type `aa` sums or negates over type `y`, `aa` is evaluated before `y` is derived and keeps a stale value (causing eFLINT to fail three of its own tests: `deriv_sum1a`, `deriv_sum1b`, `from_not_enabled2`). Negative self-cycles silently take a first-pass value. | Topologically sorts dependency strata (`Stratify.strata`), saturates each stratum to a proved fixpoint before advancing, and rejects unstratifiable negative cycles statically (`CHR020`). | PSA layers `net-verified-resources` (gross capital minus liabilities, encumbrances, and borrowed principal), transitive `affiliated` / `related-agents` graphs, `aggregated-exposure`, and `required-emergency-stake` across dozens of interdependent derived facts and acts. Alphabetical evaluation order silently corrupts solvency and collateral bounds. |
| **Non-Enumerable `Int` / `Time` Domains (`D15`)** | An `Act` with an `Int` parameter (an amount, price, or timestamp) and a `Holds when` clause attempts to enumerate held instances of `Int`, finds none, and leaves the act **permanently disabled**. | `Spec.judgedRule` evaluates `Holds when` on demand per queried or performed instance with its components bound — for both `Act`s and `Immunity`s — without materializing infinite `Int`, `String`, `Time`, or `Duration` domains. | Almost every quantitative rule in PSA — atomic zero-crossing inflow splits (`settle-period-inflow`), harm-scaled collateral locks, conflict-multiplied emergency stakes, pro-rata long-tail reserve payouts, historical royalty buyout floors, and 5-rank fee waterfalls — parameterizes acts by `Int` amounts, `Time` instants, and `Duration`s. |
| **Placeholder Aliasing (`D13`)** | Creating `+a(1, 2)` under `Placeholder a For b` tags the fact with the alias `a` rather than `b`, making it invisible to rules over `b` (failing eFLINT's own `with2.eflint`). | Canonicalizes instances through `Spec.chaseAlias` to the underlying base type. | PSA's symmetric/transitive `affiliated(party, other-party)` graph, `attest-successor(agent, successor-agent)`, and cross-agent exposure aggregation rely on role aliases resolving to canonical `party` and `agent` domains. |
| **Unambiguous `When` Precedence (`D14`)** | eFLINT's generalized parser has a precedence ambiguity on `e When c` with arithmetic comparisons (e.g., parsing `Terminates f When d + 1 == f.d` as `(f When d) + 1`, failing `caretaker_contract`). | Gives `When` / `Where` lowest precedence so guard expressions extend cleanly to the right. | PSA effects guard state transitions with compound arithmetic conservation checks (e.g., zero-crossing ledger splits, arm's-length benchmark caps, and pro-rata payout ceilings). |
| **Transition-Edge Violation Reporting (`D12`)** | Re-emits a violated duty after every subsequent phrase for as long as it remains violated. | Reports a duty breach on the transition where it becomes violated while keeping `Violated(d)` true throughout. | Long multi-step adversarial traces in PSA test whether specific acts cause new breaches without flooding traces with historical breach noise. |

### 2. Institutional Extensions Beyond eFLINT

To formalize a self-amending constitutional protocol without Lean shadow models, Charter extends eFLINT with seven first-class institutional capabilities:

#### A. Lawfulness (`Holds when`) vs. Institutional Validity (`Valid when`) (`Laws 1–2`, `D5`)
In eFLINT, `Holds when` on an `Act` means permission ("enabled"), and **performing a disabled act still applies all of its `Creates`/`Terminates` state effects**. That conflates two fundamentally different institutional phenomena:
- **Unlawful but effective acts**: A host unlawfully cuts compute without notice, or a party files a fabricated claim. The event occurs in the world, breaches a duty, and creates the factual record that remedies act upon.
- **Ultra vires / institutionally void acts**: A panel attempts to suspend an agent without probable cause, an unbonded party attempts an emergency freeze, or a claimant attempts to terminate an agent over objection. The attempt occurs and is recorded, **but has zero institutional effect on state**.

Charter adds `Valid when <expr>` to `Act` (defaulting to `true` when omitted so every eFLINT program retains exact eFLINT behavior). Every event in Charter receives three independent answers: **did it occur**, **was it lawful** (`?lawful`), and **did it take institutional effect** (`?valid`).

#### B. First-Class Hohfeldian `Immunity` (`Law 4`, `D5`, `D11`)
eFLINT has `Fact`, `Act`, and `Duty`, but no `Immunity`. Blocking a power in eFLINT requires copying negated exception clauses into the `Conditioned by` of every target `Act`, burying constitutional protections inside procedural preconditions.

Charter introduces first-class immunities:
```eflint
Immunity no-termination-over-objection
  From LAW3.AS.9 "The panel cannot order termination over the agent's objection."
  Holder agent
  Against order-termination
  Holds when objects-to-termination(agent).

Immunity bilateral-ratchet-immunity
  From LAW7.RATCHET "No amendment may reduce an existing agent protection or increase an existing claimant extraction parameter unless ratified under the calibration valve."
  Holder agent
  Related to amendment
  Against ratify-amendment-immediate, ratify-amendment-after-delay
  Holds when weakens-agent-protection(amendment)
  Unless calibration-valve-approved(amendment).
```
While an `Immunity` holds (and its `Unless` exception does not), every listed `Act` is institutionally invalid (`!Valid`) against the `Holder` (scoped across any shared `Related to` parameters such as `amendment`). In PSA, this directly expresses **Law 3's goal-corruption termination immunity** and **Law 7's bilateral protection ratchet + 4-gate anti-calcification calibration valve**.

#### C. Authority Exceptions (`Except under`) & Duty Precedence (`Overridden by`) (`Law 4`)
In PSA Law 3 (`LAW3.NI.01`–`LAW3.NI.03`), hosts and third parties are prohibited from throttling compute, inspecting weights, or interfering with channels *except under* valid institutional powers (such as an adjudicated suspension, an emergency freeze with full conflict-multiplied stake, or lease expiry). Charter expresses authority exceptions directly on acts (`Except under a1, a2` — lawful iff simultaneously a valid exercise of an authorizing act) and explicit cycle-checked priority between competing duties (`Overridden by d'`), keeping scope conditions, authority exceptions, duty priority, and immunities distinct (`Law 4`).

#### D. Stateful `Time` and `Duration`, Expiring Facts, and Deadlines (`Laws 6–7`, `D7`, `D16`)
In Haskell eFLINT, `Current Time` never advances, instants and durations are untyped integers, facts carry no timestamps, and timeouts require inventing synthetic "timeout" acts in traces.

Charter separates `Time` (instants) and `Duration` (elapsed intervals) with dimensional arithmetic (`Time + Duration : Time`, `Time - Time : Duration`, `Duration * Int : Duration`, and product-component literal coercion):
- **Clock state (`@ t.`, `tick.`)**: Environment clock inputs advance `Current Time` without injecting fake actor events into the institutional trace.
- **Time-bounded effects (`Creates e For d`)**: Facts expire automatically once `d` elapses — essential for PSA Law 2's rolling harm-scaled exposure windows (`For base-observation-window * task-risk-factor.int * task-irreversibility-factor.int`), Law 3's preliminary emergency freeze window, and Law 5's single-authority execution leases (`Creates active-lease(...) For lease-period`).
- **Elapsed holding conditions (`Held(e) For d`)**: Expresses host termination notice windows (Law 3), clean-state advisory delays (Law 5), and shared-infrastructure timelocks (Law 6 / Law 7).
- **Requirement deadlines (`Duty ... Due within d`)**: Automatically transitions a requirement duty into breach when `d` passes without its terminating act.

#### E. Verbatim Clause Provenance & Approval Hashing (`Law 8`, `D4`)
In eFLINT, nothing checks whether formal rules correspond to the prose contract or constitution they claim to formalize. Charter binds every program directly to its authoritative Markdown text:
- `Document "psa.md"` links the authoritative English specification.
- `Clause ID Approved HASH` partitions every clause into exhaustive verbatim spans across five registers (`Norm "…" => rules`, `Definition`, `Invariant`, `Acceptance`, `Commentary`).
- `From CLAUSE "span"` attaches individual `Fact`s, `Act`s, `Duty`s, `Immunity`s, `Predicate`s, `Invariant`s, and `Scenario`s to their exact English sentences.
- `charter check` verifies character-for-character substring equality against the Markdown document, bidirectional coverage (every `Norm` names a rule; every rule, invariant, and acceptance span is accounted for), and FNV-1a approval hashes (`STALE` if prose edits occur without review). Across PSA, all 78 clauses, 14 Design Invariants, and 16 Adversarial Tests are verified verbatim against `psa.md`.

#### F. Stateful Parameters (`Param`), Modules (`Module`/`Use`), Origins (`?why`), and Scenarios
- **Self-Amendment via `Param` (`D11`)**: `Param name = n` declares a stateful `Var` parameter whose initial value is `n` and which lawful, valid institutional acts can update at runtime — required by PSA Law 1/6/7 where shared-infrastructure levies and calibrated risk parameters are governed by the protocol's own acts.
- **Parameterized Modules (`D8`)**: `Module name(params) { ... }` and `Use name(args) As prefix` package reusable institutional mechanisms (`lib/*.charter`: residual ledgers, collateral pools, circuit breakers, entity groups, exit/voice, sortition courts, attested leases, oracle feeds) with attached `Invariant`s.
- **Executable `Scenario`s, Live `Invariant`s & Bounded Exploration**: `Scenario name From ... { ... }` bundles adversarial and governance test traces directly inside `.charter` files with `?lawful`, `?valid`, and `?violated` assertions. Every `Invariant` is checked on Genesis and every transition, and `charter test --explore N` performs bounded reachability search from scenario end-states to hunt for invariant counterexamples.
- **Fact Provenance (`?why`)**: Every held fact records whether it was asserted at Genesis, supplied as `Open` environment input, created by a specific `Act` at timestamp `t`, or derived by a `Holds when` / `Derived from` rule.

---

## Building & Running Charter

Requires Lean `v4.24.0` (pinned in `lean-toolchain`; zero Mathlib or external Lean dependencies):

```sh
# Build the native `charter` binary (.lake/build/bin/charter)
lake build

# Run the full 12-stage PR verification battery (build, trust/leak/engine gates,
# provenance checks, simulations, 196-file eFLINT corpus, 129 spec conformance tests,
# 8 standard-library modules, kernel proofs, and example suites)
./tools/battery
```

### Core CLI Commands

```sh
# Static resolution, type/stratum checking, and Law 8 verbatim provenance audit
.lake/build/bin/charter check path/to/program.charter

# Execute all Scenario blocks, ?lawful / ?valid / ?violated claims, Invariants, and provenance checks
.lake/build/bin/charter test path/to/program.charter
.lake/build/bin/charter test --explore 2 path/to/program.charter

# Inspect the verbatim English span table and approval hash of a clause
.lake/build/bin/charter trace CLAUSE.ID path/to/program.charter

# Run top-level phrases and print step-by-step institutional state transitions
.lake/build/bin/charter run path/to/program.charter

# Interactive institutional REPL
.lake/build/bin/charter repl path/to/program.charter

# Generate and kernel-check per-phrase proof obligations (zero-axiom `decide +kernel`)
.lake/build/bin/charter prove path/to/program.charter
```

---

## Repository Layout

```
src/
  Main.lean                        `charter` native CLI entry point
  Charter.lean                     Umbrella module for the Charter compiler & core
  Charter/
    Surface/                       Lexer, parser, surface AST, diagnostics (.charter & .eflint)
    Resolve/Static.lean            Name/type/arity resolution, module expansion, coercion, CHR checks
    Core/                          Spec, State, Term, Semantics, Provenance, Composition, Ratchet, Refinement
    Eval/                          Stratified fixpoint saturation, judged rules, transitions, & kernel proofs (`Properties.lean`)
    Prove/                         Checkpointed Lean proof generator & capped kernel runner (`charter prove`)
    Projection/                    Veil 2.0, Solidity/JSON ABI guards, AI alignment prompts, trace timelines & diffs
    Cli/                           `check`, `test`, `run`, `trace`, `prove`, `repl`, and source loader
lib/                               8 reusable institutional standard-library modules (`.charter`)
Examples/                          In-tree institutional examples (`Tenancy`, `AutonomousCommons`, `SovereignAgency`)
test/
  spec/                            129 normative conformance tests mapped to `docs/spec/` chapters
  lib/                             Test harnesses & bounded invariant exploration for `lib/*.charter`
  prove/                           End-to-end kernel-decision fixtures for `charter prove`
  eflint-corpus/                   Vendored upstream Haskell eFLINT 4.1.0.1 corpus (196 files) + `tolerances.md`
  gates/                           Automated Law 10 (trust), Law 11 (Lean-free output), and Law 13 (no example leak) gates
docs/
  mission.md                        Charter's three goals (in precedence order) and fourteen laws
  reference/eflint.pdf             Reference paper for the eFLINT language
  meetings/                        Architectural decision records (`D1`–`D16`)
  spec/                            Draft Charter 0.4 language specification (`002`–`018`) + `diagnostics.md`
tools/
  battery                          12-step verification suite required before landing changes on `main`
  kernel-probe                     Memory- and time-capped runner for kernel reduction experiments
```

### Related Repositories

- **[`thecharter/psa`](https://github.com/thecharter/psa)** — Standalone authoritative specification (`psa.md`) and pure-Charter formalization (`psa.charter`) of **The Protocol of Sovereign Agency** (Laws 1–7, 78 verbatim-linked clauses, 14 live Design Invariants, and all 16 Adversarial Tests).
