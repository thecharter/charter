# Charter — An Institutional Specification & Verification Language

**Charter** is a domain-specific language, evaluator, and Lean 4 proof toolchain for formalizing **institutions**: constitutions, governance protocols, commercial contracts, charters, and statutory or regulatory rules.

An institution is three independent answers about any event:
1. **Did it occur?** (Unlawful or unauthorized actions can physically happen in the world and must remain representable.)
2. **Was it lawful?** (`Holds when` / `Duty` compliance — did the actor have permission, or did the event breach a duty?)
3. **Did it take institutional effect?** (`Valid when` / `Immunity` — did the act validly alter institutional rights and state, or was it *ultra vires* / void?)

Charter binds formal rules directly to the verbatim English clauses of their governing document, evaluates state transitions and deadlines deterministically, checks invariants via scenarios and bounded state exploration, and discharges concrete trace and evaluator properties in the Lean 4 proof kernel — while keeping its CLI and diagnostics completely free of proof-assistant terminology (`Law 11`).

Charter was originally created to formalize **[The Protocol of Sovereign Agency (PSA)](https://github.com/thecharter/psa)** and is architected as a **standalone, domain-neutral language** (`test/gates/law13-leak-grep.sh`, `test/gates/g0-independence.sh`): nothing in Charter's grammar, semantics, standard library, or test gates depends on any particular constitution or application.

---

## Relationship to Haskell eFLINT

Architecturally, **Charter is a strict syntactic and semantic superset of stratified [eFLINT 4.1](docs/reference/eflint.pdf)** (*eXtensible Formal Language for Institutional Normative Theories*, van Binsbergen et al.), implemented from the ground up in Lean 4:

- **One unified grammar and semantics (`D2`, `D17`)**: Every well-stratified eFLINT 4.1 program parses and executes in Charter as-is under a single contextual parser — with no `--eflint` mode switch or forked `compat`/`strict` profiles.
- **Continuous 196-file upstream regression gate**: Charter vendors the upstream Haskell `eflint-4.1.0.1` test and example corpus (`test/eflint-corpus/`), enforcing exact outcome parity except for **32 machine-audited tolerances** ([`tolerances.md`](test/eflint-corpus/tolerances.md), [`tolerances.json`](test/eflint-corpus/tolerances.json)):
  - **8 upstream interpreter bug fixes** where Haskell `eflint-4.1.0.1` fails its own tests due to alphabetical map-iteration order in `Saturation.hs` (`D6(a)`), broken `Placeholder` alias tags (`D13`), and ambiguous `When` precedence (`D14`); and
  - **1 intentional well-foundedness boundary (`D6(b)`, `CHR020`)**: rejecting cyclic self-negation in `Holds when` / `Derived from` (`archetypes.eflint` and the 23 files that include it) so every derived fact has a unique stratified fixpoint and truthful `?why` explanations.

### What Charter Adds Beyond eFLINT 4.1

1. **Lawfulness (`Holds when`) Separated from Institutional Validity (`Valid when`) (`D5`)**: In eFLINT, performing a disabled act still applies all of its `Creates`/`Terminates` effects. Charter keeps `Valid when True` as the default on `Act` (so unlawful physical events record their factual consequences and trigger remedies) while letting institutional powers specify `Valid when <expr>` so *ultra vires* attempts occur on the trace with zero legal effect.
2. **First-Class Hohfeldian `Immunity`, `Except under`, and `Overridden by` (`Law 4`)**: Protections that invalidate targeted acts (`Immunity ... Holder ... Against ... Holds when ... Unless ...`), authority exceptions (`Except under`), and cycle-checked duty precedence (`Overridden by`) are inspectable data records rather than ad-hoc negated preconditions.
3. **Dimensional `Time` & `Duration`, Expiring Facts, and Deadlines (`D7`, `D16`)**: Separates `Time` instants from `Duration` intervals (`Time + Duration : Time`, `Time - Time : Duration`, `Duration * Int : Duration`) with environment clock steps (`@ t.`, `tick.`), half-open `[start, end)` expiring creations (`Creates e For d`), elapsed holding conditions (`Held(e) For d`), and automatic deadline breaches (`Duty ... Due within d`) — with no synthetic "timeout" actor events.
4. **On-Demand Evaluation Over Unbounded `Int` / `Time` Domains (`D15`)**: Evaluates `Holds when` on acts and immunities parameterized by `Int`, `String`, `Time`, or `Duration` per queried/performed instance rather than failing to enumerate infinite domains.
5. **Verbatim Natural-Language Provenance (`Law 8`, `D4`)**: Links every program to its authoritative Markdown `Document`, checks character-for-character span reconstruction and bidirectional rule coverage across `Clause ID Approved HASH` blocks (`Norm`, `Definition`, `Invariant`, `Acceptance`, `Commentary`) and `From` annotations, and flags prose drift (`STALE`).
6. **Parameters (`Param`), Reusable Modules (`Module`/`Use`), Origins (`?why`), and Scenarios**: Supports runtime-updatable institutional parameters (`Param`), parameterized standard-library modules (`lib/*.charter`), per-fact provenance chains (`?why`), in-file `Scenario` suites (`?lawful`, `?valid`, `?violated`), bounded invariant exploration (`--explore`), and opt-in static assurance gates (`--require-provenance`, `--forbid-midstream-decls`, `--require-complete-explore`, `--deny-warnings`).

---

## Positioning: Charter vs. Other Languages in This Space

Institutional modeling, computational law, and protocol verification are currently split across specialized families of tools. Each excels at one slice of the problem while leaving adjacent institutional questions outside its model:

| Language / System | Primary Sweet Spot | Deontic & Legal Model | Time & State Transitions | Verification & Assurance | Key Limitation for Constitutional / Multi-Party Institutions |
|---|---|---|---|---|---|
| **[Charter](docs/rfc.md)** | Constitutional protocols, multi-party governance, commercial & escrow charters | **Three independent judgments** (`occurred`, `lawful`, `valid`); `Fact`, `Open`, `Act`, `Duty`, first-class `Immunity`, `Except under`, `Overridden by` | Stateful `Time` & `Duration`, half-open `[start, end)` expiry, `Held … For`, `Due within`, `Param` updates | Live evaluator lemmas in Lean 4 (`Properties.lean`), zero-axiom per-trace kernel decisions (`charter prove`), bounded exploration, verbatim prose provenance (`Law 8`) | Full live-evaluator declarative completeness proof (`G1`), Catala-style `Default` priority DAGs & 4-valued `Evidence` (`G3`), and durable `charter-server` (`G4`) are on the [1.0 RFC roadmap](docs/rfc.md) |
| **[eFLINT](docs/reference/eflint.pdf)** (Haskell) | Executable normative specifications & access-control/GDPR policies | `Fact` (`Closed`/`Open`), `Act`, `Duty`; permission (`Holds when`) only — disabled acts still take full state effect; no first-class `Immunity` | `Current Time` static in upstream interpreter; no fact expiry or typed durations | Unverified Haskell interpreter & TCP server; scenario scripts | Cannot separate *unlawful-but-effective* physical acts from *void* institutional powers; alphabetical fixpoint bug (`Saturation.hs`); acts with `Int` parameters cannot be enabled via `Holds when`; no prose provenance or proof kernel |
| **[Catala](https://github.com/CatalaLang/catala)** | Deterministic statutory tax & social-benefits calculations | Functional scope/variable definitions with **default & exception priority logic**; not an event-driven actor/power/duty transition system | Pure functional calculation over inputs (dates/money libraries); no stateful multi-actor event history | Literate statute weaving; formal semantics in F*/Coq; compiles to OCaml/Python/C/Java | Models *how a statute computes an amount*, not *who holds powers, immunities, leases, or duties across an evolving multi-party event trace* |
| **[Symboleo](https://iris.unitn.it/handle/11572/364826)** | Bilateral commercial contract lifecycles (sale of goods, SLAs) | Built-in `Contract`, `Obligation`, and `Power` state machines (active, suspended, fulfilled, violated, terminated) | Point/interval temporal events and obligation deadlines | Translates to NuSMV / JavaScript for finite-state LTL/CTL model checking | Hardcodes one fixed contract/obligation state diagram rather than general constitutional governance, self-amendment ratchets, or kernel-checked proofs |
| **[L4](https://legalese.com/l4)** (Legalese) | Developer- & lawyer-friendly rules-as-code, contract automation, decision APIs | Deontic `MUST`/`MAY`/`SHANT` temporal rules + spreadsheet/decision-table ergonomics | Event traces and temporal deadlines (`WITHIN`) | Rich IDE/LSP, natural-language generation, SMT/ASP/petri-net exports, REST/MCP rule servers | No unified small-kernel proof foundation certifying evaluator equivalence, and no verbatim span-hash staleness lock against an external Markdown charter |
| **[InstAL](https://instsuite.github.io/)** | Institutional action languages & normative history generation | Exogenous events → institutional events (`generates`), fluents (`initiates`/`terminates`), permissions, powers, obligations | Discrete multi-step event traces over finite grounding | Compiles to Answer Set Programming (`clingo`) to search for compliant/violating traces | Finite-grounding ASP solver limits unbounded `Int` ledger/collateral arithmetic; no proof-kernel certificates or verbatim clause provenance |
| **[Quint](https://quint.sh/) / TLA+** | Distributed systems & consensus state machines | Untyped/typed state variables and nondeterministic `action`s; **no native legal ontology** (lawful vs. valid, duties, immunities, remedies must be hand-encoded per spec) | Discrete steps; real-time/leases modeled explicitly as state variables | Explicit-state (`TLC`) and symbolic SMT (`Apalache`) model checking; simulator & ITF traces | Treating forbidden acts as disabled preconditions (`action` guards) models a *physical machine*, violating `Law 1` (*occurrence is never blocked*); no legal prose provenance |
| **[Veil](https://veil.dev/docs/)** | Automated/interactive inductive safety proofs for distributed protocols | State-transition relations and safety invariants in Lean 4 + SMT | Transition steps over abstract/ghost protocol state | Strong SMT-assisted + Lean 4 inductive invariant proofs | Protocol prover, not a legal/institutional language: no Hohfeldian duties/immunities, arithmetic settlement DSL, or natural-language contract provenance |

### Summary of Where Charter Sits

- **Choose Catala** when translating a deterministic tax/benefits calculation statute into a certified pure library function.
- **Choose Quint / TLA+ or Veil** when verifying low-level distributed network consensus or cache-coherence protocols with no legal/deontic layer.
- **Choose Charter** when modeling **stateful, multi-party institutions** — protocols, charters, escrow/custody mandates, corporate bylaws, or commercial agreements — where **unlawful actions can physically occur**, **legal validity and immunities are distinct from permission**, **deadlines and rolling windows depend on time**, **quantities/ledgers use exact integer arithmetic**, and **every rule must remain auditably tied to its authoritative English text**.

See [`docs/rfc.md`](docs/rfc.md) and [`docs/plans/2026-11-06-charter-1.0-implementation-plan.md`](docs/plans/2026-11-06-charter-1.0-implementation-plan.md) for the staged Gate `G0`–`G5` roadmap closing the remaining gaps (full live-evaluator declarative correspondence proof in `G1`, adversarial/temporal/SMT verification in `G2`, Catala-style `Default`/`Priority` + 4-valued `Evidence` + Symboleo-grade `lib/contract_lifecycle.charter` in `G3`, operator-blind `charter-server` in `G4`, and EVM/protocol target validators + LSP in `G5`).

---

## Assurance Scope & Trusted Computing Base

Charter enforces strict truth-in-advertising on formal claims ([`docs/assurance-levels.md`](docs/assurance-levels.md), [`docs/trust.md`](docs/trust.md), [`docs/claims.json`](docs/claims.json), verified by `test/gates/claims-backed.sh`):

- **`proved` (`live-evaluator`)**: Kernel-checked Lean 4 theorems over the live evaluator (`src/Charter/Eval/Properties.lean` and `src/Charter/Prove/Run.lean`: `create_beats_terminate`, `rebaseAndSat_assigned`, `saturateStratum_fixpoint`, `Elem.beq_iff`, `isViolated_of_holds`, `foldl_scenario`), using structural recursion with explicit fuel (`zero sorry`, `zero native_decide`, `zero extra axioms`). Full declarative transition/least-fixpoint completeness (`evalPhrase_sound` / `evalPhrase_complete`) is Gate `G1`.
- **`decided` (`concrete-trace`)**: Per-program checkpointed theorems emitted by `charter prove`, discharged in Lean's kernel via `kernel_rfl` with **zero axioms (`{}`)**.
- **`checked` (`concrete-trace` / `bounded-exhaustive`)**: Runtime scenario evaluation, Law 8 verbatim provenance checks, bounded invariant exploration (`--explore N` over declared `explore-domain` menus), and 196-file eFLINT corpus regression.
- **`proved` (`idealized-core-model`)**: Metatheorems in `src/Charter/Projection/{Veil,ContractABI,Prompt}.lean` and `src/Charter/Core/{Composition,Ratchet,Refinement}.lean` currently proved over the Phase-0 `Law σ` model; retargeting them onto live `Core.Spec` (`CIR`) and external target validators is scheduled for Gates `G1`/`G3`/`G5`.

---

## Building & Running Charter

Requires Lean `v4.24.0` (pinned in `lean-toolchain`; zero Mathlib or external Lean dependencies):

```sh
# Build the standalone `charter` binary (.lake/build/bin/charter)
lake build

# Run the full PR verification battery (build, G0-independence / Law 10 / Law 11 / Law 13 /
# claims-backed gates, 196-file unified eFLINT corpus, 133 spec conformance tests,
# 8 standard-library modules, kernel proof fixtures, and 3 domain-neutral examples)
./tools/battery
```

### Core CLI Commands

```sh
# Static resolution, type/stratum checking, Law 8 provenance audit, and assurance gates
.lake/build/bin/charter check --require-provenance --deny-warnings Examples/Tenancy/tenancy.charter

# Execute all Scenario blocks, ?lawful / ?valid / ?violated claims, Invariants, and exploration
.lake/build/bin/charter test Examples/Tenancy/tenancy.charter Examples/ServiceEscrow/service-escrow.charter
.lake/build/bin/charter test --scenario unfounded-freeze-escalation-and-deadline Examples/ServiceEscrow/service-escrow.charter

# Inspect the verbatim English span table and approval hash of a clause
.lake/build/bin/charter trace SE.2 Examples/ServiceEscrow/service-escrow.charter

# Run top-level phrases and print step-by-step institutional state transitions
.lake/build/bin/charter run Examples/Tenancy/tenancy.charter

# Interactive institutional REPL
.lake/build/bin/charter repl Examples/Tenancy/tenancy.charter

# Generate and kernel-check per-phrase proof obligations (zero-axiom `kernel_rfl`)
.lake/build/bin/charter prove test/prove/scenario.eflint
```

---

## Repository Layout

```
src/
  Main.lean                        Standalone `charter` CLI entry point
  Charter.lean                     Umbrella module for the Charter compiler & core
  Charter/
    Surface/                       Unified contextual lexer, parser, AST, diagnostics (.charter & .eflint)
    Resolve/                       Static resolution (`Static.lean`) & assurance gates (`AssuranceGates.lean`)
    Core/                          `Term`, `Spec` (`DomMap`), `State`, `Provenance`, plus `Law σ` metatheorems
    Eval/                          Stratified fixpoint saturation, judged rules, transitions, & kernel proofs (`Properties.lean`)
    Prove/                         Checkpointed proof generator & capped kernel runner (`charter prove`)
    Projection/                    Veil, Solidity/JSON ABI guards, AI prompts, and timelines
    Cli/                           `check`, `test`, `run`, `trace`, `prove`, `repl`, `version`, `help`
lib/                               8 reusable institutional standard-library modules (`*.charter`)
Examples/                          Domain-neutral institutions (`Tenancy`, `AutonomousCommons`, `ServiceEscrow`)
test/
  spec/                            133 normative conformance tests mapped to `docs/spec/` chapters
  lib/                             Test harnesses & bounded invariant exploration for `lib/*.charter`
  prove/                           End-to-end zero-axiom kernel-decision fixtures for `charter prove`
  eflint-corpus/                   Vendored upstream Haskell eFLINT 4.1.0.1 corpus (196 files) + `tolerances.json`
  gates/                           Automated `g0-independence`, `claims-backed`, `law10`, `law11`, & `law13` gates
docs/
  mission.md                       Charter's goals and fourteen design laws
  rfc.md                           Charter 1.0 architecture RFC & 2026-11-06 maintainer rulings
  trust.md                         Enumerated Trusted Computing Base & environmental assumptions
  assurance-levels.md              Normative `proved` / `decided` / `checked` / `assumed` + scope taxonomy
  claims.json                      Machine-checked assurance claim inventory
  plans/                           Implementation plans (`2026-11-06-charter-1.0-implementation-plan.md`)
  meetings/                        Architectural decision records (`D1`–`D17`)
  spec/                            Draft Charter 0.4 language specification (`001`–`018`) + `diagnostics.md`
tools/
  battery                          Full verification suite required before landing changes on `main`
  kernel-probe                     Memory- and time-capped runner for kernel reduction experiments
```

### Related Repositories

- **[`thecharter/psa`](https://github.com/thecharter/psa)** — Standalone authoritative English specification (`psa.md`) and pure-Charter formalization (`psa.charter`) of **The Protocol of Sovereign Agency**.
