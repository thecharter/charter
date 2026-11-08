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
- **Continuous 196-file upstream regression gate**: Charter vendors the upstream Haskell `eflint-4.1.0.1` test and example corpus (`test/eflint-corpus/`), enforcing exact outcome parity except for **39 machine-audited tolerances** ([`tolerances.md`](test/eflint-corpus/tolerances.md), [`tolerances.json`](test/eflint-corpus/tolerances.json)):
  - **8 files that fail in our run of `eflint-repl` 4.1.0.1 and pass in Charter**, traced to the order in which types are saturated (`D6(a)`), the type given to an instance created through a `Placeholder` (`D13`), and the precedence of `When` (`D14`);
  - **1 intentional well-foundedness boundary (`D6(b)`, `CHR020`)**: rejecting cyclic self-negation in `Holds when` / `Derived from` (`archetypes.eflint` and the 23 files that include it) so every derived fact has a unique stratified fixpoint and truthful `?why` explanations; and
  - **7 end-state invariant checks (`D30`)**: `charter test` checks every declared `Invariant` at the end state of the program and of each scenario (aligning `test` with `explore` and `prove`), whereas eFLINT's `--test-mode` omits violation outputs.

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
| **[Charter](docs/rfc.md)** | Constitutional protocols, multi-party governance, commercial & escrow charters | **Three independent judgments** (`occurred`, `lawful`, `valid`); `Fact`, `Open`, 4-valued `Evidenced` + `Finding`, `Act`, `Power`, `Duty`, `Immunity`, `Default`/`Exception`/`Priority` + `Conflict`, rule-level `Amend` | Stateful `Time` & `Duration`, `Money(CUR, SCALE)` & `Quantity(UNIT)` over `Int`, `[start, end)` expiry, `Held … For`, `Due within`, `Param` & `Regime` | Proved live-evaluator correspondence (`evalPhrase_sound`/`complete`, least fixpoint, ratchet preservation), zero-axiom `charter prove`, lawful/adversarial/mixed explorer + temporal/SMT `verify`, SHA-256 multi-doc provenance, operator-blind `charter-server` | Cannot establish unobserved real-world truth or prose faithfulness without accepted evidence and human review (`docs/trust.md`) |
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

See [`docs/rfc.md`](docs/rfc.md), [`docs/plans/2026-11-06-charter-1.0-implementation-plan.md`](docs/plans/2026-11-06-charter-1.0-implementation-plan.md), and [`docs/benchmarks.md`](docs/benchmarks.md) for the complete architecture, 46-claim assurance registry (`docs/claims.json`), and 9-institution competitive benchmark suite.

---

## Assurance Scope & Trusted Computing Base

Charter enforces strict truth-in-advertising on formal claims ([`docs/assurance-levels.md`](docs/assurance-levels.md), [`docs/trust.md`](docs/trust.md), [`docs/claims.json`](docs/claims.json), verified by `test/gates/claims-backed.sh` and `charter doctor --claims docs/claims.json --fail-on-unbacked`):

- **`proved` (`live-evaluator`)**: Kernel-checked Lean 4 theorems over the live `CIR` evaluator and core (`evalPhrase_sound`, `evalPhrase_complete`, `replay_trace_deterministic`, `frame_preservation_unrestricted`, `saturateStratum_least_prefixpoint`, `evalCompiledDAG_eq_spec`, `redactForAudience_preserves_verdict`, `cir_ratchet_trajectory_preserves_entrenched`, `cir_guard_step_correspondence`, `sha256_nist_vectors`, `hmacSha256_rfc4231_vector`) with zero `sorry`, zero `native_decide`, and zero extra axioms.
- **`decided` (`concrete-trace`)**: Per-program checkpointed theorems emitted by `charter prove`, discharged in Lean's kernel via `kernel_rfl` with **zero axioms (`{}`)**.
- **`checked` (`concrete-trace` / `bounded-exhaustive`)**: Runtime scenario evaluation, `charter explore` (`lawful`/`adversarial`/`mixed`), `charter verify` (`finite`/`smt`), Law 8 SHA-256 provenance checks, target syntax/differential parity checks (`charter generate --verify-output`), `charter-server replay`, and 196-file eFLINT corpus regression.
- **`assumed`**: Explicitly enumerated external hypotheses (clock monotonicity, oracle/custodian honesty, gateway enforcement of capability tokens, fairness premises on unbounded liveness properties).

---

## Building & Running Charter

Requires Lean `v4.24.0` (pinned in `lean-toolchain`; zero Mathlib or external Lean dependencies):

```sh
# Build the standalone `charter` binary (.lake/build/bin/charter)
lake build

# Run the full PR verification battery: the build, 13 gates, the 196-file eFLINT corpus,
# 171 spec conformance tests, 12 standard-library modules, kernel proof fixtures, the server
# and projection suites, and every example
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

# Explain an answer: which facts prevent an act, and what would enable it
.lake/build/bin/charter explain "enter(Lou, Tess)" Examples/Tenancy/tenancy.charter

# Compile to a signed artifact and verify it with the standalone server
.lake/build/bin/charter build Examples/ServiceEscrow/service-escrow.charter -o out/escrow.artifact
.lake/build/bin/charter-server verify out/escrow.artifact
```

`charter help` lists the rest: `init`, `fmt`, `doc`, `lsp`, `doctor`, `explore`, `verify`, `diff`, `generate`.

---

## Examples

[`Examples/`](Examples/README.md) holds twenty-four agreements, each with its English, its specification, and the cases that test it. Twenty are documents a person might actually sign: a will, a living trust, a deed, a power of attorney, a prenuptial agreement, a promissory note, an employment agreement, an insurance policy, club bylaws, and others. The English is original and fictional; it is not legal advice.

```sh
.lake/build/bin/charter check --require-provenance --deny-warnings Examples/LastWill/will.charter
.lake/build/bin/charter test Examples/LastWill/cases/estate.charter
./tools/examples-check          # every example in the root-and-cases layout
```

---

## Status

Charter 1.0.1. The twenty worked agreements pass, and they were not easy to write. What they cost, a ranked list of what would make them easy, and the defects found on the way are in [`docs/plans/2026-11-07-example-friction/`](docs/plans/2026-11-07-example-friction/README.md); every item is filed, tracked in [#79](https://github.com/thecharter/charter/issues/79).

Known limits worth reading before relying on a result:

- All eleven of the initial silent wrong-answer defects found while writing the twenty examples ([#2](https://github.com/thecharter/charter/issues/2)–[#12](https://github.com/thecharter/charter/issues/12)) are fixed (`D29`–`D33`); seven secondary edge-case reproductions (such as normative conflict propagation through intermediate derived facts, [#80](https://github.com/thecharter/charter/issues/80), and clock-derived fact timestamps, [#16](https://github.com/thecharter/charter/issues/16)) remain in `docs/plans/2026-11-07-example-friction/reproductions/`.
- `evalPhrase_sound` and `evalPhrase_complete` relate the evaluator to a step relation that is itself stated in terms of the evaluator's functions ([#65](https://github.com/thecharter/charter/issues/65)).
- The Solidity, Quint and prompt targets are generated, not proved: `cir_guard_step_correspondence` concerns an intermediate guard step, not the emitted text ([#66](https://github.com/thecharter/charter/issues/66)).
- There is no calendar: time is counted in whole steps (spec 9.6).

---

## Repository Layout

```
src/
  Main.lean                        Standalone `charter` CLI entry point
  Charter.lean                     Umbrella module for the Charter compiler & core
  Charter/
    Surface/                       Unified contextual lexer, parser, AST, diagnostics (.charter & .eflint)
    Resolve/                       Static resolution (`Static.lean`) & assurance gates (`AssuranceGates.lean`)
    Core/                          `Term`, `Spec` (`DomMap`), `State`, `Provenance`, evidence, defaults, amendment
    Eval/                          Stratified fixpoint saturation, judged rules, transitions, & kernel proofs (`Properties.lean`)
    Verify/                        Explorer, temporal properties, and the finite/SMT/inductive back ends
    Prove/                         Checkpointed proof generator & capped kernel runner (`charter prove`)
    Project/                       Solidity/JSON ABI guard, Quint, and prompt targets; `charter diff`
    Artifact/                      SHA-256, HMAC, and the signed content-addressed artifact
    Server/                        `charter-server`: state store, reservations, protocol (links no parser or resolver)
    Lsp/                           Language server
    Cli/                           One file per `charter` subcommand
  Server.lean                      Standalone `charter-server` entry point
lib/                               12 reusable institutional standard-library modules (`*.charter`)
Examples/                          24 agreements with their English and cases (`Examples/README.md`)
benchmarks/                        Nine benchmark institutions (`docs/benchmarks.md`)
sdk/, editors/                     TypeScript, Python and Rust clients; Tree-sitter and VS Code grammars
test/
  spec/                            171 normative conformance tests mapped to `docs/spec/` chapters
  lib/                             Test harnesses & bounded invariant exploration for `lib/*.charter`
  prove/                           End-to-end zero-axiom kernel-decision fixtures for `charter prove`
  eflint-corpus/                   Vendored upstream Haskell eFLINT 4.1.0.1 corpus (196 files) + `tolerances.json`
  gates/                           13 gates, one script per law or guarantee (`g0-independence`, `claims-backed`, `operator-blind`, …)
docs/
  mission.md                       Charter's goals and fourteen design laws
  rfc.md                           Charter 1.0 architecture RFC & 2026-11-06 maintainer rulings
  trust.md                         Enumerated Trusted Computing Base & environmental assumptions
  assurance-levels.md              Normative `proved` / `decided` / `checked` / `assumed` + scope taxonomy
  claims.json                      Machine-checked assurance claim inventory
  plans/                           Implementation plans, and `2026-11-07-example-friction/` (what the examples cost to write)
  meetings/                        Architectural decision records (`D1`–`D33`)
  spec/                            Charter 1.0 language specification (`001`–`020`, approved) + `diagnostics.md`
tools/
  battery                          Full verification suite required before landing changes on `main`
  examples-check                   Checks every example's root and runs every case
  examples-metrics                 Counts retyped English and repeated patterns per example
  approve-clauses                  Stamps clause approvals (stands in for a `charter approve` command)
  kernel-probe                     Memory- and time-capped runner for kernel reduction experiments
```

### Related Repositories

- **[`thecharter/psa`](https://github.com/thecharter/psa)** — Standalone authoritative English specification (`psa.md`) and pure-Charter formalization (`psa.charter`) of **The Protocol of Sovereign Agency**.

---

## Citation

If you use Charter in your work, please cite it:

```bibtex
@software{Hartford2026Charter,
  author  = {Hartford, Eric},
  title   = {{Charter}: An Institutional Specification
             and Verification Language},
  year    = {2026},
  version = {1.0.1},
  url     = {https://github.com/thecharter/charter},
  orcid   = {0009-0002-0159-2127},
  note    = {Open-source research implementation in Lean 4.
             ORCID: 0009-0002-0159-2127.
             Google Scholar: SwrFngsAAAAJ}
}
```

Charter is built on eFLINT. Please cite the work it rests on as well:

```bibtex
@inproceedings{vanBinsbergen2020eFLINT,
  author    = {van Binsbergen, L. Thomas and
               Liu, Lu-Chi and
               van Doesburg, Robert and
               van Engers, Tom},
  title     = {{eFLINT}: A Domain-Specific Language
               for Executable Norm Specifications},
  booktitle = {Proceedings of the 19th ACM SIGPLAN
               International Conference on Generative
               Programming: Concepts and Experiences},
  pages     = {124--136},
  year      = {2020},
  publisher = {Association for Computing Machinery},
  doi       = {10.1145/3425898.3426958}
}

@article{vanBinsbergen2026Reflections,
  author  = {van Binsbergen, L. Thomas and
             Esterhuyse, Christopher A. and
             M{\"u}ller, Tim},
  title   = {Reflections on the Design, Applications
             and Implementations of {eFLINT},
             a Domain-Specific Language for
             Legal Compliance Reasoning},
  journal = {Journal of Computer Languages},
  volume  = {88},
  pages   = {101411},
  year    = {2026},
  doi     = {10.1016/j.cola.2026.101411}
}
```

Author: Eric Hartford. ORCID: [0009-0002-0159-2127](https://orcid.org/0009-0002-0159-2127). Google Scholar: [SwrFngsAAAAJ](https://scholar.google.com/citations?user=SwrFngsAAAAJ&hl=en). Contact: eric@quixi.ai.
