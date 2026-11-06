# Charter 1.0: Semantic Completion, Verification Assurance, and Competitive Institutional-Language Architecture

Status: Approved design RFC (maintainer rulings recorded 2026-11-06 in §18.3); implementation tracked in `docs/plans/2026-11-06-charter-1.0-implementation-plan.md`\
Prepared: 2026-11-06\
Target: `thecharter/charter`\
Primary audience: language implementers, formal-methods engineers, legal-informatics researchers, protocol designers, and deployment/security engineers\
Project boundary: Charter is a standalone, general-purpose institutional language and tooling project. Its normative requirements, semantics, implementation, proofs, libraries, examples, tests, and release criteria must be independent of any particular application written in Charter.

> Design thesis. Charter should make a precise, independently checkable promise: an institutional text and its approved formal model yield a determinate, auditable judgment concerning the occurrence, lawfulness, and legal effect of events; the operational evaluator implements the model; verification backends analyze the model under explicit assumptions; and enforcement adapters authorize only the operations entrusted to them. Nothing in that promise implies that Charter discovers hidden real-world facts, proves the meaning of English, prevents every physical offense, or certifies deployments without evidence.

Navigation: Current-state audit · Formal semantics · Legal extensions · Verification · Charter server · Implementation packages · Acceptance tests · Competitive positioning · Release criteria.

## 0. Executive decision record

This RFC recommends semantic completion before feature expansion, followed by extensions that close identifiable gaps with eFLINT, Symboleo, InstAL, Catala, Veil, L4, and Quint. It deliberately avoids a wholesale rewrite and preserves Charter's most valuable differentiators: eFLINT-style institutional modeling, independently represented occurrence / lawfulness / validity, first-class immunities, executable time, direct natural-language provenance, and Lean 4 proofs.

### 0.1 Proposed release gates

| Gate | Release name (descriptive)    | Required deliverable                                                                                                               |
| ---- | ----------------------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| G0   | Claims-aligned baseline       | Accurate public claims, versioned spec, reproducible tests, documented proof and trust boundaries                                  |
| G1   | Semantic foundation           | Formal declarative semantics; proved correspondence to the live evaluator and all supported constructs                             |
| G2   | Verification-grade Charter    | Both compliant and adversarial exploration; temporal properties; generalized proof support and precise assurance labels            |
| G3   | Institutional completeness    | Contract lifecycle, delegated powers, defeasible exceptions, evidentiary uncertainty, amendments and multi-institution composition |
| G4   | Deployment-grade Charter      | Durable transactional `charter-server`, authenticated evidence inputs, executable authorization protocol, audit and recovery       |
| G5   | Verified multi-target product | End-to-end verified or explicitly qualified projections; IDE/LSP, explainability, packages, benchmark suite, documentation         |

No stage may claim guarantees belonging to a later gate. Stages are dependency-ordered milestones, not calendar promises. A deliberately limited, correctly documented product is preferable to a broadly advertised but unproved one.

### 0.2 Non-negotiable invariants of the project itself

1. The English leads. An identified authoritative source can ground an institutional rule; literal span coverage does not automatically establish that the encoding has the right meaning.
2. Occurrence is not permission. Unlawful conduct can physically occur and must remain representable. Legal effect is a distinct question.
3. Fact truth is an external responsibility. The engine applies law to typed, provenance-bearing evidence and lawful findings; it does not create unknown real-world facts.
4. No hidden interpretive authority. Any external human or software actor may supply evidence or a proposed interpretation; those claims have only the standing granted by the modeled institutional rules and cannot silently modify Charter semantics.
5. The trusted computing base is enumerated. Proofs identify their assumptions, model, target, and checker. Claim labels never overstate their scope.
6. Unified stratified-eFLINT superset. Charter maintains one unified language grammar and semantics — never two diverging semantic profiles — as a strict syntactic and semantic superset of stratified eFLINT 4.1 (`Law 12`, `Law 13`). Cyclic self-negation in `Holds when` / `Derived from` remains rejected (`CHR020`) to preserve unique Tarski least fixpoints and truthful explanations, while upstream `eflint-4.1.0.1` interpreter defects are documented and regression-tested in `test/eflint-corpus/tolerances.md`.
7. Institutional abstractions remain general. Facts, acts, duties, powers, immunities, delegation, evidence, time, and composition are domain-neutral constructs. Optional library modules describe reusable legal patterns; no application contract or product-specific rule may define their semantics.
8. Any new syntax needs formal semantics, negative tests, a conformance suite, an explanation model, and a backward-compatibility decision before acceptance.

### 0.3 Project independence: enforceable architecture boundary

Charter is a language implementation, not the governing constitution or a subproject of any program written in it. This RFC MUST be implementable without consulting, importing, compiling, or executing any specific customer or external application. The language's semantics must come from its public language specification and approved formal definitions, not from the requirements of a motivating use case.

The intended dependency direction is strictly one way:

```
    arbitrary source documents and institutional policies
                         │
                         ▼
                user-authored Charter code
                         │
                         ▼
       public Charter parser / IR / semantics / evaluator
                         │
           ┌─────────────┼─────────────┐
           ▼             ▼             ▼
        check/prove    projections    server/SDK

    No dependency or import is permitted in the reverse direction.
```

Enforce the boundary in code review and CI:

1. Language core: parser, AST, resolver, evaluator, proof kernel, temporal semantics, and projection contracts MUST contain no named or special-cased concepts drawn from any particular application. A new semantic primitive must be justified by at least two independent institutional examples, or by a general formal requirement whose scope does not depend on the originating example.
2. Standard library: modules MAY encode reusable, optional patterns (leases, escrow, delegations, elections, accounts, remedies, governance, etc.). No built-in module may assume one constitution's rates, protected parties, financial instruments, identity categories, rights, or substantive prohibitions. Specialized policy templates remain third-party packages.
3. Documentation and examples: normative documentation and tutorial examples must demonstrate multiple unrelated institutions. A single external application must not define release readiness, language correctness, feature naming, or version compatibility.
4. Conformance and proofs: CI must test language semantics with small, neutral fixtures and general theorems. Optional integration tests for applications belong in those applications' own repositories, not Charter's mandatory correctness gate.
5. Server and API: requests carry a versioned institution identifier, source bundle, facts/evidence, acting party, and proposed action. No API route, schema, client SDK, diagnostics, or authorization result depends on a particular product or institutional ideology.
6. Governance and public claims: Charter is released and versioned independently; another project being written in Charter creates no authorship, governance, or normative coupling. The README and published comparison tables must describe general language capabilities and their actual proof scope, not infer general correctness from one deployed application.

Required cleanup of the present repository (part of G0, not optional future polish):

- Complete the `D10` retirement of Phase-0 application companions: remove `import Examples` (`SovereignAgency.cli`, `AutonomousCommons.cli`), `ProtocolWorldState`, `charter_*` Lean macros, and the v0.3 flat-grammar runtime paths from `src/Main.lean`, `Examples/`, and `src/Charter/`.
- Update `docs/mission.md` and `README.md` so that Charter's normative release gates, feature justification, and verification claims stand on general institutional requirements and exact assurance tables rather than hardcoded clause/scenario counts from an external repository. Charter's historical origin (created to formalize the Protocol of Sovereign Agency while keeping zero domain-specific primitives in the language, enforced by `test/gates/law13-leak-grep.sh`) remains part of its documented provenance, never a normative coupling or release gate in `thecharter/charter`.
- Refactor `tools/battery` to remove steps coupled to Phase-0 linked companions and hardcoded application scenario counts (`psa 16/16`, `commons 8/8`), replacing them with neutral multi-institution conformance, library, exploration, and kernel-proof suites while preserving all language-feature regression coverage.
- Keep specialized external constitutions and their application suites in their own repositories (such as `thecharter/psa`), ensuring every semantic property formerly exercised only by an in-tree Phase-0 companion has a minimal domain-neutral regression fixture in `test/`.
- Audit `AGENTS.md`, `HANDOFF.md`, `docs/`, `Examples/`, `lib/`, `test/`, and `tools/` so active requirements and gate scripts remain domain-neutral; historical entries in `docs/meetings/` and `HANDOFF.md` remain as archival decision records.

Acceptance gate `G0-INDEPENDENCE`: a clean Charter build, the existing conformance/proof battery, and all standard-library fixtures pass in an isolated checkout with no external application repositories, private domain fixtures, or domain-specific environment variables; when the server is introduced at G4, its smoke tests must pass under the same isolation requirement. A static dependency scan must reject prohibited product-specific imports and special-case identifiers in the language core. The gate is a structural requirement, not a substitute for semantic review.

## 1. Evidence, scope, and verified baseline

### 1.1 Source audit performed for this RFC

The design is grounded in the `main` branch repository as inspected on 2026-11-06, especially:

- `README.md`, which describes Lean-backed formal verification, eFLINT superset semantics, source provenance, bounded exploration, proof certificates, and projections;
- `docs/mission.md`, Charter's three goals and fourteen design laws;
- `docs/plans/2026-10-22-redesign.md`, including §3a's compiler/server split over certified operator-blind artifacts;
- `docs/spec/README.md`, identifying the 0.4 draft status, conformance tests, and unwritten chapters;
- `src/Charter/Eval/Properties.lean`, proving local properties of the live evaluator (`create_beats_terminate`, `rebaseAndSat_assigned`, `saturateStratum_fixpoint`, `isViolated_of_holds`) while explicitly noting that the independent declarative semantics and full evaluator soundness/completeness proof remain open;
- `src/Charter/Core/Spec.lean`, `Core/State.lean`, and `Eval/Interpreter.lean`, the live kernel-reducible `.charter`/`.eflint` representation, stratified fixpoint evaluator, half-open `[start, end)` expiry (`Info.live`), `Open` missing-input checks (`CHR100`), and bounded explorer;
- `src/Charter/Core/Syntax.lean` and `Core/Semantics.lean`, the Phase-0 typed `Law σ` model whose metatheorems are not yet connected to the live `Core.Spec` / `Eval` pipeline;
- `docs/spec/013_invariants_and_proof.md`, distinguishing `checked`, `decided`, `proved`, and `assumed`;
- `docs/spec/014_parameters_and_regimes.md`, where `Param` is implemented and `Amend` / `Regime` / entrenched invariants are pending;
- `docs/spec/018_toolchain_and_cli.md`, identifying currently implemented commands and pending server/tooling;
- `src/Charter/Projection/Veil.lean` and `Projection/ContractABI.lean`, internal `Law σ` correspondence theorems and source renderers;
- `test/eflint-corpus/tolerances.md` and `tools/battery`, the 196-file eFLINT compatibility and 12-step regression infrastructure.

Evidence limit: This is a source/design audit, not an independent local execution of `lake build`, the full battery, the generated Solidity, or an external Veil toolchain. README assertions are therefore treated as repository claims unless the inspected code directly supports the narrower fact. The proposal below is not an assessment of the current branch's runtime behavior in production.

### 1.2 What appears implemented, partial, and pending

| Subsystem                                               | Current repository evidence                                           | Evaluation / gap                                                                                            |
| ------------------------------------------------------- | --------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| eFLINT-style parser, resolver, evaluated facts and acts | `Surface/Parser.lean`, `Resolve/Static.lean`, `Eval/Interpreter.lean` | Real core implementation; formal semantics of every supported path still needs a total correspondence proof |
| Three independent legal judgments                       | `Valid when`, `Holds when`, typed `Core.Semantics`                    | Major strength; prove surface-to-Core connection and handle physical effects explicitly                     |
| Duty/institutional protection                           | `Duty`, `Immunity`, `Except under`, `Overridden by`                   | Strong expressiveness; expand legal standing, conflict handling and lifecycle                               |
| Stratified derivation and timestamps                    | Evaluator and spec chapters 004/009                                   | Add independent least-fixpoint theorem, time-boundary tests, event/wall-clock assumptions                   |
| Scenarios/invariants and breadth-first exploration      | Spec chapter 013, live evaluator                                      | Bounded, predominantly enabled-action exploration; generalized adversarial model checking needed            |
| Kernel decisions for concrete programs                  | `Prove/Run.lean`, CLI and checked fixtures                            | Valuable trace evidence; not a universal proof over all executions                                          |
| Law-to-Core projection and Veil representation          | `Core/Semantics.lean`, `Projection/Veil.lean`                         | Internal proofs exist; external target syntax/semantics and emitted code still need assurance               |
| Solidity/ABI guard projection                           | `Projection/ContractABI.lean`                                         | Internal correctness theorem and renderer; not proof of deployed EVM behavior                               |
| Text provenance                                         | `Document`, `Clause`, span hash and tracing                           | Provenance is unusually good; improve cryptographic integrity and multi-document authority                  |
| Rules amendment                                         | `Param` exists; `Amend` and `Regime` pending                          | Complete versioned amendment semantics and transition compatibility                                         |
| Full language specification                             | `docs/spec/README.md` says 0.4 draft, some chapters unwritten         | Publish canonical grammar and revision-controlled semantics                                                 |
| Persistent server / authorization service               | Future in `docs/spec/018...`                                          | Essential gap for runtime use                                                                               |
| LSP/IDE, packages, integrations                         | Planned or partial                                                    | Essential gap relative to L4 developer experience                                                           |

### 1.3 Claims that must be reformulated immediately

- Replace unqualified "formally verified compiler" with a scoped statement enumerating exactly which theorems are checked and which verification obligations remain open.
- State the eFLINT relationship at its exact mathematical boundary: **Charter is a strict syntactic and semantic superset of stratified eFLINT 4.1**, rejecting cyclic self-negation (`CHR020`) to guarantee unique least fixpoints and truthful explanations, and fixing documented `eflint-4.1.0.1` interpreter defects enumerated in `test/eflint-corpus/tolerances.md`.
- Replace claims that a Veil, Solidity, prompt, or JSON ABI projection is proved faithful with the precise domain of the theorem (internal typed representation, renderer, compiler, executable artifact, or deployed target). Promote only the proven boundary.
- Never call a finite set of passing scenarios a proof that an arbitrary program's invariants hold for all reachable states. The tool's existing `checked`/`decided`/`proved`/`assumed` vocabulary is the right foundation.
- Disclose the discrepancy between completed `Core`-level metatheorems and the still-missing live-evaluator-to-Core elaboration and simulation proof. Proving a separate, idealized model is not yet a proof of the operative language.
- State expressly that legal source-text correspondence is a human/reviewed specification judgment. Verbatim span and hash checks certify provenance, not legal interpretive accuracy.

## 2. Product scope and objective acceptance criteria

### 2.1 Supported domains

Charter 1.0 should be competent for (i) institutional constitutions and public governance; (ii) commercial and service contracts; (iii) delegated agency, representation and fiduciary mandates; (iv) deadlines, claims, remedies and termination; (v) stateful financial and collateral obligations; (vi) verifiable authorization of operations; and (vii) formal assessment of conflicting laws under explicitly declared precedence and jurisdictional rules.

### 2.2 Explicit non-goals

Charter is not an omniscient truth engine; an autonomous decision-maker; a general predictor of harms; an implicit world court; a replacement for all national law; a self-executing bridge to bank accounts; a universal legal-theory oracle; or proof that a law's English is ethically or legally correct. It also should not become a general-purpose programming language with arbitrary side effects inside proof expressions.

### 2.3 End-state success definition

A conforming 1.0 distribution must, for every supported source program and action, (a) parse and resolve against a versioned spec; (b) produce an immutable semantic artifact; (c) calculate occurrence, compliance, legal validity and institutional effects deterministically; (d) attribute every non-derived premise to a named actor, evidence source, or assumption; (e) report deadlines and status transitions; (f) support concrete execution plus bounded and unbounded-where proven verification; (g) issue reasoned, replayable judgments through a transactional server; and (h) emit a verifiable assurance manifest enumerating what is proved, merely tested, bounded, or externally assumed.

No silent success: unsupported constructs, unproved target projections, insufficient model-checking coverage, unresolved necessary evidence, stale legal text, and incomplete proofs must be visible as explicit typed outcomes, never green passes.

## 3. Semantic architecture: one law, one meaning

### 3.1 Canonical pipeline

```
Authoritative documents + approved authority/priority manifest
                          |
                   Parser + spans
                          |
                 Typed elaboration
                          |
        Canonical Institutional IR (CIR)
        /     |        |          |     \
   evaluator  proof  explorer  explain  projections
        |       |        |         |         |
  server state proofs  traces     reasons   targets
```

Single-source semantics means a single canonical formal representation, not that the text parser itself is the semantics. The meaning of the elaborated CIR is fixed by a declarative small-step transition relation independent from the optimized evaluator. Parser and elaborator produce proof certificates or validator-checkable CIR well-formedness; their correctness is covered by tests and a checkable refinement statement, ideally a theorem.

### 3.2 CIR schema (minimal kernel-reducible data model)

Evolve `Core.Spec` directly into a compact, strongly typed, kernel-reducible `CIR` (`Institution`) rather than introducing a bloated domain-heavy AST. Because `charter prove` (`decide +kernel` / `kernel_rfl`) and the `eval_sound` / `eval_complete` theorems depend directly on the size of the core inductive types, **high-level legal patterns (`Contract` lifecycles, `Mandate`s, accounting estates, jurisdictional conflict policies) belong in `lib/*.charter` modules, never as primitive AST nodes in `src/Charter/Core/`**.

`CIR` extends `Core.Spec` with only the irreducible semantic primitives that cannot be expressed as library modules:

```
Institution {
  sourceManifest: [SourceRef]
  languageVersion: Version
  types: [TypeSpec]          // Fact, Open/Evidenced Fact, Act/Power, Duty, Event, Immunity
                             // over String, Int, Time, Duration, Money<CUR,SCALE>, Quantity<UNIT>
  strata: [[DomId]]          // topologically sorted derivation & Default/Priority DAG
  amendmentRules: [AmendSpec]
  entrenchedProtections: [RuleId]
  evidencePolicies: [EvidenceSpec]
  invariants: [InvariantSpec]
  temporalProperties: [TemporalSpec]   // consumed by Verify/, never widening Eval TCB
  initialState: State
}
```

Every rule has a stable identifier, original source span(s), drafting version, type-checked expression, legal standing/holder/beneficiary, applicable scope, activation/termination conditions, and explicit priority. Do not encode legal relationships only as opaque arbitrary functions: projections, diffs and explanations must be able to inspect their structure (`Mission Law 5`).

Represent the compiled artifact (`2026-10-22-redesign.md` §3a) as a versioned, content-addressed binary/canonical-JSON bundle combining the `CIR`, the span-verified source manifest, and the proof/assurance certificate under one cryptographic digest. Maintain code-generated schemas and version migration readers.

### 3.3 Normative event outcome

For state `S`, event `e`, observed-world snapshot `W`, and law version `L`:

```
Judgment(L, S, W, e) = {
  occurred: observed | hypothetical,
  lawful: yes | no | undetermined,
  valid: yes | no | undetermined,
  dutyBreaches: [Breach],
  exercisedPowers: [PowerId],
  institutionalEffects: [Effect],
  obligationsOpenedOrClosed: [ObligationInstance],
  unmetEvidence: [EvidenceRequirement],
  reasons: ReasonGraph,
  assumptions: [Assumption],
  snapshot: {lawHash, stateVersion, evidenceRoot, time}
}
```

There is no meaningful universal answer to "was an event observed?" for a hypothetical event: the static evaluator should return a hypothetical outcome while `record-observation` creates an observed event record. The current lawfulness and validity predicates are deliberately separate. An event may be unlawful but valid, lawful but legally ineffective, both, or neither. Missing evidence is not automatically exculpatory or incriminating.

Physical and legal state must be disjoint. A forged transfer can change the world even if the purported corporate authority was void. `WorldStep` changes observed physical/economic facts as evidence is received; `LegalStep` applies valid institutional effects. A void act cannot authorize a legal effect, but the observed fact of the attempted act, damage and restitution claim must remain modelable. The model must never equate "institutionally ineffective" with "physically impossible".

### 3.4 Declarative transition semantics

Introduce independent relations and their proved implementation correspondences:

```
WellFormed(L)
EvidenceAdmissible(L, W, fact, support)
WorldStep(W, event, W')
Breach(L, S, W, event, duty)
ValidExercise(L, S, W, event, power)
LegalStep(L, S, W, event, S')
TimedStep(L, S, t, t', S')        // no fictitious actor event
DerivesLeast(L, S, derivedFacts)
TraceStepStar(L, S0, W0, events, Sn, Wn)
```

Define what happens when multiple powers react to one event and what happens when their effects conflict. For boolean facts, eFLINT's order-independent `create beats terminate` merge (`Store.union`, proved in `Eval/Properties.lean`) remains normative across the unified language. For functional/quantitative state (`Param`, typed `Money`/`Quantity` balances, and explicit `Unique` functional facts), two incompatible simultaneous assignments within a single atomic transition are rejected (or flagged statically/dynamically) unless an explicit priority or aggregation rule resolves them; simultaneous creations of distinct values on legacy eFLINT `Var`/`Function` types emit a diagnostic warning while preserving eFLINT execution semantics.

In eFLINT scripts where declarations (`Extend`, `Fact`, etc.) appear interleaved with execution phrases (`spec_011_6`), each mid-trace declaration phrase is modeled cleanly as a host-level `LawVersion k -> LawVersion (k+1)` epoch transition over immutable `CIR` snapshots, while `charter-server` accepts runtime law transitions solely through valid, immunity-checked institutional `Amend` acts.

For every supported syntax/IR feature, require these theorems (or a precisely declared, test-only subset before release):

```
resolve_sound : WellTypedSource p -> WellFormed (elaborate p)
eval_sound   : Evaluator.run L S e = result -> DeclarativeStep L S e result
eval_complete: DeclarativeStep L S e result -> Evaluator.run L S e = result
replay_deterministic : same law/state/evidence/time/event -> same decision
frame_preservation   : unrelated facts remain unchanged by each legal step
```

The evaluator-correctness theorem should address actual dynamic declarations, modules, parameters, quantities, evidence, and time, not just an idealized `Law σ` embedding. Use a typed elaboration relation with explicit feature coverage; failure to implement a construct must not be hidden by omitting it from the theorem's input domain.

### 3.5 Derived facts and stratification

Specify positive dependency closure as the least fixpoint; prove both soundness and leastness (a stable fixpoint alone is insufficient). Specify a stratification algorithm rejecting or explicitly handling non-monotone cycles. Use decidable finite-domain assumptions for rules that require enumeration; on-demand judgments for non-enumerable domains. Distinguish non-termination/resource exhaustion from false. Maintain provenance of each derivation edge, including its evidence dependencies and rule version.

### 3.6 Unified language surface and strict stratified-eFLINT superset

Charter does **not** split into diverging `eflint-4.1-compat` and `charter-1.x-strict` semantic profiles (`Mission Law 12`, `Mission Law 13`). Instead, Charter maintains **one unified grammar and operational/declarative semantics** that is a strict superset of stratified eFLINT 4.1:

1. **Contextual Charter keywords**: Single-word uppercase Charter additions (`Document`, `Clause`, `Approved`, `Text`, `Norm`, `Definition`, `Acceptance`, `Commentary`, `From`, `Immunity`, `Against`, `Unless`, `Duration`, `Held`, `Param`, `Module`, `Use`, `As`, `Scenario`, `Power`, `Default`, `Evidence`, `Finding`) are parsed contextually in declaration/clause positions so unquoted eFLINT `Atom`s (`Identified by Valid, Invalid` or `f(Text)`) remain valid everywhere, eliminating even the `--eflint` lexical mode switch. A standalone `tick.` resolves to an act `tick` if one is declared in scope, and to the environment clock step otherwise.
2. **`Act` vs. `Power` (`D5`)**: `Act` retains `Valid when True` by default (required by both eFLINT compatibility and Mission Laws 1–2 so unlawful physical acts still record factual state transitions), while `Power` requires an explicit `Valid when <expr>` clause and desugars to `Act`.
3. **Stratification boundary (`D6`)**: Cyclic self-negation in `Holds when` / `Derived from` remains rejected (`CHR020`) so every derived fact has a unique Tarski least fixpoint, post-state logical equivalence, truthful `?why` / `ReasonGraph` premises, and direct translation to Lean/SMT/Veil. Default rules (`archetypes.eflint`'s motivating pattern) are expressed cleanly via Charter's stratified `Default` / `Exception` rules (§4.4).
4. **Opt-in static assurance gates, never semantic forks**: Stricter project discipline (`--require-provenance`, `--require-complete-explore`, `--deny-warnings`) is enforced by opt-in static checker gates that never alter the runtime meaning of a construct.

The new constructs in §§4–7 below are illustrative design sketches, not currently executable Charter syntax. Settle their unique spellings in normative `docs/spec/` chapters (blessed per `AGENTS.md`) before implementation.

## 4. Institutional ontology and legal semantics extensions

The objective is to bridge the most important expressiveness gaps without importing a full unrestricted programming language, bloating the kernel TCB (`src/Charter/Core/`), or hiding institutional meaning in application-specific predicates. **Architectural rule (`D8`, `Law 9`, `Law 10`)**: only constructs that cannot be expressed cleanly over existing primitives (`Power` requiring `Valid when`, stratified `Default`/`Priority` with `Conflict`, multi-document `SourceRef`, and rule-level `Amend`/`Regime`) enter the compiler core; domain-neutral legal structures (`Contract` lifecycles §4.2, `Mandate`s §4.3, conflict-of-laws modules §4.6, and monetary estates §6.4) ship as verified standard-library modules (`lib/*.charter`) with proved module invariants.

### 4.1 Hohfeldian relations as inspectable views and (where necessary) primitives

Retain Charter's `Duty`, `Power`, and `Immunity` and define precise normalized relations for:

- Claim-right ↔ duty: holder, obligor, bearer/beneficiary, object, activation, fulfillment and breach.
- Privilege / liberty ↔ no-claim: permitted conduct relative to a specified counterparty, not an inferred universal permission.
- Power ↔ liability: actor may produce an institutional change affecting a target; validity and effective date are distinct.
- Immunity ↔ disability: the protected actor's legal position cannot be altered by specified exercises of power.
- Authorization / delegation: a principal confers limited exercise authority on a delegate while retaining defined responsibilities.
- Competence / standing / jurisdiction: who may initiate proceedings, make findings, act on behalf of whom, or appeal.

Many can be derived from existing rules; do not introduce duplicate mutable facts where a proved view suffices. A `Power` should not be treated as an ordinary permission; validity, lawfulness and performance must be modeled separately. Explicitly define what happens when a power is lawfully exercised but its target is immune, and when an unlawful act nonetheless exercises a valid power.

### 4.2 Contract lifecycle state machine (Symboleo gap — `lib/contract_lifecycle.charter`)

Provide reusable `Contract` / `ContractInstance` and `Obligation` standard-library modules (`lib/contract_lifecycle.charter`, instantiated via `Module`/`Use`) with explicit lifecycle states and transition causes, keeping `src/Charter/Core/` free of hardcoded contract-law doctrine:

```
Draft -> Offered -> Accepted -> InForce -> {Completed, Expired, Rescinded,
                                        Terminated, Frustrated, Void}
                                    \-> Disputed (procedural overlay)
```

Do not hardcode this as one globally mandatory state diagram: contracts may have staged effectiveness, multiple parties, partial completion, suspension, or revival. Provide a standard lifecycle library and require programs to declare allowed transitions. `Void` is an institutional status; `Breached` is not automatically a terminal status. A valid contract can remain in force after breach with accrued remedies.

Obligation instances require: obligor; claimant; owed performance; creation source; temporal window; suspension/tolling rules; satisfaction evidence; discharge rules; breach threshold; remedies; defenses; and survival after termination. Support performance, payment, waiver, novation, assignment, setoff, settlement, replacement, frustration, restitution, and partial satisfaction as named institution-level operations.

Important: subcontracting, assignment of benefits, delegation of performance, and novation of obligations have different legal consequences. Charter must preserve those distinctions, with configurable consent, privity, and recourse requirements. This directly addresses ordinary corporate and financial delegation without treating agents, accountants, and counterparties as special language types.

Proposed normalized record:

```
Obligation {
  id, obligor, claimant, performanceSpec, amount?, currency?,
  effectiveAt, dueWindow, defenses, priority, guarantee,
  status: Active | Suspended | PartSatisfied | Satisfied |
          Breached | Discharged | Expired,
  remainingPerformance, accruedRemedies, provenance
}
```

Acceptance: a principal delegates performance of a debt; the delegate performs half; the obligation remains open for half; assignment of the claim changes its claimant only when authorized; unauthorized delegation is recorded but may not discharge the original principal.

### 4.3 Delegation, representation, attributable acts (`lib/agency_mandate.charter`)

Ship a domain-neutral agency mandate module in `lib/agency_mandate.charter` (paired with core provenance and epistemic `Evidence` primitives from §5), rather than hardcoding common-law or civil-law agency doctrine into `src/Charter/Core/` or tailoring rules to any one application. A mandate is the institutional record of granted authority, not proof that every physical act of a delegate is observed.

```
Mandate {
  principal, delegate, role, powers, purpose, resourceBounds,
  permittedFurtherDelegation, noticeAndReporting, effectiveAt, expiresAt,
  revocableBy, revocationEffects, survivalOfThirdPartyRights,
  liabilityRule, evidenceRequirement
}
```

Formal semantics must distinguish:

1. Direct authorized action: principal performs an act under its own power.
2. Authorized representation: delegate acts with authority on behalf of principal, producing an effect attributed according to the mandate.
3. Exceeding authority: delegate acts physically, but the purported principal-binding legal effect may be void, voidable or valid through applicable apparent-authority rules.
4. Independent contractor action: contractor has its own duties; its misconduct is not universally imputed to principal.
5. Intentional circumvention: a principal cannot achieve compliance merely by arranging a prohibited outcome through a delegate.

Attribution is a defined rule with evidence requirements, not an automatic assumption. Model express authority, apparent authority, ratification, revocation notice, retained control, causation, and scope of employment/mandate where a legal program invokes them. Explicitly represent unknown delegate activity as incomplete observation rather than false.

Proof obligation: a delegate's effective powers are never greater than the grant (subject to explicitly modeled apparent-authority/public-law exceptions), and revocation prevents new acts from exercising the mandate once its legally effective notice condition is met. This is a legal-effect guarantee, not a guarantee that a dishonest delegate cannot act physically.

### 4.4 Exceptions and defeasible norms (Catala gap)

Current `Except under` and `Overridden by` are useful but insufficient as a uniform statutory exception calculus. Define a normalized default–exception–priority model with explicit conflicts:

```
Rule R = {defaultOutcome, applicability, exceptions[], overrides[],
          priority, scope, source, effectiveVersion}
```

Three distinct outcomes are essential:

- Unambiguous: one applicable rule yields an answer.
- Unresolved evidence: facts needed for an otherwise determinate rule are missing/contested.
- Normative conflict: two rules with equal effective authority prescribe incompatible outcomes and no conflict rule resolves them.

No blanket "last rule wins" policy. Reject circular priority graphs statically. For conflicts not resolved by hierarchy, return `indeterminate: conflict` with both source rules and an adjudication path. Use exception specificity only when the governing law explicitly says to; specificity is not a universally safe jurisprudential assumption.

Support Catala-inspired overlapping definitions: a rule supplies a default result, another a scoped exception, another an exception to that exception. Compile this to a canonical decision DAG and prove equivalence of evaluation to the rule-resolution semantics. Distinguish exceptions from compensatory remedies and from institutional immunities.

### 4.5 Provenance, authority and multi-document sources

Generalize the current `Document "..."` mechanism to a source authority manifest that works for arbitrary source files and document sets:

```
SourceRef {
  id, uri, contentDigest, canonicalBytesDigest, effectiveFrom,
  effectiveUntil?, issuingAuthority?, jurisdiction?, legalRank?,
  signaturePolicy?, approvalProof?, humanReadableLabel
}
```

A program can cite several documents: constitutions, contracts, amendments, bylaws, regulations, judgments. Each rule binds to exact span coordinates and quoted bytes (with a reproducible encoding and newline policy). For Markdown, also store an anchor + surrounding textual fingerprint so line rearrangement does not silently mutate meaning. Use collision-resistant SHA-256/BLAKE3 digests for content integrity; maintain the existing FNV-1a hash only for legacy compatibility (not as a security guarantee). Define a separate signing/approval mechanism with recognized approvers, key rotation and expiration. Hashing does not itself grant authority.

Guarantee bidirectional coverage between normative English spans and encoded rules, while allowing labeled commentary that has no formal consequence. Introduce `coverage = complete | partial | illustrative`; refuse an unqualified completeness claim unless every normative span is resolved, every formal rule has a source, and all referenced documents are approved and current.

Provide a legal-source diff engine with three views: changed English, changed formal semantics, and changed externally observable decisions. Semantic drift requires review even if the English is unchanged; English drift requires review even if the rules are unchanged.

### 4.6 Institutional hierarchy, conflicts of laws, composition (`lib/jurisdiction.charter` + `Core/Composition`)

Existing `Core/Composition.lean` provides a foundation for vertical/horizontal composition and preservation theorems. Retarget those metatheorems onto the live `CIR` while shipping reusable authority/priority patterns as `lib/jurisdiction.charter` (paired with §4.4's `Default`/`Priority` calculus) covering:

- legal rank and authority (superior/subordinate);
- applicable jurisdiction and nexus (not implicit universal jurisdiction);
- temporal precedence and version applicability;
- reserved subjects and protected institutional interfaces;
- specific priority, conflict, saving, and override clauses;
- independent-party/role conflict checks;
- explicit outcomes when no valid legal order can be derived.

Avoid a general rule that "later statute beats earlier" or "higher-level text always wins": those depend on the governing legal system. Source rules select the conflict policy; an unresolved jurisdictional conflict remains contested. Proofs must show that subordinate valid amendments cannot remove superior immunities or evade reserved protections when a formal priority relation is present. These are conditional theorems, not claims about actual-world legal validity.

### 4.7 Amendment, ratification and entrenchment

Finish the features currently marked pending in specification chapter 014: rule-level `Amend`, `Regime`, and entrenched invariants. Model amendments as institutional events with an actor, relevant consents, review periods, vote thresholds, legal validity, effective date, target clause versions, and effects.

Define:

```
AmendmentProposal -> Published -> Eligible -> Ratified -> Effective
                      \-> Rejected / Expired / Challenged
```

A change may require a quorum, signature set, time-lock and a higher law's permission. The engine records law-version IDs per transition. Old obligations retain the applicable prior version unless a valid transition changes them. Never retroactively re-evaluate old acts under new law without an explicit retroactivity rule.

A proof of ratchet preservation must compose actual amendments of the live language model, not only a parametrized ideal `RatchetSpec` detached from source amendment operations. Provide pre-/post-state semantic equivalence tests across versions and a theorem target: if each valid amendment preserves entrenched rule interfaces, every reachable amendment trajectory preserves their constraints. Include explicit assumptions for the ratification and source-authenticity oracles.

## 5. Evidence, uncertainty, adjudication, and explanations

### 5.1 Extending eFLINT's `Closed` / `Open` split with structured epistemic evidence

In eFLINT 4.1 and Charter today (`docs/spec/003_types_and_domains.md` §3.6, `spec_003_6b_open_missing_input.eflint`), facts are **already** partitioned into two worlds:

- `Closed` facts (the default): ontic institutional state (`active-lease`, `duty-held`, `ratified`), which genuinely does not hold until a valid institutional act creates it; and
- `Open` facts (plus `Obfuscates` / `~f`): external world inputs, where querying an unassigned or obfuscated instance **already refuses to collapse unknown to `false`** and raises `CHR100: missing input` (`Mission Law 6: the world is input`).

What is missing for externally contested facts (account ownership, beneficial control, valuation, human contractor actions, jurisdictional nexus) is a non-aborting, structured epistemic layer on `Open` / `Evidenced` facts so a program and `charter-server` can reason over contested or missing evidence without halting evaluation with `CHR100`:

- Ontic assertions (`Closed` `Fact`): institutional positions established by valid legal acts;
- Epistemic observations (`Open` / `Evidenced` `Fact`): supported, opposed, disputed, unobserved, or superseded claims about the external world.

Extend `Open` / `Evidenced` facts conservatively with one canonical evidence status record:

```
EvidenceStatus = Established | Refuted | Unresolved | Conflicted
```

Existing eFLINT `Closed` and `Open` programs retain 100% of their current semantics. Do not implement unconstrained fuzzy probabilities as legal truth. Probabilities, likelihood ratios, or model confidence scores can be pieces of typed evidence, but must not silently substitute for a legal burden or standard of proof. A formal judgment becomes `undetermined` (`NeedEvidence` / `ReferForFinding` in the server API) when a legally necessary `Open`/`Evidenced` premise is `Unresolved` or `Conflicted`; it becomes determinate only under an explicit default, burden, presumption, deadline, or adjudicated `Finding`.

### 5.2 Findings versus evidence

Finding is an institutional act by an actor legally empowered to adjudicate. Evidence is material tendered to support or rebut a proposition. A finding must cite its applicable rule, standards, supporting evidence, contested material, and any appeals affecting effectiveness. This implements Charter mission Law 3: breaches and findings remain distinct.

Support legal standards as named, source-defined decision procedures (e.g., `preponderance`, `probableCause`, `clearAndConvincing`, `verifiedBenchmark`) whose meanings are not universally hardcoded. An opaque external fact-finder can supply a signed finding under a contractually approved assumption; Charter must label that assumption and the trust boundary.

### 5.3 Mandatory reason graph

Every nontrivial judgment should return a compact machine-readable reason DAG:

```
Decision -> Rule applied -> Applicability facts -> Evidence/finding
         -> Exception defeated? -> Priority decision -> Legal consequence
```

Each node includes a stable rule ID, source span/digest, fact value and status, authority, institution version, and execution time. Provide a minimal explanation for the decisive path and an expanded graph for audit. Generate counterfactual explanations: "What single unsatisfied condition would change this ruling?" Guard against explanation leaking confidential evidence by declaring an audience-specific projection and provenance-preserving redaction policy.

### 5.4 Obligatory evidence requests and provisional holds

Define a separate decision-service protocol, not a new judicial power: `Allow`, `Deny`, `NeedEvidence`, `ReferForFinding`, `Conflict`, `Unavailable` (these are API outcomes, not moral/legal verdicts). A holding action is permitted only if the operative law grants it, and must carry a named basis and expiry. No unconstrained `NeedEvidence` retry loop or indefinite hold. Once necessary facts are established and an action is lawful and valid, the service must issue the prescribed authorization (subject to separately enumerated concurrency/solvency constraints).

### 5.5 Testable impartiality

Support metamorphic independence tests: replace irrelevant actor names, reputations, model providers, or natural-language rationales while holding all legally relevant facts fixed. The judgment must remain identical, apart from source/identity provenance. Test `lawful` and `valid` independently, and test that legally relevant status differences change the ruling exactly when the relevant provision says they should.

## 6. Time, concurrency, quantities and financial semantics

### 6.1 Temporal model

Retain `Time` / `Duration`, expiring facts, `Held ... For`, `Due within`, and the project's principle that elapsed time is not a fictitious institutional actor. Add explicit models for:

1. Logical event sequence: a monotonically ordered commit index in one institutional instance.
2. Trusted calendar time: a timestamp with uncertainty/clock source; required for legal sunsets, fixed deadlines and filing windows.
3. Monotonic elapsed time: used for leases, durations and elapsed technical constraints.
4. Event time vs. observation time: a bank transaction may occur before the evidence reaches Charter.
5. Effective legal time: a contract amendment may be validly adopted now but take effect later.
6. Time divergence: liveness properties require a stated assumption that time progresses and the relevant scheduler continues to run.

Half-open intervals `[start, end)` (`now < expiry`) are **already** the live Charter semantics (`src/Charter/Core/State.lean:65`, `Info.live`, tested in `test/spec/spec_009_3d_expiry.eflint`), and eFLINT 4.1 has no `Creates ... For d` expiry construct that would require a legacy exception. Align the legacy Phase-0 `Core/Semantics.lean` model (`now <= expiry`) to `now < expiry` during G1 retirement/unification so `[start, end)` is universal across the entire codebase. Ship an expanded boundary-conformance suite covering `t=end-1`, `t=end`, `t=end+1`, interrupted clocks, and stale signed timestamps.

Propose a `ClockPolicy` record (source-defined and signed) with maximum skew, monotonic time source, late-observation policy, event ordering at equal timestamp, and expiry resolution. Model tolling as a legal shift of an obligation's effective due time under a valid institutional event, never as a change to un-tollable deadlines.

### 6.2 Nondeterminism, partitions, and concurrent events

Distinguish law-induced determinism (same settled facts and state yield same decision) from environmental nondeterminism (multiple actors, incomplete messages, losses, delays, concurrent orders). The formal model may admit several event orders; the server must serialize transitions within one legal institution or prove an appropriate commutative composition.

Add generalized `Environment` actions for attempts, observations, network partitions, delayed messages, forgery attempts, hidden delegated acts, clock faults, nonpayment, account closure, and partial infrastructure failures. Never assume a disconnected local fact is available in globally visible state. Model local knowledge separately from publicly registered knowledge where the institution's safety property depends on that distinction.

For overlapping operations, define serializability or legal equivalence. A ledger payment must be checked and committed against a particular version; it cannot be authorized twice against the same balance. Distinguish reservations (pending, expires, revocable under rules) from finalized effects.

### 6.3 Financial types and exact arithmetic

Introduce typed fixed-point money and explicit units as **static dimensional/scale type tags over exact arbitrary-precision `Int`** — the exact same zero-overhead kernel architecture used for `Time` and `Duration` (`D7`, `D16`) — with rational/division expressions statically checked for explicit rounding modes (`floor`, `ceil`, `nearestEven`, `exactOrReject`) before lowering to integer `Core.Term` operations. Do not use binary floating point, and do not bloat the `charter prove` kernel evaluator with unreduced rational denominators at runtime.

```
Money<CUR, SCALE> = static (CUR, SCALE) tag over exact Int minor units
Rate = integer basis points / scaled numerator-denominator with explicit Rounding
Quantity<UNIT> = static UNIT tag over exact Int with dimensional checks
Rounding = {floor, ceil, nearestEven, exactOrReject}
```

Currency-conversion quotes (`FxQuote`), custodial accounts, and multi-tier settlement waterfalls belong in `lib/monetary_estate.charter`, while mixing distinct `<CUR, SCALE>` or `<UNIT>` domains without an explicit conversion is rejected statically (`CHR012`). Fees, discounts, transaction cost, capital basis, outstanding collateral and assets remain distinct named types/roles even when denominated in the same currency.

Provide a generic tiered-allocation/settlement library, not a hardcoded obligation formula in the language evaluator. An application supplies its account type, priority tiers, amounts, rates, and precise rounding policy. For a quantity allowance `A`, prior usage `U`, new quantity `Q`, and tier rates `r₁` and `r₂`, a simple capped-tier calculation is:

```
remaining_allowance = max(0, A - U)
quantity_first_tier = min(Q, remaining_allowance)
quantity_second_tier = Q - quantity_first_tier
charge = r₁ * quantity_first_tier + r₂ * quantity_second_tier
new_usage = U + Q
```

For example `A=20`, `U=0`, `Q=300`, `r₁=2%`, `r₂=5%` yields `charge=14.4` in exact-rational arithmetic before applying the explicit currency-rounding rule. A two-transaction and a one-transaction billing history must agree if and only if the governing contract states period-aggregate accounting; the language must not silently choose accounting policy. Concurrent use of the same allowance must be serialized or transactionally reserved.

Reserved obligations: support a generic, source-defined settlement priority (e.g., secured claims, statutory charges, unsecured claims) as an optional institutional library. Never apply a deduction and intercept the same cash flow for the same liability unless the operative source rule expressly requires both. Provide reusable invariants for `no-double-recognition`, `no-double-pledge`, and `consolidated-attribution-no-double-count`, without making any of them universal legal rules.

### 6.4 External assets and accounting events

Core Charter should not hardcode any particular kind of asset, account, or instrument. Optionally provide a reusable financial accounting library with `Asset`, `Holding`, `ControlRelationship`, `Custodian`, `Loan`, `Encumbrance`, `Transaction`, `Valuation`, `ConsolidatedEntity`, and `EvidenceLink`.

Distinguish stocks and flows. Buying a bond converts an asset, and does not by itself create equivalent new income; interest received can create income; a mark-to-market gain may or may not be recognized under the governing source law. A subsidiary's equity interest and its underlying assets must not be counted twice in consolidation.

For off-ledger actors and human accountants: record delegation mandate, require reports and independent reconciliations where the governing rules demand them, treat missing reports as missing evidence or an actual breach of reporting duties, and distinguish principal culpability from delegate misconduct. Charter cannot claim to detect secret property merely because the program asserts a completeness invariant over known records.

### 6.5 Precision and model checking

Quantitative infinite domains defeat naïve exhaustive exploration. Provide three explicitly distinct capabilities: (a) concrete exact arithmetic execution; (b) finite representative bounded exploration with declared `explore-domain`/fairness assumptions; (c) symbolic arithmetic constraints via SMT or solver-backed IR for formulas in a supported decidable fragment. Unsupported nonlinear formulas or external valuation oracles return `unsupported`/`assumed`, not a fabricated proof.

## 7. Verification strategy: from scenarios to proofs

### 7.1 Evidence taxonomy, enforced by the tooling

| Label                              | Precise meaning                                                                                                                              | Permissible examples                              |
| ---------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------- |
| checked                            | A particular evaluator run returned the stated result                                                                                        | Unit/conformance tests, simulation assertions     |
| decided                            | A finite concrete proposition was recomputed and accepted by the Lean kernel                                                                 | Checkpointed trace judgment                       |
| bounded (proposed new label)       | All cases in an explicitly finite explored domain/depth satisfy a property, with complete enumeration certificate or validated solver result | `verify --bound ...`; never call this `proved`    |
| proved                             | A theorem with a checkable proof covers the stated quantified domain, under listed assumptions                                               | Soundness, inductive safety, conditional liveness |
| assumed                            | An external hypothesis or intentionally unproved component of the chain                                                                      | Oracle honesty, trusted clock, verifier soundness |
| inconclusive (proposed new status) | A checker timed out, exhausted memory, under-approximated coverage or hit unsupported syntax                                                 | Report as neither true nor false                  |

The public mission currently names four claim tags. Preserve those four tags if a Law 10 amendment is not accepted, and represent `bounded` and `inconclusive` as result scope/status fields rather than extra claim tags. Either choice must be approved explicitly so the tooling does not quietly violate its own Law 10. This RFC favors retaining the four top-level proof labels, with independent machine-readable `scope` and `completion` fields.

Suggested certificate:

```
{
  "claim": "INV.single_authority",
  "verdict": "holds",
  "assurance": "checked",
  "scope": {"kind": "bounded-exhaustive", "steps": 12, "actors": 3,
            "timeRange": [0, 40], "eventClasses": ["lawful", "unlawful"]},
  "completion": "complete-for-declared-domain",
  "lawHash": "sha256:...",
  "semanticIRHash": "sha256:...",
  "modelHash": "sha256:...",
  "assumptions": ["clock.monotonic", "environment.partial-observability"],
  "checker": {"name": "Charter explorer", "version": "...", "buildHash": "..."},
  "proofArtifact": null
}
```

This JSON is illustrative, not yet a supported API. A truly kernel-proved claim must carry a proof-object/build hash and enough metadata to verify it independently.

### 7.2 Kernel proof layer

Build a semantic bridge from `Surface`/`Resolve.Static` to `Core.Syntax` and `Core.Semantics`. This is the highest-priority formal-methods task. Without it, Core-level metatheorems can be correct while not describing actual `.charter` evaluation.

Proof milestones:

1. Canonical elaboration from checked source constructs into typed CIR; define explicit unsupported cases and a source coverage report.
2. Declarative reference semantics for CIR and typed facts, events, validity, remedies, clocks, and derivation.
3. Evaluator soundness/completeness for the supported CIR fragment, plus determinism of normalized judgments.
4. Invariant preservation for individual transitions and composition, then extension to traces by induction.
5. Quantitative and time refinement, including exact arithmetic and expiry semantics.
6. Rule-amendment preservation with version-stamped transitions and entrenched rights.
7. Proved projection correctness per supported target semantics, including serialization and target language boundaries.

The `Core/Semantics.lean` file already gives a typed deep embedding; retain and extend it rather than inventing another disconnected formal model. `Eval/Properties.lean` contains relevant local lemmas; use these as stepping stones toward a complete operational/declarative correspondence proof. A theorem must quantify over every well-formed program in its stated feature fragment, not just a representative instance.

### 7.3 Concrete decision proofs and scalability

Retain `charter prove`'s checkpointed kernel evaluations. Improve its representation and performance without changing its mathematical proposition:

- Intern names in typed IR; canonicalize sorted fact maps, immutable interned value IDs and timestamps;
- Cache immutable derivation strata and compiled guards by semantic program hash;
- Incrementally recompute only fact dependencies invalidated by a step (with proof of observational equivalence);
- Maintain Merkleized state/checkpoint hashes with inclusion proofs;
- Prove cache reuse/compaction does not change results;
- Keep resource caps for generated kernel work and use separate worker processes;
- Make `Timeout`, `OutOfMemory`, `Unknown` explicitly distinct from a failed legal assertion.

Performance improvements may use optimized native code only if its results are checked or the implementation is proved equivalent. Do not quietly promote an optimized evaluator from "checked" to "proved" based on the existence of a kernel decision path elsewhere.

### 7.4 Safety, bounded response, and liveness

Support at least these temporal-property categories:

```
Always φ                                 // state safety
Always (event -> Next ψ)                 // transition safety
Always (request -> Eventually response)  // liveness
Always (request -> EventuallyWithin Δ response)  // bounded response
Until(φ, ψ) / WeakUntil(φ, ψ)
```

These are proposed surface concepts; settle exact grammar separately. Every temporal proof declares required fairness, scheduler progress, clock divergence, and environment assumptions. Without those assumptions, a server that simply never processes a request may vacuously satisfy many state invariants while violating the institution's promise of bounded adjudication.

For liveness, distinguish unconditional from conditional results. Example: "Every accepted filing eventually receives a decision" is false if all processing stops forever; the proof must explicitly assume scheduler fairness, clock progress and any required service availability.

### 7.5 Native exploration: both compliant and adversarial

Current explorer: breadth-first search of enabled acts, depth and state bounded, explicit enumeration menus. Retain this as `explore --mode lawful`. Add:

- `--mode adversarial`: permitted physical attempt events even when unlawful or legally void; violations are recorded, remedies/findings may follow;
- `--mode mixed`: a bounded adversary controls selected actors, actions, observations and message timing;
- `--coverage`: percentage and list of action schemas and parameter domains actually explored, uncovered/non-enumerable choices;
- `--minimize`: shrink counterexample traces preserving violation and source provenance;
- `--seed`: reproducible fuzzing; `--strategy`: BFS, DFS, stochastic, and coverage-guided;
- partial-order reduction with a proved independence condition for commutative events;
- symmetry reduction for interchangeable actors with formally checked permutation invariance;
- scenario replay and counterexample export to source-level tests.

No `pass` on incomplete search. Display `inconclusive` for missing enumerations, exhausted caps, timed-out solvers, unresolved evidence, or unsupported temporal operators.

### 7.6 Symbolic backends and proof checking (focused 1.0 matrix vs. post-1.0 extensions)

Add a backend-neutral Transition Verification IR (TVIR), derived from CIR with explicit state variables, guarded actions, external nondeterminism, fairness and temporal formulae. To prevent external-toolchain churn from blocking 1.0, **Gate G5 commits 1.0 to five focused verification/guard targets** and defers overlapping research targets to post-1.0 extensions:

**Charter 1.0 Required Targets:**
1. **Kernel proofs (`Prove/`)**: both checkpointed concrete-trace decisions (`decide +kernel`, zero extra axioms) and inductive invariant/ratchet proofs in Lean over `CIR`.
2. **Native explicit checker (`Verify/Explorer.lean`)**: compliant, adversarial, and mixed-mode state exploration directly over the proved `Charter.Eval` transition function, emitting exact counterexamples and finite-domain completeness manifests.
3. **SMT bounded model checking (`Verify/Smt.lean`)**: Z3/cvc5 over `TVIR` for symbolic `Int`/`Money`/`Time` constraints; solver verdicts carry `checked` + `bounded` scope (never `proved` without a kernel-checked certificate).
4. **One external protocol verifier target (`Project/VeilTarget.lean` or `QuintTarget.lean`)**: compilable external specification with pinned toolchain validation, semantic correspondence tests, and counterexample trace replay back into Charter.
5. **On-chain / API execution guards (`Project/ContractABI.lean`)**: compiled and EVM-tested Solidity state-transition guards and canonical JSON ABIs.

**Post-1.0 Optional Extensions (non-blocking for 1.0):**
- Secondary protocol export (the remaining choice between Veil 2.0 and Quint/TLA+ once one ships in 1.0);
- ASP/InstAL-style `clingo` history generator;
- Typed pure-function FFI to external Catala calculators.

Never claim that "the Veil projection is proved" solely because the internal `VeilSpec` structure is proved equivalent to `Law σ`. The produced `.veil` text, its parser, external semantics, and generated executable need their own trusted/refined boundaries. The same holds for EVM bytecode, ABI wrappers, JavaScript libraries, and LLM prompts. Prompt equivalence cannot generally imply deterministic legal compliance of an LLM; a prompt is a non-authoritative explanation/training artifact.

### 7.7 Counterexample and proof-certificate formats

All backends should emit the same trace structure:

```
Counterexample {
  lawHash, irHash, checkerAndVersion, modelAssumptions,
  initialState, orderedEvents [{actor, event, when, knowledge, environmentEffects}],
  legalStateAfterEachStep, observedStateAfterEachStep,
  violatedProperty, decisiveRuleSpans, unsatisfiedOrFailedAssumption,
  replayCommand, minimalityStatus
}
```

A sound external checker may report a proof or a counterexample. A failed/unsupported translation must not be interpreted as proof of absence of bugs. Provide cross-backend differential tests on identical finite fragments; if semantics disagree, fail release gating and create a minimized test fixture.

### 7.8 Model-checking exercise suite

Require benchmark institutions representative of all competitors' strongest domains:

- timed tenancy and sale-of-goods contract (Symboleo lifecycle);
- family-benefit / tax exception computation (Catala-style decision DAG);
- multi-institution access-control + delegation (InstAL reasoning);
- replicated lease, handover and message-delivery protocols under partitions (Veil/Quint temporal safety);
- generic secured loans, tiered fees, receivables, tax/benefit assessments and inter-company accounting (exact arithmetic and attribution);
- lawful but not valid action, unlawful but institutionally valid action, and a proved immunity;
- ratification and amendment across law versions;
- unknown beneficial-owner fact, missing custody report, and an adjudicated finding;
- conflicting jurisdictions and explicit unresolved priority.

For each example publish its source, formal semantics version, assumption inventory, a clean trace, a counterexample, the proof/conformance status, and enough replay instructions for an external reviewer.

## 8. Operational deployment: durable Charter server and enforcement protocol

A production server is essential if Charter is to govern real-world institutions rather than merely inspect simulations. The server evaluates rules and records institutional effects; it does not acquire the legal powers of any actor merely by running the software. All capacities, decisions, and authority relationships are defined by the specific institution being modeled.

### 8.1 Server architecture

```
External actors / agent harness / ERP / custodians / legal portals
                           |
                Authenticated API / SDK
                           |
                  Authorization service
             (state snapshot, quote, reserve)
                           |
        +------------------+-------------------+
        |                  |                   |
    CIR evaluator      Evidence vault     Explanation service
    (pure, pinned)     (typed, signed)     (reason DAG)
        |                  |                   |
        +------------------+-------------------+
                           |
               Institution state machine
         durable log + snapshots + reservations
                           |
        Exporters / audit readers / proof checkers
                           |
           External execution gateway / adapters
```

Define a single-writer logical commit sequence per institution. Preserve `2026-10-22-redesign.md` §3a's **operator-blind artifact boundary**: `charter-server` loads a pre-compiled, signed `Artifact` (`CIR` + source manifest + proof/assurance certificate under one digest), links `Core`, `Eval`, `Artifact`, and `Server` only (never `Surface/` or `Resolve/`, enforced by an import-graph gate), and executes the **exact same proved `Charter.Eval`** as the compiler. Runtime amendments submit a new compiled `Artifact` checked against the active law's `Amend` rules, `Immunity` ratchets, and certificate requirements before taking office. Physical implementation may use a leader/replicated state machine, but its consistency semantics and failover policy must be explicit and modeled. No temporary memory state may become the sole authoritative version. Use an append-only signed event log with cryptographic state roots and independently backed up snapshots. The server's source-of-truth boundary is its committed legal state plus authenticated observations, not the agent's natural-language request.

### 8.2 API (proposed JSON/HTTP and optional MCP binding)

| Operation              | Meaning                                                                      | Side effects                                            |
| ---------------------- | ---------------------------------------------------------------------------- | ------------------------------------------------------- |
| `CreateInstitution`    | Install approved source manifest, signed CIR, parameters, genesis state      | New institution only after checks                       |
| `GetLaw` / `GetState`  | Retrieve law/state version and allowed audience view                         | None                                                    |
| `Evaluate`             | Hypothetical outcome of a proposed event at a specified version              | None                                                    |
| `Reserve`              | Atomically reserve capacity/assets or a deadline-governed authorization slot | Reservation log event                                   |
| `Authorize`            | Issue a constrained execution capability after compliant/valid judgment      | Authorization record, not external action               |
| `ConfirmExecution`     | Submit authenticated result/receipt; settle committed effects                | State and economic log commit                           |
| `ObserveExternal`      | Record externally occurring activity, lawful or unlawful                     | Observational history; triggers permitted legal effects |
| `SubmitEvidence`       | Add/revoke/supersede evidence with chain-of-custody                          | Evidence record, optionally derived re-evaluation       |
| `ExercisePower`        | Submit a legally relevant institutional act (e.g. file, rule, ratify)        | Conditional valid legal effects                         |
| `AdvanceClock`         | Authenticated time progress, expiries and deadlines                          | Timed step and obligation changes                       |
| `Explain` / `Trace`    | Proof/reason/citation graph                                                  | None                                                    |
| `AppealOrChallenge`    | Exercise a defined procedural right                                          | Institution-defined proceeding                          |
| `Subscribe`            | Stream changes for a principal/custodian/monitor with scope                  | None                                                    |
| `Replay` / `VerifyLog` | Recompute state from immutable evidence and committed events                 | None (offline checker)                                  |

All responses include institution ID, law version/hash, state version, evidence root, time model, decision ID, relevant source span IDs, evidence statuses, decision assurance level, and signature of the server or permitted quorum. `Authorize` must be idempotent on a client-generated intent ID and unambiguously bind to exact action parameters.

### 8.3 Preflight-to-execution protocol

Do not treat an external side effect as atomically roll-backable just because an internal legal state transition is atomic.

```
1. Proposal(intent_id, typed action, max effects, requested deadline)
2. Evaluate against immutable (lawHash, stateVersion, evidenceRoot)
3. If prerequisites met: Reserve resources/authority within serializable transaction
4. Issue signed, short-lived, least-privilege AuthorizationToken
5. Trusted execution gateway validates token and performs precisely that operation
6. Receive external signed receipt / observe outcome
7. Reconcile reservation, commit legal effects, post fees and obligations
8. If uncertain/failure: enter PendingExternalOutcome; never assume rollback
9. Resolve by replay-safe reconcile/compensation under explicit legal rules
```

The server must have an idempotency guarantee across retries and crashes. Tokens are bound to institution, law hash, state version or reservation version, actor, delegated mandate, operation type, exact args (or canonical digest), max value, external destination, expiry, unique nonce, and execution count. A token cannot authorize an arbitrary later operation or broaden delegation. Implement transaction budgets and irreversible-action cooldowns only when law grants the power to impose them.

For actions requiring an instantaneous legal state update, use compare-and-swap state versions or serialized transactions. For external bank transactions, physical transfers or human actions, use saga/compensation semantics, preserving the actual event and recording breach/remedy if a prohibited action occurred.

### 8.4 Lawful-action entitlement in the service

The authorization service is not a discretionary censor. Under a declared decision policy:

```
If (lawful == yes) and (valid == yes) and evidence satisfied
   and required reservation successful -> Authorize
If (lawful == no) or (valid == no) -> Deny with rule and facts
If necessary evidence unresolved -> NeedEvidence/ReferForFinding
If operationally unavailable -> Unavailable with retry/recovery reason
```

Lawful but institutionally invalid operations may have no effective action to authorize. Lawful-action entitlement applies to actions legally within the service's granted execution jurisdiction, not to physically impossible operations or interactions with unbound third parties. Resource locks, conflicts and capacity caps must be specified in the institution; server infrastructure failure is operational unavailability, not an invented legal denial. Never silently interpret model advice as a binding source of law.

### 8.5 External observations, human contractors and delayed evidence

Many events occur outside the server: a hired accountant opens an account, a customer disputes a charge, a vault changes inventory, or a malicious host disconnects an agent. `ObserveExternal` creates a provenance-bearing observation, not a presumption of lawful authorization. Observations can arrive late, duplicated, contradictory, or malicious.

Maintain separate event-time, observation-time, and adjudication-time. Provide reconciliation policies: historical projection, corrective adjustment, voidability, retroactivity only when allowed, restitution claim, unknown provenance, or escalation to findings. The engine must not invent a clean history by deleting an inconvenient observation. A legal program may require an accountant's reporting duty and let the agent terminate an uncooperative mandate; the runtime cannot guarantee omniscient visibility over that accountant.

### 8.6 Storage and consistency contract

Recommended data stores:

- Canonical event store: `(institutionId, seqNo)` unique, append-only, signed; supports legal acts, external observations, findings, time advances and amendments.
- Materialized state: deterministic replay from genesis; cached as Merkleized snapshots verified against log tail.
- Evidence vault: content-addressed objects with ACL, signatures, issuers, acquisition time, validity and supersession/withdrawal chain; privacy-preserving references and hashes in audit log.
- Authorization reservations: serializable resource locks, expiry and reconciliation states.
- Proof/assurance store: proof artifacts, bounded-search manifests, compiler/version hashes, external assumptions.

Use a database with serializable transactions for the first implementation. Distributed operation can follow after formalizing and testing a consensus/failover protocol. Never claim single authority in a distributed deployment purely because the database shows one `activeLease` fact. The issued credentials, old hosts, network partitions and timeout/fencing guarantees are part of the property.

### 8.7 Service security and operating governance

Threats: malicious principals; dishonest delegates; compromised server; compromised oracle; privilege escalation; stolen authorization tokens; replay; equivocation; log tampering; late receipts; unsafe projection changes; key compromise; DoS; corrupt adjudicator; supply-chain attack; cross-tenant data disclosure. For each, define prevention, detection, recovery and unpreventable residual risk.

Minimum controls: mTLS or equivalent authenticated channel; short-lived scoped capability tokens; HSM-backed signing where justified; deny insecure defaults; tenant isolation; least-privilege service accounts; per-operation idempotency; strong secrets management; auditable admin operations; legal-institution version pinning; rate limits; offline replay verifier; monitored resource budgets; external independent backups; redaction/audience separation; security-reviewed dependencies; reproducible builds with SBOM and provenance.

When a deployment claims enforceable veto, every side-effecting action in the claimed scope must traverse a gateway the principal cannot bypass. The server should report enforcement coverage: tool/action classes mediated, unmanaged channels, externally delegated powers, unverified financial custody, and residual trust assumptions. An incomplete enforcement boundary must never be represented as full constitutional enforcement.

### 8.8 Example wire protocol (illustrative)

```
{
  "request": {
    "type": "Evaluate",
    "institutionId": "acme-lease",
    "lawHash": "sha256:approved-law",
    "stateVersion": 912,
    "intentId": "6dc5dafe-...",
    "actor": "custodian-3",
    "action": {"type": "Transfer", "asset": "asset-42", "amountMinor": "120000"},
    "evidenceRefs": ["ev:loan-limit-22"]
  }
}
```

```
{
  "decision": {
    "outcome": "NeedEvidence",
    "lawful": "undetermined",
    "valid": "undetermined",
    "stateVersion": 912,
    "missing": ["beneficial-owner-of-destination"],
    "reasonIds": ["CONTRACT.TRANSFER.ELIGIBILITY"],
    "expiresAt": null,
    "assurance": "checked"
  }
}
```

Canonical serialization must specify strings, decimal amounts, timezone/clock handling, absent vs. null values, normalized identifiers, and signature scheme. No trust decision should depend on an LLM rewriting this JSON.

## 9. Verified projections and interoperability

### 9.1 Projection architecture

Every target takes CIR or verified TVIR, never independently re-parsed English. Partition target features into `supported`, `lowered-with-assumption`, and `rejected`. The projection API must return a feature-coverage manifest; no silent weakening of an immunity, duty, evidence requirement, or amendment rule.

Define a formal refinement statement for each compiler target:

```
SourceLaw L --compile--> TargetArtifact A
For all admitted inputs/traces τ in declared fragment F:
  ObserveTarget(A, encode(τ)) = encode(ObserveCharter(L, τ))
under explicitly named environmental / arithmetic / toolchain assumptions.
```

If proving arbitrary source rendering is impractical, create a small independent target validator that parses generated target syntax and checks a semantic relation to CIR. The distinction between proved internal IR correspondence and checked external compiler output should always appear in the certificate.

### 9.2 Veil target

Retain existing `Projection/Veil.lean` theorems for internal `VeilSpec` (they are useful). Add:

1. A typed external Veil AST conforming to a pinned Veil version, not merely generated strings;
2. A renderer and parser validation round-trip, acceptance by an actual Veil installation, and source-span mapping;
3. A translation proof/validated checker linking CIR transitions and target transitions;
4. Two emitted models: compliant-authorized and adversarial-physical, including delayed and unknown world observations;
5. A verified mapping of safety/temporal properties and explicit unsupported fragment diagnostics;
6. A trace importer proving or validating that the external counterexample replays under Charter.

Minimum end-to-end acceptance: a generated, externally accepted model of a generic distributed lease-handover protocol finds an intentionally introduced partition-time double-authorization counterexample and proves or exhaustively checks a corrected finite model under declared clock and message-delivery assumptions.

### 9.3 Quint and TLA+ target (1.0 alternative protocol target / post-1.0 companion)

Emit an idiomatic typed Quint module or TLA+ model with nondeterministic action choice, init, next-state relation, safety properties, fairness assumptions and scenario constants. Use Apalache (bounded/symbolic) and TLC (finite exhaustive) according to their actual guarantees. Clearly report backend and bound. Support importing traces into Charter and minimizing them while preserving provenance. (Gate G5 requires shipping end-to-end validation for at least one of Veil §9.2 or Quint/TLA+ §9.3 in 1.0, depending on upstream Veil 2.0 toolchain stability.)

### 9.4 ASP/InstAL target (post-1.0 optional extension)

Generate ASP encodings only for the supported finite institutional fragment (events, derived facts, deontic states, constraints, timesteps, action choices). Use `clingo` to search for existential histories and adversarial combinations. Verify generated answers against native Charter evaluator, and require a correspondence theorem or independent validated translation before advertising soundness. Non-stratified negation or infinite arithmetic domains must be rejected or explicitly bounded. Deferred past 1.0 because native adversarial exploration (§7.5) and SMT bounded model checking (§7.6) cover existential trace search in 1.0 without an additional external solver dependency.

### 9.5 Catala and deterministic calculation interoperability (post-1.0 optional extension)

Provide typed foreign pure-function interfaces to certified financial/benefits calculators in a post-1.0 extension; do not embed arbitrary filesystem, network, or mutable external function calls inside evaluable legal rules. In 1.0, statutory default/exception decision DAGs (§4.4) and scaled integer `Money`/`Quantity` arithmetic (§6.3) are supported natively inside Charter. When an externally compiled calculator is later connected, show `assumed` unless formally verified against `CIR`.

### 9.6 Smart contracts and EVM targets

Distinguish guard generation from full contract deployment. Existing source generation in `ContractABI.lean` is a starting point, but target claims require:

- target restrictions (no impossible unbounded state, no unsupported oracle assumptions, explicit gas/storage bounds);
- unit-precise integer and overflow semantics, immutable law hashes, time-source assumptions;
- explicit external custody assumptions and on-chain facts only;
- ABI/schema/hash consistency, signature checking, replay resistance and upgrade controls;
- compile emitted Solidity, run static analyzers and adversarial EVM tests;
- verify the supported target fragment against a formal or independently checkable EVM semantics, or explicitly mark generated output as unverified prototype.

Do not claim smart-contract verification for an off-chain bank transfer simply because an on-chain legal guard is correct.

### 9.7 AI-facing projections

Generate (a) human-readable rule summaries and (b) model-consumable tool schemas with source spans, but never call a system prompt a semantics-preserving enforcement mechanism. LLMs may decide what to propose, surface relevant evidence, and explain reasons; the deterministically checked tool server remains authoritative for decisions. Any `training_row_faithful_to_semantics` theorem demonstrates the structure of generated examples, not the future behavior of a trained model. Include model uncertainty and prompt-injection restrictions in integration docs.

## 10. Developer experience and product competitiveness (L4 / Catala gap)

### 10.1 Unified CLI

Keep existing `check`, `run`, `test`, `trace`, `repl`, `prove`. Add or complete:

```
charter init [template]             # reproducible project manifest + UAT
charter fmt                         # canonical formatting
charter doc                         # human-readable rule book + annotated source
charter build                       # emit content-addressed Artifact (CIR + manifest + cert)
charter explain DECISION            # audience-aware reason graph
charter diff OLD NEW                # source/rule/behavior semantic diff
charter verify [--backend ...]      # inductive/finite/smt verification (never names engine)
charter explore [--mode ...]        # lawful, adversarial, and mixed-mode exploration
charter generate --target ...       # certified/qualified projection (solidity, abi, veil/quint, prompt)
charter package / publish / fetch   # pinned modules & signatures
charter doctor                      # checks dependencies, trust, and assurance coverage
charter-server serve <artifact>     # durable operator-blind institution server
charter-server replay / audit       # verify externally supplied log/receipts against artifact
```

All commands should support machine-readable JSON with stable schemas, distinct exit codes for false claims vs. incomplete checking vs. tool error, and explicit proof status. Error messages, help text, and CLI flag names must use Charter's own terminology and never expose engine internals (`Lean`, `Lake`, `tactic`, `sorry`) unless `--show-checker` is explicitly passed (preserving Mission Law 11 and `test/gates/law11-no-engine-in-output.sh`).

### 10.2 IDE / LSP

Provide a Language Server Protocol implementation supporting syntax highlighting, formatting, diagnostics, semantic completion, inlay types, clause span navigation, `go to` legal source, refactoring of stable rule IDs, symbol search, rename, proof/assumption hovers, counterexample traces, and semantic-diff previews. Integrate with VS Code first, then editor-neutral LSP clients. Provide visible consequences of `Amend`: which rules, definitions, examples and proof obligations become stale.

### 10.3 Lawyer- and policy-author-facing views

Generate:

- consolidated statute/contract with side-by-side formal rules;
- a decision table for exceptions and conditions;
- obligation timeline and lifecycle diagram;
- power/standing/beneficiary graph and conflict-of-interest matrix;
- legal-effect trace distinguished from physical occurrence;
- counterexample narrative with exact clause references;
- assurance report stating verified, checked, bounded and assumed elements.

The default human view should explain why the result follows from the source rule, not print a wall of evaluated facts. Reuse source spans without requiring users to know Lean or machine proof syntax.

### 10.4 Packages and reproducibility

Define `charter.toml` (proposed) with language version, source manifests, module dependencies, verified library packages, trusted oracles, legal jurisdictions, permitted backends, deployment policies, and proof minima. Dependencies are locked by content hash and publisher signature. Module versions use semantic compatibility rules; breaking changes to rule meaning require explicit migrations. Provide an offline build with archived source/docs/proof dependencies so that a law decided in 2050 can still be audited in 2226.

### 10.5 Adoptable templates and integration adapters

Ship domain-neutral templates for commercial agreements, leases, service-level agreements, debt/collateral, simple voting, delegated authority, arbitration, public-law eligibility and financial accounting. Keep applications, their interpretations, and their domain-specific benchmarks entirely in their own repositories and CI. Provide SDKs for TypeScript, Python and Rust/Go based on OpenAPI/JSON Schema and a reference HTTP/MCP server. Expose tools only for typed querying and action proposals, not unrestricted mutation of state.

### 10.6 Documentation standards

Publish one canonical versioned language specification with a complete grammar, operational/declarative semantics, examples, errors, compatibility profiles, trust model, target coverage and proof legend. Keep a beginner tutorial and expert reference. Require a test for every normative specification sentence and a stable URL for each versioned section. A claim in README must link to the test/theorem/certificate that establishes it.

## 11. Implementation architecture and ownership by source directory

### 11.1 Proposed modules and refactor boundaries

Keep the current `src/Charter/{Surface,Resolve,Core,Eval,Prove,Projection,Cli}` division; add the following organized subsystems. Names below are proposed and do not imply the files exist today.

```
src/Charter/
  Surface/
    Lexer.lean, Ast.lean, Parser.lean   # unified grammar with contextual Charter keywords
    Pretty.lean                         # canonical formatter and round-trip validation
  Resolve/
    Static.lean                         # name/type/arity/scale/stratum & Default DAG checks
    ElaborateCIR.lean                   # total elaboration to canonical CIR
    AssuranceGates.lean                 # opt-in static gates (--require-provenance, etc.)
  Core/
    Term.lean, Spec.lean, State.lean    # compact kernel-reducible CIR & state
    Transition.lean                     # independent declarative Prop transition relation
    Derivation.lean                     # declarative least-fixpoint & stratification Prop
    Evidence.lean                       # 4-valued Open/Evidenced status & Finding records
    Defeasible.lean                     # stratified Default/Exception/Priority & Conflict
    Scale.lean                          # static Money<CUR,SCALE> & Quantity<UNIT> tags over Int
    Amend.lean                          # rule-level Amend, LawVersion, reflexive entrenchment
    Provenance.lean                     # multi-document SourceRef, SHA-256 digests, ReasonGraph
    Composition.lean, Ratchet.lean      # compositional & ratchet metatheorems over CIR
  Artifact/
    Format.lean, Hash.lean, Cert.lean   # content-addressed bundle consumed by charter-server
  Eval/
    Eval.lean, Interpreter.lean         # single executable evaluator (with DomMap / interning)
    Properties.lean                     # eval_sound, eval_complete, derives_least_fixpoint
  Verify/
    Temporal.lean, Explorer.lean        # lawful, adversarial, and mixed-mode state explorer
    TVIR.lean, Smt.lean                 # symbolic transition IR and Z3/cvc5 BMC adapter
    Counterexample.lean, Coverage.lean
  Prove/
    Run.lean, LeanGen.lean, Kernel.lean # checkpointed kernel decisions & inductive obligations
  Project/
    ContractABI.lean, VeilTarget.lean, QuintTarget.lean
    Prompt.lean, Views.lean, Diff.lean, Soundness.lean
  Server/                               # imports Core, Eval, Artifact, Server ONLY (operator-blind)
    Protocol.lean, StateStore.lean, Auth.lean, Reservations.lean
    EvidenceStore.lean, Replay.lean, Clock.lean, Audit.lean, Api.lean
  Cli/
    (Check, Run, Test, Trace, Prove, Explore, Verify, Build, Diff, Explain, Fmt, Doc, Doctor)
  Lsp/
    Server.lean, Diagnostics.lean, SourceNavigation.lean
lib/
  contract_lifecycle.charter            # Symboleo-grade contract & obligation lifecycles (§4.2)
  agency_mandate.charter                # mandates, attribution, notice & apparent authority (§4.3)
  monetary_estate.charter               # accounts, tiered waterfalls, consolidation (§6.3–6.4)
  jurisdiction.charter                  # hierarchical authority & conflict-of-laws patterns (§4.6)
  ... existing 8 institutional modules + lib/lean/ proofs ...
docs/
  spec/001..020 + semantics + trust + assurance-levels
  plans/ + meetings/ + examples/
test/
  spec/ lib/ prove/ verify/ projections/ server/ gates/
  eflint-corpus/
```

Ownership rule: Parser owns syntax, resolver owns names/types/scales/strata, `Core` owns minimal normative `CIR` data and declarative `Prop` relations, `Eval` owns the **single** executable evaluator (`Mission Law 9`), `Prove`/`Eval/Properties.lean` own kernel-checked correspondence proofs, `Artifact` owns the compiled bundle, `Server` owns durable operator-blind state transitions, `lib/*.charter` owns domain-neutral legal ontologies (`Contract`, `Mandate`, `MonetaryEstate`, `Jurisdiction`), and adapters own external execution. No two subsystems may independently invent semantics for `valid`, `lawful`, time, or derived facts.

### 11.2 Internal typed data models

Use stable identifiers and strongly typed addresses:

```
ActorId, InstitutionId, RuleId, ClauseId, SourceDigest, EvidenceId,
EventId, DecisionId, StateVersion, LawVersion, FactId, PowerId,
ObligationId, MandateId, CurrencyCode, AssetId, IssuerId
```

No unqualified string comparisons as the fundamental identity semantics of legal entities. Strings are for external names and documents; core identifiers are typed and namespaced. Equality and role aliasing should have a proved canonicalization discipline. Avoid permanently assuming actors, claims and events are drawn from fixed finite enumerations: proof search can instantiate finite worlds, but live state must support new parties and identifiers.

### 11.3 Declarative `Prop` specification and single executable evaluator (`Mission Law 9`)

Per `Mission Law 9` (*"There is no second interpreter"*), Charter must **not** ship two competing executable evaluators that could diverge at runtime:

- **Declarative specification (`Core/Transition.lean`, `Core/Derivation.lean`)**: small, transparent inductive `Prop` relations defining term evaluation, Tarski least-fixpoint derivation per stratum, occurrence/lawfulness/validity, simultaneous effect merge, and clock progression.
- **Single executable evaluator (`Eval/Eval.lean`, `Eval/Interpreter.lean`)**: structural-recursion evaluator (with transient `DomMap` radix indexing, interned identifiers, and incremental stratum caching) compiled into both `charter` and `charter-server`, and **proved sound and complete** against the declarative `Prop` relations (`eval_sound`, `eval_complete`).

Every optimization to `Eval` (indexing, interning, incremental invalidation across `Amend` or clock steps) must preserve kernel reducibility for `charter prove` (`decide +kernel`, zero extra axioms) and update the correspondence proof in `Eval/Properties.lean` in the same commit. Property-based tests supplement, never replace, the correspondence theorem.

### 11.4 Runtime execution states

Define and test a transaction lifecycle:

```
Proposed -> Evaluated -> Reserved -> Authorized ->
  {ExecutedConfirmed, ExecutedUnknown, ExpiredUnused,
   Rejected, Disputed, Compensated}
```

The lifecycle is not a second source of legal authority. It records service execution state and maps to institutional acts only when source law specifies. Define per-state allowed operations, idempotent retries, and recovery after crash. `ExecutedUnknown` must not automatically release reserved collateral, nor permit an unbounded repeat payment; compensation and investigation follow law and external evidence.

### 11.5 Performance targets (measured, not assumed)

Target measurements should include parse/resolution time, evaluator step latency, derived-fact recomputation, state memory, proof time, proof memory, bounded search throughput, server authorization p50/p95/p99 latency, recovery time and external-target compilation. Publish workloads and hardware. Establish a target contract rather than inventing unmeasured goals:

- Every authorization path meets a configurable per-institution deadline or returns `Unavailable`, never a silently guessed ruling.
- Every proof/checking run obeys configured memory and time caps and emits the correct completeness status.
- Large facts and documents are indexed rather than repeatedly parsed on every evaluation.
- Historical records remain replayable under the pinned original semantic version.
- A cold-started server independently reconstructs the same state root and decisions from a signed log.

Only fix numerical latency SLAs after measurements on representative real workloads; do not write unsupported capacity claims into the specification.

## 12. Compatibility, versioning and migration

### 12.1 Unified language semantics and opt-in static assurance gates

Charter ships **one unified language grammar and semantics** — a strict syntactic and semantic superset of stratified eFLINT 4.1 (`Mission Law 12`, `Mission Law 13`) — rather than diverging `eflint-4.1-compat` and `charter-1.x-strict` profiles:

1. **Unified parser & core semantics**: Contextual keyword parsing accepts every stratified `.eflint` and `.charter` file under a single deterministic grammar (one unambiguous spelling per construct). `Act` defaults to `Valid when True` (`D5`), `Power` requires explicit `Valid when`, `Closed` and `Open`/`Evidenced` facts coexist cleanly, `[start, end)` half-open expiry (`now < u`) holds everywhere, and cyclic self-negation in `Holds when`/`Derived from` is rejected with `CHR020` (`D6`).
2. **Machine-auditable upstream tolerance manifest**: Every behavioral difference from Haskell `eflint-4.1.0.1` in `test/eflint-corpus/tolerances.md` is backed by a structured entry (fixture, upstream `eflint-4.1.0.1` result, Charter result, root-cause bug/decision ID, and conformance test).
3. **Opt-in static assurance gates (orthogonal to semantics)**: Projects and CI pipelines enable higher assurance checks via `charter.toml` or CLI flags (`--require-provenance`, `--require-complete-explore`, `--deny-warnings`, `--forbid-midstream-decls`) that enforce static completeness and auditability requirements **without ever changing the operational or declarative meaning of a phrase**.

### 12.2 Migration from the current branch

1. Complete `D10` Phase-0 cleanup: remove linked v0.3 Lean companions (`Examples/SovereignAgency`, `Examples/AutonomousCommons`, `import Examples` in `src/Main.lean`, `charter_*` macros, and v0.3 `Core/Syntax.lean` / `Core/Semantics.lean` duplication) after verifying neutral conformance coverage.
2. Replace lexer-reserved `charterWordKeywords` with contextual parser keywords so `.eflint` and `.charter` share a single lexer and grammar without `--eflint` mode divergence.
3. Evolve `Core.Spec` and `Core.State` directly into canonical `CIR` feature by feature, proving `eval_sound` and `eval_complete` against `Core/Transition.lean` + `Core/Derivation.lean` before adding G3 extensions.
4. Add multi-document `SourceRef` SHA-256 digests and semantic `CIR` hashes alongside legacy FNV-1a clause approval hashes during migration.
5. Add the four minimal core G3 extensions (`Evidence`/`Finding` on `Open` facts, stratified `Default`/`Priority`, rule-level `Amend`/`Regime`, and `Money`/`Quantity` scale tags over `Int`), while implementing `contract_lifecycle`, `agency_mandate`, `monetary_estate`, and `jurisdiction` as `lib/*.charter` modules.
6. Build `Artifact`, `Verify` (adversarial/mixed explorer + SMT), and operator-blind `charter-server` directly over `CIR` and `Charter.Eval`; keep `check`, `run`, `test`, `trace`, and `prove` backward-compatible.
7. Publish a regression diff report over `test/spec/`, `test/lib/`, and `test/eflint-corpus/`; third-party applications manage their own migration on independent release cadences.

### 12.3 Public version and release policy

Use semantic versioning for language semantics and a distinct compatibility version for target/proof formats. A patch release may improve performance or diagnostics without changing normative meaning. A minor version may add opt-in constructs. A major release changes default semantic judgments or the source grammar. Keep signed, reproducible artifacts for each release. Do not describe a breaking semantic correction as a nonbreaking bug fix just because it is desirable.

### 12.4 Schema and API compatibility

The API should version its JSON schema separately from the legal program. Clients must pin accepted schema versions. A new API field must not change old authorization meaning; a revoked token must never become valid because a server version interprets it differently. Incompatible changes require new token domains, law hashes and explicit migration strategy.

## 13. Concrete implementation work packages and dependency graph

A feasible path is depth-first in correctness: finish one complete vertical slice, then generalize. Each package below has concrete deliverables and acceptance gates. Work may proceed in parallel only where the semantic interfaces are already settled.

### WP-0 — Claims and baseline reproducibility (G0)

Implement: audit the README against code and tests; perform the G0 independence cleanup (mission, battery, examples and normative docs); complete an assurance-claims table; pin source, compiler, dependency and proof-tool versions; define trust boundaries; move unimplemented features to the roadmap. Reconcile stale or contradictory counts between documentation, tests, and current artifacts without importing external application metrics into product claims.

Files: `README.md`, `docs/mission.md`, `docs/spec/README.md`, `docs/trust.md`, `tools/battery` and a new machine-readable `claims.json`.

Exit: Every promotional sentence about proof, compatibility, projections or server functionality points to an existing test, theorem or explicit planned milestone. An unfulfilled guarantee cannot be displayed as implemented.

### WP-1 — Unified grammar, contextual keywords, and typed CIR (G1 foundation)

Implement: finish spec 001, 017, 019, 020; make Charter single-word additions contextual in the parser so `.eflint` and `.charter` parse identically under one grammar; evolve `Core.Spec` into canonical `CIR` with deterministic serialization (`Artifact`); test parser/formatter round trips, aliases, case distinctions, well-formedness and stable hashes.

Exit: All supported `.eflint` and `.charter` constructs elaborate to `CIR` or return a typed `CHR` rejection with source location. No undocumented grammar behavior and no `--eflint` profile split. All `eflint-4.1.0.1` tolerances are machine-auditable.

### WP-2 — Declarative semantics and evaluator correspondence (G1)

Implement: independent semantics for facts, derivation, acts, duties, powers, immunities, time, quantity, scenarios; soundness/completeness connection to live evaluator; least-fixpoint and simultaneous-effect semantics; deterministic replay.

Exit: All semantics in the supported core fragment are covered by kernel-checked refinement theorems. No independent `Core` theorem is advertised as proof of live behavior before the bridge is complete. Include intentionally faulty evaluator regression fixtures showing that the proof/build gate fails.

### WP-3 — Reliable proof/evaluation infrastructure (G1/G2)

Implement: state interning, dependency-indexed incremental evaluation, exact arithmetic, checkable checkpoint certificates, resource cap/timeout statuses, proof-manifest format and independent replay verifier.

Exit: Large-protocol tests are reproducible and report complete vs. incomplete proof outcomes truthfully; optimization changes require proof or checkable result. `charter prove` never claims success on exhausted resources.

### WP-4 — Adversarial and temporal verification (G2)

Implement: lawful/adversarial/mixed exploration, finite coverage report, fairness/time semantics, temporal syntax, counterexample minimization, symbolic TVIR, solver integration, proof/assumption manifest.

Exit: Known counterexample workloads are found without manually supplying exact offending traces; in correct finite models the explorer finishes and emits a complete-domain certificate. Liveness property with impossible fairness premise is reported as conditional or unproved, not green.

### WP-5 — Minimal core extensions, standard-library ontology, and source authority (G3)

Implement: in `Core`/`Resolve`/`Eval`, add only the four minimal G3 primitives (`Power` requiring `Valid when`, 4-valued `Evidence`/`Finding` on `Open` facts + `ReasonGraph`, stratified `Default`/`Priority` with `Conflict`, rule-level `Amend`/`Regime` with reflexive `Immunity` entrenchment, multi-doc SHA-256 `SourceRef`, and static `Money`/`Quantity` scale tags over `Int`); in `lib/*.charter`, ship verified `contract_lifecycle`, `agency_mandate`, `monetary_estate`, and `jurisdiction` modules with proved invariants (`D8`).

Exit: A real-inspired sale-of-goods, delegated accountant (`TreasuryMandate` §16), multi-jurisdiction contract, amended constitution, and benefits-calculation suite all execute with source-linked rulings, preserved `charter prove` kernel reducibility, and proved `eval_sound`/`eval_complete` coverage. Confirm that lawful-but-void, unlawful-but-effective, and unknown-fact cases all remain distinct.

### WP-6 — Deployable operator-blind server and audit (G4)

Implement: `Artifact` bundle (`CIR` + source manifest + certificate), standalone `charter-server` executable (linking `Core`, `Eval`, `Artifact`, `Server` only — `operator-blind` gate), transactional state store, authentication, `Evaluate`/`Reserve`/`Authorize`/`ConfirmExecution`/`ObserveExternal` API, capability tokens, deterministic replay, evidence vault, clock service, audit root and signatures, role/tenant isolation.

Exit: `operator-blind`, `replay`, and `certificate-at-office` gates pass; crash/retry/reorder/failover tests demonstrate no double execution authorization, no lost legal state, no unauthorized tool action in the declared enforcement scope, and identical replay state roots. Report coverage exclusions explicitly.

### WP-7 — Focused 1.0 backends and end-to-end projection assurance (G5)

Implement: typed target ASTs, certified/validated renderers, parser round trips, external integration for one 1.0 protocol verifier (`VeilTarget` or `QuintTarget`) plus compiled/EVM-tested Solidity/JSON ABI guards (`ContractABI`), SDKs and OpenAPI/MCP schemas, target coverage manifests. (ASP/`clingo` and Catala FFI remain optional post-1.0 packages.)

Exit: Each advertised 1.0 target has (i) actual external compiler/checker acceptance, (ii) a `CIR`-to-target fidelity theorem or clearly scoped validator, (iii) cross-trace differential tests, and (iv) machine-readable unsupported-feature rejections. A projected prompt is labeled advisory.

### WP-8 — IDE, publication and competitive adoption (G5)

Implement: formatter, LSP, explanations, semantic diff, visual reports, package manager/lockfile, documentation, versioned examples and deployment templates.

Exit: A new user can create a law, inspect its source-linked rules, test adversarial scenarios, receive a reasoned authorization, deploy a small institution, and audit its decisions without reading Lean. An external evaluator can run the published conformance suite from a clean checkout.

### 13.1 Critical dependency ordering

```
WP-0 (truthful baseline)
  -> WP-1 (canonical syntax + typed CIR)
     -> WP-2 (formal semantics + evaluator proof)
        -> WP-3 (certified, scalable evaluator)
           -> WP-4 (verification) ------+
           -> WP-5 (new legal features) +--> WP-7 (verified projections)
           -> WP-6 (server) ------------+
                                       -> WP-8 (product polish)
```

WP-5 can develop legal ontology before WP-4 finishes, but must not merge extensions without proof/verification requirements specified. WP-6 can build operational scaffolding early, but the deployed authorization path must pin a semantic fragment covered by WP-2. WP-7 must not bootstrap on a target renderer whose format is merely assumed to be syntactically valid.

## 14. Formal conformance and acceptance test matrix

Every feature gets positive, negative, boundary, adversarial and metamorphic tests. A test suite is not a substitute for proof; tests prevent regressions and expose wrong interpretations.

| ID  | Required test                                                                                           | Expected semantic result / failure condition                                                                            |
| --- | ------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| T01 | Unlawful host cuts service                                                                              | Occurred physical event, duty breach, legal effect and remedy assessed separately                                       |
| T02 | Panel orders termination lacking valid power                                                            | Occurred; order institutionally void; target state unchanged by void power                                              |
| T03 | Immunity defeats otherwise authorized power                                                             | `valid=no` with immunity clause; provenance included                                                                    |
| T04 | Extralegal advisory annotation accompanies an otherwise lawful event                                    | Advisory data never changes lawfulness or validity unless an operative rule expressly incorporates it                   |
| T05 | Actor identity renamed in otherwise identical state                                                     | Same legal result when the identifier is not legally relevant (metamorphic impartiality)                                |
| T06 | Unknown related-party status                                                                            | Returns legally specified default or evidence requirement; no invented fact                                             |
| T07 | False evidence and contrary evidence submitted                                                          | `Conflicted`, finding required if decision depends on status                                                            |
| T08 | Judgment with missing provenance                                                                        | Fails compliance-quality gate; no full-coverage certificate                                                             |
| T09 | Two simultaneous draws against a capped contractual account                                             | Aggregate cannot exceed the balance; no double allocation                                                               |
| T10 | Tiered fee crosses a quantity allowance: `allowance=20`, `used=0`, `purchase=300`, `feeA=2%`, `feeB=5%` | 20 units in tier A, 280 in tier B; exact total fee `0.4+14=14.4` before declared rounding                               |
| T11 | Tiered charge split across multiple transactions                                                        | Aggregate equals the declared billing-period rule; rounding/order dependence is explicit                                |
| T12 | Same expense capitalized and expensed                                                                   | Second recognition invalid / violation per governing rules                                                              |
| T13 | Same collateral double-pledged                                                                          | Duplicate available capacity never created                                                                              |
| T14 | Subsidiary interest and underlying assets consolidated                                                  | Consolidation does not double-count net holdings                                                                        |
| T15 | Out-of-scope delegate action                                                                            | Event recorded; no unsupported principal authority; liability determined by stated rule                                 |
| T16 | Valid accountant delegation followed by undisclosed transaction                                         | Missing evidence/report obligation represented; no pretend omniscience                                                  |
| T17 | Delegate mandate revoked but later purportedly exercised                                                | Validity follows effective notice/apparent-authority clauses                                                            |
| T18 | Subcontracting vs. assignment vs. novation                                                              | Different obligated parties and discharge statuses as encoded                                                           |
| T19 | Contract half performed before deadline                                                                 | Partial satisfaction, remaining obligation and remedy status correct                                                    |
| T20 | Breach occurs while contract still in force                                                             | Breach does not terminate contract absent governing rule                                                                |
| T21 | Two conflicting rules with no priority                                                                  | Explicit legal conflict, not arbitrary last-rule-wins                                                                   |
| T22 | Exception to exception under Catala-style rules                                                         | Deterministic correct outcome with complete reason DAG                                                                  |
| T23 | Amendment while a contract escrow remains active                                                        | Versioned transition, no unapproved retroactivity                                                                       |
| T24 | Subordinate amendment weakens superior immunity                                                         | Invalid or held according to priority and consent rules                                                                 |
| T25 | Lease expires at exact boundary (`t=end-1`, `t=end`, `t=end+1`)                                         | Universal half-open `[start, end)` (`now < expiry`) holds across `Eval`, `Core`, and projections                        |
| T26 | Partitioned node records a local request unseen by the coordinator                                      | Hidden local information cannot be assumed globally visible; verifier finds the resulting authorization race if present |
| T27 | New leaseholder activation races old leaseholder                                                        | Single-authority property preserved only under explicit fencing assumptions                                             |
| T28 | Unlawful event is necessary to reach a counterexample                                                   | Adversarial explorer includes it; lawful-only explorer labels omission                                                  |
| T29 | Open infinite integer action domain without menu                                                        | Bounded explorer returns incomplete coverage, not success                                                               |
| T30 | SMT backend bound smaller than exploit trace                                                            | Result marked bounded/inconclusive for larger traces                                                                    |
| T31 | Liveness without scheduler fairness                                                                     | Not claimed unconditionally; fairness assumptions named                                                                 |
| T32 | External Veil-generated artifact                                                                        | Accepted by pinned Veil parser; target trace replays in Charter                                                         |
| T33 | Solidity/EVM artifact                                                                                   | Compiles, ABI round-trips, tested against modeled EVM semantics/assumptions                                             |
| T34 | Attempt to reuse stale authorization token                                                              | Rejected; no second external action authorized                                                                          |
| T35 | Server crashes after transfer but before confirmation                                                   | `ExecutedUnknown`; no automatic duplicate payment; reconciliation path                                                  |
| T36 | Server restarts from log + snapshot                                                                     | Same legal state, evidence root and decision history                                                                    |
| T37 | Source English changes with unchanged formal rule                                                       | STALE source / review required                                                                                          |
| T38 | Formal rule changes without English change                                                              | Semantic diff and approval required                                                                                     |
| T39 | Hash collision attempt on legacy FNV approval                                                           | Modern cryptographic content digest prevents false authenticated approval                                               |
| T40 | Unified stratified-eFLINT 4.1 corpus and machine-readable tolerances                                    | Zero profile split; contextual keywords accept eFLINT atoms; `CHR020` and documented `eflint-4.1.0.1` fixes pinned      |
| T41 | Published theorem fails on mutant evaluator                                                             | Build/proof gate rejects the mutation                                                                                   |
| T42 | Actor introduces a new entity at runtime                                                                | Generic identity domain works; no hardcoded enumerated actor set                                                        |
| T43 | Insufficient confidential evidence authorization                                                        | Reason graph redacts correctly without changing the legal verdict                                                       |
| T44 | Artificially expensive proof / model checking                                                           | Caps trigger explicit incomplete/error, never green                                                                     |
| T45 | Obligation assignment followed by asset transfer through an intermediary                                | Governing assignment and liability clauses determine outcomes; no Charter-specific financial-policy patch               |
| T46 | Build Charter with no application code or repositories installed                                        | All existing compiler/checker/proof gates pass; once deployed, server gates also pass; no hidden external dependency    |
| T47 | Attempt to add product-specific predicates to core                                                      | Static boundary gate and review policy reject the change                                                                |
| T48 | Apply identical Charter rules to unrelated contract, election and licensing examples                    | Same general semantics and diagnostics, with no special-cased institution                                               |
| T49 | External client application ships its own fixtures and release cadence                                  | Charter tests remain independent; versioned API and compatibility contract suffice                                      |

Testing discipline: create one minimal repro fixture per historical failure, require a negative test that fails on the pre-fix version, and publish the version in which it was fixed. Each source rule's `From ...` span must be traceable from both the pass and the counterexample.

## 15. Competitor-gap closure and product positioning

This proposal should not be evaluated by feature count alone. Each competitor's useful strength is adopted only where Charter can retain a coherent institutional semantics and checkable assurance chain.

| Reference system | Capability to learn from                                                                            | Charter implementation commitment                                                                                            | Minimum evidence of parity                                                             |
| ---------------- | --------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| eFLINT           | Executable norms and institutional relationships                                                    | Unified strict superset of stratified eFLINT 4.1; contextual keywords; `Act` + `Power`; documented `eflint-4.1.0.1` bug fixes | 196-file corpus + machine-readable tolerances; proved `CIR` semantics for full subset  |
| Symboleo         | Contract/obligation/power lifecycle; subcontract, assignment, substitution; temporal contract tests | `lib/contract_lifecycle.charter` & `lib/agency_mandate.charter` modules with proved invariants                               | Sale-of-goods lifecycle and novation/assignment/subcontracting conformance suite       |
| InstAL           | Existential institutional histories and constraints                                                 | Native adversarial/mixed explorer + SMT in 1.0; optional ASP/`clingo` backend post-1.0                                       | Find existential prohibited history without hand-encoding exact trace                  |
| Catala           | Statutory defaults/exceptions and literate source review; high-assurance calculation                | Stratified `Default`/`Priority` calculus, decision DAG, scaled `Money` over `Int`, source-consequence diff                   | Tax/benefit exception benchmarks and explicit `Conflict` behavior                      |
| Veil             | Automated/interactive inductive safety proofs for protocols                                         | Kernel inductive proofs + validated Veil or Quint/TLA+ protocol target with trace replay in 1.0                              | Verified generic distributed lease-handover scenario with checked assumptions          |
| Quint            | Nondeterministic temporal models, TLC/Apalache integration                                          | Temporal operators, fairness, native/SMT verification, and validated protocol target export                                  | Safety and bounded-response models with appropriate proof labels                       |
| L4               | Developer-friendly legal rules, explanations, APIs, MCP, IDE                                        | Operator-blind `charter-server`, `ReasonGraph`, LSP, REST/MCP tooling, artifact build-and-deploy workflow                    | External developer can author, test, deploy, query and audit a rule service            |

### 15.1 Primary reference material (external)

These links document the feature categories the RFC seeks to bridge; they do not imply source-level equivalence or benchmarking of the present versions:

- eFLINT compatibility reference: the Charter repository's vendored `docs/reference/eflint.pdf` and tolerance corpus `test/eflint-corpus/tolerances.md`.
- Symboleo contract lifecycles: [Parvizimosaed et al., Specification and Analysis of Legal Contracts with Symboleo](https://iris.unitn.it/handle/11572/364826).
- InstAL and clingo: [InstAL project](https://instsuite.github.io/).
- Catala and source-oriented legal compilation: [Catala repository](https://github.com/CatalaLang/catala); [Catala: a programming language for the law](https://doi.org/10.1145/3473582).
- Veil transition verification: [Veil documentation](https://veil.dev/docs/), including the Veil 2.0 pre-release caveat.
- Quint model checking: [Quint model-checker documentation](https://quint.sh/docs/model-checkers).
- L4 deployment and editor tooling: [Legalese L4 documentation](https://legalese.com/l4) and [exporting rules for deployment](https://legalese.com/l4/tutorials/deploying-rules/exporting-rules-for-deployment).

### 15.2 Definition of genuine competitiveness

Charter can claim competitive readiness in a domain only when it can demonstrate:

1. Expressive equivalence for a defined representative workload, with no hidden manual shadow model.
2. Semantic clarity: a published interpretation of every construct used, including exceptions, time, unknown evidence and effects.
3. Correct implementation: reproducible tests and checkable proof/refinement evidence appropriate to the claimed guarantee.
4. Usability: a user can understand an adverse ruling, trace it to English, change the law safely and deploy the result.
5. Interoperability: external verifiers/services accept the artifact and round-trip its significant state and counterexamples.
6. Operational security: the claims survive realistic crash, retry, delay, delegation and adversarial-input tests within a declared trust boundary.

Do not market parity with Catala's legislative compilation if Charter cannot handle overlapping exceptions correctly; parity with Veil if Charter cannot establish inductive safety for a real nontrivial transition model; or parity with L4 if Charter cannot expose a robust, audited decision service.

## 16. End-to-end reference slice: delegated treasury mandate

This neutral reference workload ties together several new constructs without requiring any policy, entity type, or economic formula from an external application.

### 16.1 Authoritative natural-language requirements (example)

> A company may appoint an accountant to purchase approved bonds using a specified custody account, up to a stated mandate limit. The accountant must provide transaction confirmations within two business days and a signed monthly account inventory. Any bond purchase beyond the mandate is not authorized on the company's behalf, except where a separately defined apparent-authority rule makes it effective against an innocent counterparty. An unauthorized purchase is recorded as an external event even if it has no authorized corporate effect. A missing report creates a reporting breach and a contestable remedy; it does not automatically establish theft or deliberate concealment by the company.

### 16.2 Proposed normalized typed model (NOT CURRENT CHARTER SYNTAX)

```
Institution TreasuryMandate
  Principal company
  Delegate accountant
  Mandate m1 {
    power: purchaseBond(account="A", assetClass="approved", cap=100000 USD)
    effective: [2027-01-01, 2028-01-01)
    maySubdelegate: false
    reporting: transactionConfirmation DueWithin 2 businessDays
    reporting: monthlyInventory DueWithin 5 calendarDaysAfterMonthEnd
    revoke: noticeTo(accountant, custodian)
  }
  Duty reportTransactions Holder accountant Claimant company
    HoldsWhen mandateActive(m1)
    FulfilledBy submitConfirmation(m1, tradeId)
    DueWithin businessDays(2)
  Power recognizeBondPurchase Holder accountant
    ValidWhen mandateActive(m1)
      && accountPermitted("A")
      && newExposure <= mandateRemaining
      && assetApproved(asset)
    Creates recognizedHolding(company, asset, amount)
  Rule apparentAuthority ...  // source-defined, absent unless granted
  Evidence bankTradeConfirmation VerifiedBy approvedCustodian
  Invariant noDoubleCount ...
  Invariant mandateAuthorizationBound ...
```

Use this as a design specimen, not an attempt to force its precise spelling onto the existing parser. The language grammar review decides the final representation; the semantics and outputs below are fixed acceptance expectations.

### 16.3 Required traces

Trace A — normal performance. Principal issues mandate; accountant purchases a bond within cap; custodian supplies evidence; transaction becomes recognized; confirmation is filed on time; record and reason graph cite the mandate and trade confirmation.

Trace B — delegate exceeds scope. Accountant purchases above cap; the act physically occurs; the purported exercise of company authority is not automatically valid; the model considers the separately applicable apparent-authority clause if one exists; legal liability is adjudicated using applicable evidence.

Trace C — missing report. Trade occurs, but accountant does not report; the reporting duty breaches after its due time; the system does not conclude that the company concealed the asset or that the accountant stole it merely because the report is missing.

Trace D — conflicting evidence. Custodian reports one position and accountant reports a different one; ownership/amount is `Conflicted` until valid finding or contractual rule resolves it; the engine does not silently choose the more favorable value.

Trace E — revoked mandate. Company revokes mandate, but custodian receives notice later. An action in the gap is decided under the express notice/apparent-authority rules, not by assuming all actors shared the same immediate knowledge.

Trace F — double execution. An execution authorization is retried after a network timeout; the custody adapter uses the same intent ID and authorization nonce; it cannot cause a second transfer even though the caller repeats the API request.

### 16.4 Verification targets for this slice

- Safety: all recognized and authorized holdings arise under an effective mandate and stay within declared limits, subject to explicit third-party legal-effect exceptions.
- Accounting: the same purchase receipt and capital basis are recognized at most once.
- Liveness (conditional): if the service and clock progress and the custodian eventually supplies an admissible receipt, each reserved transaction eventually becomes settled or enters a declared dispute state.
- Attribution: physically observed accountant misconduct is not automatically imputed as an intentional principal breach.
- Evidence: no proof of global wealth visibility is claimed absent sufficient independent observations.
- Provenance: every legal consequence links to its operative source clause and applicable law version.

This one vertical slice should work end-to-end before Charter is presented as a fully deployable institutional language.

## 17. Assurance case for a specific deployed institution

For production deployments, require a structured assurance argument rather than a single green checkmark.

```
CLAIM: An external transfer cannot be lawfully authorized in violation of R.
  BASIS:
    C1. Approved document and CIR hashes pin R's meaning.
    C2. Elaboration/evaluation preserves declared CIR semantics.
    C3. R's safety property is proved or bounded-checked under stated assumptions.
    C4. Authorization adapter executes only the specific issued capability.
    C5. Reservation/replay prevents double spend of authority.
    C6. Trusted environment feeds required facts and time according to policy.
  QUALIFICATIONS:
    Q1. Unknown or forged external evidence may change what the server believes.
    Q2. Unmediated channels exist only if explicitly disclosed.
    Q3. An unauthorized external party can physically act, creating a breach.
  EVIDENCE:
    [source manifest, proof artifact, backend logs, security tests,
     audited policy, replay root, trusted-input declarations]
```

One of the strongest scientific claims Charter could eventually make is not "the law is always obeyed" but "the scope, meaning, and failure conditions of a particular institutional guarantee are mechanically inspectable and auditable." That is both rigorous and commercially useful.

## 18. Threats to correctness and design decisions requiring explicit approval

### 18.1 Semantic risks

- English/formal divergence: no algorithm can establish complete semantic faithfulness to arbitrary legal prose. Mitigation: legal review, source spans, behavior diffs, adversarial examples, formally defined version authority.
- Unforeseen rule conflict: automatic priority is dangerous. Mitigation: conflict as a typed outcome; source-defined precedence; proof of hierarchy preservation.
- Unassigned external fact halting or misclassified: raw `Open` missing-input (`CHR100`) halts rather than expressing contested status. Mitigation: 4-valued `EvidenceStatus` (`Established | Refuted | Unresolved | Conflicted`) and `Finding` acts on `Open`/`Evidenced` facts.
- Competing institutional powers: risk of ambiguous simultaneous effects. Mitigation: boolean `create beats terminate` + conflict rejection on simultaneous distinct functional/monetary updates.
- Calendar-time assumptions: risk of boundary/offline split-brain. Mitigation: universal `[start, end)` (`now < expiry`), distinct legal, observed, and monotonic time with explicit substrate assumptions.

### 18.2 Implementation risks

- Separate idealized proof model: provable but not operative. Mitigation: live-evaluator correspondence gate.
- Unverified generated syntax: renderer theorem doesn't ensure external compilation. Mitigation: target AST, parser acceptance, refinement and differential tests.
- External solver trust: model checker can be wrong or translation unsound. Mitigation: validated counterexamples, checked proof objects, explicit trust declaration.
- Unobservable physical events: system cannot veto an unobserved contractor's conduct. Mitigation: mandate, independent evidence, audit and reporting duties.
- Overly powerful server: deterministic law service can become discretionary censor if unspecified holds are allowed. Mitigation: source-grounded decisions, bounded holds, impartiality tests and appeal.
- Intractable proofs: Lean kernel cost can grow rapidly. Mitigation: performance work, incremental proof certificates, explicit inconclusive outcomes.
- Excessive feature scope: a universal language that never reaches proof closure can be less useful than a precise smaller system. Mitigation: G0–G5 gates, complete vertical slice, no unsupported public claims.

### 18.3 Maintainer rulings (ruled 2026-11-06 by Eric)

| Decision                  | Options weighed                                                                        | Ruled direction (2026-11-06)                                                                                      |
| ------------------------- | -------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| Semantic reference        | Operational evaluator alone vs. declarative `Prop` relation + single proved `Eval`     | Declarative `Prop` relation + **one** executable `Eval` proved sound & complete (`Law 9`)                         |
| eFLINT relationship       | Forked `compat`/`strict` profiles vs. unified superset of stratified eFLINT 4.1        | **One unified language**: strict superset of stratified eFLINT 4.1 (`CHR020` kept; contextual keywords; no split) |
| Core TCB vs. `lib/`       | Domain records (`Contract`, `Mandate`, `Jurisdiction`) in `Core/` vs. `lib/*.charter`  | Keep `Core/` minimal (4 primitives, kernel-reducible); ship legal ontologies in `lib/*.charter` (`D8`)            |
| Evidence uncertainty      | Closed-world everywhere vs. `Closed` ontic + 4-valued `Open`/`Evidenced` epistemic     | Keep `Closed` default (`false`) + extend `Open`/`Evidenced` with `Established/Refuted/Unresolved/Conflicted`      |
| Decision status labels    | Expand four Law-10 tags vs. retain four tags + orthogonal `scope`/`completion`         | Retain four tags (`proved`, `decided`, `checked`, `assumed`) + typed `scope` and `completion`                     |
| Norm priority & defaults  | Inflationary self-negation vs. stratified `Default`/`Priority` with typed `Conflict`   | Stratified `Default`/`Priority` DAG; unranked ties yield explicit `Conflict`                                      |
| Simultaneous effects      | List-order everywhere vs. boolean `create beats terminate` + functional conflict check | Boolean `create beats terminate`; reject conflicting simultaneous `Money`/`Param`/`Unique` writes                 |
| Amendments                | Mutable source text vs. versioned `Amend` acts producing certified `Artifact`s         | Versioned `Amend` acts with reflexive `Immunity` entrenchment & `certificate-at-office` (`D11`, §3a)              |
| External effect           | Optimistic atomic assumption vs. two-step `Reserve` + receipt + `ExecutedUnknown`      | `Reserve` + capability token + reconcile with explicit `ExecutedUnknown`                                          |
| 1.0 Backend scope         | All 7 external tools in 1.0 vs. focused 5-target 1.0 matrix                            | 1.0 ships Kernel + Native Explorer + SMT + 1 protocol target (Veil or Quint/TLA+) + Solidity/ABI                  |
| Repository independence   | Erase PSA history vs. strict technical decoupling (`G0-INDEPENDENCE` + `D10`)          | Complete `D10` technical decoupling (`Main.lean`, `battery`, `README` counts); keep honest origin history         |
| Server authority          | Source-compiling supervisor vs. operator-blind law-governed deterministic service      | Operator-blind `charter-server` over certified `Artifact`; lawful-action entitlement                              |

## 19. Recommended acceptance statement for Charter 1.0

A public release should claim no more than the following, and only after the stated conditions are met:

> Charter 1.0 is a typed institutional specification and execution language. It models facts, acts, legal duties, powers, permissions, immunities, obligations, evidence, deadlines, delegations, amendments and inter-institutional priority. It distinguishes events that occur from conduct that is lawful and from institutional acts that take legal effect. A versioned, source-linked Charter program is interpreted by a deterministic evaluator whose behavior is proved to implement the supported formal semantics. Charter provides source-level explanations, counterexample search and proof tools with explicit coverage/assumption labels, and a durable server that issues tightly scoped authorizations and records external outcomes. Generated target artifacts identify their verified fragment and require validated target behavior. Charter cannot establish the truth of unobserved external facts or the legal meaning of prose without accepted evidence and review.

This is a future release claim, not an accurate description of all current code.

## 20. Final recommendation

Do not try to win on feature breadth before closing the central proof and deployment gap. The immediate work should be: (1) make public claims exact; (2) complete a canonical typed CIR and the semantics-to-live-evaluator proof; (3) build a genuinely adversarial verifier with explicit model scope; (4) establish the server's durable, least-privilege execution boundary; and only then (5) add the substantial legal-lifecycle and developer-experience features that create parity with other tools.

The strongest long-term differentiator is not that Charter contains more syntax than eFLINT, more arithmetic than Catala, more model-checker backends than Quint, or more interfaces than L4. It is that Charter could become the credible institutional semantic core linking approved legal text, executable legal consequences, verifiable operational state, and independently checkable enforcement decisions. Such a system should serve commercial contracts, governance institutions, public programs, and future legal actors through the same application-independent semantic core.

### Appendix A — Required documentation and proof inventory

| Artifact                                | Purpose                                                 | Exit gate |
| --------------------------------------- | ------------------------------------------------------- | --------- |
| `docs/spec/001_design_goals.md`         | Single normative design scope                           | G0        |
| `docs/spec/020_grammar.md`              | Complete versioned grammar                              | G1        |
| `docs/spec/019_eflint_compatibility.md` | Full compatibility/tolerance semantics                  | G1        |
| `docs/spec/017_projections.md`          | Target semantics and verification claims                | G5        |
| `docs/trust.md`                         | Trusted computing base, environmental assumptions       | G0/G4     |
| `docs/assurance-levels.md`              | Formal meanings of checks/proofs/bounds                 | G0        |
| `docs/semantics.md`                     | Mathematical transition and derivation relations        | G1        |
| `docs/evidence.md`                      | Fact provenance, findings, legal standards, uncertainty | G3        |
| `docs/server-protocol.md`               | Auth, reserve, event, replay and failure semantics      | G4        |
| `docs/security.md`                      | Threat model, key management, sandbox coverage          | G4        |
| `docs/targets.md`                       | Supported projection fragments and certificates         | G5        |
| `docs/migrations.md`                    | Cross-profile and versioned law migrations              | G5        |
| `docs/benchmarks.md`                    | Published test and proof performance                    | G5        |
| `proofs/eval-correspondence`            | Proof of actual evaluator against independent semantics | G1        |
| `proofs/derived-fixpoint`               | Least fixed-point property and stratification           | G1        |
| `proofs/time-money-refinement`          | Quantitative and temporal correspondence                | G2/G3     |
| `proofs/amendments`                     | Versioned entrenchment preservation                     | G3        |
| `proofs/projection-*`                   | Verified target fragments with precise boundaries       | G5        |

### Appendix B — Minimum CI pipeline (proposed)

```
# Commands are design targets: several are not implemented in the current repo.
# Note: CLI flags never expose engine names (Law 11).
charter doctor --lock --verify-toolchains
charter fmt --check .
charter test test/eflint-corpus/tests test/eflint-corpus/examples --expect test/eflint-corpus/eflint-outcomes.txt --tolerate test/eflint-corpus/tolerances.md
charter check --require-provenance --deny-warnings Examples/ lib/
charter test test/spec test/lib test/semantics test/security
charter explore --mode adversarial --require-complete test/explore
charter verify --backend inductive --must-prove test/proof-contracts/
charter verify --backend finite --require-complete test/finite-models/
charter verify --backend smt --report-assumptions test/symbolic/
charter generate --target veil --verify-output test/projections/
charter generate --target solidity --verify-output test/projections/
charter build Examples/Tenancy/tenancy.charter -o out/tenancy.artifact
charter-server replay --verify-root out/tenancy.artifact test/server/log-fixtures/
charter doctor --claims docs/claims.json --fail-on-unbacked
```

Do not replace the existing battery without a migration plan. Add gates individually, then require every gate in release CI. Archive checker versions, proof outputs and artifact digests for reproducibility. The publication gate rejects stale text, unbacked proof claims, incomplete target coverage, missing negative tests, and unjustified semantic drift.

### Appendix C — Scheduled decision records (`docs/meetings/`)

- `D17`: Canonical `CIR` evolution from `Core.Spec` and declarative `Prop` transition/fixpoint correspondence.
- `D18`: Unified stratified-eFLINT 4.1 superset, contextual keywords, `Power` vs. `Act`, and opt-in static assurance gates.
- `D19`: Four-valued epistemic `EvidenceStatus` and `Finding` acts over `Open` facts.
- `D20`: Minimal `Core` TCB boundary vs. `lib/*.charter` legal ontologies (`contract_lifecycle`, `agency_mandate`, `monetary_estate`, `jurisdiction`).
- `D21`: Stratified `Default`/`Priority` calculus and typed `Conflict` outcomes.
- `D22`: Assurance certificates: four Law-10 tags (`proved`, `decided`, `checked`, `assumed`) paired with `scope` and `completion`.
- `D23`: Focused 1.0 verification/projection targets and external verifier trust boundaries.
- `D24`: Operator-blind `charter-server`, `Artifact` certificate verification (`B10`), reservations, and `ExecutedUnknown` reconciliation.
- `D25`: Rule-level `Amend` acts, `LawVersion` epochs, reflexive `Immunity` entrenchment, and multi-document SHA-256 `SourceRef`.
- `D26`: Static dimensional `Money<CUR, SCALE>` and `Quantity<UNIT>` tags over exact `Int` with explicit rounding.
- `D27`: Temporal LTL operators, fairness assumptions, and partial-observability environment transitions in `Verify/`.

All ADRs must identify the affected Charter mission law, at least one corresponding formal or executable test, and any migration effect on the public language corpus or versioned compatibility profiles. Application-specific migration belongs to the application maintainer.

