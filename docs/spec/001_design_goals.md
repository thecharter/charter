# 001 — Design goals and institutional invariants

**Status:** approved (Eric, 2026-11-06; Charter 1.0.0). Grounded in `docs/mission.md` and `docs/rfc.md` (§0.2, §18.3). Every design decision in `docs/meetings/` instances one or more of the laws below.

**1.1 Purpose.** An institution is three independent answers about any event: *did it occur*, *was it lawful*, and *did it take institutional effect* (Laws 1–2). A Charter program binds formal institutional rules directly to the authoritative natural-language text from which those answers come, evaluates events deterministically, checks or proves invariants under explicit assumptions, and projects inspectable records without exposing proof-engine internals to authors.

**1.2 Domain neutrality (`Law 13`, `G0-INDEPENDENCE`).** Charter is a standalone, general-purpose institutional language. Facts, acts, duties, immunities, time, parameters, modules, and provenance are domain-neutral constructs; nothing in `src/Charter/`, `lib/`, `docs/spec/`, or `tools/battery` names a specific external constitution or product (`test/gates/law13-leak-grep.sh`, `test/gates/g0-independence.sh`).

**1.3 Unified superset of stratified eFLINT 4.1 (`Law 12`, `Law 13`, `D2`, `D17`).** Charter maintains one unified lexer, parser, and operational/declarative semantics — never diverging `compat` and `strict` semantic profiles. Every well-stratified eFLINT 4.1 program is a valid Charter program with identical meaning. Cyclic self-negation in `Holds when` / `Derived from` is rejected (`CHR020`, `D6`) so derived facts have a unique Tarski least fixpoint and truthful explanations; documented upstream `eflint-4.1.0.1` interpreter defects fixed by Charter are tracked in `test/eflint-corpus/tolerances.md` and `tolerances.json`.

**1.4 Occurrence, compliance, and validity (`Laws 1–4`, `D5`).**
- Any event can physically occur; forbidden conduct is never made syntactically unreachable (`Law 1`).
- Lawfulness (`Holds when`), institutional validity (`Valid when` and `Immunity`), and occurrence are reported independently (`Law 2`).
- Duty breaches are facts; findings that trigger remedies are institutional acts (`Law 3`).
- Scope filters (`Where`/`Conditioned by`), authority exceptions (`Except under`), duty priority (`Overridden by`), and protections (`Immunity ... Against ... Unless`) have distinct representations (`Law 4`).

**1.5 Data, world inputs, and stateful time (`Laws 5–7`, `D7`, `D16`).**
- Rules, clauses, and spans are inspectable data records, never opaque host closures (`Law 5`).
- Closed types default to false (ontic institutional state); `Open` types represent external world inputs and raise missing-input (`CHR100`) when unassigned rather than silently collapsing unknown to false; every held instance records its `Origin` (`?why`, `Law 6`).
- `Time` and `Duration` are distinct dimensional types over `Int`; assignments carry establishment timestamps (`since`) and optional half-open `[start, end)` expiries (`now < expiry`), with deadlines (`Due within`, `Held ... For`) evaluated over clock state rather than synthetic lapse events (`Law 7`).

**1.6 Provenance, single evaluator, and kernel assurance (`Laws 8–11`, `Law 14`).**
- Normative rules link verbatim to their authoritative `Document` via `Clause ... Approved` and `From` spans (`Law 8`).
- One executable evaluator (`Charter.Eval`) implements the language semantics, proved against declarative relations in Lean (`Law 9`).
- The Lean kernel is the sole trusted proof checker (`zero sorry`, `zero native_decide`, `zero extra axioms`), and every claim carries one of four assurance tags (`proved`, `decided`, `checked`, `assumed`) paired with explicit scope and completion metadata (`Law 10`, `docs/assurance-levels.md`).
- User-facing CLI flags, help text, and diagnostics never expose Lean or engine internals (`Law 11`, `test/gates/law11-no-engine-in-output.sh`).
- Every mission law and public assurance claim is backed by an automated gate (`Law 14`, `docs/claims.json`, `test/gates/`).
