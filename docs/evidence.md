# Epistemic Evidence, Institutional Findings, and Audience-Scoped Explanations (`G3.2`, `D22`)

Charter separates **ontic institutional state** from **epistemic external-world observations** (`Mission Law 3`, `Mission Law 6`, `docs/rfc.md` §5):

1. **`Closed` `Fact` (default)**: ontic legal positions (`lease-active`, `duty-held`, `ratified`). Absent a valid creation or derivation, an instance genuinely does not hold (`False`).
2. **Plain `Open` `Fact` (eFLINT 4.1)**: external inputs whose absence aborts direct queries with `CHR100: missing input` (`spec_003_6b_open_missing_input.eflint`).
3. **`Evidenced Fact` (`003.13`, `004.11`)**: non-aborting external-world propositions evaluated over Belnap's four-valued epistemic lattice:
   - `Unresolved` — neither supporting nor contrary evidence is active, and no finding governs (`T06`);
   - `Established` — supported by active evidence (with no active rebuttal) or resolved positively by a valid `Finding`;
   - `Refuted` — rebutted by active contrary evidence (with no active support) or resolved negatively by a valid `Finding`;
   - `Conflicted` — both supporting and contrary evidence are active with no superseding `Finding` (`T07`).

---

## 1. Surface Constructs

### 1.1 `Evidenced Fact` and `Confidential` Audience Policies
```charter
Evidenced Fact beneficial-owner Identified by account * party
  Confidential To auditor, court.
```
- `Evidenced` opens the fact (`isClosed = false`) and activates 4-valued epistemic tracking.
- `Confidential` (or `Confidential To a1, a2`) marks raw evidentiary details on that fact confidential in `ReasonGraph` / `charter explain` for callers outside the named audiences, without ever altering legal verdicts (`redactForAudience_preserves_verdict`, `T43`).

### 1.2 Tendering and Retracting Evidence
- **Environment / vault phrases**:
  - `SubmitEvidence beneficial-owner(Acc1, Alice) By "custodian-bank".` (supporting)
  - `SubmitEvidence !beneficial-owner(Acc1, Alice) By "tax-filing".` (rebutting)
  - `RetractEvidence beneficial-owner(Acc1, Alice) By "tax-filing".` (retracting)
- **Act clauses**:
  - `Supports beneficial-owner(account, party)`
  - `Rebuts beneficial-owner(account, party)`
  - `Retracts beneficial-owner(account, party)`
- Targeting any non-`Evidenced` type is rejected statically with `CHR033`.

### 1.3 Institutional `Finding` Acts (`Mission Law 3`)
```charter
Finding adjudicate-owner Actor court Related to account, party
  Resolves beneficial-owner(account, party)
  Standard preponderance
  Valid when quorum(court).
```
- `Finding` is an institutional competence (`isPower = true`) requiring an explicit `Valid when` clause (`CHR032`).
- When valid, a `Finding` resolves `Unresolved` or `Conflicted` status on its target to `Established` (or `Refuted` for `Resolves !e`) under the named `Standard` (`preponderance`, `clearAndConvincing`, etc.).
- When void (`!valid`), the `Finding` event occurs in the trace (`occurred = yes, valid = no`) and leaves the contested proposition unchanged (`T02`, `T07`).

### 1.4 Epistemic Predicates and Strong Kleene 3-Valued Guards
- Explicit epistemic predicates: `Established(e)`, `Refuted(e)`, `Unresolved(e)`, `Conflicted(e)` always evaluate to definite `Bool` (`True`/`False`), allowing explicit statutory presumptions (`When Unresolved(...)`, `T06`) or escalation rules (`When Conflicted(...)`, `T07`).
- Bare `Evidenced` references inside `Holds when` / `Valid when` propagate strong Kleene 3-valued `TriBool` (`yes | no | undetermined` + `unmetEvidence`):
  - `no && undetermined = no` and `yes || undetermined = yes` (`triBool_classical_conservative`, `triBool_deMorgan_and`);
  - an `undetermined` `Valid when` guard never authorizes institutional effects (`valid = false`, `validTri = undetermined`), and `?undetermined act(args)` / `?!undetermined act(args)` test epistemic indeterminacy directly in scenarios.

---

## 2. `ReasonGraph`, `charter explain`, and Metamorphic Impartiality

- **`charter explain <expr> <file.charter> [--scenario <name>] [--audience <role>] [--out json]`**:
  Evaluates `<expr>` at the end state of `<file.charter>` (or `<scenario>`), returning a `ReasonGraph` DAG citing rule IDs, `From` verbatim English spans, premise statuses, tendered evidence / `Finding` standards, defeated `Immunity`/`Except under` edges, and single-condition counterfactuals, filtered through `redactForAudience` (`T43`).
- **`charter test --metamorphic` (`//! metamorphic`)**:
  Re-executes the program and scenarios after (1) stripping non-operative advisory metadata (`Note "..."`, `Clause`, `Document`, `From`, `T04`) and (2) permuting interchangeable actor atoms not referenced as constants in rules (`T05`), failing if any legal judgment changes.
