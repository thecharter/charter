# D30–D33 — End-state invariant checks, status-explicit `Evidenced` derivations, missing-input `Var`/`Function` effects, and source-keyed evidence

**Laws:** 2, 3, 4, 6, 9, 12, 13 (`docs/mission.md`). Briefs: `B13`–`B16` in `2026-11-07-briefs-for-ruling.md`.
**Date:** 2026-11-07
**Status:** ruled (Eric, 2026-11-07)

## D30 (`B13`, #6) — `charter test` always checks end states of the program and of each scenario

- **Ruling (`B`):** `charter test` requires every declared `Invariant` to hold at the end state of the program and at the end state of each `Scenario` (with or without `//! explore`), unless the breach is explicitly claimed there (`?!inv().`). Mid-run invariant violations during genesis setup or transition sequences stay reports (`013.1`).
- **Laws:** `Law 9` (aligns `test` with `explore` and `prove`, which already check those same end states) and `Law 2` (rejects `C`'s hidden mode switch on file contents).
- **Measured & verified:** All 6 of the 12 `test/lib/*_test.eflint` files that emit mid-run violations were inspected individually; all 6 violate invariants only during partial genesis setup before their `Var`s are assigned, and all 12 pass at end state.
- **Cost accepted:** 7 upstream eFLINT corpus files that end with a violated invariant become documented tolerances in `test/eflint-corpus/tolerances.json` / `tolerances.md` ("Charter asks an end-state question eFLINT does not", bringing total tolerances to 39).
- **Fixture:** `test/spec/spec_011_10b_end_states_satisfy_invariants.charter`.
- **Reopens if:** a new construct gives modules atomic genesis blocks (#42) so mid-genesis violations disappear as well.

## D31 (`B14`, #9) — Bare reads of `Evidenced` facts in two-valued derivation rules are permanently refused (`CHR038`)

- **Ruling (`A`, permanent):** Only an act's `Holds when` and `Valid when` guards are three-valued and may read an `Evidenced` fact bare. Every two-valued rule (deriving a `Fact`/`Bool`/`Var`/`Function`, a duty's `Violated when`, an immunity's `Holds when` / `Unless`, or `Conditioned by`) must state which epistemic status it means (`Established`, `Refuted`, `Unresolved`, `Conflicted`); a bare read is rejected statically with `CHR038`.
- **Laws:** `Law 6` (never invent truth from `Unresolved` under `Not`) and `Law 13` (in a two-valued rule, bare has no meaning distinct from `Established(e)`).
- **Separate defect filed:** `004.12` normative conflict leakage through intermediate derived facts (`T21` narrower than `004.12`) filed separately as [#80](https://github.com/thecharter/charter/issues/80) with the bounded taint-overlay route.
- **Examples updated under ruling:** `Examples/RentersInsurance/policy.charter`, `Examples/BillOfSale/bill-of-sale.charter`, and `psa.charter` (`amendment-consent-complete`).
- **Fixtures:** `test/spec/spec_004_11b_bare_evidenced_read_refused.charter`, `spec_004_11c_status_read_in_derivation.charter`.
- **Reopens if:** a source clause's English explicitly declares a *fact* (not an act's lawfulness or validity) to be three-valued `undetermined`.

## D32 (`B15`, #11; plus warnings #3, #8) — Effects reading an unset `Var` or an unassigned `Function` argument halt with missing input (`CHR100`)

- **Ruling (`A`, scoped to `Var` and `Function` as `CHR100`):**
  1. Ordinary `Fact` binders over zero holding instances in effects remain set operations that produce nothing (`005.4`).
  2. Reading a `Var` with no holding instance in an effect (other than a bare `Terminates v` / `Obfuscates v` clearing `v` itself), or reading an implicitly bound `Function` at an unassigned key argument, halts with `CHR100` (`MissingInput.unassignedVar` / `MissingInput.unassignedFunction`), routing through the same missing-input channel as `Open` facts (`Law 13`).
  3. Companion static warnings (`#3`, `#8`): `CHR039` warns on unfiltered `Count(Foreach x: f(x))` over an enumerable binder (`010.7`), and `CHR040` warns on binders over unrestricted, non-derived, closed `Money`, `Quantity`, `Duration`, or built-in `int`/`string` carrier types (`004.7`). `CHR040` immediately surfaced and fixed vacuous binders in `Examples/Deed`, `Examples/TreasuryMandate`, `lib/monetary_estate.charter`, and `lib/agency_mandate.charter`.
- **Corpus impact:** 0 divergences across all 196 upstream eFLINT files.
- **Fixtures:** `test/spec/spec_005_4b_unset_var_in_effect.charter`, `spec_005_4c_unassigned_function_in_effect.charter`, `spec_010_7b_count_of_constructor_warns.charter`, `spec_004_7c_carrier_binder_warns.charter`.
- **Reopens if:** declaration-site initial values on `Var` (#42) make unset `Var` states unreachable by construction.

## D33 (`B16`, #12) — Evidence is identified by `(fact, polarity, source)` defaulting to the actor, with `By s`, `Retracts !e`, and `CHR109`

- **Ruling (`A` + `By`):** A piece of evidence is keyed by `(fact, polarity, source)`. On act-level `Supports e [By s]`, `Rebuts e [By s]`, and `Retracts [!]e [By s]`, `source` defaults to the performing actor (so two physicians performing `determine` record two distinct tenders, and one physician withdrawing via another act withdraws their own tender while leaving the other's standing), and `By s` names another component of the act or a string/atom source (e.g. a clerk filing a physician's report). `Retracts !e` withdraws contrary evidence (mirroring `SubmitEvidence !e`), and any retraction that finds no active matching evidence emits warning `CHR109` rather than silently succeeding. Authority to retract another's evidence remains governed separately by the act's `Valid when` (`Law 4`).
- **Fixtures:** `test/spec/spec_005_11b_evidence_belongs_to_its_source.charter`, `spec_005_11c_retract_of_nothing_is_reported.charter`.
- **Reopens if:** an institution requires multiple distinct concurrent tenders from the *same* actor on the *same* fact and polarity (a docket/exhibit ID component on the `Evidenced` fact already handles this without changing evidence identity).
