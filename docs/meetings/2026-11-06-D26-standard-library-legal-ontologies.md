# D26 — Verified standard-library legal ontologies (`contract_lifecycle`, `agency_mandate`, `monetary_estate`, `jurisdiction`) outside `Core` TCB (`D8`, `T09`, `T12`–`T20`, `T24`, `T45`)

**Laws:** 1, 2, 3, 5, 6, 9, 10, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `D8`, `docs/rfc.md` §3.2, §4.2, §4.3, §4.6, §6.3–§6.4, §18.3)

## Ruling
1. Rather than bloating `src/Charter/Core/` with hardcoded contract-law, common-law agency, accounting, or conflict-of-laws AST nodes, Charter ships four domain-neutral standard-library modules in `lib/*.charter` (`Module`/`Use`), each with checked and explored `Invariant`s (`test/lib/`) and kernel-checked backing theorems (`src/Charter/Modules/LegalOntologies.lean`, `D8`):
   - `lib/contract_lifecycle.charter`: configurable contract status transitions (`Draft -> Offered -> Accepted -> InForce -> {Completed, Expired, Rescinded, Terminated, Frustrated, Void}` + `Disputed` overlay), partial performance (`T19`), survival of remedies after breach/termination (`T20`), and distinct subcontracting vs. claim assignment vs. novation consequences (`T18`, `T45`).
   - `lib/agency_mandate.charter`: express mandate caps, physical occurrence vs. void principal-binding recognition (`T15`), optional apparent-authority protection prior to counterparty revocation notice (`T17`), reporting-duty deadlines without invented concealment/theft findings (`T16`), and non-imputation vs. anti-circumvention attribution.
   - `lib/monetary_estate.charter`: reservation locks preventing concurrent over-draws (`T09`), two-tier capped-allowance fee charging (`T10`, `T11`), `no-double-recognition` (`T12`), `no-double-pledge` (`T13`), and `consolidated-no-double-count` eliminating intercompany equity (`T14`).
   - `lib/jurisdiction.charter`: superior/subordinate polity rank, explicit `nexus` requirement, reserved subjects, protection of superior entrenched rights (`T24`), and explicit `contested-jurisdiction` detection.

## Context
Symboleo (contract/obligation lifecycles), InstAL (delegation/multi-institution rules), and Catala (financial/statutory rules) demonstrate expressive legal patterns that institutions need, while `charter prove` requires `Core.Spec` and `Core.State` to stay minimal and kernel-reducible.

## Mission fit
`Law 1` & `Law 2` (unauthorized delegations and breaches occur physically while principal-binding effects depend on `Power` validity), `Law 9` & `Law 10` (minimal `Core` TCB; invariants explored and proved), `Law 13` (zero domain-specific keywords in `Core`).

## Cost accepted
Programs instantiate legal patterns explicitly via `#require` + `Use <module>(...) As <prefix>`.

## Reopens if
Any recurring legal ontology pattern proves unexpressible without a new irreducible `Core` primitive.
