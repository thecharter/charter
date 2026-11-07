# Charter 1.0 Competitive Benchmark Suite & Measured Performance (`G5.5`)

Implements all 9 domain-neutral benchmark institutions specified in `docs/rfc.md` §7.8, gated continuously by `tools/g5-check` in `tools/battery`.

---

## 1. Benchmark Matrix & Measured Wall-Clock Latency

Measured on Darwin arm64 (`Lean v4.24.0`, compiled native binary `.lake/build/bin/charter`, including parse, static resolution, stratification, scenario execution, and `--explore` invariant search):

| # | Benchmark File | Reference Domain | Key Constructs Exercised | `charter test` Latency |
|---|---|---|---|---:|
| 1 | `benchmarks/01_symboleo_sale_of_goods.charter` | Symboleo contract lifecycle | `lib/contract_lifecycle`, subcontracting, partial delivery (`T19`), novation (`T18`) | 86.0 ms |
| 2 | `benchmarks/02_catala_benefit_exceptions.charter` | Catala statutory defaults | 3-tier `Default` / `Exception` / exception-to-exception `Function` DAG (`T22`) | 29.3 ms |
| 3 | `benchmarks/03_instal_delegated_access.charter` | InstAL institutional delegation | `lib/agency_mandate`, `Physical` occurrence vs. `Power` principal recognition (`T15`) | 45.2 ms |
| 4 | `benchmarks/04_veil_quint_lease_handover.charter` | Veil / Quint protocol safety | Fenced single-authority lease handover, `Invariant`, `WeakUntil` `Property` (`T26`, `T27`) | 34.0 ms |
| 5 | `benchmarks/05_tiered_loan_consolidation.charter` | Exact financial accounting | `MulDivRound` (`T10`), collateral pledge cap (`T13`), intercompany elimination (`T14`) | 75.1 ms |
| 6 | `benchmarks/06_three_answers_immunity_triad.charter` | Hohfeldian legal triad | Unlawful-valid act, lawful-void power, `Immunity ... Against ... Unless` (`T01`–`T03`) | 55.6 ms |
| 7 | `benchmarks/07_amend_reflexive_ratchet.charter` | Constitutional self-amendment | `Amend ... Repeals`, `Entrenched Invariant`, reflexive `Immunity ... Against Amend` (`T24`) | 39.1 ms |
| 8 | `benchmarks/08_evidenced_beneficial_owner.charter` | Epistemic adjudication | 4-valued `Evidenced` fact, `Conflicted` filings, `Finding` under named `Standard` (`T06`, `T07`) | 39.1 ms |
| 9 | `benchmarks/09_contested_jurisdiction.charter` | Conflict of laws | `lib/jurisdiction`, `nexus`, superior entrenched right, `contested-jurisdiction` (`T24`) | 61.4 ms |

---

## 2. Reproducing the Suite

```sh
# Execute all 9 benchmark institutions (scenarios + bounded invariant exploration)
.lake/build/bin/charter test benchmarks

# Compile any benchmark to a signed operator-blind artifact and verify it in charter-server
.lake/build/bin/charter build benchmarks/08_evidenced_beneficial_owner.charter -o out/bench08.artifact
.lake/build/bin/charter-server verify out/bench08.artifact
```
