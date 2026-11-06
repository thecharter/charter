# D19 — Structured assurance certificates (`scope` + `completion`) and monotonic symbol interning

**Laws:** 9, 10, 11 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §7.1, §7.3, §18.3)

## Ruling
1. Charter retains the exact four `Law 10` assurance tags (`proved`, `decided`, `checked`, `assumed`) and never introduces a fifth tag. Every structured claim certificate (`Charter.Artifact.Cert`) pairs its `AssuranceTag` with two orthogonal typed fields:
   - `scope`: `live-evaluator | idealized-core-model | concrete-trace | bounded-exhaustive(depth)`;
   - `completion`: `complete | inconclusive | timeout | oom`.
2. In `charter prove`, hitting a wall-clock (`--time`) or resident-memory (`--memory`) cap never reports a legal assertion as false or green: the obligation carries `verdict = null`, `completion = timeout | oom`, and `charter prove` exits with status `3` (distinct from `0` = all decided, `1` = falsified claim, `2` = usage error; `T44`).
3. `Charter.Core.Intern` provides a monotonic, append-only `SymbolTable` (`String ↔ Nat`) with kernel-proved `intern_resolve_self` and `intern_preserves_resolved`, supporting unbounded runtime actor/entity creation (`T42`) without fixed finite enumerations.

## Context
Bounded model checking (`--explore`) and resource-capped kernel runs (`charter prove`) need machine-readable scope and truncation semantics without violating `Law 10`'s four-tag discipline.

## Alternatives weighed
Adding `bounded` and `inconclusive` as top-level claim tags: rejected — violates `Law 10` ("every claim carries one of four tags and never a fifth") and conflates *who checked the claim* (`checked` vs. `decided` vs. `proved`) with *what domain was covered* (`scope`) and *whether checking finished* (`completion`).

## Mission fit
`Law 10` (four tags preserved; resource exhaustion never silent), `Law 11` (all status codes and JSON fields use Charter vocabulary).

## Cost accepted
JSON claim records carry `assurance`, `scope`, and `completion` alongside legacy `tag`/`result` fields for backward compatibility.

## Reopens if
Distributed multi-signer quorum attestations (`G4`) require nested cosigner arrays on `ClaimCertificate`.
