# D34–D38 — Language Ergonomics (`#35`–`#61`) and Standard-Library Provenance (`#62`)

**Laws:** 1, 2, 4, 6, 7, 8, 9, 10, 12, 13 (`docs/mission.md`). Briefs `B17`–`B26`.
**Date:** 2026-11-07
**Status:** ruled as predicted (Eric, 2026-11-07)

## Rulings Implemented

### D34 (`B17`, `B18`, `B26`, `#62`, `#35`, `#36`, `#59`, `#23`, `#30`, `#32`; partial `#31`) — Heading-resolved `Clause` citations, rule-aware `charter.lock` approvals, full span targets, template blanks, and `Use ... From`
- `Clause <ID> [Register] [=> targets]` extracts paragraphs and `/k` sentences directly from `Document` without retyping prose (`#35`).
- `charter approve [--lock] [--restamp]` writes both `textSha256` and `rulesSha256` into `charter.lock` (`#23`, `#32`).
- Spans may cite any declared `Fact`, `Param`, `Event`, or `Default`/`Exception` rule ID, and assert ground initial facts (`=> named(House, Anna)`, `#36`).
- `{param}` / `{role}` blanks in template `Document`s substitute declared `Param`s and singleton `Fact`s (`#59`).
- `Use m(...) As pfx From <CLAUSE>` grounds standard-library instantiations under `--require-provenance`, accompanied by `lib/{debt,ballot,succession}.charter` (`#62`).

### D35 (`B19`, `B24`, `#37`, `#38`, `#51`–`#55`, `#57`, `#60`, `#13`, `#15`, `#18`/`#26`) — Single-condition `Power`s, `Prohibited`, `Protection`, `Presumed` & `Decides`, `Amend Procedure`, `Input Fact`, Duty `Overrides`/`Excused when`, and `Qualifies as`
- `Power`, `Finding`, and `Amend` default `Holds when` to `Valid when` when `Holds when` is omitted (`#37`); `,` inside `Valid when` is rejected (`CHR003`, `#38`); `Finding` requires `Resolves` or `Decides` (`CHR032`, `#18`/`#26`).
- Added `Prohibited`, `Forbidden when`, `Void when` (`#51`); `Protection ... For ...` dual of `Immunity` (`#52`); `Evidenced ... Presumed True|False` & `Finding ... Decides` (`#53`); `Amend Procedure` & `Protects Clause` (`#54`); `Input Fact` (`#55`); `Duty ... Overrides` with swapped-role mapping & `Excused when` (`#57`); `Qualifies as` (`#60`); and `CHR041`/`CHR042` (`#13`, `#15`).

### D36 (`B20`, `B22`, `#39`–`#41`, `#46`, `#50`, `#61`, `#14`) — `Role`s, status actors, `First of` succession, `f(k)` application, `Count(pred)`, `Amount`, `Decided by`, bare `Bool`, and `Scenario` ergonomics
- Added `Role ... Is ...`, `Role ... Where ...`, `Role ... First of ... Unless ...`, status-fact actors, `(Forall|Exists) v Except e:`, fixed duty claimants, single-party duties, and `Duration %` (`#39`, `#40`, `#61`).
- Fixed `Var` binding over enumerated domains across derivations and queries (`#14`).
- Added 1-argument `Function` lookup `f(k)`, `Count(pred)`, `Amount name Is expr`, `Decided by ... At least n/d In vote-fact`, bare 0-arity `Bool`, multi-name powers, and `Scenario ... After ...` / `Let` / singleton `Role` elision (`#41`, `#46`, `#50`, `#61`).

### D37 (`B21`, `#42`, `#45`, `#56`, `#58`, `#17`, `#22`) — Money literals, currency shorthands, `Var` starting values, `Rate`s, `Share`/`ProRata`, `Debt`, and `Applies ... To`
- Added `$10,000.00` money literals, `: USD`/`EUR`/`GBP`/`Rate` shorthands, `Var v : USD = init` (`#42`), `6%` & `bps` `Rate` type with 3-arg `MulDivRound(amt, rate, mode)` (`#58`), and same-unit `MulDivRound` dimensional ratios (`#22`).
- Added `If(c, t, e)`, 2-arg `Min`/`Max`, `Share` & `ProRata` with mandatory `Remainder To` (`#56`), `Debt` with independent per-raising IDs/deadlines (`#45`, `#17`), and `Applies amt To v1, v2, ...` waterfalls.

### D38 (`B23`, `B25`, `#43`, `#44`, `#47`–`#49`, `#16`) — `Done`/`?occurred`, moment relations (`Before`, `Within ... Of`, `At`, `Age`, `Overdue`), `Grace`/`?late`, exact clock stamps, `Every` duties, and Civil Calendar
- Added `$occ` transition stamping (gated by `Spec.tracksHistory`), `Done(e)`, `?occurred`, `Since(e)`, `Age(e)`, `Overdue(d)`, `a Before b`, `a Within d Of b`, and resolver-synthesized `cond At ev` snapshot latches (`#43`, `#49`).
- Added `Due within d Grace g` (`?late` vs `?violated`), `Due within d After ev` (`#44`), exact clock-threshold stamps (`#16`), clock-derived `Every <period>` recurring duties & `On breach Creates` (`#47`), and ISO `YYYY-MM-DD` civil dates + `days`/`weeks` + `Year`/`Month`/`Day`/`Weekday`/`AddMonths`/`AddYears` (`#48`).
