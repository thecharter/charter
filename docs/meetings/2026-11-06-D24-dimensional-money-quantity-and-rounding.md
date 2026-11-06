# D24 — Static dimensional `Money(CUR, SCALE)` and `Quantity(UNIT)` over exact `Int` with `MulDivRound` (`T10`, `T11`)

**Laws:** 5, 6, 9, 10, 12, 13 (`docs/mission.md`).
**Date:** 2026-11-06
**Status:** ruled (Eric, `docs/rfc.md` §6.3, §18.3)

## Ruling
1. **Zero-overhead dimensional domains (`003.2`, `003.14`)**:
   - `Money(CUR, SCALE)` (`Domain.money cur scale`, `Ty.money cur scale`) represents exact `Int` minor units (`10^SCALE` minor units per major unit of currency `CUR`, e.g. `Money(USD, 2)` in cents).
   - `Quantity(UNIT)` (`Domain.quantity unit`, `Ty.quantity unit`) represents exact `Int` units of `UNIT`.
   - At run time (`Core.State` and `Charter.Eval`), values remain bare `Elem.int` values (just like `Time` and `Duration`, `D7`), avoiding floating-point drift and unreduced rational heap objects inside `charter prove`.
2. **Dimensional typing (`010.2`, `010.12`, `CHR012`)**:
   - `+`, `-`, `<`, `<=`, `>`, `>=`, `==`, `!=` require matching `(CUR, SCALE)` or `UNIT` (with integer-literal coercion by demand); cross-currency, cross-scale, and cross-unit mixes fail statically with `CHR012`.
   - `Money(c, s)` and `Quantity(u)` may be scaled by `Int` (`*`, `/`) and summed/bounded via `Sum`, `Max`, `Min` while preserving their dimensional type; multiplying two `Money` or two `Quantity` values is rejected (`CHR012`).
3. **Explicit scaled rounding (`MulDivRound(x, num, den, mode)`, `CHR108`, `T10`, `T11`)**:
   - `MulDivRound(x, num, den, Floor | Ceil | NearestEven | ExactOrReject)` computes `(x * num) / den` in exact arbitrary-precision integer arithmetic and rounds according to `mode`, preserving `x`'s dimensional type (`Money`, `Quantity`, `Duration`, or `Int`).
   - Division by zero or a non-zero remainder under `ExactOrReject` fails loudly at evaluation with `CHR108` (`RuntimeError.arithmeticError`).

## Context
Financial contracts and tiered fee schedules (`T10`, `T11`) require exact minor-unit representation, currency/scale isolation, and explicit rounding without binary floating point or kernel-bloating rational heap wrappers.

## Mission fit
`Law 5` (scales and rounding modes are explicit AST data), `Law 9` & `Law 10` (exact `Int` reduction in the proof kernel; `mulDivRound_t10_tiered_allowance` and `mulDivRound_nearestEven_ties_even` proved), `Law 12` (contextual `Money(...)`, `Quantity(...)`, `MulDivRound(...)` preserve 196/196 eFLINT compatibility).

## Cost accepted
Explicit cross-scale or FX conversions must be written in source rules (`MulDivRound` or `lib/monetary_estate.charter`), never inserted implicitly.

## Reopens if
Arbitrary symbolic rational denominators are ever required across multi-step state variables without intermediate minor-unit settlement.
