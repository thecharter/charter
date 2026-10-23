# D8 — A standard-library module's properties are declared as `Invariant`s in its `.charter` file and proved in `lib/lean/` by name, reported as *proved*

**Laws:** 5, 9, 10, 11 (docs/mission.md). Brief: B5.
**Date:** 2026-10-23
**Status:** ruled (Eric), as predicted

## Ruling
Each of the eight modules under `lib/` is a `.charter` module. Every property is an `Invariant` in that file (visible, data, citable). Its proof lives in `lib/lean/Modules/` attached by the invariant's name, and `charter prove` on a program that `Use`s the module cites the theorem rather than re-proving it, tagged *proved*. Properties `prove` can discharge alone need no Lean file. Module authors are Charter maintainers, so Lean in `lib/lean/` does not violate Law 11.

## Reopens if
Name binding proves fragile under module parameterization.
