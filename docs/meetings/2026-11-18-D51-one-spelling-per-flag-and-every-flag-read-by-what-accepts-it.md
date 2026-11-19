# D51 — One spelling per flag, and a flag is read by everything that accepts it

**Laws:** 10, 13 (`docs/mission.md`); `AGENTS.md` "No silent fallbacks". Brief `B39` (`2026-11-18-briefs-for-ruling.md`). Follows `D50`.
**Date:** 2026-11-18
**Status:** ruled as predicted (Eric, 2026-11-18: "approved", option A). The same word approved the agent's wordings listed in `D50` (the two pointer rewordings, the "Flags by command" list in `018`) and the deletion of `explore --require-complete`.

## Context

Listing every parsed flag in `018` for the `D50` gate showed four that were a second spelling, or were accepted by a command and read by only part of it. The gate checks that a flag is named, not that it does anything, so it could not have found them.

## Ruling

1. `charter approve --reviewed` is deleted; `--restamp` is the one spelling.
2. `charter explore --minimize` is deleted; minimizing is the default and `--no-minimize` turns it off.
3. `charter verify --invariant <name>` restricts **every** backend to the named invariants. Before, only `inductive` read it, and `finite` reported "N invariant(s) verified" over all of them whatever was named. The other invariants stay in the program as the derived facts they are and are not checked. An unknown name is `CHR003` under every backend. With `--replay` it is a usage error: the replay compares verdicts over every invariant of the model.
4. `charter verify --time <S>` caps the inductive backend's kernel run. Under `finite`, `thresholds`, or `--replay`, where nothing is timed, passing it is a usage error (exit 2).
5. `charter test` rejects an argument beginning `--` that it does not know (exit 2). Before, it was taken as a path.

## Evidence

`tools/verify-check`, 40 passed. `test/verify/d51_two_invariants.charter` (new) has one invariant violated in one step and one that holds: `finite` and `thresholds` report the violation when asked about both or about the violated one, and `ok … 1 invariant(s) verified` when asked about the other. `--time` under `finite`, `approve --reviewed`, `explore --minimize`, and `test --no-such-flag` each exit 2.

## Cost accepted

A script that passed `--time` to a non-inductive `verify`, or `--reviewed`, or `--minimize`, now gets exit 2 and the flag's name. Nothing in `tools/`, `test/`, `sdk/`, or CI did.

## Reopens if

A backend other than `inductive` gains a clock (then `--time` applies to it), or temporal `Property` checks should also be selectable by name (`--invariant` does not restrict them).
