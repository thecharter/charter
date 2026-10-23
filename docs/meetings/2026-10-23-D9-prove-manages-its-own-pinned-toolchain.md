# D9 — `charter prove` downloads and manages its own pinned toolchain into `~/.charter/toolchains/<digest>/`; it never asks the author to install Lean

**Laws:** 11, goal 2 (docs/mission.md). Brief: B6.
**Date:** 2026-10-23
**Status:** ruled (Eric), as predicted

## Ruling
First use of `prove` fetches the toolchain pinned by digest in `tools/pins.lock`, verifies it, and caches it. `--offline` refuses rather than searching PATH. No help text, path, or message names Lean. This is With's Law 8 ("the toolchain absorbs the environment, within a boundary") applied to Charter.

## Reopens if
Download size or first-use latency makes `prove` unusable in authors' CI; then `--toolchain <dir>`, still Lean-free in its wording.
