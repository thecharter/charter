# D6 — Derivation is a stratified fixpoint; unstratifiable negation is rejected with a diagnostic (first eFLINT tolerance)

**Laws:** 6, 9, 10, 12 (docs/mission.md). Brief: B3.
**Date:** 2026-10-23
**Status:** ruled (Eric), as predicted

## Ruling
eFLINT's `Saturation.hs` is an inflationary fixpoint evaluating negation against intermediate states, so results can depend on type order. Charter stratifies; a program whose negation cannot be stratified is rejected with a `CHR` diagnostic naming the cycle. This is the first entry in the eFLINT tolerance file (D2). A stratified fixpoint has one structural-recursion definition (Law 9), gives every derived fact one origin (Law 6), and keeps scenarios kernel-decidable (Law 10).

## Alternatives weighed
Stable-model semantics with multiple models (eFLINT's GPCE'25 direction; rejected for v1: Law 6 cannot answer "where did this fact come from" with one chain).

## Reopens if
A PSA clause needs non-stratified negation, or more than a handful of corpus programs stop passing.
