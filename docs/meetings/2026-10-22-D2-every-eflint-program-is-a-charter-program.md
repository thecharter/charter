# D2 — Every eFLINT program is a Charter program: eFLINT's constructs, phrases, and semantics are Charter's core, extended and never revised

**Laws:** 12, 13 (docs/mission.md).
**Date:** 2026-10-22
**Status:** ruled (Eric)

## Ruling
Charter adopts eFLINT's constructs, keywords, phrase language, and semantics unchanged in spelling and meaning (`.reference/eflint`, v4.1). Charter extends with new constructs; it does not alter an eFLINT meaning. The eFLINT test suite and examples corpus are vendored under `test/eflint-corpus/` and run as Charter regression tests. Where eFLINT has a documented defect, Charter fixes it under a decision naming the defect and the tolerance (D6 is the first).

## Context
eFLINT is the one existing language on Charter's square (Hohfeldian facts, acts, duties; individuals; Int facts; in-file scenarios), with five years of applied use. The alternative was a fresh syntax inspired by it with no import path.

## What the references do
Catala, Quint, Symboleo are each incompatible with their predecessors (TLA+ for Quint is a target, not a subset). None vendors a predecessor's corpus.

## Mission fit
Law 12 is this decision. Law 13 is kept because eFLINT's spelling becomes the only spelling (keyword casing is therefore eFLINT's; see the briefs file, B-casing, no separate ruling).

## Cost accepted
Charter inherits eFLINT's `.` phrase terminator, capitalised keywords, and the "disabled act still has effects" default (D5).

## Reopens if
The corpus cannot be made to pass without reproducing a defect the mission forbids.
