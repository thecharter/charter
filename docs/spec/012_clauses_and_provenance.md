# 012 — Clauses and provenance

**Status:** draft (2026-10-23). Meaning fixed by D4 and Law 8; the spellings are the plan's (§2.2.5) and await Eric's wording. Implementation: compliant (Phase 2's third slice, landed the same day); every statement has a passing conformance test. The literate `.charter.md` container of D4 is Phase 5.

Every norm carries its English, and the English leads (Law 8). A program names its authoritative document, quotes that document clause by clause, classifies every span of a clause into a register, and says which rule each normative span means. The checks below are run by `charter check` and at the end of `charter test`; each is a *claim* tagged *checked*, about *provenance*, and a failed one fails the file.

**12.1 Document.** `Document "path"` names the authoritative English, relative to the program's file. `test/spec/spec_012_1_clauses_resolve.eflint`

**12.2 Clauses.** `Clause ID [Approved HASH]` declares a clause; `ID` is atoms and identifiers joined by dots (`DEF.01`, `T.2`). Its items are `Text "…"` (the clause's text; when absent, the spans concatenated) and register spans: `Norm "…" => rule, rule`, `Definition "…" [=> ids]`, `Invariant "…" => invariant`, `Acceptance "…"`, `Commentary "…"`. Spans are in document order. Declaring a clause id twice replaces the first. `test/spec/spec_012_1_clauses_resolve.eflint`

**12.3 `From`.** An act, duty, immunity, or invariant may carry `From CLAUSE "span"`: the English it is the meaning of. The clause must be declared and must contain the quoted text. `test/spec/spec_012_1_clauses_resolve.eflint`

**12.4 Coverage.** A clause's spans, concatenated in order, reproduce its text exactly. `test/spec/spec_012_3_coverage.eflint`

**12.5 Norms are interpreted.** Every `Norm` span names at least one rule, and every id a span names is a declared act, duty, immunity, or invariant; an `Invariant` span names a declared `Invariant`. `test/spec/spec_012_4_norm_needs_rule.eflint`, `spec_012_7_invariant_span.eflint`

**12.6 Every rule has its English.** Every declared act, duty, immunity, and invariant is named by some span, in a clause or by its own `From`. A rule with no span is the question and the rule is the answer under review (Law 8). `test/spec/spec_012_5_every_rule_named.eflint`

**12.7 Verbatim.** Each clause's text occurs verbatim in the document. A document that cannot be read is a warning, not a failure, and the check is skipped. `test/spec/spec_012_6_verbatim.eflint`

**12.8 Approval.** `Approved HASH` records the hash of the clause's text when its spans and meanings were reviewed. A clause whose text hashes to its approval is current; one with no approval, or whose text has drifted, is STALE: the report prints the hash to declare once reviewed, and names the rules whose reviewed status the drift invalidates. The English is never edited to fit a rule, and an `Approved` value is never copied to silence the check (`AGENTS.md`). `test/spec/spec_012_2_approved_hash.eflint`

**12.9 Tracing.** `charter trace <clause> <file>` prints the clause's span table: register, text, and the rules each span means, with the approval state and current hash.

*Reused from v0.3:* the records `Clause`, `Span`, `Register` and the functions `covered`, `normsInterpreted`, `reverseProvenanceWith`, `stale`, `invalidated` in `src/Charter/Core/Provenance.lean` are the same definitions the v0.3 checker used (Law 13: one definition).
