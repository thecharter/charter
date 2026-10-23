# Mission

An institution is three answers about one event: did it occur, was it lawful, did it take effect. A Charter program is the English those answers come from, written so that a machine can give them. Everything else in the language exists to keep those three answers honest, traceable to their sentence, and the same no matter who or what is asking.

The name is the thing itself: a charter is the document that creates a body, grants it its powers, and binds it. Charter programs are such documents, including the clauses by which the body changes its own charter.

## Goals

Charter exists to do three things, in this order of precedence:

1. **Fully formally represent the Protocol of Sovereign Agency.** Every clause of the protocol, every quantity it reasons about, every party, deadline, power, protection, and remedy, written in Charter, checked by Charter, with its English beside it. Nothing of the protocol lives only in a proof assistant or only in prose. The protocol amends itself under its own rules, so representing it fully means that an amendment is an event the program judges like any other.
2. **Be a universal language for any such law or contract.** The constructs that express the protocol are institutional, not protocol-specific: facts, acts, duties, powers, immunities, time, parties, and the English they come from. Any constitution, bylaw, charter, statute, or agreement between parties is in scope, and nothing in the language names one of them.
3. **Be one language for human contracts, smart contracts, and law.** The same program reads as the agreement people sign, runs as the guard a blockchain enforces, and briefs the machine that acts under it. Charter does not translate between these; it is the single source from which each is projected, and each projection is proved faithful.

The order matters when they conflict. A feature the protocol needs that the second goal would generalize away is added and then generalized, not refused. A projection the third goal wants that the semantics cannot prove faithful is not shipped.

## Laws

Every design decision in `docs/meetings/README.md` is an instance of a law below, or names the new law it needs, which is written here before the decision is. Each law carries its test: the question that decides a case.

**1. Occurrence is never blocked.** Any event can occur. The language forbids nothing from happening; it says only what follows when it does. A program that makes a forbidden act unperformable has described a machine, not an institution. *Test: does this make a forbidden event unreachable?*

**2. Three questions, three answers.** Whether an act occurred, whether it was lawful, and whether it had institutional effect are independent judgments. The tool never collapses two into one, and the user can always tell which one an output is about. An unlawful act may be valid; a lawful act may be void. *Test: can the reader tell from this output which of the three it answers?*

**3. Violations are facts; findings are events.** A breach is recorded when it occurs. A finding is an institutional act whose effect is the breached duty's declared remedies. The link between them is an assumption a program states, never a theorem the language supplies. *Test: does anything read a violation where the institution meant a finding, or the reverse?*

**4. Exceptions keep their kind.** A scope condition, an authority exception, duty-over-duty precedence, and protection-over-power precedence are four mechanisms with four spellings. A breach's consequences are remedies, never exceptions. *Test: which of the four is this, and is it written as that one?*

**5. Rules are data.** A duty, a power, an immunity, a clause, and a span are records with named fields, never functions, predicates, or anything a projection would have to evaluate to inspect. Every view, prompt, guard, machine, and diff reads the record. *Test: can every projection inspect this without evaluating it?*

**6. The world is input.** Charter never invents a fact. Whatever is not derived from other facts was asserted by a party's act or supplied by the environment, and the program can say which. Charter decides what follows; it never decides what is true. *Test: where did this fact come from?*

**7. Time is state, not events.** A fact carries the time it was established and when it expires. Deadlines, notice windows, pauses, and "held for" are conditions over those stamps, never synthetic lapse events in the history. *Test: does this add an event to the trace that no party performed?*

**8. Every norm carries its English, and the English leads.** A rule names the span that justifies it; a clause's text is checked verbatim against the authoritative document; a clause whose text has drifted is stale until re-approved; a rule with no span is a warning. When the English and the rule disagree, the English is the question and the rule is the answer under review. *Test: can a reader go from this rule to the sentence, and from the sentence to every rule it grounds?*

**9. The evaluator is the semantics.** One definition of what a program means, written in Lean and proved; one evaluator, proved to agree with it; every projection proved sound against it. There is no second interpreter, no informal reference, and no projection whose faithfulness is tested rather than proved. *Test: if this code were wrong, which proof would fail?*

**10. The kernel is the only trusted checker.** No `sorry`, no `native_decide`, no axiom beyond Lean's standard three; a decided scenario depends on no axioms at all. Every claim the tool makes carries one of four tags and never a fifth: *proved* (for all traces and parameters, kernel-checked), *decided* (on concrete inputs, kernel-evaluated), *checked* (by the evaluator at run time, not kernel-certified), *assumed* (a hypothesis the program names). *Test: what does `#print axioms` say, and which tag does the user see?*

**11. The author never sees Lean.** Charter is written, checked, run, tested, proved, and projected through one binary. No diagnostic, path, flag, or document shown to an author names Lean, Lake, a tactic, or a theorem it did not ask for. Lean is how Charter is right, not how Charter is used. *Test: does any text the author can see mention the engine?*

**12. Every eFLINT program is a Charter program.** Charter's core is eFLINT's constructs, phrases, and semantics, unchanged in spelling and meaning. Charter extends; it does not revise. Where eFLINT has a documented defect, Charter fixes it under a decision that names the defect and the tolerance. *Test: does the vendored eFLINT corpus still pass?*

**13. One spelling per meaning.** Two ways to write one thing is a defect; an escape hatch that outlives its reason is a defect. When the better route exists, the old one is deleted, not deprecated. *Test: is this still the only way to say it, or a habit?*

**14. The mission is tested, not described.** Each law above has a program under `test/gates/` that fails if the law is quietly lost, and the three goals have theirs: the full protocol checks and proves; the language layer names no institution; each projection's soundness theorem builds. A rule with no such program is written down before the rule lands. *Test: what program fails if this is lost? If none, write it first.*

Laws 1 through 4 are what an institution is; they are why goal 1 is satisfiable at all. Laws 5 through 7 are what a program is made of: inspectable records, facts from outside, time as a stamp. Law 8 binds the program to its document, which is what makes it a contract rather than a model. Laws 9 and 10 are how goal 3 is honest: a projection is a theorem, not a translation, and the theorem is checked by one thing. Law 11 is goal 2's precondition: a universal language cannot require a proof assistant of its authors. Law 12 is the decision to stand on prior work rather than beside it. Laws 13 and 14 are the discipline that keeps the first twelve true as the code changes.
