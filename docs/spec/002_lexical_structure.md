# 002 — Lexical structure

**Status:** draft (2026-10-23). The meaning is fixed by D2 (eFLINT 4.1's lexer, `Parse.hs` `lexer_settings`) and D14; the wording awaits Eric's blessing. Implementation: compliant (`src/Charter/Surface/Lexer.lean`); every statement below has its conformance test under `test/spec/` and all pass.

A Charter source file is a sequence of tokens separated by whitespace and comments.

**2.1 Identifiers.** An identifier is a word starting with a lowercase letter and continued by lowercase letters, `_`, or `-` immediately followed by a lowercase letter (`neighbour-of`, `cast_vote`). A digit ends the word: in `person1` the identifier is `person` and `1` is the *decoration* of a variable (003.3), and so is each `'` that follows (`actor'`). Decoration may be separated from the identifier by spaces (`actor 2`). `test/spec/spec_002_1_identifiers.eflint`

**2.2 Atoms.** A word starting with an uppercase letter and continued by letters, digits, or `_` is an atom: the string literal of its own spelling, so `Bob` and `"Bob"` are the same value. A keyword is never an atom. `test/spec/spec_002_2_atoms.eflint`

**2.3 Keywords.** The keywords are eFLINT's, including the multi-word ones (`Holds when`, `Identified by`, `Related to`, `Conditioned by`, `Terminated by`, `Created by`, `Enforced by`, `Syncs with`, `Derived from`, `Violated when`, `Present when`, `Current Time`), matched longest first and only at a word boundary. `Holds when`, `Holds When`, `Present when`, and `Present When` are one keyword. `test/spec/spec_002_3_keyword_spellings.eflint`

**2.4 Comments.** `//` starts a comment to the end of the line; `/* … */` encloses one. `test/spec/spec_002_4_comments.eflint`

**2.5 Bracketed and spaced identifiers.** `[` any text without `]`, `>`, `+`, `=`, or a line break `]` is an identifier, brackets included (`[data subject]`). A sequence of identifiers separated by spaces is one identifier (`other candidate`); this is unambiguous because no construct places two identifiers side by side. `test/spec/spec_002_5_bracketed_and_spaced_identifiers.eflint`

**2.6 The dot.** A `.` immediately preceded by a non-space character and immediately followed by a lowercase letter, `(`, or `[` is a projection (010.9); every other `.` ends the phrase (011.8). `test/spec/spec_002_6_projection_dot.eflint`

**2.7 Literals.** Integer literals are unsigned decimal; `0-1` is a subtraction. String literals are double-quoted with `\"`, `\\`, `\n`, `\t` escapes. A character literal `'a'` appears only in a range `'a'..'z'` (003.2). `test/spec/spec_002_7_integers_unsigned.eflint`

**2.8 Symbols.** `?--`, `?-`, `!?`, `||`, `&&`, `<=`, `>=`, `..`, `==`, `!=`, `#include`, `#require`, and the single characters `[ ] ( ) ! , ' + - * / . = > < : ? { } % ~`.

*Differences from eFLINT:* none in token classes. eFLINT's generalised parser resolves the dot and the `When` ambiguities by trying every parse; Charter decides each once (2.6, D14).
