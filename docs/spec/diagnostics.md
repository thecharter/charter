# 016 — Diagnostics

Every error and warning the `charter` binary reports is a record
`{code, severity, message, span: {file, line, col}, notes}` (plan §3). Codes are
allocated here and never reused or renumbered (Quint ADR002). A code's message is
hand-written and names the construct and its location; no message names the
engine (Law 11). `test/diagnostics/` holds one fixture per code once the fixture
format (plan §5.4) lands; until then the column says where the code is raised.

Severity: `error` stops evaluation of the program (resolution continues to report
more errors); `warning` does not.

## Lexical and syntactic (CHR001–CHR009)

| Code | Severity | Meaning | Raised by |
|---|---|---|---|
| CHR001 | error | unexpected character; the lexer cannot form a token | `Charter.Surface.Lexer` |
| CHR002 | error | unterminated string literal | `Charter.Surface.Lexer` |
| CHR003 | error | unexpected token; the parser expected something else (message says what) | `Charter.Surface.Parser` |
| CHR004 | error | a phrase or declaration is missing its `.` terminator at end of input | `Charter.Surface.Parser` |
| CHR005 | error | a `#include` or `#require` names a file that cannot be found or read (the message lists the directories searched) or the include chain is too deep | `Charter.Cli.Load` |

## Resolution and typing (CHR010–CHR049)

| Code | Severity | Meaning | Raised by |
|---|---|---|---|
| CHR010 | error | undeclared type or placeholder | `Charter.Resolve` |
| CHR011 | error | wrong number of arguments for a product type | `Charter.Resolve` |
| CHR012 | error | a value of one type where another was needed and no conversion applies | `Charter.Resolve` |
| CHR013 | error | `Extend` names a type that is not declared | `Charter.Resolve` |
| CHR014 | error | a domain extension (`Identified by`/`Domain` in an `Extend`) on a type whose domain is not a primitive of that kind | `Charter.Resolve` |
| CHR015 | error | `Holds`, `Enabled`, or `Violated` applied to a literal rather than an instance | `Charter.Resolve` |
| CHR016 | error | projection `e.x` on a value that is not a product containing `x` | `Charter.Resolve` |
| CHR017 | error | a `Syncs with` operand that is not an instance expression | `Charter.Resolve` |
| CHR018 | error | a primitive type applied to other than exactly one argument | `Charter.Resolve` |
| CHR019 | warning (pending ruling B9) | a type declared twice; the later declaration replaces the earlier | `Charter.Resolve` |
| CHR020 | error | derivation not stratifiable: a cycle through negation, naming the types on the cycle (D6) | `Charter.Resolve` |
| CHR021 | error | a type used in a position that needs a composite (product) type | `Charter.Resolve` |
| CHR022 | error | `Except under` or `Against` names something that is not an act | `Charter.Resolve` |

## Evaluation (CHR100–CHR149)

| Code | Severity | Meaning | Raised by |
|---|---|---|---|
| CHR100 | error | missing input: an instance of an open type has no truth value and the state has none to infer | `Charter.Eval` |
| CHR101 | error | cannot enumerate an infinite domain (`String`, `Int`) | `Charter.Eval` |
| CHR102 | error | a variable is not bound (internal; a resolution gap) | `Charter.Eval` |
| CHR103 | error | a phrase triggers a type that is not an act or event | `Charter.Eval` |
| CHR104 | error | evaluation fuel exhausted (a derivation or sync chain did not converge within the bound) | `Charter.Eval` |
| CHR105 | error | an undeclared type reached the evaluator (internal; a resolution gap) | `Charter.Eval` |
| CHR106 | error | `@ t` would move the clock backwards (D7) | `Charter.Eval.Interpreter` |

## Claims are not diagnostics

A query (`?e`, `?!e`, `?-e`, `?--e`), a scenario expectation, and a theorem outcome are *claims* `{claim, tag, about, span}` with one of the tags `proved | decided | checked | assumed` and one of the questions `occurred | lawful | valid | holds` (plan §2.2.12). A failed query is a failed claim, exit status non-zero from `charter test`, and never a CHR code.
