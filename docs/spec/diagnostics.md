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
| CHR019 | error | a type, parameter, or amount declared twice (`003.11`, `D39`; use `Extend` or `Amend`) | `Charter.Resolve` |
| CHR020 | error | derivation not stratifiable: a cycle through negation, naming the types on the cycle (D6) | `Charter.Resolve` |
| CHR021 | error | a type used in a position that needs a composite (product) type | `Charter.Resolve` |
| CHR022 | error | `Except under` or `Against` names something that is not an act | `Charter.Resolve` |
| CHR023 | error | `Use` names no declared module, or gives the wrong number of arguments (D8) | `Charter.Resolve` |
| CHR024 | error | a `Function` whose domain is not a product of exactly two components (003.7; eFLINT ignores its assignments silently) | `Charter.Resolve` |
| CHR025 | warning | a binder over an act whose domain is not enumerable and that has a `Holds when`: it sees only the act's assigned instances, since the rule is judged per instance and never materialised (004.7, D15) | `Charter.Resolve` |
| CHR026 | error | `Overridden by` names something that is not a duty (007.3) | `Charter.Resolve` |
| CHR027 | error | `Terminated by` or `Created by` names an act that lacks one of the duty's components, so it cannot bind it (006.4) | `Charter.Resolve` |
| CHR028 | warning | `Exists` or `Forall` over an enumerable type with a constant `True`/`False` body: it tests only whether the domain is non-empty, ignoring whether any instance holds (010.6) | `Charter.Resolve` |
| CHR029 | error | under `--require-provenance`: normative rules lack an authoritative readable `Document` and `Clause` coverage (012.10, T08) | `Charter.Resolve.AssuranceGates` |
| CHR030 | error | under `--forbid-midstream-decls`: a declaration phrase appears after an execution, assignment, or query phrase at top level (018.2) | `Charter.Resolve.AssuranceGates` |
| CHR031 | error | under `--require-complete-explore`: invariants are declared without a positive exploration depth (`--explore N` or `//! explore: N`) (018.2) | `Charter.Resolve.AssuranceGates` |
| CHR032 | error | a `Power` or `Finding` declaration omits `Valid when <expr>` (institutional powers require explicit competence conditions; use `Act` when validity defaults to `True`, 005.10, 005.11) | `Charter.Resolve` |
| CHR033 | error | `SubmitEvidence`, `RetractEvidence`, `Supports`, `Rebuts`, `Retracts`, or `Resolves` targets a type not declared `Evidenced` (003.13, 005.11, 011.14) | `Charter.Resolve` |
| CHR034 | error | defeasible `Overrides` / `Priority` rules on a type contain a priority cycle or duplicate rule ID (004.12, 007.6) | `Charter.Resolve` |
| CHR035 | error | `charter generate` target does not support a construct in the specification (no silent rule dropping, 017.2) | `Charter.Project` |
| CHR036 | error | an application gives two different arguments to a component its type names twice (003.3; both positions hold one value, so one argument would be dropped silently) | `Charter.Resolve` |
| CHR037 | error | an `Amend` whose `Installs` block declares a `Param` (014.1, 014.3; an amendment installs rules and leaves state intact, so the parameter would silently keep its value) | `Charter.Resolve` |
| CHR038 | error | a rule that derives a fact, a duty's violation, or an immunity reads an `Evidenced` fact without naming a status (004.11; only an act's `Holds when` and `Valid when` are three-valued) | `Charter.Resolve` |
| CHR039 | warning | `Count(Foreach x: f(x))` without `When` constructs an instance of `f` for every domain element of `x` without testing whether `f(x)` holds (010.7) | `Charter.Resolve` |
| CHR040 | warning | a binder over an unrestricted, non-derived, closed `Money`, `Quantity`, `Duration`, or built-in `int`/`string` carrier type ranges over held instances of that type itself, of which none are asserted (004.7) | `Charter.Resolve` |
| CHR041 | warning | an `Immunity` has no `Holds when` / `Default` rule and nothing creates an instance of it, so it protects no one (007.4) | `Charter.Resolve.AssuranceGates` |
| CHR042 | warning | an `Act` declares both `Except under` and `Holds when` (`Holds when` is ignored when `Except under` is present, 007.2) | `Charter.Resolve` |

## Evaluation (CHR100–CHR149)

| Code | Severity | Meaning | Raised by |
|---|---|---|---|
| CHR100 | error | missing input: an instance of an open type has no truth value, or an effect reads an unset `Var` or a `Function` at an unassigned argument (003.6, 005.4) | `Charter.Eval` |
| CHR101 | error | cannot enumerate an infinite domain (`String`, `Int`) | `Charter.Eval` |
| CHR102 | error | a variable is not bound (internal; a resolution gap) | `Charter.Eval` |
| CHR103 | error | a phrase triggers a type that is not an act or event | `Charter.Eval` |
| CHR104 | error | evaluation fuel exhausted (a derivation or sync chain did not converge within the bound) | `Charter.Eval` |
| CHR105 | error | an undeclared type reached the evaluator (internal; a resolution gap) | `Charter.Eval` |
| CHR106 | error | `@ t` would move the clock backwards (D7) | `Charter.Eval.Interpreter` |
| CHR108 | error | `MulDivRound` division by zero or non-zero remainder under `ExactOrReject` (010.12) | `Charter.Eval` |
| CHR109 | warning | `Retracts` / `RetractEvidence` found no active matching evidence from that source to withdraw (005.11) | `Charter.Eval` |

## Claims are not diagnostics

A query (`?e`, `?!e`, `?-e`, `?--e`), a scenario expectation, and a theorem outcome are *claims* `{claim, tag, about, span}` with one of the tags `proved | decided | checked | assumed` and one of the questions `occurred | lawful | valid | holds` (plan §2.2.12). A failed query is a failed claim, exit status non-zero from `charter test`, and never a CHR code.
