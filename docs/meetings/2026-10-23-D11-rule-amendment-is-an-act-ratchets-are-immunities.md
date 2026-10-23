# D11 — Rule amendment is an act (`Amend`) whose effects target rule records; ratchets are immunities against `Amend`, reflexively entrenched; `Extend` never changes rules at run time

**Laws:** 1, 2, 4, 5, 6, 7, 12, 14; goal 1 (docs/mission.md). Brief: B8.
**Date:** 2026-10-23
**Status:** ruled (Eric), differs from the prediction (ratchets were predicted as `Invariant`s); Eric's words below are the ruling

## Ruling (Eric, verbatim)
Rule amendment is an act. Charter adds `Amend`, whose `Creates`/`Terminates` target rule records (Law 5). `Extend` remains eFLINT's scenario-time mechanism (Law 12) and is never used to change a program's rules at run time.

1. **Amendment is an event in the history.** Every rule change has an actor, a time stamp, a validity answer, and an effect answer (Law 2). A question of what the rules were when an earlier act occurred is answered from the trace (Laws 6, 7). `Extend` satisfies none of these, which is the fourth defect the question did not list.
2. **Ratchets are immunities, not invariants.** Each entrenched protection is `I.<NAME> Against Amend`, with the `Against` clause naming the rule records it covers (Law 4, protection-over-power). A weakening `Amend` occurs (Law 1), is recorded as performed, and is void. It does not take effect and then breach; it has no effect.
3. **Entrenchment is reflexive.** An immunity `Against Amend` covers the amendment of itself and of any record that governs `Amend`'s validity. An `Amend` that would remove or narrow such an immunity is void. Without this clause the ratchet is bypassable in two acts.
4. **The universal ratchet theorem is restated** (`Charter.Core.Ratchet`): for every valid `Amend` trajectory, every `Invariant` tagged `Entrenched` is preserved. Its proof is from clause 2: the trajectory contains no effective weakening. Tag: *proved*.
5. **Consent and timelock are `Valid when` facts** supplied by parties' acts (consent) and by stamps (timelock), per Law 6 and Law 7. An `Amend` whose consent set is incomplete or whose timelock has not elapsed is performable and void.
6. **`charter diff`** compares the rule set before and after each `Amend`, and reports which protections were tested and which voided the act.

## Gates (Law 14)
- `test/gates/amend-is-an-act`: a program in which a weakening `Amend` is performed; fails unless the trace records the act, reports it void, and leaves the rule set unchanged.
- `test/gates/amend-reflexive`: a program that first amends the ratchet immunity, then the floor; fails unless both acts are void.
- `test/gates/extend-never-at-runtime`: fails if any run-time path invokes `Extend`.

## Consequences for the plan
The rule set is part of the evaluator's state and `Immunity … Against Amend` names rule records in its `Against` clause, so the `Core.Law` record must be addressable by rule id from within the semantics. Parameter amendment (an act creating a `Var` instance) and rule amendment (`Amend`) are the same mechanism at two granularities.

## Reopens if (Eric, verbatim)
Rule records as effect targets make the evaluator's agreement proof (Law 9) materially harder. Then v1 ships parameter amendment as acts and **no** rule amendment, with the gap named against goal 1. It does not ship rule amendment as `Extend`: that would make a forbidden amendment unperformable instead of void, which is a Law 1 violation, not a reduced scope.
