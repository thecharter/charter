# Deed
## Size
English sentences: 6. Clause blocks: 5 (6 spans). Scenarios: 6.
## What was hard
Nothing was rejected. The first version, without role placeholders, passed but read badly:
`deed(person, person'', parcel) && title(parcel, person'') && Not(recorded(person'', parcel))`
and `payoff-due(person', person, parcel, string)` with holder and claimant swapped by position.
Rewriting with `Placeholder grantor For person` let every condition drop its arguments
(`signed()`, `deed()`, `lien()`) and let `Created by demand-payoff` bind by role name.
## Improvements
1. **Declare a role where it is used.** Roles cost a line each
   (`Placeholder grantor For person`, `Placeholder grantee For person`) and are the difference
   between the two versions above. Proposed: `Fact person Identified by Robert, Sofia As grantor, grantee`
   or roles inferred from `Actor grantor : person`.
2. **`Holds when True`.** `Act sign … Holds when True`: an act with no condition is never
   enabled, so "anyone may" must be said. Proposed: an act with effects and no condition is
   enabled.
3. **`Holds when` repeated in `Valid when`** (`deliver`): see LivingTrust 1.
4. **World input has no spelling.** `+paid-value(Victor, Lot7)` and `+notice(Victor, Lot7)` are
   asserted in scenarios with no act behind them. They are facts about the world. Proposed:
   `Input Fact notice Identified by grantee * parcel`, so `check` can tell an input from a fact
   that an act should have created.
5. **Long instance names in cases.**
   `payoff-due(Robert, Sofia, Lot7, "county tax lien")` is written five times. Proposed: a
   scenario-local name, `Let d = payoff-due(Robert, Sofia, Lot7, "county tax lien").`
## Tool defects
None new. `charter fmt --stdout` on this file deletes every comment and blank line,
parenthesises every condition onto one line, and adds a `Text "…"` line that repeats each
clause a third time.
## What a lay author would have guessed
`Actor grantor` without first declaring the placeholder.
