# LastWill
## Size
English sentences: 11. Clause blocks: 7 (8 spans). Scenarios: 6.
Declarations no clause span can refer to (facts and an event, where the will's content lives):
`in-effect`, `revoked`, `acting`, `named`, `failed`, `entitled`, `lapsed`, `death`.
## What was hard
1. `Norm "... The executor's authority begins at my death." => death, distribute` was rejected:
   `FAIL W.3: spans name undeclared rules: death`. An event is not a "rule".
2. `Definition "I revoke every will I made before this one." => revoked` was rejected the same
   way: a span cannot name a derived fact. The revocation clause now names nothing.
3. Every clause first failed `STALE W.n: not yet approved; once reviewed, declare Approved "…"`.
   Seven 64-character digests to copy; I wrote `tools/approve-clauses` to do it.
4. `cases/estate.charter` requiring `../will.charter` warned `will.md could not be read
   (… cases/will.md)`: the document was looked up beside the case, not beside the file that
   declared it. Fixed in `src/Charter/Cli/Load.lean`, fixture `spec_012_1b`.
## Improvements
1. **Let a span name a fact (and state it).** A will's gifts are facts, not acts. Today:
   ```
   Clause W.5 Approved "662b…d641"
     Norm "I give my house to Anna Ellis. I give twenty thousand dollars to Ben Ellis." => distribute
   …
   +named(House, Anna). +named(Cash, Ben).
   ```
   The two assertions that *are* the clause sit at the bottom of the file, cited by nothing, and
   the clause points at `distribute` because it must point at an act. Proposed, does not parse today:
   ```
   Clause W.5
     Norm "I give my house to Anna Ellis." => named(House, Anna)
     Norm " I give twenty thousand dollars to Ben Ellis." => named(Cash, Ben)
   ```
   Saves the detached genesis lines and makes 5 of the 7 clauses actually traceable (W.1, W.3,
   W.5, W.6, W.7 all name `distribute` or nothing today). Pattern: 5 of 7 clauses.
2. **Cite a passage, do not retype it.** The whole will is typed twice: `will.md` and the
   `Clause` blocks (8 spans, about 900 characters), plus 7 × 75 characters of `Approved` digests.
   Proposed: the checker finds the clause under its heading and the rules cite it.
   ```
   Act distribute … From W.4, W.5, W.6, W.7      // text read from will.md, headings W.4 …
   ```
   with approvals kept in `charter.lock`, written by `charter approve`. Saves 100% of the clause
   blocks (25 of 87 lines) and every digest.
3. **A named individual as a role.** Today `Act sign Actor person Holds when person == Margaret`,
   `Default named-executor Holds when executor == Daniel`, `beneficiary == Shelter`,
   `Held(deceased(Margaret))`. Proposed: `Role testator Is Margaret` then `Act sign Actor testator`.
   Occurs 8 times.
4. **Ordered substitutes.** "Daniel, or if he cannot act, Priya" took three defeasible rules:
   ```
   Fact acting Identified by executor
     Default named-executor Holds when executor == Daniel
     Exception daniel-cannot-act Overrides named-executor
       Rejects when executor == Daniel && (declined(Daniel) || deceased(Daniel))
     Default substitute-executor
       Holds when executor == Priya && (declined(Daniel) || deceased(Daniel))
   ```
   Proposed: `Fact acting Identified by executor First of Daniel, Priya Skipping declined(executor) || deceased(executor)`.
   6 lines to 1. Same pattern in LivingTrust (trustee).
5. **"At least two".** `Count(Foreach witness: witness When witnessed()) >= 2`.
   Proposed: `AtLeast 2 witness: witnessed()`. Same pattern in LivingTrust (two physicians).
6. **Shared scenario openings.** Five of six scenarios begin
   `sign(Margaret). attest(Wendy). attest(Walt). … death(Margaret).` because a scenario cannot
   start from another. Proposed: `Scenario x After duly-executed { … }`. Saves 10 of 57 case lines.
7. **"Survives me by thirty days".** Today a conditional effect on the death event:
   `lapsed(person) When person != Margaret && Not(Held(deceased(Margaret)) For survivorship)`.
   Proposed: `Fact lapsed Identified by beneficiary Holds when deceased(beneficiary) Within survivorship After deceased(Margaret)`
   (and before it). The author should not have to see that "did not survive by 30 days" is
   "died while the testator had not yet been dead 30 days".
8. **The sum is not in the program.** "twenty thousand dollars" appears only in the English;
   `Cash` is an atom. Writing it would need a money carrier type and cents. See LivingTrust.
## Tool defects
- Document path resolved against the requiring file (fixed, see above).
- Approvals cover only the clause text. I rewrote every rule in `will.charter` (roles, implicit
  arguments) and `check` still said `approved mapping current` for all seven clauses. The check
  says the mapping was reviewed when only the English is hashed.
## What a lay author would have guessed
`=> death`, `=> revoked`, `Actor Margaret`, `at least 2 witnesses`.
