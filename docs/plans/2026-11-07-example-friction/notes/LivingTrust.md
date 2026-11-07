# LivingTrust
## Size
English sentences: 14. Five article files plus a root. Clause blocks: 11. Scenarios: 6.
Declarations no clause span can refer to: `trustee`, `incapacitated`, `successor`, `share`,
`in-force`, `fund`, `death`, `year-ends`.
## What was hard
1. `Document "trust.md"` followed by `#require …` : `CHR004: expected '.' to end the phrase but
   found '#require'`.
2. `Terminated by account` on a duty with a claimant: `CHR027: the component person' of
   annual-account is not a component of account`. One account discharges the duty to every
   beneficiary, so the act has no recipient; I wrote the `Terminates (Foreach …)` by hand.
3. `usd <= fund` : `CHR012: cannot use an instance of fund where an integer is needed`. A money
   variable is read as `fund.usd`.
4. Both of those were reported at `4-duties.charter:3:1` and `5-distributions.charter:3:1`, the
   first line of the block, six and four lines above the fault.
5. Article 2 (revocation) needs `incapacitated`, which Article 3 defines. The document's order is
   not a dependency order even in a two-page trust.
## Improvements
1. **`Power` conditions written twice.** Today:
   ```
   Power revoke Actor person
     Holds when person == Margaret && in-force()
     Valid when person == Margaret && Not(deceased(Margaret)) && Not(incapacitated())
   Power pay-settlor Actor person Related to usd
     Holds when trustee(person) && Not(deceased(Margaret))
     Valid when trustee(person) && Not(deceased(Margaret)) && usd <= fund.usd
   ```
   Five powers, five near-duplicate pairs. Proposed: a power's `Holds when` defaults to its
   `Valid when`, so the common case is one line:
   `Power revoke Actor settlor Valid when alive(settlor) && Not(incapacitated())`.
2. **Money.** Today: `Fact usd Identified by Money(USD, 2)`, `Var fund Identified by usd`,
   `settle(Margaret, 50000000)`, `fund.usd`, and
   `share(Anna, MulDivRound(fund.usd, 1, 2, Floor)), share(Ben, MulDivRound(fund.usd, 1, 2, Floor))`.
   Proposed: `Var fund : USD`, `settle(Margaret, $500,000)`, `Split fund Equally Among Anna, Ben Into share`.
   The author today must know cents, the carrier type, projection, and rounding mode.
3. **Roles that change hands.** `trustee` is the same three-rule pattern as the will's executor.
4. **"Every beneficiary consents".** Today `consented(Anna, asset) && consented(Ben, asset)`,
   and `(person' == Anna || person' == Ben)` in the year-end effect. The beneficiaries are named
   in 5.2 and nowhere declared as a group. Proposed: `Group beneficiary Is Anna, Ben` (a subset of
   `person`), then `Forall beneficiary: consented()`.
5. **Recurring duties.** "within sixty days after the end of each year" needed a hand-triggered
   `Event year-ends` and an effect that creates one duty per beneficiary:
   ```
   Extend Event year-ends
     Creates (Foreach person, person': annual-account(person, person')
                When trustee(person) && (person' == Anna || person' == Ben))
   ```
   Proposed: `Duty annual-account Holder trustee Claimant beneficiary Every year Due within 60`.
6. **Prohibitions.** "The trustee may not mix …" is `Act mix-with-own-property Actor person Holds when False`.
   It cannot say *who* is forbidden, and reads as a puzzle. Proposed:
   `Prohibited mix-with-own-property For trustee`.
7. **Ages and dates.** "reaches the age of twenty-five" is a fact asserted by hand
   (`+reached-twenty-five(Anna)`); there is no birth date and no calendar.
8. **Article files.** Each article re-`#require`s what it needs so it can be checked alone, and
   the `Document` is declared only in the root, so an article checked alone has clauses but no
   document and the verbatim check is silently skipped.
## Tool defects
- Diagnostics at block start (above). Scenario claim failures report the scenario's first line
  (`[scenario …, phrase 3]:6`), not the claim's line.
- An article checked alone passes `check --deny-warnings` although none of its clause text was
  compared with any document.
## What a lay author would have guessed
`usd <= fund`, `Terminated by account`, `Clause 3.2 … => trustee`, `Actor trustee`.
