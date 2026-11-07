# PowerOfAttorney

Files: `Examples/PowerOfAttorney/poa.md`, `poa.charter`, `cases/household.charter` (7 scenarios).
`charter check --require-provenance --deny-warnings poa.charter` ends
`ok   Examples/PowerOfAttorney/poa.charter: 1 phrase(s) resolve (28 declared types, 7 clauses, coverage complete, 0 warning(s))`.
`charter test --deny-warnings cases/household.charter` ends `1 passed, 0 failed, 1 total`.
Mutation: in a copy under `/tmp/cf-poa/mut`, `?valid pay(Marcus, Lakeside, 12000)` flipped to `?!valid` gave
`cases/household.charter [scenario after-revocation-only-a-person-without-notice-is-protected, phrase 5]:52: claim failed: ?!valid pay("Marcus", "Lakeside", 12000)` and `0 passed, 1 failed`.

## Size

English sentences: 16. Charter lines outside clause blocks and comments: 59. Clause-block lines: 20.
Case lines: 82. Declarations no sentence of the text refers to: 2 (`usd`, the type that has to be
declared before an amount of money can be a component; `regains-capacity`, which the text only
implies with "while I am incapacitated"). Two more exist only as a pair for one idea: every dealing
creates both `dealt` and `unrecorded`, because "binds me" and "keeps a record of" each need a fact.

Known issues, counted in this example:

- A span cannot name a fact or event: 5 of 11 spans. P.4 "authority continues while I am
  incapacitated" means the derived `authority`; P.5 "ends when I revoke it, and it ends at my death"
  means `authority` and the event `death`; P.6 means the derived `binding`; P.2 "binds me" means
  `binding`; P.1 "appoint Marcus Brooks as my agent" has no declaration at all (it is eleven
  `== Marcus` comparisons). Each of these spans lists `pay, transfer, give` instead, so the same
  three names appear in four spans and tell the reader nothing about which sentence does what.
- `person == Helen` / `agent == Marcus`: 11 comparisons on 11 lines.
- `Power` whose `Valid when` is its `Holds when` verbatim: 2 of 5 (`revoke`, `change-beneficiary`).
- `Created by`/`Terminated by` and component names: worked once (`account-due`), failed once
  (a record-keeping duty, CHR027, below).
- Amounts in cents: 1 in the program (`50000` for five hundred dollars), 28 in the case file.
- A failed claim reported the scenario's first line: every time (2 of 2 failures I caused).
- `Holds when True`, `Document` before `#require`, "at least two of": 0.

No calendar: nothing was distorted here. "Within thirty days of my request" is a count of days.

## What was hard

1. **`lib/agency_mandate` with one `person` type.** First thing written:

   ```
   Fact person Identified by Helen, Marcus, Bank
   Use agency-mandate(poa, person, person, person, dealing) As am.
   am-grant-mandate(Helen, Marcus, ThePoa, 50000).
   ```

   No diagnostic. `charter run` shows `+am-mandate-holder(poa("ThePoa"),person("Helen"),person("Helen"))`:
   the agent argument was dropped and the principal became her own agent. The first claim then failed
   with only `claim failed: ?valid am-recognize-on-principal("Bank", "D1", "ThePoa", "Helen", "Marcus", 100)`.
   See Tool defects 1.

2. **`lib/agency_mandate` with three placeholders.** `Placeholder principal For person` (and `agent`,
   `third`), then `Use agency-mandate(poa, principal, agent, third, dealing) As am`. This runs. I did
   not keep it. Honest verdict: it did not help, for these reasons, each observed by running it.
   - `check --require-provenance` answers `FAIL rules with no English: am-imputation-requires-direction,
     am-revoked-notified-never-binds-after, am-bound-within-mandate-cap, am-recognize-on-principal,
     am-submit-trade-confirmation, am-execute-delegate-trade, am-report-trade,
     am-deliver-revocation-notice, am-revoke-mandate, am-grant-mandate`. Ten rules need a sentence;
     a two-page power of attorney has sentences for about five of them. The three invariants and
     "imputation" have none.
   - The module's cap is cumulative over every dealing. The text caps each gift and does not cap
     bills at all.
   - A dealing is two acts with invented identifiers: `am-execute-delegate-trade(Marcus, D1, ThePoa,
     Bank, 100)` then `am-recognize-on-principal(Bank, D1, ThePoa, Helen, Marcus, 100)`, six arguments,
     performed by the bank. The text has one act: the agent pays.
   - Protection of a third party without notice needs `+am-apparent-authority-enabled(ThePoa)`, a
     fact no act creates. Without it the claim after revocation fails:
     `t2.charter [scenario after-revocation, phrase 3]:22: claim failed: ?valid am-recognize-on-principal(...)`.
   - Amounts are `int`, not `Money`. There is no death, no capacity, and the report duty is "two
     days after each trade", not "thirty days after a request".
   - Needed two types that exist only for the module: `Fact poa Identified by ThePoa` and
     `Fact dealing Identified by D1, D2`.
   The plain program is 59 lines; the module version needed the same facts for death, capacity,
   gifts and the account on top of the module.

3. **"No unrecorded dealing" was silently always true.** Written first:

   ```
   Act give-account Actor agent Recipient person
     Conditioned by Not(Exists third, usd: unrecorded())
   ```

   No diagnostic from `check --deny-warnings`. The test said
   `cases/household.charter [scenario the-account-is-due-thirty-days-after-the-request, phrase 5]:73: claim failed: ?!lawful give-account("Marcus", "Helen")`.
   Cause (spec 004.7): `usd` is a money type, so a binder over it ranges over held instances of
   `usd` itself, and there are none. The `Exists` is false whatever `unrecorded` holds. The spelling
   that works is `Not(Exists unrecorded: unrecorded)`. See Tool defects 2.

4. **"The agent keeps a record" as a duty.** Written first:

   ```
   Duty to-record Holder agent Claimant person Related to third, usd
     Created by pay
     Terminated by record
   ```

   `t8.charter:1:0: error CHR027: `Created by pay` on to-record: the component person of to-record is not a component of pay, so pay cannot bind it`
   (reported at line 1, column 0; the duty was on line 6). The claimant is always Helen, but `pay`
   has no component for her and a duty cannot name a fixed claimant. I used a plain fact
   `unrecorded` created by each dealing, so the text's duty is not a `Duty` in the program.

5. **`Immunity` for the protected third party.** It can be written, and it passes (`/tmp/cf-poa/t9.charter`):

   ```
   Immunity authority-ended Holder third Against pay, transfer, give
     Holds when signed() && Not(authority())
     Unless Not(notice())
   ```

   I did not keep it. An immunity makes an act against its holder void. The text's protection is
   the opposite: an act that would be void stands. So the immunity's "holder" is the person who
   loses (the third party who had notice), its name has to describe the unprotected case, and the
   protection itself is the double negative `Unless Not(notice())`. The plain form is one derived
   fact, `binding`, read by three `Valid when` lines. The immunity form has one real advantage:
   a span can name it, so P.6 would map to one declaration instead of four names.

Everything else resolved at the first attempt.

## Improvements (most valuable first)

### 1. A protection: the dual of `Immunity` ("this act stands even though it was not lawful")

Today (3 powers, 1 derived fact, and P.6 names four rules):

```
Fact binding Identified by agent * third
  Holds when agent == Marcus && signed() && (authority() || Not(notice()))
Power pay Actor agent Recipient third Related to usd
  Holds when agent == Marcus && authority()
  Valid when binding()
  Creates dealt(), unrecorded()
...
  Norm "A person who deals with the agent without notice that the agent's authority has ended is protected: the dealing binds me or my estate. Once that person has notice, it does not." => give-notice, pay, transfer, give
```

Proposed, does not parse today:

```
Power pay Actor agent Recipient third Related to usd
  Holds when authority()
  Creates dealt(), unrecorded()
Protection without-notice Holder third For pay, transfer, give
  Unless notice()
...
  Norm "A person who deals with the agent without notice ... it does not." => give-notice, without-notice
```

Meaning: a `Power` with no `Valid when` is valid exactly when lawful; an act named in `For` whose
recipient holds the protection is valid although unlawful. Saves the `binding` fact (2 lines), three
`Valid when` lines, and three names in the P.6 span; the sentence "is protected" becomes one
declaration with the protected person as its holder. Occurs once here (three acts); the same shape
is `Deed` D.5 (later buyer without notice) and `TreasuryMandate` (apparent authority).

### 2. "Has it happened" without a flag: `Done(act)`

Today (4 flags, each with the act or event that sets it):

```
Bool signed
Bool revoked
Bool deceased
Event death Creates deceased()
Act sign Actor person
  Holds when person == Helen
  Creates signed()
Bool authority
  Holds when signed() && Not(revoked()) && Not(deceased())
```

Proposed, does not parse today:

```
Event death
Act sign Actor person
  Holds when person == Helen
Bool authority
  Holds when Done(sign) && Not(Done(revoke)) && Not(Done(death))
```

`Done(a)` holds once a valid instance of `a` has occurred. Saves 3 `Bool` lines and 3 `Creates`
lines here, and the reader no longer has to check that `signed` is set by `sign` and nothing else.
Occurs 3 times (`signed`, `revoked`, `deceased`); `incapacitated` is a true toggle and stays.

### 3. Name the person in a role once

Today: `agent == Marcus` 6 times, `person == Helen` 5 times.

```
Power give Actor agent Recipient third Related to usd
  Holds when agent == Marcus && authority() && usd <= gift-limit
Power revoke Actor person
  Holds when person == Helen && authority() && Not(incapacitated())
  Valid when person == Helen && authority() && Not(incapacitated())
```

Proposed, does not parse today:

```
Role principal Is Helen
Role agent Is Marcus
Power give Actor agent Recipient third Related to usd
  Holds when authority() && usd <= gift-limit
Power revoke Actor principal
  Holds when authority() && Not(incapacitated())
```

An act whose actor is a `Role … Is X` is neither lawful nor valid for anyone else. Saves 11
comparisons. It also removes a real hazard: a `Valid when` that forgets `agent == Marcus` lets any
stranger bind the principal, and nothing warns. P.1 "I appoint Marcus Brooks as my agent" would then
have a declaration to point at.

### 4. A fixed party in a duty

Today (the record-keeping duty could not be written; this is the substitute):

```
Fact unrecorded Identified by third * usd
Power pay ... Creates dealt(), unrecorded()
Power transfer ... Creates dealt(), unrecorded()
Power give ... Creates dealt(), unrecorded()
Act record Actor agent Related to third, usd
  Holds when agent == Marcus && unrecorded()
  Terminates unrecorded()
```

Proposed, does not parse today:

```
Duty to-record Holder agent Claimant Helen Related to third, usd
  Created by pay, transfer, give
  Terminated by record
Act record Actor agent Related to third, usd
```

A constant (or a `Role`) in a component position. Saves the `unrecorded` fact, three effect items
and two lines of `record`; "the agent keeps a record" becomes a duty a span can name. Occurs once
here; `TreasuryMandate` writes `report-trade-duty(accountant, AcmeCorp, trade-id)` by hand for the
same reason.

### 5. One declaration for acts that differ only in name

Today:

```
Power pay Actor agent Recipient third Related to usd
  Holds when agent == Marcus && authority()
  Valid when binding()
  Creates dealt(), unrecorded()
Power transfer Actor agent Recipient third Related to usd
  Holds when agent == Marcus && authority()
  Valid when binding()
  Creates dealt(), unrecorded()
```

Proposed, does not parse today:

```
Power pay, transfer Actor agent Recipient third Related to usd
  Holds when agent == Marcus && authority()
  Valid when binding()
  Creates dealt(), unrecorded()
```

Saves 4 lines per extra act (4 here; `give` differs by one conjunct and would be
`Extend Power give Holds when usd <= gift-limit` if `Extend` narrowed instead of widening).
Occurs once.

### 6. One condition for a power that is void exactly when it is not allowed

Today:

```
Power change-beneficiary Actor person Related to account, person'
  Holds when person == Helen
  Valid when person == Helen
```

Proposed, does not parse today:

```
Power change-beneficiary Actor person Related to account, person'
  Only when person == Helen
```

Saves one line and the question "are these two meant to differ?" on every power. Occurs 2 of 5.

### 7. Entries, not a set, when the thing is money

Today `Fact dealt Identified by third * usd`: two payments of the same amount to the same payee are
one fact (verified: two `pay(Marcus, Bank, 100)` give `Sum(Foreach dealt: dealt.usd) == 100`). The
author has to invent an identifier component to keep them apart. Proposed, does not parse today:

```
Ledger dealt Identified by third * usd
```

Each `Creates dealt()` adds an entry; `Sum` counts every entry. Saves a `dealing-id` type, an
argument on every act and every scenario line, and a silent under-count. Occurs once (I left the
set, since no sentence of this text sums the dealings).

### 8. Money written as money

Today `Param gift-limit : Money(USD, 2) = 50000` and `give(Marcus, Nora, 50001)`. Proposed, does
not parse today: `Param gift-limit = $500.00` and `give(Marcus, Nora, $500.01)`. Saves the
`Fact usd Identified by Money(USD, 2)` line and every misreading of `50000` as fifty thousand.
Occurs 29 times.

## Tool defects

1. **A product with the same component twice drops an argument silently.**

   ```
   Fact person Identified by Helen, Marcus
   Fact pair Identified by person * person.
   +pair(Helen, Marcus).
   ?pair(Helen, Helen).
   ?!pair(Helen, Marcus).
   ```

   Expected: an error that the component `person` occurs twice (write `person * person'`).
   Actual: `check --deny-warnings` says `ok … 0 warning(s)`; `run` shows
   `+pair(person("Helen"),person("Helen"))`, `?pair(Helen, Helen)` holds, and `?pair(Helen, Marcus)`
   also holds. The same happens through a module: `Use m(person, person)` gives
   `am-grant(Helen, Marcus)` reported as `occurred act am-grant(person("Helen"),person("Helen"))`
   (`/tmp/cf-poa/t3.charter`, `t5.charter`). Workaround: a decorated name or a placeholder per role.

2. **A binder over a money, integer or string type is silently empty.**

   ```
   Fact person Identified by Helen, Marcus
   Fact usd Identified by Money(USD, 2)
   Fact unrecorded Identified by person * usd.
   +unrecorded(Marcus, 100).
   ?(Exists person, usd: unrecorded(person, usd)).
   ?(Exists unrecorded: unrecorded).
   ```

   Expected: both hold, or a warning on the first that `usd` has no held instances to range over.
   Actual: no warning; the first query fails, the second holds (`/tmp/cf-poa/t6.charter`). Under
   `Not(…)` this makes a condition vacuously true. It follows from spec 004.7, but CHR028 warns only
   for a constant body. Workaround: bind the fact itself.

3. **Naming a fact or event in a span says it is undeclared.** `=> give-notice, binding, death`
   gives `FAIL P.6: spans name undeclared rules: binding, death`. Both are declared; they are a fact
   and an event. Expected: "binding is a fact; a span can name only acts, duties, immunities and
   invariants".

4. **CHR027 is reported at `1:0`**, the first line of the file, for a duty declared on line 6.

## What a lay author would have guessed

- `Use agency-mandate(poa, person, person, person, dealing)`: one kind of person, three roles.
  Accepted, wrong.
- `Not(Exists third, usd: unrecorded())` for "nothing is unrecorded". Accepted, always true.
- `Duty to-record Holder agent Claimant person … Created by pay` for "the agent keeps a record of
  every payment". Rejected, CHR027.
- An `Immunity` for "is protected". It means the reverse: the holder's counterparty's act is void.
- `=> binding` on the sentence that defines when a dealing binds. Rejected as "undeclared".
- `50000` read as fifty thousand dollars by anyone who has not seen `Money(USD, 2)`.
