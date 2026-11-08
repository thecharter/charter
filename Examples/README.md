# Examples

Each directory is one agreement a person might actually sign: its English, the Charter
specification of it, and the cases that test it. The English texts are original, written for
these examples with invented parties. They are illustrative. They are not legal advice and are
not written for any jurisdiction.

| Directory | Document | What it shows |
|---|---|---|
| `Tenancy/` | residential lease | the toy the spec uses: deadlines, entry with notice, a capped deposit |
| `ServiceEscrow/` | milestone escrow | payment held and released on delivery |
| `TreasuryMandate/` | corporate mandate | agency, apparent authority, contested evidence, money |
| `AutonomousCommons/` | a charter for a commons | the standard library modules together |
| `LastWill/` | last will and testament | a will without two witnesses has no effect; lapse; substitute executor |
| `LivingTrust/` | revocable living trust | successor trustee on incapacity; revocable until death; split by article |
| `Deed/` | warranty deed | a grantor passes only the title held; recording; lien warranty |
| `PowerOfAttorney/` | durable power of attorney | acts outside the authority bind no one; revocation and a third party without notice |
| `HealthcareDirective/` | advance healthcare directive | capacity as a disputed fact settled by a finding; an instruction that overrides the agent |
| `Prenup/` | prenuptial agreement | separate and marital property as defaults and exceptions; equal division; lapse after ten years |
| `ParentingPlan/` | parenting plan and child support | alternating weeks, holidays that override them, monthly support; split by article |
| `HomePurchase/` | home purchase agreement | earnest money, inspection and financing contingencies, who keeps the deposit |
| `PromissoryNote/` | personal loan | instalments, interest, late fees, acceleration, order of application of payments |
| `Guaranty/` | co-signer's guaranty | a duty that arises on another's default; a cap; release when the loan is changed |
| `BillOfSale/` | vehicle bill of sale | as-is with an exception for a concealed defect; title warranty; delivery of the title |
| `Employment/` | employment agreement | at-will termination, notice, severance against a release, obligations that survive |
| `NonDisclosure/` | mutual non-disclosure agreement | a prohibition with four exceptions; a three-year term; return on request |
| `ReturnPolicy/` | shop return and warranty policy | return windows, store credit, repair or refund |
| `Settlement/` | settlement and mutual release | a release that takes effect only on payment; dismissal; confidentiality |
| `RentersInsurance/` | renters insurance policy | coverage with exclusions; a disputed cause settled by an adjuster; deductible and limit |
| `Roommates/` | roommate agreement | rent shares, joint liability, leaving with notice and a replacement all approve |
| `HomeownersAssociation/` | association rules | assessments, fines only after a hearing, approval deemed by silence, amendment; split by article |
| `OperatingAgreement/` | LLC operating agreement | weighted votes, pro-rata distributions, first refusal, withdrawal, amendment; split by article |
| `ClubBylaws/` | club bylaws | quorum, elections, removal, amendment, one clause that cannot be amended; split by article |

## Layout

A short agreement is one file and a `cases/` directory:

```
LastWill/
  will.md               the English; the authority
  will.charter          Document, declarations, Clause blocks
  cases/
    estate.charter      #require "../will.charter". then the people, the facts, the scenarios
```

A long agreement is split by the divisions of its own text, one file per article, numbered as
the document numbers them, with a root that requires them in order:

```
LivingTrust/
  trust.md
  trust.charter         Document, then #require of each article in document order
  1-creation.charter
  2-revocation.charter
  ...
  cases/
    family.charter      #require "../trust.charter".
```

An article file holds the declarations that article grounds, their `Clause` blocks, and
whatever those declarations need to compute. It `#require`s the articles it depends on, so it
can be checked alone.

A case file declares no acts, duties or rules. It names the people and things of one situation
(`Extend Fact person Identified by …`), sets the initial state, and holds `Scenario` blocks.

## Writing one

1. Write the English first, as numbered clauses under headings. Keep it to what a careful
   layperson would write: one or two pages.
2. Declare who and what the text talks about. Name each role with a `Placeholder`
   (`Placeholder grantor For person`), so acts read `Actor grantor Recipient grantee` and
   conditions can leave arguments implicit (`signed()`, `lien()`).
3. For each sentence that says what someone may, must or cannot do, write the act, duty or
   power it means. Say `Valid when` where the text says something "has no effect" or "is void";
   say `Holds when` where it says something is permitted or a breach.
4. Quote the text in `Clause` blocks, one per numbered clause, splitting it into spans and
   naming the rules each normative span means.
5. Run `tools/approve-clauses FILE.charter` to stamp each clause's approval, once you have read
   each span against the rule it names.
6. Write cases: for each sentence, a scenario in which it makes a difference.

## Checking

```sh
B=.lake/build/bin/charter
$B check --require-provenance --deny-warnings Examples/Deed/deed.charter
$B test  --deny-warnings Examples/Deed/cases/lot7.charter
```

`check` on the root verifies that every clause occurs verbatim in the English, that every
normative span names a rule, and that every act, duty and immunity is named by some span.
`test` on a case runs its scenarios; every `?` line is a claim that must hold.

`tools/examples-check` runs both over every example in this layout, and the battery runs it.

`charter fmt` preserves comments, blank lines and line breaks while normalizing spacing.

What these examples cost to write, and what would make them easier, is in
`docs/plans/2026-11-07-example-friction/`.
