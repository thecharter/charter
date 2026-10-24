# lib/ — the standard library

The eight institutional patterns of `src/Charter/Modules/` as Charter modules (D8, spec
015.5). A program includes one with `#require "lib/<name>.eflint"` and instantiates it with
`Use <module>(<type arguments>) As <prefix>`; every name the module declares then appears as
`<prefix>-<name>`. Each module's header says what its parameters are and where it deviates
from the Lean original. The files are `.eflint` until the `.charter` extension moves to this
grammar (spec 011.10).

| Module | Pattern | Parameters |
|---|---|---|
| `entity_group` | per-member ledgers, consent-gated amendment, capped subsidy, targeted forfeiture | `group, member, stakeholder, amount` |
| `oracle_feed` | contestable valuation feed, atomic settlement waterfall | `oracle, party, asset` |
| `circuit_breaker` | staked preliminary freeze, probable cause, bounded suspension, wrongful-pause damages | `initiator, member, panel` |
| `residual_ledger` | founding ledger retirement, royalty after retirement, sunset, loan principal, single recognition, buyout | `steward, member, period` |
| `collateral_pool` | harm-scaled commitments with decaying exposure, long-tail reserve, mutual forfeit, frivolous-claim stake | `entity, action, claimant, operator` |
| `exit_and_voice` | unilateral exit with cooling-off, stay, tolling and censorship default; rate-limited voice; redaction | `member, operator, panel` |
| `sortition_court` | validated sortition panels, supermajority, bounded appeals, finality, consolidation, fee-pool waterfall | `arbiter, party, dispute, registrar` |
| `attested_lease` | single-authority leases, quarantined restores, fenced migration, revocation and erasure | `instance, operator, member` |

## Conventions

- **Inputs are facts** (D10). What the world supplies, such as a valuation, an inflow, a
  bond, a draw, a damages finding, is a `Fact` or `Function` the program asserts; the acts
  act on it by name (`settle-inflow Actor oracle Related to asset`). Where a module keeps one
  value per key it is a `Function` (two components) or a `Var`.
- **Quantities are `Int` facts.** A binder over a type with an `Int` component ranges over
  what holds (spec 004.7), so `Sum(Foreach basis: basis.int)` is the ledger total and costs
  nothing. A binder over a type whose components are all enumerable ranges over the whole
  domain; write the application form (`frozen(member, initiator)`) or say the instance holds
  (`filer && …`).
- **An amount an act names is `Related to int`.** The act's lawfulness is judged for the
  instance performed or asked about (D15, 005.5), so nothing is enumerated. A binder over
  such an act sees only its assigned instances (CHR025); a module that needs "every
  transfer so far" records them with an effect. A test that explores such an act names the
  candidates with `//! explore-domain: int = 0..N` (013.2); without one the act is reported
  unexplored and the exploration is not a pass.
- **Minimum and maximum are conditional derivations.** `min(a, b)` is two `Derived from`
  clauses with `When a <= b` and `When b < a`; `Min(Foreach int'': …)` ranges over held `int`
  instances and so is empty.
- **Durations add and scale.** `Duration + Duration`, `Duration * Int`, and `Duration / Int`
  are durations (D16); a window the English scales is written `base * factor`.
- **Every property is an `Invariant`** named for the Lean theorem it replaces, checked after
  every phrase and explored from every end state by `charter test`. Frame properties of
  acts are not state invariants and wait for `prove` (spec 013.4).
- **Stamps are per derivation** (009.3). A derived fact is stamped at the phrase that first
  derived it, so a program that reads `Held(f) For d` must observe the clock when `f` becomes
  true.
