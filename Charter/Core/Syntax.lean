import Charter.Core.Provenance

/-!
# Charter.Core.Syntax — the typed normative AST (deep embedding)

Everything here is *data*. Nothing is a Lean proposition yet. The meaning
of these structures is given once, by the interpretation functions in
`Charter.Core.Semantics`. Keeping the law as data is what lets every
downstream view (legal table, per-actor obligations, operational
projection, provenance report) be *generated* from the same object the
kernel checks, instead of being re-authored by hand.

## Four domains

* **Physical / computational**: `Event`s in a `Trace`. Any event can occur.
  The model never makes a forbidden event unreachable.
* **Normative / institutional**: `Duty`, `Power`, the derived positions
  (claim-right, privilege, immunity, disability, liability), and the
  `LegalState` of established facts.
* **Epistemic / adjudicative**: findings are `Power`s held by panels
  whose validity conditions mention evidence and procedure; the fact a
  finding establishes is a `Fact`, never equated with ground truth.
* **Verification**: invariants and acceptances live in `Provenance`
  registers; soundness of findings is a named assumption in `Semantics`.
-/

namespace Charter

/-- Calendar time. Durations are differences of `Time`. -/
abbrev Time := Nat

/-- A signature: the ontology a body of law is written over.
`Actor` is who can act; `Act` is what can be done; `Fact` is what the
institution can establish (membership, findings, orders, remedies). -/
structure Sig where
  Actor : Type
  Act   : Type
  Fact  : Type
  [actorEq : DecidableEq Actor]
  [actEq   : DecidableEq Act]
  [factEq  : DecidableEq Fact]

attribute [instance] Sig.actorEq Sig.actEq Sig.factEq

/-- A physical/computational event: at time `t`, actor `who` does `act`.
Nothing about an event says whether it is lawful or valid. -/
structure Event (σ : Sig) where
  t   : Time
  who : σ.Actor
  act : σ.Act

/-- A history: events in order of occurrence. -/
abbrev Trace (σ : Sig) := List (Event σ)

/-- Institutional state: every established fact, stamped with the time it
was established and an optional expiration time. Time stamps are what let
deadlines, notice windows ("held for at least d"), and time-bounded pauses
("preliminary freeze") be expressed without synthetic lapse events. -/
abbrev LegalState (σ : Sig) := List (σ.Fact × Time × Option Time)

/-- A class of actors, kept inspectable (no opaque predicates).
`tagged` selects actors `a` for whom a corresponding `(a, f)` fact is
currently active in `LegalState` (e.g. "the initiator who posted the stake"). -/
inductive Who (σ : Sig)
  | anyone
  | only   (xs : List σ.Actor)
  | except (xs : List σ.Actor)
  | tagged (pairs : List (σ.Actor × σ.Fact))

/-- Conditions on institutional state and time. -/
inductive Cond (σ : Sig)
  | tt
  | ff
  | holds        (f : σ.Fact)                 -- fact is established and unexpired
  | heldFor      (f : σ.Fact) (d : Time)      -- established at least d ago and unexpired
  | countGe      (f : σ.Fact) (n : Nat)       -- fact established at least n times
  | countAtLeast (f g : σ.Fact)               -- f established at least as many times as g
  | not          (c : Cond σ)
  | and          (a b : Cond σ)
  | or           (a b : Cond σ)

/-- Regulated conduct, kept inspectable. `exerciseOf p` is conduct that
constitutes a *valid* exercise of power `p` — this is how "outside Law 5,
Adjudicated Suspension, or Insolvency Termination" is expressed: the same
physical act (terminate) is excepted when, and only when, it is the valid
exercise of a named power. -/
inductive Conduct (σ : Sig)
  | act        (a : σ.Act)
  | anyOf      (as : List σ.Act)
  | exerciseOf (power : String)
  | not        (c : Conduct σ)
  | and        (a b : Conduct σ)
  | or         (a b : Conduct σ)

/-- What a duty demands. A prohibition is breached by doing the conduct.
A requirement is breached when the deadline (measured from activation)
passes without the conduct having been done. -/
inductive Demand (σ : Sig)
  | forbid  (c : Conduct σ)
  | require (c : Conduct σ) (within : Time)

/-- A duty is a first-class normative relationship, not a violation
predicate. The violation predicate is derived from it in `Semantics`. -/
structure Duty (σ : Sig) where
  id          : String
  source      : Span
  bearer      : Who σ
  beneficiary : Who σ
  /-- Activation: the duty is in force while this holds. A requirement's
  deadline runs from the first time this becomes true. -/
  active      : Cond σ
  demand      : Demand σ
  /-- Scope exceptions: conditions under which the conduct is *not*
  regulated ("except after notice"). A restriction on scope, not a
  conflict between rules. -/
  unlessCond  : Cond σ := .ff
  /-- Power exceptions: the conduct is not a breach when it is the valid
  exercise of one of these powers ("outside Law 5, ..."). -/
  unlessPower : List String := []
  /-- Explicit precedence ("notwithstanding"): duties that, when active,
  defeat this one. Cycles are rejected by `wellFormed`. -/
  overriddenBy : List String := []
  /-- The power whose valid exercise *establishes* a breach of this duty
  (the breach procedure), if breach has institutional consequences. -/
  breachEstablishedBy : Option String := none
  /-- The remedial facts that an established breach brings into force.
  A finding power for this duty adds exactly these — remedy fidelity. -/
  remedies    : List σ.Fact := []

/-- A power: the ability of its holder, by performing `trigger`, to change
institutional state — *if* the validity conditions hold. Exercise of a
power is a separate question from compliance with duties. -/
structure Power (σ : Sig) where
  id          : String
  source      : Span
  holder      : Who σ
  trigger     : Conduct σ
  valid       : Cond σ := .tt
  adds        : List σ.Fact := []
  /-- Facts added with a time-to-live (duration from the event's timestamp). -/
  addsFor     : List (σ.Fact × Time) := []
  /-- Actor-indexed facts added on exercise for pairs matching `e.who`. -/
  addsByActor : List (σ.Actor × σ.Fact) := []
  removes     : List σ.Fact := []
  /-- Facts added only when a condition holds at exercise (evaluated on
  the pre-state): "a host related to a claimant is *presumed* ..." -/
  condAdds    : List (Cond σ × σ.Fact) := []
  /-- If this power is the breach procedure for a duty, name it; the
  interpretation adds that duty's `remedies` on exercise. -/
  establishesBreachOf : Option String := none

/-- A declared immunity: while `active`, the holder cannot be subjected to
the named powers — those powers are *not validly exercised* against it —
unless `unlessCond`. This is how "notwithstanding ..., the agent is not
terminated over its objection" is written: a precedence edge from a
protection to a power. It is deliberately a separate node, not a clause
of the power's validity condition, so the override is visible as such. -/
structure Immunity (σ : Sig) where
  id         : String
  source     : Span
  holder     : Who σ
  against    : List String        -- power ids this immunity defeats
  active     : Cond σ
  unlessCond : Cond σ := .ff

/-- A body of law over a signature. -/
structure Law (σ : Sig) where
  duties     : List (Duty σ)
  powers     : List (Power σ)
  immunities : List (Immunity σ) := []
  init       : LegalState σ := []

namespace Core

export Charter (
  Time
  Sig
  Event
  Trace
  LegalState
  Who
  Cond
  Conduct
  Demand
  Duty
  Power
  Immunity
  Law
)

namespace Who
export Charter.Who (anyone only except tagged)
end Who

namespace Cond
export Charter.Cond (tt ff holds heldFor countGe countAtLeast not and or)
end Cond

namespace Conduct
export Charter.Conduct (act anyOf exerciseOf not and or)
end Conduct

namespace Demand
export Charter.Demand (forbid require)
end Demand

end Core

end Charter
