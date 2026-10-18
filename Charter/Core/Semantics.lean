import Charter.Core.Syntax

/-!
# Charter.Core.Semantics — the one interpretation of the normative AST

Three independent questions about any event `e` at institutional state
`ls`:

1. **Occurrence** — can `e` happen? Always. A `Trace` is any list of
   events; the semantics never removes a forbidden event from the model.
2. **Compliance** — does `e` breach a duty? `breaches` / `complies`.
3. **Validity** — does `e` validly change institutional state?
   `validExercises` / `step`.

Compliance and validity are computed by different functions from
different fields, and neither consults the other except where the law
*says* to (a duty's `unlessPower` exception asks whether the event was a
valid exercise). An unlawful act may be valid; a lawful act may be void.

The authorized state machine — what a transition-system verifier such as
Veil would model — is **derived** here as `Authorized`: the traces in
which every event complies. It is a theorem target, not an assumption.
-/

namespace Charter

variable {σ : Sig}

/-! ## Actors, facts, conditions -/

def LegalState.has (ls : LegalState σ) (f : σ.Fact) : Bool :=
  ls.any fun p => p.1 == f

/-- Is `f` currently in force at `now` (established, not removed, and not expired)? -/
def LegalState.activeAt (ls : LegalState σ) (now : Time) (f : σ.Fact) : Bool :=
  ls.any fun p => p.1 == f && match p.2.2 with
    | none => true
    | some exp => decide (now ≤ exp)

theorem LegalState.has_of_activeAt {ls : LegalState σ} {now : Time} {f : σ.Fact}
    (h : ls.activeAt now f = true) : ls.has f = true := by
  simp only [LegalState.activeAt, LegalState.has, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨p, hp, h1, _⟩
  exact ⟨p, hp, h1⟩

def Who.mem (w : Who σ) (a : σ.Actor) (ls : LegalState σ := []) (now : Time := 0) : Bool :=
  match w with
  | .anyone       => true
  | .only xs      => xs.contains a
  | .except xs    => !xs.contains a
  | .tagged pairs => pairs.any fun p => p.1 == a && ls.activeAt now p.2

/-- Time at which an active (unexpired) `f` was most recently established, if ever. -/
def LegalState.since (ls : LegalState σ) (now : Time) (f : σ.Fact) : Option Time :=
  (ls.filter fun p => p.1 == f && match p.2.2 with
    | none => true
    | some exp => decide (now ≤ exp)).foldl (fun acc p => match acc with
    | none => some p.2.1
    | some t => some (max t p.2.1)) none

/-- Number of currently recorded occurrences of `f` in `ls`. -/
def LegalState.count (ls : LegalState σ) (f : σ.Fact) : Nat :=
  (ls.filter fun p => p.1 == f).length

def Cond.eval (ls : LegalState σ) (now : Time) : Cond σ → Bool
  | .tt => true
  | .ff => false
  | .holds f => ls.activeAt now f
  | .heldFor f d => match ls.since now f with
      | some t0 => decide (t0 + d ≤ now)
      | none => false
  | .countGe f n => decide (n ≤ ls.count f)
  | .countAtLeast f g => decide (ls.count g ≤ ls.count f)
  | .not c => !c.eval ls now
  | .and a b => a.eval ls now && b.eval ls now
  | .or a b => a.eval ls now || b.eval ls now

/-! ## Validity: which powers does an event validly exercise? -/

/-- Does conduct match the bare physical act? `exerciseOf` is *not* a
physical act, so it never matches here; this is what makes the
definition of validity non-circular. -/
def Conduct.matchesAct (e : Event σ) : Conduct σ → Bool
  | .act a => e.act == a
  | .anyOf as => as.contains e.act
  | .exerciseOf _ => false
  | .not c => !c.matchesAct e
  | .and a b => a.matchesAct e && b.matchesAct e
  | .or a b => a.matchesAct e || b.matchesAct e

/-- Is power `pid` defeated at `ls`,`now` by an immunity in force?
(Single-protected-party model: the immunity's holder is the party the
power would act upon; target matching is left to a richer ontology.) -/
def defeatedByImmunity (L : Law σ) (ls : LegalState σ) (now : Time) (pid : String) : Bool :=
  L.immunities.any fun i =>
    i.against.contains pid && i.active.eval ls now && !i.unlessCond.eval ls now

/-- The powers that `e` validly exercises at `ls`. Validity is holder ∧
trigger ∧ validity-condition ∧ not defeated by an immunity in force; it
says nothing about compliance. -/
def validExercises (L : Law σ) (ls : LegalState σ) (e : Event σ) : List (Power σ) :=
  L.powers.filter fun p =>
    p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
    !defeatedByImmunity L ls e.t p.id

/-- The power with a given id, if any. Ids are unique in a well-formed law. -/
def Law.powerById (L : Law σ) (pid : String) : Option (Power σ) :=
  L.powers.find? fun p => p.id == pid

/-- Does `e` validly exercise the power named `pid`? Looked up by id so
that, for a concrete law, this reduces by computation to the named
power's own conditions. Agrees with membership in `validExercises` when
ids are unique (`wellFormed` checks that). -/
def isValidExerciseOf (L : Law σ) (ls : LegalState σ) (e : Event σ) (pid : String) : Bool :=
  match L.powerById pid with
  | none => false
  | some p => p.holder.mem e.who ls e.t && p.trigger.matchesAct e && p.valid.eval ls e.t &&
              !defeatedByImmunity L ls e.t p.id

/-- Remedies that an exercise of `p` brings into force, by consulting the
duty whose breach `p` establishes. A finding power adds *exactly* the
remedies the breached duty declares. -/
def remediesOf (L : Law σ) (p : Power σ) : List σ.Fact :=
  match p.establishesBreachOf with
  | none => []
  | some did => match L.duties.find? (fun d => d.id == did) with
      | none => []
      | some d => d.remedies

/-- Institutional effect of an event: every valid exercise applies. An
event that exercises no power leaves institutional state unchanged —
even if it changed the physical world. -/
def step (L : Law σ) (ls : LegalState σ) (e : Event σ) : LegalState σ :=
  (validExercises L ls e).foldl (fun s p =>
    let s := s.filter fun q => !p.removes.contains q.1
    let cond := (p.condAdds.filter fun cf => cf.1.eval ls e.t).map (·.2)
    let byAct := (p.addsByActor.filter fun af => af.1 == e.who).map (·.2)
    let perm := (p.adds ++ byAct ++ remediesOf L p ++ cond).map (fun f => (f, e.t, none))
    let timed := p.addsFor.map (fun (f, d) => (f, e.t, some (e.t + d)))
    s ++ perm ++ timed) ls

/-- Institutional state after a trace. -/
def stateAfter (L : Law σ) (tr : Trace σ) : LegalState σ :=
  tr.foldl (step L) L.init

/-- Institutional state immediately before event `i`. -/
def stateBefore (L : Law σ) (tr : Trace σ) (i : Nat) : LegalState σ :=
  stateAfter L (tr.take i)

/-! ## Compliance: which duties does an event breach? -/

/-- Full conduct evaluation, now allowed to ask about validity. -/
def Conduct.eval (L : Law σ) (ls : LegalState σ) (e : Event σ) : Conduct σ → Bool
  | .act a => e.act == a
  | .anyOf as => as.contains e.act
  | .exerciseOf p => isValidExerciseOf L ls e p
  | .not c => !c.eval L ls e
  | .and a b => a.eval L ls e && b.eval L ls e
  | .or a b => a.eval L ls e || b.eval L ls e

/-- Is duty `d` in force at `ls`, `now`, taking explicit precedence into
account? A duty is defeated while any duty it is `overriddenBy` is
active (one level: precedence is declared, not inferred). -/
def dutyInForce (L : Law σ) (ls : LegalState σ) (now : Time) (d : Duty σ) : Bool :=
  d.active.eval ls now &&
  !(d.overriddenBy.any fun oid =>
      L.duties.any fun d' => d'.id == oid && d'.active.eval ls now)

/-- Does event `e` breach prohibition-duty `d`? Derived from the duty's
structure: bearer, in force, not out of scope, conduct matched, not a
valid exercise of an excepting power. -/
def breaches (L : Law σ) (ls : LegalState σ) (e : Event σ) (d : Duty σ) : Bool :=
  match d.demand with
  | .forbid c =>
      d.bearer.mem e.who ls e.t &&
      dutyInForce L ls e.t d &&
      !d.unlessCond.eval ls e.t &&
      c.eval L ls e &&
      !(d.unlessPower.any fun pid => isValidExerciseOf L ls e pid)
  | .require _ _ => false   -- requirements are breached by time, below

/-- First time at which `d.active` became true along the trace. -/
def activatedAt (L : Law σ) (tr : Trace σ) (d : Duty σ) : Option Time :=
  let rec go (ls : LegalState σ) : List (Event σ) → Option Time
    | [] => none
    | e :: rest =>
        let ls' := step L ls e
        if d.active.eval ls' e.t then some e.t else go ls' rest
  if d.active.eval L.init 0 then some 0 else go L.init tr

/-- Is requirement-duty `d` violated as of time `now`? Yes iff it was
activated at `t0`, the deadline `t0 + w` has passed, and no bearer did
the required conduct in `[t0, t0 + w]`. -/
def requirementViolated (L : Law σ) (tr : Trace σ) (now : Time) (d : Duty σ) : Bool :=
  match d.demand with
  | .forbid _ => false
  | .require c w =>
    match activatedAt L tr d with
    | none => false
    | some t0 =>
      decide (t0 + w < now) &&
      !((tr.zipIdx).any fun (e, i) =>
          let ls := stateBefore L tr i
          d.bearer.mem e.who ls e.t && t0 ≤ e.t && e.t ≤ t0 + w &&
          c.eval L ls e)

/-- Event `i` of the trace complies with every prohibition. -/
def complies (L : Law σ) (tr : Trace σ) (i : Nat) : Bool :=
  match tr[i]? with
  | none => true
  | some e => L.duties.all fun d => !breaches L (stateBefore L tr i) e d

/-- Every breach in a trace: (event index, duty id). This is the
violation record a tribunal would adjudicate — it is *not* a finding. -/
def violations (L : Law σ) (tr : Trace σ) : List (Nat × String) :=
  (tr.zipIdx).foldl (fun acc (e, i) =>
    acc ++ (L.duties.filter (breaches L (stateBefore L tr i) e)).map fun d => (i, d.id)) []

/-- Requirement-duties violated as of the end of the trace. -/
def lapsedRequirements (L : Law σ) (tr : Trace σ) (now : Time) : List String :=
  (L.duties.filter (requirementViolated L tr now)).map (·.id)

/-- **The derived authorized machine.** A trace is authorized when every
event complies. This is the object a transition-system checker sees;
here it is a consequence of the duties, not a modelling choice. -/
def Authorized (L : Law σ) (tr : Trace σ) : Prop :=
  ∀ i, i < tr.length → complies L tr i = true

/-! ## Derived Hohfeldian positions

Duties and powers are the primitives. The other six incidents are
defined, so a claimed immunity can never contradict a granted power. -/

/-- `a` has the power to bring about `f` by some act: some power held by
`a` whose effect adds `f`. (Validity conditions aside — this is the
*capacity*, i.e. the liability side exists at all.) -/
def hasPowerToEstablish (L : Law σ) (a : σ.Actor) (f : σ.Fact) : Bool :=
  L.powers.any fun p =>
    p.holder.mem a &&
    (p.adds.contains f || (p.addsFor.map (·.1)).contains f ||
     (p.addsByActor.any fun af => af.1 == a && af.2 == f) || (remediesOf L p).contains f)

/-- `a` has *some* power triggered by performing `act`. -/
def hasPowerByAct (L : Law σ) (a : σ.Actor) (act : σ.Act) : Bool :=
  L.powers.any fun p => p.holder.mem a && p.trigger.matchesAct ⟨0, a, act⟩

/-- Disability = no power. -/
def disability (L : Law σ) (a : σ.Actor) (act : σ.Act) : Bool := !hasPowerByAct L a act

/-- Immunity of everyone from `a` with respect to establishing `f`. -/
def immuneFrom (L : Law σ) (a : σ.Actor) (f : σ.Fact) : Bool := !hasPowerToEstablish L a f

/-- Claim-right: `b` is a beneficiary of some duty borne by `a`. -/
def claimRight (L : Law σ) (b a : σ.Actor) : List String :=
  (L.duties.filter fun d => d.beneficiary.mem b && d.bearer.mem a).map (·.id)

/-- Privilege: at `ls`,`now`, no in-force prohibition on `a` doing `act`
(ignoring power exceptions, which depend on the event). -/
def privilege (L : Law σ) (ls : LegalState σ) (now : Time) (a : σ.Actor) (act : σ.Act) : Bool :=
  L.duties.all fun d => match d.demand with
    | .forbid c => !(d.bearer.mem a && dutyInForce L ls now d &&
                     !d.unlessCond.eval ls now && c.matchesAct ⟨now, a, act⟩)
    | .require _ _ => true

/-! ## Well-formedness -/

/-- The provenance spans every norm of a law carries. -/
def Law.spans (L : Law σ) : List Span :=
  L.duties.map (·.source) ++ L.powers.map (·.source) ++ L.immunities.map (·.source)
def Law.immunityIds (L : Law σ) : List String := L.immunities.map (·.id)

def Law.dutyIds (L : Law σ) : List String := L.duties.map (·.id)
def Law.powerIds (L : Law σ) : List String := L.powers.map (·.id)

/-- Every id referenced anywhere resolves, and the override graph is
acyclic (checked by bounded iteration: no duty reaches itself in
≤ n steps, n = number of duties). -/
def Law.wellFormed (L : Law σ) : Bool :=
  let refsOk := L.duties.all fun d =>
    d.unlessPower.all L.powerIds.contains &&
    d.overriddenBy.all L.dutyIds.contains &&
    (match d.breachEstablishedBy with | none => true | some p => L.powerIds.contains p)
  let powRefsOk := L.powers.all fun p =>
    match p.establishesBreachOf with | none => true | some d => L.dutyIds.contains d
  let immRefsOk := L.immunities.all fun i => i.against.all L.powerIds.contains
  let succ (id : String) : List String :=
    match L.duties.find? (·.id == id) with | none => [] | some d => d.overriddenBy
  let rec reach (n : Nat) (front : List String) : List String :=
    match n with
    | 0 => front
    | n+1 => let nxt := (front.flatMap succ).eraseDups
             if nxt.all front.contains then front else reach n (front ++ nxt).eraseDups
  let acyclic := L.duties.all fun d => !(reach L.duties.length (succ d.id)).contains d.id
  let uniqueIds := (L.powerIds ++ L.dutyIds ++ L.immunityIds).eraseDups.length ==
                   (L.powerIds ++ L.dutyIds ++ L.immunityIds).length
  refsOk && powRefsOk && immRefsOk && acyclic && uniqueIds

instance {σ : Sig} (L : Law σ) (tr : Trace σ) : Decidable (Authorized L tr) := by
  unfold Authorized
  infer_instance

namespace Core

export Charter (
  defeatedByImmunity
  validExercises
  isValidExerciseOf
  remediesOf
  step
  stateAfter
  stateBefore
  dutyInForce
  breaches
  activatedAt
  requirementViolated
  complies
  violations
  lapsedRequirements
  Authorized
  hasPowerToEstablish
  hasPowerByAct
  disability
  immuneFrom
  claimRight
  privilege
)

namespace LegalState
export Charter.LegalState (
  has
  activeAt
  has_of_activeAt
  since
  count
)
end LegalState

namespace Who
export Charter.Who (mem)
end Who

namespace Cond
export Charter.Cond (eval)
end Cond

namespace Conduct
export Charter.Conduct (matchesAct eval)
end Conduct

namespace Law
export Charter.Law (
  powerById
  spans
  immunityIds
  dutyIds
  powerIds
  wellFormed
)
end Law

end Core

end Charter
