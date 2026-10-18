import Charter.Core.Views

/-!
# Charter.Core.Explain — structured answers, not booleans

"Can my host terminate my execution right now?" is answered by
`explain`: for a proposed event at the institutional state reached by a
history, which duties it would breach (with their source clauses), which
exceptions would make it lawful, which powers it would validly exercise,
what facts it would establish, and — if it is a breach — which procedure
establishes the breach and what remedies that would bring into force.

Every line of the answer is read off the normative AST; nothing is
authored here.
-/

namespace Charter

variable {σ : Sig}

structure BreachExplanation (σ : Sig) where
  duty          : Duty σ
  lawfulIfPower : List String          -- would be lawful as a valid exercise of one of these
  lawfulIfCond  : Option (Cond σ)      -- would be lawful if this held
  procedure     : Option String        -- the power whose exercise establishes the breach
  remedies      : List σ.Fact

structure Explanation (σ : Sig) where
  event       : Event σ
  state       : LegalState σ
  breaches    : List (BreachExplanation σ)
  exercises   : List (Power σ)
  establishes : List σ.Fact
  /-- Powers this actor holds with this trigger whose validity condition
  currently fails: "you could do this if ..." -/
  blockedPowers : List (Power σ)

def explain (L : Law σ) (tr : Trace σ) (e : Event σ) : Explanation σ :=
  let ls := stateAfter L tr
  let ex := validExercises L ls e
  let br := (L.duties.filter (breaches L ls e)).map fun d =>
    { duty := d
      lawfulIfPower := d.unlessPower
      lawfulIfCond := match d.unlessCond with | .ff => none | c => some c
      procedure := d.breachEstablishedBy
      remedies := d.remedies }
  let blocked := L.powers.filter fun p =>
    p.holder.mem e.who ls e.t && p.trigger.matchesAct e &&
    (!p.valid.eval ls e.t || defeatedByImmunity L ls e.t p.id)
  { event := e, state := ls, breaches := br, exercises := ex
    establishes := (stateAfter L (tr ++ [e])).filter (fun f => f.2.1 == e.t) |>.map (·.1)
    blockedPowers := blocked }

variable [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]

def Explanation.render (x : Explanation σ) : String :=
  let verdict :=
    if x.breaches.isEmpty then "LAWFUL: no duty in force is breached." else
      s!"UNLAWFUL: breaches {x.breaches.map (·.duty.id)}."
  let effect :=
    if x.exercises.isEmpty then "No institutional effect: no power is validly exercised."
    else s!"Valid exercise of {x.exercises.map (·.id)}; establishes {rs x.establishes}."
  let brs := x.breaches.map fun b =>
    let how := (if b.lawfulIfPower.isEmpty then [] else [s!"as a valid exercise of {b.lawfulIfPower}"]) ++
               (match b.lawfulIfCond with | none => [] | some c => [s!"if {c.render}"])
    let howS := if how.isEmpty then "no exception applies" else String.intercalate ", or " how
    let proc := match b.procedure with
      | none => "no institutional consequence is specified"
      | some p => s!"breach is established by {p}, which brings into force {rs b.remedies}"
    s!"  {b.duty.id} [{b.duty.source.clause}] — {b.duty.bearer.render} must not do this toward {b.duty.beneficiary.render} while {b.duty.active.render}.\n    Lawful only {howS}.\n    If it occurs: {proc}.\n    Source: {rs b.duty.source.text}"
  let blocked := x.blockedPowers.map fun p =>
    if p.valid.eval x.state x.event.t then
      s!"  {p.id} [{p.source.clause}]: you hold this power and its conditions are met, but it is defeated by an immunity in force."
    else
      s!"  {p.id} [{p.source.clause}]: you hold this power, but it is valid only when {p.valid.render} — not now."
  s!"Event: {rs x.event.who} {rs x.event.act} at t={x.event.t}\n{verdict}\n{effect}\n" ++
  (if brs.isEmpty then "" else "Governing duties:\n" ++ String.intercalate "\n" brs ++ "\n") ++
  (if blocked.isEmpty then "" else "Powers not currently valid:\n" ++ String.intercalate "\n" blocked ++ "\n")

/-- Step-by-step evaluation of a history: after each event, what it was. -/
def evalTrace (L : Law σ) (tr : Trace σ) : String :=
  let rows := (tr.zipIdx).map fun (e, i) =>
    let ls := stateBefore L tr i
    let br := (L.duties.filter (breaches L ls e)).map (·.id)
    let ex := (validExercises L ls e).map (·.id)
    let added := (stateBefore L tr (i+1)).filter (fun f => f.2.1 == e.t) |>.map (·.1)
    s!"[{i}] t={e.t} {rs e.who} {rs e.act}: " ++
    (if br.isEmpty then "lawful" else s!"BREACH {br}") ++
    (if ex.isEmpty then "; no effect" else s!"; exercises {ex} → +{rs added}")
  let final := (stateAfter L tr).map (·.1)
  String.intercalate "\n" rows ++ s!"\nViolation record: {violations L tr}\nInstitutional state: {rs final}"

namespace Core

export Charter (
  BreachExplanation
  Explanation
  explain
  evalTrace
)

namespace Explanation
export Charter.Explanation (render)
end Explanation

end Core

end Charter
