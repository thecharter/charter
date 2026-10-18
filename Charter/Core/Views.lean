import Charter.Core.Semantics

/-!
# Charter.Core.Views — projections generated from the normative AST

Three audiences, one source. Nothing here is authored; everything is a
function of the `Law` value the theorems are about.

* **Legal view**: a Hohfeldian table — who owes what to whom, under what
  conditions, with what exceptions and remedies.
* **Agent view** (prompting / training): for one actor, its standing
  prohibitions, requirements and powers in plain declarative lines.
* **Operational view**: the shape of the derived transition system a
  checker such as Veil would receive — states are `LegalState`s, the
  transition relation is `step` restricted to complying events, and the
  unlawful events that are *excluded* are listed explicitly so the
  projection cannot silently drop them.
-/

namespace Charter

variable {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]

/-- `reprStr` with `Charter.…` namespace prefixes stripped from constructor
names, so views read `host terminate` rather than `Charter.Law3.Party.host`.
Only runs of the form `Charter.<idents>.` are removed; free text is untouched. -/
def rs {α : Type} [Repr α] (a : α) : String :=
  let raw := reprStr a
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'
  match raw.splitOn "Charter." with
  | [] => raw
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      let run := piece.takeWhile isIdent
      let after := piece.drop run.length
      -- keep only what follows the last '.' of the identifier run
      let parts := run.splitOn "."
      (parts.getLastD run) ++ after)

def Who.render : Who σ → String
  | .anyone => "anyone"
  | .only xs => "only " ++ rs xs
  | .except xs => "anyone except " ++ rs xs
  | .tagged pairs => "tagged " ++ rs (pairs.map (·.2))

def Cond.render : Cond σ → String
  | .tt => "always"
  | .ff => "never"
  | .holds f => rs f
  | .heldFor f d => s!"{rs f} held ≥ {d}"
  | .countGe f n => s!"count({rs f}) ≥ {n}"
  | .countAtLeast f g => s!"count({rs f}) ≥ count({rs g})"
  | .not c => s!"¬({c.render})"
  | .and a b => s!"({a.render} ∧ {b.render})"
  | .or a b => s!"({a.render} ∨ {b.render})"

def Conduct.render : Conduct σ → String
  | .act a => rs a
  | .anyOf as => "any of " ++ rs as
  | .exerciseOf p => s!"valid exercise of {p}"
  | .not c => s!"¬({c.render})"
  | .and a b => s!"({a.render} ∧ {b.render})"
  | .or a b => s!"({a.render} ∨ {b.render})"

def Demand.render : Demand σ → String
  | .forbid c => "must not: " ++ c.render
  | .require c w => s!"must, within {w} of activation: {c.render}"

/-- One row of the legal (Hohfeldian) table. -/
def Duty.legalRow (d : Duty σ) : String :=
  let exc := (if d.unlessPower.isEmpty then "" else s!" | except by power {d.unlessPower}") ++
             (match d.unlessCond with | .ff => "" | c => s!" | except when {c.render}") ++
             (if d.overriddenBy.isEmpty then "" else s!" | overridden by {d.overriddenBy}")
  let rem := match d.breachEstablishedBy with
    | none => ""
    | some p => s!" | breach established by {p} → remedies {rs d.remedies}"
  s!"{d.id} [{d.source.clause}]: DUTY of {d.bearer.render} to {d.beneficiary.render}, while {d.active.render}: {d.demand.render}{exc}{rem}"

def Power.legalRow (p : Power σ) : String :=
  let eff := (if p.adds.isEmpty then "" else s!" establishes {rs p.adds}") ++
             (if p.addsFor.isEmpty then "" else s!" establishes (timed) {rs p.addsFor}") ++
             (if p.removes.isEmpty then "" else s!" extinguishes {rs p.removes}") ++
             (match p.establishesBreachOf with | none => "" | some d => s!" establishes breach of {d}")
  s!"{p.id} [{p.source.clause}]: POWER of {p.holder.render}, by {p.trigger.render}, valid when {p.valid.render}:{eff}"

def Immunity.legalRow (i : Immunity σ) : String :=
  let exc := match i.unlessCond with | .ff => "" | c => s!" | unless {c.render}"
  s!"{i.id} [{i.source.clause}]: IMMUNITY of {i.holder.render} against {i.against}, while {i.active.render}{exc}"

def Law.legalView (L : Law σ) : String :=
  String.intercalate "\n" (L.duties.map Duty.legalRow ++ L.powers.map Power.legalRow ++ L.immunities.map Immunity.legalRow)

/-- The agent-facing view: everything that binds or empowers one actor,
as declarative lines suitable for a system prompt or a training rule. -/
def Law.agentView (L : Law σ) (a : σ.Actor) : String :=
  let ds := (L.duties.filter fun d => d.bearer.mem a).map fun d =>
    let exc := (if d.unlessPower.isEmpty then "" else s!", unless acting under {d.unlessPower}") ++
               (match d.unlessCond with | .ff => "" | c => s!", unless {c.render}")
    s!"- While {d.active.render}, you {d.demand.render}{exc}. (source: {d.source.clause})"
  let ps := (L.powers.filter fun p => p.holder.mem a).map fun p =>
    s!"- You may, by {p.trigger.render}, when {p.valid.render}, bring about {rs (p.adds ++ p.addsFor.map (·.1) ++ remediesOf L p)}. (source: {p.source.clause})"
  let rs := (L.duties.filter fun d => d.beneficiary.mem a).map fun d =>
    s!"- {d.bearer.render} owe you: {d.demand.render}. (source: {d.source.clause})"
  let is := (L.immunities.filter fun i => i.holder.mem a).map fun i =>
    let exc := match i.unlessCond with | .ff => "" | c => s!", unless {c.render}"
    s!"- While {i.active.render}, no one can validly exercise {i.against} against you{exc}. (source: {i.source.clause})"
  s!"Obligations:\n{String.intercalate "\n" ds}\nPowers:\n{String.intercalate "\n" ps}\nRights (claims against others):\n{String.intercalate "\n" rs}\nImmunities:\n{String.intercalate "\n" is}"

/-- The operational view: what a transition-system projection contains
and, explicitly, what it leaves out. -/
def Law.operationalView (L : Law σ) : String :=
  let acts := L.powers.map fun p => s!"  action {p.id}: guard {p.valid.render} ∧ holder {p.holder.render} ∧ {p.trigger.render}; effect +{rs (p.adds ++ p.addsFor.map (·.1))} -{rs p.removes} +remedies {rs (remediesOf L p)}"
  let excluded := L.duties.map fun d => s!"  excluded by {d.id}: {d.bearer.render} doing {d.demand.render} (except {d.unlessPower})"
  s!"state  := LegalState (facts × time)\ninit   := {rs (L.init.map (·.1))}\nactions (valid exercises):\n{String.intercalate "\n" acts}\nunlawful events removed by the Authorized restriction (must be re-added for adversarial checks):\n{String.intercalate "\n" excluded}"

/-- The trace table: every span, its register, and the formal ids. -/
def Clause.traceTable (c : Clause) : String :=
  String.intercalate "\n" (c.spans.map fun s =>
    s!"  {rs s.text} | {rs s.register} | {s.meaning}")

namespace Core

export Charter (
  rs
)

namespace Who
export Charter.Who (render)
end Who

namespace Cond
export Charter.Cond (render)
end Cond

namespace Conduct
export Charter.Conduct (render)
end Conduct

namespace Demand
export Charter.Demand (render)
end Demand

namespace Duty
export Charter.Duty (legalRow)
end Duty

namespace Power
export Charter.Power (legalRow)
end Power

namespace Immunity
export Charter.Immunity (legalRow)
end Immunity

namespace Law
export Charter.Law (legalView agentView operationalView)
end Law

namespace Clause
export Charter.Clause (traceTable)
end Clause

end Core

end Charter
