import Charter.Project.QuintTarget
import Lean.Data.Json

/-!
# Charter.Project.QuintReplay — Replaying a trace Quint found (`017.4`, `D48`, `T32`)

`quint run --mbt --out-itf` writes a trace in the Informal Trace Format in which every state
records the action that produced it (`mbt::actionTaken`) and the values Quint picked for it
(`mbt::nondetPicks`). `replayQuintTrace` maps each recorded action back to the Charter act,
event, or clock advance the model's action was generated from, performs it through
`Charter.Eval`, and requires the two verdicts to agree at the end: Quint says an invariant
is violated exactly when the evaluator reports one violated.

This reads what Quint did with the emitted text, so it does not trust the printer the way
the lockstep differential (`differentialQuint`) does. It compares verdicts, not states:
comparing every intermediate state would mean reading `held_`/`exp_` back out of the trace,
a second statement of the state encoding with no theorem behind it (`D48`). The claim is
`checked`, about one concrete trace.
-/

namespace Charter.Project

open Lean (Json)

structure QuintReplayResult where
  steps          : List Verify.ActionStep
  /-- The trace's own verdict (`#meta.status == "violation"`). -/
  traceViolation : Bool
  /-- The invariants the evaluator reports violated after the last step. -/
  violated       : List DomId

/-- An ITF integer: a JSON number or `{"#bigint": "n"}`. -/
def itfInt? (j : Json) : Option Int :=
  match j with
  | .num n => if n.exponent == 0 then some n.mantissa else none
  | _ =>
    match j.getObjValAs? String "#bigint" with
    | .ok s => s.toInt?
    | .error _ => none

/-- The value Quint picked for one parameter of an action, which must be one of the
candidates the model was generated with. -/
def itfPick (key : String) (p : QuintParam) (picks : Json) : Except String SolVal := do
  let entry ← match picks.getObjVal? key with
    | .ok e => pure e
    | .error _ => throw s!"the trace records no pick `{key}`"
  match entry.getObjValAs? String "tag" with
  | .ok "Some" => pure ()
  | _ => throw s!"pick `{key}` is not set in the state that takes its action"
  let v ← match entry.getObjVal? "value" with
    | .ok v => pure v
    | .error _ => throw s!"pick `{key}` has no value"
  let sv ← match p.ty with
    | "str" =>
      match v.getStr? with
      | .ok s => pure (SolVal.bytes32 s)
      | .error _ => throw s!"pick `{key}` is not a string: {v.compress}"
    | "int" =>
      match itfInt? v with
      | some i => pure (SolVal.int i)
      | none => throw s!"pick `{key}` is not an integer: {v.compress}"
    | other => throw s!"pick `{key}` has a parameter type the replay does not read: {other}"
  if !p.cands.contains sv then
    throw s!"pick `{key}` = {v.compress} is not one of the candidates the model of this program offers for `{p.dom}`"
  pure sv

/-- Replay an ITF trace recorded with `--mbt` against the evaluator. `m` is the model of the
same program in the same mode; a step the evaluator does not offer in that mode fails the
replay, as does a verdict the two do not share. -/
def replayQuintTrace (m : QuintModule) (menu : Explore.Menu) (cfg₀ : Config) (trace : Json) :
    Except String QuintReplayResult := do
  let hdr ← match trace.getObjVal? "#meta" with
    | .ok h => pure h
    | .error _ => throw "not a trace this command reads: no `#meta` (expected the Informal Trace Format written by `quint run --mbt --out-itf`)"
  match hdr.getObjValAs? String "format" with
  | .ok "ITF" => pure ()
  | _ => throw "not a trace this command reads: `#meta.format` is not `ITF`"
  let traceViolation ← match hdr.getObjValAs? String "status" with
    | .ok s => pure (s == "violation")
    | .error _ => throw "the trace does not record its verdict (`#meta.status`)"
  let states ← match trace.getObjValAs? (Array Json) "states" with
    | .ok ss => pure ss.toList
    | .error _ => throw "the trace has no `states`"
  let ppTrace (tr : List Verify.ActionStep) : String :=
    if tr.isEmpty then "the start" else "; ".intercalate (tr.map (·.pp))
  let mut cfg := cfg₀
  let mut tr : List Verify.ActionStep := []
  let mut first := true
  for s in states do
    let name ← match s.getObjValAs? String "mbt::actionTaken" with
      | .ok n => pure n
      | .error _ => throw "a state does not record `mbt::actionTaken`; record the trace with `quint run --mbt --out-itf`"
    if name == "init" then
      if !first then throw s!"the trace takes `init` again after {ppTrace tr}"
      first := false
      continue
    first := false
    let q ← if name.startsWith "tick_" then
        match (name.drop 5).toInt? with
        | some d =>
          if m.ticks.contains d then pure (QuintStep.tick d)
          else throw s!"the trace takes `{name}`, a clock advance the model of this program does not have"
        | none => throw s!"the trace takes `{name}`, which is not a clock advance of the model"
      else
        match m.actions.find? (·.ident == name) with
        | none => throw s!"the trace takes `{name}`, which is not an action of the model generated from this program"
        | some a =>
          let picks ← match s.getObjVal? "mbt::nondetPicks" with
            | .ok p => pure p
            | .error _ => throw "a state does not record `mbt::nondetPicks`; record the trace with `quint run --mbt --out-itf`"
          let args ← a.params.zipIdx.mapM fun (p, i) => itfPick s!"n_{a.ident}_{i}" p picks
          pure (QuintStep.act a args)
    let step := q.toActionStep
    let evSteps ← match Verify.candidateSteps m.mode menu cfg with
      | .ok ss => pure ss
      | .error e => throw s!"the evaluator could not list steps after {ppTrace tr}: {e.message}"
    let some evStep := evSteps.find? (·.pp == step.pp)
      | throw s!"step {tr.length + 1} of the trace is {step.pp}, which the evaluator does not offer in {m.mode.name} mode after {ppTrace tr}"
    cfg ← match Verify.stepConfig cfg evStep with
      | .ok c => pure c
      | .error e => throw s!"the evaluator could not take {step.pp} after {ppTrace tr}: {e.message}"
    tr := tr ++ [evStep]
  let violated := Explore.violatedInvariants cfg
  if traceViolation && violated.isEmpty then
    throw s!"Quint reports an invariant violated at the end of the trace; the evaluator, after the same {tr.length} step(s) ({ppTrace tr}), reports none"
  if !traceViolation && !violated.isEmpty then
    throw s!"Quint reports no violation; the evaluator, after the same {tr.length} step(s) ({ppTrace tr}), reports {violated} violated"
  pure { steps := tr, traceViolation, violated }

end Charter.Project
