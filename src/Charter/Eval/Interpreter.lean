import Charter.Eval.Step
import Charter.Resolve.Static

/-!
# Charter.Eval.Interpreter — Surface Phrase Resolution + Step & Exploration

Delegates saturation and compiled-phrase execution to `Charter.Eval.Step` (`Law 9`: one
runtime engine shared identically with `charter-server`), adding surface `Phrase` resolution
(`runPhrase`) and explicit-state invariant exploration (`Explore`).
-/

namespace Charter

mutual
/-- Whether a phrase introduces or extends declarations (so `spec` and `strata` change). -/
def Phrase.hasDecls : Phrase → Bool
  | .decls _ => true
  | .par ps => Phrase.listHasDecls ps
  | _ => false
def Phrase.listHasDecls : List Phrase → Bool
  | [] => false
  | p :: ps => p.hasDecls || Phrase.listHasDecls ps
end

/-- Run one phrase: resolve it against the configuration, evaluate, apply, saturate,
report. On failure the configuration is returned unchanged. -/
def runPhrase (cfg : Config) (p : Phrase) : Config × List Output :=
  let declChanged := p.hasDecls
  match resolvePhrase cfg.spec p with
  | .error ds => (cfg, ds.map .diag)
  | .ok (spec', cp, warnings) =>
    let warnOuts := warnings.map Output.diag
    let strataRes : Except (List DomId) (List (List DomId)) :=
      if declChanged then Stratify.strata spec' else .ok cfg.strata
    match strataRes with
    | .error cycle =>
      (cfg, warnOuts ++ [.diag (Diagnostic.error "CHR020"
        s!"derivation is not stratifiable: {", ".intercalate cycle} depend on their own absence (through Not, Forall, or an aggregate)")])
    | .ok strata =>
      let specIdx := spec'.buildIndex
      match Interp.evalClockStep spec' specIdx cfg.state cp with
      | .error e => (cfg, warnOuts ++ [Interp.diagOf e])
      | .ok newTime =>
      let state0 := match newTime with
        | some t => { cfg.state with time := t, step := cfg.state.step + 1 }
        | none => { cfg.state with step := cfg.state.step + 1 }
      let (store?, outs) := Interp.semPhrase spec' specIdx state0 1000 cp
      let outs := match newTime with
        | some t => Output.timeSet t :: outs
        | none => outs
      match store? with
      | none => (cfg, warnOuts ++ outs)
      | some store =>
        if !declChanged && newTime.isNone && store.isEmpty then
          match Interp.checkInvariants spec' specIdx state0 with
          | .error e => (cfg, warnOuts ++ outs ++ [Interp.diagOf e])
          | .ok invViol =>
            let outs2 := invViol.map (fun d => Output.violation (.invariant d))
            ({ cfg with spec := spec', state := state0 }, warnOuts ++ outs ++ outs2)
        else
          let state1 := State.makeAssignments spec' store state0
          let (cfg'?, outs2) := Interp.newContext cfg spec' specIdx strata state1
          match cfg'? with
          | none => (cfg, warnOuts ++ outs ++ outs2)
          | some cfg' => (cfg', warnOuts ++ outs ++ outs2)

/-! ## Exploration (plan §2.2.7): bounded search over acts from a state -/

namespace Explore

open M

inductive Source where
  | menu
  | stateValues
  deriving Repr, BEq, Inhabited

structure Coverage where
  act    : DomId
  comp   : DomId
  source : Source
  deriving Repr, Inhabited

abbrev Menu := List (DomId × List Elem)

partial def Elem.leaves : Elem → List Elem
  | .prod xs => xs.flatMap (fun p => Elem.leaves p.1)
  | e => [e]

def stateValues (s : State) (dom : Domain) : List Elem :=
  let leaves := s.holdsList.flatMap (fun te => Elem.leaves te.1)
  let wanted := leaves.filter fun e => match dom, e with
    | .anyInt, .int _ | .time, .int _ | .duration, .int _ | .money _ _, .int _ | .quantity _, .int _ => true
    | .anyString, .str _ => true
    | _, _ => false
  wanted.foldl (fun acc e => if acc.any (Elem.beq e) then acc else acc ++ [e]) []

def needsMenu (spec : Spec) (d : DomId) : Option Domain :=
  match spec.findDecl d with
  | some t => match t.domain with
    | .anyInt | .anyString | .time | .duration | .money _ _ | .quantity _ => some t.domain
    | _ => none
  | none => none

def coverage (spec : Spec) (menu : Menu) : List Coverage :=
  spec.decls.flatMap fun (p : DomId × TypeSpec) =>
    match spec.judgedAct p.1 with
    | none => []
    | some _ => (spec.components p.1).filterMap fun x =>
      let d := spec.removeDecoration x
      match needsMenu spec d with
      | none => none
      | some _ => some ⟨p.1, d, if menu.any (·.1 == d) then .menu else .stateValues⟩

def scopeJudged (menu : Menu) : Nat → List Var → M Tagged → M Tagged
  | 0, _, _ => err (.fuelExhausted "binding a judged act's components")
  | _, [], m => m
  | fuel + 1, x :: xs, m => do
    let spec ← getSpec
    let state ← getState
    let d := spec.removeDecoration x
    let te ← match needsMenu spec d with
      | none => everyValidSubs fuel x
      | some dom =>
        let vals := match menu.find? (·.1 == d) with
          | some (_, vs) => vs
          | none => stateValues state dom
        let te ← nd (vals.map fun e => ((e, d) : Tagged))
        if ← isValidInstance fuel te then pure te else empty
    bindVar x te (scopeJudged menu fuel xs m)

def enabledActs (menu : Menu) (cfg : Config) : Except RuntimeError (List Tagged) := do
  let spec := cfg.spec
  let ctx := Ctx.of spec cfg.state
  let acts := spec.decls.filterMap fun (p : DomId × TypeSpec) => match p.2.kind with
    | .act _ => some p.1
    | _ => none
  acts.foldlM (fun acc d => do
    let xs := spec.components d
    let body : M Tagged := whenTagged (eval M.fuel (.app d (.named []))) pure
    let m : M (List Tagged) := results (match spec.judgedAct d with
      | some _ => scopeJudged menu M.fuel xs body
      | none => scope M.fuel xs body)
    let insts ← (ignoreMissingInput m).run ctx []
    let insts := insts.flatten
    let enabled ← insts.filterMapM fun te => do
      let r ← (ignoreMissingInput (isEnabled M.fuel te)).run ctx []
      pure (if r.any id then some te else none)
    pure (acc ++ enabled)) []

def perform (cfg : Config) (te : Tagged) : Except RuntimeError Config := do
  let specIdx := cfg.spec.buildIndex
  let ctx := Ctx.ofIdx cfg.spec specIdx cfg.state
  let infos ← (instantiateTrans M.fuel [] te).run ctx []
  let store := Store.unions (infos.map (·.assignments))
  let state1 := State.makeAssignments cfg.spec store { cfg.state with step := cfg.state.step + 1 }
  let state' ← Saturate.rebaseAndSatWithIdx cfg.spec specIdx cfg.strata state1
  pure { cfg with state := state' }

def violatedInvariants (cfg : Config) : List DomId :=
  let ctx := Ctx.of cfg.spec cfg.state
  cfg.spec.invariants.filter fun d =>
    let term := Term.exists_ [⟨d, ""⟩] (.present (.ref ⟨d, ""⟩))
    match (ignoreMissingInput (checkFalse (eval M.fuel term))).run ctx [] with
    | .ok rs => !rs.isEmpty
    | .error _ => false

def stateKey (s : State) : String :=
  let names := s.holdsList.map Tagged.pp
  String.intercalate "|" (names.toArray.qsort (· < ·)).toList

inductive Result where
  | safe (visited : Nat) (cov : List Coverage)
  | violated (invariant : DomId) (trace : List Tagged) (visited : Nat)
  | error (e : RuntimeError)

def bfs (menu : Menu) (cfg : Config) (depth cap : Nat) : Result :=
  let cov := coverage cfg.spec menu
  match violatedInvariants cfg with
  | d :: _ => .violated d [] 1
  | [] =>
    let rec go (frontier : List (Config × List Tagged)) (seen : List String) (fuel : Nat) : Result :=
      match fuel with
      | 0 => .safe seen.length cov
      | fuel + 1 =>
        if frontier.isEmpty then .safe seen.length cov else
        let step := frontier.foldl (fun (acc : Except RuntimeError (List (Config × List Tagged) × List String × Option (DomId × List Tagged))) (c, trace) =>
          match acc with
          | .error e => .error e
          | .ok (next, seen, some v) => .ok (next, seen, some v)
          | .ok (next, seen, none) =>
            match enabledActs menu c with
            | .error e => .error e
            | .ok cands =>
              cands.foldl (fun acc te =>
                match acc with
                | .error e => .error e
                | .ok (next, seen, some v) => .ok (next, seen, some v)
                | .ok (next, seen, none) =>
                  if seen.length ≥ cap then .ok (next, seen, none) else
                  match perform c te with
                  | .error e => .error e
                  | .ok c' =>
                    let key := stateKey c'.state
                    if seen.contains key then .ok (next, seen, none)
                    else
                      let trace' := trace ++ [te]
                      match violatedInvariants c' with
                      | d :: _ => .ok (next, key :: seen, some (d, trace'))
                      | [] => .ok (next ++ [(c', trace')], key :: seen, none)) (.ok (next, seen, none)))
          (.ok ([], seen, none))
        match step with
        | .error e => .error e
        | .ok (_, seen, some (d, trace)) => .violated d trace seen.length
        | .ok (next, seen, none) => go next seen fuel
    go [(cfg, [])] [stateKey cfg.state] depth

end Explore

end Charter
