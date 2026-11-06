import Charter.Verify.Reduction
import Charter.Artifact.Hash
import Charter.Artifact.Cert
import Lean.Data.Json

/-!
# Charter.Verify.Explorer — Lawful, Adversarial, and Mixed-Mode Explorer (`G2.1`, `T28`, `T29`)

Extends state-space exploration beyond compliant (`lawful`) actions to:
- `adversarial`: all candidate `Act` and `Event` instances (lawful or unlawful, valid or void)
  plus optional `@ (now + δ)` clock advances from `explore-domain: duration = ...`;
- `mixed`: designated adversary actors may perform unlawful actions while other actors act
  only when `Enabled` (`lawful`);
- `bfs`, `dfs`, and reproducible seeded `random` search strategies;
- partial-order canonical ordering on statically independent actions (`Verify.Reduction`);
- counterexample trace minimization (`minimizeTrace`) and canonical `Counterexample` JSON/Scenario export.
-/

namespace Charter.Verify

open Lean (Json)
open M

inductive ExploreMode
  | lawful
  | adversarial
  | mixed (adversaries : List String)
  deriving Repr, DecidableEq, Inhabited

def ExploreMode.name : ExploreMode → String
  | .lawful => "lawful"
  | .adversarial => "adversarial"
  | .mixed _ => "mixed"

inductive Strategy
  | bfs
  | dfs
  | random (seed : UInt64)
  deriving Repr, DecidableEq, Inhabited

inductive ActionStep
  | trigger (te : Tagged)
  | advanceClock (delta : Int)
  deriving Repr, Inhabited

def ActionStep.domName : ActionStep → Option DomId
  | .trigger te => some te.2
  | .advanceClock _ => none

def ActionStep.pp : ActionStep → String
  | .trigger te => te.pp
  | .advanceClock d => s!"@ (+{d})"

def ActionStep.toPhraseText : ActionStep → String
  | .trigger te =>
    match te.1 with
    | .prod args =>
      let argStrs := args.map fun
        | (.str s, _) => showString s
        | (.int i, _) => toString i
        | (e, d) => Elem.pp e d
      s!"{te.2}({", ".intercalate argStrs})."
    | .str s => s!"{te.2}({showString s})."
    | .int i => s!"{te.2}({i})."
  | .advanceClock d => s!"@ (Current Time + {d})."

/-- Extract the actor string of an act instance, if its first product component is a string. -/
def actorNameOf (te : Tagged) : Option String :=
  match te.1 with
  | .prod ((.str s, _) :: _) => some s
  | _ => none

/-- Coverage check tailored to `mode` (`T29`): in `lawful` mode, checks `judgedAct`s; in
`adversarial`/`mixed` mode, checks every triggerable `Act`/`Event` with non-enumerable
primitive components so missing menus never yield a false pass. -/
def modeCoverage (mode : ExploreMode) (spec : Spec) (menu : Explore.Menu) : List Explore.Coverage :=
  match mode with
  | .lawful => Explore.coverage spec menu
  | .adversarial | .mixed _ =>
    spec.decls.flatMap fun (p : DomId × TypeSpec) =>
      let isTrig := match p.2.kind with | .act _ | .event _ => true | _ => false
      if !isTrig || spec.enumerable p.2.domain then []
      else
        (spec.components p.1).filterMap fun x =>
          let d := spec.removeDecoration x
          match Explore.needsMenu spec d with
          | none => none
          | some _ => some ⟨p.1, d, if menu.any (·.1 == d) then .menu else .stateValues⟩

/-- Candidate steps from `cfg` under `mode` and `menu`. -/
def candidateSteps (mode : ExploreMode) (menu : Explore.Menu) (cfg : Config) :
    Except RuntimeError (List ActionStep) := do
  let spec := cfg.spec
  let ctx := Ctx.of spec cfg.state
  let trigTypes := spec.decls.filterMap fun (p : DomId × TypeSpec) =>
    match mode, p.2.kind with
    | .lawful, .act _ => some (p.1, p.2)
    | .adversarial, .act _ | .adversarial, .event _ => some (p.1, p.2)
    | .mixed _, .act _ | .mixed _, .event _ => some (p.1, p.2)
    | _, _ => none
  let actSteps ← trigTypes.foldlM (fun acc (d, tspec) => do
    let xs := spec.components d
    let body : M Tagged := whenTagged (eval M.fuel (.app d (.named []))) pure
    let needsJudgedScope := !spec.enumerable tspec.domain
    let m : M (List Tagged) := results (if needsJudgedScope
      then Explore.scopeJudged menu M.fuel xs body
      else scope M.fuel xs body)
    let insts ← (ignoreMissingInput m).run ctx []
    let insts := insts.flatten
    let filtered ← insts.filterMapM fun te => do
      match mode with
      | .lawful =>
        let r ← (ignoreMissingInput (isEnabled M.fuel te)).run ctx []
        pure (if r.any id then some (.trigger te) else none)
      | .adversarial =>
        pure (some (.trigger te))
      | .mixed advs =>
        match tspec.kind with
        | .event _ => pure (some (.trigger te))
        | _ =>
          let isAdv := match actorNameOf te with
            | some a => advs.contains a
            | none => false
          if isAdv then pure (some (.trigger te))
          else
            let r ← (ignoreMissingInput (isEnabled M.fuel te)).run ctx []
            pure (if r.any id then some (.trigger te) else none)
    pure (acc ++ filtered)) []
  let clockSteps : List ActionStep := match mode with
    | .lawful => []
    | .adversarial | .mixed _ =>
      match menu.find? (·.1 == "duration") with
      | some (_, es) =>
        es.filterMap fun
          | .int delta => if delta > 0 then some (.advanceClock delta) else none
          | _ => none
      | none => []
  pure (actSteps ++ clockSteps)

/-- Execute one `ActionStep` from `cfg`. -/
def stepConfig (cfg : Config) : ActionStep → Except RuntimeError Config
  | .trigger te => Explore.perform cfg te
  | .advanceClock delta => do
    let specIdx := cfg.spec.buildIndex
    let state1 : State := { cfg.state with time := cfg.state.time + delta, step := cfg.state.step + 1 }
    let state' ← Saturate.rebaseAndSatWithIdx cfg.spec specIdx cfg.strata state1
    pure { cfg with state := state' }

/-- State key including clock time and holding instances so timed expiries distinguish states. -/
def timedStateKey (s : State) : String :=
  s!"@{s.time}|" ++ Explore.stateKey s

/-- Deterministic xorshift64 step for seeded pseudo-random ordering. -/
def xorshift64 (x : UInt64) : UInt64 :=
  let s := if x == 0 then 0x9e3779b97f4a7c15 else x
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def shuffleDet {α : Type} (seed : UInt64) (xs : List α) : UInt64 × List α :=
  let arr := xs.toArray
  let n := arr.size
  let rec loop (i : Nat) (st : UInt64) (a : Array α) : UInt64 × Array α :=
    match i with
    | 0 => (st, a)
    | k + 1 =>
      let st' := xorshift64 st
      let j := (st'.toNat) % (k + 1)
      if h1 : k < a.size then
        if h2 : j < a.size then
          let tmp := a[k]
          let a := a.set! k a[j]
          let a := a.set! j tmp
          loop k st' a
        else loop k st' a
      else loop k st' a
  let (seed', out) := loop n seed arr
  (seed', out.toList)

/-- Replay a candidate trace from `cfg₀` and test whether invariant `inv` is violated at the end. -/
def replaysViolation (cfg₀ : Config) (inv : DomId) (trace : List ActionStep) : Bool :=
  let rec go : Config → List ActionStep → Bool
    | cfg, [] => (Explore.violatedInvariants cfg).contains inv
    | cfg, st :: rest =>
      match stepConfig cfg st with
      | .ok cfg' => go cfg' rest
      | .error _ => false
  go cfg₀ trace

/-- Shrink a counterexample trace by delta-debugging single-step deletions (`--minimize`). -/
def minimizeTrace (cfg₀ : Config) (inv : DomId) (trace : List ActionStep) : List ActionStep :=
  let rec shrinkPass (fuel : Nat) (cur : List ActionStep) : List ActionStep :=
    match fuel with
    | 0 => cur
    | fuel + 1 =>
      let indices := List.range cur.length
      let dropped? := indices.findSome? fun idx =>
        let cand := (cur.take idx) ++ (cur.drop (idx + 1))
        if replaysViolation cfg₀ inv cand then some cand else none
      match dropped? with
      | some shorter => shrinkPass fuel shorter
      | none => cur
  shrinkPass (trace.length + 1) trace

structure Counterexample where
  invariant       : DomId
  mode            : ExploreMode
  trace           : List ActionStep
  minimized       : Bool
  visitedStates   : Nat
  lawSha256       : String
  decisiveClauses : List (ClauseId × String)

def Counterexample.toJson (cx : Counterexample) : Json :=
  Json.mkObj [
    ("kind", Json.str "counterexample"),
    ("lawSha256", Json.str cx.lawSha256),
    ("mode", Json.str cx.mode.name),
    ("violatedProperty", Json.str cx.invariant),
    ("minimized", Json.bool cx.minimized),
    ("visitedStates", Json.num cx.visitedStates),
    ("decisiveRuleSpans", Json.arr (cx.decisiveClauses.map fun (c, s) =>
      Json.mkObj [("clause", Json.str c), ("span", Json.str s)]).toArray),
    ("orderedEvents", Json.arr (cx.trace.map fun st => Json.str st.pp).toArray),
    ("replayScenario", Json.arr (cx.trace.map fun st => Json.str st.toPhraseText).toArray)
  ]

inductive VerifyResult
  | safe (visited : Nat) (cov : List Explore.Coverage) (cappedOut : Bool)
  | counterexample (cx : Counterexample)
  | error (e : RuntimeError)

structure SearchOpts where
  mode     : ExploreMode := .lawful
  strategy : Strategy := .bfs
  depth    : Nat := 3
  stateCap : Nat := 5000
  minimize : Bool := true
  menu     : Explore.Menu := []

/-- Run state-space exploration from `cfg₀`. -/
def search (opts : SearchOpts) (cfg₀ : Config) : VerifyResult :=
  let cov := modeCoverage opts.mode cfg₀.spec opts.menu
  let lawHash := Artifact.sha256String (reprStr cfg₀.spec)
  let mkCx (inv : DomId) (tr : List ActionStep) (vis : Nat) : VerifyResult :=
    let tr' := if opts.minimize then minimizeTrace cfg₀ inv tr else tr
    let spans := match cfg₀.spec.findDecl inv with
      | some t => t.spans
      | none => []
    .counterexample {
      invariant := inv
      mode := opts.mode
      trace := tr'
      minimized := opts.minimize
      visitedStates := vis
      lawSha256 := lawHash
      decisiveClauses := spans
    }
  match Explore.violatedInvariants cfg₀ with
  | d :: _ => mkCx d [] 1
  | [] =>
    let initSeed : UInt64 := match opts.strategy with | .random s => s | _ => 1
    let rec loop (frontier : List (Config × List ActionStep)) (seen : List String)
        (rng : UInt64) (fuel : Nat) : VerifyResult :=
      match fuel with
      | 0 => .safe seen.length cov (!frontier.isEmpty)
      | fuel + 1 =>
        match frontier with
        | [] => .safe seen.length cov false
        | (c, tr) :: rest =>
          if tr.length ≥ opts.depth then
            loop rest seen rng fuel
          else
            match candidateSteps opts.mode opts.menu c with
            | .error e => .error e
            | .ok rawSteps =>
              -- Canonical partial-order pruning: if last step `dPrev` and candidate `dCur` are
              -- statically independent and `dCur < dPrev`, skip the inverted permutation (`G2.2`).
              let steps := match tr.getLast?.bind ActionStep.domName with
                | some dPrev =>
                  rawSteps.filter fun st =>
                    match st.domName with
                    | some dCur => !(dCur < dPrev && staticallyIndependent cfg₀.spec dPrev dCur)
                    | none => true
                | none => rawSteps
              let (rng', orderedSteps) := match opts.strategy with
                | .random _ => shuffleDet rng steps
                | _ => (rng, steps)
              let rec expand : List ActionStep → List (Config × List ActionStep) → List String →
                  Except RuntimeError (Option (DomId × List ActionStep) × List (Config × List ActionStep) × List String)
                | [], acc, sn => .ok (none, acc.reverse, sn)
                | st :: more, acc, sn => do
                  let c' ← stepConfig c st
                  let tr' := tr ++ [st]
                  match Explore.violatedInvariants c' with
                  | d :: _ => .ok (some (d, tr'), [], sn)
                  | [] =>
                    let k := timedStateKey c'.state
                    if sn.contains k then expand more acc sn
                    else expand more ((c', tr') :: acc) (k :: sn)
              match expand orderedSteps [] seen with
              | .error e => .error e
              | .ok (some (d, tr'), _, sn') => mkCx d tr' sn'.length
              | .ok (none, nextNodes, sn') =>
                if sn'.length ≥ opts.stateCap then
                  .safe sn'.length cov (!(rest ++ nextNodes).isEmpty)
                else
                  let nextFrontier := match opts.strategy with
                    | .dfs => nextNodes ++ rest
                    | _ => rest ++ nextNodes
                  loop nextFrontier sn' rng' fuel
    loop [(cfg₀, [])] [timedStateKey cfg₀.state] initSeed (opts.stateCap + 1)

end Charter.Verify
