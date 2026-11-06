import Charter.Cli.Test
import Charter.Verify.Explorer

/-!
# Charter.Cli.Explore — `charter explore [--mode lawful|adversarial|mixed] ... <file.charter>`

Runs native state-space exploration (`Charter.Verify.Explorer`) from top-level and `Scenario`
end-states, emitting structured `ClaimCertificate` and `Counterexample` records (`G2.1`, `G2.2`).
Never reports success on incomplete candidate coverage (`T29`) or state-cap exhaustion.
-/

namespace Charter.Cli

open Lean (Json)

structure ExploreCliOpts where
  mode            : Verify.ExploreMode := .lawful
  strategy        : Verify.Strategy := .bfs
  depth           : Option Nat := none
  stateCap        : Nat := 5000
  minimize        : Bool := true
  requireComplete : Bool := false
  json            : Bool := false
  regime          : Option String := none
  menu            : Explore.Menu := []
  files           : List String := []

def parseExploreArgs : List String → ExploreCliOpts → Except String ExploreCliOpts
  | [], o => .ok { o with files := o.files.reverse }
  | "--mode" :: "lawful" :: rest, o => parseExploreArgs rest { o with mode := .lawful }
  | "--mode" :: "adversarial" :: rest, o => parseExploreArgs rest { o with mode := .adversarial }
  | "--mode" :: "mixed" :: rest, o =>
    match o.mode with
    | .mixed advs => parseExploreArgs rest { o with mode := .mixed advs }
    | _ => parseExploreArgs rest { o with mode := .mixed [] }
  | "--mode" :: m :: _, _ => .error s!"--mode takes lawful, adversarial, or mixed, not {m}"
  | ["--mode"], _ => .error "--mode needs lawful, adversarial, or mixed"
  | "--adversary" :: actors :: rest, o =>
    let xs := actors.splitOn "," |>.map String.trim |>.filter (!·.isEmpty)
    let prev := match o.mode with | .mixed a => a | _ => []
    parseExploreArgs rest { o with mode := .mixed (prev ++ xs) }
  | ["--adversary"], _ => .error "--adversary needs comma-separated actor names"
  | "--strategy" :: "bfs" :: rest, o => parseExploreArgs rest { o with strategy := .bfs }
  | "--strategy" :: "dfs" :: rest, o => parseExploreArgs rest { o with strategy := .dfs }
  | "--strategy" :: "random" :: rest, o => parseExploreArgs rest { o with strategy := .random 1 }
  | "--strategy" :: s :: _, _ => .error s!"--strategy takes bfs, dfs, or random, not {s}"
  | ["--strategy"], _ => .error "--strategy needs bfs, dfs, or random"
  | "--seed" :: s :: rest, o => match s.toNat? with
    | some n => parseExploreArgs rest { o with strategy := .random n.toUInt64 }
    | none => .error s!"--seed needs an integer, not {s}"
  | ["--seed"], _ => .error "--seed needs an integer"
  | "--depth" :: n :: rest, o => match n.toNat? with
    | some k => parseExploreArgs rest { o with depth := some k }
    | none => .error s!"--depth needs a non-negative integer, not {n}"
  | ["--depth"], _ => .error "--depth needs a non-negative integer"
  | "--cap" :: n :: rest, o => match n.toNat? with
    | some k => parseExploreArgs rest { o with stateCap := k }
    | none => .error s!"--cap needs a positive integer, not {n}"
  | ["--cap"], _ => .error "--cap needs a positive integer"
  | "--no-minimize" :: rest, o => parseExploreArgs rest { o with minimize := false }
  | "--minimize" :: rest, o => parseExploreArgs rest { o with minimize := true }
  | "--require-complete" :: rest, o => parseExploreArgs rest { o with requireComplete := true }
  | "--regime" :: r :: rest, o => parseExploreArgs rest { o with regime := some r }
  | ["--regime"], _ => .error "--regime needs a regime name"
  | "--out" :: "json" :: rest, o => parseExploreArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseExploreArgs rest o
  | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
  | ["--out"], _ => .error "--out needs json or text"
  | "--explore-domain" :: m :: rest, o =>
    match parseMenuLine m with
    | .ok entry => parseExploreArgs rest { o with menu := o.menu ++ [entry] }
    | .error e => .error e
  | ["--explore-domain"], _ => .error "--explore-domain needs `type = values`"
  | a :: rest, o =>
    if a.startsWith "--" then .error s!"unknown flag {a}"
    else parseExploreArgs rest { o with files := a :: o.files }

/-- Run `Verify.search` at one state and return `(violatedCount, inconclusiveCount)`. -/
def runVerifyAt (o : ExploreCliOpts) (depth : Nat) (menu : Explore.Menu)
    (where_ : String) (cfg : Config) : IO (Nat × Nat) := do
  if depth == 0 || cfg.spec.invariants.isEmpty then return (0, 0)
  let sOpts : Verify.SearchOpts := {
    mode := o.mode, strategy := o.strategy, depth, stateCap := o.stateCap,
    minimize := o.minimize, menu
  }
  match Verify.search sOpts cfg with
  | .error e =>
    let d := Diagnostic.error e.code e.message
    if o.json then IO.println (diagJson d).compress else IO.eprintln d.render
    return (1, 0)
  | .counterexample cx =>
    if o.json then IO.println cx.toJson.compress
    else
      let trS := ", ".intercalate (cx.trace.map Verify.ActionStep.pp)
      IO.println s!"FAIL {where_} [{o.mode.name}]: invariant {cx.invariant} violated in {cx.trace.length} step(s) ({cx.visitedStates} state(s)): {if cx.trace.isEmpty then "(initial state)" else trS}"
    return (1, 0)
  | .safe visited cov cappedOut =>
    let missing := cov.filter (·.source == .stateValues)
    let incomplete := !missing.isEmpty || cappedOut
    let cert : Artifact.ClaimCertificate := {
      claim := s!"invariants@{where_}"
      about := "invariants"
      verdict := if incomplete then none else some true
      assurance := .checked
      scope := .boundedExhaustive depth
      completion := if incomplete then .inconclusive else .complete
      note := if !missing.isEmpty then
                s!"missing explore-domain menu for {", ".intercalate ((missing.map (·.comp)).eraseDups)}"
              else if cappedOut then s!"state cap {o.stateCap} reached before frontier exhausted"
              else s!"mode={o.mode.name}, visited={visited}"
    }
    if o.json then IO.println cert.toJson.compress
    else if incomplete then
      IO.println s!"INCONCLUSIVE {where_} [{o.mode.name}]: {cert.note} ({visited} state(s) within depth {depth})"
    else
      IO.println s!"ok   {where_} [{o.mode.name}]: {cfg.spec.invariants.length} invariant(s) hold across {visited} state(s) up to depth {depth}"
    return (0, if incomplete then 1 else 0)

/-- `charter explore [flags] <file.charter> ...`
Exit status: `0` when complete and safe, `1` on counterexample/error, `2` on usage error,
and `3` when inconclusive (`T28`, `T29`). -/
def exploreCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter explore [--mode lawful|adversarial|mixed] [--adversary <actors>] [--depth <N>] [--strategy bfs|dfs|random] [--seed <N>] [--no-minimize] [--require-complete] [--explore-domain \"type = values\"] [--out json] <file.charter> ..."
  match parseExploreArgs args {} with
  | .error e => IO.eprintln s!"charter explore: {e}\n{usage}"; return 2
  | .ok o =>
    if o.files.isEmpty then IO.eprintln usage; return 2
    let mut violations := 0
    let mut inconclusives := 0
    for f in o.files do
      let src ← try IO.FS.readFile f catch _ => pure ""
      let dirs := readDirectives src
      let depth := o.depth.getD (dirs.explore.getD 2)
      let menu := dirs.exploreMenu ++ o.menu
      let (items, loadDiags) ← loadProgram f
      for d in loadDiags do
        if o.json then IO.println (diagJson d).compress else IO.eprintln d.render
        if d.isError then violations := violations + 1
      let mut cfg : Config := {}
      for l in items do
        match l.item.val with
        | .inl _ => pure ()
        | .inr (.scenario name ps _) =>
          let mut scfg := cfg
          for p in ps do
            let (scfg', _) := runPhrase scfg p
            scfg := scfg'
          let (v, inc) ← runVerifyAt o depth menu s!"{f} [scenario {name}]" scfg
          violations := violations + v
          inconclusives := inconclusives + inc
        | .inr p =>
          let (cfg', outs) := runPhrase cfg p
          for out in outs do
            match out with
            | .diag d => if d.isError then violations := violations + 1
            | _ => pure ()
          cfg := cfg'
      if let some regName := o.regime then
        match applyRegimeOverlay cfg regName with
        | .ok cfgR => cfg := cfgR
        | .error e =>
          IO.eprintln s!"{f}: error CHR003: {e}"
          violations := violations + 1
      let (v, inc) ← runVerifyAt o depth menu f cfg
      violations := violations + v
      inconclusives := inconclusives + inc
    if violations > 0 then return 1
    else if inconclusives > 0 then return 3
    else return 0

end Charter.Cli
