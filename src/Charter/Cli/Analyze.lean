import Charter.Cli.Test
import Lean.Data.Json

/-!
# Charter.Cli.Analyze — Whole-Specification Static & Bounded-Reachability Analysis (`#69`)

`charter analyze <file.charter> [--depth <N>] [--out json]` inspects a specification for:
1. **Unranked `Default`/`Exception` overlaps (`CHR047`)**: two defeasible rules on the same type
   that prescribe distinct consequences with no explicit `Overrides` or `Document ... Rank`
   priority edge between them and non-disjoint applicability conditions;
2. **Generated-scenario invariant violations**: bounded exploration from initial & seeded states
   checking all declared invariants;
3. **Dead rules (`CHR048`)**: a `Power`/`Finding`/`Amend` that can never be valid, an undischarged
   or dead `Duty`, an `Immunity`/`Protection` that never holds, or a derived `Fact`/`Function`
   that can never be derived.
-/

namespace Charter.Cli

open Lean (Json)

structure AnalyzeOpts where
  paths : List String := []
  depth : Nat := 3
  json  : Bool := false

def parseAnalyzeArgs : List String → AnalyzeOpts → Except String AnalyzeOpts
  | [], o => .ok { o with paths := o.paths.reverse }
  | "--depth" :: n :: rest, o =>
    match n.toNat? with
    | some k => parseAnalyzeArgs rest { o with depth := k }
    | none => .error s!"--depth expects a natural number, got `{n}`"
  | ["--depth"], _ => .error "--depth requires a number"
  | "--out" :: "json" :: rest, o => parseAnalyzeArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseAnalyzeArgs rest { o with json := false }
  | ["--out"], _ => .error "--out requires `json` or `text`"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag `{a}`"
    else parseAnalyzeArgs rest { o with paths := a :: o.paths }

structure AnalyzeFinding where
  code    : String
  kind    : String
  target  : String
  message : String

def AnalyzeFinding.toJson (f : AnalyzeFinding) : Json :=
  Json.mkObj [
    ("code", Json.str f.code),
    ("kind", Json.str f.kind),
    ("target", Json.str f.target),
    ("message", Json.str f.message)
  ]

def splitTopConjuncts : Term → List Term
  | .and a b => splitTopConjuncts a ++ splitTopConjuncts b
  | .exists_ _ u => splitTopConjuncts u
  | t => [t]

/-- Conservative syntactic check for mutually exclusive rule conditions (`p` vs `Not(p)`,
`x == lit1` vs `x == lit2`, or `False`). -/
def areSyntacticallyDisjoint (c1 c2 : Term) : Bool :=
  let js1 := splitTopConjuncts c1
  let js2 := splitTopConjuncts c2
  let isFalseLit : Term → Bool
    | .boolLit false => true
    | _ => false
  if js1.any isFalseLit || js2.any isFalseLit then true
  else
    let directContradiction := js1.any fun a =>
      js2.any fun b =>
        reprStr a == reprStr (Term.not b) ||
        reprStr b == reprStr (Term.not a) ||
        match a, b with
        | .eq lhs1 (.stringLit s1), .eq lhs2 (.stringLit s2) => reprStr lhs1 == reprStr lhs2 && s1 != s2
        | .eq lhs1 (.intLit i1), .eq lhs2 (.intLit i2) => reprStr lhs1 == reprStr lhs2 && i1 != i2
        | .eq lhs1 rhs1, .neq lhs2 rhs2 => reprStr lhs1 == reprStr lhs2 && reprStr rhs1 == reprStr rhs2
        | .neq lhs1 rhs1, .eq lhs2 rhs2 => reprStr lhs1 == reprStr lhs2 && reprStr rhs1 == reprStr rhs2
        | .le lhs1 rhs1, .geq lhs2 rhs2 => reprStr lhs1 == reprStr lhs2 && reprStr rhs1 == reprStr rhs2
        | .geq lhs1 rhs1, .le lhs2 rhs2 => reprStr lhs1 == reprStr lhs2 && reprStr rhs1 == reprStr rhs2
        | _, _ => false
    directContradiction

def consequencesDiffer : DefeasibleConseq → DefeasibleConseq → Bool
  | .holdsBool b1, .holdsBool b2 => b1 != b2
  | .yieldsVal v1, .yieldsVal v2 => reprStr v1 != reprStr v2
  | _, _ => true

/-- Detect unranked `Default`/`Exception` rule pairs on `(d, t)` (`#69`, `CHR047`). -/
def checkUnrankedOverlaps (spec : Spec) (d : DomId) (t : TypeSpec)
    (conflictWitnesses : List (String × String × String)) : List AnalyzeFinding := Id.run do
  let rs := t.defeasibleRules
  if rs.length < 2 then return []
  let normId (rid : String) : String :=
    if rid.startsWith (d ++ ".") then rid.drop (d.length + 1) else rid
  let rankPairs : List (String × String) :=
    (spec.rankEdges.filter (·.1 == d)).map fun (_, e) => (normId e.higherRule, normId e.lowerRule)
  let directOverrides (hi lo : String) : Bool :=
    let nhi := normId hi
    let nlo := normId lo
    (match rs.find? (fun r => normId r.id == nhi) with
     | some r => r.overrides.any (fun ov => normId ov == nlo)
     | none => false) ||
    rankPairs.any (fun (a, b) => a == nhi && b == nlo)
  let allIds := rs.map (fun r => normId r.id)
  let rec reachesOv (fuel : Nat) (work vis : List String) (goal : String) : Bool :=
    match fuel, work with
    | 0, _ | _, [] => false
    | fuel' + 1, u :: rest =>
      if u == goal then true
      else if vis.contains u then reachesOv fuel' rest vis goal
      else
        let nbrs := allIds.filter (directOverrides u)
        reachesOv fuel' (nbrs ++ rest) (u :: vis) goal
  let ovFuel := allIds.length * allIds.length + 2
  let isRanked (r1 r2 : DefeasibleRule) : Bool :=
    let i1 := normId r1.id
    let i2 := normId r2.id
    reachesOv ovFuel (allIds.filter (directOverrides i1)) [] i2 ||
    reachesOv ovFuel (allIds.filter (directOverrides i2)) [] i1

  let mut findings : List AnalyzeFinding := []
  let arr := rs.toArray
  for i in [0 : arr.size] do
    for j in [i + 1 : arr.size] do
      let r1 := arr[i]!
      let r2 := arr[j]!
      if consequencesDiffer r1.conseq r2.conseq && !isRanked r1 r2 then
        let i1 := normId r1.id
        let i2 := normId r2.id
        let wit? := conflictWitnesses.findSome? fun (ty, a, b) =>
          if ty == d && ((normId a == i1 && normId b == i2) || (normId a == i2 && normId b == i1)) then
            some s!" (witnessed conflict in generated state)"
          else none
        if wit?.isSome || !areSyntacticallyDisjoint r1.cond r2.cond then
          findings := findings ++ [{
            code := "CHR047"
            kind := "unranked-overlap"
            target := s!"{d}:{r1.id},{r2.id}"
            message := s!"`{d}` has unranked defeasible rules `{r1.id}` and `{r2.id}` with distinct outcomes and no `Overrides` or `Document Rank` priority{wit?.getD ""}"
          }]
  return findings

def termAlwaysFalse : Term → Bool
  | .boolLit false => true
  | .exists_ _ body => termAlwaysFalse body
  | .and a b => termAlwaysFalse a || termAlwaysFalse b
  | .when _ c => termAlwaysFalse c
  | _ => false

def derivationAlwaysFalse (ds : List Derivation) : Bool :=
  !ds.isEmpty && ds.all fun
    | .holdsWhen t => termAlwaysFalse t
    | .dv _ t => termAlwaysFalse t
    | .defeasibleDAG _ rs => rs.isEmpty || rs.all (fun r => termAlwaysFalse r.cond)

/-- Collect reachable states via bounded scenario generation (`#69`). -/
def generateStates (menu : Explore.Menu) (seedCfgs : List Config) (depth cap : Nat) :
    List (Config × List Tagged) := Id.run do
  let defaultMenu : Explore.Menu :=
    if menu.any (·.1 == "int") then menu
    else ("int", [.int 0, .int 1, .int 10, .int 100]) :: menu
  let mut visited : List (Config × List Tagged) := seedCfgs.map (·, [])
  let mut seenKeys : List String := seedCfgs.map (fun c => Explore.stateKey c.state)
  let mut frontier : List (Config × List Tagged) := visited
  for _ in [0 : depth] do
    if frontier.isEmpty || visited.length >= cap then pure ()
    else
      let mut nextFrontier : List (Config × List Tagged) := []
      for (c, tr) in frontier do
        if visited.length < cap then
          match Explore.enabledActs defaultMenu c with
          | .error _ => pure ()
          | .ok acts =>
            for te in acts do
              if visited.length < cap then
                match Explore.perform c te with
                | .error _ => pure ()
                | .ok c' =>
                  let k := Explore.stateKey c'.state
                  if !seenKeys.contains k then
                    seenKeys := k :: seenKeys
                    let entry := (c', tr ++ [te])
                    visited := visited ++ [entry]
                    nextFrontier := nextFrontier ++ [entry]
      frontier := nextFrontier
  return visited

/-- Run whole-specification analysis on one `.charter` file (`#69`). -/
def analyzeFile (path : System.FilePath) (depth : Nat) : IO (Nat × List AnalyzeFinding) := do
  let src ← try IO.FS.readFile path catch _ => pure ""
  let dirs := readDirectives src
  let (items, loadDiags) ← loadProgram path
  if loadDiags.any (·.isError) then
    return (0, loadDiags.filter (·.isError) |>.map fun d =>
      { code := d.code, kind := "load-error", target := path.toString, message := d.message })

  let mut baseCfg : Config := {}
  let mut specIdx : Spec.SpecIndex := baseCfg.spec.buildIndex
  let mut scenSeeds : List Config := []
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario name ps spans) =>
      baseCfg := { baseCfg with spec := baseCfg.spec.insertScenario name spans }
      let mut scCfg := baseCfg
      let mut scIdx := specIdx
      for p in ps do
        let (c', idx', _) := runPhraseCached scCfg scIdx true p
        scCfg := c'
        scIdx := idx'
      scenSeeds := scenSeeds ++ [scCfg]
    | .inr p =>
      let (c', idx', outs) := runPhraseCached baseCfg specIdx true p
      let errs := outs.filterMap fun | .diag d => if d.isError then some d else none | _ => none
      if !errs.isEmpty then
        return (0, errs.map fun d => { code := d.code, kind := "resolve-error", target := path.toString, message := d.message })
      baseCfg := c'
      specIdx := idx'

  let spec := baseCfg.spec
  let visited := generateStates dirs.exploreMenu (baseCfg :: scenSeeds) depth 300
  let visitedStates := visited.map (·.1)

  let mut findings : List AnalyzeFinding := []

  -- 1. Check invariants across generated traces from `baseCfg`
  let genOnly := generateStates dirs.exploreMenu [baseCfg] depth 200
  for (c, tr) in genOnly do
    for inv in Explore.violatedInvariants c do
      if !findings.any (fun f => f.kind == "invariant-violation" && f.target == inv) then
        let trS := if tr.isEmpty then "(initial state)" else ", ".intercalate (tr.map Tagged.pp)
        findings := findings ++ [{
          code := "CHR049"
          kind := "invariant-violation"
          target := inv
          message := s!"invariant `{inv}` violated on generated trace: {trS}"
        }]

  -- Extract any concrete defeasible conflicts witnessed in `visitedStates`
  let witnessedConflicts : List (String × String × String) :=
    visitedStates.flatMap fun c =>
      c.state.holdsList.filterMap fun te =>
        if te.2 == defConflictDom then
          match te.1 with
          | .prod [_, (.str ty, _), (.str r1, _), (.str r2, _)] => some (ty, r1, r2)
          | _ => none
        else none

  -- 2. Unranked Default/Exception overlaps (`CHR047`)
  for (d, t) in spec.decls.reverse do
    findings := findings ++ checkUnrankedOverlaps spec d t witnessedConflicts

  -- 3. Dead rules (`CHR048`)
  let hasOpenDecls : Bool := spec.decls.any fun (nm, ts) =>
    nm != "int" && nm != "string" && nm != "actor" && !nm.startsWith "_" && !ts.isClosed
  let createdDoms : List DomId := spec.decls.flatMap fun (_, ts) =>
    let effs := match ts.kind with | .act a => a.effects | .event e => e.effects | _ => []
    effs.filterMap fun
      | .cAll _ tm _ _ => Stratify.typeOf spec tm
      | _ => none

  let everHoldsInVisited (d : DomId) : Bool :=
    visitedStates.any fun c => c.state.holdsList.any (·.2 == d)

  let everValidActInVisited (d : DomId) : Bool :=
    visitedStates.any fun c =>
      let ctx := Ctx.ofIdx c.spec specIdx c.state
      let held := c.state.holdsList.filter (·.2 == d)
      held.any fun te =>
        match (M.ignoreMissingInput (M.isValid M.fuel te)).run ctx [] with
        | .ok bs => bs.any id
        | .error _ => false

  let mut deadActs : List DomId := []
  for (d, t) in spec.decls.reverse do
    if d != "int" && d != "string" && d != "actor" && !d.startsWith "_" then
      match t.kind with
      | .act a =>
        let isInstitutionalPower := a.isPower || a.isFinding || a.isAmend
        let staticallyDeadValid := isInstitutionalPower && a.validWhen.any termAlwaysFalse
        let staticallyDeadHolds := derivationAlwaysFalse t.derivation
        let reachabilityDead :=
          isInstitutionalPower && !hasOpenDecls && spec.enumerable t.domain && !everValidActInVisited d
        if staticallyDeadValid || staticallyDeadHolds || reachabilityDead then
          deadActs := deadActs ++ [d]
          findings := findings ++ [{
            code := "CHR048"
            kind := "dead-power"
            target := d
            message := s!"power `{d}` can never be validly exercised ({if staticallyDeadValid then "`Valid when` is unsatisfiable" else if staticallyDeadHolds then "`Holds when` is unsatisfiable" else s!"never valid across {visited.length} explored state(s)"})"
          }]
      | _ => pure ()

  for (d, t) in spec.decls.reverse do
    if d != "int" && d != "string" && d != "actor" && !d.startsWith "_" then
      match t.kind with
      | .duty du =>
        if derivationAlwaysFalse t.derivation then
          findings := findings ++ [{
            code := "CHR048"
            kind := "dead-duty"
            target := d
            message := s!"duty `{d}` can never hold (`Holds when` is unsatisfiable)"
          }]
        else if !du.terminatingActs.isEmpty && du.terminatingActs.all deadActs.contains then
          findings := findings ++ [{
            code := "CHR048"
            kind := "undischargeable-duty"
            target := d
            message := s!"duty `{d}` can never be discharged (every terminating act in `{", ".intercalate du.terminatingActs}` is dead)"
          }]
      | .immunity _ =>
        let uncreatable := t.derivation.isEmpty && !createdDoms.contains d && !everHoldsInVisited d
        if derivationAlwaysFalse t.derivation || uncreatable || (!hasOpenDecls && spec.enumerable t.domain && !t.derivation.isEmpty && !everHoldsInVisited d) then
          findings := findings ++ [{
            code := "CHR048"
            kind := "dead-immunity"
            target := d
            message := s!"immunity `{d}` never holds ({if derivationAlwaysFalse t.derivation then "`Holds when` is unsatisfiable" else if uncreatable then "neither derived nor created by any act" else s!"never active across {visited.length} explored state(s)"})"
          }]
      | .fact fs =>
        if !fs.invariant && !t.derivation.isEmpty then
          if derivationAlwaysFalse t.derivation || (!hasOpenDecls && spec.enumerable t.domain && !everHoldsInVisited d) then
            findings := findings ++ [{
              code := "CHR048"
              kind := "dead-derived-fact"
              target := d
              message := s!"derived fact `{d}` can never be derived ({if derivationAlwaysFalse t.derivation then "derivation condition is unsatisfiable" else s!"never derived across {visited.length} explored state(s)"})"
            }]
      | _ => pure ()

  return (visited.length, findings)

/-- `charter analyze <file.charter> ... [--depth <N>] [--out json]` -/
def analyzeCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter analyze <file.charter> ... [--depth <N>] [--out json]"
  let opts ← match parseAnalyzeArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter analyze: {e}\n{usage}"; return 2
  if opts.paths.isEmpty then
    IO.eprintln usage
    return 2
  let mut status : UInt32 := 0
  for p in opts.paths do
    let (visCount, findings) ← analyzeFile p opts.depth
    if opts.json then
      let j := Json.mkObj [
        ("kind", Json.str "analyze"),
        ("file", Json.str p),
        ("statesVisited", Json.num visCount),
        ("ok", Json.bool findings.isEmpty),
        ("findings", Json.arr (findings.map AnalyzeFinding.toJson).toArray)
      ]
      IO.println j.compress
    else if findings.isEmpty then
      IO.println s!"ok   {p}: 0 dead rules, 0 unranked overlaps across {visCount} generated state(s)"
    else
      for f in findings do
        IO.eprintln s!"{p}: error {f.code} [{f.kind}]: {f.message}"
      IO.println s!"FAIL {p}: {findings.length} analysis finding(s) across {visCount} generated state(s)"
    if !findings.isEmpty then status := 1
  return status

end Charter.Cli
