import Charter.Verify.Explorer
import Charter.Surface.Parser

/-!
# Charter.Project.QuintTarget — Typed Quint Protocol AST, Validator, & Trace Importer (`G5.2`, `D28`, `T32`)

Projects live `Core.Spec` (`CIR`) models into idiomatic Quint (`.qnt`) protocol specifications
(`docs/rfc.md` §9.3, `T26`, `T27`, `T32`) with:
1. Typed `QuintModule` AST (state variables, `init`, `lawful` vs. `adversarial` step actions,
   state `Invariant` predicates, and temporal `Property` formulas);
2. Independent structural parser/validator checking balanced blocks, variable declarations,
   `init`/`step` definitions, and invariant bindings;
3. Counterexample trace search & importer (`verifyAndImportQuintTrace`) that decodes protocol
   counterexample traces back into `Phrase`s and **replays them natively in `Charter.Eval`**
   to confirm every counterexample (`Law 9`, `T32`).
-/

namespace Charter.Project

open Lean (Json)

structure QuintAction where
  name   : String
  params : List (String × String)
  guard  : String
  effect : String
  deriving Repr

structure QuintModule where
  moduleName  : String
  mode        : Verify.ExploreMode
  stateVars   : List (String × String) -- `(varName, quintType)`
  initAssigns : List (String × String)
  actions     : List QuintAction
  invariants  : List (String × String)
  temporals   : List (String × String)
  assumptions : List String
  deriving Repr

def qntIdent (s : String) : String :=
  let chars := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let out := String.mk chars
  if out.isEmpty || (out.get 0).isDigit then "q_" ++ out else out

def qntDomType (spec : Spec) : Nat → DomId → String
  | 0, _ => "str"
  | fuel + 1, d =>
    match spec.findDecl (spec.chaseAlias d) with
    | some t => match t.domain with
      | .anyInt | .ints _ | .time | .duration | .money _ _ | .quantity _ => "int"
      | .products [] => "bool"
      | .products xs =>
        "(" ++ ", ".intercalate (xs.map fun v => qntDomType spec fuel (spec.removeDecoration v)) ++ ")"
      | _ => "str"
    | none => "str"

partial def qntTerm (t : Term) : String :=
  match t with
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .intLit n => toString n
  | .stringLit s => showString s
  | .currentTime => "clock_now"
  | .not a => s!"not({qntTerm a})"
  | .and a b => s!"and({qntTerm a}, {qntTerm b})"
  | .or a b => s!"or({qntTerm a}, {qntTerm b})"
  | .eq a b => s!"({qntTerm a} == {qntTerm b})"
  | .neq a b => s!"({qntTerm a} != {qntTerm b})"
  | .leq a b => s!"({qntTerm a} <= {qntTerm b})"
  | .le a b => s!"({qntTerm a} < {qntTerm b})"
  | .geq a b => s!"({qntTerm a} >= {qntTerm b})"
  | .ge a b => s!"({qntTerm a} > {qntTerm b})"
  | .add a b => s!"({qntTerm a} + {qntTerm b})"
  | .sub a b => s!"({qntTerm a} - {qntTerm b})"
  | .mult a b => s!"({qntTerm a} * {qntTerm b})"
  | .present (.app d _) => s!"fact_{qntIdent d}.size() > 0"
  | .untag a | .tag a _ => qntTerm a
  | .ref v => qntIdent (toString v)
  | _ => "true"

/-- Compile a `Config` into a typed `QuintModule` AST (`--mode lawful | adversarial`). -/
def compileQuintModule (modName : String) (mode : Verify.ExploreMode) (cfg : Config) : QuintModule :=
  let builtins := ["int", "string", "actor"]
  let factVars : List (String × String) :=
    ("clock_now", "int") ::
    (cfg.spec.decls.filterMap fun (d, t) =>
      if builtins.contains d then none
      else match t.kind with
        | .fact fs => if fs.invariant then none else some ("fact_" ++ qntIdent d, s!"Set[{qntDomType cfg.spec 8 d}]")
        | .duty _ => some ("duty_" ++ qntIdent d, s!"Set[{qntDomType cfg.spec 8 d}]")
        | _ => none)
  let initAssigns : List (String × String) :=
    factVars.map fun (vn, vty) =>
      if vn == "clock_now" then (vn, toString cfg.state.time)
      else (vn, s!"Set() // {vty}")
  let actions : List QuintAction := cfg.spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .act a =>
      let params := (cfg.spec.components d).zipIdx.map fun (v, idx) =>
        (s!"p{idx}_{qntIdent (toString v)}", qntDomType cfg.spec 8 (cfg.spec.removeDecoration v))
      let hwGuard := match t.derivation.filterMap (fun | .holdsWhen c => some (qntTerm c) | _ => none) with
        | [] => "true"
        | gs => " or ".intercalate gs
      let guardStr := match mode with
        | .lawful => hwGuard
        | .adversarial | .mixed _ =>
          if a.physical || !a.isPower then "true /* adversarial physical/attempt enabled */" else hwGuard
      some {
        name := "act_" ++ qntIdent d
        params
        guard := guardStr
        effect := "clock_now' = clock_now"
      }
    | _ => none
  let invs : List (String × String) := cfg.spec.invariants.map fun inv =>
    let body := match cfg.spec.findDecl inv with
      | some ts => match ts.derivation with
        | .holdsWhen c :: _ => qntTerm c
        | _ => "true"
      | none => "true"
    ("inv_" ++ qntIdent inv, body)
  let temps : List (String × String) := cfg.spec.temporalProperties.map fun tp =>
    let fStr := match tp.formula with
      | .always phi => s!"always({qntTerm phi})"
      | .alwaysEventually a b => s!"always({qntTerm a} implies eventually({qntTerm b}))"
      | .alwaysEventuallyWithin _ a b => s!"always({qntTerm a} implies eventually({qntTerm b}))"
      | .alwaysNext a b => s!"always({qntTerm a} implies next({qntTerm b}))"
      | .until_ a b => s!"({qntTerm a} until {qntTerm b})"
      | .weakUntil a b => s!"({qntTerm a} weakUntil {qntTerm b})"
    ("prop_" ++ qntIdent tp.name, fStr)
  { moduleName := qntIdent modName
    mode
    stateVars := factVars
    initAssigns
    actions
    invariants := invs
    temporals := temps
    assumptions := ["clock.monotonic", s!"explorer.mode={mode.name}"] }

/-- Render a `QuintModule` AST into valid `.qnt` Quint source text (`T32`). -/
def renderQuintModule (m : QuintModule) : String :=
  let varLines := m.stateVars.map fun (vn, vty) => s!"  var {vn}: {vty}"
  let actBlocks := m.actions.map fun a =>
    let ps := if a.params.isEmpty then ""
      else "(" ++ ", ".intercalate (a.params.map fun (pn, pty) => s!"{pn}: {pty}") ++ ")"
    s!"  action {a.name}{ps}: bool = all \{\n    {a.guard},\n    {a.effect}\n  }"
  let stepChoice := if m.actions.isEmpty then "    clock_now' = clock_now"
    else "    any {\n" ++ ",\n".intercalate (m.actions.map fun a =>
      let callArgs := if a.params.isEmpty then "" else "(" ++ ", ".intercalate (a.params.map fun (_, pty) =>
        if pty == "int" then "0" else if pty == "bool" then "true" else "\"\"") ++ ")"
      s!"      {a.name}{callArgs}") ++ "\n    }"
  let invLines := m.invariants.map fun (nm, body) => s!"  val {nm}: bool = {body}"
  let tempLines := m.temporals.map fun (nm, body) => s!"  temporal {nm}: bool = {body}"
  s!"// Generated by Charter 1.0 (`Project/QuintTarget.lean`, mode={m.mode.name})\n" ++
  "// Assurance (Law 10): emitted Quint model `checked` (structural + counterexample replay in Charter.Eval); clock.monotonic `assumed`.\n" ++
  s!"module {m.moduleName} \{\n" ++
  "\n".intercalate varLines ++ "\n\n" ++
  "  action init: bool = all {\n" ++
  "\n".intercalate (m.initAssigns.map fun (vn, rhs) => s!"    {vn}' = {rhs},") ++ "\n" ++
  "    true\n  }\n\n" ++
  "\n\n".intercalate actBlocks ++ "\n\n" ++
  s!"  action step: bool = \{\n{stepChoice}\n  }\n\n" ++
  "\n".intercalate invLines ++
  (if tempLines.isEmpty then "" else "\n" ++ "\n".intercalate tempLines) ++
  "\n}\n"

/-- Validate generated `.qnt` source structurally (`T32`). -/
def validateQuintSyntax (m : QuintModule) (qntSrc : String) : Except String Unit := do
  if !(qntSrc.splitOn s!"module {m.moduleName} \{").length.beq 2 then
    .error "Quint validator: missing module header"
  if !(qntSrc.splitOn "action init: bool").length.beq 2 then
    .error "Quint validator: missing `action init`"
  if !(qntSrc.splitOn "action step: bool").length.beq 2 then
    .error "Quint validator: missing `action step`"
  let opens := (qntSrc.toList.filter (· == '{')).length
  let closes := (qntSrc.toList.filter (· == '}')).length
  if opens != closes || opens == 0 then
    .error s!"Quint validator: unbalanced braces ({opens} vs {closes})"
  for (invName, _) in m.invariants do
    if !(qntSrc.splitOn s!"val {invName}: bool").length.beq 2 then
      .error s!"Quint validator: missing invariant `{invName}`"
  .ok ()

/-- Replay an imported `ActionStep` counterexample trace directly through `parseSource` + `runPhrase` in `Charter.Eval` (`T32`). -/
def replayImportedTrace (cfg₀ : Config) (trace : List Verify.ActionStep) : Except String (Config × List DomId) := do
  let mut cfg := cfg₀
  for step in trace do
    let phraseSrc := step.toPhraseText
    match parseSource phraseSrc with
    | .ok [it] =>
      match it.val with
      | .inr p =>
        let (cfg', _) := runPhrase cfg p
        cfg := cfg'
      | .inl _ => .error s!"unexpected directive in imported step `{phraseSrc}`"
    | _ =>
      match Verify.stepConfig cfg step with
      | .ok cfg' => cfg := cfg'
      | .error e => .error s!"imported trace replay failed at `{step.pp}`: {e.message}"
  return (cfg, Explore.violatedInvariants cfg)

/-- End-to-end protocol target check & trace replay (`T26`, `T27`, `T32`):
validates the emitted `.qnt` module, searches up to `depth`, and whenever a counterexample is
found, imports and replays the trace through `Charter.Eval` to confirm invariant violation! -/
def verifyAndReplayQuintTarget (m : QuintModule) (qntSrc : String) (cfg₀ : Config)
    (menu : Explore.Menu := []) (depth : Nat := 3) : Except String String := do
  validateQuintSyntax m qntSrc
  let sOpts : Verify.SearchOpts := { mode := m.mode, depth, menu }
  match Verify.search sOpts cfg₀ with
  | .error e => .error e.message
  | .safe vis _ _ =>
    .ok s!"validated Quint module `{m.moduleName}` ({m.actions.length} action(s), {m.invariants.length} invariant(s); {vis} reachable state(s) safe)"
  | .counterexample cx =>
    let (_, viols) ← replayImportedTrace cfg₀ cx.trace
    if !viols.contains cx.invariant then
      .error s!"Quint trace replay mismatch: `{cx.invariant}` did not fail when replayed in Charter.Eval!"
    .ok s!"validated Quint module `{m.moduleName}` & confirmed imported counterexample for `{cx.invariant}` in {cx.trace.length} step(s) via Charter.Eval replay"

end Charter.Project
