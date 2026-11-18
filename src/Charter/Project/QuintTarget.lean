import Charter.Verify.Explorer
import Charter.Project.SolidityIR

/-!
# Charter.Project.QuintTarget — Quint Protocol Model & Differential Check (`G5.2`, `D28`, `T32`)

Projects the finite/scalar fragment of live `Core.Spec` (`CIR`) into a Quint (`.qnt`) protocol
model (`docs/rfc.md` §9.3, `T26`, `T27`, `T32`):

1. `compileQuintModule` lowers every act, event, and invariant through the same finite guard
   fragment as the Solidity target (`compileSolExpr`, `compileSolEffect`), so an action carries
   its real `Holds when` guard, its `Valid when` condition, and its `Creates` / `Terminates`
   effects with half-open expiry. A construct outside the fragment is refused with `CHR035`
   naming the rule (`017.2`): nothing is dropped and no condition is replaced by `true`.
2. `renderQuintModule` prints the model: one `held_` set and one `exp_` expiry map per fact,
   one action per act or event, clock advances, and one `val` per invariant.
3. `verifyQuintTarget` explores the model and the evaluator in lockstep (`Verify.candidateSteps`
   and `Verify.stepConfig` against `execQuintStep`), comparing the candidate steps, the state,
   and the violated invariants after every step (`Law 9`, tagged `checked`).
-/

namespace Charter.Project

open Lean (Json)

def qntIdent (s : String) : String :=
  let chars := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let out := String.mk chars
  if out.isEmpty || (out.get 0).isDigit then "q_" ++ out else out

/-- A base fact (or duty) held in the model: a `held_` set over its key and an `exp_` map. -/
structure QuintFact where
  dom     : DomId
  keyTys  : List String
  initial : List (List SolVal × Option Int)
  deriving Repr, Inhabited

structure QuintParam where
  name  : String
  ty    : String
  dom   : DomId
  cands : List SolVal
  deriving Repr, Inhabited

/-- An act or event: `lawful` is its `Holds when` and `Conditioned by`; its effects apply iff
`valid` (`D5`); an event is always valid. -/
structure QuintAction where
  dom     : DomId
  isEvent : Bool
  params  : List QuintParam
  lawful  : SolExpr
  valid   : SolExpr
  effects : List SolEffect
  deriving Repr, Inhabited

structure QuintModule where
  moduleName  : String
  mode        : Verify.ExploreMode
  clockInit   : Int
  facts       : List QuintFact
  actions     : List QuintAction
  ticks       : List Int
  invariants  : List (DomId × SolExpr)
  temporals   : List (DomId × SolExpr)
  assumptions : List String
  /-- Fact types that hold instances at the start but that no rule reads or writes and whose
  key is not scalar: they cannot influence the model and are named in its header. -/
  omitted     : List DomId
  deriving Repr, Inhabited

def QuintAction.ident (a : QuintAction) : String :=
  (if a.isEvent then "event_" else "act_") ++ qntIdent a.dom

/-! ## Reading the shared guard IR -/

mutual
/-- Every node of an expression, itself included. -/
def solExprNodes : SolExpr → List SolExpr
  | .litBool b => [.litBool b]
  | .litInt i => [.litInt i]
  | .litBytes32 t => [.litBytes32 t]
  | .paramRef i n => [.paramRef i n]
  | .blockTimestamp => [.blockTimestamp]
  | .factLive d ks => .factLive d ks :: solExprListNodes ks
  | .not a => .not a :: solExprNodes a
  | .and a b => .and a b :: (solExprNodes a ++ solExprNodes b)
  | .or a b => .or a b :: (solExprNodes a ++ solExprNodes b)
  | .ite c t e => .ite c t e :: (solExprNodes c ++ solExprNodes t ++ solExprNodes e)
  | .eq a b => .eq a b :: (solExprNodes a ++ solExprNodes b)
  | .neq a b => .neq a b :: (solExprNodes a ++ solExprNodes b)
  | .lt a b => .lt a b :: (solExprNodes a ++ solExprNodes b)
  | .le a b => .le a b :: (solExprNodes a ++ solExprNodes b)
  | .add a b => .add a b :: (solExprNodes a ++ solExprNodes b)
  | .sub a b => .sub a b :: (solExprNodes a ++ solExprNodes b)
  | .mul a b => .mul a b :: (solExprNodes a ++ solExprNodes b)
  | .div a b => .div a b :: (solExprNodes a ++ solExprNodes b)
  | .mod a b => .mod a b :: (solExprNodes a ++ solExprNodes b)
termination_by structural x => x

def solExprListNodes : List SolExpr → List SolExpr
  | [] => []
  | e :: es => solExprNodes e ++ solExprListNodes es
termination_by structural x => x
end

def solEffectExprs : SolEffect → List SolExpr
  | .createFact _ ks dur? => ks ++ dur?.toList
  | .terminateFact _ ks => ks

def solEffectDom : SolEffect → DomId
  | .createFact d _ _ => d
  | .terminateFact d _ => d

def solEffectKeys : SolEffect → List SolExpr
  | .createFact _ ks _ => ks
  | .terminateFact _ ks => ks

def qntStringOk (s : String) : Bool :=
  s.toList.all fun c => c != '"' && c != '\\' && c != '\n' && c != '\r'

/-- What in an expression the Quint text cannot say exactly, if anything. -/
def qntExprObstacle (e : SolExpr) : Option String :=
  (solExprNodes e).findSome? fun
    | .div _ _ | .mod _ _ => some "integer division or remainder (Quint does not round as Charter's floor division does)"
    | .litBytes32 t => if qntStringOk t then none else some s!"the string {showString t} (a quote, backslash, or line break cannot be written in a Quint string)"
    | _ => none

def qntExprFacts (e : SolExpr) : List DomId :=
  (solExprNodes e).filterMap fun
    | .factLive d _ => some d
    | _ => none

def quintReject (what why : String) : Diagnostic :=
  Diagnostic.error "CHR035" s!"quint target rejects {what}: {why}"

/-- The Quint scalar type of a component, or `none` when it is not a string or an integer. -/
def qntScalarTy (spec : Spec) (d : DomId) : Option String :=
  match spec.findDecl d with
  | some t => match t.domain with
    | .strings _ | .anyString => some "str"
    | .ints _ | .anyInt | .time | .duration | .money _ _ | .quantity _ | .rate => some "int"
    | .products _ => none
  | none => none

def qntKeyTys (spec : Spec) (d : DomId) : Option (List String) :=
  (spec.components d).mapM fun v => qntScalarTy spec (spec.removeDecoration v)

/-- Whether `d` is state the model can hold: a plain closed fact or a duty, never derived. -/
def quintBaseFact (spec : Spec) (d : DomId) : Except String Unit :=
  match spec.findDecl d with
  | none => .error s!"`{d}` is not declared"
  | some t =>
    let plain := match t.kind with
      | .fact fs => !fs.invariant && !fs.evidenced
      | .duty _ => true
      | _ => false
    if !plain then .error s!"`{d}` is not a plain fact or duty"
    else if !t.derivation.isEmpty then .error s!"`{d}` is derived, and the model holds only asserted facts"
    else if !t.isClosed then .error s!"`{d}` is `Open`: an unassigned instance is missing input, which the model cannot represent"
    else if t.restriction.isSome then .error s!"`{d}` is a `Var` or `Function`, which binds to its value rather than to its domain"
    else .ok ()

def isBaseFactKind (spec : Spec) (d : DomId) : Bool :=
  match quintBaseFact spec d with
  | .ok _ => true
  | .error _ => false

def solValMatches (ty : String) : SolVal → Bool
  | .bytes32 _ => ty == "str"
  | .int _ => ty == "int"
  | .bool _ => false

/-- The candidates for one component of an act: every element of an enumerable domain, or the
`explore-domain` menu for one that is not. With neither, the model has no finite universe to
choose from and the act is refused. -/
def quintParam (spec : Spec) (menu : Explore.Menu) (act : DomId) (idx : Nat) (v : Var) :
    Except Diagnostic QuintParam := do
  let d := spec.removeDecoration v
  let some t := spec.findDecl d
    | throw (quintReject s!"`{act}`" s!"its component `{d}` is not declared")
  if !t.domainConstraint.isTrueLit then
    throw (quintReject s!"`{act}`" s!"its component `{d}` has a `Where` constraint")
  if t.restriction.isSome then
    throw (quintReject s!"`{act}`" s!"its component `{d}` is a `Var` or `Function`")
  let name := s!"p{idx}_{qntIdent (toString v)}"
  match t.domain with
  | .strings ss =>
    match ss.find? (fun s => !qntStringOk s) with
    | some bad => throw (quintReject s!"`{act}`" s!"the value {showString bad} of `{d}` cannot be written in a Quint string")
    | none => pure { name, ty := "str", dom := d, cands := ss.map SolVal.bytes32 }
  | .ints is => pure { name, ty := "int", dom := d, cands := is.map SolVal.int }
  | .products _ => throw (quintReject s!"`{act}`" s!"its component `{d}` is itself a product")
  | .rate => throw (quintReject s!"`{act}`" s!"its component `{d}` is a `Rate`, which has no finite candidates")
  | dom =>
    let ty := match dom with | .anyString => "str" | _ => "int"
    match menu.find? (·.1 == d) with
    | none =>
      throw (quintReject s!"`{act}`"
        s!"its component `{d}` is not enumerable; name its candidates with `//! explore-domain: {d} = …`")
    | some (_, vs) =>
      let cands ← vs.mapM fun e =>
        match e with
        | .str s =>
          if ty == "str" && qntStringOk s then pure (SolVal.bytes32 s)
          else throw (quintReject s!"`{act}`" s!"the `explore-domain` value {showString s} does not fit `{d}`")
        | .int i =>
          if ty == "int" then pure (SolVal.int i)
          else throw (quintReject s!"`{act}`" s!"the `explore-domain` value {i} does not fit `{d}`")
        | .prod _ => throw (quintReject s!"`{act}`" s!"an `explore-domain` value for `{d}` is a product")
      pure { name, ty, dom := d, cands }

def quintExpr (spec : Spec) (what : String) (env : List (Var × SolExpr)) (tm : Term) :
    Except Diagnostic SolExpr :=
  match compileSolExpr spec 64 env tm with
  | .error why => throw (quintReject what why)
  | .ok e =>
    match qntExprObstacle e with
    | some why => throw (quintReject what why)
    | none => pure e

/-- Lower one act or event. `holds` and `conds` are its `Holds when` and `Conditioned by`. -/
def compileQuintAction (spec : Spec) (menu : Explore.Menu) (d : DomId) (tspec : TypeSpec)
    (isEvent : Bool) (validWhen : List Term) (effects : List Effect) : Except Diagnostic QuintAction := do
  let what := s!"`{d}`"
  if !tspec.domainConstraint.isTrueLit then
    throw (quintReject what "it has a `Where` constraint on its instances")
  let comps ← match tspec.domain with
    | .products xs => pure xs
    | _ => throw (quintReject what "it is not declared over components")
  let params ← comps.zipIdx.mapM fun (v, idx) => quintParam spec menu d idx v
  let env : List (Var × SolExpr) := (comps.zip params).zipIdx.map fun ((v, p), idx) =>
    (v, SolExpr.paramRef idx p.name)
  let hwTerms := tspec.derivation.filterMap fun
    | .holdsWhen tm => some tm
    | _ => none
  if tspec.derivation.length != hwTerms.length || !tspec.defeasibleRules.isEmpty then
    throw (quintReject what "it is derived by something other than `Holds when`")
  let hw ← hwTerms.mapM (quintExpr spec s!"{what} (`Holds when`)" env)
  let conds ← tspec.conditions.mapM (quintExpr spec s!"{what} (`Conditioned by`)" env)
  let lawful := conds.foldl SolExpr.and (hw.foldr SolExpr.or (.litBool false))
  let vs ← validWhen.mapM (quintExpr spec s!"{what} (`Valid when`)" env)
  let valid := match vs with
    | [] => SolExpr.litBool true
    | v :: rest => rest.foldl SolExpr.and v
  let effLists ← effects.mapM fun eff =>
    match compileSolEffect spec env eff with
    | .ok es => pure es
    | .error why => throw (quintReject s!"{what} (effect)" why)
  let effs := effLists.flatten
  for eff in effs do
    for e in solEffectExprs eff do
      if let some why := qntExprObstacle e then throw (quintReject s!"{what} (effect)" why)
    if let .error why := quintBaseFact spec (solEffectDom eff) then
      throw (quintReject s!"{what} (effect)" why)
  pure { dom := d, isEvent, params, lawful, valid, effects := effs }

def QuintAction.exprs (a : QuintAction) : List SolExpr :=
  a.lawful :: a.valid :: a.effects.flatMap solEffectExprs

/-- Compile a `Config` into a Quint model, or say with `CHR035` what the model cannot carry. -/
def compileQuintModule (modName : String) (mode : Verify.ExploreMode) (menu : Explore.Menu)
    (cfg : Config) : Except Diagnostic QuintModule := do
  let spec := cfg.spec
  let adversarial ← match mode with
    | .lawful => pure false
    | .adversarial => pure true
    | .mixed _ => throw (quintReject "`--mode mixed`" "the model has one step relation; use `lawful` or `adversarial`")
  if spec.hasEpistemicOrDefeasible then
    throw (quintReject "this program"
      "`Evidenced` facts and `Default` / `Exception` rules are judged in three values, which the model does not carry")
  let mut actions : List QuintAction := []
  for (d, t) in spec.decls do
    match t.kind with
    | .act a =>
      let what := s!"`{d}`"
      if !a.exceptUnder.isEmpty then throw (quintReject what "`Except under` is not carried by the model")
      if !a.syncs.isEmpty then throw (quintReject what "`Syncs with` is not carried by the model")
      if a.isAmend || !a.installedNames.isEmpty || !a.repeals.isEmpty then
        throw (quintReject what "an `Amend` changes the rules, and the model has one fixed rule set")
      if !(spec.immunitiesAgainst d).isEmpty || !(spec.protectionsFor d).isEmpty then
        throw (quintReject what "an `Immunity` or `Protection` against it is not carried by the model")
      actions := actions ++ [← compileQuintAction spec menu d t false a.validWhen a.effects]
    | .event e =>
      if adversarial then
        if !e.syncs.isEmpty then throw (quintReject s!"`{d}`" "`Syncs with` is not carried by the model")
        actions := actions ++ [← compileQuintAction spec menu d t true [] e.effects]
    | .immunity im =>
      if !im.against.isEmpty && im.against.contains "Amend" then
        throw (quintReject s!"`{d}`" "an immunity against `Amend` is not carried by the model")
    | _ => pure ()
  -- an act asserted outright (`+act(…)`) is lawful by assignment, which no guard expresses
  for (te, info) in cfg.state.contents do
    if !info.fromSat then
      let triggerable := match spec.findDecl te.2 with
        | some t => (match t.kind with | .act _ | .event _ => true | _ => false)
        | none => false
      if triggerable then
        throw (quintReject s!"`{te.2}`" s!"the instance {te.pp} is asserted in the starting state rather than derived")
  let mut invariants : List (DomId × SolExpr) := []
  for inv in spec.invariants do
    let some t := spec.findDecl inv
      | throw (quintReject s!"invariant `{inv}`" "it is not declared")
    let what := s!"invariant `{inv}`"
    if !(spec.components inv).isEmpty then throw (quintReject what "it has components")
    if !t.conditions.isEmpty then throw (quintReject what "it has a `Conditioned by`")
    let hwTerms := t.derivation.filterMap fun
      | .holdsWhen tm => some tm
      | _ => none
    if t.derivation.length != hwTerms.length then
      throw (quintReject what "it is derived by something other than `When`")
    let hw ← hwTerms.mapM (quintExpr spec what [])
    invariants := invariants ++ [(inv, hw.foldr SolExpr.or (.litBool false))]
  let mut temporals : List (DomId × SolExpr) := []
  for tp in spec.temporalProperties do
    let what := s!"property `{tp.name}`"
    match tp.formula with
    | .always phi => temporals := temporals ++ [(tp.name, ← quintExpr spec what [] phi)]
    | _ => throw (quintReject what "only `Always` over a state condition is carried by the model")
  -- the facts the model holds: everything a rule reads or writes, and whatever starts held
  let allExprs := actions.flatMap QuintAction.exprs ++ invariants.map (·.2) ++ temporals.map (·.2)
  let referenced := (allExprs.flatMap qntExprFacts ++ actions.flatMap (·.effects.map solEffectDom)).eraseDups
  let startHeld := (cfg.state.contents.filterMap fun (te, info) =>
    if info.live cfg.state.time && isBaseFactKind spec te.2 then some te.2 else none).eraseDups
  let mut facts : List QuintFact := []
  let mut omitted : List DomId := []
  for d in (referenced ++ startHeld).eraseDups do
    let isRef := referenced.contains d
    if let .error why := quintBaseFact spec d then throw (quintReject s!"`{d}`" why)
    match qntKeyTys spec d with
    | none =>
      if isRef then throw (quintReject s!"`{d}`" "a component of it is itself a product")
      else omitted := omitted ++ [d]
    | some keyTys =>
      let mut initial : List (List SolVal × Option Int) := []
      for (te, info) in cfg.state.contents do
        if te.2 == d && info.live cfg.state.time then
          let ks? : Option (List SolVal) := match te.1 with
            | .prod ps => ps.mapM (fun (e, _) => SolVal.ofElem e)
            | single => (SolVal.ofElem single).map (· :: [])
          match ks? with
          | some ks =>
            if ks.length == keyTys.length && (ks.zip keyTys).all (fun (k, ty) => solValMatches ty k)
                && ks.all (fun k => match k with | .bytes32 s => qntStringOk s | _ => true) then
              initial := initial ++ [(ks, info.expiry)]
            else throw (quintReject s!"`{d}`" s!"the starting instance {te.pp} does not fit its key")
          | none => throw (quintReject s!"`{d}`" s!"the starting instance {te.pp} does not fit its key")
      facts := facts ++ [{ dom := d, keyTys, initial }]
  let idents := facts.map (fun f => qntIdent f.dom) ++ actions.map QuintAction.ident
    ++ invariants.map (fun p => "inv_" ++ qntIdent p.1)
  if let some dup := idents.find? (fun i => (idents.filter (· == i)).length > 1) then
    throw (quintReject "this program" s!"two names both become `{dup}` in Quint")
  let ticks : List Int := if !adversarial then [] else
    match menu.find? (·.1 == "duration") with
    | some (_, es) => (es.filterMap fun
        | .int delta => if delta > 0 then some delta else none
        | _ => none).eraseDups
    | none => []
  pure {
    moduleName := qntIdent modName
    mode
    clockInit := cfg.state.time
    facts
    actions
    ticks
    invariants
    temporals
    assumptions := ["clock.monotonic", s!"explorer.mode={mode.name}"]
    omitted }

/-! ## Quint text -/

def qntVal : SolVal → String
  | .bool b => if b then "true" else "false"
  | .int i => if i < 0 then s!"({i})" else toString i
  | .bytes32 s => "\"" ++ s ++ "\""

def qntKey : List String → String
  | [] => "true"
  | [k] => k
  | ks => "(" ++ ", ".intercalate ks ++ ")"

def qntKeyTy : List String → String
  | [] => "bool"
  | [t] => t
  | ts => "(" ++ ", ".intercalate ts ++ ")"

mutual
def renderQntExpr : SolExpr → String
  | .litBool b => if b then "true" else "false"
  | .litInt i => if i < 0 then s!"({i})" else toString i
  | .litBytes32 tag => "\"" ++ tag ++ "\""
  | .paramRef _ nm => nm
  | .blockTimestamp => "clock_now"
  | .factLive d ks => s!"live_{qntIdent d}({qntKey (renderQntExprList ks)})"
  | .not a => s!"not({renderQntExpr a})"
  | .and a b => s!"({renderQntExpr a} and {renderQntExpr b})"
  | .or a b => s!"({renderQntExpr a} or {renderQntExpr b})"
  | .ite c t e => s!"(if ({renderQntExpr c}) {renderQntExpr t} else {renderQntExpr e})"
  | .eq a b => s!"({renderQntExpr a} == {renderQntExpr b})"
  | .neq a b => s!"({renderQntExpr a} != {renderQntExpr b})"
  | .lt a b => s!"({renderQntExpr a} < {renderQntExpr b})"
  | .le a b => s!"({renderQntExpr a} <= {renderQntExpr b})"
  | .add a b => s!"({renderQntExpr a} + {renderQntExpr b})"
  | .sub a b => s!"({renderQntExpr a} - {renderQntExpr b})"
  | .mul a b => s!"({renderQntExpr a} * {renderQntExpr b})"
  | .div a b => s!"({renderQntExpr a} / {renderQntExpr b})"
  | .mod a b => s!"({renderQntExpr a} % {renderQntExpr b})"
termination_by structural x => x

def renderQntExprList : List SolExpr → List String
  | [] => []
  | e :: es => renderQntExpr e :: renderQntExprList es
termination_by structural x => x
end

def qntSet (xs : List String) : String := "Set(" ++ ", ".intercalate xs ++ ")"

def qntCall (name : String) (args : List String) : String :=
  if args.isEmpty then name else name ++ "(" ++ ", ".intercalate args ++ ")"

def qntSig (params : List QuintParam) : String :=
  if params.isEmpty then "" else "(" ++ ", ".intercalate (params.map fun p => s!"{p.name}: {p.ty}") ++ ")"

/-- The `held_` and `exp_` right-hand sides for fact `f` after `effs`: terminations first, then
creations in order, so a create beats a terminate of the same instance (`005.3`). -/
def renderFactUpdate (f : QuintFact) (effs : List SolEffect) : String × String :=
  let id := qntIdent f.dom
  let mine := effs.filter (fun e => solEffectDom e == f.dom)
  let key (e : SolEffect) : String := qntKey (renderQntExprList (solEffectKeys e))
  let terms := mine.filterMap fun | .terminateFact _ ks => some (qntKey (renderQntExprList ks)) | _ => none
  let creates := mine.filter fun | .createFact _ _ _ => true | _ => false
  let held0 := if terms.isEmpty then s!"held_{id}" else s!"held_{id}.exclude({qntSet terms})"
  let held := if creates.isEmpty then held0 else s!"{held0}.union({qntSet (creates.map key)})"
  let exp0 := if terms.isEmpty then s!"exp_{id}" else s!"dropKeys(exp_{id}, {qntSet terms})"
  let exp := creates.foldl (fun acc e =>
    match e with
    | .createFact _ _ (some dur) => s!"{acc}.put({key e}, clock_now + {renderQntExpr dur})"
    | _ => s!"dropKeys({acc}, {qntSet [key e]})") exp0
  (held, exp)

def renderQuintAction (m : QuintModule) (a : QuintAction) : String :=
  let args := a.params.map (·.name)
  let sig := qntSig a.params
  let lawfulDef := s!"  def lawful_{qntIdent a.dom}{sig}: bool =\n    {renderQntExpr a.lawful}\n"
  let validDef := s!"  def valid_{qntIdent a.dom}{sig}: bool =\n    {renderQntExpr a.valid}\n"
  let alwaysValid := match a.valid with | .litBool true => true | _ => false
  let gate (rhs unchanged : String) : String :=
    if alwaysValid then rhs else s!"if ({qntCall ("valid_" ++ qntIdent a.dom) args}) {rhs} else {unchanged}"
  let factLines := m.facts.flatMap fun f =>
    let id := qntIdent f.dom
    if a.effects.any (fun e => solEffectDom e == f.dom) then
      let (held, exp) := renderFactUpdate f a.effects
      [s!"    held_{id}' = {gate held s!"held_{id}"},", s!"    exp_{id}' = {gate exp s!"exp_{id}"},"]
    else [s!"    held_{id}' = held_{id},", s!"    exp_{id}' = exp_{id},"]
  let guardLine := match m.mode, a.isEvent with
    | .lawful, false => [s!"    {qntCall ("lawful_" ++ qntIdent a.dom) args},"]
    | _, _ => []
  (if a.isEvent then "" else lawfulDef) ++ (if a.isEvent then "" else validDef) ++
  s!"  action {a.ident}{sig}: bool = all \{\n" ++
  "\n".intercalate (guardLine ++ factLines ++ ["    clock_now' = clock_now,"]) ++ "\n  }"

def renderQuintModule (m : QuintModule) : String :=
  let frame := m.facts.flatMap fun f =>
    let id := qntIdent f.dom
    [s!"    held_{id}' = held_{id},", s!"    exp_{id}' = exp_{id},"]
  let varLines := "  var clock_now: int" :: m.facts.flatMap fun f =>
    let id := qntIdent f.dom
    let kt := qntKeyTy f.keyTys
    [s!"  var held_{id}: Set[{kt}]", s!"  var exp_{id}: {kt} -> int"]
  let liveDefs := m.facts.map fun f =>
    let id := qntIdent f.dom
    s!"  def live_{id}(k: {qntKeyTy f.keyTys}): bool =\n    held_{id}.contains(k) and (not(exp_{id}.keys().contains(k)) or clock_now < exp_{id}.get(k))"
  let initLines := s!"    clock_now' = {qntVal (.int m.clockInit)}," :: m.facts.flatMap fun f =>
    let id := qntIdent f.dom
    let keys := f.initial.map fun (ks, _) => qntKey (ks.map qntVal)
    let exps := f.initial.filterMap fun (ks, u?) => u?.map fun u => s!"{qntKey (ks.map qntVal)} -> {qntVal (.int u)}"
    [s!"    held_{id}' = {qntSet keys},", s!"    exp_{id}' = Map({", ".intercalate exps}),"]
  let tickBlocks := m.ticks.map fun d =>
    s!"  action tick_{d}: bool = all \{\n" ++ "\n".intercalate (frame ++ [s!"    clock_now' = clock_now + {d},"]) ++ "\n  }"
  let branches := (m.actions.filterMap fun a =>
    if a.params.any (·.cands.isEmpty) then none
    else
      let picks := a.params.zipIdx.map fun (p, i) =>
        (s!"n_{a.ident}_{i}", s!"      nondet n_{a.ident}_{i} = oneOf({qntSet (p.cands.map qntVal)})")
      some ("\n".intercalate (picks.map (·.2) ++ [s!"      {qntCall a.ident (picks.map (·.1))}"])))
    ++ m.ticks.map (fun d => s!"      tick_{d}")
  let stepBody := if branches.isEmpty
    then "all {\n" ++ "\n".intercalate (frame ++ ["    clock_now' = clock_now,"]) ++ "\n  }"
    else "any {\n" ++ ",\n".intercalate branches ++ ",\n    }"
  let invLines := m.invariants.map fun (nm, body) => s!"  val inv_{qntIdent nm}: bool =\n    {renderQntExpr body}"
  let allInv := if m.invariants.isEmpty then "true"
    else " and ".intercalate (m.invariants.map fun (nm, _) => "inv_" ++ qntIdent nm)
  let tempLines := m.temporals.map fun (nm, body) => s!"  temporal prop_{qntIdent nm} = always({renderQntExpr body})"
  let omittedLine := if m.omitted.isEmpty then ""
    else s!"// Not modelled (no rule reads or writes them): {", ".intercalate m.omitted}.\n"
  let noCands := m.actions.filter (fun a => a.params.any (·.cands.isEmpty))
  let noCandLine := if noCands.isEmpty then ""
    else s!"// No candidates, so never stepped: {", ".intercalate (noCands.map (·.dom))}.\n"
  s!"// Generated by Charter 1.0 (target=quint, mode={m.mode.name})\n" ++
  "// Assurance (Law 10): this model is `checked` against the evaluator step by step under --verify-output; clock.monotonic is `assumed`.\n" ++
  omittedLine ++ noCandLine ++
  s!"module {m.moduleName} \{\n" ++
  "\n".intercalate varLines ++ "\n\n" ++
  "  pure def dropKeys(m: a -> int, ks: Set[a]): a -> int =\n    m.keys().exclude(ks).mapBy(k => m.get(k))\n\n" ++
  (if liveDefs.isEmpty then "" else "\n".intercalate liveDefs ++ "\n\n") ++
  "  action init: bool = all {\n" ++ "\n".intercalate initLines ++ "\n  }\n\n" ++
  (if m.actions.isEmpty then "" else "\n\n".intercalate (m.actions.map (renderQuintAction m)) ++ "\n\n") ++
  (if tickBlocks.isEmpty then "" else "\n\n".intercalate tickBlocks ++ "\n\n") ++
  s!"  action step: bool = {stepBody}\n\n" ++
  (if invLines.isEmpty then "" else "\n".intercalate invLines ++ "\n") ++
  s!"  val charter_invariants: bool = {allInv}\n" ++
  (if tempLines.isEmpty then "" else "\n".intercalate tempLines ++ "\n") ++
  "}\n"

/-! ## The model's own step relation, and the differential check against the evaluator -/

inductive QuintStep where
  | act (a : QuintAction) (args : List SolVal)
  | tick (delta : Int)
  deriving Inhabited

def cartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (cartesian rest).map (x :: ·)

def solValElem : SolVal → Elem
  | .int i => .int i
  | .bytes32 s => .str s
  | .bool _ => .prod []

/-- The step as the evaluator names it. -/
def QuintStep.toActionStep : QuintStep → Verify.ActionStep
  | .act a args => .trigger (.prod ((args.zip a.params).map fun (v, p) => (solValElem v, p.dom)), a.dom)
  | .tick d => .advanceClock d

/-- The steps the model offers from `st`: every instance in adversarial mode, the lawful ones
in lawful mode, and the clock advances. `none` when a guard does not evaluate. -/
def QuintModule.candidates (m : QuintModule) (st : SolStore) : Option (List QuintStep) := do
  let acts ← m.actions.mapM fun a =>
    (cartesian (a.params.map (·.cands))).filterMapM fun args =>
      match m.mode, a.isEvent with
      | .lawful, false =>
        match execSolExpr st args a.lawful with
        | some (.bool true) => some (some (QuintStep.act a args))
        | some (.bool false) => some none
        | _ => none
      | _, _ => some (some (QuintStep.act a args))
  pure (acts.flatten ++ m.ticks.map QuintStep.tick)

/-- One step of the model: an action's effects apply iff it is valid (`D5`); the clock moves. -/
def execQuintStep (st : SolStore) : QuintStep → Option SolStore
  | .tick d => some { st with blockTimestamp := st.blockTimestamp + d }
  | .act a args =>
    match execSolExpr st args a.valid with
    | some (.bool true) => applySolEffects st args a.effects
    | some (.bool false) => some st
    | _ => none

def sortedStrings (xs : List String) : List String := (xs.toArray.qsort (· < ·)).toList

/-- What holds of the modelled facts in `st`, with expiries, in a canonical order. -/
def QuintModule.view (m : QuintModule) (st : SolStore) : List String :=
  sortedStrings (st.entries.filterMap fun ((d, ks), e) =>
    if m.facts.any (·.dom == d) && e.live st.blockTimestamp then
      some s!"{d}{reprStr ks}{reprStr e.expiry}"
    else none) ++ [s!"@{st.blockTimestamp}"]

def QuintModule.violated (m : QuintModule) (st : SolStore) : List DomId :=
  m.invariants.filterMap fun (nm, body) =>
    match execSolExpr st [] body with
    | some (.bool true) => none
    | _ => some nm

structure QuintDiffResult where
  states   : Nat
  steps    : Nat
  capped   : Bool
  cx       : Option (DomId × List Verify.ActionStep)

/-- Explore the model and the evaluator together to `depth`, failing at the first step where
they offer different candidates, reach different states, or disagree on an invariant. A state
that violates an invariant is recorded and not expanded. -/
def differentialQuint (m : QuintModule) (menu : Explore.Menu) (cfg₀ : Config)
    (depth : Nat) (cap : Nat := 2000) : Except String QuintDiffResult := do
  let ppTrace (tr : List Verify.ActionStep) : String :=
    if tr.isEmpty then "the start" else "; ".intercalate (tr.map (·.pp))
  let agree (tr : List Verify.ActionStep) (cfg : Config) (st : SolStore) : Except String (List DomId) := do
    let ev := m.view (SolStore.ofState cfg.state)
    let md := m.view st
    if ev != md then
      throw s!"state differs after {ppTrace tr}: the evaluator holds {ev}, the model holds {md}"
    let evInv := sortedStrings (Explore.violatedInvariants cfg)
    let mdInv := sortedStrings (m.violated st)
    if evInv != mdInv then
      throw s!"invariants differ after {ppTrace tr}: the evaluator reports {evInv} violated, the model {mdInv}"
    pure evInv
  let st₀ := SolStore.ofState cfg₀.state
  match ← agree [] cfg₀ st₀ with
  | d :: _ => return { states := 1, steps := 0, capped := false, cx := some (d, []) }
  | [] => pure ()
  let mut frontier : List (Config × SolStore × List Verify.ActionStep) := [(cfg₀, st₀, [])]
  let mut seen : List String := [Verify.timedStateKey cfg₀.state]
  let mut steps := 0
  let mut cx : Option (DomId × List Verify.ActionStep) := none
  let mut capped := false
  for _ in [0:depth] do
    let mut next : List (Config × SolStore × List Verify.ActionStep) := []
    for (cfg, st, tr) in frontier do
      let evSteps ← match Verify.candidateSteps m.mode menu cfg with
        | .ok ss => pure ss
        | .error e => throw s!"the evaluator could not list steps after {ppTrace tr}: {e.message}"
      let some mdSteps := m.candidates st
        | throw s!"a guard of the model does not evaluate after {ppTrace tr}"
      let evNames := sortedStrings (evSteps.map (·.pp)).eraseDups
      let mdNames := sortedStrings (mdSteps.map (·.toActionStep.pp)).eraseDups
      if evNames != mdNames then
        throw s!"candidate steps differ after {ppTrace tr}: the evaluator offers {evNames}, the model offers {mdNames}"
      for q in mdSteps do
        let step := q.toActionStep
        let some evStep := evSteps.find? (·.pp == step.pp)
          | throw s!"step {step.pp} is not offered by the evaluator after {ppTrace tr}"
        let cfg' ← match Verify.stepConfig cfg evStep with
          | .ok c => pure c
          | .error e => throw s!"the evaluator could not take {step.pp} after {ppTrace tr}: {e.message}"
        let some st' := execQuintStep st q
          | throw s!"the model could not take {step.pp} after {ppTrace tr}"
        let tr' := tr ++ [evStep]
        steps := steps + 1
        match ← agree tr' cfg' st' with
        | d :: _ => if cx.isNone then cx := some (d, tr')
        | [] =>
          let k := Verify.timedStateKey cfg'.state
          if !seen.contains k then
            if seen.length ≥ cap then capped := true
            else
              seen := k :: seen
              next := next ++ [(cfg', st', tr')]
    frontier := next
  pure { states := seen.length, steps, capped, cx }

/-- Check the emitted text has the model's shape: its header, `init`, `step`, every action and
invariant, and balanced braces. -/
def validateQuintSyntax (m : QuintModule) (qntSrc : String) : Except String Unit := do
  let has (needle : String) : Bool := (qntSrc.splitOn needle).length ≥ 2
  if !has s!"module {m.moduleName} \{" then throw "Quint validator: missing module header"
  if !has "action init: bool" then throw "Quint validator: missing `action init`"
  if !has "action step: bool" then throw "Quint validator: missing `action step`"
  let opens := (qntSrc.toList.filter (· == '{')).length
  let closes := (qntSrc.toList.filter (· == '}')).length
  if opens != closes || opens == 0 then
    throw s!"Quint validator: unbalanced braces ({opens} vs {closes})"
  for a in m.actions do
    if !has s!"action {a.ident}" then throw s!"Quint validator: missing action `{a.ident}`"
  for (inv, _) in m.invariants do
    if !has s!"val inv_{qntIdent inv}: bool" then throw s!"Quint validator: missing invariant `{inv}`"

/-- `--verify-output` for the Quint target (`T26`, `T27`, `T32`): the text has the model's
shape, and the model and the evaluator agree on every step explored to `depth`. A violated
invariant is reported with the trace on which both of them reach it. -/
def verifyQuintTarget (m : QuintModule) (qntSrc : String) (cfg₀ : Config)
    (menu : Explore.Menu := []) (depth : Nat := 3) : Except String String := do
  validateQuintSyntax m qntSrc
  let r ← differentialQuint m menu cfg₀ depth
  let bound := if r.capped then " (state cap reached)" else ""
  match r.cx with
  | none =>
    pure s!"validated Quint module `{m.moduleName}` ({m.actions.length} action(s), {m.invariants.length} invariant(s); {r.states} reachable state(s) safe, {r.steps} step(s) agree with the evaluator{bound})"
  | some (inv, tr) =>
    pure s!"validated Quint module `{m.moduleName}` & confirmed counterexample for `{inv}` in {tr.length} step(s) on both the model and the evaluator ({r.steps} step(s) agree{bound})"

end Charter.Project
