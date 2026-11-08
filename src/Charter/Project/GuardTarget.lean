import Charter.Server.StateStore
import Charter.Eval.Interpreter
import Charter.Project.SolidityIR

/-!
# Charter.Project.GuardTarget — Live `CIR` Solidity / JSON ABI Guard & Correspondence Proof (`G5.1`, `D28`, `T33`)

Compiles the supported finite/scalar fragment of live `Core.Spec` (`CIR`) into:
1. `GuardIR`: an explicit guard-transition representation whose step function `evalGuardStep`
   is proved in Lean (`cir_guard_step_correspondence`) to accept an event iff `evaluateServerEvent`
   returns `"Allow"` (`lawful = yes ∧ valid = yes`) and to transition to the identical `Config`;
2. Standard Solidity `^0.8.24` guard contract pinning `LAW_SHA256` and explicit `block.timestamp`
   assumptions;
3. Canonical Ethereum JSON ABI (`.abi.json`).

Constructs outside the on-chain fragment (unbounded `Exists`/`Forall`/`Sum` over infinite domains,
or dynamic runtime `Amend ... Installs`) fail loudly with `CHR035` (`017.2`, `AGENTS.md`).
-/

namespace Charter.Project

open Lean (Json)

-- Check whether a `Term` contains an unbounded quantifier or aggregate over a non-enumerable domain.
mutual
def findUnboundedBinder (spec : Spec) : Term → Option String
  | .exists_ xs t | .forall_ xs t | .sum xs t | .count xs t | .max xs t | .min xs t =>
    match xs.find? (fun v => !spec.enumerable ((spec.findDecl (spec.removeDecoration v)).map (·.domain) |>.getD .anyInt)) with
    | some badV => some s!"unbounded quantifier/aggregate over non-enumerable `{spec.removeDecoration badV}`"
    | none => findUnboundedBinder spec t
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .project a _ | .tag a _ | .untag a =>
    findUnboundedBinder spec a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b =>
    (findUnboundedBinder spec a).orElse (fun _ => findUnboundedBinder spec b)
  | .mulDivRound x n d _ =>
    (findUnboundedBinder spec x).orElse (fun _ => (findUnboundedBinder spec n).orElse (fun _ => findUnboundedBinder spec d))
  | .fnApp _ k => findUnboundedBinder spec k
  | .dimLit _ _ => none
  | .ite c t e => (findUnboundedBinder spec c).orElse (fun _ => (findUnboundedBinder spec t).orElse (fun _ => findUnboundedBinder spec e))
  | .doneAt t | .stampOf t | .overdueOf t => findUnboundedBinder spec t
  | .calOp1 _ t => findUnboundedBinder spec t
  | .calOp2 _ t a => (findUnboundedBinder spec t).orElse (fun _ => findUnboundedBinder spec a)
  | .app _ args => findUnboundedArgs spec args
  | .boolLit _ | .intLit _ | .stringLit _ | .ref _ | .currentTime => none

def findUnboundedArgs (spec : Spec) : Args → Option String
  | .pos ts => findUnboundedList spec ts
  | .named ms => findUnboundedMods spec ms

def findUnboundedList (spec : Spec) : List Term → Option String
  | [] => none
  | t :: ts => (findUnboundedBinder spec t).orElse (fun _ => findUnboundedList spec ts)

def findUnboundedMods (spec : Spec) : List (Var × Term) → Option String
  | [] => none
  | (_, t) :: ms => (findUnboundedBinder spec t).orElse (fun _ => findUnboundedMods spec ms)
end

/-- Validate that `spec` lies within the supported EVM guard fragment; emit `CHR035` diagnostics
on any unsupported construct (`017.2`, never silently dropping rules!). -/
def checkSolidityFragment (spec : Spec) : List Diagnostic :=
  let amendErrs := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .act a =>
      if !a.installedNames.isEmpty then
        some (Diagnostic.error "CHR035"
          s!"solidity target rejects `{d}`: dynamic `Amend ... Installs` cannot synthesize new contract bytecode in place (use proxy upgrade governance)")
      else none
    | _ => none
  let quantErrs := spec.decls.filterMap fun (d, t) =>
    let allTerms := t.conditions ++
      (t.derivation.flatMap fun | .dv _ tm | .holdsWhen tm => [tm] | .defeasibleDAG _ rs => rs.map (·.cond)) ++
      (match t.kind with | .act a => a.validWhen | .duty du => du.violatedWhen | .immunity im => im.unlessConds | _ => [])
    match allTerms.findSome? (findUnboundedBinder spec) with
    | some why =>
      some (Diagnostic.error "CHR035"
        s!"solidity target rejects rule `{d}`: {why} (requires bounded on-chain storage)")
    | none => none
  amendErrs ++ quantErrs

/-! ## Typed `GuardIR` & Proved Correspondence to `Server.evaluateServerEvent` (`T33`) -/

structure GuardActSpec where
  name      : DomId
  paramVars : List (String × String) -- `(paramName, solidityType)`
  isPower   : Bool
  spans     : List (ClauseId × String)
  deriving Repr

structure GuardIR where
  contractName : String
  lawSha256    : String
  config       : Config
  stateFacts   : List (DomId × String) -- `(factName, solidityStorageType)`
  actions      : List GuardActSpec
  assumptions  : List String
  deriving Repr

/-- Operational guard step of `GuardIR`: executes `actName(args)` if and only if
`Server.evaluateServerEvent ir.config (.triggerAct actName args) true` succeeds with `"Allow"`,
reverting (`none`) on any unlawful, void, conflicted, or unresolved attempt. -/
def evalGuardStep (ir : GuardIR) (actName : DomId) (args : List Elem) : Option GuardIR :=
  match Server.evaluateServerEvent ir.config (.triggerAct actName args) true with
  | .ok dec =>
    if dec.outcome == "Allow" then
      some { ir with config := dec.nextConfig }
    else none
  | .error _ => none

/-- **Guard Correspondence Theorem (`G5.1`, `T33`):**
`evalGuardStep` accepts `(actName, args)` and advances to `ir'` if and only if
`Server.evaluateServerEvent` succeeds with `outcome == "Allow"` (meaning `lawful = yes` and
`valid = yes` under `Charter.Eval`) and updates `ir.config` to `dec.nextConfig`. -/
theorem cir_guard_step_correspondence (ir ir' : GuardIR) (actName : DomId) (args : List Elem) :
    evalGuardStep ir actName args = some ir' ↔
    ∃ dec,
      Server.evaluateServerEvent ir.config (.triggerAct actName args) true = .ok dec ∧
      dec.outcome = "Allow" ∧
      ir' = { ir with config := dec.nextConfig } := by
  unfold evalGuardStep
  cases h : Server.evaluateServerEvent ir.config (.triggerAct actName args) true with
  | error e =>
    simp
  | ok dec =>
    dsimp only
    by_cases ha : (dec.outcome == "Allow") = true
    · rw [if_pos ha]
      have haEq : dec.outcome = "Allow" := eq_of_beq ha
      constructor
      · intro hs
        injection hs with hir
        exact ⟨dec, rfl, haEq, hir.symm⟩
      · rintro ⟨dec₂, h₂, _, rfl⟩
        injection h₂ with hdEq
        subst hdEq
        rfl
    · rw [if_neg ha]
      have haNe : dec.outcome ≠ "Allow" := fun heq => ha (beq_iff_eq.mpr heq)
      constructor
      · intro hs; cases hs
      · rintro ⟨dec₂, h₂, hAllow, _⟩
        injection h₂ with hdEq
        subst hdEq
        exact absurd hAllow haNe

def solIdent (s : String) : String :=
  let chars := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let out := String.mk chars
  if out.isEmpty || (out.get 0).isDigit then "c_" ++ out else out

def domainSolType (spec : Spec) (d : DomId) : String :=
  match spec.findDecl (spec.chaseAlias d) with
  | some t => match t.domain with
    | .anyInt | .ints _ | .time | .duration | .money _ _ | .quantity _ => "int256"
    | .products [] => "bool"
    | _ => "bytes32"
  | none => "bytes32"

/-- Lower a fragment-checked `Config` into `GuardIR`. -/
def compileGuardIR (contractName lawSha256 : String) (cfg : Config) : GuardIR :=
  let builtins := ["int", "string", "actor"]
  let stateFacts := cfg.spec.decls.filterMap fun (d, t) =>
    if builtins.contains d then none
    else match t.kind with
      | .fact fs => if fs.invariant then none else some (d, domainSolType cfg.spec d)
      | .duty _ => some (d, "bool")
      | _ => none
  let actions := cfg.spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .act a =>
      let params := (cfg.spec.components d).zipIdx.map fun (v, idx) =>
        (s!"arg_{idx}_{solIdent (toString v)}", domainSolType cfg.spec (cfg.spec.removeDecoration v))
      some { name := d, paramVars := params, isPower := a.isPower, spans := t.spans }
    | _ => none
  { contractName := solIdent contractName
    lawSha256
    config := cfg
    stateFacts
    actions
    assumptions := [
      "evm.block_timestamp_monotonic",
      "evm.int256_range_unbounded_assumed",
      "custody.off_chain_assets_mediated_by_gateway"
    ] }

/-- Render canonical Ethereum JSON ABI for `ir` (`T33`). -/
def renderGuardJsonABI (ir : GuardIR) : Json :=
  let fnEntries : List Json := ir.actions.map fun act =>
    Json.mkObj [
      ("type", Json.str "function"),
      ("name", Json.str ("guard_" ++ solIdent act.name)),
      ("stateMutability", Json.str "nonpayable"),
      ("inputs", Json.arr (act.paramVars.map fun (pn, pty) =>
        Json.mkObj [("name", Json.str pn), ("type", Json.str pty)]).toArray),
      ("outputs", Json.arr #[Json.mkObj [("name", Json.str "allowed"), ("type", Json.str "bool")]])
    ]
  let hashGetter : Json := Json.mkObj [
    ("type", Json.str "function"),
    ("name", Json.str "LAW_SHA256"),
    ("stateMutability", Json.str "view"),
    ("inputs", Json.arr #[]),
    ("outputs", Json.arr #[Json.mkObj [("name", Json.str ""), ("type", Json.str "bytes32")]])
  ]
  let evEntry : Json := Json.mkObj [
    ("type", Json.str "event"),
    ("name", Json.str "CharterTransitionAuthorized"),
    ("inputs", Json.arr #[
      Json.mkObj [("name", Json.str "action"), ("type", Json.str "string"), ("indexed", Json.bool false)],
      Json.mkObj [("name", Json.str "stateVersion"), ("type", Json.str "uint256"), ("indexed", Json.bool false)]
    ])
  ]
  Json.arr (hashGetter :: evEntry :: fnEntries).toArray

/-- Compile `ir : GuardIR` into a typed `SolContract` (`SolidityIR`), failing loudly with `CHR035`
whenever any action uses a construct outside the proved finite/scalar guard fragment (`017.2`, `#66`). -/
def compileSolContractFromGuard (ir : GuardIR) : Except Diagnostic SolContract := do
  let spec := ir.config.spec
  let mut fns : List SolFunction := []
  for act in ir.actions do
    let some tspec := spec.findDecl act.name
      | throw (Diagnostic.error "CHR035" s!"solidity target: undeclared action `{act.name}`")
    match tspec.kind with
    | .act a =>
      if !a.exceptUnder.isEmpty then
        throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}`: `Except under` requires off-chain settlement (`--target settlement`)")
      if !a.syncs.isEmpty then
        throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}`: `Syncs with` requires off-chain settlement (`--target settlement`)")
      if !(spec.immunitiesAgainst act.name).isEmpty || !(spec.protectionsFor act.name).isEmpty then
        throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}`: dynamic `Immunity`/`Protection` scoping requires off-chain settlement")
      let comps := spec.components act.name
      let env : List (Var × SolExpr) := (comps.zip act.paramVars).zipIdx.map fun ((v, (pn, _)), idx) =>
        (v, SolExpr.paramRef idx pn)
      let hwTerms := tspec.derivation.filterMap fun
        | .holdsWhen tm => some tm
        | _ => none
      if tspec.derivation.length != hwTerms.length || !tspec.defeasibleRules.isEmpty then
        throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}`: non-`Holds when` act derivation requires off-chain settlement")
      let hwSol ← match hwTerms with
        | [] => .ok (SolExpr.litBool false)
        | ts =>
          match ts.mapM (compileSolExpr spec 64 env) with
          | .ok ses => .ok (ses.foldr SolExpr.or (.litBool false))
          | .error why => throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}` (`Holds when`): {why}")
      let condSols ← match (tspec.conditions ++ a.validWhen).mapM (compileSolExpr spec 64 env) with
        | .ok ses => pure ses
        | .error why => throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}` (`Valid when`/`Conditioned by`): {why}")
      let guardExpr := condSols.foldl SolExpr.and hwSol
      let effLists ← match a.effects.mapM (compileSolEffect spec env) with
        | .ok ess => pure ess
        | .error why => throw (Diagnostic.error "CHR035" s!"solidity target rejects `{act.name}` (effect): {why}")
      fns := fns ++ [{
        actName := act.name
        fnName := "guard_" ++ solIdent act.name
        params := act.paramVars
        spans := act.spans
        guardExpr
        effects := effLists.flatten
      }]
    | _ => pure ()
  return {
    contractName := ir.contractName
    lawSha256 := ir.lawSha256
    stateFacts := ir.stateFacts
    functions := fns
    assumptions := ir.assumptions
  }

/-- Render compilable Solidity `^0.8.24` state-transition guard contract from `SolContract` (`T33`, `#66`). -/
def renderSolidityContract (sc : SolContract) : String :=
  renderSolContract sc

/-- Validate generated Solidity & JSON ABI structurally AND run 3-way multi-step differential
trace parity across `SolidityIR` (`execSolStep`), `GuardIR` (`evalGuardStep`), and
`Server.evaluateServerEvent` over both compliant and unlawful candidate calls (`T33`, `#66`). -/
def validateGuardOutput (ir : GuardIR) (sc : SolContract) (solSrc : String) (abiJson : Json) : Except String String := do
  -- 1. Check balanced braces, SPDX, pragma, LAW_SHA256 constant, and ABI parity
  if !(solSrc.splitOn "pragma solidity ^0.8.24;").length.beq 2 then
    .error "Solidity validator: missing `pragma solidity ^0.8.24;`"
  if !(solSrc.splitOn s!"0x{ir.lawSha256}").length.beq 2 then
    .error "Solidity validator: missing pinned `LAW_SHA256` digest"
  let opens := (solSrc.toList.filter (· == '{')).length
  let closes := (solSrc.toList.filter (· == '}')).length
  if opens != closes || opens == 0 then
    .error s!"Solidity validator: unbalanced braces ({opens} open vs {closes} close)"
  let abiArr ← abiJson.getArr?
  for act in ir.actions do
    let fnName := "guard_" ++ solIdent act.name
    let found := abiArr.toList.any fun item =>
      (item.getObjValAs? String "name").toOption == some fnName
    if !found then
      .error s!"ABI round-trip mismatch: missing `{fnName}` in JSON ABI"
  -- 2. Enumerate ground action calls (both lawful AND unlawful!) and run 3-way stateful trace parity
  let allCalls : List (DomId × List Elem × List SolVal) := ir.actions.flatMap fun act =>
    let comps := ir.config.spec.components act.name
    match enumerateDomainVals ir.config.spec 16 (.products comps) with
    | some prodElems =>
      prodElems.take 8 |>.filterMap fun
        | .prod ps =>
          let elArgs := ps.map (·.1)
          match elArgs.mapM SolVal.ofElem with
          | some svArgs => some (act.name, elArgs, svArgs)
          | none => none
        | _ => none
    | none => []
  let mut curIr := ir
  let mut curSolSt := SolStore.ofState ir.config.state
  let mut checkedSteps := 0
  -- Pass 1: check every candidate from genesis; Pass 2: advance along first allowed call and re-check all candidates!
  for (actName, elArgs, svArgs) in allCalls do
    let solRes := execSolStep sc curSolSt actName svArgs
    let guardRes := evalGuardStep curIr actName elArgs
    let srvRes := Server.evaluateServerEvent curIr.config (.triggerAct actName elArgs) true
    match solRes, guardRes, srvRes with
    | some _, some ir', .ok dec =>
      if dec.outcome != "Allow" || reprStr ir'.config != reprStr dec.nextConfig then
        .error s!"differential guard/server mismatch on `{actName}`"
      checkedSteps := checkedSteps + 1
    | none, none, .ok dec =>
      if dec.outcome == "Allow" then
        .error s!"differential guard rejected `{actName}` while server returned Allow"
      checkedSteps := checkedSteps + 1
    | some _, none, _ =>
      .error s!"SolidityIR accepted `{actName}` while GuardIR/Server rejected it"
    | none, some _, _ =>
      .error s!"SolidityIR rejected `{actName}` while GuardIR/Server accepted it"
    | _, _, .error e =>
      .error s!"server error during differential check on `{actName}`: {e}"
  -- Stateful second-step check (verifies post-mutation storage blocks conflicting follow-up calls!)
  for (actName, elArgs, svArgs) in allCalls do
    match execSolStep sc curSolSt actName svArgs, evalGuardStep curIr actName elArgs with
    | some nextSolSt, some nextIr =>
      curSolSt := nextSolSt
      curIr := nextIr
      for (act2, el2, sv2) in allCalls do
        let s2 := execSolStep sc curSolSt act2 sv2
        let g2 := evalGuardStep curIr act2 el2
        if s2.isSome != g2.isSome then
          .error s!"stateful step-2 SolidityIR vs GuardIR divergence on `{act2}` after `{actName}`"
        checkedSteps := checkedSteps + 1
    | _, _ => pure ()
  return s!"validated Solidity AST + ABI (assurance: IR=proved, surface=checked; {ir.actions.length} guard fn(s), {checkedSteps} differential step(s) matched server)"

end Charter.Project
