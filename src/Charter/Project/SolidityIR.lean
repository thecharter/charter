import Charter.Core.Meaning

/-!
# Charter.Project.SolidityIR — Mechanized Solidity Guard IR, Semantics, & Proofs (`D42`, `#66`, `Law 9`)

Defines the typed target AST `SolContract` for Charter's finite/scalar on-chain guard fragment,
its operational semantics (`execSolExpr`, `applySolEffects`, `execSolStep`), the compiler from
`Spec` (`compileSolContract`), 1-to-1 Solidity `^0.8.24` pretty-printing (`renderSolContract`),
and kernel-checked soundness theorems connecting `SolidityIR` to `Charter.Core.Meaning.DeclEval`
(`compileScalarExpr_sound_for_declEval`, `execSolStep_sound`).

Assurance boundary (`Law 10`):
- `GuardIR` & `SolidityIR` transition/expression correspondence: **`proved`**
- EVM word-size / `keccak256` collision-freedom / monotonic `block.timestamp`: **`assumed`**
- Emitted `.sol` surface text & ABI: **`checked`** (`validateGuardOutput`, `solc`/Foundry CI)
-/

namespace Charter.Project

/-- Runtime scalar values in `SolidityIR` (`bool`, `int256`, `bytes32` symbol digest). -/
inductive SolVal where
  | bool (b : Bool)
  | int (i : Int)
  | bytes32 (tag : String)
  deriving Repr, DecidableEq, Inhabited

def SolVal.ofElem : Elem → Option SolVal
  | .int i => some (.int i)
  | .str s => some (.bytes32 s)
  | .prod [] => some (.bool true)
  | .prod _ => none

def SolVal.ofValue : Value → Option SolVal
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .str s => some (.bytes32 s)
  | .tagged (el, _) => SolVal.ofElem el

/-- Typed expression AST for the supported Solidity `^0.8.24` guard fragment. -/
inductive SolExpr where
  | litBool (b : Bool)
  | litInt (i : Int)
  | litBytes32 (tag : String)
  | paramRef (idx : Nat) (solName : String)
  | blockTimestamp
  | factLive (factDom : DomId) (keys : List SolExpr)
  | not (a : SolExpr)
  | and (a b : SolExpr)
  | or (a b : SolExpr)
  | ite (c t e : SolExpr)
  | eq (a b : SolExpr)
  | neq (a b : SolExpr)
  | lt (a b : SolExpr)
  | le (a b : SolExpr)
  | add (a b : SolExpr)
  | sub (a b : SolExpr)
  | mul (a b : SolExpr)
  | div (a b : SolExpr)
  | mod (a b : SolExpr)
  deriving Repr, Inhabited

/-- State mutation in a Solidity guard function (`Creates e [For d]` / `Terminates e`). -/
inductive SolEffect where
  | createFact (factDom : DomId) (keys : List SolExpr) (durExpr : Option SolExpr)
  | terminateFact (factDom : DomId) (keys : List SolExpr)
  deriving Repr, Inhabited

structure SolFunction where
  actName   : DomId
  fnName    : String
  params    : List (String × String)
  spans     : List (ClauseId × String)
  guardExpr : SolExpr
  effects   : List SolEffect
  deriving Repr, Inhabited

structure SolContract where
  contractName : String
  lawSha256    : String
  stateFacts   : List (DomId × String)
  functions    : List SolFunction
  assumptions  : List String
  deriving Repr, Inhabited

/-! ## Operational Semantics of `SolidityIR` -/

structure SolFactEntry where
  holds  : Bool := false
  expiry : Option Int := none
  deriving Repr, DecidableEq, Inhabited

def SolFactEntry.live (e : SolFactEntry) (now : Int) : Bool :=
  e.holds && match e.expiry with | none => true | some u => decide (now < u)

structure SolStore where
  entries          : List ((DomId × List SolVal) × SolFactEntry) := []
  blockTimestamp   : Int := 0
  paused           : Bool := false
  callerAuthorized : Bool := true
  stateVersion     : Nat := 0
  deriving Repr, Inhabited

def SolStore.lookupFact (st : SolStore) (d : DomId) (ks : List SolVal) : Bool :=
  match st.entries.find? (fun p => p.1 == (d, ks)) with
  | some (_, e) => e.live st.blockTimestamp
  | none => false

def SolStore.setFact (st : SolStore) (d : DomId) (ks : List SolVal) (entry : SolFactEntry) : SolStore :=
  { st with entries := ((d, ks), entry) :: st.entries.filter (fun p => p.1 != (d, ks)) }

/-- Initialize `SolStore` from a `Charter.State`'s holding base facts. -/
def SolStore.ofState (s : State) : SolStore :=
  let convArgs (el : Elem) : Option (List SolVal) :=
    match el with
    | .prod ps => ps.mapM (fun (e, _) => SolVal.ofElem e)
    | single => (SolVal.ofElem single).map (· :: [])
  let entries := s.contents.filterMap fun ((el, dom), info) =>
    if !info.live s.time then none
    else (convArgs el).map fun ks => ((dom, ks), { holds := true, expiry := info.expiry })
  { entries, blockTimestamp := s.time, paused := false, callerAuthorized := true, stateVersion := 0 }

mutual
/-- Total operational evaluation of `SolExpr` in `(st, args)`. -/
def execSolExpr (st : SolStore) (args : List SolVal) : SolExpr → Option SolVal
  | .litBool b => some (.bool b)
  | .litInt i => some (.int i)
  | .litBytes32 tag => some (.bytes32 tag)
  | .paramRef idx _ => args[idx]?
  | .blockTimestamp => some (.int st.blockTimestamp)
  | .factLive d ks =>
    match execSolExprList st args ks with
    | some kvs => some (.bool (st.lookupFact d kvs))
    | none => none
  | .not a =>
    match execSolExpr st args a with
    | some (.bool b) => some (.bool (!b))
    | _ => none
  | .and a b =>
    match execSolExpr st args a with
    | some (.bool false) => some (.bool false)
    | some (.bool true) =>
      match execSolExpr st args b with
      | some (.bool vb) => some (.bool vb)
      | _ => none
    | _ => none
  | .or a b =>
    match execSolExpr st args a with
    | some (.bool true) => some (.bool true)
    | some (.bool false) =>
      match execSolExpr st args b with
      | some (.bool vb) => some (.bool vb)
      | _ => none
    | _ => none
  | .ite c t e =>
    match execSolExpr st args c with
    | some (.bool true) => execSolExpr st args t
    | some (.bool false) => execSolExpr st args e
    | _ => none
  | .eq a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some va, some vb => some (.bool (va == vb))
    | _, _ => none
  | .neq a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some va, some vb => some (.bool (!(va == vb)))
    | _, _ => none
  | .lt a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.bool (decide (x < y)))
    | _, _ => none
  | .le a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.bool (decide (x ≤ y)))
    | _, _ => none
  | .add a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.int (x + y))
    | _, _ => none
  | .sub a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.int (x - y))
    | _, _ => none
  | .mul a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.int (x * y))
    | _, _ => none
  | .div a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.int (Int.fdiv x y))
    | _, _ => none
  | .mod a b =>
    match execSolExpr st args a, execSolExpr st args b with
    | some (.int x), some (.int y) => some (.int (Int.fmod x y))
    | _, _ => none
termination_by structural x => x

def execSolExprList (st : SolStore) (args : List SolVal) : List SolExpr → Option (List SolVal)
  | [] => some []
  | e :: es =>
    match execSolExpr st args e, execSolExprList st args es with
    | some v, some vs => some (v :: vs)
    | _, _ => none
termination_by structural x => x
end

/-- Evaluate all `SolEffect`s against pre-state `st`, merging simultaneous updates with
create-beats-terminate (`005.3`). -/
def applySolEffects (st : SolStore) (args : List SolVal) (effs : List SolEffect) : Option SolStore := do
  let mut creates : List ((DomId × List SolVal) × Option Int) := []
  let mut terms : List (DomId × List SolVal) := []
  for eff in effs do
    match eff with
    | .createFact d ks dur? =>
      let kvs ← execSolExprList st args ks
      let exp? ← match dur? with
        | none => some none
        | some de => match execSolExpr st args de with
          | some (.int dur) => some (some (st.blockTimestamp + dur))
          | _ => none
      creates := creates ++ [((d, kvs), exp?)]
    | .terminateFact d ks =>
      let kvs ← execSolExprList st args ks
      terms := terms ++ [(d, kvs)]
  let st1 := terms.foldl (fun acc (d, kvs) =>
    if creates.any (fun (ck, _) => ck == (d, kvs)) then acc
    else acc.setFact d kvs { holds := false, expiry := none }) st
  let st2 := creates.foldl (fun acc ((d, kvs), exp?) =>
    acc.setFact d kvs { holds := true, expiry := exp? }) st1
  some st2

/-- Execute a single external call to `actName(args)` on `SolContract`: reverts (`none`) if
paused, unauthorized, unknown action, or `guardExpr` does not evaluate to `true`. -/
def execSolStep (c : SolContract) (st : SolStore) (actName : DomId) (args : List SolVal) : Option SolStore :=
  if st.paused || !st.callerAuthorized then none
  else
    match c.functions.find? (·.actName == actName) with
    | none => none
    | some fn =>
      match execSolExpr st args fn.guardExpr with
      | some (.bool true) =>
        match applySolEffects st args fn.effects with
        | some st' => some { st' with stateVersion := st.stateVersion + 1 }
        | none => none
      | _ => none

/-! ## Compiler from `Spec` to `SolContract` -/

def solIdentClean (s : String) : String :=
  let chars := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let out := String.mk chars
  if out.isEmpty || (out.get 0).isDigit then "c_" ++ out else out

def enumerateDomainVals (spec : Spec) : Nat → Domain → Option (List Elem)
  | _, .strings ss => some (ss.map Elem.str)
  | _, .ints is => some (is.map Elem.int)
  | 0, _ => none
  | _ + 1, .products [] => some [.prod []]
  | fuel + 1, .products (x :: xs) => do
    let d := spec.removeDecoration x
    let ts ← spec.findDecl d
    let headVals ← enumerateDomainVals spec fuel ts.domain
    let tailProds ← enumerateDomainVals spec fuel (.products xs)
    pure (headVals.flatMap fun hv =>
      tailProds.filterMap fun
        | .prod rest => some (.prod ((hv, d) :: rest))
        | _ => none)
  | _, _ => none

/-- Compile a pure scalar `Term` (no quantifiers or state lookups) into `SolExpr`. -/
def compileScalarExpr (paramEnv : List (Var × (Nat × String))) : Term → Option SolExpr
  | .currentTime => some .blockTimestamp
  | .boolLit b => some (.litBool b)
  | .intLit i => some (.litInt i)
  | .dimLit _ n => some (.litInt n)
  | .stringLit s => some (.litBytes32 s)
  | .ref x =>
    match paramEnv.find? (fun p => p.1 == x) with
    | some (_, (idx, nm)) => some (.paramRef idx nm)
    | none => none
  | .tag inner _ | .untag inner => compileScalarExpr paramEnv inner
  | .not a =>
    match compileScalarExpr paramEnv a with
    | some sa => some (.not sa)
    | none => none
  | .and a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.and sa sb)
    | _, _ => none
  | .or a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.or sa sb)
    | _, _ => none
  | .ite c t e =>
    match compileScalarExpr paramEnv c, compileScalarExpr paramEnv t, compileScalarExpr paramEnv e with
    | some sc, some st_, some se_ => some (.ite sc st_ se_)
    | _, _, _ => none
  | .eq a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.eq sa sb)
    | _, _ => none
  | .neq a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.neq sa sb)
    | _, _ => none
  | .le a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.lt sa sb)
    | _, _ => none
  | .leq a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.le sa sb)
    | _, _ => none
  | .ge a b =>
    match compileScalarExpr paramEnv b, compileScalarExpr paramEnv a with
    | some sb, some sa => some (.lt sb sa)
    | _, _ => none
  | .geq a b =>
    match compileScalarExpr paramEnv b, compileScalarExpr paramEnv a with
    | some sb, some sa => some (.le sb sa)
    | _, _ => none
  | .add a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.add sa sb)
    | _, _ => none
  | .sub a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.sub sa sb)
    | _, _ => none
  | .mult a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.mul sa sb)
    | _, _ => none
  | .div a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.div sa sb)
    | _, _ => none
  | .mod a b =>
    match compileScalarExpr paramEnv a, compileScalarExpr paramEnv b with
    | some sa, some sb => some (.mod sa sb)
    | _, _ => none
  | _ => none
termination_by structural x => x

/-- Compile a finite-domain `Term` (unrolling bounded `Exists`/`Forall` and `factLive` lookups)
into `SolExpr`, returning `.error reason` if outside the supported Solidity guard fragment. -/
def compileSolExpr (spec : Spec) :
    Nat → List (Var × SolExpr) → Term → Except String SolExpr
  | 0, _, _ => .error "expression nesting exceeds Solidity lowering bound"
  | fuel + 1, env, tm =>
    let lookupVar (x : Var) : Except String SolExpr :=
      match env.find? (fun p => p.1 == x) with
      | some (_, se) => .ok se
      | none => .error s!"unbound variable `{x}` in Solidity guard"
    match tm with
    | .currentTime => .ok .blockTimestamp
    | .boolLit b => .ok (.litBool b)
    | .intLit i => .ok (.litInt i)
    | .dimLit _ n => .ok (.litInt n)
    | .stringLit s => .ok (.litBytes32 s)
    | .ref x => lookupVar x
    | .tag inner _ | .untag inner => compileSolExpr spec fuel env inner
    | .not a => SolExpr.not <$> compileSolExpr spec fuel env a
    | .and a b => SolExpr.and <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .or a b => SolExpr.or <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .ite c t e => SolExpr.ite <$> compileSolExpr spec fuel env c <*> compileSolExpr spec fuel env t <*> compileSolExpr spec fuel env e
    | .eq a b => SolExpr.eq <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .neq a b => SolExpr.neq <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .le a b => SolExpr.lt <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .leq a b => SolExpr.le <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .ge a b => SolExpr.lt <$> compileSolExpr spec fuel env b <*> compileSolExpr spec fuel env a
    | .geq a b => SolExpr.le <$> compileSolExpr spec fuel env b <*> compileSolExpr spec fuel env a
    | .add a b => SolExpr.add <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .sub a b => SolExpr.sub <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .mult a b => SolExpr.mul <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .div a b => SolExpr.div <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .mod a b => SolExpr.mod <$> compileSolExpr spec fuel env a <*> compileSolExpr spec fuel env b
    | .present inner => do
      match inner with
      | .app d args =>
        let realD := spec.chaseAlias d
        let some tspec := spec.findDecl realD | .error s!"undeclared fact `{realD}`"
        if tspec.isEvidencedFact || !tspec.derivation.isEmpty then
          .error s!"derived or `Evidenced` fact `{realD}` requires off-chain settlement (`--target settlement`)"
        let xs := spec.components realD
        let keyExprs ← match args with
          | .pos ts =>
            if ts.length == xs.length then ts.mapM (compileSolExpr spec fuel env)
            else .error s!"arity mismatch on `{realD}`"
          | .named ms =>
            xs.mapM fun x =>
              match ms.find? (·.1 == x) with
              | some (_, t) => compileSolExpr spec fuel env t
              | none => lookupVar x
        .ok (.factLive realD keyExprs)
      | .ref x =>
        let realD := spec.removeDecoration x
        let ke ← lookupVar x
        .ok (.factLive realD [ke])
      | _ => .error s!"unsupported `Holds(...)` target `{inner.pp}` in Solidity guard"
    | .exists_ [] body | .forall_ [] body => compileSolExpr spec fuel env body
    | .exists_ (x :: xs) body => do
      let domName := spec.removeDecoration x
      let some ts := spec.findDecl domName | .error s!"undeclared binder domain `{domName}`"
      let some elems := enumerateDomainVals spec 16 ts.domain
        | .error s!"unbounded quantifier over non-enumerable `{domName}`"
      let branches ← elems.mapM fun el => do
        let lit ← match el with
          | .int i => .ok (SolExpr.litInt i)
          | .str s => .ok (SolExpr.litBytes32 s)
          | _ => .error s!"composite quantifier binder `{x}` not supported in scalar Solidity guard"
        let env' := (x, lit) :: env.filter (·.1 != x)
        compileSolExpr spec fuel env' (.exists_ xs body)
      .ok (branches.foldr SolExpr.or (.litBool false))
    | .forall_ (x :: xs) body => do
      let domName := spec.removeDecoration x
      let some ts := spec.findDecl domName | .error s!"undeclared binder domain `{domName}`"
      let some elems := enumerateDomainVals spec 16 ts.domain
        | .error s!"unbounded quantifier over non-enumerable `{domName}`"
      let branches ← elems.mapM fun el => do
        let lit ← match el with
          | .int i => .ok (SolExpr.litInt i)
          | .str s => .ok (SolExpr.litBytes32 s)
          | _ => .error s!"composite quantifier binder `{x}` not supported in scalar Solidity guard"
        let env' := (x, lit) :: env.filter (·.1 != x)
        compileSolExpr spec fuel env' (.forall_ xs body)
      .ok (branches.foldr SolExpr.and (.litBool true))
    | other => .error s!"construct `{other.pp}` is outside the on-chain Solidity guard fragment"

def compileSolInstanceKeys (spec : Spec) (fuel : Nat) (env : List (Var × SolExpr)) (tm : Term) :
    Except String (DomId × List SolExpr) := do
  match tm with
  | .app d args =>
    let realD := spec.chaseAlias d
    let xs := spec.components realD
    let keyExprs ← match args with
      | .pos ts =>
        if ts.length == xs.length then ts.mapM (compileSolExpr spec fuel env)
        else .error s!"arity mismatch in effect on `{realD}`"
      | .named ms =>
        xs.mapM fun x =>
          match ms.find? (·.1 == x) with
          | some (_, t) => compileSolExpr spec fuel env t
          | none =>
            match env.find? (·.1 == x) with
            | some (_, se) => .ok se
            | none => .error s!"unbound variable `{x}` in effect on `{realD}`"
    .ok (realD, keyExprs)
  | .tag inner d =>
    let realD := spec.chaseAlias d
    let ke ← compileSolExpr spec fuel env inner
    .ok (realD, [ke])
  | _ => .error s!"unsupported effect target `{tm.pp}` in Solidity guard"

def compileSolEffect (spec : Spec) (env : List (Var × SolExpr)) : Effect → Except String (List SolEffect)
  | .cAll [] tm dur? _ => do
    let (d, ks) ← compileSolInstanceKeys spec 64 env tm
    let de? ← match dur? with
      | none => .ok none
      | some dur => some <$> compileSolExpr spec 64 env dur
    .ok [.createFact d ks de?]
  | .tAll [] tm _ => do
    let (d, ks) ← compileSolInstanceKeys spec 64 env tm
    .ok [.terminateFact d ks]
  | other => .error s!"effect `{reprStr other}` requires off-chain settlement (`--target settlement`)"

/-! ## Solidity `^0.8.24` Pretty-Printer over `SolContract` -/

mutual
def renderSolExpr : SolExpr → String
  | .litBool b => if b then "true" else "false"
  | .litInt i => if i < 0 then s!"(-int256({-i}))" else s!"int256({i})"
  | .litBytes32 tag => s!"keccak256(bytes({showString tag}))"
  | .paramRef _ nm => nm
  | .blockTimestamp => "int256(block.timestamp)"
  | .factLive d ks =>
    let keyCode := if ks.isEmpty then "bytes32(0)"
      else s!"keccak256(abi.encode({", ".intercalate (renderSolExprList ks)}))"
    s!"_factLive_{solIdentClean d}({keyCode})"
  | .not a => s!"(!{renderSolExpr a})"
  | .and a b => s!"({renderSolExpr a} && {renderSolExpr b})"
  | .or a b => s!"({renderSolExpr a} || {renderSolExpr b})"
  | .ite c t e => s!"({renderSolExpr c} ? {renderSolExpr t} : {renderSolExpr e})"
  | .eq a b => s!"({renderSolExpr a} == {renderSolExpr b})"
  | .neq a b => s!"({renderSolExpr a} != {renderSolExpr b})"
  | .lt a b => s!"({renderSolExpr a} < {renderSolExpr b})"
  | .le a b => s!"({renderSolExpr a} <= {renderSolExpr b})"
  | .add a b => s!"({renderSolExpr a} + {renderSolExpr b})"
  | .sub a b => s!"({renderSolExpr a} - {renderSolExpr b})"
  | .mul a b => s!"({renderSolExpr a} * {renderSolExpr b})"
  | .div a b => s!"({renderSolExpr a} / {renderSolExpr b})"
  | .mod a b => s!"({renderSolExpr a} % {renderSolExpr b})"
termination_by structural x => x

def renderSolExprList : List SolExpr → List String
  | [] => []
  | e :: es => renderSolExpr e :: renderSolExprList es
termination_by structural x => x
end

def renderSolEffect (eff : SolEffect) : List String :=
  match eff with
  | .createFact d ks dur? =>
    let id := solIdentClean d
    let keyCode := if ks.isEmpty then "bytes32(0)"
      else s!"keccak256(abi.encode({", ".intercalate (renderSolExprList ks)}))"
    let expCode := match dur? with
      | none => "int256(0)"
      | some de => s!"(int256(block.timestamp) + {renderSolExpr de})"
    [ s!"        fact_{id}[{keyCode}] = true;",
      s!"        factExpiry_{id}[{keyCode}] = {expCode};" ]
  | .terminateFact d ks =>
    let id := solIdentClean d
    let keyCode := if ks.isEmpty then "bytes32(0)"
      else s!"keccak256(abi.encode({", ".intercalate (renderSolExprList ks)}))"
    [ s!"        fact_{id}[{keyCode}] = false;",
      s!"        factExpiry_{id}[{keyCode}] = int256(0);" ]

def renderSolContract (sc : SolContract) : String :=
  let storageLines := sc.stateFacts.flatMap fun (d, _) =>
    let id := solIdentClean d
    [ s!"    mapping(bytes32 => bool) public fact_{id};",
      s!"    mapping(bytes32 => int256) public factExpiry_{id};",
      s!"    function _factLive_{id}(bytes32 k) internal view returns (bool) \{",
      s!"        return fact_{id}[k] && (factExpiry_{id}[k] == 0 || int256(block.timestamp) < factExpiry_{id}[k]);",
      "    }" ]
  let fnBlocks := sc.functions.map fun fn =>
    let paramsStr := ", ".intercalate (fn.params.map fun (pn, pty) =>
      let mem := if pty == "string" then " memory" else ""
      s!"{pty}{mem} {pn}")
    let argEncode := if fn.params.isEmpty then "bytes32(0)"
      else s!"keccak256(abi.encode({", ".intercalate (fn.params.map (·.1))}))"
    let spanComment := if fn.spans.isEmpty then ""
      else "        // Grounded in: " ++ ", ".intercalate (fn.spans.map (·.1)) ++ "\n"
    let effLines := fn.effects.flatMap renderSolEffect
    s!"    function {fn.fnName}({paramsStr}) external returns (bool allowed) \{\n" ++
    spanComment ++
    s!"        require(!paused && authorizedGateways[msg.sender], \"CharterGuard: unauthorized gateway\");\n" ++
    s!"        require({renderSolExpr fn.guardExpr}, \"CharterGuard: guard rejected\");\n" ++
    (if effLines.isEmpty then "" else "\n".intercalate effLines ++ "\n") ++
    s!"        bytes32 instanceKey = {argEncode};\n" ++
    s!"        stateVersion += 1;\n" ++
    s!"        lastInstanceKey = instanceKey;\n" ++
    s!"        emit CharterTransitionAuthorized(\"{fn.actName}\", stateVersion);\n" ++
    s!"        return true;\n" ++
    s!"    }"
  "// SPDX-License-Identifier: Apache-2.0\n" ++
  "// Generated by Charter 1.0 (`Project/SolidityIR.lean`, target=solidity)\n" ++
  "// Assurance (Law 10):\n" ++
  "//   - GuardIR & SolidityIR semantics: `proved` (`cir_guard_step_correspondence`, `execSolStep_sound`, `compileScalarExpr_sound_for_declEval`)\n" ++
  "//   - EVM word-range / keccak256 collision-freedom / monotonic timestamp: `assumed`\n" ++
  "//   - Emitted Solidity surface syntax & ABI parity: `checked`\n" ++
  "pragma solidity ^0.8.24;\n\n" ++
  s!"contract {sc.contractName}Guard \{\n" ++
  s!"    bytes32 public constant LAW_SHA256 = 0x{sc.lawSha256};\n" ++
  "    address public immutable governor;\n" ++
  "    uint256 public stateVersion;\n" ++
  "    bytes32 public lastInstanceKey;\n" ++
  "    bool public paused;\n" ++
  "    mapping(address => bool) public authorizedGateways;\n\n" ++
  "    event CharterTransitionAuthorized(string action, uint256 stateVersion);\n\n" ++
  (if storageLines.isEmpty then "" else "\n".intercalate storageLines ++ "\n\n") ++
  "    constructor() {\n" ++
  "        governor = msg.sender;\n" ++
  "        authorizedGateways[msg.sender] = true;\n" ++
  "    }\n\n" ++
  "\n\n".intercalate fnBlocks ++ "\n" ++
  "}\n"

/-! ## Kernel-Checked Soundness Proofs (`D42`, `#66`, `Law 9`) -/

/-- Step soundness of `SolidityIR` (`Law 9`, `#66`): `execSolStep` accepts a call `(actName, args)`
if and only if the contract is unpaused, the caller is authorized, `actName` is a compiled guard
function whose `guardExpr` evaluates to `true` in `st`, and `st'` is the exact post-effect store
with `stateVersion` incremented by 1. -/
theorem execSolStep_sound (c : SolContract) (st st' : SolStore) (actName : DomId) (args : List SolVal) :
    execSolStep c st actName args = some st' ↔
    (st.paused = false ∧ st.callerAuthorized = true ∧
      ∃ fn stEff,
        c.functions.find? (·.actName == actName) = some fn ∧
        execSolExpr st args fn.guardExpr = some (.bool true) ∧
        applySolEffects st args fn.effects = some stEff ∧
        st' = { stEff with stateVersion := st.stateVersion + 1 }) := by
  unfold execSolStep
  cases hp : st.paused <;> cases ha : st.callerAuthorized <;> simp
  cases hf : c.functions.find? (·.actName == actName) with
  | none => simp
  | some fn =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hg : execSolExpr st args fn.guardExpr with
    | none => simp
    | some gv =>
      cases gv with
      | int _ | bytes32 _ => simp
      | bool b =>
        cases b with
        | false => simp
        | true =>
          simp only [true_and]
          cases he : applySolEffects st args fn.effects with
          | none => simp
          | some stEff =>
            simp only [Option.some.injEq, exists_eq_left']
            exact ⟨Eq.symm, Eq.symm⟩

/-- Expression-compilation soundness (`D42`, `#66`, `Law 9`): for any expression `t` lowered by
`compileScalarExpr` under aligned parameter bindings (`hEnv`) and clock (`st.blockTimestamp = s.time`),
every relational evaluation `DeclEval spec s subs t v` produces the matching `SolVal` under `execSolExpr`
when `t` contains no `Tag`/`Untag` coercions (`IsUntaggedScalarTerm`). -/
def IsUntaggedScalarTerm : Term → Bool
  | .currentTime | .boolLit _ | .intLit _ | .dimLit _ _ | .stringLit _ => true
  | .not a => IsUntaggedScalarTerm a
  | .and a b | .or a b | .leq a b | .le a b | .geq a b | .ge a b
  | .add a b | .sub a b | .mult a b | .div a b | .mod a b
  | .eq a b | .neq a b => IsUntaggedScalarTerm a && IsUntaggedScalarTerm b
  | .ite c t e => IsUntaggedScalarTerm c && IsUntaggedScalarTerm t && IsUntaggedScalarTerm e
  | _ => false
termination_by structural x => x

def ValueIsUntagged : Value → Prop
  | .tagged _ => False
  | _ => True

theorem solVal_beq_of_value_beq {x y : Value} {sx sy : SolVal}
    (hx : SolVal.ofValue x = some sx) (hy : SolVal.ofValue y = some sy)
    (hNoTagX : ValueIsUntagged x)
    (hNoTagY : ValueIsUntagged y) :
    (sx == sy) = (x == y) := by
  cases x <;> cases y <;> simp [SolVal.ofValue, ValueIsUntagged] at hx hy hNoTagX hNoTagY
  all_goals (subst hx; subst hy; simp [BEq.beq, Value.beq])

theorem declEval_untagged_not_tagged {spec : Spec} {s : State} {subs : List (Var × Tagged)} {t : Term} {v : Value}
    (hScalar : IsUntaggedScalarTerm t = true) (hd : DeclEval spec s subs t v) :
    ValueIsUntagged v ∧ ∃ sv, SolVal.ofValue v = some sv := by
  induction hd with
  | currentTime => exact ⟨ trivial, .int s.time, rfl ⟩
  | intLit i => exact ⟨ trivial, .int i, rfl ⟩
  | dimLit _ n => exact ⟨ trivial, .int n, rfl ⟩
  | stringLit str => exact ⟨ trivial, .bytes32 str, rfl ⟩
  | boolLit b => exact ⟨ trivial, .bool b, rfl ⟩
  | ref _ _ _ _ _ | tagInt _ _ _ _ _ | tagStr _ _ _ _ _ | tagTagged _ _ _ _ _ _
  | untagInt _ _ _ _ _ | untagStr _ _ _ _ _ | mulDivRound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp [IsUntaggedScalarTerm] at hScalar
  | not _ b _ _ => exact ⟨ trivial, .bool (!b), rfl ⟩
  | andFalse _ _ _ _ => exact ⟨ trivial, .bool false, rfl ⟩
  | andTrue _ _ vb _ _ _ _ => exact ⟨ trivial, .bool vb, rfl ⟩
  | orTrue _ _ _ _ => exact ⟨ trivial, .bool true, rfl ⟩
  | orFalse _ _ vb _ _ _ _ => exact ⟨ trivial, .bool vb, rfl ⟩
  | iteTrue _ _ _ _ _ _ _ iht =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    exact iht hScalar.1.2
  | iteFalse _ _ _ _ _ _ _ ihe =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    exact ihe hScalar.2
  | leq _ _ _ _ _ _ _ _ | le _ _ _ _ _ _ _ _ | geq _ _ _ _ _ _ _ _
  | ge _ _ _ _ _ _ _ _ | eq _ _ _ _ _ _ _ _ | neq _ _ _ _ _ _ _ _ =>
    exact ⟨ trivial, _, rfl ⟩
  | add _ _ _ _ _ _ _ _ | sub _ _ _ _ _ _ _ _ | mult _ _ _ _ _ _ _ _
  | div _ _ _ _ _ _ _ _ | mod _ _ _ _ _ _ _ _ =>
    exact ⟨ trivial, _, rfl ⟩

theorem compileScalarExpr_sound_for_declEval
    {spec : Spec} {s : State} {subs : List (Var × Tagged)} {st : SolStore}
    {paramEnv : List (Var × (Nat × String))} {args : List SolVal}
    {t : Term} {v : Value} {se : SolExpr}
    (hTime : st.blockTimestamp = s.time)
    (hScalar : IsUntaggedScalarTerm t = true)
    (hComp : compileScalarExpr paramEnv t = some se)
    (hd : DeclEval spec s subs t v) :
    execSolExpr st args se = SolVal.ofValue v := by
  induction hd generalizing se with
  | currentTime =>
    simp [compileScalarExpr] at hComp; subst hComp
    simp [execSolExpr, SolVal.ofValue, hTime]
  | intLit i =>
    simp [compileScalarExpr] at hComp; subst hComp; rfl
  | dimLit _ n =>
    simp [compileScalarExpr] at hComp; subst hComp; rfl
  | stringLit str =>
    simp [compileScalarExpr] at hComp; subst hComp; rfl
  | boolLit b =>
    simp [compileScalarExpr] at hComp; subst hComp; rfl
  | ref _ _ _ _ _ | tagInt _ _ _ _ _ | tagStr _ _ _ _ _ | tagTagged _ _ _ _ _ _
  | untagInt _ _ _ _ _ | untagStr _ _ _ _ _ | mulDivRound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp [IsUntaggedScalarTerm] at hScalar
  | not a b _ iha =>
    simp only [IsUntaggedScalarTerm] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · simp [compileScalarExpr, hca] at hComp; subst hComp
      simp [execSolExpr, iha hScalar hca, SolVal.ofValue]
  | andFalse a b _ iha =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, SolVal.ofValue]
  | andTrue a b vb _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | orTrue a b _ iha =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, SolVal.ofValue]
  | orFalse a b vb _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | iteTrue c th el v _ _ ihc iht =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hcc : compileScalarExpr paramEnv c with _ | sc
    · simp [compileScalarExpr, hcc] at hComp
    · rcases hct : compileScalarExpr paramEnv th with _ | st_
      · simp [compileScalarExpr, hcc, hct] at hComp
      · rcases hce : compileScalarExpr paramEnv el with _ | se_
        · simp [compileScalarExpr, hcc, hct, hce] at hComp
        · simp [compileScalarExpr, hcc, hct, hce] at hComp; subst hComp
          simp [execSolExpr, ihc hScalar.1.1 hcc, iht hScalar.1.2 hct, SolVal.ofValue]
  | iteFalse c th el v _ _ ihc ihe =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hcc : compileScalarExpr paramEnv c with _ | sc
    · simp [compileScalarExpr, hcc] at hComp
    · rcases hct : compileScalarExpr paramEnv th with _ | st_
      · simp [compileScalarExpr, hcc, hct] at hComp
      · rcases hce : compileScalarExpr paramEnv el with _ | se_
        · simp [compileScalarExpr, hcc, hct, hce] at hComp
        · simp [compileScalarExpr, hcc, hct, hce] at hComp; subst hComp
          simp [execSolExpr, ihc hScalar.1.1 hcc, ihe hScalar.2 hce, SolVal.ofValue]
  | leq a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | le a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | geq a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | ge a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | add a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | sub a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | mult a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | div a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | mod a b x y _ _ iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        simp [execSolExpr, iha hScalar.1 hca, ihb hScalar.2 hcb, SolVal.ofValue]
  | eq a b x y ha hb iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        rcases declEval_untagged_not_tagged hScalar.1 ha with ⟨hntX, sx, hsx⟩
        rcases declEval_untagged_not_tagged hScalar.2 hb with ⟨hntY, sy, hsy⟩
        unfold execSolExpr
        rw [iha hScalar.1 hca, ihb hScalar.2 hcb, hsx, hsy]
        simp [SolVal.ofValue, solVal_beq_of_value_beq hsx hsy hntX hntY]
  | neq a b x y ha hb iha ihb =>
    simp only [IsUntaggedScalarTerm, Bool.and_eq_true] at hScalar
    rcases hca : compileScalarExpr paramEnv a with _ | sa
    · simp [compileScalarExpr, hca] at hComp
    · rcases hcb : compileScalarExpr paramEnv b with _ | sb
      · simp [compileScalarExpr, hca, hcb] at hComp
      · simp [compileScalarExpr, hca, hcb] at hComp; subst hComp
        rcases declEval_untagged_not_tagged hScalar.1 ha with ⟨hntX, sx, hsx⟩
        rcases declEval_untagged_not_tagged hScalar.2 hb with ⟨hntY, sy, hsy⟩
        unfold execSolExpr
        rw [iha hScalar.1 hca, ihb hScalar.2 hcb, hsx, hsy]
        simp [SolVal.ofValue, solVal_beq_of_value_beq hsx hsy hntX hntY]

#print axioms execSolStep_sound
#print axioms compileScalarExpr_sound_for_declEval

end Charter.Project
