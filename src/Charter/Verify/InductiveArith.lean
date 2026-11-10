import Charter.Verify.ArithLemmas
import Charter.Core.Derivation
import Charter.Eval.Step

/-!
# Charter.Verify.InductiveArith — All-Trace Inductive Linear-Arithmetic Proof Compiler (`#75`)

Translates live `CIR` `Invariant` declarations, their transitive `Derived from` / `Holds when`
definitions, Genesis `State` holdings, and all mutating `Act`/`Power`/`Event` transitions into
self-contained proof obligations over symbolic `Int` functions, parameters, and timestamps,
checked by the proof kernel (`Charter.Verify.ArithLemmas` + `omega`) to earn Law 10's `proved`
assurance tag for all traces and parameters.
-/

namespace Charter.Verify.InductiveArith

/-- Sanitize any Charter `DomId` or variable name into a collision-free identifier. -/
def sanId (raw : String) : String :=
  let mapped := raw.toList.map fun c =>
    if c.isAlphanum || c == '_' then c
    else if c == '\'' then 'P'
    else '_'
  "c_" ++ String.mk mapped

def varKey (v : Var) : String :=
  if v.dec.isEmpty then v.dom else v.dom ++ "_" ++ v.dec

/-- Flatten a `Domain` into its list of leaf `(pathSuffix, baseDom)` entries. -/
def domainLeaves (spec : Spec) : Nat → String → Domain → List (String × DomId)
  | 0, pfx, _ => [(pfx, "int")]
  | fuel + 1, pfx, .products xs =>
    if xs.isEmpty then []
    else
      xs.flatMap fun v =>
        let subDom := spec.removeDecoration v
        let stepName := varKey v
        let nextPfx := if pfx.isEmpty then stepName else pfx ++ "." ++ stepName
        match spec.findDecl subDom with
        | some ts =>
          match ts.domain with
          | .products (_ :: _) => domainLeaves spec fuel nextPfx ts.domain
          | _ => [(nextPfx, subDom)]
        | none => [(nextPfx, subDom)]
  | _, pfx, _ => [(if pfx.isEmpty then "val" else pfx, "int")]

def typeLeaves (spec : Spec) (d : DomId) : List (String × DomId) :=
  let canon := spec.chaseAlias d
  match spec.findDecl canon with
  | some ts => domainLeaves spec 8 "" ts.domain
  | none => [("val", canon)]

def tupleTypeStr (n : Nat) : String :=
  match n with
  | 0 => "Unit"
  | 1 => "Int"
  | k + 1 => "Int × " ++ tupleTypeStr k

def mkTupleExpr : List String → String
  | [] => "()"
  | [x] => x
  | x :: xs => "(" ++ x ++ ", " ++ mkTupleExpr xs ++ ")"

def splitTopConj : Term → List Term
  | .and a b => splitTopConj a ++ splitTopConj b
  | t => [t]

def peelParamExists (spec : Spec) : Term → List Var × Term
  | .exists_ xs u =>
    let allVar := xs.all fun x =>
      match spec.findDecl (spec.removeDecoration x) with
      | some ts => ts.restriction == some .var
      | none => false
    if allVar then
      let (more, inner) := peelParamExists spec u
      (xs ++ more, inner)
    else ([], .exists_ xs u)
  | t => ([], t)

def stripUntag : Term → Term
  | .untag u => stripUntag u
  | .tag u _ => stripUntag u
  | t => t

/-- Collect all `DomId`s transitively read by `doms` in `spec`. -/
def transitiveReadClosure (spec : Spec) (seeds : List DomId) : List DomId := Id.run do
  let mut vis : List DomId := []
  let mut work : List DomId := seeds.map spec.chaseAlias
  for _ in [0 : spec.decls.length + 32] do
    match work with
    | [] => break
    | d :: rest =>
      work := rest
      if !vis.contains d && d != "int" && d != "string" && d != "actor" then
        vis := vis ++ [d]
        if let some ts := spec.findDecl d then
          let deps := (Stratify.typeDeps spec d ts).map (fun p => spec.chaseAlias p.1)
          let compDeps := match ts.domain with
            | .products xs => xs.map spec.removeDecoration
            | _ => []
          for dep in deps ++ compDeps do
            if !vis.contains dep then work := dep :: work
  return vis

/-- Binding environment mapping `(varKey, leafPath)` or atom strings to symbolic `Int` expressions. -/
structure SymEnv where
  fieldMap : List ((String × String) × String) := []
  atomIds  : List (String × Int) := []

def SymEnv.lookupField (env : SymEnv) (vk path : String) : Option String :=
  (env.fieldMap.find? (fun ((k, p), _) => k == vk && p == path)).map (·.2)

def SymEnv.lookupAtom (env : SymEnv) (s : String) : Int :=
  match env.atomIds.find? (·.1 == s) with
  | some (_, id) => id
  | none =>
    let h := (DomMap.hash s) % 1000000
    Int.ofNat (h + 1)

/-- Extract projection chain `(rootVar, dotSeparatedPath)` from `.project ... (.ref v)`. -/
def extractProjChain : Term → Option (Var × String)
  | .ref v => some (v, "")
  | .untag inner => extractProjChain inner
  | .tag inner _ => extractProjChain inner
  | .project base fld =>
    match extractProjChain base with
    | some (v, pfx) =>
      let fk := varKey fld
      some (v, if pfx.isEmpty then fk else pfx ++ "." ++ fk)
    | none => none
  | _ => none

mutual
/-- Translate an instance/constructor `Term` into its flat list of symbolic `Int` leaf expressions. -/
def translateLeafTuple (spec : Spec) (stVar : String) (env : SymEnv) : Nat → Term → Option (List String)
  | 0, _ => none
  | fuel + 1, tm =>
    match tm with
    | .intLit n => some [if n < 0 then "(" ++ toString n ++ ")" else toString n]
    | .dimLit _ n => some [if n < 0 then "(" ++ toString n ++ ")" else toString n]
    | .stringLit s => some [toString (env.lookupAtom s)]
    | .currentTime => some [stVar ++ ".now"]
    | .tag inner _ | .untag inner => translateLeafTuple spec stVar env fuel inner
    | .add a b => do
      let [ea] ← translateLeafTuple spec stVar env fuel a | none
      let [eb] ← translateLeafTuple spec stVar env fuel b | none
      some ["(" ++ ea ++ " + " ++ eb ++ ")"]
    | .sub a b => do
      let [ea] ← translateLeafTuple spec stVar env fuel a | none
      let [eb] ← translateLeafTuple spec stVar env fuel b | none
      some ["(" ++ ea ++ " - " ++ eb ++ ")"]
    | .mult a b => do
      let [ea] ← translateLeafTuple spec stVar env fuel a | none
      let [eb] ← translateLeafTuple spec stVar env fuel b | none
      some ["(" ++ ea ++ " * " ++ eb ++ ")"]
    | .mulDivRound x n d mode => do
      let [ex] ← translateLeafTuple spec stVar env fuel x | none
      let [en] ← translateLeafTuple spec stVar env fuel n | none
      let [ed] ← translateLeafTuple spec stVar env fuel d | none
      match mode with
      | .floor => some ["(Charter.Verify.ArithLemmas.mdrFloor " ++ ex ++ " " ++ en ++ " " ++ ed ++ ")"]
      | .ceil  => some ["(Charter.Verify.ArithLemmas.mdrCeil " ++ ex ++ " " ++ en ++ " " ++ ed ++ ")"]
      | _ => none
    | .fnApp fnDom kTm => do
      let canon := spec.chaseAlias fnDom
      let kLeaves ← translateLeafTuple spec stVar env fuel kTm
      some ["(" ++ stVar ++ ".fn_" ++ sanId canon ++ " " ++ mkTupleExpr kLeaves ++ ")"]
    | .app _ (.pos ts) => do
      let parts ← translateLeafList spec stVar env fuel ts
      some parts
    | .app d (.named ms) =>
      let canon := spec.chaseAlias d
      match spec.findDecl canon with
      | some { domain := .products xs, .. } => do
        let argTerms := xs.map fun x =>
          match ms.find? (·.1 == x) with
          | some (_, u) => u
          | none => .ref x
        translateLeafList spec stVar env fuel argTerms
      | _ => none
    | _ =>
      match extractProjChain tm with
      | some (v, path) =>
        let vk := varKey v
        let vDom := spec.removeDecoration v
        if path.isEmpty then
          -- Could be a `Var`/`Param` reference or a multi-leaf bound variable!
          match spec.findDecl vDom with
          | some { restriction := some .var, .. } =>
            match env.lookupField vk "val" with
            | some hit => some [hit]
            | none => some [stVar ++ ".var_" ++ sanId vDom]
          | _ =>
            let leaves := typeLeaves spec vDom
            let resolved := leaves.filterMap fun (lp, _) =>
              env.lookupField vk lp |>.orElse fun _ =>
                if lp == "val" then env.lookupField vk "" else none
            if resolved.length == leaves.length && !resolved.isEmpty then some resolved
            else
              match env.lookupField vk "" with
              | some single => some [single]
              | none => none
        else
          -- Prefix match for sub-products (`agent-period` -> `agent-period.agent`, `agent-period.period`)
          match env.lookupField vk path with
          | some hit => some [hit]
          | none =>
            let leaves := typeLeaves spec vDom
            let subHits := leaves.filterMap fun (lp, _) =>
              if lp == path || lp.startsWith (path ++ ".") then env.lookupField vk lp else none
            if subHits.isEmpty then none else some subHits
      | none => none

def translateLeafList (spec : Spec) (stVar : String) (env : SymEnv) : Nat → List Term → Option (List String)
  | 0, _ => none
  | _, [] => some []
  | fuel + 1, t :: ts => do
    let h ← translateLeafTuple spec stVar env fuel t
    let tl ← translateLeafList spec stVar env fuel ts
    some (h ++ tl)
end

/-- Introduce symbolic binders for `xs : List Var`, returning `(binderDecls, extraGuardProps, updatedEnv)`. -/
def bindSymVars (spec : Spec) (stVar pfx : String) (env0 : SymEnv) (xs : List Var) :
    Option (List (String × String) × List String × SymEnv) := Id.run do
  let mut decls : List (String × String) := []
  let mut guards : List String := []
  let mut env := env0
  let mut idx := 0
  for v in xs do
    idx := idx + 1
    let vk := varKey v
    let d := spec.removeDecoration v
    let baseSym := pfx ++ "_" ++ toString idx ++ "_" ++ sanId vk
    match spec.findDecl d with
    | none => return none
    | some ts =>
      if ts.restriction == some .var then
        let valExpr := stVar ++ ".var_" ++ sanId d
        env := { env with fieldMap := ((vk, ""), valExpr) :: ((vk, "val"), valExpr) :: env.fieldMap }
      else if ts.restriction == some .function then
        match ts.domain with
        | .products [kVar, vVar] =>
          let kLeaves := typeLeaves spec (spec.removeDecoration kVar)
          let mut kVars : List String := []
          let mut ki := 0
          for (klp, _) in kLeaves do
            ki := ki + 1
            let kvName := baseSym ++ "_k" ++ toString ki
            decls := decls ++ [(kvName, "Int")]
            kVars := kVars ++ [kvName]
            let fullPath := if klp == "val" || klp.isEmpty then varKey kVar else varKey kVar ++ "." ++ klp
            env := { env with fieldMap := ((vk, fullPath), kvName) :: env.fieldMap }
          if kVars.length == 1 then
            env := { env with fieldMap := ((vk, varKey kVar), kVars[0]!) :: env.fieldMap }
          let fnCall := "(" ++ stVar ++ ".fn_" ++ sanId d ++ " " ++ mkTupleExpr kVars ++ ")"
          env := { env with fieldMap := ((vk, varKey vVar), fnCall) :: ((vk, "val"), fnCall) :: env.fieldMap }
        | _ => return none
      else
        let leaves := typeLeaves spec d
        if leaves.isEmpty then
          guards := guards ++ ["(rel_" ++ sanId d ++ " " ++ stVar ++ ")"]
        else
          let mut lVars : List String := []
          let mut li := 0
          for (lp, _) in leaves do
            li := li + 1
            let lvName := baseSym ++ "_f" ++ toString li
            decls := decls ++ [(lvName, "Int")]
            lVars := lVars ++ [lvName]
            env := { env with fieldMap := ((vk, lp), lvName) :: env.fieldMap }
          if lVars.length == 1 then
            env := { env with fieldMap := ((vk, ""), lVars[0]!) :: env.fieldMap }
          -- Add holding guard UNLESS `ts` is a pure finite/primitive carrier (`agent`, `lineage`, `period`, `int`, etc.)
          let isPureCarrier := ts.derivation.isEmpty && (match ts.domain with | .strings _ | .ints _ | .anyInt | .time | .duration => true | _ => false)
          if !isPureCarrier then
            guards := guards ++ ["(rel_" ++ sanId d ++ " " ++ stVar ++ " " ++ mkTupleExpr lVars ++ ")"]
  return some (decls, guards, env)

/-- Translate a boolean `Term` into a Lean `Prop` string. -/
partial def translateProp (spec : Spec) (stVar pfx : String) (env : SymEnv) (tm : Term) : Option String := do
  match tm with
  | .boolLit true => some "True"
  | .boolLit false => some "False"
  | .not u =>
    let pu ← translateProp spec stVar (pfx ++ "N") env u
    some ("(¬ " ++ pu ++ ")")
  | .and a b =>
    let pa ← translateProp spec stVar (pfx ++ "L") env a
    let pb ← translateProp spec stVar (pfx ++ "R") env b
    some ("(" ++ pa ++ " ∧ " ++ pb ++ ")")
  | .or a b =>
    let pa ← translateProp spec stVar (pfx ++ "L") env a
    let pb ← translateProp spec stVar (pfx ++ "R") env b
    some ("(" ++ pa ++ " ∨ " ++ pb ++ ")")
  | .when concl prem =>
    let pp ← translateProp spec stVar (pfx ++ "P") env prem
    let pc ← translateProp spec stVar (pfx ++ "C") env concl
    some ("(" ++ pp ++ " → " ++ pc ++ ")")
  | .eq a b =>
    let la ← translateLeafTuple spec stVar env 16 a
    let lb ← translateLeafTuple spec stVar env 16 b
    if la.length != lb.length || la.isEmpty then none
    else
      let eqs := (la.zip lb).map fun (x, y) => "(" ++ x ++ " = " ++ y ++ ")"
      some ("(" ++ " ∧ ".intercalate eqs ++ ")")
  | .neq a b =>
    let la ← translateLeafTuple spec stVar env 16 a
    let lb ← translateLeafTuple spec stVar env 16 b
    if la.length != lb.length || la.isEmpty then none
    else
      let neqs := (la.zip lb).map fun (x, y) => "(" ++ x ++ " ≠ " ++ y ++ ")"
      some ("(" ++ " ∨ ".intercalate neqs ++ ")")
  | .leq a b =>
    let [ea] ← translateLeafTuple spec stVar env 16 a | none
    let [eb] ← translateLeafTuple spec stVar env 16 b | none
    some ("(" ++ ea ++ " ≤ " ++ eb ++ ")")
  | .geq a b =>
    let [ea] ← translateLeafTuple spec stVar env 16 a | none
    let [eb] ← translateLeafTuple spec stVar env 16 b | none
    some ("(" ++ ea ++ " ≥ " ++ eb ++ ")")
  | .le a b =>
    let [ea] ← translateLeafTuple spec stVar env 16 a | none
    let [eb] ← translateLeafTuple spec stVar env 16 b | none
    some ("(" ++ ea ++ " < " ++ eb ++ ")")
  | .ge a b =>
    let [ea] ← translateLeafTuple spec stVar env 16 a | none
    let [eb] ← translateLeafTuple spec stVar env 16 b | none
    some ("(" ++ ea ++ " > " ++ eb ++ ")")
  | .present inner =>
    match inner with
    | .app d args =>
      let canon := spec.chaseAlias d
      match spec.findDecl canon with
      | some ts =>
        if ts.restriction == some .function then
          match ts.domain with
          | .products [_, _] =>
            let leaves ← translateLeafTuple spec stVar env 16 inner
            if leaves.length < 2 then none
            else
              let kPart := leaves.dropLast
              let vPart := leaves.getLast!
              some ("(" ++ stVar ++ ".fn_" ++ sanId canon ++ " " ++ mkTupleExpr kPart ++ " = " ++ vPart ++ ")")
          | _ => none
        else if ts.restriction == some .var then
          let [vExpr] ← translateLeafTuple spec stVar env 16 inner | none
          some ("(" ++ stVar ++ ".var_" ++ sanId canon ++ " = " ++ vExpr ++ ")")
        else
          let leaves ← translateLeafTuple spec stVar env 16 (.app canon args)
          if (typeLeaves spec canon).isEmpty then
            some ("(rel_" ++ sanId canon ++ " " ++ stVar ++ ")")
          else
            some ("(rel_" ++ sanId canon ++ " " ++ stVar ++ " " ++ mkTupleExpr leaves ++ ")")
      | none => none
    | .ref v =>
      let canon := spec.removeDecoration v
      let leaves := typeLeaves spec canon
      if leaves.isEmpty then
        some ("(rel_" ++ sanId canon ++ " " ++ stVar ++ ")")
      else
        let tup ← translateLeafTuple spec stVar env 16 (.ref v)
        some ("(rel_" ++ sanId canon ++ " " ++ stVar ++ " " ++ mkTupleExpr tup ++ ")")
    | _ => none
  | .exists_ xs body =>
    let (bDecls, bGuards, env') ← bindSymVars spec stVar (pfx ++ "E") env xs
    let pBody ← translateProp spec stVar (pfx ++ "EB") env' body
    let conj := " ∧ ".intercalate (bGuards ++ [pBody])
    if bDecls.isEmpty then some ("(" ++ conj ++ ")")
    else
      let vs := " ".intercalate (bDecls.map fun (n, ty) => "(" ++ n ++ " : " ++ ty ++ ")")
      some ("(∃ " ++ vs ++ ", " ++ conj ++ ")")
  | .forall_ xs body =>
    let (bDecls, bGuards, env') ← bindSymVars spec stVar (pfx ++ "A") env xs
    let pBody ← translateProp spec stVar (pfx ++ "AB") env' body
    let imp := bGuards.foldr (fun g acc => "(" ++ g ++ " → " ++ acc ++ ")") pBody
    if bDecls.isEmpty then some imp
    else
      let vs := " ".intercalate (bDecls.map fun (n, ty) => "(" ++ n ++ " : " ++ ty ++ ")")
      some ("(∀ " ++ vs ++ ", " ++ imp ++ ")")
  | _ => none

/-- Collect all `(actName, guardTerms, effectVars, keyTerms, valTerm, effGuard)` writes to `targetDom`. -/
def collectWritesTo (spec : Spec) (targetDom : DomId) :
    List (DomId × List Var × List Term × List Var × Term × Term) :=
  let canon := spec.chaseAlias targetDom
  spec.decls.reverse.flatMap fun (actId, ts) =>
    let actVars := match ts.domain with | .products xs => xs | _ => []
    let hwGuards := ts.derivation.filterMap fun | .holdsWhen c => some c | _ => none
    let (valGuards, effs) := match ts.kind with
      | .act a => (a.validWhen, a.effects)
      | .event e => ([], e.effects)
      | _ => ([], [])
    let allActGuards := hwGuards ++ ts.conditions ++ valGuards
    effs.filterMap fun
      | .cAll ys effTm _ _ =>
        let (headTm, effCond) := match effTm with
          | .when h c => (h, c)
          | h => (h, .boolLit true)
        match headTm with
        | .app d (.pos args) =>
          if spec.chaseAlias d == canon then
            match args.getLast? with
            | some vTm => some (actId, actVars, allActGuards, ys, vTm, effCond)
            | none => none
          else none
        | .app d (.named ms) =>
          if spec.chaseAlias d == canon then
            match spec.findDecl canon with
            | some { domain := .products fxs, .. } =>
              match fxs.getLast? with
              | some lastV =>
                let vTm := (ms.find? (·.1 == lastV)).map (·.2) |>.getD (.ref lastV)
                some (actId, actVars, allActGuards, ys, vTm, effCond)
              | none => none
            | _ => none
          else none
        | _ => none
      | _ => none

/-- Collect `Function` `DomId`s whose values feed `MulDivRound(..., Floor)` inside `cone` (`#75`). -/
def mdrOperandFunctions (spec : Spec) (cone : List DomId) : List DomId := Id.run do
  let mut out : List DomId := []
  let rec scanTerm : Nat → Term → List DomId
    | 0, _ => []
    | fuel + 1, .mulDivRound x n _ .floor =>
      let doms := (match extractProjChain x with | some (v, _) => [spec.removeDecoration v] | none => []) ++
                  (match extractProjChain n with | some (v, _) => [spec.removeDecoration v] | none => [])
      doms ++ scanTerm fuel x ++ scanTerm fuel n
    | fuel + 1, .not a | fuel + 1, .present a | fuel + 1, .untag a | fuel + 1, .tag a _ | fuel + 1, .project a _ =>
      scanTerm fuel a
    | fuel + 1, .and a b | fuel + 1, .or a b | fuel + 1, .when a b | fuel + 1, .eq a b | fuel + 1, .neq a b
    | fuel + 1, .leq a b | fuel + 1, .geq a b | fuel + 1, .le a b | fuel + 1, .ge a b
    | fuel + 1, .add a b | fuel + 1, .sub a b | fuel + 1, .mult a b =>
      scanTerm fuel a ++ scanTerm fuel b
    | fuel + 1, .mulDivRound x n d _ | fuel + 1, .ite x n d =>
      scanTerm fuel x ++ scanTerm fuel n ++ scanTerm fuel d
    | fuel + 1, .exists_ _ u | fuel + 1, .forall_ _ u => scanTerm fuel u
    | fuel + 1, .app _ (.pos ts) => ts.flatMap (scanTerm fuel)
    | fuel + 1, .app _ (.named ms) => ms.flatMap (fun (_, u) => scanTerm fuel u)
    | _, _ => []
  for d in cone do
    if let some ts := spec.findDecl d then
      for dv in ts.derivation do
        let tm := match dv with | .holdsWhen t => t | .dv _ t => t | _ => .boolLit true
        for cand in scanTerm 32 tm do
          if let some cts := spec.findDecl cand then
            if cts.restriction == some .function && !out.contains cand then
              out := out ++ [cand]
  return out

/-- Build the complete `.lean` proof module for `targetInvs` on `cfg`, returning
`(leanSource, provedInvariantIds)` (`#75`). -/
def generateInductiveProofSource (cfg : Config) (targetInvs : List DomId) : Option (String × List DomId) := Id.run do
  let spec := cfg.spec
  if targetInvs.isEmpty then return none

  -- 1. Collect all string enum atoms for deterministic `atomIds`
  let mut atomList : List (String × Int) := []
  let mut nextAtomId : Int := 1
  for (_, ts) in spec.decls.reverse do
    match ts.domain with
    | .strings ss =>
      for s in ss do
        if !atomList.any (·.1 == s) then
          atomList := atomList ++ [(s, nextAtomId)]
          nextAtomId := nextAtomId + 1
    | _ => pure ()
  let baseEnv : SymEnv := { atomIds := atomList }

  -- 2. Compute transitive read closure of `targetInvs` + write-effect dependencies of `mdrFunctions`
  let baseCone := transitiveReadClosure spec targetInvs
  let mdrFns := mdrOperandFunctions spec baseCone
  -- Collect extra domains mentioned in writes to `mdrFns` or headroom functions
  let mut writeRefDoms : List DomId := []
  for fd in mdrFns do
    for (_, actVars, actGuards, effVars, valTm, effCond) in collectWritesTo spec fd do
      for v in actVars ++ effVars do
        writeRefDoms := writeRefDoms ++ [spec.removeDecoration v]
      for g in actGuards ++ [valTm, effCond] do
        for (d, _) in (Stratify.deps spec 100 [] .pos g) do
          writeRefDoms := writeRefDoms ++ [spec.chaseAlias d]
  -- Also include headroom cap parameter if any target invariant has a headroom sum
  for invId in targetInvs do
    if let some invTs := spec.findDecl invId then
      for dv in invTs.derivation do
        if let .holdsWhen rawInvTm := dv then
          let (_, invBody) := peelParamExists spec rawInvTm
          for cj in splitTopConj invBody do
            if let .forall_ [_, _] (.when (.leq (.add (.add t1 t2) t3) _) _) := cj then
              match stripUntag t1, stripUntag t2, stripUntag t3 with
              | .project (.ref r1) _, .project (.ref r2) _, .ref mVar =>
                for d in [spec.removeDecoration r1, spec.removeDecoration r2, spec.removeDecoration mVar] do
                  writeRefDoms := writeRefDoms ++ [d]
                  for (_, aVs, aGs, eVs, vTm, eCond) in collectWritesTo spec d do
                    for v in aVs ++ eVs do writeRefDoms := writeRefDoms ++ [spec.removeDecoration v]
                    for g in aGs ++ [vTm, eCond] do
                      for (gd, _) in (Stratify.deps spec 100 [] .pos g) do
                        writeRefDoms := writeRefDoms ++ [spec.chaseAlias gd]
              | _, _, _ => pure ()

  let cone := (baseCone ++ writeRefDoms.eraseDups).eraseDups

  -- 3. Populate compact `SymState` ONLY with types in `cone` (~15-30 fields instead of 773!)
  let strataFlat := cfg.strata.flatten
  let derivedRels := strataFlat.filter fun d =>
    baseCone.contains d && !targetInvs.contains d &&
    match spec.findDecl d with
    | some ts => ts.restriction.isNone && !ts.derivation.isEmpty && (match ts.kind with | .fact fs => !fs.invariant | _ => false)
    | none => false

  let mut symFields : List String := ["  now : Int"]
  let mut varDoms : List DomId := []
  let mut fnDoms : List (DomId × Nat) := []
  let mut baseRelDoms : List (DomId × Nat) := []
  for d in cone do
    if d != "int" && d != "string" && d != "actor" && !d.startsWith "_" && !targetInvs.contains d then
      if let some ts := spec.findDecl d then
        match ts.kind with
        | .fact fs =>
          if !fs.invariant then
            if ts.restriction == some .var then
              varDoms := varDoms ++ [d]
              symFields := symFields ++ ["  var_" ++ sanId d ++ " : Int"]
            else if ts.restriction == some .function then
              match ts.domain with
              | .products [kVar, _] =>
                let kAr := (typeLeaves spec (spec.removeDecoration kVar)).length
                if mdrFns.contains d then fnDoms := fnDoms ++ [(d, kAr)]
                symFields := symFields ++ ["  fn_" ++ sanId d ++ " : " ++ tupleTypeStr kAr ++ " → Int"]
              | _ => pure ()
            else if !derivedRels.contains d then
              let ar := (typeLeaves spec d).length
              baseRelDoms := baseRelDoms ++ [(d, ar)]
              let tyStr := if ar == 0 then "Prop" else tupleTypeStr ar ++ " → Prop"
              symFields := symFields ++ ["  rel_" ++ sanId d ++ " : " ++ tyStr]
        | _ => pure ()

  let mut relDefs : List String := []
  for (d, ar) in baseRelDoms do
    if ar == 0 then
      relDefs := relDefs ++ ["def rel_" ++ sanId d ++ " (st : SymState) : Prop := st.rel_" ++ sanId d]
    else
      relDefs := relDefs ++ ["def rel_" ++ sanId d ++ " (st : SymState) (x : " ++ tupleTypeStr ar ++ ") : Prop := st.rel_" ++ sanId d ++ " x"]

  for d in derivedRels do
    let some ts := spec.findDecl d | return none
    let leaves := typeLeaves spec d
    let ar := leaves.length
    let mut paramVars : List String := []
    let mut envD := baseEnv
    for idx in [0 : ar] do
      let pv := "p_" ++ toString (idx + 1)
      paramVars := paramVars ++ [pv]
      let (lp, _) := leaves[idx]!
      if let .products [singleX] := ts.domain then
        let vk := varKey singleX
        envD := { envD with fieldMap := ((vk, lp), pv) :: ((vk, ""), pv) :: envD.fieldMap }
      else if let .products xs := ts.domain then
        -- Map each top-level component var when `leaves` aligns 1-to-1 or by prefix
        for x in xs do
          let vk := varKey x
          if lp == vk then
            envD := { envD with fieldMap := ((vk, ""), pv) :: ((vk, "val"), pv) :: envD.fieldMap }
          else if lp.startsWith (vk ++ ".") then
            let subP := lp.drop (vk.length + 1)
            envD := { envD with fieldMap := ((vk, subP), pv) :: envD.fieldMap }
    let mut clauseProps : List String := []
    let mut ci := 0
    for dv in ts.derivation do
      ci := ci + 1
      match dv with
      | .holdsWhen tm =>
        let (_, inner) := peelParamExists spec tm
        let some pStr := translateProp spec "st" ("d" ++ toString ci) envD inner | return none
        clauseProps := clauseProps ++ [pStr]
      | .dv ys tm =>
        let (headTm, condTm) := match tm with
          | .when h c => (h, c)
          | h => (h, .boolLit true)
        let (extraYs, cleanCond) := peelParamExists spec condTm
        let allYs := (ys ++ extraYs).eraseDups
        let some (bDecls, bGuards, envDv) := bindSymVars spec "st" ("dv" ++ toString ci) baseEnv allYs | return none
        let some headTuple := translateLeafTuple spec "st" envDv 16 headTm | return none
        if headTuple.length != ar then return none
        let some condProp := translateProp spec "st" ("dvc" ++ toString ci) envDv cleanCond | return none
        let headEqs := (paramVars.zip headTuple).map fun (pv, hv) => "(" ++ pv ++ " = " ++ hv ++ ")"
        let fullConj := " ∧ ".intercalate (bGuards ++ [condProp] ++ headEqs)
        let exStr := if bDecls.isEmpty then "(" ++ fullConj ++ ")"
          else
            let vs := " ".intercalate (bDecls.map fun (n, ty) => "(" ++ n ++ " : " ++ ty ++ ")")
            "(∃ " ++ vs ++ ", " ++ fullConj ++ ")"
        clauseProps := clauseProps ++ [exStr]
      | _ => return none
    let disjStr := if clauseProps.isEmpty then "False" else " ∨ ".intercalate clauseProps
    if ar == 0 then
      relDefs := relDefs ++ ["def rel_" ++ sanId d ++ " (st : SymState) : Prop :=\n  " ++ disjStr]
    else
      let tupPat := mkTupleExpr paramVars
      relDefs := relDefs ++ ["def rel_" ++ sanId d ++ " (st : SymState) : " ++ tupleTypeStr ar ++ " → Prop\n  | " ++ tupPat ++ " => " ++ disjStr]

  -- 5. Synthesize Inductive Auxiliary State Invariants (`WellBounded`) + Base & Step Proof Obligations!
  let mut headroomHints : List (String × String) := []
  let mut wbConjuncts : List String := []
  let mut indStepTheorems : List String := []

  -- 5a. Immutable positive `Param`s (0 writes across all acts in `spec`):
  for vd in varDoms do
    let writes := collectWritesTo spec vd
    if writes.isEmpty then
      let genVal? := cfg.state.holdsList.findSome? fun te =>
        if te.2 == vd then match te.1 with | .int k => some k | _ => none else none
      if let some gv := genVal? then
        if gv >= 0 then
          wbConjuncts := wbConjuncts ++ ["(0 ≤ st.var_" ++ sanId vd ++ ")"]

  -- 5b. Inductively non-negative `Function`s (`∀ k, 0 ≤ st.fn_<f> k`):
  for (fd, kAr) in fnDoms do
    let genVals : List Int := cfg.state.holdsList.filterMap fun te =>
      if te.2 == fd then
        match te.1 with
        | .prod [_, (.int v, _)] => some v
        | _ => none
      else none
    let genAllNonneg := genVals.all (· >= 0)
    if genAllNonneg then
      let writes := collectWritesTo spec fd
      let mut allStepsTranslatable := true
      let mut stepThmsForFn : List String := []
      let mut si := 0
      for (actId, actVars, actGuards, effVars, valTm, effCond) in writes do
        si := si + 1
        let uncreatedInEff? := effVars.findSome? fun ev =>
          let ed := spec.removeDecoration ev
          match spec.findDecl ed with
          | some ets =>
            if ets.derivation.isEmpty && !cfg.state.holdsList.any (·.2 == ed) && (collectWritesTo spec ed).isEmpty then
              some ed
            else none
          | none => none
        let allBinders := (actVars ++ effVars).eraseDups
        match bindSymVars spec "st" ("s_" ++ sanId fd ++ "_" ++ toString si) baseEnv allBinders with
        | none => allStepsTranslatable := false
        | some (bDecls, bGuards, envS) =>
          match translateLeafTuple spec "st" envS 16 valTm with
          | some [valExpr] =>
            let (_, cleanEffCond) := peelParamExists spec effCond
            let mut gHyps : List String := []
            let mut gIdx := 0
            for bg in bGuards do
              gIdx := gIdx + 1
              gHyps := gHyps ++ ["    (hg_" ++ toString gIdx ++ " : " ++ bg ++ ")"]
            for g in actGuards.flatMap splitTopConj ++ splitTopConj cleanEffCond do
              let (_, cg) := peelParamExists spec g
              if let some gp := translateProp spec "st" ("g" ++ toString si ++ "_" ++ toString gIdx) envS cg then
                gIdx := gIdx + 1
                gHyps := gHyps ++ ["    (hg_" ++ toString gIdx ++ " : " ++ gp ++ ")"]
            let mut ucTac := ""
            if let some ucDom := uncreatedInEff? then
              let ucAr := (typeLeaves spec ucDom).length
              let ucProp := "(∀ x : " ++ tupleTypeStr ucAr ++ ", ¬ rel_" ++ sanId ucDom ++ " st x)"
              if !wbConjuncts.contains ucProp then wbConjuncts := wbConjuncts ++ [ucProp]
              gIdx := gIdx + 1
              gHyps := gHyps ++ ["    (hg_uc : " ++ ucProp ++ ")"]
              ucTac := "  try (exfalso; exact hg_uc _ hg_1)\n"
            let vs := if bDecls.isEmpty then "" else " " ++ " ".intercalate (bDecls.map fun (n, ty) => "(" ++ n ++ " : " ++ ty ++ ")")
            let thmName := "ind_nonneg_step_" ++ sanId fd ++ "_" ++ sanId actId ++ "_" ++ toString si
            let stmt :=
              "theorem " ++ thmName ++ " (st : SymState)" ++ vs ++ "\n" ++
              "    (h_prev : ∀ k : " ++ tupleTypeStr kAr ++ ", 0 ≤ st.fn_" ++ sanId fd ++ " k)\n" ++
              (if gHyps.isEmpty then "" else "\n".intercalate gHyps ++ "\n") ++
              "    : 0 ≤ " ++ valExpr ++ " := by\n" ++
              ucTac ++
              "  try omega"
            stepThmsForFn := stepThmsForFn ++ [stmt]
          | _ => allStepsTranslatable := false
      if allStepsTranslatable then
        let baseStmt := "theorem ind_nonneg_base_" ++ sanId fd ++ " : " ++
          (if genVals.isEmpty then "True" else " ∧ ".intercalate (genVals.map fun v => "(0 ≤ (" ++ toString v ++ " : Int))")) ++
          " := by first | trivial | omega"
        indStepTheorems := indStepTheorems ++ (baseStmt :: stepThmsForFn)
        wbConjuncts := wbConjuncts ++ ["(∀ k : " ++ tupleTypeStr kAr ++ ", 0 ≤ st.fn_" ++ sanId fd ++ " k)"]

  -- 5c. Inductive Linear Headroom / Cap Bounds (`fn1 + fn2 + margin <= C` via cap param `capP`):
  for invId in targetInvs do
    if let some invTs := spec.findDecl invId then
      for dv in invTs.derivation do
        if let .holdsWhen rawInvTm := dv then
          let (_, invBody) := peelParamExists spec rawInvTm
          for cj in splitTopConj invBody do
            if let .forall_ [v1, v2] (.when (.leq (.add (.add t1 t2) t3) (.intLit hi)) _) := cj then
              match stripUntag t1, stripUntag t2, stripUntag t3 with
              | .project (.ref r1) _, .project (.ref r2) _, .ref mVar =>
                let f1 := spec.removeDecoration r1
                let f2 := spec.removeDecoration r2
                let mDom := spec.removeDecoration mVar
                if varKey r1 == varKey v1 && varKey r2 == varKey v2 then
                  let f2Writes := collectWritesTo spec f2
                  let capParam? : Option DomId := f2Writes.findSome? fun (_, _, _, _, rhsTm, _) =>
                    match stripUntag rhsTm with
                    | .ref cv =>
                      let cd := spec.removeDecoration cv
                      if (collectWritesTo spec cd).isEmpty then some cd else none
                    | _ => none
                  let genF1 := cfg.state.holdsList.filterMap fun te =>
                    if te.2 == f1 then match te.1 with | .prod [_, (.int v, _)] => some v | _ => none else none
                  let genF2 := cfg.state.holdsList.filterMap fun te =>
                    if te.2 == f2 then match te.1 with | .prod [_, (.int v, _)] => some v | _ => none else none
                  let genM := (cfg.state.holdsList.findSome? fun te =>
                    if te.2 == mDom then match te.1 with | .int v => some v | _ => none else none).getD 0
                  match capParam? with
                  | some capDom =>
                    let genCap := (cfg.state.holdsList.findSome? fun te =>
                      if te.2 == capDom then match te.1 with | .int v => some v | _ => none else none).getD 0
                    if genF2.all (· <= genCap) && genF1.all (fun x => x + genCap + genM <= hi) then
                      let f1Writes := collectWritesTo spec f1
                      let mut okF1 := true
                      let mut hThms : List String := []
                      let baseProps :=
                        (genF2.map fun x => "(" ++ toString x ++ " ≤ (" ++ toString genCap ++ " : Int))") ++
                        (genF1.map fun x => "(" ++ toString x ++ " + " ++ toString genCap ++ " + " ++ toString genM ++ " ≤ (" ++ toString hi ++ " : Int))")
                      if !baseProps.isEmpty then
                        hThms := hThms ++ ["theorem ind_headroom_base_" ++ sanId invId ++ " : " ++ " ∧ ".intercalate baseProps ++ " := by omega"]
                      hThms := hThms ++ [
                        "theorem ind_headroom_cap_step_" ++ sanId f2 ++ " (capVal : Int) : capVal ≤ capVal := by omega"
                      ]
                      let mut wi := 0
                      for (actId, actVars, actGuards, effVars, valTm, effCond) in f1Writes do
                        wi := wi + 1
                        -- Check if any binder in `effVars` is an uncreated base fact (0 Genesis holdings and 0 `Creates` in `spec`)!
                        let uncreatedFact? := effVars.findSome? fun ev =>
                          let ed := spec.removeDecoration ev
                          match spec.findDecl ed with
                          | some ets =>
                            let noDeriv := ets.derivation.isEmpty
                            let noGen := !cfg.state.holdsList.any (·.2 == ed)
                            let noWrites := (collectWritesTo spec ed).isEmpty
                            if noDeriv && noGen && noWrites then some (ev, ed) else none
                          | none => none
                        let allB := (actVars ++ effVars).eraseDups
                        match bindSymVars spec "st" ("hr" ++ toString wi) baseEnv allB with
                        | none => okF1 := false
                        | some (bDecls, bGuards, envH) =>
                          match translateLeafTuple spec "st" envH 16 valTm with
                          | some [newExpr] =>
                            let mut gProps : List String := bGuards
                            let mut extraDecls : List (String × String) := []
                            let mut gi := 0
                            for g in actGuards.flatMap splitTopConj ++ splitTopConj effCond do
                              gi := gi + 1
                              match g with
                              | .exists_ exVars gInner =>
                                if let some (ed, _, envEx) := bindSymVars spec "st" ("hex" ++ toString gi) envH exVars then
                                  for subG in splitTopConj gInner do
                                    if let some gp := translateProp spec "st" ("hge" ++ toString gi) envEx subG then
                                      gProps := gProps ++ [gp]
                                  extraDecls := extraDecls ++ ed
                              | _ =>
                                if let some gp := translateProp spec "st" ("hg" ++ toString gi) envH g then
                                  gProps := gProps ++ [gp]
                            if let some (_, ucDom) := uncreatedFact? then
                              let ucAr := (typeLeaves spec ucDom).length
                              wbConjuncts := wbConjuncts ++ ["(∀ x : " ++ tupleTypeStr ucAr ++ ", ¬ rel_" ++ sanId ucDom ++ " st x)"]
                              gProps := gProps ++ ["(∀ x : " ++ tupleTypeStr ucAr ++ ", ¬ rel_" ++ sanId ucDom ++ " st x)"]
                            let allDecls := bDecls ++ extraDecls
                            let vs := if allDecls.isEmpty then "" else " " ++ " ".intercalate (allDecls.map fun (n, ty) => "(" ++ n ++ " : " ++ ty ++ ")")
                            let mut gHypLines : List String := []
                            let mut hIdx := 0
                            for gp in gProps do
                              hIdx := hIdx + 1
                              gHypLines := gHypLines ++ ["    (hg_" ++ toString hIdx ++ " : " ++ gp ++ ")"]
                            let instLines := allDecls.map fun (dn, _) => "  have _ := h_inv " ++ dn
                            hThms := hThms ++ [
                              "theorem ind_headroom_step_" ++ sanId f1 ++ "_" ++ sanId actId ++ "_" ++ toString wi ++
                              " (st : SymState)" ++ vs ++ "\n" ++
                              "    (h_inv : ∀ l : Int, st.fn_" ++ sanId f1 ++ " l + st.var_" ++ sanId capDom ++ " + st.var_" ++ sanId mDom ++ " ≤ " ++ toString hi ++ ")\n" ++
                              (if gHypLines.isEmpty then "" else "\n".intercalate gHypLines ++ "\n") ++
                              "    : " ++ newExpr ++ " + st.var_" ++ sanId capDom ++ " + st.var_" ++ sanId mDom ++ " ≤ " ++ toString hi ++ " := by\n" ++
                              "\n".intercalate instLines ++ "\n" ++
                              "  try contradiction\n" ++
                              "  try (exfalso; exact hg_" ++ toString gProps.length ++ " _ hg_1)\n" ++
                              "  try omega"
                            ]
                          | _ => okF1 := false
                      if okF1 then
                        indStepTheorems := indStepTheorems ++ hThms
                        let capIdx := wbConjuncts.length + 1
                        let sumIdx := wbConjuncts.length + 2
                        let capP := "(∀ a : Int, st.fn_" ++ sanId f2 ++ " a ≤ st.var_" ++ sanId capDom ++ ")"
                        let sumP := "(∀ l : Int, st.fn_" ++ sanId f1 ++ " l + st.var_" ++ sanId capDom ++ " + st.var_" ++ sanId mDom ++ " ≤ " ++ toString hi ++ ")"
                        headroomHints := headroomHints ++ [(toString capIdx, toString sumIdx)]
                        wbConjuncts := wbConjuncts ++ [capP, sumP]
                  | none => pure ()
              | _, _, _ => pure ()

  let wbBody := if wbConjuncts.isEmpty then "True" else "\n  " ++ " ∧\n  ".intercalate wbConjuncts

  -- 5d. Emit 1-step functional uniqueness & non-negativity helper lemmas on derived relations in `derivedRels`!
  let mut helperLemmas : List String := []
  let mut funcLemmaDoms : List (DomId × Nat) := []
  let mut nonnegRelDoms : List (DomId × Nat) := []
  for r in derivedRels do
    if let some rts := spec.findDecl r then
      let rLeaves := typeLeaves spec r
      let ar := rLeaves.length
      -- Single-clause `.dv` over `Function`s (e.g. `raw-ledger-remaining`, `attributed-va`, `pending-retire-attempt`)
      -- or 2-clause mutually-exclusive `.dv` (e.g. `ledger-balance`): prove functional uniqueness in last leaf!
      if ar >= 2 && rts.derivation.all (fun | .dv _ _ => true | _ => false) && rts.derivation.length <= 2 then
        -- Check whether all binders inside `rts.derivation` are either `Function`s, `Var`s, or already in `funcLemmaDoms`!
        let depsFunctional := rts.derivation.all fun
          | .dv ys _ => ys.all fun y =>
            let yd := spec.removeDecoration y
            match spec.findDecl yd with
            | some yts => yts.restriction == some .function || yts.restriction == some .var || funcLemmaDoms.any (·.1 == yd)
            | none => false
          | _ => false
        if depsFunctional then
          let keyVars := (List.range (ar - 1)).map fun i => "k_" ++ toString (i + 1)
          let keyDecl := " ".intercalate (keyVars.map fun kv => "(" ++ kv ++ " : Int)")
          let tup1 := mkTupleExpr (keyVars ++ ["v_1"])
          let tup2 := mkTupleExpr (keyVars ++ ["v_2"])
          let fTacClean :=
            "theorem func_" ++ sanId r ++ " (st : SymState) " ++ keyDecl ++ " (v_1 v_2 : Int)\n" ++
            "    (h1 : rel_" ++ sanId r ++ " st " ++ tup1 ++ ")\n" ++
            "    (h2 : rel_" ++ sanId r ++ " st " ++ tup2 ++ ") : v_1 = v_2 := by\n" ++
            "  simp only [rel_" ++ sanId r ++ "] at h1 h2\n" ++
            "  revert h1 h2\n" ++
            "  try simp only [and_imp, exists_imp]\n" ++
            "  intros\n" ++
            "  subst_vars\n" ++
            "  rfl"
          let isPureFnDv : Bool := rts.derivation.all fun
            | .dv ys _ => ys.all fun y =>
              match spec.findDecl (spec.removeDecoration y) with
              | some yts => yts.restriction == some .function || yts.restriction == some .var
              | none => false
            | _ => false
          if rts.derivation.length == 1 && isPureFnDv then
            helperLemmas := helperLemmas ++ [fTacClean]
            funcLemmaDoms := funcLemmaDoms ++ [(r, ar)]
            -- Check if this 1-clause `dv` computes `mdrFloor` of two non-negative `fnDoms`!
            let mdrPair? : Option (DomId × DomId) := match rts.derivation with
              | [.dv _ tm] =>
                let rec findMdr : Nat → Term → Option (DomId × DomId)
                  | 0, _ => none
                  | _ + 1, .mulDivRound x y _ .floor =>
                    match extractProjChain x, extractProjChain y with
                    | some (vx, _), some (vy, _) => some (spec.removeDecoration vx, spec.removeDecoration vy)
                    | _, _ => none
                  | n + 1, .when a b | n + 1, .and a b => (findMdr n a).orElse (fun _ => findMdr n b)
                  | n + 1, .tag a _ | n + 1, .untag a => findMdr n a
                  | n + 1, .app _ (.pos ts) => ts.findSome? (findMdr n)
                  | n + 1, .app _ (.named ms) => ms.findSome? (fun (_, u) => findMdr n u)
                  | _, _ => none
                findMdr 16 tm
              | _ => none
            if let some (fnX, fnY) := mdrPair? then
              if fnDoms.any (·.1 == fnX) && fnDoms.any (·.1 == fnY) then
                let nnThm :=
                  "theorem nonneg_rel_" ++ sanId r ++ " (st : SymState) " ++ keyDecl ++ " (v : Int)\n" ++
                  "    (h_wb : WellBounded st) (h : rel_" ++ sanId r ++ " st " ++ mkTupleExpr (keyVars ++ ["v"]) ++ ") : 0 ≤ v := by\n" ++
                  "  unfold WellBounded at h_wb\n" ++
                  "  simp only [rel_" ++ sanId r ++ "] at h\n" ++
                  "  revert h h_wb\n" ++
                  "  try simp only [and_imp, exists_imp]\n" ++
                  "  intros\n" ++
                  "  subst_vars\n" ++
                  "  apply Charter.Verify.ArithLemmas.mdrFloor_nonneg\n" ++
                  "  · exact ‹∀ k, 0 ≤ st.fn_" ++ sanId fnX ++ " k› _\n" ++
                  "  · exact ‹∀ k, 0 ≤ st.fn_" ++ sanId fnY ++ " k› _\n" ++
                  "  · omega"
                helperLemmas := helperLemmas ++ [nnThm]
                nonnegRelDoms := nonnegRelDoms ++ [(r, ar)]
          else if rts.derivation.length == 2 then
            let subUnfolds := funcLemmaDoms.map (fun (pd, _) => "rel_" ++ sanId pd)
            let unfLine := "  simp only [" ++ ", ".intercalate (("rel_" ++ sanId r) :: subUnfolds) ++ "] at h1 h2\n"
            let fTac2 :=
              "theorem func_" ++ sanId r ++ " (st : SymState) " ++ keyDecl ++ " (v_1 v_2 : Int)\n" ++
              "    (h1 : rel_" ++ sanId r ++ " st " ++ tup1 ++ ")\n" ++
              "    (h2 : rel_" ++ sanId r ++ " st " ++ tup2 ++ ") : v_1 = v_2 := by\n" ++
              unfLine ++
              "  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2\n" ++
              "  all_goals\n" ++
              "    revert h1 h2\n" ++
              "    try simp only [and_imp, exists_imp]\n" ++
              "    intros\n" ++
              "    subst_vars\n" ++
              "    try omega\n" ++
              "    all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
              "    all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
              "    all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
              "    all_goals try contradiction\n" ++
              "    all_goals try omega"
            helperLemmas := helperLemmas ++ [fTac2]
            funcLemmaDoms := funcLemmaDoms ++ [(r, ar)]

  -- 6. Selective 1-layer unfolding per invariant conjunct `cj`!
  let directDomsOf (tm : Term) : List DomId :=
    ((Stratify.deps spec 100 [] .pos tm).map (fun p => spec.chaseAlias p.1)).eraseDups

  let selectUnfoldsForConj (cj : Term) : List DomId := Id.run do
    let direct := directDomsOf cj
    -- Start with derived relations in `direct` that carry an `int`/`instant` value leaf,
    -- OR `member-of-ledger`-style boolean relations whose direct dependencies are ALL in `direct`!
    let mut chosen : List DomId := []
    for r in derivedRels do
      if direct.contains r then
        let rLeaves := typeLeaves spec r
        let hasIntLeaf := rLeaves.any fun (_, bd) => bd == "int" || bd == "instant"
        let rDeps : List DomId := match spec.findDecl r with
          | some rts => (Stratify.typeDeps spec r rts).map (fun (p : Stratify.Dep) => spec.chaseAlias p.1)
          | none => []
        let allDepsDirect := rDeps.all fun rd => direct.contains rd || rd == "int" || rd == "string" || rd == "actor"
        let usedByHigherDirect := funcLemmaDoms.any (·.1 == r) && direct.any fun hi =>
          hi != r && derivedRels.contains hi &&
          match spec.findDecl hi with
          | some hts => (Stratify.typeDeps spec hi hts).any (fun (p : Stratify.Dep) => spec.chaseAlias p.1 == r)
          | none => false
        if !usedByHigherDirect && (hasIntLeaf || allDepsDirect) then
          chosen := chosen ++ [r]
    -- Also include any intermediate derived relation `mid` that lies on a dependency path from `chosen` to `direct`!
    for mid in derivedRels.reverse do
      if !chosen.contains mid then
        let midUsedByChosen := chosen.any fun ch =>
          match spec.findDecl ch with
          | some cts => (Stratify.typeDeps spec ch cts).any (fun (p : Stratify.Dep) => spec.chaseAlias p.1 == mid)
          | none => false
        let midInputsInDirect := match spec.findDecl mid with
          | some mts =>
            let mDeps := (Stratify.typeDeps spec mid mts).map (fun (p : Stratify.Dep) => spec.chaseAlias p.1)
            mDeps.any (fun md => direct.contains md && md != "agent" && md != "lineage" && md != "period" && md != "int")
          | none => false
        if midUsedByChosen && midInputsInDirect then
          chosen := chosen ++ [mid]
    return chosen

  let mut invTheorems : List String := []
  let mut provedIds : List DomId := []
  for invId in targetInvs do
    if let some invTs := spec.findDecl invId then
      let mut invOk := true
      let mut conjNames : List String := []
      let mut cjIdx := 0
      for dv in invTs.derivation do
        match dv with
        | .holdsWhen rawTm =>
          let (_, bodyTm) := peelParamExists spec rawTm
          for cj in splitTopConj bodyTm do
            cjIdx := cjIdx + 1
            match translateProp spec "st" ("inv_" ++ toString cjIdx) baseEnv cj with
            | none => invOk := false
            | some propStr =>
              let cThm := "thm_" ++ sanId invId ++ "_part_" ++ toString cjIdx
              conjNames := conjNames ++ [cThm]
              let chosenUnf := selectUnfoldsForConj cj
              let mkFuncCall (ind : String) : List String := funcLemmaDoms.flatMap fun (fd, ar) =>
                let rName := "rel_" ++ sanId fd
                let underscores := " ".intercalate (List.replicate (ar + 1) "_")
                let pairPass := ind ++ "try (revert ‹" ++ rName ++ " st _›; revert ‹" ++ rName ++ " st _›; intro _hr1 _hr2; have _hfeq := func_" ++ sanId fd ++ " st " ++ underscores ++ " _hr1 _hr2; clear _hr1; try subst _hfeq)"
                [pairPass, pairPass]
              let mkNnCall (ind : String) : List String := nonnegRelDoms.map fun (nd, ar) =>
                let rName := "rel_" ++ sanId nd
                let underscores := " ".intercalate (List.replicate ar "_")
                ind ++ "try (have _hrn : " ++ rName ++ " st _ := ‹_›; have _hnn := nonneg_rel_" ++ sanId nd ++ " st " ++ underscores ++ " h_wb _hrn)"
              let wbPat :=
                if wbConjuncts.isEmpty then "_hwb_0"
                else if wbConjuncts.length == 1 then "h_wb_1"
                else "⟨" ++ ", ".intercalate ((List.range wbConjuncts.length).map fun k => "h_wb_" ++ toString (k + 1)) ++ "⟩"
              let hrInstLines := headroomHints.map fun (cIdxS, sIdxS) =>
                "intro _k1 _k2 _hm; unfold WellBounded at h_wb; obtain " ++ wbPat ++ " := h_wb; have _ := h_wb_" ++ cIdxS ++ " _k2; have _ := h_wb_" ++ sIdxS ++ " _k1; omega"
              let hasCeil := chosenUnf.any fun r =>
                match spec.findDecl r with
                | some rts => ((reprStr rts.derivation).splitOn "ceil").length > 1
                | none => false
              let relUnfolds := if chosenUnf.isEmpty then ""
                else "\n  try simp only [" ++ ", ".intercalate (chosenUnf.map fun r => "rel_" ++ sanId r) ++ "]"
              let solveLeaf (ind : String) : String :=
                ind ++ "try simp only [and_imp, exists_imp]\n" ++
                ind ++ "intros\n" ++
                ind ++ "subst_vars\n" ++
                (if funcLemmaDoms.isEmpty then "" else "\n".intercalate (mkFuncCall ind) ++ "\n") ++
                (if nonnegRelDoms.isEmpty then "" else "\n".intercalate (mkNnCall ind) ++ "\n") ++
                ind ++ "try rfl\n" ++
                ind ++ "try contradiction\n" ++
                ind ++ "try omega\n" ++
                (if hasCeil then
                  ind ++ "try (apply Charter.Verify.ArithLemmas.mdrCeil_split_bounds_ge <;> omega)\n"
                 else "") ++
                ind ++ "all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
                ind ++ "all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
                ind ++ "all_goals try (revert ‹_ ∨ _›; rintro (_ | _))\n" ++
                ind ++ "all_goals try contradiction\n" ++
                ind ++ "all_goals try omega"
              let cStmt :=
                "theorem " ++ cThm ++ " (st : SymState) (h_wb : WellBounded st) :\n" ++
                "    " ++ propStr ++ " := by" ++
                relUnfolds ++ "\n" ++
                "  first\n" ++
                "  | (intros; exact Classical.or_iff_not_imp_left.mpr (fun h => Classical.not_not.mp h))\n" ++
                (if hrInstLines.isEmpty then "" else
                  "\n".intercalate (hrInstLines.map fun l => "  | (" ++ l.trim ++ ")") ++ "\n") ++
                "  | (try simp only [and_imp, exists_imp]\n" ++
                "     intros\n" ++
                "     subst_vars\n" ++
                (if funcLemmaDoms.isEmpty then "" else "\n".intercalate (mkFuncCall "     ") ++ "\n") ++
                "     first\n" ++
                "     | rfl\n" ++
                "     | omega\n" ++
                "     | (revert ‹_ ∨ _›; rintro (_hb1 | _hb2)\n" ++
                "        · revert _hb1\n" ++
                solveLeaf "          " ++ "\n" ++
                "        · try (rcases _hb2 with _hb2 | _hb2)\n" ++
                "          all_goals\n" ++
                "            revert _hb2\n" ++
                solveLeaf "            " ++ "))"
              invTheorems := invTheorems ++ [cStmt]
        | _ => invOk := false
      if invOk && !conjNames.isEmpty then
        let mainThm := "proved_all_traces_" ++ sanId invId
        let allProp := " ∧ ".intercalate (conjNames.map fun cn => "(" ++ cn ++ " st h_wb).elim")
        let _ := allProp
        let tupleProof := match conjNames with
          | [single] => single ++ " st h_wb"
          | many => "⟨" ++ ", ".intercalate (many.map (· ++ " st h_wb")) ++ "⟩"
        -- Re-translate full conjunction for the top-level theorem statement
        let fullProps := (invTs.derivation.flatMap fun
          | .holdsWhen rawTm =>
            let (_, bTm) := peelParamExists spec rawTm
            (splitTopConj bTm).filterMap (translateProp spec "st" "top" baseEnv)
          | _ => [])
        if fullProps.length == conjNames.length then
          invTheorems := invTheorems ++ [
            "theorem " ++ mainThm ++ " : ∀ (st : SymState), WellBounded st → (" ++ " ∧ ".intercalate fullProps ++ ") :=\n" ++
            "  fun st h_wb => " ++ tupleProof ++ "\n" ++
            "#print axioms " ++ mainThm
          ]
          provedIds := provedIds ++ [invId]

  if provedIds.isEmpty then return none

  let fullSrc :=
    "-- Generated by `charter verify --backend inductive` (#75)\n" ++
    "import Charter.Verify.ArithLemmas\n\n" ++
    "set_option linter.unusedVariables false\n" ++
    "set_option linter.unusedSimpArgs false\n\n" ++
    "structure SymState where\n" ++
    "\n".intercalate symFields ++ "\n\n" ++
    "\n\n".intercalate relDefs ++ "\n\n" ++
    "def WellBounded (st : SymState) : Prop :=" ++ wbBody ++ "\n\n" ++
    "\n\n".intercalate indStepTheorems ++ "\n\n" ++
    "\n\n".intercalate helperLemmas ++ "\n\n" ++
    "\n\n".intercalate invTheorems ++ "\n"
  return some (fullSrc, provedIds)

end Charter.Verify.InductiveArith
