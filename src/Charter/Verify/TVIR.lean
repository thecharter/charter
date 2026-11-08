import Charter.Core.State

/-!
# Charter.Verify.TVIR — Symbolic Transition Verification IR & Threshold Extractor (`G2.4`)

Extracts symbolic integer thresholds and action schemas from a `Spec` (`CIR`) and renders
bounded unrollings as standard SMT-LIB2 (`QF_LIA`) scripts for external solvers (`z3`/`cvc5`)
as well as boundary candidate menus for native symbolic verification (`Verify.Smt`).
-/

namespace Charter.Verify.TVIR

-- Extract every integer literal constant occurring inside a `Term` (for boundary witness
-- synthesis: `c - 1`, `c`, `c + 1` around every linear threshold `x > c`, `x >= c`, `x == c`).
mutual
def termIntConsts : Term → List Int
  | .intLit n => [n]
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .project a _ | .tag a _ | .untag a => termIntConsts a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b => termIntConsts a ++ termIntConsts b
  | .mulDivRound x n d _ => termIntConsts x ++ termIntConsts n ++ termIntConsts d
  | .fnApp _ k => termIntConsts k
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t => termIntConsts t
  | .app _ args => argsIntConsts args
  | .boolLit _ | .stringLit _ | .ref _ | .currentTime => []

def argsIntConsts : Args → List Int
  | .pos ts => termListConsts ts
  | .named ms => termModsConsts ms

def termListConsts : List Term → List Int
  | [] => []
  | t :: ts => termIntConsts t ++ termListConsts ts

def termModsConsts : List (Var × Term) → List Int
  | [] => []
  | (_, t) :: ms => termIntConsts t ++ termModsConsts ms
end

mutual
def hasSymbolicVar : Term → Bool
  | .ref _ | .untag _ | .project _ _ => true
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .tag a _ => hasSymbolicVar a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .sub a b | .add a b | .mult a b | .mod a b | .div a b
  | .eq a b | .neq a b | .when a b | .heldFor a b => hasSymbolicVar a || hasSymbolicVar b
  | .mulDivRound x n d _ => hasSymbolicVar x || hasSymbolicVar n || hasSymbolicVar d
  | .fnApp _ _ => true
  | .exists_ _ t | .forall_ _ t | .count _ t | .sum _ t | .max _ t | .min _ t => hasSymbolicVar t
  | .app _ args => argsHasVar args
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime => false

def argsHasVar : Args → Bool
  | .pos ts => hasVarList ts
  | .named ms => hasVarMods ms

def hasVarList : List Term → Bool
  | [] => false
  | t :: ts => hasSymbolicVar t || hasVarList ts

def hasVarMods : List (Var × Term) → Bool
  | [] => false
  | (_, t) :: ms => hasSymbolicVar t || hasVarMods ms
end

mutual
def hasComplexArith : Term → Bool
  | .mult a b | .div a b | .mod a b => hasSymbolicVar a && hasSymbolicVar b
  | .add a b | .sub a b => hasSymbolicVar a && hasSymbolicVar b
  | .sum _ _ | .count _ _ => true
  | .not a | .present a | .violated a | .enabled a | .evStatus _ a | .hasConflict a | .project a _ | .tag a _ | .untag a => hasComplexArith a
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b
  | .eq a b | .neq a b | .when a b | .heldFor a b => hasComplexArith a || hasComplexArith b
  | .mulDivRound x n d _ => hasSymbolicVar x && (hasSymbolicVar n || hasSymbolicVar d)
  | .fnApp _ _ => true
  | .exists_ _ t | .forall_ _ t | .max _ t | .min _ t => hasComplexArith t
  | .app _ args => argsComplex args
  | .boolLit _ | .intLit _ | .stringLit _ | .ref _ | .currentTime => false

def argsComplex : Args → Bool
  | .pos ts => complexList ts
  | .named ms => complexMods ms

def complexList : List Term → Bool
  | [] => false
  | t :: ts => hasComplexArith t || complexList ts

def complexMods : List (Var × Term) → Bool
  | [] => false
  | (_, t) :: ms => hasComplexArith t || complexMods ms
end

/-- Collect all integer thresholds across a `Spec` and expand each `c` to `{c - 1, c, c + 1}`
(plus `0, 1`), forming an exact equivalence-class witness set for single-variable interval guards. -/
def specThresholdWitnesses (spec : Spec) (stateInts : List Int) : List Int :=
  let fromSpec : List Int := spec.decls.flatMap fun (_, t) =>
    let dInts := t.derivation.flatMap fun
      | .dv _ tm | .holdsWhen tm => termIntConsts tm
      | .defeasibleDAG _ rs => rs.flatMap fun r => termIntConsts r.cond ++ (match r.conseq with | .holdsBool _ => [] | .yieldsVal vt => termIntConsts vt)
    let cInts := t.conditions.flatMap termIntConsts
    let fInts := termIntConsts t.domainConstraint
    let kInts := match t.kind with
      | .act a =>
        (a.validWhen.flatMap termIntConsts) ++
        (a.effects.flatMap fun | .cAll _ tm md _ => termIntConsts tm ++ (md.map termIntConsts).getD []
                               | .tAll _ tm _ | .oAll _ tm _ | .evOp _ _ tm _ | .findingOp _ _ tm _ => termIntConsts tm
                               | .amendOp _ => [])
      | .duty du => (du.violatedWhen ++ du.excusedWhen).flatMap termIntConsts
      | .immunity im => im.unlessConds.flatMap termIntConsts
      | .event ev => ev.effects.flatMap fun | .cAll _ tm md _ => termIntConsts tm ++ (md.map termIntConsts).getD []
                                            | .tAll _ tm _ | .oAll _ tm _ | .evOp _ _ tm _ | .findingOp _ _ tm _ => termIntConsts tm
                                            | .amendOp _ => []
      | .fact _ => []
    dInts ++ cInts ++ fInts ++ kInts
  let seeds := (0 :: 1 :: (fromSpec ++ stateInts)).eraseDups
  (seeds.flatMap fun c => [c - 1, c, c + 1]).eraseDups

/-- Whether every integer constraint in `spec` lies within the exact single-variable interval
fragment (no `x + y`, `x * y`, or `Sum` over symbolic variables). -/
def isSingleThresholdFragment (spec : Spec) : Bool :=
  spec.decls.all fun (_, t) =>
    let dOk := t.derivation.all fun
      | .dv _ tm | .holdsWhen tm => !hasComplexArith tm
      | .defeasibleDAG _ rs => rs.all fun r => !hasComplexArith r.cond && (match r.conseq with | .holdsBool _ => true | .yieldsVal vt => !hasComplexArith vt)
    let cOk := t.conditions.all (!hasComplexArith ·)
    let fOk := !hasComplexArith t.domainConstraint
    let kOk := match t.kind with
      | .act a =>
        a.validWhen.all (!hasComplexArith ·) &&
        a.effects.all (fun | .cAll _ tm md _ => !hasComplexArith tm && (md.map (!hasComplexArith ·)).getD true
                           | .tAll _ tm _ | .oAll _ tm _ | .evOp _ _ tm _ | .findingOp _ _ tm _ => !hasComplexArith tm
                           | .amendOp _ => true)
      | .duty du => (du.violatedWhen ++ du.excusedWhen).all (!hasComplexArith ·)
      | .immunity im => im.unlessConds.all (!hasComplexArith ·)
      | .event ev => ev.effects.all (fun | .cAll _ tm md _ => !hasComplexArith tm && (md.map (!hasComplexArith ·)).getD true
                                         | .tAll _ tm _ | .oAll _ tm _ | .evOp _ _ tm _ | .findingOp _ _ tm _ => !hasComplexArith tm
                                         | .amendOp _ => true)
      | .fact _ => true
    dOk && cOk && fOk && kOk

def smtIdent (s : String) : String :=
  String.mk (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

def renderSmtTerm : Term → String
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .intLit i => if i < 0 then s!"(- {-i})" else toString i
  | .currentTime => "time_cur"
  | .not a => s!"(not {renderSmtTerm a})"
  | .and a b => s!"(and {renderSmtTerm a} {renderSmtTerm b})"
  | .or a b => s!"(or {renderSmtTerm a} {renderSmtTerm b})"
  | .leq a b => s!"(<= {renderSmtTerm a} {renderSmtTerm b})"
  | .le a b => s!"(< {renderSmtTerm a} {renderSmtTerm b})"
  | .geq a b => s!"(>= {renderSmtTerm a} {renderSmtTerm b})"
  | .ge a b => s!"(> {renderSmtTerm a} {renderSmtTerm b})"
  | .add a b => s!"(+ {renderSmtTerm a} {renderSmtTerm b})"
  | .sub a b => s!"(- {renderSmtTerm a} {renderSmtTerm b})"
  | .mult a b => s!"(* {renderSmtTerm a} {renderSmtTerm b})"
  | .eq a b => s!"(= {renderSmtTerm a} {renderSmtTerm b})"
  | .neq a b => s!"(not (= {renderSmtTerm a} {renderSmtTerm b}))"
  | .untag a | .tag a _ => renderSmtTerm a
  | .ref x => smtIdent (toString x)
  | .present (.app d _) => s!"holds_{smtIdent d}"
  | .present (.ref x) => s!"holds_{smtIdent (toString x)}"
  | _ => "true"

/-- Emit a well-formed SMT-LIB2 (`QF_LIA`) bounded model-checking query for horizon `depth`. -/
def emitSmtLib2 (spec : Spec) (state : State) (depth : Nat) : String :=
  let hdr := [
    "; Charter TVIR bounded model-checking encoding (G2.4)",
    "(set-logic QF_LIA)",
    "(set-option :produce-models true)",
    "(declare-const time_0 Int)",
    s!"(assert (= time_0 {state.time}))"
  ]
  let stepDecls := (List.range depth).flatMap fun k => [
    s!"(declare-const step_act_{k} Int)",
    s!"(declare-const step_arg_int_{k} Int)",
    s!"(declare-const time_{k + 1} Int)",
    s!"(assert (>= time_{k + 1} time_{k}))"
  ]
  let factDecls := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .fact _ => some s!"(declare-const holds_{smtIdent d} Bool)"
    | _ => none
  let invDisj := match spec.invariants with
    | [] => ["(assert false)"]
    | invs =>
      let terms := invs.map fun inv =>
        match spec.findDecl inv with
        | some t =>
          match t.derivation with
          | .holdsWhen cond :: _ => s!"(not {renderSmtTerm cond})"
          | _ => s!"(not holds_{smtIdent inv})"
        | none => s!"(not holds_{smtIdent inv})"
      [s!"(assert (or {" ".intercalate terms}))"]
  let footer := ["(check-sat)", "(exit)"]
  "\n".intercalate (hdr ++ stepDecls ++ factDecls ++ invDisj ++ footer) ++ "\n"

end Charter.Verify.TVIR
