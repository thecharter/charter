import Charter.Surface.Ast
import Charter.Core.State

/-!
# Charter.Resolve.Static — Names, types, arities, and the checked form of terms

eFLINT's static evaluation (`StaticEval.hs`, `Binders.hs`), per D2. Resolution
owns names, types, and arities (AGENTS.md, "One owner per fact"): it checks that
every type a term names is declared, infers each term's static type, inserts the
conversions eFLINT inserts (`Untag` for a primitive instance used as a value,
`Present` for an instance used as a condition, `Geq _ 1` for an integer used as
a condition, `Tag` for a value used as an instance), binds the free variables of
conditions and effects (`Exists` in conditions, `Foreach` in effects), and
desugars the duty clauses `Enforced by`, `Terminated by`, `Created by` into
violation conditions, effects, and derivations of the named acts.

Its output is the Core object the evaluator runs: a `Spec` of `TypeSpec` records
whose terms are all in checked form, and the compiled phrases. Every failure is a
`Diagnostic` with a CHR01x code (`docs/spec/diagnostics.md`). Resolution keeps
going after an error where eFLINT does (the `Eq`/`Neq` alternative), and reports
the first error of a declaration otherwise.

Phase 1 note: this stage is both "Resolve" and "Lower" of plan §3, as it is in
eFLINT, where the checked term is the runtime term. Phase 2 separates them when
Charter's additions need a resolved AST distinct from the records.
-/

namespace Charter

/-- A compiled phrase: declarations have been executed into the spec. -/
inductive CPhrase where
  | trigger (xs : List Var) (t : Term)
  | create (xs : List Var) (t : Term)
  | terminate (xs : List Var) (t : Term)
  | obfuscate (xs : List Var) (t : Term)
  | query (t : Term)
  | instQuery (mustHold : Bool) (xs : List Var) (t : Term)
  /-- Declarations executed; `init` holds the initial instances of `Param`s (D11). -/
  | onlyDecls (init : Store := [])
  | par (ps : List CPhrase)
  /-- Charter: a scenario's phrases are resolved when `charter test` runs them. -/
  | scenario (name : String) (ps : List Phrase)
  /-- Charter: `?lawful`/`?valid`/`?violated` over the instances of `t`, `xs` bound to every instance. -/
  | expect (what : Expect) (negated : Bool) (xs : List Var) (t : Term)
  /-- Charter (D7): `@ t.` and `tick.`, the clock as environment input. -/
  | setTime (t : Term)
  | tick
  /-- Charter (Law 6): `?why e`, `xs` bound to every instance. -/
  | why (xs : List Var) (t : Term)
  deriving Inhabited

namespace Resolve

/-- The static monad: a spec threaded through, errors as diagnostics, warnings
collected. -/
structure Out (α : Type) where
  spec     : Spec
  warnings : List Diagnostic
  val      : α

structure Stc (α : Type) where
  run : Spec → List Diagnostic → Except (List Diagnostic) (Out α)

instance : Monad Stc where
  pure a := ⟨fun s w => .ok ⟨s, w, a⟩⟩
  bind m f := ⟨fun s w => match m.run s w with
    | .ok o => (f o.val).run o.spec o.warnings
    | .error e => .error e⟩

def err {α} (code msg : String) : Stc α := ⟨fun _ _ => .error [Diagnostic.error code msg]⟩

def warn (code msg : String) : Stc Unit := ⟨fun s w => .ok ⟨s, w ++ [Diagnostic.warning code msg], ()⟩⟩

/-- Try `p`; on failure try `q`, reporting both errors if both fail. -/
def orElse {α} (p q : Stc α) : Stc α := ⟨fun s w => match p.run s w with
  | .ok o => .ok o
  | .error e1 => match q.run s w with
    | .ok o => .ok o
    | .error e2 => .error (e1 ++ e2)⟩

def getSpec : Stc Spec := ⟨fun s w => .ok ⟨s, w, s⟩⟩

def setSpec (s' : Spec) : Stc Unit := ⟨fun _ w => .ok ⟨s', w, ()⟩⟩

def modifySpec (f : Spec → Spec) : Stc Unit := ⟨fun s w => .ok ⟨f s, w, ()⟩⟩

/-- Run `m` against `s'`, keeping the current spec afterwards. -/
def withSpec {α} (s' : Spec) (m : Stc α) : Stc α := ⟨fun s w => match m.run s' w with
  | .ok o => .ok ⟨s, o.warnings, o.val⟩
  | .error e => .error e⟩

def withDecl {α} (d : DomId) (t : TypeSpec) (m : Stc α) : Stc α := ⟨fun s w =>
  match m.run (s.insertDecl d t) w with
  | .ok o => .ok ⟨s, o.warnings, o.val⟩
  | .error e => .error e⟩

def getDom (d : DomId) : Stc Domain := do
  match (← getSpec).findDecl d with
  | some t => return t.domain
  | none => err "CHR010" s!"undeclared type {d}"

def getDecl (d : DomId) : Stc TypeSpec := do
  match (← getSpec).findDecl d with
  | some t => return t
  | none => err "CHR010" s!"undeclared type {d}"

/-! ## Free variables (eFLINT `Binders.hs`) -/

def union (a b : List Var) : List Var := a ++ b.filter (fun x => !a.contains x)
def diff (a b : List Var) : List Var := a.filter (fun x => !b.contains x)

mutual
def freeVars (spec : Spec) : Term → List Var
  | .boolLit _ | .intLit _ | .stringLit _ | .currentTime => []
  | .ref x => [x]
  | .app d args =>
    match spec.findDecl d with
    | some t =>
      match t.domain with
      | .products xs =>
        -- components not given as arguments stay free (eFLINT binds them by name)
        let named : List Var := match args with
          | .named ms => ms.map (·.1)
          | .pos ts => xs.take ts.length
        union (diff xs named) (freeVarsArgs spec args)
      | _ => freeVarsArgs spec args
    | none => freeVarsArgs spec args
  | .not t | .present t | .violated t | .enabled t | .project t _ | .tag t _ | .untag t => freeVars spec t
  | .heldFor t d => union (freeVars spec t) (freeVars spec d)
  | .and a b | .or a b | .leq a b | .geq a b | .ge a b | .le a b | .mult a b | .mod a b
  | .div a b | .sub a b | .add a b | .eq a b | .neq a b | .when a b => union (freeVars spec a) (freeVars spec b)
  | .exists_ xs t | .forall_ xs t | .count xs t | .max xs t | .min xs t | .sum xs t => diff (freeVars spec t) xs
def freeVarsArgs (spec : Spec) : Args → List Var
  | .pos ts => freeVarsList spec ts
  | .named ms => freeVarsMods spec ms
def freeVarsList (spec : Spec) : List Term → List Var
  | [] => []
  | t :: ts => union (freeVars spec t) (freeVarsList spec ts)
def freeVarsMods (spec : Spec) : List (Var × Term) → List Var
  | [] => []
  | (_, t) :: ms => union (freeVars spec t) (freeVarsMods spec ms)
end

def checkKnownType (xs : List Var) : Stc Unit := do
  let spec ← getSpec
  xs.forM fun x =>
    if (spec.findDecl (spec.removeDecoration x)).isNone then
      err "CHR010" s!"undeclared type or placeholder `{x}`"
    else pure ()

def freeVarsChecked (t : Term) : Stc (List Var) := do
  let xs := freeVars (← getSpec) t
  checkKnownType xs
  return xs

/-! ## Domains and types -/

/-- Whether a value of the first domain converts to the second (eFLINT `match_domain`). -/
def matchDomain : Domain → Domain → Bool
  | .anyString, .anyString => true
  | .strings _, .anyString => true
  | .anyString, .strings _ => false
  | .strings s1, .strings s2 => s1.all s2.contains
  | .anyString, _ => false
  | .strings _, _ => false
  | .anyInt, .anyInt => true
  | .ints _, .anyInt => true
  | .anyInt, .ints _ => true
  | .ints i1, .ints i2 => i1.all i2.contains
  | .anyInt, _ => false
  | .ints _, _ => false
  | .time, .time => true
  | .time, _ => false
  | .duration, .duration => true
  | .duration, _ => false
  | .products r, .products r' => r == r'
  | .products _, _ => false

def matchType (ty : Ty) (dom : Domain) : Stc Bool := do
  match ty with
  | .tagged d => return matchDomain (← getDom d) dom
  | .ints => return match dom with | .anyInt | .ints _ => true | _ => false
  | .strings => return match dom with | .anyString | .strings _ => true | _ => false
  | .time => return match dom with | .time => true | _ => false
  | .duration => return match dom with | .duration => true | _ => false
  | .bool => return false

/-- A term built only from literals and arithmetic: the only integer that converts to a
`Time` or a `Duration` by demand (D7). -/
def literalArith : Term → Bool
  | .intLit _ => true
  | .add a b | .sub a b | .mult a b | .div a b | .mod a b => literalArith a && literalArith b
  | _ => false

/-- The result type of `+`/`-` over integers, times, and durations (D7), or `none`. -/
def arithTy (isSub : Bool) : Ty → Ty → Option Ty
  | .ints, .ints => some .ints
  | .time, .duration => some .time
  | .duration, .time => if isSub then none else some .time
  | .duration, .duration => some .duration
  | .time, .time => if isSub then some .duration else none
  | _, _ => none

/-! ## Terms -/

def convErr {α} (source target : Ty) : Stc α :=
  err "CHR012" s!"cannot use {source} where {target} is needed"

/-- D15 (brief B11): a binder over an act whose domain is not enumerable and that has a
`Holds when` sees only the act's assigned instances; the rule is judged per instance and
never materialised, so the binder is almost never what the author meant. CHR025 says so. -/
def warnJudgedBinders (xs : List Var) : Stc Unit := do
  let spec ← getSpec
  xs.forM fun x => do
    let d := spec.removeDecoration x
    match spec.judgedAct d with
    | some _ => warn "CHR025" s!"a binder over {d} sees only its assigned instances: the domain of {d} is not enumerable and its Holds when is judged per instance, never materialised (D15)"
    | none => pure ()

mutual

/-- Infer the type of a term and rewrite it into checked form (eFLINT `compile_term`). -/
def compileTerm : Nat → Term → Stc (Term × Ty)
  | 0, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, t0 => do
    let spec ← getSpec
    match t0 with
    | .currentTime => return (t0, .time)
    | .stringLit _ => return (t0, .strings)
    | .intLit _ => return (t0, .ints)
    | .boolLit _ => return (t0, .bool)
    | .ref x => checkKnownType [x]; return (t0, .tagged (spec.removeDecoration x))
    | .app d args =>
      checkKnownType [⟨d, ""⟩]
      let isProduct := match spec.findDecl d with
        | some t => match t.domain with | .products _ => true | _ => false
        | none => false
      if isProduct then
        let args' ← compileArguments fuel d args
        return (.app d args', .tagged d)
      else compilePrimitiveApplication fuel d args
    | .tag _ _ => err "CHR003" "tagging `e:t` is an internal operation and cannot be written"
    | .untag t => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged d =>
        match spec.findDecl d with
        | none => err "CHR003" "untagging is an internal operation"
        | some decl => match decl.domain with
          | .strings _ | .anyString => return (.untag t', .strings)
          | .ints _ | .anyInt => return (.untag t', .ints)
          | .time => return (.untag t', .time)
          | .duration => return (.untag t', .duration)
          | _ => err "CHR003" "untagging is an internal operation"
      | _ => err "CHR003" "untagging is an internal operation"
    | .not t => do let t' ← convertTerm fuel t .bool; return (.not t', .bool)
    | .and a b => do let a' ← convertTerm fuel a .bool; let b' ← convertTerm fuel b .bool; return (.and a' b', .bool)
    | .or a b => do let a' ← convertTerm fuel a .bool; let b' ← convertTerm fuel b .bool; return (.or a' b', .bool)
    | .geq a b => do let (a', b') ← compileCompare fuel a b; return (.geq a' b', .bool)
    | .leq a b => do let (a', b') ← compileCompare fuel a b; return (.leq a' b', .bool)
    | .le a b => do let (a', b') ← compileCompare fuel a b; return (.le a' b', .bool)
    | .ge a b => do let (a', b') ← compileCompare fuel a b; return (.ge a' b', .bool)
    | .mult a b => do let (a', b', ty) ← compileScale fuel false a b; return (.mult a' b', ty)
    | .mod a b => do let a' ← convertTerm fuel a .ints; let b' ← convertTerm fuel b .ints; return (.mod a' b', .ints)
    | .div a b => do let (a', b', ty) ← compileScale fuel true a b; return (.div a' b', ty)
    | .sub a b => do let (a', b', ty) ← compileArith fuel true a b; return (.sub a' b', ty)
    | .add a b => do let (a', b', ty) ← compileArith fuel false a b; return (.add a' b', ty)
    | .heldFor t d => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged _ =>
        let d' ← convertTerm fuel d .duration
        return (.heldFor t' d', .bool)
      | _ => err "CHR015" s!"Held({t}) needs an instance, not {ty}"
    | .sum xs t => do warnJudgedBinders xs; let t' ← convertTerm fuel t .ints; return (.sum xs t', .ints)
    | .eq a b =>
      orElse
        (do let (a', ta) ← compileTerm fuel a; let b' ← convertTerm fuel b ta; return (.eq a' b', .bool))
        (do let (b', tb) ← compileTerm fuel b; let a' ← convertTerm fuel a tb; return (.eq a' b', .bool))
    | .neq a b =>
      orElse
        (do let (a', ta) ← compileTerm fuel a; let b' ← convertTerm fuel b ta; return (.neq a' b', .bool))
        (do let (b', tb) ← compileTerm fuel b; let a' ← convertTerm fuel a tb; return (.neq a' b', .bool))
    | .count xs t => do warnJudgedBinders xs; let (t', _) ← compileTerm fuel t; return (.count xs t', .ints)
    | .max xs t => do warnJudgedBinders xs; let t' ← convertTerm fuel t .ints; return (.max xs t', .ints)
    | .min xs t => do warnJudgedBinders xs; let t' ← convertTerm fuel t .ints; return (.min xs t', .ints)
    | .when a c => do let (a', ta) ← compileTerm fuel a; let c' ← convertTerm fuel c .bool; return (.when a' c', ta)
    | .present t => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged _ => return (.present t', .bool)
      | _ => err "CHR015" s!"Holds({t}) needs an instance, not {ty}"
    | .violated t => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged _ => return (.violated t', .bool)
      | _ => err "CHR015" s!"Violated({t}) needs an instance, not {ty}"
    | .enabled t => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged _ => return (.enabled t', .bool)
      | _ => err "CHR015" s!"Enabled({t}) needs an instance, not {ty}"
    | .exists_ xs t => do warnJudgedBinders xs; let t' ← convertTerm fuel t .bool; return (.exists_ xs t', .bool)
    | .forall_ xs t => do warnJudgedBinders xs; let t' ← convertTerm fuel t .bool; return (.forall_ xs t', .bool)
    | .project t x => do
      let (t', ty) ← compileTerm fuel t
      match ty with
      | .tagged d =>
        match ← getDom d with
        | .products xs =>
          if xs.contains x then return (.project t' x, .tagged (spec.removeDecoration x))
          else err "CHR016" s!"{t}.{x}: {d} has no component {x} (its components are {", ".intercalate (xs.map toString)})"
        | _ => err "CHR016" s!"{t}.{x}: {d} is not a product type"
      | _ => err "CHR016" s!"{t}.{x}: the value is {ty}, not an instance of a product type"

/-- Check a term against an expected type, inserting a conversion (eFLINT `convert_term`). -/
def convertTerm : Nat → Term → Ty → Stc Term
  | 0, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, t, ty => do
    let (t', ty') ← compileTerm fuel t
    if ty' == ty then return t'
    else match ty with
    | .strings =>
      match ty' with
      | .tagged d => if matchDomain (← getDom d) .anyString then return .untag t' else convErr ty' ty
      | _ => convErr ty' ty
    | .ints =>
      match ty' with
      | .tagged d => if matchDomain (← getDom d) .anyInt then return .untag t' else convErr ty' ty
      | _ => convErr ty' ty
    | .bool =>
      match ty' with
      | .ints => return .geq t' (.intLit 1)
      | .tagged _ => return .present t'
      | _ => convErr ty' ty
    | .tagged d =>
      if ← matchType ty' (← getDom d) then return .tag t' d else convErr ty' ty
    | .time =>
      match ty' with
      | .ints => if literalArith t' then return t' else convErr ty' ty
      | .tagged d => if matchDomain (← getDom d) .time then return .untag t' else convErr ty' ty
      | _ => convErr ty' ty
    | .duration =>
      match ty' with
      | .ints => if literalArith t' then return t' else convErr ty' ty
      | .tagged d => if matchDomain (← getDom d) .duration then return .untag t' else convErr ty' ty
      | _ => convErr ty' ty

/-- An instance of an integer, time, or duration type used as its value. -/
def asNumber (t : Term) (ty : Ty) : Stc (Term × Ty) := do
  match ty with
  | .tagged d => match ← getDom d with
    | .anyInt | .ints _ => pure (Term.untag t, Ty.ints)
    | .time => pure (Term.untag t, Ty.time)
    | .duration => pure (Term.untag t, Ty.duration)
    | _ => convErr ty .ints
  | _ => pure (t, ty)

/-- Two operands of a comparison, resolved to one type among integer, time, duration
(D7: a time is never compared with a duration or an integer other than a literal). -/
def compileCompare : Nat → Term → Term → Stc (Term × Term)
  | 0, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, a, b => do
    let (a', ta) ← compileTerm fuel a
    let (b', tb) ← compileTerm fuel b
    let (a', ta) ← asNumber a' ta
    let (b', tb) ← asNumber b' tb
    let numeric (t : Ty) : Bool := t == .ints || t == .time || t == .duration
    if !(numeric ta) then convErr ta .ints
    else if !(numeric tb) then convErr tb .ints
    else if ta == tb then return (a', b')
    else if ta == .ints && literalArith a' then return (a', b')
    else if tb == .ints && literalArith b' then return (a', b')
    else convErr tb ta

/-- `+`/`-` over integers, times, and durations (D7). -/
def compileArith : Nat → Bool → Term → Term → Stc (Term × Term × Ty)
  | 0, _, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, isSub, a, b => do
    let (a', ta) ← compileTerm fuel a
    let (b', tb) ← compileTerm fuel b
    -- an instance of an integer/time/duration type is used as its value
    let (a', ta) ← asNumber a' ta
    let (b', tb) ← asNumber b' tb
    match arithTy isSub ta tb with
    | some ty => return (a', b', ty)
    | none =>
      -- a literal side takes the other's type (`Current Time + 10`)
      if ta == .ints && literalArith a' && (tb == .time || tb == .duration) then
        match arithTy isSub (if tb == .time && isSub then .time else tb) tb with
        | _ => return (a', b', if isSub && tb == .time then .time else tb)
      else if tb == .ints && literalArith b' && (ta == .time || ta == .duration) then
        return (a', b', ta)
      else err "CHR012" s!"cannot {if isSub then "subtract" else "add"} {tb} {if isSub then "from" else "to"} {ta} (D7: a time and a duration combine, two times only subtract)"
/-- `*`/`/` over integers and durations (D16, brief B12): `Int * Int : Int`,
`Duration * Int : Duration`, `Int * Duration : Duration`, `Duration / Int : Duration`
(rounding toward negative infinity, as `Int /`); at most one operand of `*` may be a
duration, an instant is never scaled, and `Int / Duration` has no meaning. A literal
beside a duration resolves to `Int`, so `base * 2` is unambiguous (D7). -/
def compileScale : Nat → Bool → Term → Term → Stc (Term × Term × Ty)
  | 0, _, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, isDiv, a, b => do
    let (a', ta) ← compileTerm fuel a
    let (b', tb) ← compileTerm fuel b
    let (a', ta) ← asNumber a' ta
    let (b', tb) ← asNumber b' tb
    let op := if isDiv then "/" else "*"
    match ta, tb with
    | .ints, .ints => return (a', b', .ints)
    | .duration, .ints => return (a', b', .duration)
    | .ints, .duration =>
      if isDiv then err "CHR012" s!"cannot divide an integer by a duration (D16: `Duration / Int` is a duration; `Int / Duration` has no meaning)"
      else return (a', b', .duration)
    | .duration, .duration =>
      err "CHR012" s!"cannot {if isDiv then "divide" else "multiply"} a duration by a duration (D16: in `{op}` at most one operand may be a duration)"
    | .time, _ | _, .time => err "CHR012" s!"cannot use an instant in `{op}` (D16: a time is never scaled)"
    | .ints, other | .duration, other => convErr other .ints
    | other, _ => convErr other .ints

def compilePrimitiveApplication : Nat → DomId → Args → Stc (Term × Ty)
  | 0, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, d, args => do
    let dom ← getDom d
    let e : Stc (Term × Ty) := err "CHR018" s!"{d} is a primitive type and takes exactly one positional argument"
    let prim (t : Term) (ty : Ty) : Stc (Term × Ty) := do
      let t' ← convertTerm fuel t ty
      return (.tag t' d, .tagged d)
    match dom, args with
    | _, .pos (_ :: _ :: _) => e
    | .anyString, .pos [a] => prim a .strings
    | .strings [s], .pos [] => prim (.stringLit s) .strings
    | .strings [s], .named [] => prim (.stringLit s) .strings
    | .strings _, .pos [a] => prim a .strings
    | .anyInt, .pos [a] => prim a .ints
    | .ints [i], .named [] => prim (.intLit i) .ints
    | .ints [i], .pos [] => prim (.intLit i) .ints
    | .ints _, .pos [a] => prim a .ints
    | .time, .pos [a] => prim a .time
    | .duration, .pos [a] => prim a .duration
    | _, _ => e

/-- Positional arguments become named modifiers; every modifier is checked
against its variable's type (eFLINT `compile_arguments`, `compile_modifiers`). -/
def compileArguments : Nat → DomId → Args → Stc Args
  | 0, _, _ => err "CHR003" "expression too deeply nested to resolve"
  | fuel + 1, d, args => do
    match args with
    | .named ms => return .named (← compileMods fuel ms)
    | .pos ts =>
      match ← getDom d with
      | .products xs =>
        if xs.length == ts.length then return .named (← compileMods fuel (xs.zip ts))
        else err "CHR011" s!"{d} has {xs.length} component(s), {ts.length} given"
      | _ => err "CHR021" s!"{d} is not a composite type and cannot take positional arguments"

def compileMods : Nat → List (Var × Term) → Stc (List (Var × Term))
  | 0, _ => err "CHR003" "expression too deeply nested to resolve"
  | _, [] => return []
  | fuel + 1, (x, t) :: ms => do
    let spec ← getSpec
    let t' ← convertTerm fuel t (.tagged (spec.removeDecoration x))
    return (x, t') :: (← compileMods fuel ms)

end

def termFuel : Nat := 100000

/-- Compile a condition of type `d` (eFLINT `convert_precon`): checked as a
boolean, with variables other than `d`'s components existentially bound. -/
def convertPrecon (d : DomId) (tspec : TypeSpec) (t : Term) : Stc Term := do
  let xs := match tspec.domain with | .products xs => xs | _ => [⟨d, ""⟩]
  let cond ← convertTerm termFuel t .bool
  let fs ← freeVarsChecked cond
  let unbound := diff fs xs
  return if unbound.isEmpty then cond else .exists_ unbound cond

def compileViolationCondition (d : DomId) (t : Term) : Stc Term := do
  let xs := match ← getDom d with | .products xs => xs | _ => [⟨d, ""⟩]
  let t' ← convertTerm termFuel t .bool
  let fs ← freeVarsChecked t'
  let unbound := diff fs xs
  return if unbound.isEmpty then t' else .exists_ unbound t'

def compileSync (bound : List Var) (s : Sync) : Stc Sync := do
  let (t', ty) ← compileTerm termFuel s.t
  match ty with
  | .tagged _ =>
    let fs ← freeVarsChecked t'
    return ⟨s.xs ++ diff fs (s.xs ++ bound), t'⟩
  | _ => err "CHR017" s!"`Syncs with {s.t}` is not an act or event instance"

def compileEffect' (mk : List Var → Term → Effect) (bound xs : List Var) (t : Term) : Stc Effect := do
  let (t', _) ← compileTerm termFuel t
  let fs ← freeVarsChecked t'
  warnJudgedBinders (xs ++ diff fs (bound ++ xs))
  return mk (xs ++ diff fs (bound ++ xs)) t'

def compileEffect (bound : List Var) : Effect → Stc Effect
  | .cAll xs t none => compileEffect' (fun xs t => .cAll xs t none) bound xs t
  | .cAll xs t (some d) => do
    -- the expiry's free variables (a `Param`, 014.1) are bound with the effect's
    let d' ← convertTerm termFuel d .duration
    let dfs ← freeVarsChecked d'
    compileEffect' (fun ys t => .cAll (ys ++ diff dfs (bound ++ ys)) t (some d')) bound xs t
  | .tAll xs t => compileEffect' .tAll bound xs t
  | .oAll xs t => compileEffect' .oAll bound xs t

def compileDerivation (bound : List Var) (d : DomId) : Derivation → Stc Derivation
  | .holdsWhen t => do
    let t' ← convertTerm termFuel t .bool
    let fs ← freeVarsChecked t'
    let unbound := diff fs bound
    warnJudgedBinders unbound
    return .holdsWhen (if unbound.isEmpty then t' else .exists_ unbound t')
  | .dv xs t => do
    let t' ← convertTerm termFuel t (.tagged d)
    let fs ← freeVarsChecked t'
    warnJudgedBinders (xs ++ diff fs xs)
    return .dv (xs ++ diff fs xs) t'

/-- Every name in `as` must be a declared act (Charter's `Except under` and `Against`). -/
def checkActs (what : String) (as : List DomId) : Stc Unit := do
  let spec ← getSpec
  as.forM fun a =>
    match spec.findDecl a with
    | some t => match t.kind with
      | .act _ => pure ()
      | k => err "CHR022" s!"`{what}` names {a}, which is {k.lowerName}, not an act"
    | none => err "CHR010" s!"undeclared type {a} in `{what}`"

/-- `Terminated by a` and `Created by a` bind the duty's components from the act's (006.4):
every component of the duty must be one of `a`'s, by name, or the effect added to `a` would
leave it unbound and fail at run time (CHR102 on the declaration, seen twice on
2026-10-25). CHR027 says so at resolution instead. -/
def checkBinds (what : String) (d : DomId) (xs : List Var) (as : List DomId) : Stc Unit := do
  let spec ← getSpec
  as.forM fun a =>
    match spec.findDecl a with
    | none => pure () -- CHR010 is reported where the act is used
    | some _ =>
      let ys := spec.components a
      match xs.find? (fun x => !ys.contains x) with
      | some x => err "CHR027" s!"`{what} {a}` on {d}: the component {x} of {d} is not a component of {a}, so {a} cannot bind it"
      | none => pure ()

/-- `Overridden by` names duties (007.3): anything else is CHR026. -/
def checkDuties (what : String) (ds : List DomId) : Stc Unit := do
  let spec ← getSpec
  ds.forM fun a =>
    match spec.findDecl a with
    | some t => match t.kind with
      | .duty _ => pure ()
      | k => err "CHR026" s!"`{what}` names {a}, which is {k.lowerName}, not a duty"
    | none => err "CHR010" s!"undeclared type {a} in `{what}`"

def compileKind (d : DomId) (tspec : TypeSpec) : Kind → Stc Kind
  | .act a => do
    let xs := match tspec.domain with | .products xs => xs | _ => []
    let effects ← a.effects.mapM (compileEffect xs)
    let syncs ← a.syncs.mapM (compileSync xs)
    let validWhen ← a.validWhen.mapM (convertPrecon d tspec)
    checkActs "Except under" a.exceptUnder
    return .act { a with effects, syncs, validWhen }
  | .immunity i => do
    let unlessConds ← i.unlessConds.mapM (convertPrecon d tspec)
    checkActs "Against" i.against
    return .immunity { i with unlessConds }
  | .event e => do
    let xs := match tspec.domain with | .products xs => xs | _ => []
    let effects ← e.effects.mapM (compileEffect xs)
    let syncs ← e.syncs.mapM (compileSync xs)
    return .event { e with effects, syncs }
  | .duty ds => do
    let vconds ← ds.violatedWhen.mapM (compileViolationCondition d)
    checkDuties "Overridden by" ds.overriddenBy
    return .duty { ds with violatedWhen := vconds }
  | k => return k

/-- Compile a whole declaration with itself in scope (eFLINT `compile_type_spec`). -/
def compileTypeSpec (d : DomId) (tspec : TypeSpec) : Stc TypeSpec :=
  withDecl d tspec do
    match tspec.domain with
    | .products xs => checkKnownType xs
    | _ => pure ()
    let xs := match tspec.domain with | .products xs => xs | _ => [⟨d, ""⟩]
    let derivation ← tspec.derivation.mapM (compileDerivation xs d)
    let kind ← compileKind d tspec tspec.kind
    let conditions ← tspec.conditions.mapM (convertPrecon d tspec)
    let filter ← convertTerm termFuel tspec.domainConstraint .bool
    let ffs ← freeVarsChecked filter
    let unbound := diff ffs xs
    let domainConstraint := if unbound.isEmpty then filter else .exists_ unbound filter
    return { tspec with derivation, kind, conditions, domainConstraint }

/-- Compile the clauses of an `Extend` (or of a declaration's own clause list)
into extensions of named types (eFLINT `compile_ext`). -/
def compileExt (ty : DomId) (clauses : List ModClause) : Stc (List (DomId × List ModClause)) := do
  let spec ← getSpec
  match spec.lookupDecl ty with
  | none => err "CHR013" s!"cannot extend {ty}: no such type"
  | some tspec =>
    let xs := match tspec.domain with | .products xs => xs | _ => [⟨ty, ""⟩]
    let one (c : ModClause) : Stc (List (DomId × List ModClause)) := do
      match c with
      | .conditionedBy conds => return [(ty, [.conditionedBy (← conds.mapM (convertPrecon ty tspec))])]
      | .derivation dvs => return [(ty, [.derivation (← dvs.mapM (compileDerivation xs ty))])]
      | .postCond effs => return [(ty, [.postCond (← effs.mapM (compileEffect xs))])]
      | .sync ss => return [(ty, [.sync (← ss.mapM (compileSync xs))])]
      | .violation vts => return [(ty, [.violation (← vts.mapM (compileViolationCondition ty))])]
      | .enforcingActs as =>
        let viols ← as.mapM fun a => do
          let (t, _) ← compileTerm termFuel (.enabled (.app a (.named [])))
          return (ty, [ModClause.violation [t]])
        return (ty, [.enforcingActs as]) :: viols
      | .terminatedBy as =>
        checkBinds "Terminated by" ty xs as
        let posts ← as.mapM fun a => do
          let e ← compileEffect' .tAll xs [] (.app ty (.named []))
          return (a, [ModClause.postCond [e]])
        let holds ← as.mapM fun a => do
          let dv ← compileDerivation xs a (.holdsWhen (.present (.app ty (.named []))))
          return (a, [ModClause.derivation [dv]])
        return (ty, [.terminatedBy as]) :: (posts ++ holds)
      | .overriddenBy ds =>
        checkDuties "Overridden by" ds
        return [(ty, [.overriddenBy ds])]
      | .createdBy as =>
        checkBinds "Created by" ty xs as
        let posts ← as.mapM fun a => do
          let e ← compileEffect' (fun xs t => .cAll xs t none) xs [] (.app ty (.named []))
          return (a, [ModClause.postCond [e]])
        return (ty, [.createdBy as]) :: posts
      | .strings ss =>
        match tspec.kind, tspec.domain with
        | .fact _, .anyString | .fact _, .strings _ => return [(ty, [.strings ss])]
        | .fact _, _ => err "CHR014" s!"cannot extend {ty} with atoms: its domain is not a string domain"
        | _, _ => err "CHR014" s!"cannot extend {ty}: only a Fact with a primitive domain can be given new instances by `Identified by`"
      | .ints is =>
        match tspec.kind, tspec.domain with
        | .fact _, .anyInt | .fact _, .ints _ => return [(ty, [.ints is])]
        | .fact _, _ => err "CHR014" s!"cannot extend {ty} with integers: its domain is not an integer domain"
        | _, _ => err "CHR014" s!"cannot extend {ty}: only a Fact with a primitive domain can be given new instances by `Identified by`"
      | .close => return [(ty, [.close])]
      | .open => return [(ty, [.open])]
      | .validWhen ts => return [(ty, [.validWhen (← ts.mapM (convertPrecon ty tspec))])]
      | .exceptUnder as => checkActs "Except under" as; return [(ty, [.exceptUnder as])]
      | .against as => checkActs "Against" as; return [(ty, [.against as])]
      | .unlessCond ts => return [(ty, [.unlessCond (← ts.mapM (convertPrecon ty tspec))])]
      | .fromSpan c text => return [(ty, [.fromSpan c text])]
      | .dueWithin d =>
        -- a requirement duty: violated once it has been held for `d` (006.7)
        match tspec.kind with
        | .duty _ =>
          let d' ← convertTerm termFuel d .duration
          let v ← compileViolationCondition ty (.heldFor (.app ty (.named [])) d')
          return [(ty, [.violation [v]])]
        | k => err "CHR003" s!"`Due within` applies to a Duty, not {k.lowerName}"
    let parts ← clauses.mapM one
    return parts.flatten

def executeExt (d : DomId) (cs : List ModClause) : Stc Unit :=
  modifySpec fun s => s.adjustDecl d (TypeSpec.applyExt cs)

def builtins : List DomId := ["int", "string", "actor"]

/-- Expand every `Use` into the renamed body of its module (D8): parameters are
replaced by the arguments, the names the module declares are prefixed with
`prefix-` when `As prefix` is given, and the module's `Use`s expand in turn. -/
def expandUses : Nat → List Decl → Stc (List Decl)
  | 0, _ => err "CHR003" "modules nest too deeply"
  | fuel + 1, ds => do
    -- register the block's modules first so a Use may precede its Module in the block
    ds.forM fun d => match d with
      | .module n ps body => modifySpec fun s => { s with modules := (n, ps, body) :: s.modules.filter (·.1 != n) }
      | _ => pure ()
    let spec ← getSpec
    let expanded ← ds.mapM fun d => match d with
      | .use n args pre =>
        match spec.modules.find? (·.1 == n) with
        | none => err "CHR023" s!"Use {n}: no such module"
        | some (_, ps, body) =>
          if ps.length != args.length then
            err "CHR023" s!"Use {n}: the module takes {ps.length} parameter(s), {args.length} given"
          else
            let declared := declaredNames body
            let f (x : DomId) : DomId :=
              match (ps.zip args).find? (·.1 == x) with
              | some (_, a) => a
              | none => if declared.contains x then (match pre with | some p => p ++ "-" ++ x | none => x) else x
            expandUses fuel (body.map (Decl.mapDom f))
      | .module .. => pure []
      | d => pure [d]
    return expanded.flatten

/-- Execute a block of declarations (eFLINT `compile_phrase (PDeclBlock ds)`):
`Use`s expanded (D8); new types and placeholders first, as written; then each new type
is compiled with every new name in scope; then the extensions. Returns the initial
instances of the block's `Param`s (D11). -/
def executeDecls (ds : List Decl) : Stc Store := do
  let ds ← expandUses 32 ds
  let (inits, exts) := ds.partition Decl.isInitial
  let init : Store := inits.filterMap fun d => match d with
    | .param n _ v => some ((.int v, n), .holdsTrue none none)
    | _ => none
  -- 1. insert the raw declarations so that mutually referring types resolve
  -- (`forM`, not `for`: see AGENTS.md, common mistakes)
  inits.forM fun d => do
    match d with
    | .typeDecl ty tspec =>
      let spec ← getSpec
      if (spec.lookupDecl ty).isSome && !builtins.contains ty then
        warn "CHR019" s!"{ty} is declared again; the new declaration replaces the earlier one (B9 pending)"
      -- a `Function` is a product of exactly two components (003.7); eFLINT silently
      -- ignores every assignment to one that is not, so Charter refuses the declaration
      if tspec.restriction == some .function then
        match tspec.domain with
        | .products [_, _] => pure ()
        | _ => err "CHR024" s!"Function {ty}: the domain must be a product of exactly two components"
      setSpec (spec.insertDecl ty tspec)
    | .placeholder f t => modifySpec (·.insertAlias f t)
    | .clause c => modifySpec (·.insertClause c)
    | .document p => modifySpec (fun s => { s with document := some p })
    | .param n dom _ =>
      let spec ← getSpec
      if (spec.lookupDecl n).isSome then
        warn "CHR019" s!"{n} is declared again; the new declaration replaces the earlier one (B9 pending)"
      setSpec (spec.insertDecl n { kind := .fact {}, domain := dom, restriction := some .var })
    | .module .. => pure ()
    | .use .. => pure ()
    | .typeExt .. => pure ()
  -- a placeholder may name a type declared later in the same block (eFLINT inserts
  -- all of them first); check the targets once every declaration is in
  inits.forM fun d => do
    match d with
    | .placeholder _ t => checkKnownType [⟨t, ""⟩]
    | _ => pure ()
  -- 2. compile each new type's own terms
  inits.forM fun d => do
    match d with
    | .typeDecl ty tspec =>
      let compiled ← compileTypeSpec ty tspec
      modifySpec (·.insertDecl ty compiled)
    | _ => pure ()
  -- 3. extensions, in order
  exts.forM fun d => do
    match d with
    | .typeExt ty clauses =>
      let parts ← compileExt ty clauses
      parts.forM fun part => executeExt part.1 part.2
    | _ => pure ()
  return init

/-- Compile a transition phrase's term and bind its free variables (eFLINT
`compile_trans_term`). -/
def compileTransTerm (xs : List Var) (t : Term) : Stc (List Var × Term) := do
  let fs ← freeVarsChecked t
  let unbound := diff fs xs
  let (t', _) ← compileTerm termFuel t
  return (xs ++ unbound, t')

/-- Compile a query: free variables are existentially bound, inside the negation
for `?!e` (eFLINT `compile_stmt (Query t)`). -/
def compileQuery (t0 : Term) : Stc Term := do
  let spec ← getSpec
  let fs := freeVars spec t0
  let t1 := if fs.isEmpty then t0 else match t0 with
    | .not inner => .not (.exists_ fs inner)
    | _ => .exists_ fs t0
  match fs.find? (fun x => (spec.findDecl (spec.removeDecoration x)).isNone) with
  | some x => err "CHR010" s!"undeclared type {spec.removeDecoration x} in query"
  | none => convertTerm termFuel t1 .bool

/-- Compile one phrase, executing its declarations into the spec (eFLINT `compile_phrase`). -/
def compilePhrase : Nat → Phrase → Stc CPhrase
  | 0, _ => err "CHR003" "phrase too deeply nested"
  | fuel + 1, p => do
    match p with
    | .trigger xs t => let (xs', t') ← compileTransTerm xs t; return .trigger xs' t'
    | .create xs t => let (xs', t') ← compileTransTerm xs t; return .create xs' t'
    | .terminate xs t => let (xs', t') ← compileTransTerm xs t; return .terminate xs' t'
    | .obfuscate xs t => let (xs', t') ← compileTransTerm xs t; return .obfuscate xs' t'
    | .query t => return .query (← compileQuery t)
    | .instQuery b xs t =>
      let fs ← freeVarsChecked t
      let (t', _) ← compileTerm termFuel t
      warnJudgedBinders (xs ++ diff fs xs)
      return .instQuery b (xs ++ diff fs xs) t'
    | .decls ds => return .onlyDecls (← executeDecls ds)
    | .why t =>
      let (t', ty) ← compileTerm termFuel t
      match ty with
      | .tagged _ =>
        let fs ← freeVarsChecked t'
        return .why fs t'
      | _ => err "CHR015" s!"?why needs an instance, not {ty}"
    | .scenario name ps => return .scenario name ps
    | .setTime t => return .setTime (← convertTerm termFuel t .time)
    | .tick => return .tick
    | .expect w neg t =>
      let (t', ty) ← compileTerm termFuel t
      match ty with
      | .tagged _ =>
        let fs ← freeVarsChecked t'
        return .expect w neg fs t'
      | _ => err "CHR015" s!"?{w.name} needs an act or duty instance, not {ty}"
    | .par ps =>
      -- declarations in a block are executed first, then the other phrases compiled
      let decls := ps.flatMap fun | .decls ds => ds | _ => []
      let rest := ps.filter fun | .decls _ => false | _ => true
      let init ← executeDecls decls
      let cs ← rest.mapM (compilePhrase fuel)
      return .par (.onlyDecls init :: cs)

end Resolve

/-- Resolve one phrase against a spec: the compiled phrase and the updated spec, or
diagnostics. Warnings are returned alongside. -/
def resolvePhrase (spec : Spec) (p : Phrase) : Except (List Diagnostic) (Spec × CPhrase × List Diagnostic) :=
  match (Resolve.compilePhrase 10000 p).run spec [] with
  | .ok o => .ok (o.spec, o.val, o.warnings)
  | .error e => .error e

end Charter
