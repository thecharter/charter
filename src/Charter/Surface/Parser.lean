import Charter.Surface.Lexer
import Charter.Surface.Ast

/-!
# Charter.Surface.Parser — The eFLINT core grammar

A deterministic recursive-descent parser for the grammar of eFLINT 4.1
(`Parse.hs`), producing `Charter.Item`s: directives and phrases, where a phrase
is a trigger, `+`/`-`/`~` effect, query, instance query, block of declarations,
or `{ … }` parallel block.

eFLINT's parser is generalised (GLL) and keeps every parse; this one commits.
Where eFLINT's grammar is ambiguous the choice made here is written down:

- **Expression precedence**, lowest to highest: `When`/`Where` (left), `||`,
  `&&`, comparisons (`== != <= >= < >`, non-associative), `+ -` (left),
  `* / %` (left), prefix `!`/`Not`/`Holds`/`Present`/`Violated`/`Enabled`,
  postfix projection `.x` and tagging `:t`, then atoms. eFLINT marks `+ - * / %`
  right-greedy and the comparisons left-greedy; the corpus does not distinguish
  the two readings and left association is the arithmetic convention.
- **A declaration block ends** at the first token that is neither a clause
  keyword of the current frame nor a continuation of the expression being
  parsed; the block as a whole ends when the next token does not begin a frame.
  So `Derived from int \n +int(1) \n .` reads `int + int(1)` (the test
  `ambig/addition3.eflint` says so).
- **`Identified by A, B` on a `Fact`** is read as the initial domain, not an
  extension clause; eFLINT notes the two readings are equivalent.
- **Variable decoration** is an integer literal and primes following an
  identifier, with or without a space (`person1`, `actor 2`), as in eFLINT's
  token stream.

Every function takes fuel and no definition is `partial`.
-/

namespace Charter

namespace Parser

structure St where
  toks : Array Tok
  i    : Nat := 0

abbrev P (α : Type) := St → Except Diagnostic (α × St)

instance : Monad P where
  pure a := fun s => .ok (a, s)
  bind m f := fun s => match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

def curPos (s : St) : Pos :=
  if h : s.i < s.toks.size then s.toks[s.i].pos else (s.toks.back?.map (·.pos)).getD {}

def fail {α} (code : String) (msg : String) : P α := fun s =>
  .error (.error code msg (curPos s))

def peekTok : P Tok := fun s =>
  if h : s.i < s.toks.size then .ok (s.toks[s.i], s) else .ok (⟨.eof, {}⟩, s)

def peek : P TokKind := do return (← peekTok).kind

def peekAt (k : Nat) : P TokKind := fun s =>
  if h : s.i + k < s.toks.size then .ok (s.toks[s.i + k].kind, s) else .ok (.eof, s)

def pos : P Pos := do return (← peekTok).pos

def advance : P Unit := fun s => .ok ((), { s with i := s.i + 1 })

def isKw (k : String) : P Bool := do return (← peek) == .kw k

/-- Match a contextual uppercase Charter keyword (lexed as `.atom k`, D17). -/
def isCtxAtom (k : String) : P Bool := do
  let t ← peek
  return t == .atom k || t == .kw k

def expectKw (k : String) : P Unit := do
  if ← isKw k then advance
  else fail "CHR003" s!"expected `{k}` but found {(← peek).describe}"

def expectCtxAtom (k : String) : P Unit := do
  if ← isCtxAtom k then advance
  else fail "CHR003" s!"expected `{k}` but found {(← peek).describe}"

def optKw (k : String) : P Bool := do
  if ← isKw k then advance; return true else return false

def unexpected {α} (what : String) : P α := do
  fail "CHR003" s!"expected {what} but found {(← peek).describe}"

def ident : P String := do
  match ← peek with
  | .ident s => advance; return s
  | _ => unexpected "a type identifier (lowercase)"

def atom : P String := do
  match ← peek with
  | .atom s => advance; return s
  | .str s => advance; return s
  | _ => unexpected "an atom or a string literal"

def intLit : P Int := do
  match ← peek with
  | .int n => advance; return n
  | _ => unexpected "an integer"

def primes (acc : String) : Nat → P String
  | 0 => return acc
  | k + 1 => do if ← isKw "'" then advance; primes (acc ++ "'") k else return acc

/-- A decorated variable: identifier, optional integer, primes. -/
def var : P Var := do
  let d ← ident
  let dec ← (do match ← peek with
    | .int n => advance; return toString n
    | _ => return "")
  let dec ← primes dec 64
  return ⟨d, dec⟩

/-- `p` separated by `sep`, at least one. -/
def sepBy1 {α} (p : P α) (sep : String) : Nat → P (List α)
  | 0 => return []
  | fuel + 1 => do
    let x ← p
    if ← isKw sep then advance; return x :: (← sepBy1 p sep fuel) else return [x]

def vars : P (List Var) := sepBy1 var "," 1000

/-- Look ahead: identifier, optional int, primes, then `=` (a named argument). -/
def isNamedStart : P Bool := fun s =>
  let rec scan (j : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if h : j < s.toks.size then
        match s.toks[j].kind with
        | .kw "'" => scan (j + 1) fuel
        | .kw "=" => true
        | _ => false
      else false
  let r := if h : s.i < s.toks.size then
    match s.toks[s.i].kind with
    | .ident _ =>
      if h2 : s.i + 1 < s.toks.size then
        match s.toks[s.i + 1].kind with
        | .int _ => scan (s.i + 2) 64
        | _ => scan (s.i + 1) 64
      else false
    | _ => false
  else false
  .ok (r, s)

/-! ## Expressions -/

mutual

/-- `When`/`Where` (lowest), left-associative. -/
def expr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← orExpr fuel
    whenTail fuel t

def whenTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    match ← peek with
    | .kw "When" | .kw "Where" => advance; let c ← orExpr fuel; whenTail fuel (.when t c)
    | _ => return t

def orExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← andExpr fuel
    orTail fuel t

def orTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    if ← isKw "||" then advance; let r ← andExpr fuel; orTail fuel (.or t r) else return t

def andExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← cmpExpr fuel
    andTail fuel t

def andTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    if ← isKw "&&" then advance; let r ← cmpExpr fuel; andTail fuel (.and t r) else return t

def cmpExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let a ← addExpr fuel
    match ← peek with
    | .kw "==" => advance; return .eq a (← addExpr fuel)
    | .kw "!=" => advance; return .neq a (← addExpr fuel)
    | .kw "<=" => advance; return .leq a (← addExpr fuel)
    | .kw ">=" => advance; return .geq a (← addExpr fuel)
    | .kw "<" => advance; return .le a (← addExpr fuel)
    | .kw ">" => advance; return .ge a (← addExpr fuel)
    | .atom "Before" =>
      advance
      let b ← addExpr fuel
      return .and (.doneAt a) (.or (.not (.doneAt b)) (.le (.stampOf a) (.stampOf b)))
    | .atom "Within" =>
      advance
      let dur ← addExpr fuel
      if !(← isCtxAtom "Of") then fail "CHR003" "expected `Of` in `<a> Within <dur> Of <b>`"
      advance
      let b ← addExpr fuel
      return .and (.doneAt a) (.and (.doneAt b) (.and (.geq (.stampOf a) (.stampOf b)) (.leq (.sub (.stampOf a) (.stampOf b)) dur)))
    | .atom "At" =>
      advance
      let b ← addExpr fuel
      return .app "$at_snap" (.pos [a, b])
    | _ => return a

def addExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← mulExpr fuel
    addTail fuel t

def addTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    match ← peek with
    | .kw "+" => advance; let r ← mulExpr fuel; addTail fuel (.add t r)
    | .kw "-" => advance; let r ← mulExpr fuel; addTail fuel (.sub t r)
    | _ => return t

def mulExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← unary fuel
    mulTail fuel t

def mulTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    match ← peek with
    | .kw "*" => advance; let r ← unary fuel; mulTail fuel (.mult t r)
    | .kw "/" => advance; let r ← unary fuel; mulTail fuel (.div t r)
    | .kw "%" => advance; let r ← unary fuel; mulTail fuel (.mod t r)
    | _ => return t

def unary : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    match ← peek with
    | .kw "!" => advance; return .not (← unary fuel)
    | .kw "Not" => advance; return .not (← unary fuel)
    | .kw "Present" => advance; return .present (← unary fuel)
    | .kw "Holds" => advance; return .present (← unary fuel)
    | .kw "Violated" => advance; return .violated (← unary fuel)
    | .kw "Enabled" => advance; return .enabled (← unary fuel)
    | .atom "Held" | .kw "Held" =>
      if (← peekAt 1) == .kw "(" then
        advance
        expectKw "("
        let t ← expr fuel
        expectKw ")"
        expectKw "For"
        let d ← addExpr fuel
        return .heldFor t d
      else postfixExpr fuel
    | .atom "Established" | .atom "Refuted" | .atom "Unresolved" | .atom "Conflicted" =>
      if (← peekAt 1) == .kw "(" then
        let want : EvidenceStatus := match ← peek with
          | .atom "Established" => .established
          | .atom "Refuted"     => .refuted
          | .atom "Unresolved"  => .unresolved
          | _                   => .conflicted
        advance
        expectKw "("
        let t ← expr fuel
        expectKw ")"
        return .evStatus want t
      else postfixExpr fuel
    | .atom "Conflict" =>
      if (← peekAt 1) == .kw "(" then
        advance
        expectKw "("
        let t ← expr fuel
        expectKw ")"
        return .hasConflict t
      else postfixExpr fuel
    | _ => postfixExpr fuel

def postfixExpr : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    let t ← primary fuel
    postfixTail fuel t

def postfixTail : Nat → Term → P Term
  | 0, t => return t
  | fuel + 1, t => do
    match ← peek with
    | .projDot =>
      advance
      if ← isKw "(" then advance; let x ← var; expectKw ")"; postfixTail fuel (.project t x)
      else let x ← var; postfixTail fuel (.project t x)
    | .kw ":" => advance; let d ← ident; postfixTail fuel (.tag t d)
    | _ => return t

/-- After `(` and a binder keyword: `xs : body )`. -/
def binderForm (isForall : Bool) : Nat → (List Var → Term → Term) → P Term
  | 0, _ => fail "CHR003" "expression too deeply nested"
  | fuel + 1, mk => do
    let xs ← vars
    let exc? ← (do
      -- `primary fuel` avoids eating `:` as eFLINT's postfix `e:t` tag operator before `: body`
      if ← isCtxAtom "Except" then advance; return some (← primary fuel)
      else return none)
    expectKw ":"
    let body ← expr fuel
    expectKw ")"
    let body' := match exc?, xs with
      | some ex, v :: _ =>
        let guard := Term.and (.present (.ref v)) (Term.neq (.ref v) ex)
        if isForall then Term.when body guard else Term.and guard body
      | _, _ => body
    return mk xs body'

/-- `Sum`/`Count`/`Max`/`Min` `(Foreach xs : body)`, `Count(pred)`, and 2-arg `Min(a, b)` / `Max(a, b)`. -/
def aggregate (kind : String) : Nat → (List Var → Term → Term) → P Term
  | 0, _ => fail "CHR003" "expression too deeply nested"
  | fuel + 1, mk => do
    expectKw "("
    if ← isKw "Foreach" then
      advance
      binderForm false fuel mk
    else if kind == "Count" then
      let p ← expr fuel
      expectKw ")"
      match p with
      | .ref v => return .count [v] (.when (.ref v) (.present (.ref v)))
      | _ => fail "CHR003" "expected `Foreach` or a fact name inside `Count(...)`"
    else if kind == "Min" || kind == "Max" then
      let a ← expr fuel
      expectKw ","
      let b ← expr fuel
      expectKw ")"
      let cmp := if kind == "Min" then Term.leq a b else Term.geq a b
      return .ite cmp a b
    else
      expectKw "Foreach"
      binderForm false fuel mk

def primary : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    match ← peek with
    | .kw "True" => advance; return .boolLit true
    | .kw "False" => advance; return .boolLit false
    | .kw "Current Time" => advance; return .currentTime
    | .int n =>
      advance
      match ← peek with
      | .ident "bps" => advance; return .dimLit .rate n
      | .ident "day" | .ident "days" => advance; return .dimLit .duration n
      | .ident "week" | .ident "weeks" => advance; return .dimLit .duration (n * 7)
      | _ => return .intLit n
    | .dateLit epochDays => advance; return .dimLit .time epochDays
    | .moneyLit cents => advance; return .dimLit (.money "USD" 2) cents
    | .pctLit bps => advance; return .dimLit .rate bps
    | .str s => advance; return .stringLit s
    | .atom "Done" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("; let t ← expr fuel; expectKw ")"; return .doneAt t
      else advance; return .stringLit "Done"
    | .atom "Since" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("; let t ← expr fuel; expectKw ")"; return .stampOf t
      else advance; return .stringLit "Since"
    | .atom "Age" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("; let t ← expr fuel; expectKw ")"
        return .ite (.doneAt t) (.sub .currentTime (.stampOf t)) (.dimLit .duration 0)
      else advance; return .stringLit "Age"
    | .atom "Overdue" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("; let t ← expr fuel; expectKw ")"; return .overdueOf t
      else advance; return .stringLit "Overdue"
    | .atom "Year" | .atom "Month" | .atom "Day" | .atom "Weekday" =>
      if (← peekAt 1) == .kw "(" then
        let op : CalOp := match ← peek with
          | .atom "Year" => .year | .atom "Month" => .month | .atom "Day" => .day | _ => .weekday
        advance; expectKw "("; let t ← expr fuel; expectKw ")"
        return .calOp1 op t
      else
        let s ← atom; return .stringLit s
    | .atom "AddMonths" | .atom "AddYears" =>
      if (← peekAt 1) == .kw "(" then
        let op : CalOp := if (← peek) == .atom "AddMonths" then .addMonths else .addYears
        advance; expectKw "("; let t ← expr fuel; expectKw ","; let m ← expr fuel; expectKw ")"
        return .calOp2 op t m
      else
        let s ← atom; return .stringLit s
    | .atom "If" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("
        let c ← expr fuel
        expectKw ","
        let t ← expr fuel
        expectKw ","
        let e ← expr fuel
        expectKw ")"
        return .ite c t e
      else advance; return .stringLit "If"
    | .atom "Share" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("
        let pool ← expr fuel
        if !(← isCtxAtom "Among") then fail "CHR003" "expected `Among <party>` in `Share(pool Among party Remainder To target)`"
        advance
        let pVar ← var
        if !(← isCtxAtom "Remainder") then
          fail "CHR003" "`Share(...)` requires `Remainder To <recipient>` so rounding cents are never lost (#56)"
        advance
        if !(← isCtxAtom "To") then fail "CHR003" "expected `To <recipient>` after `Remainder`"
        advance
        let remTarget ← expr fuel
        expectKw ")"
        let pIter : Var := { pVar with dec := pVar.dec ++ "_sh" }
        let nCnt := Term.count [pIter] (.ref pIter)
        let base := Term.mulDivRound pool (.intLit 1) nCnt .floor
        let rem := Term.sub pool (.mult base nCnt)
        return .ite (.eq (.ref pVar) remTarget) (.add base rem) base
      else advance; return .stringLit "Share"
    | .atom "ProRata" =>
      if (← peekAt 1) == .kw "(" then
        advance; expectKw "("
        let pool ← expr fuel
        if !(← isCtxAtom "By") then fail "CHR003" "expected `By <weight-fn>` in `ProRata(pool By fn Among party Remainder To target)`"
        advance
        let wFn ← ident
        if !(← isCtxAtom "Among") then fail "CHR003" "expected `Among <party>` in `ProRata(pool By fn Among party Remainder To target)`"
        advance
        let pVar ← var
        if !(← isCtxAtom "Remainder") then
          fail "CHR003" "`ProRata(...)` requires `Remainder To <recipient>` so rounding cents are never lost (#56)"
        advance
        if !(← isCtxAtom "To") then fail "CHR003" "expected `To <recipient>` after `Remainder`"
        advance
        let remTarget ← expr fuel
        expectKw ")"
        let pIter : Var := { pVar with dec := pVar.dec ++ "_pr" }
        let totW := Term.sum [pIter] (.fnApp wFn (.ref pIter))
        let myFloor := Term.mulDivRound pool (.fnApp wFn (.ref pVar)) totW .floor
        let sumFloors := Term.sum [pIter] (.mulDivRound pool (.fnApp wFn (.ref pIter)) totW .floor)
        let rem := Term.sub pool sumFloors
        return .ite (.eq (.ref pVar) remTarget) (.add myFloor rem) myFloor
      else advance; return .stringLit "ProRata"
    | .atom "MulDivRound" =>
      if (← peekAt 1) == .kw "(" then
        advance
        expectKw "("
        let x ← expr fuel
        expectKw ","
        let arg2 ← expr fuel
        expectKw ","
        -- 3-arg `MulDivRound(amt, rate, mode)` (`D37`, `#58`) or 4-arg `MulDivRound(x, num, den, mode)`
        let parseMode : P RoundingMode := do
          match ← peek with
          | .atom "Floor" | .ident "floor" => advance; return .floor
          | .atom "Ceil" | .ident "ceil" => advance; return .ceil
          | .atom "NearestEven" | .ident "nearestEven" => advance; return .nearestEven
          | .atom "ExactOrReject" | .ident "exactOrReject" => advance; return .exactOrReject
          | k => fail "CHR003" s!"expected rounding mode (`Floor`, `Ceil`, `NearestEven`, or `ExactOrReject`), found {k.describe}"
        let isModeNow := match ← peek with
          | .atom "Floor" | .ident "floor" | .atom "Ceil" | .ident "ceil"
          | .atom "NearestEven" | .ident "nearestEven" | .atom "ExactOrReject" | .ident "exactOrReject" =>
            true
          | _ => false
        if isModeNow && (← peekAt 1) == .kw ")" then
          let mode ← parseMode
          expectKw ")"
          -- Sentinel `.dimLit .rate 10000` tells `Static.lean` that `arg2` must be a `Rate`!
          return .mulDivRound x arg2 (.dimLit .rate 10000) mode
        else
          let den ← expr fuel
          expectKw ","
          let mode ← parseMode
          expectKw ")"
          return .mulDivRound x arg2 den mode
      else
        advance; return .stringLit "MulDivRound"
    | .atom s => advance; return .stringLit s
    | .kw "Sum" => advance; aggregate "Sum" fuel .sum
    | .kw "Count" => advance; aggregate "Count" fuel .count
    | .kw "Max" => advance; aggregate "Max" fuel .max
    | .kw "Min" => advance; aggregate "Min" fuel .min
    | .kw "(" =>
      advance
      match ← peek with
      | .kw "Exists" => advance; binderForm false fuel .exists_
      | .kw "Forall" => advance; binderForm true fuel .forall_
      | _ => let t ← expr fuel; expectKw ")"; return t
    | .ident _ =>
      let x ← var
      if (← isKw "(") && x.dec.isEmpty then
        advance
        let args ← arguments fuel
        expectKw ")"
        return .app x.dom args
      else return .ref x
    | k => fail "CHR003" s!"expected an expression but found {k.describe}"

/-- Arguments after `(`: empty, named `x = e, …`, or positional `e, …`. -/
def arguments : Nat → P Args
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    if ← isKw ")" then return .named []
    if ← isNamedStart then
      let ms ← sepBy1 (do let x ← var; expectKw "="; let t ← expr fuel; return (x, t)) "," 1000
      return .named ms
    else
      let ts ← sepBy1 (expr fuel) "," 1000
      return .pos ts

end

def exprFuel : Nat := 4096

def expression : P Term := expr exprFuel

def exprList : P (List Term) := sepBy1 expression "," 1000

/-- `(Foreach xs : e)` or `e`. -/
def optForeach : P (List Var × Term) := do
  if (← peek) == .kw "(" && (← peekAt 1) == .kw "Foreach" then
    advance; advance
    let xs ← vars
    expectKw ":"
    let t ← expression
    expectKw ")"
    return (xs, t)
  else
    return ([], ← expression)

/-! ## Type expressions -/

def intsFromRange (lo hi : Int) : List Int :=
  if lo > hi then [] else (List.range (hi - lo).toNat.succ).map (fun (k : Nat) => lo + (k : Int))

def stringsFromRange (lo hi : Char) : List String :=
  if lo.toNat > hi.toNat then [] else
    (List.range (hi.toNat - lo.toNat + 1)).map (fun k => (Char.ofNat (lo.toNat + k)).toString)

def currencyAtomDom : String → Option Domain
  | "USD" => some (.money "USD" 2)
  | "EUR" => some (.money "EUR" 2)
  | "GBP" => some (.money "GBP" 2)
  | "Rate" => some .rate
  | _ => none

def parseProductVarWithCarriers : P (Var × List Decl) := do
  match ← peek with
  | .atom s =>
    match currencyAtomDom s with
    | some dom =>
      advance
      let cname := "_cur_" ++ s
      return (⟨cname, ""⟩, [.ensureCarrier cname dom])
    | none =>
      let v ← var
      return (v, [])
  | _ =>
    let v ← var
    if ← isKw ":" then
      advance
      let dom ← (do match ← peek with
        | .kw "Int" => advance; return Domain.anyInt
        | .kw "Time" => advance; return Domain.time
        | .atom "Duration" | .kw "Duration" => advance; return Domain.duration
        | .atom "Rate" => advance; return Domain.rate
        | .atom s =>
          match currencyAtomDom s with
          | some cd => advance; return cd
          | none =>
            if s == "Money" then
              advance; expectKw "("
              let cur ← (do match ← peek with | .atom c | .ident c | .str c => advance; return c | k => fail "CHR003" s!"expected currency in Money(...), found {k.describe}")
              expectKw ","
              let sc ← intLit
              expectKw ")"
              return .money cur sc.toNat
            else if s == "Quantity" then
              advance; expectKw "("
              let u ← (do match ← peek with | .atom c | .ident c | .str c => advance; return c | k => fail "CHR003" s!"expected unit in Quantity(...), found {k.describe}")
              expectKw ")"
              return .quantity u
            else fail "CHR003" s!"unexpected domain `{s}` after `:`"
        | k => fail "CHR003" s!"unexpected domain {k.describe} after `:`")
      return (v, [.ensureCarrier v.dom dom])
    else
      return (v, [])

/-- `Identified by …` domain (eFLINT `type_expr`). -/
def typeExpr : P Domain := do
  match ← peek with
  | .kw "String" | .kw "Atom" => advance; return .anyString
  | .kw "Int" => advance; return .anyInt
  | .kw "Time" => advance; return .time
  | .atom "Duration" | .kw "Duration" =>
    let n ← peekAt 1
    if n == .kw "," || n == .kw "+" then
      let a ← atom
      let rest ← moreAtoms
      return .strings (a :: rest)
    else
      advance; return .duration
  | .atom "Money" =>
    if (← peekAt 1) == .kw "(" then
      advance; expectKw "("
      let cur ← (do match ← peek with | .atom s | .ident s | .str s => advance; return s | k => fail "CHR003" s!"expected currency code in `Money(CUR, SCALE)`, found {k.describe}")
      expectKw ","
      let sc ← intLit
      if sc < 0 then fail "CHR003" s!"Money({cur}, {sc}): scale must be non-negative"
      expectKw ")"
      return .money cur sc.toNat
    else
      let a ← atom
      let rest ← moreAtoms
      return .strings (a :: rest)
  | .atom "Quantity" =>
    if (← peekAt 1) == .kw "(" then
      advance; expectKw "("
      let unit ← (do match ← peek with | .atom s | .ident s | .str s => advance; return s | k => fail "CHR003" s!"expected unit name in `Quantity(UNIT)`, found {k.describe}")
      expectKw ")"
      return .quantity unit
    else
      let a ← atom
      let rest ← moreAtoms
      return .strings (a :: rest)
  | .int lo =>
    advance
    if ← isKw ".." then advance; let hi ← intLit; return .ints (intsFromRange lo hi)
    else
      let rest ← moreInts
      return .ints (lo :: rest)
  | .chr lo =>
    advance; expectKw ".."
    match ← peek with
    | .chr hi => advance; return .strings (stringsFromRange lo hi)
    | _ => unexpected "a character literal after `..`"
  | .atom _ | .str _ =>
    let a ← atom
    let rest ← moreAtoms
    return .strings (a :: rest)
  | .kw "(" =>
    advance
    let xs ← sepBy1 var "*" 1000
    expectKw ")"
    return .products xs
  | .ident _ =>
    let pairs ← sepBy1 parseProductVarWithCarriers "*" 1000
    return .products (pairs.map (·.1))
  | k => fail "CHR003" s!"expected a domain after `Identified by` but found {k.describe}"
where
  moreInts : P (List Int) := do
    match ← peek with
    | .kw "," | .kw "+" =>
      -- a list separator only if an integer follows (`+` may also begin a phrase after a `.`-less decl; eFLINT reads it as a list)
      match ← peekAt 1 with
      | .int _ => advance; let n ← intLit; return n :: (← moreInts')
      | _ => return []
    | _ => return []
  moreInts' : P (List Int) := do
    match ← peek with
    | .kw "," | .kw "+" =>
      match ← peekAt 1 with
      | .int _ => advance; let n ← intLit; return n :: (← moreInts'')
      | _ => return []
    | _ => return []
  moreInts'' : P (List Int) := sepTailInts 1000
  sepTailInts : Nat → P (List Int)
    | 0 => return []
    | k + 1 => do
      match ← peek with
      | .kw "," | .kw "+" =>
        match ← peekAt 1 with
        | .int _ => advance; let n ← intLit; return n :: (← sepTailInts k)
        | _ => return []
      | _ => return []
  moreAtoms : P (List String) := sepTailAtoms 1000
  sepTailAtoms : Nat → P (List String)
    | 0 => return []
    | k + 1 => do
      match ← peek with
      | .kw "," | .kw "+" =>
        match ← peekAt 1 with
        | .atom _ | .str _ => advance; let a ← atom; return a :: (← sepTailAtoms k)
        | _ => return []
      | _ => return []

/-- `Identified by`/`Domain` extension lists inside a frame's clauses. -/
def extendDomainClause : P ModClause := do
  match ← peek with
  | .int lo =>
    advance
    if ← isKw ".." then advance; let hi ← intLit; return .ints (intsFromRange lo hi)
    else return .ints (lo :: (← typeExpr.sepTailInts 1000))
  | .chr lo =>
    advance; expectKw ".."
    match ← peek with
    | .chr hi => advance; return .strings (stringsFromRange lo hi)
    | _ => unexpected "a character literal after `..`"
  | .atom _ | .str _ =>
    let a ← atom
    return .strings (a :: (← typeExpr.sepTailAtoms 1000))
  | k => fail "CHR003" s!"expected atoms or integers after `Identified by` but found {k.describe}"

/-! ## Declarations -/

inductive FrameKind | fact | act | event | duty | immunity
  deriving DecidableEq

/-- `Derived from` / `Holds when` / `Present when` / `Holds When` / `Present When`. -/
def derivationClause : P (Option (List Derivation)) := do
  match ← peek with
  | .kw "Derived from" =>
    advance
    let ds ← sepBy1 (do let (xs, t) ← optForeach; return Derivation.dv xs t) "," 1000
    return some ds
  | .kw "Holds when" | .kw "Present when" =>
    advance
    let ts ← exprList
    return some (ts.map .holdsWhen)
  | .kw "Holds" | .kw "Present" =>
    if (← peekAt 1) == .kw "When" then
      advance; advance
      let ts ← exprList
      return some (ts.map .holdsWhen)
    else return none
  | _ => return none

def effectClause (mk : List Var → Term → Effect) : P (List Effect) := do
  let es ← sepBy1 optForeach "," 1000
  return es.map (fun (xs, t) => mk xs t)

/-- `Creates e [For d], …`: a creation may carry an expiry duration (D7). -/
def createsClause : P (List Effect) := do
  let one : P Effect := do
    let (xs, t) ← optForeach
    if ← isKw "For" then advance; let d ← expression; return .cAll xs t (some d)
    else return .cAll xs t none
  sepBy1 one "," 1000

def idList : P (List DomId) := sepBy1 ident "," 1000

/-- A clause identifier: `DEF.01`, `COM.LEDGER`, `ART.3.2`: atoms and identifiers joined by dots. -/
def clauseId : P String := do
  let first ← (do match ← peek with
    | .atom s => advance; return s
    | .ident s => advance; return s
    | .int n => advance; return toString n
    | k => fail "CHR003" s!"expected a clause identifier but found {k.describe}")
  let rec more (acc : String) : Nat → P String
    | 0 => return acc
    | fuel + 1 => do
      match ← peek with
      | .projDot | .kw "." =>
        match ← peekAt 1 with
        | .atom s => advance; advance; more (acc ++ "." ++ s) fuel
        | .ident s => advance; advance; more (acc ++ "." ++ s) fuel
        | .int n => advance; advance; more (acc ++ "." ++ toString n) fuel
        | _ => return acc
      | .kw "/" =>
        match ← peekAt 1 with
        | .int n => advance; advance; return acc ++ "/" ++ toString n
        | _ => return acc
      | _ => return acc
  more first 32

def registerOf : TokKind → Option Register
  | .atom "Norm" | .kw "Norm" => some .norm
  | .atom "Definition" | .kw "Definition" => some .definition
  | .kw "Invariant" => some .invariant
  | .atom "Acceptance" | .kw "Acceptance" => some .acceptance
  | .atom "Commentary" | .kw "Commentary" => some .commentary
  | _ => none

/-- Whether tokens starting at `idx` begin a declaration frame (D17 contextual check). -/
def isFrameHeadAt (idx : Nat) : P Bool := do
  match ← peekAt idx with
  | .kw s =>
    return ["Fact", "Var", "Function", "Bool", "Predicate", "Invariant", "Act", "Physical",
            "Event", "Duty", "Extend", "Placeholder"].contains s
  | .atom s =>
    if ["Immunity", "Protection", "Prohibited", "Role", "Amount", "Debt", "Module", "Use", "Param", "Property", "Power", "Finding", "Amend"].contains s then
      return (match ← peekAt (idx + 1) with
        | .ident _ => true
        | .atom "Procedure" => s == "Amend"
        | _ => false)
    else if s == "Entrenched" then
      return (match ← peekAt (idx + 1) with | .kw "Invariant" | .kw "Predicate" => true | _ => false)
    else if s == "Regime" then
      let t1 ← peekAt (idx + 1)
      let t2 ← peekAt (idx + 2)
      return (match t1, t2 with
        | .ident _, .kw "{" | .atom _, .kw "{" | .str _, .kw "{" => true
        | _, _ => false)
    else if s == "Evidenced" || s == "Input" then
      let t1 ← peekAt (idx + 1)
      let t2 ← peekAt (idx + 2)
      return (match t1, t2 with
        | .kw "Fact", _ | .kw "Var", _ | .kw "Function", _ | .kw "Bool", _ => true
        | .kw "Open", .kw "Fact" | .kw "Open", .kw "Var" | .kw "Open", .kw "Function" | .kw "Open", .kw "Bool" => true
        | _, _ => false)
    else if s == "Document" then
      let t1 ← peekAt (idx + 1)
      let t2 ← peekAt (idx + 2)
      return (match t1, t2 with
        | .str _, _ => true
        | .atom _, .str _ | .ident _, .str _ => true
        | _, _ => false)
    else if s == "Clause" then
      return (match ← peekAt (idx + 1) with | .atom _ | .ident _ | .int _ => true | _ => false)
    else return false
  | _ => return false

/-- Parse a defeasible rule identifier (`r-base`, `r1`, or `R1`). -/
def ruleId : P String := do
  match ← peek with
  | .atom s => advance; return s
  | _ => toString <$> var

/-- Parse one target after `=>` in a `Clause` (`D34`, `#36`): a type/rule id, a qualified
defeasible rule `ty.r`, or a ground-fact constructor `f(args)` that also initializes state. -/
def spanTarget : P (String × Option Term) := do
  let base ← ruleId
  match ← peek with
  | .projDot =>
    advance
    let sub ← ruleId
    return (s!"{base}.{sub}", none)
  | .kw "(" =>
    advance
    let args ← arguments exprFuel
    expectKw ")"
    return (base, some (.app base args))
  | _ =>
    return (base, none)

def clauseItems (cid : ClauseId) : Nat → P (Option String × List Span × List Term)
  | 0 => return (none, [], [])
  | fuel + 1 => do
    match ← peek with
    | .atom "Text" | .kw "Text" =>
      if (match ← peekAt 1 with | .str _ => true | _ => false) then
        advance
        match ← peek with
        | .str t => advance; let (_, spans, inits) ← clauseItems cid fuel; return (some t, spans, inits)
        | k => fail "CHR003" s!"expected the clause text in double quotes after `Text` but found {k.describe}"
      else return (none, [], [])
    | k =>
      match registerOf k with
      | some reg =>
        -- `Invariant "…"` is a span; `Invariant id When …` starts a new frame
        match ← peekAt 1 with
        | .str text =>
          advance; advance
          let targets ← (do if ← isKw "=>" then advance; sepBy1 spanTarget "," 1000 else return [])
          let ids := targets.map (·.1)
          let hereInits := targets.filterMap (·.2)
          let (txt, spans, moreInits) ← clauseItems cid fuel
          return (txt, ⟨cid, text, reg, ids⟩ :: spans, hereInits ++ moreInits)
        | _ => return (none, [], [])
      | none => return (none, [], [])

/-- Parse `(Holds when | Rejects when) <expr>` or `Yields <val> When <cond>` for a `Default` / `Exception` rule (`D23`). -/
def defeasibleBody : P (Term × DefeasibleConseq) := do
  match ← peek with
  | .kw "Holds when" | .kw "Present when" =>
    advance
    let c ← expression
    return (c, .holdsBool true)
  | .kw "Holds" | .kw "Present" =>
    advance; expectKw "When"
    let c ← expression
    return (c, .holdsBool true)
  | .kw "Rejects when" =>
    advance
    let c ← expression
    return (c, .holdsBool false)
  | .atom "Rejects" =>
    advance; expectKw "When"
    let c ← expression
    return (c, .holdsBool false)
  | .atom "Yields" =>
    advance
    let valTerm ← orExpr 1000
    match ← peek with
    | .kw "When" | .kw "Where" => advance
    | k => fail "CHR003" s!"expected `When` after `Yields <expr>` but found {k.describe}"
    let condTerm ← expression
    return (condTerm, .yieldsVal valTerm)
  | k =>
    fail "CHR003" s!"expected `Holds when`, `Rejects when`, or `Yields <expr> When` in defeasible rule, found {k.describe}"

/-- One clause of a frame of the given kind, or `none` when the next token is not one. -/
def clause (k : FrameKind) : P (Option ModClause) := do
  match ← peek with
  | .kw "Conditioned by" =>
    advance
    -- eFLINT allows an empty list here (`multipleSepBy`), so accept a bare keyword
    match ← peek with
    | .kw "." | .kw "}" | .eof => return some (.conditionedBy [])
    | _ => return some (.conditionedBy (← exprList))
  | .kw "Closed" | .kw "Open" =>
    -- `Open Fact x` after a declaration starts the next frame; a bare `Open`/`Closed` is a clause
    if ← isFrameHeadAt 1 then return none
    else
      let isClosed := (← peek) == .kw "Closed"
      advance
      return some (if isClosed then .close else .open)
  | .kw "Identified by" | .kw "Domain" =>
    if k == .fact then advance; return some (← extendDomainClause) else return none
  | .kw "Creates" =>
    if k == .fact || k == .immunity then return none
    advance; return some (.postCond (← createsClause))
  | .atom "Applies" =>
    if k != .act then return none
    advance
    let amt ← expression
    if !(← isCtxAtom "To") then fail "CHR003" "expected `To <var1, var2, ...>` after `Applies <amount>`"
    advance
    let targets ← sepBy1 var "," 100
    let rec buildWaterfall (rem : Term) : List Var → List Effect
      | [] => []
      | v :: vs =>
        let vTm := Term.ref v
        let take := Term.ite (.leq rem vTm) rem vTm
        let eff := Effect.cAll [] (.app v.dom (.pos [.sub vTm take])) none
        eff :: buildWaterfall (.sub rem take) vs
    return some (.postCond (buildWaterfall amt targets))
  | .kw "Terminates" =>
    if k == .fact || k == .immunity then return none
    advance; return some (.postCond (← effectClause .tAll))
  | .kw "Obfuscates" =>
    if k == .fact || k == .immunity then return none
    advance; return some (.postCond (← effectClause .oAll))
  | .kw "Syncs with" =>
    if k == .fact || k == .duty || k == .immunity then return none
    advance
    let ss ← sepBy1 optForeach "," 1000
    return some (.sync (ss.map fun (xs, t) => ⟨xs, t⟩))
  | .kw "Qualifies as" | .atom "QualifiesAs" =>
    if k == .fact || k == .duty || k == .immunity then return none
    advance
    let ss ← sepBy1 optForeach "," 1000
    return some (.sync (ss.map fun (xs, t) => ⟨xs, t⟩))
  | .atom "Qualifies" =>
    if k == .fact || k == .duty || k == .immunity then return none
    if (← peekAt 1) != .atom "As" then return none
    advance; advance
    let ss ← sepBy1 optForeach "," 1000
    return some (.sync (ss.map fun (xs, t) => ⟨xs, t⟩))
  | .kw "Violated when" =>
    if k != .duty then return none
    advance; return some (.violation (← exprList))
  | .kw "Excused when" =>
    if k != .duty then return none
    advance
    return some (.excusedWhen (← exprList))
  | .atom "Excused" =>
    if k != .duty then return none
    if (← peekAt 1) != .kw "When" then return none
    advance; advance
    return some (.excusedWhen (← exprList))
  | .atom "Overrides" =>
    if k != .duty then return none
    advance
    let parseOvTarget : P (DomId × Option Args) := do
      let d ← ident
      if ← isKw "(" then
        advance
        let args ← arguments exprFuel
        expectKw ")"
        return (d, some args)
      else return (d, none)
    return some (.overridesDuties (← sepBy1 parseOvTarget "," 1000))
  | .kw "Enforced by" =>
    if k != .duty then return none
    advance; return some (.enforcingActs (← idList))
  | .kw "Terminated by" =>
    if k != .duty then return none
    advance; return some (.terminatedBy (← idList))
  | .kw "Created by" =>
    if k != .duty then return none
    advance; return some (.createdBy (← idList))
  | .kw "Overridden by" =>
    if k != .duty then return none
    advance; return some (.overriddenBy (← idList))
  | .kw "Due within" =>
    if k != .duty then return none
    advance
    let dur ← expression
    if ← isCtxAtom "Grace" then
      advance
      let gr ← expression
      return some (.dueWithinGrace dur gr)
    else if ← isCtxAtom "After" then
      advance
      let ev ← expression
      return some (.dueWithinAfter dur ev)
    else
      return some (.dueWithin dur)
  | .atom "From" | .kw "From" =>
    -- `From CLAUSE ["span"]` on an act, duty, immunity, event, or fact (`D34`)
    if !(match ← peekAt 1 with | .atom _ | .ident _ | .int _ => true | _ => false) then return none
    advance
    let cid ← clauseId
    match ← peek with
    | .str text => advance; return some (.fromSpan cid text)
    | _ => return some (.fromSpan cid "")
  | .kw "Valid when" =>
    if k != .act then return none
    advance
    let e ← expression
    if ← isKw "," then
      fail "CHR003" "do not separate `Valid when` conditions with `,` (after `Holds when`, `,` means `||`); write `&&` for both or `||` for either (005.9)"
    return some (.validWhen [e])
  | .kw "Forbidden when" =>
    if k != .act then return none
    advance
    let e ← expression
    return some (.derivation [.holdsWhen (.not e)])
  | .atom "Forbidden" =>
    if k != .act then return none
    if (← peekAt 1) != .kw "When" then return none
    advance; advance
    let e ← expression
    return some (.derivation [.holdsWhen (.not e)])
  | .kw "Void when" =>
    if k != .act then return none
    advance
    let e ← expression
    return some (.validWhen [.not e])
  | .atom "Void" =>
    if k != .act then return none
    if (← peekAt 1) != .kw "When" then return none
    advance; advance
    let e ← expression
    return some (.validWhen [.not e])
  | .kw "Except under" =>
    if k != .act then return none
    advance; return some (.exceptUnder (← idList))
  | .atom "Presumed" =>
    if k != .fact then return none
    advance
    match ← peek with
    | .kw "True" => advance; return some (.presumed true)
    | .kw "False" => advance; return some (.presumed false)
    | kk => fail "CHR003" s!"expected `True` or `False` after `Presumed` but found {kk.describe}"
  | .atom "Confidential" =>
    if k != .fact then return none
    advance
    if ← isCtxAtom "To" then
      advance
      let auds ← sepBy1 (do match ← peek with
        | .ident s | .atom s | .str s => advance; return s
        | kk => fail "CHR003" s!"expected audience identifier after `Confidential To` but found {kk.describe}") "," 100
      return some (.confidential auds)
    else return some (.confidential [])
  | .atom "Default" =>
    if k != .fact then return none
    if !(match ← peekAt 1 with | .ident _ | .atom _ => true | _ => false) then return none
    advance
    let rid ← ruleId
    let (cond, conseq) ← defeasibleBody
    return some (.defeasibleRule { id := rid, isDefault := true, overrides := [], cond, conseq })
  | .atom "Exception" =>
    if k != .fact then return none
    if !(match ← peekAt 1 with | .ident _ | .atom _ => true | _ => false) then return none
    advance
    let rid ← ruleId
    if !(← isCtxAtom "Overrides") then
      fail "CHR003" s!"expected `Overrides <rule-id>` after `Exception {rid}`"
    advance
    let ovs ← sepBy1 ruleId "," 1000
    let (cond, conseq) ← defeasibleBody
    return some (.defeasibleRule { id := rid, isDefault := false, overrides := ovs, cond, conseq })
  | .atom "Priority" =>
    if k != .fact then return none
    if !(match ← peekAt 1 with | .ident _ | .atom _ => true | _ => false) then return none
    advance
    let hi ← ruleId
    if !(← isCtxAtom "Over") then
      fail "CHR003" s!"expected `Over <rule-id>` after `Priority {hi}`"
    advance
    let los ← sepBy1 ruleId "," 1000
    return some (.priorityEdge hi los)
  | .atom "Resolves" =>
    if k != .act then return none
    advance
    let neg ← optKw "!"
    let target ← expression
    return some (.resolves (!neg) target)
  | .atom "Decides" =>
    if k != .act then return none
    advance
    let target ← expression
    let cond ← (do
      if ← isCtxAtom "By" then
        advance
        let v ← var
        return (.eq (.ref v) (.stringLit "Yes"))
      else if (← isKw "When") || (← peek) == .ident "when" then
        advance
        expression
      else
        fail "CHR003" "expected `By <component>` or `When <cond>` after `Decides <fact>`")
    return some (.decides target cond)
  | .kw "Decided by" =>
    if k != .act then return none
    advance
    let voter ← var
    let weightFn ← (do
      if ← isKw "Weighted by" then advance; return some (← ident)
      else return none)
    expectKw "At least"
    let num ← intLit
    expectKw "/"
    let den ← intLit
    if den == 0 then fail "CHR003" "denominator in `At least n/d` cannot be 0"
    if !(← isCtxAtom "In") then fail "CHR003" "expected `In <vote-fact>` after `At least n/d`"
    advance
    let voteFact ← ident
    return some (.decidedBy voter weightFn num den voteFact)
  | .atom "Repeals" =>
    if k != .act then return none
    advance
    let rs ← idList
    return some (.repeals rs)
  | .atom "Protects" =>
    if k != .immunity then return none
    advance
    if ← isCtxAtom "Clause" then
      advance
      let cids ← sepBy1 clauseId "," 1000
      return some (.protectsClauses cids)
    else
      let ps ← idList
      return some (.protects ps)
  | .atom "Standard" =>
    if k != .act then return none
    advance
    match ← peek with
    | .ident s | .atom s | .str s => advance; return some (.standard s)
    | kk => fail "CHR003" s!"expected standard name after `Standard` but found {kk.describe}"
  | .atom "Supports" | .atom "Rebuts" | .atom "Retracts" =>
    if k != .act then return none
    let op : EvidenceOp := match ← peek with
      | .atom "Supports" => .support
      | .atom "Rebuts"   => .rebut
      | _                => .retract
    advance
    -- `Retracts !e` withdraws contrary evidence, as `SubmitEvidence !e` tenders it (005.11)
    let contrary ← if op == .retract then optKw "!" else pure false
    let op : EvidenceOp := if op == .retract then (if contrary then .retractRebut else .retractSupport) else op
    let ts ← sepBy1 optForeach "," 1000
    -- `By s`: in whose name the evidence is tendered or withdrawn; the actor's when absent
    let src? ← (do if ← isCtxAtom "By" then advance; return some (← expression) else return none)
    return some (.evEffect op ts src?)
  | .atom "Against" | .kw "Against" =>
    if k != .immunity then return none
    advance
    let parseAgainstTarget : P DomId := do
      if ← isCtxAtom "Amend" then advance; return "Amend"
      else ident
    return some (.against (← sepBy1 parseAgainstTarget "," 1000))
  | .kw "For" =>
    if k != .immunity then return none
    advance
    return some (.against (← idList))
  | .atom "Unless" | .kw "Unless" =>
    if k != .immunity && k != .act then return none
    advance; return some (.unlessCond (← exprList))
  | _ =>
    match ← derivationClause with
    | some ds => return some (.derivation ds)
    | none => return none

/-- Zero or more `From CLAUSE ["span"]` clauses on an `Invariant`, `Predicate`, `Use`, or `Scenario`. -/
def fromClauses : Nat → P (List (ClauseId × String))
  | 0 => return []
  | fuel + 1 => do
    if ← isCtxAtom "From" then
      advance
      let cid ← clauseId
      let txt ← (do match ← peek with | .str text => advance; return text | _ => return "")
      return (cid, txt) :: (← fromClauses fuel)
    else return []

def clauses (k : FrameKind) : Nat → P (List ModClause)
  | 0 => return []
  | fuel + 1 => do
    match ← clause k with
    | some c => return c :: (← clauses k fuel)
    | none => return []

def openness : P (Bool × Bool × Bool) := do
  match ← peek with
  | .kw "Closed" => advance; return (true, false, false)
  | .kw "Open" =>
    advance
    if ← isCtxAtom "Evidenced" then advance; return (false, true, false)
    else return (false, false, false)
  | .atom "Evidenced" =>
    advance
    let _ ← optKw "Open"
    return (false, true, false)
  | .atom "Input" =>
    advance
    let _ ← optKw "Open"
    return (true, false, true)
  | _ => return (true, false, false)

def domainConstraint : P Term := do
  match ← peek with
  | .kw "When" | .kw "Where" => advance; expression
  | _ => return .boolLit true

def relatedToWithCarriers : P (List Var × List Decl) := do
  if ← isKw "Related to" then
    advance
    let pairs ← sepBy1 parseProductVarWithCarriers "," 1000
    return (pairs.map (·.1), pairs.flatMap (·.2))
  else return ([], [])

def relatedTo : P (List Var) := do
  let (vs, _) ← relatedToWithCarriers
  return vs

def mkFact (inv isActor isClosed : Bool) (restr : Option Restriction) (d : DomId) (dom : Domain)
    (filter : Term) (cls : List ModClause) (isEv : Bool := false) (isEnt : Bool := false)
    (isInp : Bool := false) : List Decl :=
  [ .typeDecl d { kind := .fact { invariant := inv, actor := isActor, evidenced := isEv, entrenched := isEnt, isInput := isInp },
                  domain := dom, domainConstraint := filter, restriction := restr, derivation := [],
                  closed := if isClosed && !isEv then none else some false, conditions := [] },
    .typeExt d cls ]

/-- `: Int | Time | Duration | Rate | USD | Money(...) | Quantity(...)` after a `Param` or `Var`. -/
def paramDomain : P Domain := do
  if ← isKw ":" then
    advance
    match ← peek with
    | .kw "Int" => advance; return Domain.anyInt
    | .kw "Time" => advance; return Domain.time
    | .atom "Duration" | .kw "Duration" => advance; return Domain.duration
    | .atom "Rate" => advance; return Domain.rate
    | .atom "USD" => advance; return .money "USD" 2
    | .atom "EUR" => advance; return .money "EUR" 2
    | .atom "GBP" => advance; return .money "GBP" 2
    | .atom "Money" =>
      advance; expectKw "("
      let cur ← (do match ← peek with | .atom s | .ident s | .str s => advance; return s | k => fail "CHR003" s!"expected currency code in `Money(CUR, SCALE)`, found {k.describe}")
      expectKw ","
      let sc ← intLit
      if sc < 0 then fail "CHR003" s!"Money({cur}, {sc}): scale must be non-negative"
      expectKw ")"
      return .money cur sc.toNat
    | .atom "Quantity" =>
      advance; expectKw "("
      let unit ← (do match ← peek with | .atom s | .ident s | .str s => advance; return s | k => fail "CHR003" s!"expected unit name in `Quantity(UNIT)`, found {k.describe}")
      expectKw ")"
      return .quantity unit
    | k => fail "CHR003" s!"expected Int, Time, Duration, Rate, USD, Money(CUR, SCALE), or Quantity(UNIT) after `:` but found {k.describe}"
  else return Domain.anyInt

/-- Parse a `TemporalFormula` after `Property <name> [Assumes ...] When` (`D20`). -/
def temporalFormula : P TemporalFormula := do
  if ← isCtxAtom "Always" then
    advance
    if ← isKw "(" then
      let saved : St ← fun s => .ok (s, s)
      advance
      let lhs ← expression
      if ← isKw "=>" then
        advance
        if ← isCtxAtom "Next" then
          advance; let rhs ← expression; expectKw ")"; return .alwaysNext lhs rhs
        else if ← isCtxAtom "EventuallyWithin" then
          advance
          let bound ← addExpr exprFuel
          let rhs ← expression
          expectKw ")"
          return .alwaysEventuallyWithin bound lhs rhs
        else if ← isCtxAtom "Eventually" then
          advance; let rhs ← expression; expectKw ")"; return .alwaysEventually lhs rhs
        else
          fail "CHR003" "expected `Next`, `Eventually`, or `EventuallyWithin` after `=>` in `Always (... => ...)`"
      else
        let _ ← (fun _ => .ok ((), saved) : P Unit)
        return .always (← expression)
    else
      return .always (← expression)
  else if ← isCtxAtom "Until" then
    advance; expectKw "("; let phi ← expression; expectKw ","; let psi ← expression; expectKw ")"
    return .until_ phi psi
  else if ← isCtxAtom "WeakUntil" then
    advance; expectKw "("; let phi ← expression; expectKw ","; let psi ← expression; expectKw ")"
    return .weakUntil phi psi
  else
    fail "CHR003" s!"expected `Always`, `Until`, or `WeakUntil` in `Property` but found {(← peek).describe}"

def parseRegimeEntries : Nat → P (List (DomId × Int))
  | 0 => return []
  | rem + 1 => do
    if ← isKw "}" then advance; return []
    else
      let pname ← ident
      expectKw "="
      let neg ← optKw "-"
      let n ← intLit
      let val : Int := if neg then -n else n
      let _ ← (do if (← isKw ",") || (← isKw ".") then advance else pure ())
      return (pname, val) :: (← parseRegimeEntries rem)

mutual

def parseActExtras (bodyFuel : Nat) : Nat → P (List ModClause × List Decl)
  | 0 => return ([], [])
  | rem + 1 => do
    if (← isCtxAtom "Installs") && (← peekAt 1) == .kw "{" then
      advance; expectKw "{"
      let body ← moduleBody bodyFuel
      let (moreCls, moreInsts) ← parseActExtras bodyFuel rem
      return (moreCls, body ++ moreInsts)
    else
      match ← clause .act with
      | some c =>
        let (moreCls, moreInsts) ← parseActExtras bodyFuel rem
        return (c :: moreCls, moreInsts)
      | none => return ([], [])

/-- The declarations of a `Module` body, up to `}`, each block ended by `.` or by the
next declaration keyword. -/
def moduleBody : Nat → P (List Decl)
  | 0 => return []
  | fuel + 1 => do
    if ← isKw "}" then advance; return []
    if ← isKw "." then advance; return (← moduleBody fuel)
    let ds ← frame fuel
    return ds ++ (← moduleBody fuel)

/-- One frame: a type declaration, an `Extend`, a `Placeholder`, a `Clause`, … -/
def frame : Nat → P (List Decl)
  | 0 => fail "CHR003" "declarations nest too deeply"
  | fuel + 1 => do
  let (isClosed, isEv, isInp) ← openness
  match ← peek with
  | .kw "Fact" | .kw "Var" | .kw "Function" =>
    let restr : Option Restriction ← (do match ← peek with
      | .kw "Var" => advance; return some .var
      | .kw "Function" => advance; return some .function
      | _ => advance; return none)
    let d ← ident
    -- `Var paid : USD = $0` (`D37`, `#42`) alongside `Identified by ...`
    let hasColon := (← isKw ":")
    let (dom, extraCarriers) ← (do
      if hasColon then
        let dm ← paramDomain
        return (dm, [])
      else if ← isKw "Identified by" then
        advance
        -- Check product containing `USD`/`EUR`/`GBP` (`Identified by spouse * USD`)
        match ← peek with
        | .ident _ =>
          let pairs ← sepBy1 parseProductVarWithCarriers "*" 1000
          return (.products (pairs.map (·.1)), pairs.flatMap (·.2))
        | .atom s =>
          match currencyAtomDom s with
          | some cd => advance; return (cd, [])
          | none => return (← typeExpr, [])
        | _ => return (← typeExpr, [])
      else return (.anyString, []))
    let filter ← domainConstraint
    let initDecls ← (do
      if restr == some .var && (← isKw "=") then
        advance
        let initE ← expression
        return [Decl.varInit d initE]
      else return [])
    let cls ← clauses .fact 1000
    return extraCarriers ++ mkFact false false isClosed restr d dom filter cls isEv false isInp ++ initDecls
  | .kw "Bool" =>
    advance
    let d ← ident
    let cls ← clauses .fact 1000
    return mkFact false false isClosed none d (.products []) (.boolLit true) cls isEv false isInp
  | .kw "Predicate" | .kw "Invariant" | .atom "Entrenched" =>
    let isEnt ← if ← isCtxAtom "Entrenched" then advance; pure true else pure false
    let inv := (← peek) == .kw "Invariant"
    if !inv && (← peek) != .kw "Predicate" then
      unexpected "`Invariant` after `Entrenched`"
    advance
    let d ← ident
    match ← peek with
    | .kw "When" | .kw "Where" => advance
    | _ => unexpected "`When` after the predicate name"
    let t ← expression
    let fs ← fromClauses 100
    return mkFact inv false true none d (.products []) (.boolLit true)
      (.derivation [.holdsWhen t] :: fs.map (fun (c, s) => .fromSpan c s)) false isEnt false
  | .kw "Act" | .atom "Power" | .kw "Power" | .atom "Finding" | .kw "Finding" | .atom "Amend" | .kw "Amend" =>
    let cur ← peek
    let isFind := cur == .atom "Finding" || cur == .kw "Finding"
    let isAm := cur == .atom "Amend" || cur == .kw "Amend"
    let isPow := isFind || isAm || cur != .kw "Act"
    if isAm && (← peekAt 1) == .atom "Procedure" then
      advance; advance
      let _ ← optKw "With"
      let _ ← (do if ← isKw "Actor" then advance; let _ ← var; pure () else pure ())
      let _ ← (do if ← isKw "Recipient" then advance; let _ ← var; pure () else pure ())
      let _ ← relatedTo
      expectKw "Valid when"
      let e ← expression
      return [.amendProcedure [e]]
    advance
    let ds ← sepBy1 ident "," 100
    let _ ← optKw "With"
    let actor ← (do if ← isKw "Actor" then advance; return some (← var) else return none)
    let recip ← (do if ← isKw "Recipient" then advance; return some (← var) else return none)
    let (objs, relCarriers) ← relatedToWithCarriers
    let filter ← domainConstraint
    let (cls, instBody) ← parseActExtras fuel 1000
    let actorV := actor.getD ⟨"actor", ""⟩
    let mkOne (d : DomId) : List Decl :=
      let instDecls := if instBody.isEmpty then [] else [Decl.amendInstall d instBody]
      [ .typeDecl d { kind := .act { hasRecipient := recip.isSome, isPower := isPow, isFinding := isFind, isAmend := isAm },
                      domain := .products (actorV :: (recip.toList ++ objs)),
                      domainConstraint := filter, closed := if isClosed then none else some false },
        .typeExt d cls ] ++ instDecls
    return relCarriers ++ ds.flatMap mkOne
  | .atom "Role" =>
    advance
    let d ← ident
    let base? ← (do if ← isKw "For" then advance; return some (← ident) else return none)
    if ← isCtxAtom "Is" then
      advance
      let who ← atom
      let cls ← clauses .fact 1000
      match base? with
      | none =>
        return [ .typeDecl d { kind := .fact { isRole := true }, domain := .strings [who],
                               derivation := [.holdsWhen (.boolLit true)], closed := none },
                 .typeExt d cls ]
      | some base =>
        let pVar : Var := ⟨base, ""⟩
        let eqCond := Term.eq (.ref pVar) (.stringLit who)
        return [ .typeDecl d { kind := .fact { isRole := true, roleBase := some base },
                               domain := .products [pVar], domainConstraint := eqCond,
                               derivation := [.holdsWhen eqCond], closed := none },
                 .typeExt d cls ]
    else if ← isKw "First of" then
      advance
      let base ← match base? with
        | some b => pure b
        | none => fail "CHR003" s!"`Role {d} First of ...` requires `For <base-type>` before `First of`"
      let pVar : Var := ⟨base, ""⟩
      let pVarAlt : Var := ⟨base, "'"⟩
      let cands ← sepBy1 atom "," 100
      if !(← isCtxAtom "Unless") && !(← isKw "Unless") then
        fail "CHR003" s!"expected `Unless <condition>` after `First of` in `Role {d}`"
      advance
      let unavail ← expression
      let cls ← clauses .fact 1000
      -- Build Default/Exception ordered succession rules over `cands`
      let rec mkChain (idx : Nat) (priorAtoms : List String) : List String → List ModClause
        | [] => []
        | cAtom :: rest =>
          let isMe := Term.eq (.ref pVar) (.stringLit cAtom)
          let priorsUnavail := priorAtoms.foldr (fun pa acc =>
            let sub := unavail.substVars [(pVar, pVarAlt)]
            let ex := Term.exists_ [pVarAlt] (.and (.eq (.ref pVarAlt) (.stringLit pa)) sub)
            Term.and ex acc) (.boolLit true)
          let defId := s!"cand-{idx}"
          let excId := s!"unavail-{idx}"
          let defRule : DefeasibleRule :=
            { id := defId, isDefault := true, overrides := [], cond := .and isMe priorsUnavail, conseq := .holdsBool true }
          let excRule : DefeasibleRule :=
            { id := excId, isDefault := false, overrides := [defId], cond := .and isMe unavail, conseq := .holdsBool false }
          .defeasibleRule defRule :: .defeasibleRule excRule :: mkChain (idx + 1) (priorAtoms ++ [cAtom]) rest
      return [ .typeDecl d { kind := .fact { isRole := true, roleBase := some base },
                             domain := .products [pVar], closed := none },
               .typeExt d (mkChain 0 [] cands ++ cls) ]
    else if (← isKw "Where") || (← isKw "When") then
      advance
      let base ← match base? with
        | some b => pure b
        | none => fail "CHR003" s!"`Role {d} Where ...` requires `For <base-type>`"
      let cond ← expression
      let cls ← clauses .fact 1000
      return [ .typeDecl d { kind := .fact { isRole := true, roleBase := some base },
                             domain := .products [⟨base, ""⟩], domainConstraint := cond,
                             derivation := [.holdsWhen cond], closed := none },
               .typeExt d cls ]
    else
      fail "CHR003" s!"expected `Is <Name>`, `Where <cond>`, or `First of ... Unless <cond>` in `Role {d}`"
  | .atom "Amount" =>
    advance
    let d ← ident
    let dom? ← (do
      if ← isKw ":" then
        let dm ← paramDomain
        return some dm
      else return none)
    if ← isCtxAtom "Is" then advance
    else expectKw "="
    let e ← expression
    return [.amountDef d dom? e]
  | .atom "Prohibited" =>
    advance
    let d ← ident
    let _ ← optKw "With"
    let actor ← (do if ← isKw "Actor" then advance; return some (← var) else return none)
    let recip ← (do if ← isKw "Recipient" then advance; return some (← var) else return none)
    let objs ← relatedTo
    let whenCond? ← (do
      match ← peek with
      | .kw "When" | .ident "when" => advance; return some (← expression)
      | _ => return none)
    let (cls, _) ← parseActExtras fuel 1000
    let unlessTerms := cls.flatMap fun | .unlessCond ts => ts | _ => []
    let cleanCls := cls.filter fun | .unlessCond _ => false | _ => true
    let excOr := unlessTerms.foldr Term.or (.boolLit false)
    let lawfulTerm : Term := match whenCond?, unlessTerms.isEmpty with
      | none, true => .boolLit false
      | none, false => excOr
      | some wc, true => .not wc
      | some wc, false => .or (.not wc) excOr
    let actorV := actor.getD ⟨"actor", ""⟩
    return [ .typeDecl d { kind := .act { hasRecipient := recip.isSome },
                           domain := .products (actorV :: (recip.toList ++ objs)),
                           closed := if isClosed then none else some false },
             .typeExt d (.derivation [.holdsWhen lawfulTerm] :: cleanCls) ]
  | .kw "Physical" =>
    advance
    let d ← ident
    let _ ← optKw "With"
    let actor ← (do if ← isKw "Actor" then advance; return some (← var) else return none)
    let objs ← relatedTo
    let filter ← domainConstraint
    let cls ← clauses .act 1000
    let actorV := actor.getD ⟨"actor", ""⟩
    return [ .typeDecl d { kind := .act { physical := true }, domain := .products (actorV :: objs),
                           domainConstraint := filter, closed := none },
             .typeExt d (.derivation [.holdsWhen (.boolLit true)] :: cls) ]
  | .kw "Event" =>
    advance
    let d ← ident
    let _ ← optKw "With"
    let objs ← relatedTo
    let filter ← domainConstraint
    let cls ← clauses .event 1000
    return [ .typeDecl d { kind := .event {}, domain := .products objs, domainConstraint := filter,
                           closed := if isClosed then none else some false },
             .typeExt d cls ]
  | .kw "Duty" =>
    advance
    let d ← ident
    let _ ← optKw "With"
    expectKw "Holder"
    let holder ← var
    let (claimant, extraDecls) ← (do
      if ← isKw "Claimant" then
        advance
        match ← peek with
        | .atom fixedParty =>
          advance
          let rDom := "_party_" ++ fixedParty
          let rDecl := Decl.typeDecl rDom { kind := .fact { isRole := true }, domain := .strings [fixedParty],
                                            derivation := [.holdsWhen (.boolLit true)], closed := none }
          return (⟨rDom, ""⟩, [rDecl])
        | _ =>
          let c ← var
          return (c, [])
      else
        return (holder, []))
    let (objs, relCarriers) ← relatedToWithCarriers
    let filter ← domainConstraint
    -- Check optional `Every <period>` recurring duty (`D38`, `#47`)
    let everyPeriod? ← (do
      if ← isCtxAtom "Every" then
        advance
        let n ← intLit
        let mult ← (do match ← peek with
          | .ident "week" | .ident "weeks" => advance; return (7 : Int)
          | .ident "day" | .ident "days" => advance; return (1 : Int)
          | _ => return (1 : Int))
        return some (n * mult)
      else return none)
    let cls ← clauses .duty 1000
    let paidBy ← (do if ← isKw "Paid by" then advance; idList else return [])
    let breachTarget? ← (do
      if ← isKw "On breach" then
        advance; expectKw "Creates"
        return some (← ident)
      else return none)
    let clsAfter ← clauses .duty 1000
    let allCls := cls ++ clsAfter
    match everyPeriod? with
    | none =>
      let breachExts := match breachTarget? with
        | none => []
        | some bt =>
          let dVar : Var := ⟨d, ""⟩
          [Decl.typeExt bt [.derivation [.holdsWhen (.exists_ [dVar] (.violated (.ref dVar)))]] "Fact"]
      return extraDecls ++ relCarriers ++
             [ .typeDecl d { kind := .duty {}, domain := .products (holder :: claimant :: objs),
                             domainConstraint := filter, closed := if isClosed then none else some false },
               .typeExt d allCls ] ++ breachExts
    | some perLen =>
      let clkDom := "_clk_time"
      let clkV : Var := ⟨clkDom, ""⟩
      let intV : Var := ⟨"int", ""⟩
      let paidDom := d ++ "-paid"
      let elapsed := Term.sub (.ref clkV) (.dimLit .time 0)
      let perDur := Term.dimLit .duration perLen
      let periodExpr := Term.div elapsed perDur
      let aligned := Term.eq (.mod elapsed perDur) (.dimLit .duration 0)
      let notPaid := Term.not (.present (.app paidDom (.pos [.ref holder, .ref claimant, periodExpr])))
      let dvTerm := Term.when (.app d (.pos ([.ref holder, .ref claimant] ++ objs.map .ref ++ [periodExpr])))
                              (.and aligned notPaid)
      let dvClause := ModClause.derivation [.dv (holder :: claimant :: clkV :: objs) dvTerm]
      let payExts := paidBy.map fun pAct =>
        let markPaid := Effect.cAll [] (.app paidDom (.pos [.ref holder, .ref claimant, .ref intV])) none
        Decl.typeExt pAct [.postCond [markPaid]] "Act"
      let breachExts := match breachTarget? with
        | none => []
        | some bt =>
          let dVar : Var := ⟨d, ""⟩
          [Decl.typeExt bt [.derivation [.holdsWhen (.exists_ [dVar] (.violated (.ref dVar)))]] "Fact"]
      return extraDecls ++ relCarriers ++
             [ .ensureCarrier clkDom .time,
               .typeDecl paidDom { kind := .fact {}, domain := .products [holder, claimant, intV] },
               .typeDecl d { kind := .duty { everyPeriod := some perLen },
                             domain := .products (holder :: claimant :: objs ++ [intV]),
                             domainConstraint := filter, closed := if isClosed then none else some false },
               .typeExt d (dvClause :: allCls) ] ++ payExts ++ breachExts
  | .atom "Immunity" | .kw "Immunity" | .atom "Protection" =>
    let isProt := (← peek) == .atom "Protection"
    advance
    let d ← ident
    let _ ← optKw "With"
    expectKw "Holder"
    let holder ← var
    let objs ← relatedTo
    let filter ← domainConstraint
    let cls ← clauses .immunity 1000
    return [ .typeDecl d { kind := .immunity { isProtection := isProt }, domain := .products (holder :: objs),
                           domainConstraint := filter, closed := if isClosed then none else some false },
             .typeExt d cls ]
  | .kw "Extend" =>
    advance
    match ← peek with
    | .atom "Immunity" | .kw "Immunity" => advance; let d ← ident; return [.typeExt d (← clauses .immunity 1000) "Immunity"]
    | .atom "Protection" => advance; let d ← ident; return [.typeExt d (← clauses .immunity 1000) "Protection"]
    | .kw "Fact" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Fact"]
    | .kw "Var" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Var"]
    | .kw "Function" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Function"]
    | .kw "Bool" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Bool"]
    | .atom "Role" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Role"]
    | .kw "Act" => advance; let d ← ident; return [.typeExt d (← clauses .act 1000) "Act"]
    | .atom "Power" | .kw "Power" => advance; let d ← ident; return [.typeExt d (← clauses .act 1000) "Power"]
    | .atom "Finding" | .kw "Finding" => advance; let d ← ident; return [.typeExt d (← clauses .act 1000) "Finding"]
    | .atom "Amend" | .kw "Amend" => advance; let d ← ident; return [.typeExt d (← clauses .act 1000) "Amend"]
    | .kw "Event" => advance; let d ← ident; return [.typeExt d (← clauses .event 1000) "Event"]
    | .kw "Duty" => advance; let d ← ident; return [.typeExt d (← clauses .duty 1000) "Duty"]
    | k => fail "CHR003" s!"expected `Fact`, `Act`, `Power`, `Finding`, `Amend`, `Event`, `Duty`, or `Immunity` after `Extend` but found {k.describe}"
  | .kw "Placeholder" =>
    advance
    let f ← ident
    expectKw "For"
    let t ← ident
    return [.placeholder f t]
  | .atom "Module" | .kw "Module" =>
    advance
    let name ← ident
    expectKw "("
    let params ← (do if ← isKw ")" then return [] else sepBy1 ident "," 1000)
    expectKw ")"
    expectKw "{"
    let body ← moduleBody fuel
    return [.module name params body]
  | .atom "Use" | .kw "Use" =>
    advance
    let name ← ident
    expectKw "("
    let args ← (do if ← isKw ")" then return [] else sepBy1 ident "," 1000)
    expectKw ")"
    let pre ← (do if ← isCtxAtom "As" then advance; return some (← ident) else return none)
    let fs ← fromClauses 100
    return [.use name args pre fs]
  | .atom "Debt" =>
    -- `Debt <d> Holder h Claimant c Amount <amt> [Raised by <r>] [Paid by <p>] [Due within <dur>] [From ...]` (`D37`, `#45`, `#17`)
    advance
    let d ← ident
    expectKw "Holder"
    let holder ← var
    expectKw "Claimant"
    let claimant ← var
    if !(← isCtxAtom "Amount") then fail "CHR003" s!"expected `Amount <expr>` in `Debt {d}`"
    advance
    let amtExpr ← expression
    let raisedBy ← (do if ← isKw "Raised by" then advance; idList else return [])
    let paidBy ← (do if ← isKw "Paid by" then advance; idList else return [])
    let dueDur? ← (do if ← isKw "Due within" then advance; return some (← expression) else return none)
    let fs ← fromClauses 100
    let nextIdDom := d ++ "-next-id"
    let remDom := d ++ "-remaining"
    let curDom := "_cur_USD"
    let intV : Var := ⟨"int", ""⟩
    let curV : Var := ⟨curDom, ""⟩
    let nextIdV : Var := ⟨nextIdDom, ""⟩
    let dueCls := match dueDur? with | some dur => [ModClause.dueWithin dur] | none => []
    let fromCls := fs.map fun (cid, txt) => ModClause.fromSpan cid txt
    let raiseExts := raisedBy.map fun rAct =>
      let createDuty := Effect.cAll [] (.app d (.pos [.ref holder, .ref claimant, .ref nextIdV])) none
      let createRem := Effect.cAll [] (.app remDom (.pos [.ref nextIdV, amtExpr])) none
      let bumpNext := Effect.cAll [] (.app nextIdDom (.pos [.add (.ref nextIdV) (.intLit 1)])) none
      Decl.typeExt rAct [.postCond [createDuty, createRem, bumpNext]] "Act"
    let payExts := paidBy.map fun pAct =>
      -- Payment amount variable in `pAct` is its last component (after `int`)
      let payV : Var := ⟨"payment", ""⟩
      let curRem := Term.fnApp remDom (.ref intV)
      let validAmt := ModClause.validWhen [.and (.ge (.ref payV) (.intLit 0)) (.leq (.ref payV) curRem)]
      let updRem := Effect.cAll [] (.app remDom (.pos [.ref intV, .sub curRem (.ref payV)])) none
      let clearDuty := Effect.tAll [] (.when (.app d (.pos [.ref holder, .ref claimant, .ref intV])) (.eq curRem (.ref payV)))
      Decl.typeExt pAct [validAmt, .postCond [updRem, clearDuty]] "Act"
    return [ .ensureCarrier curDom (.money "USD" 2),
             .param nextIdDom .anyInt 1,
             .typeDecl remDom { kind := .fact {}, domain := .products [intV, curV], restriction := some .function },
             .typeDecl d { kind := .duty {}, domain := .products [holder, claimant, intV] },
             .typeExt d (dueCls ++ fromCls) ] ++ raiseExts ++ payExts
  | .atom "Param" | .kw "Param" =>
    advance
    let name ← ident
    let explicitColon := (← isKw ":")
    let dom0 ← paramDomain
    expectKw "="
    let neg ← optKw "-"
    match ← peek with
    | .moneyLit cents =>
      advance
      let val : Int := if neg then -(cents : Int) else (cents : Int)
      let dom := if explicitColon then dom0 else .money "USD" 2
      return [.param name dom val]
    | .pctLit bps =>
      advance
      let val : Int := if neg then -(bps : Int) else (bps : Int)
      let dom := if explicitColon then dom0 else .rate
      return [.param name dom val]
    | .dateLit epochDays =>
      advance
      let dom := if explicitColon then dom0 else .time
      return [.param name dom epochDays]
    | _ =>
      let n ← intLit
      match ← peek with
      | .ident "bps" =>
        advance
        let val : Int := if neg then -n else n
        let dom := if explicitColon then dom0 else .rate
        return [.param name dom val]
      | .ident "day" | .ident "days" =>
        advance
        let val : Int := if neg then -n else n
        let dom := if explicitColon then dom0 else .duration
        return [.param name dom val]
      | .ident "week" | .ident "weeks" =>
        advance
        let val : Int := (if neg then -n else n) * 7
        let dom := if explicitColon then dom0 else .duration
        return [.param name dom val]
      | _ =>
        let val : Int := if neg then -n else n
        return [.param name dom0 val]
  | .atom "Regime" | .kw "Regime" =>
    advance
    let rname ← (do match ← peek with
      | .ident s | .atom s | .str s => advance; return s
      | k => fail "CHR003" s!"expected regime name after `Regime`, found {k.describe}")
    expectKw "{"
    let entries ← parseRegimeEntries 1000
    return [.regime { name := rname, params := entries }]
  | .atom "Property" | .kw "Property" =>
    advance
    let name ← ident
    let assumes ← (do
      if ← isCtxAtom "Assumes" then
        advance
        sepBy1 ident "," 100
      else return [])
    match ← peek with
    | .kw "When" | .kw "Where" => advance
    | _ => unexpected "`When` after `Property` header"
    let tf ← temporalFormula
    let fs ← fromClauses 100
    return [.property { name, assumptions := assumes, formula := tf, spans := fs }]
  | .atom "Document" | .kw "Document" =>
    advance
    let docId? ← (do match ← peek with
      | .atom s | .ident s =>
        if (match ← peekAt 1 with | .str _ => true | _ => false) then advance; return some s else return none
      | _ => return none)
    let p ← (do match ← peek with
      | .str path => advance; return path
      | k => fail "CHR003" s!"expected the document path in double quotes after `Document` but found {k.describe}")
    let sha? ← (do
      if ← isCtxAtom "SHA256" then
        advance
        match ← peek with
        | .str hex => advance; return some hex
        | k => fail "CHR003" s!"expected SHA-256 hex digest in double quotes after `SHA256` but found {k.describe}"
      else return none)
    let rank? ← (do
      if ← isCtxAtom "Rank" then
        advance
        let neg ← optKw "-"
        let n ← intLit
        let val : Int := if neg then -n else n
        return some val
      else return none)
    return [.document p docId? sha? rank?]
  | .atom "Clause" | .kw "Clause" =>
    advance
    let cid ← clauseId
    let docId? ← (do
      if ← isCtxAtom "In" then
        advance
        match ← peek with
        | .atom s | .ident s => advance; return some s
        | k => fail "CHR003" s!"expected document identifier after `In` but found {k.describe}"
      else return none)
    let (approvedFnv, approvedSha?) ← (do
      if ← isCtxAtom "Approved" then
        advance
        match ← peek with
        | .str hex => advance; return ((0 : UInt64), some hex)
        | .int n => advance; return (n.toUInt64, none)
        | k => fail "CHR003" s!"expected approval hash or SHA-256 hex string after `Approved` but found {k.describe}"
      else return ((0 : UInt64), none))
    let (txt, spans, inits) ← clauseItems cid 1000
    if txt.isNone && spans.isEmpty then
      -- `D34` (`#35`): heading/paragraph citation by reference (`Clause 1.3 [Reg] [=> r1, ...]`)
      let k ← peek
      let isNextInvFrame ← (do
        if k == .kw "Invariant" then
          match ← peekAt 2 with
          | .kw "When" | .kw "Where" | .atom "Assumes" => return true
          | _ => return false
        else return false)
      let regOpt ← if isNextInvFrame then pure none else match registerOf k with
        | some r => advance; pure (some r)
        | none => pure none
      let targets ← (do if ← isKw "=>" then advance; sepBy1 spanTarget "," 1000 else return [])
      let ids := targets.map (·.1)
      let refInits := targets.filterMap (·.2)
      let reg := match regOpt with
        | some r => r
        | none => if ids.isEmpty then .commentary else .norm
      return (.clause { id := cid, source := "", spans := [⟨cid, "", reg, ids⟩],
                        approvedHash := approvedFnv, docId := docId?,
                        approvedSha256 := approvedSha?, byRef := true }) :: refInits.map .spanInit
    else
      let source := match txt with
        | some t => t
        | none => String.join (spans.map (·.text))
      return (.clause { id := cid, source, spans, approvedHash := approvedFnv,
                        docId := docId?, approvedSha256 := approvedSha?, byRef := false }) :: inits.map .spanInit
  | k => fail "CHR003" s!"expected a declaration but found {k.describe}"

end

/-- Whether the upcoming tokens begin a frame (D17). -/
def startsFrame : P Bool := do
  match ← peek with
  | .kw "Open" | .kw "Closed" => isFrameHeadAt 1
  | .atom "Evidenced" | .atom "Input" => isFrameHeadAt 0
  | _ => isFrameHeadAt 0

def declarations : Nat → P (List Decl)
  | 0 => return []
  | fuel + 1 => do
    let ds ← frame fuel
    if ← startsFrame then return ds ++ (← declarations fuel) else return ds

/-! ## Phrases -/

def optBySource : P String := do
  if ← isCtxAtom "By" then
    advance
    match ← peek with
    | .str s | .atom s | .ident s => advance; return s
    | k => fail "CHR003" s!"expected evidence source after `By` but found {k.describe}"
  else return ""

def optTriggerNote : P (Option String) := do
  if ← isCtxAtom "Note" then
    match ← peekAt 1 with
    | .str s => advance; advance; return some s
    | _ => return none
  else return none

def phrase : P Phrase := do
  if ← startsFrame then return .decls (← declarations 10000)
  match ← peek with
  | .kw "+" => advance; let (xs, t) ← optForeach; return .create xs t
  | .kw "-" => advance; let (xs, t) ← optForeach; return .terminate xs t
  | .kw "~" => advance; let (xs, t) ← optForeach; return .obfuscate xs t
  | .kw "?" => advance; return .query (← expression)
  | .kw "!?" => advance; return .query (.not (← expression))
  | .kw "?-" => advance; let (xs, t) ← optForeach; return .instQuery false xs t
  | .kw "?--" => advance; let (xs, t) ← optForeach; return .instQuery true xs t
  | .kw "?occurred" => advance; return .expect .occurred false (← expression)
  | .kw "?lawful" => advance; return .expect .lawful false (← expression)
  | .kw "?valid" => advance; return .expect .valid false (← expression)
  | .kw "?violated" => advance; return .expect .violated false (← expression)
  | .kw "?late" => advance; return .expect .late false (← expression)
  | .kw "?undetermined" => advance; return .expect .undetermined false (← expression)
  | .kw "?conflict" => advance; return .expect .conflict false (← expression)
  | .kw "?!occurred" => advance; return .expect .occurred true (← expression)
  | .kw "?!lawful" => advance; return .expect .lawful true (← expression)
  | .kw "?!valid" => advance; return .expect .valid true (← expression)
  | .kw "?!violated" => advance; return .expect .violated true (← expression)
  | .kw "?!late" => advance; return .expect .late true (← expression)
  | .kw "?!undetermined" => advance; return .expect .undetermined true (← expression)
  | .kw "?!conflict" => advance; return .expect .conflict true (← expression)
  | .kw "@" => advance; return .setTime (← expression)
  | .atom "SubmitEvidence" =>
    let t1 ← peekAt 1
    if (match t1 with | .kw "!" | .ident _ | .kw "(" => true | _ => false) then
      advance
      let neg ← optKw "!"
      let t ← expression
      let src ← optBySource
      return .submitEvidence (!neg) t src
    else
      let (xs, t) ← optForeach; let n ← optTriggerNote; return .trigger xs t n
  | .atom "RetractEvidence" =>
    let t1 ← peekAt 1
    if (match t1 with | .ident _ | .kw "(" => true | _ => false) then
      advance
      let t ← expression
      let src ← optBySource
      return .retractEvidence t src
    else
      let (xs, t) ← optForeach; let n ← optTriggerNote; return .trigger xs t n
  | .ident "tick" | .kw "tick" =>
    let next ← peekAt 1
    if next == .kw "." || next == .kw "}" || next == .eof then
      advance; return .tick
    else
      let (xs, t) ← optForeach; let n ← optTriggerNote; return .trigger xs t n
  | .kw "?why" => advance; return .why (← expression)
  | .kw "!" => advance; let (xs, t) ← optForeach; let n ← optTriggerNote; return .trigger xs t n
  | _ => let (xs, t) ← optForeach; let n ← optTriggerNote; return .trigger xs t n

/-- The body of `Scenario name { … }`: phrases, `Let alias = expr.`, and parallel blocks. -/
def scenarioBody : Nat → P (List Phrase)
  | 0 => return []
  | fuel + 1 => do
    if ← isKw "}" then advance; return []
    if ← isKw "{" then
      advance
      let ps ← parBlockFuel fuel
      return .par ps :: (← scenarioBody fuel)
    if (← isCtxAtom "Let") && (match ← peekAt 2 with | .kw "=" => true | _ => false) then
      advance
      let aliasName ← (do match ← peek with
        | .atom s => advance; return s
        | .ident s => advance; return s
        | k => fail "CHR003" s!"expected alias name after `Let` but found {k.describe}")
      expectKw "="
      let val ← expression
      expectKw "."
      let rest ← scenarioBody fuel
      return Phrase.substAliasList aliasName val rest
    let p ← phrase
    match ← peek with
    | .kw "." => advance; return p :: (← scenarioBody fuel)
    | .kw "}" => advance; return [p]
    | k => fail "CHR004" s!"expected `.` to end the phrase but found {k.describe}"
where
  parBlockFuel : Nat → P (List Phrase)
    | 0 => return []
    | fuel + 1 => do
      if ← isKw "}" then advance; return []
      let p ← phrase
      if ← isKw "." then
        advance
        return p :: (← parBlockFuel fuel)
      else if ← isKw "}" then advance; return [p]
      else unexpected "`.` or `}` after a phrase in a parallel block"

/-- `{ p₁. p₂. … }` with an optional final `.`. -/
def parBlock : Nat → P (List Phrase)
  | 0 => return []
  | fuel + 1 => do
    if ← isKw "}" then advance; return []
    let p ← phrase
    if ← isKw "." then
      advance
      return p :: (← parBlock fuel)
    else if ← isKw "}" then advance; return [p]
    else unexpected "`.` or `}` after a phrase in a parallel block"

def directive : P (Option Directive) := do
  match ← peek with
  | .kw "#include" => advance; let p ← stringLit; return some (.include p)
  | .kw "#require" => advance; let p ← stringLit; return some (.require p)
  | _ => return none
where
  stringLit : P String := do
    match ← peek with
    | .str s => advance; return s
    | _ => unexpected "a file name in double quotes"

/-- The whole file: directives and phrases, each terminated by `.` except a
parallel block and an optional last phrase. -/
def items (lineOf : Pos → String) (seenScenarios : List (String × List Phrase) := []) : Nat → P (List Item)
  | 0 => fail "CHR003" "file too long to parse"
  | fuel + 1 => do
    if (← peek) == .eof then return []
    let p ← pos
    match ← directive with
    | some d =>
      expectKw "."
      return ⟨p, lineOf p, .inl d⟩ :: (← items lineOf seenScenarios fuel)
    | none =>
    if ← isKw "{" then
      advance
      let ps ← parBlock 10000
      return ⟨p, lineOf p, .inr (.par ps)⟩ :: (← items lineOf seenScenarios fuel)
    else if (← isCtxAtom "Scenario") && (match ← peekAt 1 with | .ident _ | .atom _ | .str _ => true | _ => false) then
      advance
      let name ← (do match ← peek with
        | .ident s => advance; return s
        | .atom s => advance; return s
        | .str s => advance; return s
        | k => fail "CHR003" s!"expected a scenario name but found {k.describe}")
      let after? ← (do
        if ← isCtxAtom "After" then
          advance
          match ← peek with
          | .ident s => advance; return some s
          | .atom s => advance; return some s
          | .str s => advance; return some s
          | k => fail "CHR003" s!"expected base scenario name after `After` but found {k.describe}"
        else return none)
      let fs ← fromClauses 100
      expectKw "{"
      let ownPs ← scenarioBody 10000
      let fullPs ← match after? with
        | none => pure ownPs
        | some baseName =>
          match seenScenarios.find? (·.1 == baseName) with
          | some (_, basePs) => pure (basePs ++ ownPs)
          | none => fail "CHR010" s!"Scenario `{name}` After `{baseName}`: unknown prior scenario `{baseName}`"
      let seen' := (name, fullPs) :: seenScenarios.filter (·.1 != name)
      return ⟨p, lineOf p, .inr (.scenario name fullPs fs)⟩ :: (← items lineOf seen' fuel)
    else
      let ph ← phrase
      match ← peek with
      | .kw "." => advance; return ⟨p, lineOf p, .inr ph⟩ :: (← items lineOf seenScenarios fuel)
      | .eof => return [⟨p, lineOf p, .inr ph⟩]
      | k => fail "CHR004" s!"expected `.` to end the phrase but found {k.describe}"

end Parser

/-- Parse a source text into items; `eflint` restricts the keywords to eFLINT's. -/
def parseSource (src : String) (eflint : Bool := false) : Except Diagnostic (List Item) := do
  let toks ← tokenize src eflint
  let lines := src.splitOn "\n" |>.toArray
  let lineOf (p : Pos) : String :=
    if h : p.line - 1 < lines.size then lines[p.line - 1].trim else ""
  match Parser.items lineOf [] (toks.size + 2) { toks } with
  | .ok (its, _) => return its
  | .error e => throw e

end Charter
