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
def binderForm : Nat → (List Var → Term → Term) → P Term
  | 0, _ => fail "CHR003" "expression too deeply nested"
  | fuel + 1, mk => do
    let xs ← vars
    expectKw ":"
    let body ← expr fuel
    expectKw ")"
    return mk xs body

/-- `Sum`/`Count`/`Max`/`Min` `(Foreach xs : body)`. -/
def aggregate : Nat → (List Var → Term → Term) → P Term
  | 0, _ => fail "CHR003" "expression too deeply nested"
  | fuel + 1, mk => do
    expectKw "("
    expectKw "Foreach"
    binderForm fuel mk

def primary : Nat → P Term
  | 0 => fail "CHR003" "expression too deeply nested"
  | fuel + 1 => do
    match ← peek with
    | .kw "True" => advance; return .boolLit true
    | .kw "False" => advance; return .boolLit false
    | .kw "Current Time" => advance; return .currentTime
    | .int n => advance; return .intLit n
    | .str s => advance; return .stringLit s
    | .atom "MulDivRound" =>
      if (← peekAt 1) == .kw "(" then
        advance
        expectKw "("
        let x ← expr fuel
        expectKw ","
        let num ← expr fuel
        expectKw ","
        let den ← expr fuel
        expectKw ","
        let mode : RoundingMode ← (do
          match ← peek with
          | .atom "Floor" | .ident "floor" => advance; return .floor
          | .atom "Ceil" | .ident "ceil" => advance; return .ceil
          | .atom "NearestEven" | .ident "nearestEven" => advance; return .nearestEven
          | .atom "ExactOrReject" | .ident "exactOrReject" => advance; return .exactOrReject
          | k => fail "CHR003" s!"expected rounding mode (`Floor`, `Ceil`, `NearestEven`, or `ExactOrReject`), found {k.describe}")
        expectKw ")"
        return .mulDivRound x num den mode
      else
        advance; return .stringLit "MulDivRound"
    | .atom s => advance; return .stringLit s
    | .kw "Sum" => advance; aggregate fuel .sum
    | .kw "Count" => advance; aggregate fuel .count
    | .kw "Max" => advance; aggregate fuel .max
    | .kw "Min" => advance; aggregate fuel .min
    | .kw "(" =>
      advance
      match ← peek with
      | .kw "Exists" => advance; binderForm fuel .exists_
      | .kw "Forall" => advance; binderForm fuel .forall_
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
    let xs ← sepBy1 var "*" 1000
    return .products xs
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
    if ["Immunity", "Module", "Use", "Param", "Property", "Power", "Finding", "Amend"].contains s then
      return (match ← peekAt (idx + 1) with | .ident _ => true | _ => false)
    else if s == "Entrenched" then
      return (match ← peekAt (idx + 1) with | .kw "Invariant" | .kw "Predicate" => true | _ => false)
    else if s == "Regime" then
      let t1 ← peekAt (idx + 1)
      let t2 ← peekAt (idx + 2)
      return (match t1, t2 with
        | .ident _, .kw "{" | .atom _, .kw "{" | .str _, .kw "{" => true
        | _, _ => false)
    else if s == "Evidenced" then
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

/-- The items of a `Clause` frame: `Text "…"` and register spans `Norm "…" => ids`. -/
def clauseItems (cid : ClauseId) : Nat → P (Option String × List Span)
  | 0 => return (none, [])
  | fuel + 1 => do
    match ← peek with
    | .atom "Text" | .kw "Text" =>
      if (match ← peekAt 1 with | .str _ => true | _ => false) then
        advance
        match ← peek with
        | .str t => advance; let (_, spans) ← clauseItems cid fuel; return (some t, spans)
        | k => fail "CHR003" s!"expected the clause text in double quotes after `Text` but found {k.describe}"
      else return (none, [])
    | k =>
      match registerOf k with
      | some reg =>
        -- `Invariant "…"` is a span; `Invariant id When …` starts a new frame
        match ← peekAt 1 with
        | .str text =>
          advance; advance
          let ids ← (do if ← isKw "=>" then advance; sepBy1 ident "," 1000 else return [])
          let (txt, spans) ← clauseItems cid fuel
          return (txt, ⟨cid, text, reg, ids⟩ :: spans)
        | _ => return (none, [])
      | none => return (none, [])

/-- Parse a defeasible rule identifier (`r-base`, `r1`, or `R1`). -/
def ruleId : P String := do
  match ← peek with
  | .atom s => advance; return s
  | _ => toString <$> var

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
  | .kw "Violated when" =>
    if k != .duty then return none
    advance; return some (.violation (← exprList))
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
    advance; return some (.dueWithin (← expression))
  | .atom "From" | .kw "From" =>
    -- `From CLAUSE "span"` on an act, duty, immunity, or fact (an Invariant)
    if k == .event then return none
    if !(match ← peekAt 1 with | .atom _ | .ident _ | .int _ => true | _ => false) then return none
    advance
    let cid ← clauseId
    match ← peek with
    | .str text => advance; return some (.fromSpan cid text)
    | kk => fail "CHR003" s!"expected the span text in double quotes after `From {cid}` but found {kk.describe}"
  | .kw "Valid when" =>
    if k != .act then return none
    advance; return some (.validWhen (← exprList))
  | .kw "Except under" =>
    if k != .act then return none
    advance; return some (.exceptUnder (← idList))
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
  | .atom "Repeals" =>
    if k != .act then return none
    advance
    let rs ← idList
    return some (.repeals rs)
  | .atom "Protects" =>
    if k != .immunity then return none
    advance
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
  | .atom "Unless" | .kw "Unless" =>
    if k != .immunity then return none
    advance; return some (.unlessCond (← exprList))
  | _ =>
    match ← derivationClause with
    | some ds => return some (.derivation ds)
    | none => return none

/-- Zero or more `From CLAUSE "span"` clauses on an `Invariant`, `Predicate`, or `Scenario`. -/
def fromClauses : Nat → P (List (ClauseId × String))
  | 0 => return []
  | fuel + 1 => do
    if ← isCtxAtom "From" then
      advance
      let cid ← clauseId
      match ← peek with
      | .str text => advance; return (cid, text) :: (← fromClauses fuel)
      | kk => fail "CHR003" s!"expected the span text in double quotes after `From {cid}` but found {kk.describe}"
    else return []

def clauses (k : FrameKind) : Nat → P (List ModClause)
  | 0 => return []
  | fuel + 1 => do
    match ← clause k with
    | some c => return c :: (← clauses k fuel)
    | none => return []

def openness : P (Bool × Bool) := do
  match ← peek with
  | .kw "Closed" => advance; return (true, false)
  | .kw "Open" =>
    advance
    if ← isCtxAtom "Evidenced" then advance; return (false, true)
    else return (false, false)
  | .atom "Evidenced" =>
    advance
    let _ ← optKw "Open"
    return (false, true)
  | _ => return (true, false)

def domainConstraint : P Term := do
  match ← peek with
  | .kw "When" | .kw "Where" => advance; expression
  | _ => return .boolLit true

def relatedTo : P (List Var) := do
  if ← isKw "Related to" then advance; vars else return []

def mkFact (inv isActor isClosed : Bool) (restr : Option Restriction) (d : DomId) (dom : Domain)
    (filter : Term) (cls : List ModClause) (isEv : Bool := false) (isEnt : Bool := false) : List Decl :=
  [ .typeDecl d { kind := .fact { invariant := inv, actor := isActor, evidenced := isEv, entrenched := isEnt }, domain := dom,
                  domainConstraint := filter, restriction := restr, derivation := [],
                  closed := if isClosed && !isEv then none else some false, conditions := [] },
    .typeExt d cls ]

/-- `: Int | Time | Duration` after a `Param` name; `Int` when absent. -/
def paramDomain : P Domain := do
  if ← isKw ":" then
    advance
    match ← peek with
    | .kw "Int" => advance; return Domain.anyInt
    | .kw "Time" => advance; return Domain.time
    | .atom "Duration" | .kw "Duration" => advance; return Domain.duration
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
    | k => fail "CHR003" s!"expected Int, Time, Duration, Money(CUR, SCALE), or Quantity(UNIT) after `:` but found {k.describe}"
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
  let (isClosed, isEv) ← openness
  match ← peek with
  | .kw "Fact" | .kw "Var" | .kw "Function" =>
    let restr : Option Restriction ← (do match ← peek with
      | .kw "Var" => advance; return some .var
      | .kw "Function" => advance; return some .function
      | _ => advance; return none)
    let d ← ident
    let dom ← (do if ← isKw "Identified by" then advance; typeExpr else return .anyString)
    let filter ← domainConstraint
    let cls ← clauses .fact 1000
    return mkFact false false isClosed restr d dom filter cls isEv
  | .kw "Bool" =>
    advance
    let d ← ident
    let cls ← clauses .fact 1000
    return mkFact false false isClosed none d (.products []) (.boolLit true) cls isEv
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
      (.derivation [.holdsWhen t] :: fs.map (fun (c, s) => .fromSpan c s)) false isEnt
  | .kw "Act" | .atom "Power" | .kw "Power" | .atom "Finding" | .kw "Finding" | .atom "Amend" | .kw "Amend" =>
    let cur ← peek
    let isFind := cur == .atom "Finding" || cur == .kw "Finding"
    let isAm := cur == .atom "Amend" || cur == .kw "Amend"
    let isPow := isFind || isAm || cur != .kw "Act"
    advance
    let d ← ident
    let _ ← optKw "With"
    let actor ← (do if ← isKw "Actor" then advance; return some (← var) else return none)
    let recip ← (do if ← isKw "Recipient" then advance; return some (← var) else return none)
    let objs ← relatedTo
    let filter ← domainConstraint
    let (cls, instBody) ← parseActExtras fuel 1000
    let actorV := actor.getD ⟨"actor", ""⟩
    let instDecls := if instBody.isEmpty then [] else [Decl.amendInstall d instBody]
    return [ .typeDecl d { kind := .act { hasRecipient := recip.isSome, isPower := isPow, isFinding := isFind, isAmend := isAm },
                           domain := .products (actorV :: (recip.toList ++ objs)),
                           domainConstraint := filter, closed := if isClosed then none else some false },
             .typeExt d cls ] ++ instDecls
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
    expectKw "Claimant"
    let claimant ← var
    let objs ← relatedTo
    let filter ← domainConstraint
    let cls ← clauses .duty 1000
    return [ .typeDecl d { kind := .duty {}, domain := .products (holder :: claimant :: objs),
                           domainConstraint := filter, closed := if isClosed then none else some false },
             .typeExt d cls ]
  | .atom "Immunity" | .kw "Immunity" =>
    advance
    let d ← ident
    let _ ← optKw "With"
    expectKw "Holder"
    let holder ← var
    let objs ← relatedTo
    let filter ← domainConstraint
    let cls ← clauses .immunity 1000
    return [ .typeDecl d { kind := .immunity {}, domain := .products (holder :: objs),
                           domainConstraint := filter, closed := if isClosed then none else some false },
             .typeExt d cls ]
  | .kw "Extend" =>
    advance
    match ← peek with
    | .atom "Immunity" | .kw "Immunity" => advance; let d ← ident; return [.typeExt d (← clauses .immunity 1000) "Immunity"]
    | .kw "Fact" => advance; let d ← ident; return [.typeExt d (← clauses .fact 1000) "Fact"]
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
    return [.use name args pre]
  | .atom "Param" | .kw "Param" =>
    advance
    let name ← ident
    let dom ← paramDomain
    expectKw "="
    let neg ← optKw "-"
    let n ← intLit
    let value : Int := if neg then -n else n
    return [.param name dom value]
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
    let (txt, spans) ← clauseItems cid 1000
    let source := match txt with
      | some t => t
      | none => String.join (spans.map (·.text))
    return [.clause { id := cid, source, spans, approvedHash := approvedFnv, docId := docId?, approvedSha256 := approvedSha? }]
  | k => fail "CHR003" s!"expected a declaration but found {k.describe}"

end

/-- Whether the upcoming tokens begin a frame (D17). -/
def startsFrame : P Bool := do
  match ← peek with
  | .kw "Open" | .kw "Closed" => isFrameHeadAt 1
  | .atom "Evidenced" => isFrameHeadAt 0
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
  | .kw "?lawful" => advance; return .expect .lawful false (← expression)
  | .kw "?valid" => advance; return .expect .valid false (← expression)
  | .kw "?violated" => advance; return .expect .violated false (← expression)
  | .kw "?undetermined" => advance; return .expect .undetermined false (← expression)
  | .kw "?conflict" => advance; return .expect .conflict false (← expression)
  | .kw "?!lawful" => advance; return .expect .lawful true (← expression)
  | .kw "?!valid" => advance; return .expect .valid true (← expression)
  | .kw "?!violated" => advance; return .expect .violated true (← expression)
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

/-- The body of `Scenario name { … }`: phrases and parallel blocks, as at top level. -/
def scenarioBody : Nat → P (List Phrase)
  | 0 => return []
  | fuel + 1 => do
    if ← isKw "}" then advance; return []
    if ← isKw "{" then
      advance
      let ps ← parBlockFuel fuel
      return .par ps :: (← scenarioBody fuel)
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
def items (lineOf : Pos → String) : Nat → P (List Item)
  | 0 => fail "CHR003" "file too long to parse"
  | fuel + 1 => do
    if (← peek) == .eof then return []
    let p ← pos
    match ← directive with
    | some d =>
      expectKw "."
      return ⟨p, lineOf p, .inl d⟩ :: (← items lineOf fuel)
    | none =>
    if ← isKw "{" then
      advance
      let ps ← parBlock 10000
      return ⟨p, lineOf p, .inr (.par ps)⟩ :: (← items lineOf fuel)
    else if (← isCtxAtom "Scenario") && (match ← peekAt 1 with | .ident _ | .atom _ | .str _ => true | _ => false) then
      advance
      let name ← (do match ← peek with
        | .ident s => advance; return s
        | .atom s => advance; return s
        | .str s => advance; return s
        | k => fail "CHR003" s!"expected a scenario name but found {k.describe}")
      let fs ← fromClauses 100
      expectKw "{"
      let ps ← scenarioBody 10000
      return ⟨p, lineOf p, .inr (.scenario name ps fs)⟩ :: (← items lineOf fuel)
    else
      let ph ← phrase
      match ← peek with
      | .kw "." => advance; return ⟨p, lineOf p, .inr ph⟩ :: (← items lineOf fuel)
      | .eof => return [⟨p, lineOf p, .inr ph⟩]
      | k => fail "CHR004" s!"expected `.` to end the phrase but found {k.describe}"

end Parser

/-- Parse a source text into items; `eflint` restricts the keywords to eFLINT's. -/
def parseSource (src : String) (eflint : Bool := false) : Except Diagnostic (List Item) := do
  let toks ← tokenize src eflint
  let lines := src.splitOn "\n" |>.toArray
  let lineOf (p : Pos) : String :=
    if h : p.line - 1 < lines.size then lines[p.line - 1].trim else ""
  match Parser.items lineOf (toks.size + 2) { toks } with
  | .ok (its, _) => return its
  | .error e => throw e

end Charter
