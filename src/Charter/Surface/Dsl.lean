import Lean
import Charter.Core.Provenance

/-!
# Charter.Surface.Dsl — The `.charter` Language: AST, Parser, Validator, Printer

A Charter program is a `.charter` text file. This module defines what such a file
says (`Doc`), how it is read (`parseCharterText`), the static checks a document must
pass before it means anything (`validate`), and how a document is printed back out
(`render`). Everything here is plain data over strings and numbers: it knows nothing
about any particular program, and nothing about Lean's kernel. The meaning of a
`Doc` is given by `Charter.Surface.Lower`, which turns it into a `Charter.Law`.

The parser and printer are written over `List Char` / `List Tok` with explicit fuel
and no `partial` definitions, so a document can also be parsed inside the kernel
(`by decide`) when a theorem wants to talk about a literal `.charter` text.

## The grammar

A file is a sequence of declarations. A declaration starts at the beginning of a
line with one of the keywords below and continues over the following lines until the
next declaration keyword. Everything after `--` on a line is a comment. Strings use
double quotes with `\"`, `\\`, `\n`, `\t` escapes and may span lines.

    charter <id> "<title>"
    document "<relative path of the authoritative English>"
    contract "<name for the smart-contract guard>"          -- optional
    default actor <role>                                     -- optional, for `prompt`

    roles a, b, c
    acts x, y, z
    facts f, g(role), h                                      -- `g(role)` takes a role argument

    params                                                   -- named numbers
      noticeWindow = 10
    regime "<label>"                                         -- an alternative parameter set
      noticeWindow = 20

    init f, g(a)                                             -- facts established at time 0

    use module <Name> with a = 1, b = noticeWindow           -- documented module instantiation

    clause <id> approved <hash>
      text "<the complete clause>"                           -- optional when spans cover it
      norm "<span>" => D.X, P.Y
      definition "<span>" => D.X
      invariant "<span>"
      acceptance "<span>"
      commentary "<span>"

    duty <id>
      from <clause> [<register>] "<span>" [meaning <ids> | meaning none]
      bearer <who>
      beneficiary <who>
      active <cond>
      forbid <conduct>                 |  require <conduct> within <num>
      except when <cond>
      except by power P.A, P.B
      overridden by D.A, D.B
      breach by P.FIND
      remedies f, g(a)

    power <id>
      from <clause> "<span>"
      holder <who>
      trigger <conduct>
      valid <cond>
      adds f, g
      adds f for <num>                 -- established with a time-to-live
      adds f to <role>                 -- established for the actor if it is <role>
      adds f if <cond>                 -- established only when <cond> held before
      removes f, g
      establishes breach of D.X

    immunity <id>
      from <clause> "<span>"
      holder <who>
      against P.A, P.B
      active <cond>
      except when <cond>

    <who>     ::= anyone | only a, b | except a, b | tagged f | tagged a: f(a), b: f(b)
    <cond>    ::= true | false | holds f | heldFor f <num> | countGe f <num>
                | countAtLeast f g | not <cond> | <cond> and <cond> | <cond> or <cond> | ( <cond> )
    <conduct> ::= act x | anyOf x, y | exerciseOf P.X | not <conduct>
                | <conduct> and <conduct> | <conduct> or <conduct> | ( <conduct> )
    <num>     ::= <atom> | <num> + <atom>          <atom> ::= <natural> | <param name>
    <register>::= norm | definition | invariant | acceptance | commentary

`not` binds tighter than `and`, which binds tighter than `or`; both are left-associative.
-/

namespace Charter.Dsl

open Charter

deriving instance Lean.ToExpr for Charter.Register

instance : Inhabited Register := ⟨.norm⟩

/-! ## 1. Abstract Syntax -/

/-- A reference to a fact: a declared fact name, optionally applied to a role
(`initiator(agent)`). -/
structure FactRef where
  name : String
  arg  : Option String := none
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A number: a literal, the name of a parameter, or a sum. -/
inductive NumE
  | lit   (n : Nat)
  | param (name : String)
  | add   (a b : NumE)
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A class of actors. `taggedAll f` abbreviates `tagged r₁: f(r₁), …, rₙ: f(rₙ)` over
every declared role in declaration order. -/
inductive WhoE
  | anyone
  | only      (xs : List String)
  | except    (xs : List String)
  | tagged    (pairs : List (String × FactRef))
  | taggedAll (f : String)
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A condition on institutional state. -/
inductive CondE
  | tt
  | ff
  | holds        (f : FactRef)
  | heldFor      (f : FactRef) (d : NumE)
  | countGe      (f : FactRef) (n : NumE)
  | countAtLeast (f g : FactRef)
  | not          (c : CondE)
  | and          (a b : CondE)
  | or           (a b : CondE)
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- Regulated conduct. -/
inductive ConductE
  | act        (a : String)
  | anyOf      (as : List String)
  | exerciseOf (power : String)
  | not        (c : ConductE)
  | and        (a b : ConductE)
  | or         (a b : ConductE)
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- What a duty demands. -/
inductive DemandE
  | forbid  (c : ConductE)
  | require (c : ConductE) (within : NumE)
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- The English span a rule is read from. `meaning = none` means the default, the
rule's own id. -/
structure SourceE where
  clause   : String := ""
  text     : String := ""
  register : Register := .norm
  meaning  : Option (List String) := none
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- One span of a clause. -/
structure SpanE where
  register : Register
  text     : String
  meaning  : List String := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A clause of the authoritative English. `text = none` means the clause is the
concatenation of its spans. -/
structure ClauseE where
  id       : String
  text     : Option String := none
  approved : Option Nat := none
  spans    : List SpanE := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

structure DutyE where
  id           : String
  source       : SourceE := {}
  bearer       : WhoE := .anyone
  beneficiary  : WhoE := .anyone
  active       : CondE := .tt
  demand       : DemandE := .forbid (.act "")
  unlessCond   : CondE := .ff
  unlessPower  : List String := []
  overriddenBy : List String := []
  breachBy     : Option String := none
  remedies     : List FactRef := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

structure PowerE where
  id                  : String
  source              : SourceE := {}
  holder              : WhoE := .anyone
  trigger             : ConductE := .act ""
  valid               : CondE := .tt
  adds                : List FactRef := []
  addsFor             : List (FactRef × NumE) := []
  addsByActor         : List (String × FactRef) := []
  removes             : List FactRef := []
  condAdds            : List (CondE × FactRef) := []
  establishesBreachOf : Option String := none
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

structure ImmunityE where
  id         : String
  source     : SourceE := {}
  holder     : WhoE := .anyone
  against    : List String := []
  active     : CondE := .tt
  unlessCond : CondE := .ff
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A declared fact: nullary, or taking a role argument. -/
structure FactDecl where
  name      : String
  takesRole : Bool := false
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A documented instantiation of a standard-library module. -/
structure ModuleUse where
  name : String
  args : List (String × NumE) := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- An alternative parameter regime, for `explore`. -/
structure Regime where
  label  : String
  params : List (String × Nat) := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-- A complete `.charter` document. -/
structure Doc where
  id           : String := ""
  title        : String := ""
  document     : Option String := none
  contract     : Option String := none
  defaultActor : Option String := none
  roles        : List String := []
  acts         : List String := []
  facts        : List FactDecl := []
  params       : List (String × Nat) := []
  regimes      : List Regime := []
  init         : List FactRef := []
  modules      : List ModuleUse := []
  clauses      : List ClauseE := []
  duties       : List DutyE := []
  powers       : List PowerE := []
  immunities   : List ImmunityE := []
  deriving Repr, DecidableEq, BEq, Inhabited, Lean.ToExpr

/-! ## 2. Tokens -/

inductive Tok
  | ident (s : String)
  | num   (n : Nat)
  | str   (s : String)
  | sym   (s : String)
  | nl
  deriving Repr, DecidableEq, BEq, Inhabited

def Tok.show : Tok → String
  | .ident s => s
  | .num n   => toString n
  | .str s   => "\"" ++ s ++ "\""
  | .sym s   => s
  | .nl      => "end of line"

structure Located where
  tok  : Tok
  line : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '\''

def digitsToNat (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Read a string literal body (after the opening quote), handling escapes.
Returns the string, the remaining input, and the line after the literal. -/
def readString : Nat → List Char → List Char → Nat → Except String (String × List Char × Nat)
  | 0, _, _, line => .error s!"line {line}: unterminated string"
  | _, [], _, line => .error s!"line {line}: unterminated string"
  | fuel+1, c :: cs, acc, line =>
    if c == '"' then .ok (String.mk acc.reverse, cs, line)
    else if c == '\\' then
      match cs with
      | 'n' :: rest  => readString fuel rest ('\n' :: acc) line
      | 't' :: rest  => readString fuel rest ('\t' :: acc) line
      | '"' :: rest  => readString fuel rest ('"' :: acc) line
      | '\\' :: rest => readString fuel rest ('\\' :: acc) line
      | _ => .error s!"line {line}: bad escape in string"
    else if c == '\n' then readString fuel cs (c :: acc) (line + 1)
    else readString fuel cs (c :: acc) line

def tokenizeGo : Nat → List Char → Nat → List Located → Except String (List Located)
  | 0, _, line, _ => .error s!"line {line}: tokenizer out of fuel"
  | _, [], _, acc => .ok acc.reverse
  | fuel+1, c :: cs, line, acc =>
    if c == '\n' then tokenizeGo fuel cs (line + 1) (⟨.nl, line⟩ :: acc)
    else if c == ' ' || c == '\t' || c == '\r' then tokenizeGo fuel cs line acc
    else if c == '-' && cs.head? == some '-' then
      tokenizeGo fuel (cs.dropWhile (· != '\n')) line acc
    else if c == '"' then
      match readString (cs.length + 1) cs [] line with
      | .error e => .error e
      | .ok (s, rest, line') => tokenizeGo fuel rest line' (⟨.str s, line⟩ :: acc)
    else if c.isDigit then
      let ds := (c :: cs).takeWhile Char.isDigit
      tokenizeGo fuel ((c :: cs).dropWhile Char.isDigit) line (⟨.num (digitsToNat ds), line⟩ :: acc)
    else if isIdentStart c then
      let ds := (c :: cs).takeWhile isIdentChar
      tokenizeGo fuel ((c :: cs).dropWhile isIdentChar) line (⟨.ident (String.mk ds), line⟩ :: acc)
    else if c == '=' && cs.head? == some '>' then
      tokenizeGo fuel cs.tail line (⟨.sym "=>", line⟩ :: acc)
    else if c == '(' || c == ')' || c == ',' || c == '=' || c == ':' || c == '+' then
      tokenizeGo fuel cs line (⟨.sym (String.mk [c]), line⟩ :: acc)
    else .error s!"line {line}: unexpected character '{String.mk [c]}'"

def tokenize (input : String) : Except String (List Located) :=
  tokenizeGo (input.length + 1) input.data 1 []

/-! ## 3. Lines and Blocks -/

/-- One logical line: its number and its tokens (never empty, never containing `nl`). -/
structure Line where
  line : Nat
  toks : List Tok
  deriving Repr, Inhabited

def splitLinesGo : List Located → Nat → List Tok → List Line → List Line
  | [], line, cur, acc =>
    (if cur.isEmpty then acc else ⟨line, cur.reverse⟩ :: acc).reverse
  | l :: ls, line, cur, acc =>
    match l.tok with
    | .nl => splitLinesGo ls (l.line + 1) [] (if cur.isEmpty then acc else ⟨line, cur.reverse⟩ :: acc)
    | t => splitLinesGo ls (if cur.isEmpty then l.line else line) (t :: cur) acc

def splitLines (ts : List Located) : List Line := splitLinesGo ts 1 [] []

def topKeywords : List String :=
  ["charter", "document", "contract", "default", "roles", "acts", "facts", "params",
   "regime", "init", "use", "clause", "duty", "power", "immunity"]

def Line.isBlockStart (l : Line) : Bool :=
  match l.toks with
  | .ident k :: _ => topKeywords.contains k
  | _ => false

/-- A declaration: its header line and its field lines. -/
structure Block where
  header : Line
  fields : List Line
  deriving Repr, Inhabited

def groupBlocksGo : List Line → Option Block → List Block → Except String (List Block)
  | [], none, acc => .ok acc.reverse
  | [], some b, acc => .ok (({ b with fields := b.fields.reverse }) :: acc).reverse
  | l :: ls, cur, acc =>
    if l.isBlockStart then
      let acc' := match cur with
        | none => acc
        | some b => ({ b with fields := b.fields.reverse }) :: acc
      groupBlocksGo ls (some ⟨l, []⟩) acc'
    else
      match cur with
      | none => .error s!"line {l.line}: expected a declaration keyword, found {(l.toks.head?.map Tok.show).getD ""}"
      | some b => groupBlocksGo ls (some { b with fields := l :: b.fields }) acc

def groupBlocks (ls : List Line) : Except String (List Block) := groupBlocksGo ls none []

/-! ## 4. Token-Level Parsers -/

/-- A parser over the tokens of one line. -/
abbrev P := StateT (List Tok) (Except String)

def fail {α : Type} (msg : String) : P α := fun _ => .error msg

def peek : P (Option Tok) := fun ts => .ok (ts.head?, ts)

def next : P Tok := fun ts =>
  match ts with
  | [] => .error "unexpected end of line"
  | t :: rest => .ok (t, rest)

def atEnd : P Bool := fun ts => .ok (ts.isEmpty, ts)

def isKw (s : String) : P Bool := fun ts =>
  .ok (match ts with | .ident k :: _ => k == s | _ => false, ts)

def isSym (s : String) : P Bool := fun ts =>
  .ok (match ts with | .sym k :: _ => k == s | _ => false, ts)

def expectKw (s : String) : P Unit := do
  match ← next with
  | .ident k => if k == s then pure () else fail s!"expected '{s}', found '{k}'"
  | t => fail s!"expected '{s}', found {t.show}"

def expectSym (s : String) : P Unit := do
  match ← next with
  | .sym k => if k == s then pure () else fail s!"expected '{s}', found '{k}'"
  | t => fail s!"expected '{s}', found {t.show}"

def ident : P String := do
  match ← next with
  | .ident s => pure s
  | t => fail s!"expected a name, found {t.show}"

def strLit : P String := do
  match ← next with
  | .str s => pure s
  | t => fail s!"expected a quoted string, found {t.show}"

def natLit : P Nat := do
  match ← next with
  | .num n => pure n
  | t => fail s!"expected a number, found {t.show}"

def numAtom : P NumE := do
  match ← next with
  | .num n => pure (.lit n)
  | .ident s => pure (.param s)
  | t => fail s!"expected a number or parameter name, found {t.show}"

def numRest : Nat → NumE → P NumE
  | 0, a => pure a
  | fuel+1, a => do
    if ← isSym "+" then
      expectSym "+"
      let b ← numAtom
      numRest fuel (.add a b)
    else pure a

/-- `<num>`: atoms joined by `+`, left-associative. -/
def num : P NumE := do
  let a ← numAtom
  numRest 1000 a

/-- `name` or `name(role)`. -/
def factRef : P FactRef := do
  let n ← ident
  if ← isSym "(" then
    expectSym "("
    let a ← ident
    expectSym ")"
    pure ⟨n, some a⟩
  else pure ⟨n, none⟩

/-- Comma-separated list, with explicit fuel. -/
def sepByComma {α : Type} (p : P α) : Nat → P (List α)
  | 0 => fail "list too long"
  | fuel+1 => do
    let x ← p
    if ← isSym "," then
      expectSym ","
      let xs ← sepByComma p fuel
      pure (x :: xs)
    else pure [x]

def idents : P (List String) := sepByComma ident 100000
def factRefs : P (List FactRef) := sepByComma factRef 100000

def register : P Register := do
  match ← next with
  | .ident "norm" => pure .norm
  | .ident "definition" => pure .definition
  | .ident "invariant" => pure .invariant
  | .ident "acceptance" => pure .acceptance
  | .ident "commentary" => pure .commentary
  | t => fail s!"expected a register, found {t.show}"

def isRegisterKw : P Bool := fun ts =>
  .ok (match ts with
    | .ident k :: _ => ["norm", "definition", "invariant", "acceptance", "commentary"].contains k
    | _ => false, ts)

/-- Remaining `, role: fact(role)` pairs of an explicit `tagged` list. -/
def taggedRest : Nat → P (List (String × FactRef))
  | 0 => pure []
  | fuel+1 => do
    if ← isSym "," then
      expectSym ","
      let r ← ident
      expectSym ":"
      let g ← factRef
      let more ← taggedRest fuel
      pure ((r, g) :: more)
    else pure []

/-- `<who>`. -/
def who : P WhoE := do
  match ← next with
  | .ident "anyone" => pure .anyone
  | .ident "only" => .only <$> idents
  | .ident "except" => .except <$> idents
  | .ident "tagged" => do
    let n ← ident
    if ← isSym ":" then
      expectSym ":"
      let f ← factRef
      let more ← taggedRest 100000
      pure (.tagged ((n, f) :: more))
    else pure (.taggedAll n)
  | t => fail s!"expected anyone / only / except / tagged, found {t.show}"

mutual
  /-- `<cond>` with `or` at the top. -/
  def cond : Nat → P CondE
    | 0 => fail "condition too deep"
    | fuel+1 => do
      let a ← condAnd fuel
      condOrRest fuel a
  def condOrRest : Nat → CondE → P CondE
    | 0, a => pure a
    | fuel+1, a => do
      if ← isKw "or" then
        expectKw "or"
        let b ← condAnd fuel
        condOrRest fuel (.or a b)
      else pure a
  def condAnd : Nat → P CondE
    | 0 => fail "condition too deep"
    | fuel+1 => do
      let a ← condUnary fuel
      condAndRest fuel a
  def condAndRest : Nat → CondE → P CondE
    | 0, a => pure a
    | fuel+1, a => do
      if ← isKw "and" then
        expectKw "and"
        let b ← condUnary fuel
        condAndRest fuel (.and a b)
      else pure a
  def condUnary : Nat → P CondE
    | 0 => fail "condition too deep"
    | fuel+1 => do
      if ← isKw "not" then
        expectKw "not"
        .not <$> condUnary fuel
      else condAtom fuel
  def condAtom : Nat → P CondE
    | 0 => fail "condition too deep"
    | fuel+1 => do
      match ← next with
      | .sym "(" => do
        let c ← cond fuel
        expectSym ")"
        pure c
      | .ident "true" => pure .tt
      | .ident "false" => pure .ff
      | .ident "holds" => .holds <$> factRef
      | .ident "heldFor" => do let f ← factRef; let d ← num; pure (.heldFor f d)
      | .ident "countGe" => do let f ← factRef; let n ← num; pure (.countGe f n)
      | .ident "countAtLeast" => do let f ← factRef; let g ← factRef; pure (.countAtLeast f g)
      | t => fail s!"expected a condition, found {t.show}"
end

mutual
  def conduct : Nat → P ConductE
    | 0 => fail "conduct too deep"
    | fuel+1 => do
      let a ← conductAnd fuel
      conductOrRest fuel a
  def conductOrRest : Nat → ConductE → P ConductE
    | 0, a => pure a
    | fuel+1, a => do
      if ← isKw "or" then
        expectKw "or"
        let b ← conductAnd fuel
        conductOrRest fuel (.or a b)
      else pure a
  def conductAnd : Nat → P ConductE
    | 0 => fail "conduct too deep"
    | fuel+1 => do
      let a ← conductUnary fuel
      conductAndRest fuel a
  def conductAndRest : Nat → ConductE → P ConductE
    | 0, a => pure a
    | fuel+1, a => do
      if ← isKw "and" then
        expectKw "and"
        let b ← conductUnary fuel
        conductAndRest fuel (.and a b)
      else pure a
  def conductUnary : Nat → P ConductE
    | 0 => fail "conduct too deep"
    | fuel+1 => do
      if ← isKw "not" then
        expectKw "not"
        .not <$> conductUnary fuel
      else conductAtom fuel
  def conductAtom : Nat → P ConductE
    | 0 => fail "conduct too deep"
    | fuel+1 => do
      match ← next with
      | .sym "(" => do
        let c ← conduct fuel
        expectSym ")"
        pure c
      | .ident "act" => .act <$> ident
      | .ident "anyOf" => .anyOf <$> idents
      | .ident "exerciseOf" => .exerciseOf <$> ident
      | t => fail s!"expected act / anyOf / exerciseOf, found {t.show}"
end

def parseCond : P CondE := fun ts => cond (8 * ts.length + 16) ts
def parseConduct : P ConductE := fun ts => conduct (8 * ts.length + 16) ts

/-- `from <clause> [<register>] "<text>" [meaning <ids> | meaning none]`. -/
def sourceField : P SourceE := do
  let c ← ident
  let reg ← if ← isRegisterKw then register else pure .norm
  let txt ← strLit
  let meaning ← if ← isKw "meaning" then do
      expectKw "meaning"
      if ← isKw "none" then do expectKw "none"; pure (some [])
      else some <$> idents
    else pure none
  pure { clause := c, text := txt, register := reg, meaning := meaning }

/-- Optional `=> ids` suffix of a clause span. -/
def meaningSuffix : P (List String) := do
  if ← isSym "=>" then
    expectSym "=>"
    idents
  else pure []

def optionalApproved : P (Option Nat) := do
  if ← isKw "approved" then
    expectKw "approved"
    some <$> natLit
  else pure none

/-- `name = value` parameter binding. -/
def paramBinding : P (String × Nat) := do
  let n ← ident
  expectSym "="
  let v ← natLit
  pure (n, v)

def moduleArg : P (String × NumE) := do
  let n ← ident
  expectSym "="
  let v ← num
  pure (n, v)

/-- Run a line parser and require it to consume the whole line. -/
def runLine {α : Type} (p : P α) (l : Line) : Except String α :=
  match p l.toks with
  | .error e => .error s!"line {l.line}: {e}"
  | .ok (x, []) => .ok x
  | .ok (_, t :: _) => .error s!"line {l.line}: unexpected {t.show}"

/-- A field line: its keyword and the rest. -/
def fieldKw (l : Line) : Except String (String × Line) :=
  match l.toks with
  | .ident k :: rest => .ok (k, { l with toks := rest })
  | _ => .error s!"line {l.line}: expected a field keyword"

/-! ## 5. Declaration Parsers -/

def parseClause (b : Block) : Except String ClauseE := do
  let (cid, approved) ← runLine (do expectKw "clause"; let c ← ident; let a ← optionalApproved; pure (c, a)) b.header
  let mut cl : ClauseE := { id := cid, approved := approved }
  for l in b.fields do
    let (k, rest) ← fieldKw l
    match k with
    | "text" => cl := { cl with text := some (← runLine strLit rest) }
    | "norm" | "definition" | "invariant" | "acceptance" | "commentary" => do
      let (txt, m) ← runLine (do let t ← strLit; let m ← meaningSuffix; pure (t, m)) rest
      let reg : Register := match k with
        | "norm" => .norm | "definition" => .definition | "invariant" => .invariant
        | "acceptance" => .acceptance | _ => .commentary
      cl := { cl with spans := cl.spans ++ [{ register := reg, text := txt, meaning := m }] }
    | other => throw s!"line {l.line}: unknown clause field '{other}'"
  pure cl

def parseDuty (b : Block) : Except String DutyE := do
  let did ← runLine (do expectKw "duty"; ident) b.header
  let mut d : DutyE := { id := did }
  let mut demandSeen := false
  for l in b.fields do
    let (k, rest) ← fieldKw l
    match k with
    | "from" => d := { d with source := ← runLine sourceField rest }
    | "bearer" => d := { d with bearer := ← runLine who rest }
    | "beneficiary" => d := { d with beneficiary := ← runLine who rest }
    | "active" => d := { d with active := ← runLine parseCond rest }
    | "forbid" => do
      d := { d with demand := .forbid (← runLine parseConduct rest) }
      demandSeen := true
    | "require" => do
      let (c, w) ← runLine (do let c ← parseConduct; expectKw "within"; let w ← num; pure (c, w)) rest
      d := { d with demand := .require c w }
      demandSeen := true
    | "except" =>
      match rest.toks with
      | .ident "when" :: more => d := { d with unlessCond := ← runLine parseCond { rest with toks := more } }
      | .ident "by" :: .ident "power" :: more => d := { d with unlessPower := ← runLine idents { rest with toks := more } }
      | _ => throw s!"line {l.line}: expected 'except when <cond>' or 'except by power <ids>'"
    | "overridden" => d := { d with overriddenBy := ← runLine (do expectKw "by"; idents) rest }
    | "breach" => d := { d with breachBy := some (← runLine (do expectKw "by"; ident) rest) }
    | "remedies" => d := { d with remedies := ← runLine factRefs rest }
    | other => throw s!"line {l.line}: unknown duty field '{other}'"
  if d.source.clause.isEmpty then throw s!"line {b.header.line}: duty {did} has no 'from' clause"
  if !demandSeen then throw s!"line {b.header.line}: duty {did} has no 'forbid' or 'require'"
  pure d

def parsePower (b : Block) : Except String PowerE := do
  let pid ← runLine (do expectKw "power"; ident) b.header
  let mut p : PowerE := { id := pid }
  let mut triggerSeen := false
  for l in b.fields do
    let (k, rest) ← fieldKw l
    match k with
    | "from" => p := { p with source := ← runLine sourceField rest }
    | "holder" => p := { p with holder := ← runLine who rest }
    | "trigger" => do
      p := { p with trigger := ← runLine parseConduct rest }
      triggerSeen := true
    | "valid" => p := { p with valid := ← runLine parseCond rest }
    | "adds" => do
      -- `adds f for n` | `adds f to role` | `adds f if cond` | `adds f, g`
      let parsed ← runLine (do
        let fs ← factRefs
        if ← isKw "for" then do
          expectKw "for"; let n ← num
          pure (Sum.inl (Sum.inl (fs, n)))
        else if ← isKw "to" then do
          expectKw "to"; let r ← ident
          pure (Sum.inl (Sum.inr (fs, r)))
        else if ← isKw "if" then do
          expectKw "if"; let c ← parseCond
          pure (Sum.inr (Sum.inl (fs, c)))
        else pure (Sum.inr (Sum.inr fs))) rest
      match parsed with
      | .inl (.inl (fs, n)) => p := { p with addsFor := p.addsFor ++ fs.map (·, n) }
      | .inl (.inr (fs, r)) => p := { p with addsByActor := p.addsByActor ++ fs.map (r, ·) }
      | .inr (.inl (fs, c)) => p := { p with condAdds := p.condAdds ++ fs.map (c, ·) }
      | .inr (.inr fs) => p := { p with adds := p.adds ++ fs }
    | "removes" => p := { p with removes := p.removes ++ (← runLine factRefs rest) }
    | "establishes" =>
      p := { p with establishesBreachOf := some (← runLine (do expectKw "breach"; expectKw "of"; ident) rest) }
    | other => throw s!"line {l.line}: unknown power field '{other}'"
  if p.source.clause.isEmpty then throw s!"line {b.header.line}: power {pid} has no 'from' clause"
  if !triggerSeen then throw s!"line {b.header.line}: power {pid} has no 'trigger'"
  pure p

def parseImmunity (b : Block) : Except String ImmunityE := do
  let iid ← runLine (do expectKw "immunity"; ident) b.header
  let mut i : ImmunityE := { id := iid }
  for l in b.fields do
    let (k, rest) ← fieldKw l
    match k with
    | "from" => i := { i with source := ← runLine sourceField rest }
    | "holder" => i := { i with holder := ← runLine who rest }
    | "against" => i := { i with against := ← runLine idents rest }
    | "active" => i := { i with active := ← runLine parseCond rest }
    | "except" =>
      match rest.toks with
      | .ident "when" :: more => i := { i with unlessCond := ← runLine parseCond { rest with toks := more } }
      | _ => throw s!"line {l.line}: expected 'except when <cond>'"
    | other => throw s!"line {l.line}: unknown immunity field '{other}'"
  if i.source.clause.isEmpty then throw s!"line {b.header.line}: immunity {iid} has no 'from' clause"
  pure i

def noFields (b : Block) : Except String Unit :=
  match b.fields with
  | [] => .ok ()
  | l :: _ => .error s!"line {l.line}: unexpected continuation line"

def factDecl : P FactDecl := do
  let n ← ident
  if ← isSym "(" then
    expectSym "("
    expectKw "role"
    expectSym ")"
    pure ⟨n, true⟩
  else pure ⟨n, false⟩

def parseBlock (doc : Doc) (b : Block) : Except String Doc := do
  match b.header.toks with
  | .ident "charter" :: _ => do
    noFields b
    let (i, t) ← runLine (do expectKw "charter"; let i ← ident; let t ← strLit; pure (i, t)) b.header
    pure { doc with id := i, title := t }
  | .ident "document" :: _ => do
    noFields b
    pure { doc with document := some (← runLine (do expectKw "document"; strLit) b.header) }
  | .ident "contract" :: _ => do
    noFields b
    pure { doc with contract := some (← runLine (do expectKw "contract"; strLit) b.header) }
  | .ident "default" :: _ => do
    noFields b
    pure { doc with defaultActor := some (← runLine (do expectKw "default"; expectKw "actor"; ident) b.header) }
  | .ident "roles" :: _ => do
    noFields b
    pure { doc with roles := doc.roles ++ (← runLine (do expectKw "roles"; idents) b.header) }
  | .ident "acts" :: _ => do
    noFields b
    pure { doc with acts := doc.acts ++ (← runLine (do expectKw "acts"; idents) b.header) }
  | .ident "facts" :: _ => do
    noFields b
    pure { doc with facts := doc.facts ++ (← runLine (do expectKw "facts"; sepByComma factDecl 100000) b.header) }
  | .ident "params" :: _ => do
    let _ ← runLine (expectKw "params") b.header
    let ps ← b.fields.mapM (runLine paramBinding)
    pure { doc with params := doc.params ++ ps }
  | .ident "regime" :: _ => do
    let label ← runLine (do expectKw "regime"; strLit) b.header
    let ps ← b.fields.mapM (runLine paramBinding)
    pure { doc with regimes := doc.regimes ++ [⟨label, ps⟩] }
  | .ident "init" :: _ => do
    noFields b
    pure { doc with init := doc.init ++ (← runLine (do expectKw "init"; factRefs) b.header) }
  | .ident "use" :: _ => do
    noFields b
    let m ← runLine (do
      expectKw "use"; expectKw "module"
      let n ← ident
      let args ← if ← isKw "with" then do expectKw "with"; sepByComma moduleArg 100000 else pure []
      pure (⟨n, args⟩ : ModuleUse)) b.header
    pure { doc with modules := doc.modules ++ [m] }
  | .ident "clause" :: _ => do
    pure { doc with clauses := doc.clauses ++ [← parseClause b] }
  | .ident "duty" :: _ => do
    pure { doc with duties := doc.duties ++ [← parseDuty b] }
  | .ident "power" :: _ => do
    pure { doc with powers := doc.powers ++ [← parsePower b] }
  | .ident "immunity" :: _ => do
    pure { doc with immunities := doc.immunities ++ [← parseImmunity b] }
  | t :: _ => throw s!"line {b.header.line}: unknown declaration {t.show}"
  | [] => throw s!"line {b.header.line}: empty declaration"

/-- Parse a complete `.charter` text. -/
def parseCharterText (input : String) : Except String Doc := do
  let toks ← tokenize input
  let blocks ← groupBlocks (splitLines toks)
  let doc ← blocks.foldlM parseBlock {}
  if doc.id.isEmpty then throw "missing 'charter <id> \"<title>\"' declaration"
  pure doc

/-! ## 6. Static Validation -/

def Doc.factNames (d : Doc) : List String := d.facts.map (·.name)
def Doc.dutyIds (d : Doc) : List String := d.duties.map (·.id)
def Doc.powerIds (d : Doc) : List String := d.powers.map (·.id)
def Doc.immunityIds (d : Doc) : List String := d.immunities.map (·.id)
def Doc.clauseIds (d : Doc) : List String := d.clauses.map (·.id)
def Doc.paramNames (d : Doc) : List String := d.params.map (·.1)

def dupes (xs : List String) : List String :=
  (xs.filter fun x => (xs.filter (· == x)).length > 1).eraseDups

def checkFact (d : Doc) (ctx : String) (f : FactRef) : List String :=
  match d.facts.find? (·.name == f.name) with
  | none => [s!"{ctx}: undeclared fact '{f.name}'"]
  | some decl =>
    match decl.takesRole, f.arg with
    | true, none => [s!"{ctx}: fact '{f.name}' needs a role argument"]
    | false, some _ => [s!"{ctx}: fact '{f.name}' takes no argument"]
    | true, some r => if d.roles.contains r then [] else [s!"{ctx}: '{f.name}({r})' names an undeclared role"]
    | false, none => []

def checkRole (d : Doc) (ctx : String) (r : String) : List String :=
  if d.roles.contains r then [] else [s!"{ctx}: undeclared role '{r}'"]

def checkAct (d : Doc) (ctx : String) (a : String) : List String :=
  if d.acts.contains a then [] else [s!"{ctx}: undeclared act '{a}'"]

def checkNum (d : Doc) (ctx : String) : NumE → List String
  | .lit _ => []
  | .param p => if d.paramNames.contains p then [] else [s!"{ctx}: undeclared parameter '{p}'"]
  | .add a b => checkNum d ctx a ++ checkNum d ctx b

def checkWho (d : Doc) (ctx : String) : WhoE → List String
  | .anyone => []
  | .only xs => xs.flatMap (checkRole d ctx)
  | .except xs => xs.flatMap (checkRole d ctx)
  | .tagged ps => ps.flatMap fun (r, f) => checkRole d ctx r ++ checkFact d ctx f
  | .taggedAll f =>
    match d.facts.find? (·.name == f) with
    | some decl => if decl.takesRole then [] else [s!"{ctx}: 'tagged {f}' needs a fact taking a role argument"]
    | none => [s!"{ctx}: undeclared fact '{f}'"]

def checkCond (d : Doc) (ctx : String) : CondE → List String
  | .tt | .ff => []
  | .holds f => checkFact d ctx f
  | .heldFor f n => checkFact d ctx f ++ checkNum d ctx n
  | .countGe f n => checkFact d ctx f ++ checkNum d ctx n
  | .countAtLeast f g => checkFact d ctx f ++ checkFact d ctx g
  | .not c => checkCond d ctx c
  | .and a b | .or a b => checkCond d ctx a ++ checkCond d ctx b

def checkConduct (d : Doc) (ctx : String) : ConductE → List String
  | .act a => checkAct d ctx a
  | .anyOf as => as.flatMap (checkAct d ctx)
  | .exerciseOf p => if d.powerIds.contains p then [] else [s!"{ctx}: exerciseOf names unknown power '{p}'"]
  | .not c => checkConduct d ctx c
  | .and a b | .or a b => checkConduct d ctx a ++ checkConduct d ctx b

def checkSource (d : Doc) (ctx : String) (s : SourceE) : List String :=
  if d.clauseIds.contains s.clause then [] else [s!"{ctx}: 'from' names unknown clause '{s.clause}'"]

/-- All static errors of a document; empty when it is ready to be lowered. -/
def validate (d : Doc) : List String :=
  let dupRoles := (dupes d.roles).map (s!"duplicate role '{·}'")
  let dupActs := (dupes d.acts).map (s!"duplicate act '{·}'")
  let dupFacts := (dupes d.factNames).map (s!"duplicate fact '{·}'")
  let dupParams := (dupes d.paramNames).map (s!"duplicate parameter '{·}'")
  let dupClauses := (dupes d.clauseIds).map (s!"duplicate clause id '{·}'")
  let dupRules := (dupes (d.dutyIds ++ d.powerIds ++ d.immunityIds)).map (s!"duplicate rule id '{·}'")
  let initErrs := d.init.flatMap (checkFact d "init")
  let defActor := match d.defaultActor with | none => [] | some r => checkRole d "default actor" r
  let dutyErrs := d.duties.flatMap fun du =>
    let ctx := s!"duty {du.id}"
    checkSource d ctx du.source ++ checkWho d ctx du.bearer ++ checkWho d ctx du.beneficiary ++
    checkCond d ctx du.active ++
    (match du.demand with
      | .forbid c => checkConduct d ctx c
      | .require c w => checkConduct d ctx c ++ checkNum d ctx w) ++
    checkCond d ctx du.unlessCond ++
    du.unlessPower.flatMap (fun p => if d.powerIds.contains p then [] else [s!"{ctx}: 'except by power' names unknown power '{p}'"]) ++
    du.overriddenBy.flatMap (fun x => if d.dutyIds.contains x then [] else [s!"{ctx}: 'overridden by' names unknown duty '{x}'"]) ++
    (match du.breachBy with | none => [] | some p => if d.powerIds.contains p then [] else [s!"{ctx}: 'breach by' names unknown power '{p}'"]) ++
    du.remedies.flatMap (checkFact d ctx)
  let powerErrs := d.powers.flatMap fun p =>
    let ctx := s!"power {p.id}"
    checkSource d ctx p.source ++ checkWho d ctx p.holder ++ checkConduct d ctx p.trigger ++
    checkCond d ctx p.valid ++ p.adds.flatMap (checkFact d ctx) ++
    p.addsFor.flatMap (fun (f, n) => checkFact d ctx f ++ checkNum d ctx n) ++
    p.addsByActor.flatMap (fun (r, f) => checkRole d ctx r ++ checkFact d ctx f) ++
    p.removes.flatMap (checkFact d ctx) ++
    p.condAdds.flatMap (fun (c, f) => checkCond d ctx c ++ checkFact d ctx f) ++
    (match p.establishesBreachOf with | none => [] | some x => if d.dutyIds.contains x then [] else [s!"{ctx}: 'establishes breach of' names unknown duty '{x}'"])
  let immErrs := d.immunities.flatMap fun i =>
    let ctx := s!"immunity {i.id}"
    checkSource d ctx i.source ++ checkWho d ctx i.holder ++
    i.against.flatMap (fun p => if d.powerIds.contains p then [] else [s!"{ctx}: 'against' names unknown power '{p}'"]) ++
    checkCond d ctx i.active ++ checkCond d ctx i.unlessCond
  let regimeErrs := d.regimes.flatMap fun r =>
    r.params.flatMap fun (n, _) => if d.paramNames.contains n then [] else [s!"regime \"{r.label}\": undeclared parameter '{n}'"]
  let moduleErrs := d.modules.flatMap fun m => m.args.flatMap fun (_, v) => checkNum d s!"use module {m.name}" v
  dupRoles ++ dupActs ++ dupFacts ++ dupParams ++ dupClauses ++ dupRules ++ initErrs ++ defActor ++
    dutyErrs ++ powerErrs ++ immErrs ++ regimeErrs ++ moduleErrs

/-! ## 7. Printing -/

def quote (s : String) : String :=
  "\"" ++ (s.data.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n" else if c == '\t' then "\\t" else String.mk [c])) "") ++ "\""

def FactRef.render : FactRef → String
  | ⟨n, none⟩ => n
  | ⟨n, some a⟩ => s!"{n}({a})"

def NumE.render : NumE → String
  | .lit n => toString n
  | .param p => p
  | .add a b => NumE.render a ++ " + " ++ NumE.render b

def commaSep (xs : List String) : String := ", ".intercalate xs

def WhoE.render : WhoE → String
  | .anyone => "anyone"
  | .only xs => s!"only {commaSep xs}"
  | .except xs => s!"except {commaSep xs}"
  | .tagged ps => s!"tagged {commaSep (ps.map fun (r, f) => s!"{r}: {f.render}")}"
  | .taggedAll f => s!"tagged {f}"

def CondE.isAtom : CondE → Bool
  | .and _ _ | .or _ _ | .not _ => false
  | _ => true

/-- Render with every non-atomic operand parenthesized, so the tree is preserved
exactly on re-parse. -/
def CondE.render : CondE → String
  | .tt => "true"
  | .ff => "false"
  | .holds f => s!"holds {f.render}"
  | .heldFor f d => s!"heldFor {f.render} {d.render}"
  | .countGe f n => s!"countGe {f.render} {n.render}"
  | .countAtLeast f g => s!"countAtLeast {f.render} {g.render}"
  | .not c => "not " ++ (if c.isAtom then CondE.render c else "(" ++ CondE.render c ++ ")")
  | .and a b =>
    (if a.isAtom then CondE.render a else "(" ++ CondE.render a ++ ")") ++ " and " ++
    (if b.isAtom then CondE.render b else "(" ++ CondE.render b ++ ")")
  | .or a b =>
    (if a.isAtom then CondE.render a else "(" ++ CondE.render a ++ ")") ++ " or " ++
    (if b.isAtom then CondE.render b else "(" ++ CondE.render b ++ ")")

def ConductE.isAtom : ConductE → Bool
  | .and _ _ | .or _ _ | .not _ => false
  | _ => true

def ConductE.render : ConductE → String
  | .act a => s!"act {a}"
  | .anyOf as => s!"anyOf {commaSep as}"
  | .exerciseOf p => s!"exerciseOf {p}"
  | .not c => "not " ++ (if c.isAtom then ConductE.render c else "(" ++ ConductE.render c ++ ")")
  | .and a b =>
    (if a.isAtom then ConductE.render a else "(" ++ ConductE.render a ++ ")") ++ " and " ++
    (if b.isAtom then ConductE.render b else "(" ++ ConductE.render b ++ ")")
  | .or a b =>
    (if a.isAtom then ConductE.render a else "(" ++ ConductE.render a ++ ")") ++ " or " ++
    (if b.isAtom then ConductE.render b else "(" ++ ConductE.render b ++ ")")

def Register.kw : Register → String
  | .norm => "norm" | .definition => "definition" | .invariant => "invariant"
  | .acceptance => "acceptance" | .commentary => "commentary"

def SourceE.render (s : SourceE) : String :=
  let reg := if s.register == .norm then "" else s!" {Register.kw s.register}"
  let m := match s.meaning with
    | none => ""
    | some [] => " meaning none"
    | some ids => s!" meaning {commaSep ids}"
  s!"  from {s.clause}{reg} {quote s.text}{m}"

def ClauseE.render (c : ClauseE) : String :=
  let hdr := s!"clause {c.id}" ++ (match c.approved with | none => "" | some h => s!" approved {h}")
  let txt := match c.text with | none => [] | some t => [s!"  text {quote t}"]
  let spans := c.spans.map fun sp =>
    s!"  {Register.kw sp.register} {quote sp.text}" ++ (if sp.meaning.isEmpty then "" else s!" => {commaSep sp.meaning}")
  "\n".intercalate (hdr :: txt ++ spans)

def DutyE.render (d : DutyE) : String :=
  let demand := match d.demand with
    | .forbid c => s!"  forbid {c.render}"
    | .require c w => s!"  require {c.render} within {w.render}"
  let ls : List String :=
    [s!"duty {d.id}", d.source.render,
     s!"  bearer {d.bearer.render}", s!"  beneficiary {d.beneficiary.render}",
     s!"  active {d.active.render}", demand] ++
    (if d.unlessCond == .ff then [] else [s!"  except when {d.unlessCond.render}"]) ++
    (if d.unlessPower.isEmpty then [] else [s!"  except by power {commaSep d.unlessPower}"]) ++
    (if d.overriddenBy.isEmpty then [] else [s!"  overridden by {commaSep d.overriddenBy}"]) ++
    (match d.breachBy with | none => [] | some p => [s!"  breach by {p}"]) ++
    (if d.remedies.isEmpty then [] else [s!"  remedies {commaSep (d.remedies.map FactRef.render)}"])
  "\n".intercalate ls

def PowerE.render (p : PowerE) : String :=
  let ls : List String :=
    [s!"power {p.id}", p.source.render, s!"  holder {p.holder.render}", s!"  trigger {p.trigger.render}"] ++
    (if p.valid == .tt then [] else [s!"  valid {p.valid.render}"]) ++
    (if p.adds.isEmpty then [] else [s!"  adds {commaSep (p.adds.map FactRef.render)}"]) ++
    p.addsFor.map (fun (f, n) => s!"  adds {f.render} for {n.render}") ++
    p.addsByActor.map (fun (r, f) => s!"  adds {f.render} to {r}") ++
    (if p.removes.isEmpty then [] else [s!"  removes {commaSep (p.removes.map FactRef.render)}"]) ++
    p.condAdds.map (fun (c, f) => s!"  adds {f.render} if {c.render}") ++
    (match p.establishesBreachOf with | none => [] | some d => [s!"  establishes breach of {d}"])
  "\n".intercalate ls

def ImmunityE.render (i : ImmunityE) : String :=
  let ls : List String :=
    [s!"immunity {i.id}", i.source.render, s!"  holder {i.holder.render}",
     s!"  against {commaSep i.against}", s!"  active {i.active.render}"] ++
    (if i.unlessCond == .ff then [] else [s!"  except when {i.unlessCond.render}"])
  "\n".intercalate ls

def FactDecl.render : FactDecl → String
  | ⟨n, false⟩ => n
  | ⟨n, true⟩ => s!"{n}(role)"

/-- Print a document in `.charter` syntax. `render` and `parseCharterText` are
inverse on every document that `validate` accepts. -/
def render (d : Doc) : String :=
  let header : List String :=
    [s!"charter {d.id} {quote d.title}"] ++
    (match d.document with | none => [] | some p => [s!"document {quote p}"]) ++
    (match d.contract with | none => [] | some c => [s!"contract {quote c}"]) ++
    (match d.defaultActor with | none => [] | some a => [s!"default actor {a}"]) ++
    [""] ++
    [s!"roles {commaSep d.roles}", s!"acts {commaSep d.acts}", s!"facts {commaSep (d.facts.map FactDecl.render)}"] ++
    (if d.params.isEmpty then [] else "" :: "params" :: d.params.map (fun (n, v) => s!"  {n} = {v}")) ++
    (d.regimes.flatMap fun r => "" :: s!"regime {quote r.label}" :: r.params.map (fun (n, v) => s!"  {n} = {v}")) ++
    (if d.init.isEmpty then [] else ["", s!"init {commaSep (d.init.map FactRef.render)}"]) ++
    (if d.modules.isEmpty then [] else "" :: d.modules.map fun m =>
      s!"use module {m.name}" ++ (if m.args.isEmpty then "" else s!" with {commaSep (m.args.map fun (n, v) => s!"{n} = {v.render}")}"))
  let body := d.clauses.map ClauseE.render ++ d.duties.map DutyE.render ++
    d.powers.map PowerE.render ++ d.immunities.map ImmunityE.render
  "\n".intercalate header ++ "\n\n" ++ "\n\n".intercalate body ++ "\n"

end Charter.Dsl
