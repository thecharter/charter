import Charter.Surface.Diagnostics

/-!
# Charter.Surface.Lexer — Tokens of the eFLINT core

The token classes and spellings of eFLINT 4.1 (`Parse.hs`, `lexer_settings`),
per D2:

- keywords, including the multi-word ones (`Holds when`, `Identified by`, …),
  matched longest first and only at a word boundary;
- symbol keywords `?--`, `?-`, `!?`, `||`, `&&`, `<=`, `>=`, `..`, `==`, `!=`
  and the single key characters `[ ] ( ) ! , ' + - * / . = > < : ? { } % ~`;
- identifiers: a lowercase word, continued by lowercase letters, `_`, or a `-`
  followed by a lowercase letter (`neighbour-of`, `cast_vote`); a digit ends the
  word, so `person1` is the identifier `person` followed by the integer `1`,
  which the parser reads as the decoration of a variable;
- atoms: a word starting with an uppercase letter (`Alice`, `A1`), used as
  string literals without quotes;
- integer literals (unsigned; `-1` is a subtraction), string literals in double
  quotes, and `//` line comments and `/* */` block comments.

One token is special to the deterministic parser: a `.` immediately preceded by
a non-space character and immediately followed by a lowercase letter or `(` is
a projection dot (`comp.string`); any other `.` is the phrase terminator. eFLINT's
generalised parser resolves the same ambiguity by trying both; this lexer decides
it once, and the corpus is the test.
-/

namespace Charter

inductive TokKind where
  /-- A keyword or symbol, by its spelling. -/
  | kw (s : String)
  | ident (s : String)
  | atom (s : String)
  | str (s : String)
  | int (n : Nat)
  | chr (c : Char)
  /-- A projection dot (see the module header). -/
  | projDot
  | eof
  deriving Repr, DecidableEq, Inhabited

structure Tok where
  kind : TokKind
  pos  : Pos
  deriving Repr, Inhabited

def TokKind.describe : TokKind → String
  | .kw s => s!"`{s}`"
  | .ident s => s!"identifier `{s}`"
  | .atom s => s!"atom `{s}`"
  | .str s => s!"string {showStringLit s}"
  | .int n => s!"integer {n}"
  | .chr c => s!"character '{c}'"
  | .projDot => "`.`"
  | .eof => "end of input"
where
  showStringLit (s : String) : String := "\"" ++ s ++ "\""

namespace Lexer

/-- Multi-word and word keywords, longest first so that `Holds when` wins over `Holds`. -/
def wordKeywords : List String :=
  [ "Derived externally", "Conditioned by", "Identified by", "Terminated by", "Violated when",
    "Present when", "Current Time", "Derived from", "Enforced by", "Related to", "Syncs with",
    "Created by", "Holds when",
    "Placeholder", "Obfuscates", "Terminates", "Identified", "Recipient", "Invariant", "Predicate",
    "Physical", "Claimant", "Function", "Violated", "Enabled", "Creates", "Current", "Derived",
    "Present", "Foreach", "Exists", "Forall", "Extend", "Closed", "Domain", "Holder", "String",
    "Actor", "Count", "Event", "False", "Force", "Holds", "Union", "Where", "Atom", "Bool",
    "Duty", "Fact", "Open", "Time", "True", "When", "With", "Act", "For", "Int", "Max", "Min",
    "Not", "Sum", "Var", "Do" ]

/-- Charter's additions to the keyword set (plan §2.2); not keywords in `--eflint` mode,
where they are atoms, as eFLINT reads them. -/
def charterWordKeywords : List String :=
  [ "Except under", "Valid when", "Due within", "Commentary", "Acceptance", "Definition",
    "Immunity", "Duration", "Scenario", "Approved", "Document", "Against", "Clause", "Unless",
    "Module", "Param", "Held", "Norm", "Text", "From", "Use", "As", "tick" ]

/-- The claim phrases. Each is a keyword only when followed by whitespace, so that
`?valid(5)` still queries a fact named `valid` and `?valid do(x)` is the claim. -/
def charterSymbolKeywords : List String :=
  [ "?!violated", "?!lawful", "?!valid", "?violated", "?lawful", "?valid", "?why" ]

/-- Charter symbols that need no whitespace after them. -/
def charterPlainSymbols : List String := [ "=>" ]

/-- Symbol keywords, longest first. -/
def symbolKeywords : List String :=
  [ "#include", "#require", "####", "###", "##", "?--", "?-", "!?", "||", "&&", "<=", ">=", "..",
    "==", "!=", "#" ]

def keyChars : List Char :=
  ['[', ']', '(', ')', '!', ',', '\'', '+', '-', '*', '/', '.', '=', '>', '<', ':', '?', '{', '}', '%', '~', '@']

def isLowerWordChar (c : Char) : Bool := c.isLower || c == '_'

def isAtomChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- A word boundary after a keyword: the next character may not continue a word. -/
def boundaryAt (cs : Array Char) (i : Nat) : Bool :=
  if h : i < cs.size then !(cs[i].isAlphanum || cs[i] == '_') else true

def startsWithAt (cs : Array Char) (i : Nat) (s : String) : Bool :=
  let ss := s.toList
  go ss i
where
  go : List Char → Nat → Bool
    | [], _ => true
    | c :: rest, j => if h : j < cs.size then cs[j] == c && go rest (j + 1) else false

structure St where
  cs   : Array Char
  i    : Nat := 0
  line : Nat := 1
  col  : Nat := 1
  toks : Array Tok := #[]
  /-- `false` in `--eflint` mode: only eFLINT's keywords. -/
  charter : Bool := true

def St.pos (s : St) : Pos := ⟨s.line, s.col⟩

def St.peek (s : St) (k : Nat := 0) : Option Char :=
  if h : s.i + k < s.cs.size then some s.cs[s.i + k] else none

def St.advance (s : St) (n : Nat := 1) : St :=
  let rec go (s : St) : Nat → St
    | 0 => s
    | k + 1 =>
      if h : s.i < s.cs.size then
        let c := s.cs[s.i]
        let s' := if c == '\n' then { s with i := s.i + 1, line := s.line + 1, col := 1 }
                  else { s with i := s.i + 1, col := s.col + 1 }
        go s' k
      else s
  go s n

def St.push (s : St) (k : TokKind) (p : Pos) : St := { s with toks := s.toks.push ⟨k, p⟩ }

/-- Skip whitespace and comments. -/
def skipTrivia (fuel : Nat) (s : St) : St :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    match s.peek with
    | some c =>
      if c.isWhitespace then skipTrivia fuel (s.advance)
      else if c == '/' && s.peek 1 == some '/' then
        skipTrivia fuel (skipLine s)
      else if c == '/' && s.peek 1 == some '*' then
        skipTrivia fuel (skipBlock (s.cs.size + 1) (s.advance 2))
      else s
    | none => s
where
  skipLine (s : St) : St :=
    let rec go (s : St) : Nat → St
      | 0 => s
      | k + 1 => match s.peek with
        | some '\n' => s
        | some _ => go s.advance k
        | none => s
    go s (s.cs.size + 1)
  skipBlock : Nat → St → St
    | 0, s => s
    | k + 1, s => match s.peek with
      | some '*' => if s.peek 1 == some '/' then s.advance 2 else skipBlock k s.advance
      | some _ => skipBlock k s.advance
      | none => s

def takeWhileFrom (cs : Array Char) (i : Nat) (p : Char → Bool) : Nat :=
  let rec go (j : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => j
    | fuel + 1 => if h : j < cs.size then (if p cs[j] then go (j + 1) fuel else j) else j
  go i (cs.size + 1)

def sliceStr (cs : Array Char) (i j : Nat) : String :=
  String.mk ((cs.extract i j).toList)

/-- An identifier: a lowercase word, continued by lowercase/underscore or `-` + lowercase;
further words joined by spaces continue it (eFLINT `types`: `other candidate` is one
identifier), which is unambiguous because no construct juxtaposes two identifiers. -/
def identEnd (cs : Array Char) (i : Nat) : Nat :=
  let rec go (j : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => j
    | fuel + 1 =>
      if h : j < cs.size then
        let c := cs[j]
        if isLowerWordChar c then go (j + 1) fuel
        else if c == '-' then
          (if h2 : j + 1 < cs.size then (if cs[j + 1].isLower then go (j + 2) fuel else j) else j)
        else if c == ' ' then
          let k := takeWhileFrom cs j (· == ' ')
          (if h2 : k < cs.size then (if cs[k].isLower then go (k + 1) fuel else j) else j)
        else j
      else j
  go i (cs.size + 1)

/-- `[name]`: eFLINT's bracketed identifier, any text but `]`, `>`, `+`, `=` on one line. -/
def bracketIdentEnd (cs : Array Char) (i : Nat) : Option Nat :=
  let j := takeWhileFrom cs (i + 1) (fun c => c != ']' && c != '>' && c != '+' && c != '=' && c != '\n')
  if h : j < cs.size then (if cs[j] == ']' then some (j + 1) else none) else none

def lexString (s : St) (p : Pos) : Except Diagnostic St :=
  let rec go (s : St) (acc : String) : Nat → Except Diagnostic St
    | 0 => .error (.error "CHR002" "unterminated string literal" p)
    | k + 1 => match s.peek with
      | none => .error (.error "CHR002" "unterminated string literal" p)
      | some '"' => .ok ((s.advance).push (.str acc) p)
      | some '\\' => match s.peek 1 with
        | some 'n' => go (s.advance 2) (acc.push '\n') k
        | some 't' => go (s.advance 2) (acc.push '\t') k
        | some c => go (s.advance 2) (acc.push c) k
        | none => .error (.error "CHR002" "unterminated string literal" p)
      | some c => go s.advance (acc.push c) k
  go (s.advance) "" (s.cs.size + 1)

def step (s : St) : Except Diagnostic St := do
  let p := s.pos
  match s.peek with
  | none => return s.push .eof p
  | some c =>
    let claimKw (k : String) : Bool :=
      startsWithAt s.cs s.i k && (match s.peek k.length with | some c' => c'.isWhitespace | none => false)
    let claim := if s.charter then charterSymbolKeywords.find? claimKw else none
    match claim with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    let symbols := if s.charter then charterPlainSymbols ++ symbolKeywords else symbolKeywords
    let words := if s.charter then charterWordKeywords ++ wordKeywords else wordKeywords
    -- symbol keywords
    match symbols.find? (startsWithAt s.cs s.i) with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    -- word keywords at a boundary
    match words.find? (fun k => startsWithAt s.cs s.i k && boundaryAt s.cs (s.i + k.length)) with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    if c == '"' then lexString s p
    else if c.isDigit then
      let j := takeWhileFrom s.cs s.i Char.isDigit
      let n := (sliceStr s.cs s.i j).toNat!
      return (s.advance (j - s.i)).push (.int n) p
    else if c.isLower then
      let j := identEnd s.cs s.i
      return (s.advance (j - s.i)).push (.ident (sliceStr s.cs s.i j)) p
    else if c == '[' then
      match bracketIdentEnd s.cs s.i with
      | some j => return (s.advance (j - s.i)).push (.ident (sliceStr s.cs s.i j)) p
      | none => return (s.advance).push (.kw "[") p
    else if c.isUpper then
      let j := takeWhileFrom s.cs s.i isAtomChar
      return (s.advance (j - s.i)).push (.atom (sliceStr s.cs s.i j)) p
    else if c == '\'' && (match s.peek 1 with | some ch => ch.isAlphanum | none => false) && s.peek 2 == some '\'' then
      -- a character literal `'a'` (only in ranges); a run of primes is decoration
      match s.peek 1 with
      | some ch => return (s.advance 3).push (.chr ch) p
      | none => return (s.advance).push (.kw "'") p
    else if c == '.' then
      -- projection dot: glued to the left, and a lowercase letter or `(` to the right
      let leftGlued := s.i > 0 && (if h : s.i - 1 < s.cs.size then !(s.cs[s.i - 1].isWhitespace) else false)
      let rightOk := match s.peek 1 with
        | some c' => c'.isLower || c' == '(' || c' == '['
        | none => false
      if leftGlued && rightOk then return (s.advance).push .projDot p
      else return (s.advance).push (.kw ".") p
    else if keyChars.contains c then
      return (s.advance).push (.kw c.toString) p
    else
      throw (.error "CHR001" s!"unexpected character `{c}`" p)

def run (fuel : Nat) (s : St) : Except Diagnostic (Array Tok) :=
  match fuel with
  | 0 => .error (.error "CHR001" "input too long to tokenize" s.pos)
  | fuel + 1 => do
    let s := skipTrivia (s.cs.size + 1) s
    let s' ← step s
    match s'.toks.back? with
    | some ⟨.eof, _⟩ => return s'.toks
    | _ => run fuel s'

end Lexer

/-- Tokenize a source text; `eflint` restricts the keywords to eFLINT's. -/
def tokenize (src : String) (eflint : Bool := false) : Except Diagnostic (Array Tok) :=
  let cs := src.toList.toArray
  Lexer.run (cs.size + 2) { cs, charter := !eflint }

end Charter
