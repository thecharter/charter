import Charter.Surface.Diagnostics
import Charter.Core.Calendar

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
  | moneyLit (cents : Nat)
  | pctLit (bps : Nat)
  | dateLit (days : Int)
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
  | .moneyLit c => s!"money literal ({c} cents)"
  | .pctLit b => s!"rate literal ({b} bps)"
  | .dateLit d => s!"date literal ({d} days)"
  | .chr c => s!"character '{c}'"
  | .projDot => "`.`"
  | .eof => "end of input"
where
  showStringLit (s : String) : String := "\"" ++ s ++ "\""

namespace Lexer

/-- Multi-word and word keywords, longest first so that `Holds when` wins over `Holds`.
Single-word uppercase Charter additions (`Immunity`, `Clause`, `Document`, `Scenario`,
`From`, `Against`, `Unless`, `Duration`, `Held`, `Param`, `Module`, `Use`, `As`, `Approved`,
`Text`, `Norm`, `Definition`, `Acceptance`, `Commentary`) lex as `.atom` tokens and `tick`
lexes as `.ident "tick"`, matched contextually by `Parser` / `Resolve` (D17). -/
def wordKeywords : List String :=
  [ "Derived externally", "Conditioned by", "Forbidden when", "Identified by", "Terminated by", "Violated when", "Overridden by",
    "Present when", "Current Time", "Derived from", "Except under", "Excused when", "Qualifies as", "Rejects when", "Weighted by", "Enforced by", "Related to", "Syncs with",
    "Decided by", "Valid when", "Created by", "Due within", "Holds when", "On breach", "Raised by", "Void when", "At least", "First of", "Paid by",
    "Placeholder", "Obfuscates", "Terminates", "Identified", "Recipient", "Invariant", "Predicate",
    "Physical", "Claimant", "Function", "Violated", "Enabled", "Creates", "Current", "Derived",
    "Present", "Foreach", "Exists", "Forall", "Extend", "Closed", "Domain", "Holder", "String",
    "Actor", "Count", "Event", "False", "Force", "Holds", "Union", "Where", "Atom", "Bool",
    "Duty", "Fact", "Open", "Time", "True", "When", "With", "Act", "For", "Int", "Max", "Min",
    "Not", "Sum", "Var", "Do" ]

/-- The claim phrases. Each is a keyword only when followed by whitespace and a
non-terminator token, so `?valid(5)` and `?valid .` still query a fact named `valid` while
`?valid do(x)` is the claim (D17). -/
def claimKeywords : List String :=
  [ "?!undetermined", "?undetermined", "?!occurred", "?occurred", "?!conflict", "?conflict",
    "?!violated", "?!lawful", "?!valid", "?!late", "?violated", "?lawful", "?valid", "?late", "?why" ]

/-- Symbol keywords, longest first. -/
def symbolKeywords : List String :=
  [ "#include", "#require", "####", "###", "##", "?--", "?-", "!?", "||", "&&", "=>", "<=", ">=", "..",
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

def csNotTerminator (c : Char) : Bool := c != '.' && c != '}'

def step (s : St) : Except Diagnostic St := do
  let p := s.pos
  match s.peek with
  | none => return s.push .eof p
  | some c =>
    let claimKw (k : String) : Bool :=
      if startsWithAt s.cs s.i k && (match s.peek k.length with | some c' => c'.isWhitespace | none => false) then
        let j := takeWhileFrom s.cs (s.i + k.length) Char.isWhitespace
        if h : j < s.cs.size then csNotTerminator s.cs[j] else false
      else false
    match claimKeywords.find? claimKw with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    -- symbol keywords
    match symbolKeywords.find? (startsWithAt s.cs s.i) with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    -- word keywords at a boundary
    match wordKeywords.find? (fun k => startsWithAt s.cs s.i k && boundaryAt s.cs (s.i + k.length)) with
    | some k => return (s.advance k.length).push (.kw k) p
    | none =>
    if c == '"' then lexString s p
    else if c == '$' && (match s.peek 1 with | some d => d.isDigit | none => false) then
      -- `$400,000.00` or `$500` (`D37`, `#42`): exact USD cents
      let rec scanMoneyDigits (j : Nat) (acc : String) (fuel : Nat) : Nat × String :=
        match fuel with
        | 0 => (j, acc)
        | fuel + 1 =>
          if h : j < s.cs.size then
            let ch := s.cs[j]
            if ch.isDigit then scanMoneyDigits (j + 1) (acc.push ch) fuel
            else if (ch == ',' || ch == '_') && (if h2 : j + 1 < s.cs.size then s.cs[j + 1].isDigit else false) then
              scanMoneyDigits (j + 1) acc fuel
            else (j, acc)
          else (j, acc)
      let (j, wholeStr) := scanMoneyDigits (s.i + 1) "" (s.cs.size + 1)
      let whole := wholeStr.toNat!
      let hasDotDigit := (if h : j < s.cs.size then s.cs[j] == '.' else false)
                      && (if h2 : j + 1 < s.cs.size then s.cs[j + 1].isDigit else false)
      if hasDotDigit then
        let k := takeWhileFrom s.cs (j + 1) Char.isDigit
        let fracStr := sliceStr s.cs (j + 1) k
        if fracStr.length != 2 then
          throw (.error "CHR001" s!"`{sliceStr s.cs s.i k}` must have no fractional part or exactly 2 decimal digits (cents)" p)
        let cents := whole * 100 + fracStr.toNat!
        return (s.advance (k - s.i)).push (.moneyLit cents) p
      else
        return (s.advance (j - s.i)).push (.moneyLit (whole * 100)) p
    else if c.isDigit then
      let j := takeWhileFrom s.cs s.i Char.isDigit
      let n := (sliceStr s.cs s.i j).toNat!
      -- Check ISO date `YYYY-MM-DD` (`D38`, `#48`): 4-digit year, `-`, 2-digit month, `-`, 2-digit day
      let isoDate? : Option Int :=
        if j - s.i == 4 && s.i + 10 <= s.cs.size then
          let sep1 := if h1 : s.i + 4 < s.cs.size then s.cs[s.i + 4] == '-' else false
          let sep2 := if h2 : s.i + 7 < s.cs.size then s.cs[s.i + 7] == '-' else false
          let mOk := (if h3 : s.i + 5 < s.cs.size then s.cs[s.i + 5].isDigit else false)
                  && (if h4 : s.i + 6 < s.cs.size then s.cs[s.i + 6].isDigit else false)
          let dOk := (if h5 : s.i + 8 < s.cs.size then s.cs[s.i + 8].isDigit else false)
                  && (if h6 : s.i + 9 < s.cs.size then s.cs[s.i + 9].isDigit else false)
          let endBnd := boundaryAt s.cs (s.i + 10)
          if sep1 && sep2 && mOk && dOk && endBnd then
            let yr : Int := (sliceStr s.cs s.i (s.i + 4)).toNat!
            let mo : Int := (sliceStr s.cs (s.i + 5) (s.i + 7)).toNat!
            let dy : Int := (sliceStr s.cs (s.i + 8) (s.i + 10)).toNat!
            if Calendar.validYmd yr mo dy then some (Calendar.daysFromCivil yr mo dy)
            else none
          else none
        else none
      if let some epochDays := isoDate? then
        return (s.advance 10).push (.dateLit epochDays) p
      -- Check `6%` or `5.25%` (`D37`, `#58`): exact basis points (`1% = 100 bps`)
      let hasDotPct :=
        if (if h : j < s.cs.size then s.cs[j] == '.' else false)
           && (if h2 : j + 1 < s.cs.size then s.cs[j + 1].isDigit else false) then
          let k := takeWhileFrom s.cs (j + 1) Char.isDigit
          if (if h3 : k < s.cs.size then s.cs[k] == '%' else false)
             && (if h4 : k + 1 < s.cs.size then !s.cs[k + 1].isAlphanum else true) then
            some (k + 1, sliceStr s.cs (j + 1) k)
          else none
        else none
      match hasDotPct with
      | some (endIdx, fracS) =>
        if fracS.length == 1 then
          return (s.advance (endIdx - s.i)).push (.pctLit (n * 100 + fracS.toNat! * 10)) p
        else if fracS.length == 2 then
          return (s.advance (endIdx - s.i)).push (.pctLit (n * 100 + fracS.toNat!)) p
        else
          throw (.error "CHR001" s!"rate literal `{sliceStr s.cs s.i endIdx}` supports at most 2 decimal places (basis points)" p)
      | none =>
        let isPlainPct := (if h : j < s.cs.size then s.cs[j] == '%' else false)
                       && (if h2 : j + 1 < s.cs.size then !s.cs[j + 1].isAlphanum else true)
        if isPlainPct then
          return (s.advance (j + 1 - s.i)).push (.pctLit (n * 100)) p
        else
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
