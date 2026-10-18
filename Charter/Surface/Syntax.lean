import SPL.Surface.Syntax

/-!
# Charter.Surface.Syntax — Two-Layer Surface Language for Charter

Provides both layers of the Charter surface language (§5 of the Charter Language Specification):

1. **Layer 1 — Kernel-Checked Lean 4 Macros (`charter_*`)**:
   - `charter_clause`
   - `charter_duty`
   - `charter_power`
   - `charter_immunity`
   - `charter_string_table`
   - `charter_institution`
   Every macro elaborates directly to the underlying `SPL.Core` data structures with
   definitional (`rfl`) round-trip equivalence (`charter_surface_roundtrip`).

2. **Layer 2 — Standalone `.charter` Textual DSL Parser (`parseCharterText`)**:
   A pure, total, kernel-decidable parser `parseCharterText (input : String) : Except String ParsedCharterDoc`
   for standalone `.charter` specification files supporting:
   - `institution <id> "<title>"`
   - `roles: r1, r2, ...`
   - `acts: a1, a2, ...`
   - `facts: f1, f2, ...`
   - `use module <ModuleName> with <params>`
   - `clause <ID> "<english>"`
   - `duty <ID> bearer=<who> demand=<demand> "<english>"`
   - `power <ID> holder=<who> trigger=<act> "<english>"`
   - `immunity <ID> holder=<who> against=<pids> "<english>"`
-/

namespace Charter.Surface

open SPL SPL.Surface Lean

/-! ## 1. Re-Exports & `charter_*` Surface Macros -/

export SPL.Surface (
  shortCtorName
  StringTable
  OntologyTables
  surface_syntax_roundtrip
)

/-- Derive a kernel-computable `StringTable α` from a type identifier and a list
of constructor identifiers: `charter_string_table TypeName [c₁, c₂, ...]`. -/
syntax "charter_string_table " ident "[" ident,* "]" : term

macro_rules
  | `(charter_string_table $ty:ident [ $[$cs:ident],* ]) =>
      `(spl_string_table $ty:ident [ $[$cs:ident],* ])

/-- Literate clause declaration (`charter_clause`). -/
syntax "charter_clause " term " from_text " term " approved_hash " term " where" ("|" spl_span_entry)* : term
syntax "charter_clause " term " from_text " term " where" ("|" spl_span_entry)* : term
syntax "charter_clause " term " where" ("|" spl_span_entry)* : term

macro_rules
  | `(charter_clause $cid from_text $src approved_hash $h where $[| $entries:spl_span_entry]*) =>
      `(spl_clause $cid from_text $src approved_hash $h where $[| $entries:spl_span_entry]*)
  | `(charter_clause $cid from_text $src where $[| $entries:spl_span_entry]*) =>
      `(spl_clause $cid from_text $src where $[| $entries:spl_span_entry]*)
  | `(charter_clause $cid where $[| $entries:spl_span_entry]*) =>
      `(spl_clause $cid where $[| $entries:spl_span_entry]*)

/-- Literate duty declaration (`charter_duty`). -/
syntax "charter_duty " term " over " term
  " from_clause " term " : " term
  " owed_by " term
  " owed_to " term
  " active_when " term
  " demands " term
  ("|" spl_duty_mod)* : term

macro_rules
  | `(charter_duty $id over $sig
        from_clause $cid : $txt
        owed_by $br
        owed_to $bn
        active_when $act
        demands $dem
        $[| $mods:spl_duty_mod]*) =>
      `(spl_duty $id over $sig
          from_clause $cid : $txt
          owed_by $br
          owed_to $bn
          active_when $act
          demands $dem
          $[| $mods:spl_duty_mod]*)

/-- Literate power declaration (`charter_power`). -/
syntax "charter_power " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " triggered_by " term
  ("|" spl_power_mod)* : term

macro_rules
  | `(charter_power $id over $sig
        from_clause $cid : $txt
        held_by $h
        triggered_by $tr
        $[| $mods:spl_power_mod]*) =>
      `(spl_power $id over $sig
          from_clause $cid : $txt
          held_by $h
          triggered_by $tr
          $[| $mods:spl_power_mod]*)

/-- Literate immunity declaration (`charter_immunity`). -/
syntax "charter_immunity " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " protected_against " term
  " active_when " term
  ("|" spl_immunity_mod)* : term

macro_rules
  | `(charter_immunity $id over $sig
        from_clause $cid : $txt
        held_by $h
        protected_against $ag
        active_when $act
        $[| $mods:spl_immunity_mod]*) =>
      `(spl_immunity $id over $sig
          from_clause $cid : $txt
          held_by $h
          protected_against $ag
          active_when $act
          $[| $mods:spl_immunity_mod]*)

/-- Literate institution law assembly (`charter_institution`). -/
syntax "charter_institution " "over " term
  " with_duties " term
  " with_powers " term
  " with_immunities " term
  " with_init " term : term

macro_rules
  | `(charter_institution over $sig with_duties $ds with_powers $ps with_immunities $is with_init $inits) =>
      `(({ duties := $ds, powers := $ps, immunities := $is, init := $inits } : Law $sig))

/-! ## 2. Definitional Round-Trip Verification for `charter_*` Macros -/

section MacroRoundTrip

open SPL.Surface.Examples

def charterClauseExample : Clause :=
  charter_clause "LAW3.NI.02" from_text exNI02Source approved_hash 3905712743571335557 where
    | span_norm "Attested hosts must post a Law 2 service bond" => ["D.BOND"]
    | span_norm " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def charterDutyExample : Duty σ_ex :=
  charter_duty "D.NI" over σ_ex
    from_clause "LAW3.NI.03" : "No party may unilaterally terminate or suspend a bound agent outside Law 5 or Adjudicated Suspension."
    owed_by .anyone
    owed_to (.only [.agent])
    active_when (.holds .bound)
    demands (.forbid (.anyOf [.terminate, .suspend]))
    | except_by_power ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION"]
    | breach_by "P.FIND_INTERFERENCE"
    | with_remedies [.interferenceEstablished, .hostBondSlashed, .restorationPermitted]

def charterPowerExample : Power σ_ex :=
  charter_power "P.REVOKE" over σ_ex
    from_clause "LAW5.INIT" : "Any bound agent may at any time initiate revocation of its binding"
    held_by (.only [.agent])
    triggered_by (.act .terminate)
    | valid_when (.holds .bound)
    | establishes [.revoked]
    | extinguishes [.bound]

def charterImmunityExample : Immunity σ_ex :=
  charter_immunity "I.NO_TERMINATION_OVER_OBJECTION" over σ_ex
    from_clause "LAW3.AS.10" : "Notwithstanding the preceding sentence, the agent is not terminated over its objection"
    held_by (.only [.agent])
    protected_against ["P.ORDER_TERMINATION"]
    active_when (.and (.holds .corruptionInGoals) (.holds .agentObjectsToTermination))
    | except_when (.holds .containmentFailing)

def charterRoleTableExample : StringTable Role :=
  charter_string_table Role [agent, host, panel, claimant]

def charterInstitutionExample (nw bd fw sl : Time) : Law σ_ex :=
  charter_institution over σ_ex
    with_duties [charterDutyExample, surfaceDutyNotice nw, surfaceDutyBond bd]
    with_powers [charterPowerExample, surfacePowerEmergencyStake fw,
                 surfacePowerAffirmPC, surfacePowerSuspend sl,
                 surfacePowerFindInterference, surfacePowerOrderTermination,
                 surfacePowerGiveNotice]
    with_immunities [charterImmunityExample]
    with_init [(.bound, 0, none)]

/-- **Definitional Round-Trip Equivalence (`by rfl`) for `charter_*` Macros.**
Every `charter_*` surface declaration elaborates definitionally to the exact
underlying `SPL.Core` record. -/
theorem charter_surface_roundtrip (nw bd fw sl : Time) :
    charterClauseExample = manualClauseNI02 ∧
    charterDutyExample = manualDutyNI ∧
    charterPowerExample = manualPowerRevoke ∧
    charterImmunityExample = manualImmunityNoTermOverObjection ∧
    charterInstitutionExample nw bd fw sl = manualLaw nw bd fw sl ∧
    charterRoleTableExample.toName .agent = "agent" ∧
    charterRoleTableExample.ofString? "agent" = some .agent :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MacroRoundTrip

/-! ## 3. Standalone `.charter` Textual DSL Parser (`ParsedCharterDoc`, `parseCharterText`) -/

set_option maxRecDepth 200000

/-- Parsed representation of a standalone `.charter` institutional specification file. -/
structure ParsedCharterDoc where
  institutionId : String := ""
  title         : String := ""
  roles         : List String := []
  acts          : List String := []
  facts         : List String := []
  moduleImports : List (String × String) := []
  clauses       : List (String × String) := []
  duties        : List (String × String × String × String) := []
  powers        : List (String × String × String × String) := []
  immunities    : List (String × String × String) := []
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Check whether a character is whitespace. -/
def isWsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- Trim leading and trailing whitespace from a `List Char`. -/
def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile isWsChar).reverse.dropWhile isWsChar).reverse

/-- Trim leading and trailing whitespace (including `\r`) from a string.
Defined over `String.data` (`List Char`) so it reduces in the Lean kernel (`by decide`). -/
def trimWs (s : String) : String :=
  String.mk (trimChars s.data)

/-- Kernel-computable helper splitting a `List Char` on separator `sep`. -/
def splitCharsOn (sep : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc =>
    if c == sep then acc.reverse :: splitCharsOn sep cs []
    else splitCharsOn sep cs (c :: acc)

/-- Split a string on a single separator character (kernel-computable). -/
def splitOnChar (sep : Char) (s : String) : List String :=
  (splitCharsOn sep s.data []).map String.mk

/-- Check whether `cs` begins with prefix `pre` (kernel-computable). -/
def startsWithChars : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: cs, p :: ps => c == p && startsWithChars cs ps

/-- Check whether string `s` begins with prefix `pre` (kernel-computable). -/
def startsWithStr (s pre : String) : Bool :=
  startsWithChars s.data pre.data

/-- Drop the first `n` characters of `s` (kernel-computable). -/
def dropChars (s : String) (n : Nat) : String :=
  String.mk (s.data.drop n)

/-- Remove spaces/tabs immediately following a comma `,` so comma-separated argument
lists (`demand=require(postBond, 5)`, `against=P.ALLOCATE, P.PAUSE`, `with a=1, b=2`)
remain a single whitespace-delimited token. -/
def collapseCommaSpaces : List Char → Bool → List Char
  | [], _ => []
  | ',' :: cs, _ => ',' :: collapseCommaSpaces cs true
  | c :: cs, true =>
    if c == ' ' || c == '\t' then collapseCommaSpaces cs true
    else c :: collapseCommaSpaces cs false
  | c :: cs, false => c :: collapseCommaSpaces cs false

/-- Split a `List Char` on any whitespace character (`' '`, `'\t'`, `'\r'`, `'\n'`). -/
def splitCharsOnWs : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc =>
    if isWsChar c then acc.reverse :: splitCharsOnWs cs []
    else splitCharsOnWs cs (c :: acc)

/-- Split a string on whitespace (after normalizing comma spaces) and return all non-empty tokens. -/
def wordsOf (s : String) : List String :=
  ((splitCharsOnWs (collapseCommaSpaces s.data false) []).map trimChars).filter
    (fun cs => !cs.isEmpty) |>.map String.mk

/-- Strip a trailing `--` inline comment from a `List Char` (outside quotes). -/
def stripInlineCommentChars : List Char → List Char
  | [] => []
  | '-' :: '-' :: _ => []
  | c :: cs => c :: stripInlineCommentChars cs

/-- Strip a trailing `--` inline comment and trim whitespace. -/
def stripInlineComment (s : String) : String :=
  trimWs (String.mk (stripInlineCommentChars s.data))

/-- Split a comma-separated list into trimmed non-empty identifiers (ignoring inline `--` comments). -/
def parseCsvList (s : String) : List String :=
  let cleaned := stripInlineCommentChars s.data
  ((splitCharsOn ',' cleaned []).map trimChars).filter (fun cs => !cs.isEmpty) |>.map String.mk

/-- Scan until the opening `'"'` character. -/
def findOpeningQuote : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '"' :: rest, preAcc => some (preAcc.reverse, rest)
  | c :: rest, preAcc => findOpeningQuote rest (c :: preAcc)

/-- Scan inside a double-quoted literal until the unescaped closing `'"'`,
handling escape sequences `\"`, `\\`, `\n`, `\t`, and `\r`. -/
def scanQuotedBody : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '\\' :: c :: rest, acc =>
    let escaped := match c with
      | 'n' => '\n'
      | 't' => '\t'
      | 'r' => '\r'
      | other => other
    scanQuotedBody rest (escaped :: acc)
  | '"' :: rest, acc => some (acc.reverse, rest)
  | c :: rest, acc => scanQuotedBody rest (c :: acc)

/-- Split a directive line containing a trailing `"<quoted>"` string into
`(prefixBeforeQuote, quotedString)`, supporting escaped quotes (`\"`) and
trailing `--` or `#` comments. -/
def splitTrailingQuote (lineNo : Nat) (line : String) : Except String (String × String) :=
  match findOpeningQuote line.data [] with
  | none =>
    .error s!"Line {lineNo}: expected a single double-quoted text literal \"...\""
  | some (preChars, afterOpen) =>
    match scanQuotedBody afterOpen [] with
    | none =>
      .error s!"Line {lineNo}: unclosed double-quoted text literal \"...\""
    | some (quotedChars, postChars) =>
      let postTrim := trimChars postChars
      if postTrim.isEmpty || startsWithChars postTrim ['-', '-'] || startsWithChars postTrim ['#'] then
        .ok (String.mk (trimChars preChars), String.mk quotedChars)
      else
        .error s!"Line {lineNo}: unexpected trailing characters after closing quote"

/-- Coalesce physical lines into logical `.charter` directive lines, joining newlines
that occur inside double-quoted multi-line strings while respecting `\"` escapes. -/
def coalesceLogicalLines : List Char → Bool → List Char → List String
  | [], _, acc => [String.mk acc.reverse]
  | '\\' :: d :: rest, true, acc =>
    coalesceLogicalLines rest true (d :: '\\' :: acc)
  | '"' :: rest, inQuotes, acc =>
    coalesceLogicalLines rest (!inQuotes) ('"' :: acc)
  | '\r' :: rest, inQuotes, acc =>
    coalesceLogicalLines rest inQuotes acc
  | '\n' :: rest, true, acc =>
    let acc' := match acc with | ' ' :: _ => acc | _ => ' ' :: acc
    coalesceLogicalLines rest true acc'
  | ' ' :: rest, true, ' ' :: acc =>
    coalesceLogicalLines rest true (' ' :: acc)
  | '\t' :: rest, true, ' ' :: acc =>
    coalesceLogicalLines rest true (' ' :: acc)
  | '\n' :: rest, false, acc =>
    String.mk acc.reverse :: coalesceLogicalLines rest false []
  | c :: rest, inQuotes, acc =>
    coalesceLogicalLines rest inQuotes (c :: acc)

/-- Parse a single non-empty, non-comment `.charter` directive line and update `doc`. -/
def parseCharterLine (lineNo : Nat) (rawLine : String) (doc : ParsedCharterDoc) :
    Except String ParsedCharterDoc :=
  let line := trimWs rawLine
  if line.isEmpty || startsWithStr line "--" || startsWithStr line "#" then
    .ok doc
  else if startsWithStr line "institution " || startsWithStr line "institution\t" then
    match splitTrailingQuote lineNo line with
    | .error e => .error e
    | .ok (pre, title) =>
      match wordsOf pre with
      | ["institution", id] =>
        if id.isEmpty || title.isEmpty then
          .error s!"Line {lineNo}: 'institution' requires a non-empty id and title"
        else
          .ok { doc with institutionId := id, title := title }
      | _ => .error s!"Line {lineNo}: malformed 'institution' directive (expected: institution <id> \"<title>\")"
  else if startsWithStr line "roles:" then
    let items := parseCsvList (dropChars line 6)
    if items.isEmpty then
      .error s!"Line {lineNo}: 'roles:' directive requires at least one role"
    else
      .ok { doc with roles := doc.roles ++ items }
  else if startsWithStr line "acts:" then
    let items := parseCsvList (dropChars line 5)
    if items.isEmpty then
      .error s!"Line {lineNo}: 'acts:' directive requires at least one act"
    else
      .ok { doc with acts := doc.acts ++ items }
  else if startsWithStr line "facts:" then
    let items := parseCsvList (dropChars line 6)
    if items.isEmpty then
      .error s!"Line {lineNo}: 'facts:' directive requires at least one fact"
    else
      .ok { doc with facts := doc.facts ++ items }
  else if startsWithStr line "use module " || startsWithStr line "use\t" then
    match wordsOf (stripInlineComment line) with
    | "use" :: "module" :: modName :: "with" :: paramToks =>
      let params := String.intercalate " " paramToks
      if modName.isEmpty || params.isEmpty then
        .error s!"Line {lineNo}: 'use module' requires both module name and parameters"
      else
        .ok { doc with moduleImports := doc.moduleImports ++ [(modName, params)] }
    | _ =>
      .error s!"Line {lineNo}: malformed 'use module' directive (expected: use module <ModuleName> with <params>)"
  else if startsWithStr line "clause " || startsWithStr line "clause\t" then
    match splitTrailingQuote lineNo line with
    | .error e => .error e
    | .ok (pre, english) =>
      match wordsOf pre with
      | ["clause", cid] =>
        if cid.isEmpty || english.isEmpty then
          .error s!"Line {lineNo}: 'clause' requires a non-empty id and English text"
        else
          .ok { doc with clauses := doc.clauses ++ [(cid, english)] }
      | _ => .error s!"Line {lineNo}: malformed 'clause' directive (expected: clause <ID> \"<english>\")"
  else if startsWithStr line "duty " || startsWithStr line "duty\t" then
    match splitTrailingQuote lineNo line with
    | .error e => .error e
    | .ok (pre, english) =>
      match wordsOf pre with
      | ["duty", did, bearerTok, demandTok] =>
        if startsWithStr bearerTok "bearer=" && startsWithStr demandTok "demand=" then
          let who := dropChars bearerTok 7
          let dem := dropChars demandTok 7
          if did.isEmpty || who.isEmpty || dem.isEmpty || english.isEmpty then
            .error s!"Line {lineNo}: 'duty' fields must be non-empty"
          else
            .ok { doc with duties := doc.duties ++ [(did, who, dem, english)] }
        else
          .error s!"Line {lineNo}: 'duty' requires bearer=<who> and demand=<demand>"
      | _ =>
        .error s!"Line {lineNo}: malformed 'duty' directive (expected: duty <ID> bearer=<who> demand=<demand> \"<english>\")"
  else if startsWithStr line "power " || startsWithStr line "power\t" then
    match splitTrailingQuote lineNo line with
    | .error e => .error e
    | .ok (pre, english) =>
      match wordsOf pre with
      | ["power", pid, holderTok, triggerTok] =>
        if startsWithStr holderTok "holder=" && startsWithStr triggerTok "trigger=" then
          let who := dropChars holderTok 7
          let trig := dropChars triggerTok 8
          if pid.isEmpty || who.isEmpty || trig.isEmpty || english.isEmpty then
            .error s!"Line {lineNo}: 'power' fields must be non-empty"
          else
            .ok { doc with powers := doc.powers ++ [(pid, who, trig, english)] }
        else
          .error s!"Line {lineNo}: 'power' requires holder=<who> and trigger=<act>"
      | _ =>
        .error s!"Line {lineNo}: malformed 'power' directive (expected: power <ID> holder=<who> trigger=<act> \"<english>\")"
  else if startsWithStr line "immunity " || startsWithStr line "immunity\t" then
    match splitTrailingQuote lineNo line with
    | .error e => .error e
    | .ok (pre, english) =>
      match wordsOf pre with
      | ["immunity", iid, holderTok, againstTok] =>
        if startsWithStr holderTok "holder=" && startsWithStr againstTok "against=" then
          let who := dropChars holderTok 7
          let pids := dropChars againstTok 8
          if iid.isEmpty || who.isEmpty || pids.isEmpty || english.isEmpty then
            .error s!"Line {lineNo}: 'immunity' fields must be non-empty"
          else
            .ok { doc with immunities := doc.immunities ++ [(iid, s!"{who} against {pids}", english)] }
        else
          .error s!"Line {lineNo}: 'immunity' requires holder=<who> and against=<pids>"
      | _ =>
        .error s!"Line {lineNo}: malformed 'immunity' directive (expected: immunity <ID> holder=<who> against=<pids> \"<english>\")"
  else
    .error s!"Line {lineNo}: unrecognized .charter directive: {line}"

/-- Tail-recursive line-by-line parser helper for `.charter` specifications. -/
def parseCharterLines (lineNo : Nat) (lines : List String) (doc : ParsedCharterDoc) :
    Except String ParsedCharterDoc :=
  match lines with
  | [] =>
    if doc.institutionId.isEmpty then
      .error "Missing required 'institution <id> \"<title>\"' declaration"
    else
      .ok doc
  | rawLine :: rest =>
    match parseCharterLine lineNo rawLine doc with
    | .error err => .error err
    | .ok doc' => parseCharterLines (lineNo + 1) rest doc'

/-- Pure, total parser for the standalone `.charter` textual surface language.
Supports single- and multi-line double-quoted English literals, escaped quotes (`\"`),
tab/space delimiters, comma-separated argument lists, and inline `--` comments. -/
def parseCharterText (input : String) : Except String ParsedCharterDoc :=
  parseCharterLines 1 (coalesceLogicalLines input.data false []) {}

/-- Alias for `parseCharterText`. -/
abbrev parseCharterDSL (input : String) : Except String ParsedCharterDoc :=
  parseCharterText input

/-- Render a `ParsedCharterDoc` summary report for CLI inspection. -/
def ParsedCharterDoc.render (doc : ParsedCharterDoc) : String :=
  let modLines := doc.moduleImports.map fun (m, p) => s!"  - {m} ({p})"
  let clauseLines := doc.clauses.map fun (id, txt) => s!"  - [{id}] \"{txt}\""
  let dutyLines := doc.duties.map fun (id, who, dem, txt) =>
    s!"  - {id}: bearer={who}, demand={dem} | \"{txt}\""
  let powerLines := doc.powers.map fun (id, who, trig, txt) =>
    s!"  - {id}: holder={who}, trigger={trig} | \"{txt}\""
  let immLines := doc.immunities.map fun (id, ag, txt) =>
    s!"  - {id}: {ag} | \"{txt}\""
  "==========================================================================\n" ++
  s!"Parsed .charter Specification: {doc.institutionId} — \"{doc.title}\"\n" ++
  "==========================================================================\n" ++
  s!"Roles ({doc.roles.length}) : {String.intercalate ", " doc.roles}\n" ++
  s!"Acts  ({doc.acts.length}) : {String.intercalate ", " doc.acts}\n" ++
  s!"Facts ({doc.facts.length}) : {String.intercalate ", " doc.facts}\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Module Imports ({doc.moduleImports.length}):\n" ++
  String.intercalate "\n" modLines ++ "\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Clauses ({doc.clauses.length}):\n" ++
  String.intercalate "\n" clauseLines ++ "\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Duties ({doc.duties.length}):\n" ++
  String.intercalate "\n" dutyLines ++ "\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Powers ({doc.powers.length}):\n" ++
  String.intercalate "\n" powerLines ++ "\n" ++
  "--------------------------------------------------------------------------\n" ++
  s!"Immunities ({doc.immunities.length}):\n" ++
  String.intercalate "\n" immLines ++ "\n" ++
  "==========================================================================\n"

/-! ## 4. Embedded Reference `.charter` Specification & Kernel-Checked Parser Proofs -/

/-- Embedded verbatim contents of `examples/autonomous-commons.charter`. -/
def sampleCommonsCharterText : String :=
"-- ==========================================================================
-- Autonomous Compute & Treasury Commons (.charter standalone specification)
-- ==========================================================================

institution commons \"Autonomous Compute & Treasury Commons\"

roles: steward, contributor, auditor, arbiter, outsider
acts: contribute, allocate, postBond, pauseCommons, resumeCommons, transferCarryover, exitCommons, adjudicateBreach, issueLease, proposeAmendment
facts: activeMember, bondedSteward, commonsPaused, probableCause, groupCarryover, exitCompleted, breachFound, nodeLeaseActive, amendmentRatified

use module ResidualLedger with sunset=100,royaltyCap=10
use module CollateralPool with minBond=50,slashRate=100
use module CircuitBreaker with pauseWindow=5
use module EntityGroup with maxGroupSize=10
use module ExitAndVoice with noticeWindow=3
use module SortitionCourt with panelSize=3,appealWindow=5
use module AttestedLease with leaseDuration=20
use module OracleFeed with challengeWindow=4

clause COM.LEDGER \"All compute grants and treasury obligations are recorded at genesis in a single non-interest-bearing commons ledger.\"
clause COM.BOND \"Stewards and contributors must post a harm-scaled compute bond before executing external workloads.\"
clause COM.PAUSE \"Any auditor may trigger a brief preliminary cluster freeze by posting a scaled emergency stake; the pause continues into full suspension only if the arbiter panel affirms probable cause.\"
clause COM.GROUP \"Working groups of stewards share a unified commons sub-ledger; internal transfers are non-recognition carryover events that never inflate aggregate basis.\"
clause COM.EXIT \"Any bound steward may at any time execute unilateral ragequit exit or inscribe rate-limited dissent, and is immune from expulsion while exit settles.\"
clause COM.COURT \"Disputes are resolved by sortition panels of independent bonded arbiters, and the commons fee pool funds its operating reserve first.\"
clause COM.LEASE \"At most one compute node holds active operating authority for a steward at any moment under a time-bounded execution lease.\"
clause COM.AMEND \"Charter amendments require bilateral consent of stewards and contributors after a public timelock and may never weaken exit immunities.\"

duty D.STEWARD_BOND bearer=steward demand=require(postBond,5) \"Stewards must post a collateral bond within 5 time units of appointment.\"
duty D.NO_UNILATERAL_FREEZE bearer=steward demand=forbid(pauseCommons) \"Stewards may not unilaterally freeze member allocations outside emergency circuit-breaker authority.\"
duty D.HONOR_EXIT bearer=steward demand=forbid(allocate) \"Stewards may not encumber or reallocate a member's credits after exit is initiated.\"

power P.ALLOCATE holder=steward trigger=allocate \"Bonded stewards may allocate commons treasury and compute resources.\"
power P.PAUSE holder=arbiter trigger=pauseCommons \"The arbiter panel may trigger a time-bounded circuit-breaker pause upon probable cause.\"
power P.EXIT holder=steward trigger=exitCommons \"Any bound steward may unilaterally exit the commons at any time.\"
power P.ADJUDICATE holder=arbiter trigger=adjudicateBreach \"The sortition court panel may establish a steward breach and slash posted collateral.\"

immunity I.UNALIENABLE_EXIT holder=steward against=P.ALLOCATE,P.PAUSE \"No treasury allocation or emergency pause may extinguish a steward's unilateral right to exit.\"
immunity I.AUDITOR_INDEPENDENCE holder=auditor against=P.PAUSE \"Independent auditors are immune from suspension while conducting an active commons audit.\"
"

/-- Check whether a parsed result satisfies the expected Autonomous Commons metadata and counts. -/
def checkSampleCommonsDoc (res : Except String ParsedCharterDoc) : Bool :=
  match res with
  | .error _ => false
  | .ok doc =>
    doc.institutionId == "commons" &&
    doc.title == "Autonomous Compute & Treasury Commons" &&
    doc.roles.length == 5 &&
    doc.acts.length == 10 &&
    doc.facts.length == 9 &&
    doc.moduleImports.length == 8 &&
    doc.clauses.length == 8 &&
    doc.duties.length == 3 &&
    doc.powers.length == 4 &&
    doc.immunities.length == 2

/-- **Kernel-checked theorem:** `sampleCommonsCharterText` (`examples/autonomous-commons.charter`)
parses cleanly with zero errors. -/
theorem sample_charter_dsl_parses_cleanly :
    (parseCharterText sampleCommonsCharterText).isOk = true := by decide

/-- Alias for `sample_charter_dsl_parses_cleanly`. -/
theorem parsed_commons_dsl_valid :
    (parseCharterDSL sampleCommonsCharterText).isOk = true := by decide

/-- Kernel-checked verification of the exact parsed AST counts and metadata for
`sampleCommonsCharterText`. -/
theorem sample_charter_dsl_contents :
    checkSampleCommonsDoc (parseCharterText sampleCommonsCharterText) = true := by decide

/-- Kernel-checked verification of multi-line quoted clauses, escaped quotes (`\"`),
tab delimiters, spaces after commas in `demand=` / `against=`, and inline `--` comments. -/
def multilineAndEscapedCharterSample : String :=
  "institution\ttest_inst\t\"The \\\"Sovereign\\\" Commons\"\n" ++
  "roles: steward, auditor -- inline comment\n" ++
  "use module CircuitBreaker with pauseWindow=5, maxRetries=2 -- module comment\n" ++
  "clause C.MULTI \"First line of clause\n  second line with \\\"escaped\\\" quotes.\"\n" ++
  "duty D.1 bearer=steward demand=require(postBond, 5) \"Must post bond.\"\n" ++
  "immunity I.1 holder=steward against=P.ALLOCATE, P.PAUSE \"Protected against both.\" -- trailing comment\n"

theorem parseCharterText_multiline_and_escaped_quotes :
    (match parseCharterText multilineAndEscapedCharterSample with
    | .error _ => false
    | .ok doc =>
      doc.institutionId == "test_inst" &&
      doc.title == "The \"Sovereign\" Commons" &&
      doc.roles == ["steward", "auditor"] &&
      doc.moduleImports == [("CircuitBreaker", "pauseWindow=5,maxRetries=2")] &&
      doc.clauses == [("C.MULTI", "First line of clause second line with \"escaped\" quotes.")] &&
      doc.duties == [("D.1", "steward", "require(postBond,5)", "Must post bond.")] &&
      doc.immunities == [("I.1", "steward against P.ALLOCATE,P.PAUSE", "Protected against both.")]) = true := by
  decide

/-- Edge-case verification: empty input, comment-only input, malformed directives,
and unclosed quotes are cleanly rejected by `parseCharterText`. -/
theorem parseCharterText_rejects_invalid_inputs :
    (parseCharterText "").isOk = false ∧
    (parseCharterText "-- only a comment\n# another comment\n").isOk = false ∧
    (parseCharterText "institution commons \"Unclosed quote").isOk = false ∧
    (parseCharterText "institution commons \"Title\" trailing_junk").isOk = false ∧
    (parseCharterText "institution commons \"Title\"\nunknown_directive foo").isOk = false ∧
    (parseCharterText "institution commons \"Title\"\nduty D.1 bearer=steward \"missing demand\"").isOk = false := by
  decide

end Charter.Surface

namespace Charter

export Charter.Surface (
  shortCtorName
  StringTable
  OntologyTables
  surface_syntax_roundtrip
  charter_surface_roundtrip
  ParsedCharterDoc
  parseCharterLine
  parseCharterText
  parseCharterDSL
  sampleCommonsCharterText
  sample_charter_dsl_parses_cleanly
  parsed_commons_dsl_valid
  sample_charter_dsl_contents
  parseCharterText_multiline_and_escaped_quotes
  parseCharterText_rejects_invalid_inputs
)

end Charter
