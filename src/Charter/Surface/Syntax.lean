import Lean
import Charter.Core.Semantics

/-!
# Charter.Surface.Syntax — Literate Catala-Style Surface Syntax for Charter

This module provides the literate surface syntax for the Charter Institutional Specification Language. Every surface declaration (`charter_clause`, `charter_duty`,
`charter_power`, `charter_immunity`, and `charter_string_table`) is a pure Lean 4 macro
that elaborates directly into the deep-embedded AST structures in
`Charter.Core.Provenance` and `Charter.Core.Syntax` (`Clause`, `Span`, `Duty`,
`Power`, `Immunity`, `Law`).

## Trust Architecture

* **Zero expansion of the trusted computing base:** Surface declarations
  elaborate into standard `Charter.Core` values before typechecking. Lean's
  kernel checks every theorem directly over the elaborated data structures.
* **Definitional round-trip identity:** Every surface declaration is
  definitionally equal (`rfl`) to the underlying hand-written record.
* **Automatic CLI string tables:** `charter_string_table` and `OntologyTables`
  derive `all`, `toName`, and `ofString?` parsers directly from constructor
  lists without hand-written string matchers.
-/

namespace Charter.Surface

open Charter Lean

/-! ## 1. Automatic CLI String Tables -/

/-- Strip namespace prefixes and surrounding parentheses from each space-separated
token of a `Repr` string, joining constructor and argument names with `"."` so
that both nullary constructors (`"Ns.Role.agent" ↦ "agent"`) and parameterized
constructors (`"Ns.Fact.initiator (Ns.Role.agent)" ↦ "initiator.agent"`) receive
unique, canonical CLI token names. -/
def shortCtorName (s : String) : String :=
  let cleanTok (tok : String) : String :=
    let t := (tok.dropWhile (· == '(')).dropRightWhile (· == ')')
    (t.splitOn ".").getLastD t
  let parts := (s.splitOn " ").filter (fun p => !p.isEmpty)
  String.intercalate "." (parts.map cleanTok)

/-- A CLI string table pairing the list of all constructors with a forward
renderer (`toName`) and a partial parser (`ofString?`). -/
structure StringTable (α : Type) where
  all       : List α
  toName    : α → String
  ofString? : String → Option α

/-- All valid CLI token strings in a `StringTable`. -/
def StringTable.names {α : Type} (t : StringTable α) : List String :=
  t.all.map t.toName

/-- Derive a `StringTable α` from `all : List α` and `[Repr α]` for runtime CLI use. -/
def StringTable.ofRepr {α : Type} [Repr α] (all : List α) : StringTable α :=
  let toName (x : α) : String := shortCtorName (reprStr x)
  { all := all
    toName := toName
    ofString? := fun s => all.find? (fun x => toName x == s) }

/-- Build a kernel-computable `StringTable α` for a unary parameterized constructor
`ctor : β → α` (such as `Fact.initiator : Party → Fact`) given a prefix name and
a `StringTable β` for its argument. Names are formatted as `"<prefixName>.<argName>"`. -/
def StringTable.param {α β : Type} [BEq α] (prefixName : String) (ctor : β → α)
    (sub : StringTable β) : StringTable α :=
  let pairs : List (α × String) :=
    sub.all.map fun b => (ctor b, s!"{prefixName}.{sub.toName b}")
  { all := pairs.map (·.1)
    toName := fun x =>
      match pairs.find? (fun p => p.1 == x) with
      | some p => p.2
      | none => ""
    ofString? := fun s =>
      match pairs.find? (fun p => p.2 == s) with
      | some p => some p.1
      | none => none }

/-- Combine two `StringTable α` tables (for example, a parameterized constructor
table from `StringTable.param` and a nullary constructor table from `charter_string_table`). -/
def StringTable.append {α : Type} (t₁ t₂ : StringTable α) : StringTable α :=
  { all := t₁.all ++ t₂.all
    toName := fun x =>
      let n := t₁.toName x
      if n.isEmpty then t₂.toName x else n
    ofString? := fun s =>
      match t₁.ofString? s with
      | some x => some x
      | none => t₂.ofString? s }

instance {α : Type} : Append (StringTable α) := ⟨StringTable.append⟩

/-- Command that declares a kernel-computable `StringTable α` from a list of nullary
constructor identifiers:

    charter_string_table Act.table : Act [c₁, c₂, ...]

It emits three top-level definitions: `Act.table.name : Act → String` and
`Act.table.parse : String → Option Act` (both plain `match` expressions, so they
reduce in the kernel) and `Act.table : StringTable Act` tying them together with the
constructor list. Constructors not listed (for instance parameterized ones) render as
`""`; combine with `StringTable.param` for those. The functions are separate
declarations rather than closures inside one structure literal because the Lean 4.24
code generator miscompiles very large closures of that shape. -/
syntax (docComment)? "charter_string_table " ident " : " ident "[" ident,* "]" : command

macro_rules
  | `($[$doc:docComment]? charter_string_table $tbl:ident : $ty:ident [ $[$cs:ident],* ]) => do
    let nameFn := mkIdentFrom tbl (tbl.getId ++ `name)
    let parseFn := mkIdentFrom tbl (tbl.getId ++ `parse)
    let mut allElems : Array (TSyntax `term) := #[]
    let mut toAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut ofAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for c in cs do
      let ctor : Ident := mkIdentFrom c (ty.getId ++ c.getId)
      let strLit : TSyntax `term := Syntax.mkStrLit c.getId.toString
      allElems := allElems.push (← `($ctor:ident))
      toAlts := toAlts.push (← `(Lean.Parser.Term.matchAltExpr| | some $ctor:ident => $strLit))
      ofAlts := ofAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $strLit => some $ctor:ident))
    toAlts := toAlts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => ""))
    ofAlts := ofAlts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
    `(def $nameFn : $ty → String := fun x => match (some x : Option $ty) with $toAlts:matchAlt*
      def $parseFn : String → Option $ty := fun s => match s with $ofAlts:matchAlt*
      $[$doc:docComment]? def $tbl : StringTable $ty :=
        { all := ([ $[$allElems],* ] : List $ty), toName := $nameFn, ofString? := $parseFn })

/-- Complete set of CLI string tables for an Charter signature `σ`. -/
structure OntologyTables (σ : Sig) where
  actors : StringTable σ.Actor
  acts   : StringTable σ.Act
  facts  : StringTable σ.Fact

/-! ## 2. Surface Syntax Categories & Combinators (`charter_clause`) -/

/-- Surface syntax category for span entries inside `charter_clause`.
Every non-normative register (`invariant`, `acceptance`, `definition`, `commentary`)
supports both an explicit `=> meaning` list and an omitted meaning list (defaulting
to `[]`, as in `Charter.Core.Provenance`). -/
declare_syntax_cat charter_span_entry

syntax "span_norm " term " => " term : charter_span_entry
syntax "span_invariant " term : charter_span_entry
syntax "span_invariant " term " => " term : charter_span_entry
syntax "span_acceptance " term : charter_span_entry
syntax "span_acceptance " term " => " term : charter_span_entry
syntax "span_definition " term : charter_span_entry
syntax "span_definition " term " => " term : charter_span_entry
syntax "span_commentary " term : charter_span_entry
syntax "span_commentary " term " => " term : charter_span_entry

/-- Elaborate a single `charter_span_entry` given the enclosing clause identifier. -/
syntax "elab_charter_span% " term " : " charter_span_entry : term

macro_rules
  | `(elab_charter_span% $cid : span_norm $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.norm, meaning := $m : Span })
  | `(elab_charter_span% $cid : span_invariant $txt) =>
      `({ clause := $cid, text := $txt, register := Register.invariant, meaning := [] : Span })
  | `(elab_charter_span% $cid : span_invariant $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.invariant, meaning := $m : Span })
  | `(elab_charter_span% $cid : span_acceptance $txt) =>
      `({ clause := $cid, text := $txt, register := Register.acceptance, meaning := [] : Span })
  | `(elab_charter_span% $cid : span_acceptance $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.acceptance, meaning := $m : Span })
  | `(elab_charter_span% $cid : span_definition $txt) =>
      `({ clause := $cid, text := $txt, register := Register.definition, meaning := [] : Span })
  | `(elab_charter_span% $cid : span_definition $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.definition, meaning := $m : Span })
  | `(elab_charter_span% $cid : span_commentary $txt) =>
      `({ clause := $cid, text := $txt, register := Register.commentary, meaning := [] : Span })
  | `(elab_charter_span% $cid : span_commentary $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.commentary, meaning := $m : Span })

/-- Elaborate a list of `charter_span_entry` items under a shared clause identifier. -/
syntax "elab_charter_spans% " term ("|" charter_span_entry)* : term

macro_rules
  | `(elab_charter_spans% $_cid) => `(([] : List Span))
  | `(elab_charter_spans% $cid | $e:charter_span_entry $[| $rest:charter_span_entry]*) =>
      `((elab_charter_span% $cid : $e) :: (elab_charter_spans% $cid $[| $rest]*))

/-- Literate clause declaration (`charter_clause`).
Supports:
1. Full provenance form with explicit source and approved hash:
   `charter_clause "ID" from_text S approved_hash H where | ...`
2. Explicit source with default hash `0`:
   `charter_clause "ID" from_text S where | ...`
3. Self-assembling literate form where `source` is synthesized by joining spans:
   `charter_clause "ID" where | ...` -/
syntax "charter_clause " term " from_text " term " approved_hash " term " where" ("|" charter_span_entry)* : term
syntax "charter_clause " term " from_text " term " where" ("|" charter_span_entry)* : term
syntax "charter_clause " term " where" ("|" charter_span_entry)* : term

macro_rules
  | `(charter_clause $cid from_text $src approved_hash $h where $[| $entries:charter_span_entry]*) =>
      `({ id := $cid
          source := $src
          approvedHash := $h
          spans := elab_charter_spans% $cid $[| $entries]* : Clause })
  | `(charter_clause $cid from_text $src where $[| $entries:charter_span_entry]*) =>
      `({ id := $cid
          source := $src
          approvedHash := 0
          spans := elab_charter_spans% $cid $[| $entries]* : Clause })
  | `(charter_clause $cid where $[| $entries:charter_span_entry]*) =>
      `(let sps : List Span := elab_charter_spans% $cid $[| $entries]*
        { id := $cid
          source := String.join (sps.map (·.text))
          approvedHash := 0
          spans := sps : Clause })

/-! ## 3. Literate Declarations for `charter_duty`, `charter_power`, and `charter_immunity` -/

/-- Optional modifier clauses for `charter_duty`. -/
declare_syntax_cat charter_duty_mod

syntax "except_when " term : charter_duty_mod
syntax "except_by_power " term : charter_duty_mod
syntax "overridden_by " term : charter_duty_mod
syntax "breach_by " term : charter_duty_mod
syntax "with_remedies " term : charter_duty_mod
syntax "with_source " term : charter_duty_mod

/-- Apply a sequence of `charter_duty_mod` modifiers to a base `Duty`. -/
syntax "apply_duty_mods% " term ("|" charter_duty_mod)* : term

macro_rules
  | `(apply_duty_mods% $base) => `($base)
  | `(apply_duty_mods% $base | except_when $c $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with unlessCond := $c } $[| $rest]*)
  | `(apply_duty_mods% $base | except_by_power $ps $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with unlessPower := $ps } $[| $rest]*)
  | `(apply_duty_mods% $base | overridden_by $ds $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with overriddenBy := $ds } $[| $rest]*)
  | `(apply_duty_mods% $base | breach_by $p $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with breachEstablishedBy := some $p } $[| $rest]*)
  | `(apply_duty_mods% $base | with_remedies $rs $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with remedies := $rs } $[| $rest]*)
  | `(apply_duty_mods% $base | with_source $sp $[| $rest:charter_duty_mod]*) =>
      `(apply_duty_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate duty declaration (`charter_duty`).
Elaborates directly to an `Charter.Duty σ` record. -/
syntax "charter_duty " term " over " term
  " from_clause " term " : " term
  " owed_by " term
  " owed_to " term
  " active_when " term
  " demands " term
  ("|" charter_duty_mod)* : term

macro_rules
  | `(charter_duty $id over $sig
        from_clause $cid : $txt
        owed_by $br
        owed_to $bn
        active_when $act
        demands $dem
        $[| $mods:charter_duty_mod]*) =>
      `((apply_duty_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             bearer := $br
             beneficiary := $bn
             active := $act
             demand := $dem : Duty $sig })
          $[| $mods]* : Duty $sig))

/-- Optional modifier clauses for `charter_power`. -/
declare_syntax_cat charter_power_mod

syntax "valid_when " term : charter_power_mod
syntax "establishes " term : charter_power_mod
syntax "establishes_for " term : charter_power_mod
syntax "establishes_by_actor " term : charter_power_mod
syntax "extinguishes " term : charter_power_mod
syntax "cond_establishes " term : charter_power_mod
syntax "establishes_breach_of " term : charter_power_mod
syntax "with_source " term : charter_power_mod

/-- Apply a sequence of `charter_power_mod` modifiers to a base `Power`. -/
syntax "apply_power_mods% " term ("|" charter_power_mod)* : term

macro_rules
  | `(apply_power_mods% $base) => `($base)
  | `(apply_power_mods% $base | valid_when $v $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with valid := $v } $[| $rest]*)
  | `(apply_power_mods% $base | establishes $fs $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with adds := $fs } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_for $fts $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with addsFor := $fts } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_by_actor $afs $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with addsByActor := $afs } $[| $rest]*)
  | `(apply_power_mods% $base | extinguishes $rs $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with removes := $rs } $[| $rest]*)
  | `(apply_power_mods% $base | cond_establishes $cfs $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with condAdds := $cfs } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_breach_of $d $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with establishesBreachOf := some $d } $[| $rest]*)
  | `(apply_power_mods% $base | with_source $sp $[| $rest:charter_power_mod]*) =>
      `(apply_power_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate power declaration (`charter_power`).
Elaborates directly to an `Charter.Power σ` record. -/
syntax "charter_power " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " triggered_by " term
  ("|" charter_power_mod)* : term

macro_rules
  | `(charter_power $id over $sig
        from_clause $cid : $txt
        held_by $h
        triggered_by $tr
        $[| $mods:charter_power_mod]*) =>
      `((apply_power_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             holder := $h
             trigger := $tr : Power $sig })
          $[| $mods]* : Power $sig))

/-- Optional modifier clauses for `charter_immunity`. -/
declare_syntax_cat charter_immunity_mod

syntax "except_when " term : charter_immunity_mod
syntax "with_source " term : charter_immunity_mod

/-- Apply a sequence of `charter_immunity_mod` modifiers to a base `Immunity`. -/
syntax "apply_immunity_mods% " term ("|" charter_immunity_mod)* : term

macro_rules
  | `(apply_immunity_mods% $base) => `($base)
  | `(apply_immunity_mods% $base | except_when $u $[| $rest:charter_immunity_mod]*) =>
      `(apply_immunity_mods% { $base with unlessCond := $u } $[| $rest]*)
  | `(apply_immunity_mods% $base | with_source $sp $[| $rest:charter_immunity_mod]*) =>
      `(apply_immunity_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate immunity declaration (`charter_immunity`).
Elaborates directly to an `Charter.Immunity σ` record. -/
syntax "charter_immunity " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " protected_against " term
  " active_when " term
  ("|" charter_immunity_mod)* : term

macro_rules
  | `(charter_immunity $id over $sig
        from_clause $cid : $txt
        held_by $h
        protected_against $ag
        active_when $act
        $[| $mods:charter_immunity_mod]*) =>
      `((apply_immunity_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             holder := $h
             against := $ag
             active := $act : Immunity $sig })
          $[| $mods]* : Immunity $sig))

/-! ## 4. Self-Contained Concrete Examples & Kernel-Checked Round-Trip Proofs -/

namespace Examples

set_option maxRecDepth 200000

/-- Self-contained reference ontology for testing the surface syntax: a toy
residential-tenancy charter unrelated to any shipped example program, including
both nullary constructors and parameterized constructors (`PropFact.initiator`). -/
inductive Role
  | tenant | landlord | tribunal | creditor
  deriving DecidableEq, Repr

inductive Action
  | evict | giveNotice | endTenancy | postDeposit
  | postEmergencyStake | suspend | affirmProbableCause | findUnlawfulEviction
  | confirmHazard | objectToEviction | declareUninhabitable
  deriving DecidableEq, Repr

inductive PropFact
  | initiator (r : Role)
  | leased | landlordRegistered | depositPosted | noticeGiven
  | emergencyStakePosted | initiatedByCreditor
  | preliminaryFreeze | probableCause | suspended
  | landlordRelatedToCreditor | directionPresumed
  | unlawfulEvictionEstablished | landlordDepositSlashed | restorationPermitted
  | hazardConfirmed | tenantObjectsToEviction | premisesUninhabitable
  | evictedByTribunal | vacated
  deriving DecidableEq, Repr

def σ_ex : Sig := { Actor := Role, Act := Action, Fact := PropFact }

instance : Repr σ_ex.Actor := inferInstanceAs (Repr Role)
instance : Repr σ_ex.Act   := inferInstanceAs (Repr Action)
instance : Repr σ_ex.Fact  := inferInstanceAs (Repr PropFact)

/-- Automatically derived, kernel-computable CLI string tables for `σ_ex`.
`factTable` combines the parameterized `PropFact.initiator` constructor family
(`StringTable.param`) with the nullary constructors (`charter_string_table`). -/
charter_string_table roleTable : Role [tenant, landlord, tribunal, creditor]

charter_string_table emptyRoleTable : Role []

charter_string_table actionTable : Action [
    evict, giveNotice, endTenancy, postDeposit,
    postEmergencyStake, suspend, affirmProbableCause, findUnlawfulEviction,
    confirmHazard, objectToEviction, declareUninhabitable
  ]

charter_string_table nullaryFactTable : PropFact [
    leased, landlordRegistered, depositPosted, noticeGiven,
    emergencyStakePosted, initiatedByCreditor,
    preliminaryFreeze, probableCause, suspended,
    landlordRelatedToCreditor, directionPresumed,
    unlawfulEvictionEstablished, landlordDepositSlashed, restorationPermitted,
    hazardConfirmed, tenantObjectsToEviction, premisesUninhabitable,
    evictedByTribunal, vacated
  ]

def factTable : StringTable PropFact :=
  StringTable.param "initiator" PropFact.initiator roleTable ++ nullaryFactTable

def exTables : OntologyTables σ_ex :=
  { actors := roleTable, acts := actionTable, facts := factTable }

/-! ### 4.1 Clause Surface Syntax Examples & Round-Trip Equivalence -/

def exTen21Source : String :=
  "Registered landlords must post a security deposit and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation (or for non-payment after notice)."

def surfaceClauseTen21 : Clause :=
  charter_clause "TEN.2.1" from_text exTen21Source approved_hash 5922915569903263201 where
    | span_norm "Registered landlords must post a security deposit" => ["D.DEPOSIT"]
    | span_norm " and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def manualClauseTen21 : Clause :=
  { id := "TEN.2.1"
    source := exTen21Source
    approvedHash := 5922915569903263201
    spans := [
      { clause := "TEN.2.1", text := "Registered landlords must post a security deposit", register := .norm, meaning := ["D.DEPOSIT"] },
      { clause := "TEN.2.1", text := " and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation", register := .norm, meaning := ["D.NOTICE", "P.GIVE_NOTICE"] },
      { clause := "TEN.2.1", text := " (or for non-payment after notice)", register := .norm, meaning := ["D.NOTICE"] },
      { clause := "TEN.2.1", text := ".", register := .commentary, meaning := [] }
    ] }

/-- Kernel-checked (`rfl`) round-trip proof: `charter_clause` with `from_text` and
`approved_hash` elaborates to the exact underlying `Charter.Clause` record. -/
theorem surfaceClauseTen21_eq_manual : surfaceClauseTen21 = manualClauseTen21 := rfl

/-- Clause exercising all five `Register` kinds (`norm`, `definition`, `invariant`,
`acceptance`, `commentary`) under `from_text` without explicit hash, including
both explicit `=> meaning` lists and omitted meaning lists on non-normative spans. -/
def exMultiRegisterSource : String :=
  "No party may lock out (change the locks on) a leased tenant; yielding zero benefit to any initiator; excess damages may prove uncollectible."

def surfaceClauseMultiRegister : Clause :=
  charter_clause "TEN.EX.MULTI" from_text exMultiRegisterSource where
    | span_norm "No party may lock out" => ["D.NO_EVICT"]
    | span_definition " (change the locks on)" => ["D.NO_EVICT"]
    | span_norm " a leased tenant" => ["D.NO_EVICT"]
    | span_invariant "; yielding zero benefit to any initiator" => ["INV.EX.1"]
    | span_acceptance "; excess damages may prove uncollectible"
    | span_commentary "." => ["NOTE.PERIOD"]

def manualClauseMultiRegister : Clause :=
  { id := "TEN.EX.MULTI"
    source := exMultiRegisterSource
    approvedHash := 0
    spans := [
      { clause := "TEN.EX.MULTI", text := "No party may lock out", register := .norm, meaning := ["D.NO_EVICT"] },
      { clause := "TEN.EX.MULTI", text := " (change the locks on)", register := .definition, meaning := ["D.NO_EVICT"] },
      { clause := "TEN.EX.MULTI", text := " a leased tenant", register := .norm, meaning := ["D.NO_EVICT"] },
      { clause := "TEN.EX.MULTI", text := "; yielding zero benefit to any initiator", register := .invariant, meaning := ["INV.EX.1"] },
      { clause := "TEN.EX.MULTI", text := "; excess damages may prove uncollectible", register := .acceptance, meaning := [] },
      { clause := "TEN.EX.MULTI", text := ".", register := .commentary, meaning := ["NOTE.PERIOD"] }
    ] }

theorem surfaceClauseMultiRegister_eq_manual :
    surfaceClauseMultiRegister = manualClauseMultiRegister := rfl

/-- Clause exercising omitted `=>` meaning lists on `span_definition`, `span_invariant`,
`span_acceptance`, and `span_commentary`. -/
def surfaceClauseNonNormativeDefaults : Clause :=
  charter_clause "TEN.EX.DEFAULTS" where
    | span_definition "Term: "
    | span_norm "must hold" => ["D.DEPOSIT"]
    | span_invariant "; invariant"
    | span_acceptance "; accepted limit" => ["ASSUMP.1"]
    | span_commentary "."

def manualClauseNonNormativeDefaults : Clause :=
  { id := "TEN.EX.DEFAULTS"
    source := "Term: must hold; invariant; accepted limit."
    approvedHash := 0
    spans := [
      { clause := "TEN.EX.DEFAULTS", text := "Term: ", register := .definition, meaning := [] },
      { clause := "TEN.EX.DEFAULTS", text := "must hold", register := .norm, meaning := ["D.DEPOSIT"] },
      { clause := "TEN.EX.DEFAULTS", text := "; invariant", register := .invariant, meaning := [] },
      { clause := "TEN.EX.DEFAULTS", text := "; accepted limit", register := .acceptance, meaning := ["ASSUMP.1"] },
      { clause := "TEN.EX.DEFAULTS", text := ".", register := .commentary, meaning := [] }
    ] }

theorem surfaceClauseNonNormativeDefaults_eq_manual :
    surfaceClauseNonNormativeDefaults = manualClauseNonNormativeDefaults := rfl

/-- Self-assembling literate clause where `source` is synthesized from spans. -/
def surfaceClauseAutoSource : Clause :=
  charter_clause "TEN.2.1.AUTO" where
    | span_norm "Registered landlords must post a security deposit" => ["D.DEPOSIT"]
    | span_norm " and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def manualClauseAutoSource : Clause :=
  { id := "TEN.2.1.AUTO"
    source := exTen21Source
    approvedHash := 0
    spans := [
      { clause := "TEN.2.1.AUTO", text := "Registered landlords must post a security deposit", register := .norm, meaning := ["D.DEPOSIT"] },
      { clause := "TEN.2.1.AUTO", text := " and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation", register := .norm, meaning := ["D.NOTICE", "P.GIVE_NOTICE"] },
      { clause := "TEN.2.1.AUTO", text := " (or for non-payment after notice)", register := .norm, meaning := ["D.NOTICE"] },
      { clause := "TEN.2.1.AUTO", text := ".", register := .commentary, meaning := [] }
    ] }

theorem surfaceClauseAutoSource_eq_manual :
    surfaceClauseAutoSource = manualClauseAutoSource := rfl

/-- Empty-span clause boundary test. -/
def surfaceClauseEmpty : Clause :=
  charter_clause "TEN.EMPTY" where

theorem surfaceClauseEmpty_eq_manual :
    surfaceClauseEmpty = { id := "TEN.EMPTY", source := "", approvedHash := 0, spans := [] } := rfl

theorem surfaceClauseTen21_covered : surfaceClauseTen21.covered = true := by decide
theorem surfaceClauseTen21_normsInterpreted : surfaceClauseTen21.normsInterpreted = true := by decide
theorem surfaceClauseMultiRegister_covered : surfaceClauseMultiRegister.covered = true := by decide
theorem surfaceClauseMultiRegister_normsInterpreted : surfaceClauseMultiRegister.normsInterpreted = true := by decide
theorem surfaceClauseNonNormativeDefaults_covered : surfaceClauseNonNormativeDefaults.covered = true := by decide
theorem surfaceClauseNonNormativeDefaults_normsInterpreted : surfaceClauseNonNormativeDefaults.normsInterpreted = true := by decide
theorem surfaceClauseAutoSource_covered : surfaceClauseAutoSource.covered = true := by decide
theorem surfaceClauseEmpty_covered : surfaceClauseEmpty.covered = true := by decide

/-! ### 4.2 Duty Surface Syntax Examples & Round-Trip Equivalence -/

/-- Prohibition duty with power exceptions, breach procedure, and remedies. -/
def surfaceDutyNoEvict : Duty σ_ex :=
  charter_duty "D.NO_EVICT" over σ_ex
    from_clause "TEN.2.2" : "No party may unilaterally evict or suspend a leased tenant outside the vacate procedure or tribunal suspension."
    owed_by .anyone
    owed_to (.only [.tenant])
    active_when (.holds .leased)
    demands (.forbid (.anyOf [.evict, .suspend]))
    | except_by_power ["P.VACATE", "P.SUSPEND", "P.ORDER_EVICTION"]
    | breach_by "P.FIND_UNLAWFUL_EVICTION"
    | with_remedies [.unlawfulEvictionEstablished, .landlordDepositSlashed, .restorationPermitted]

def manualDutyNoEvict : Duty σ_ex :=
  { id := "D.NO_EVICT"
    source := { clause := "TEN.2.2"
                text := "No party may unilaterally evict or suspend a leased tenant outside the vacate procedure or tribunal suspension."
                register := .norm
                meaning := ["D.NO_EVICT"] }
    bearer := .anyone
    beneficiary := .only [.tenant]
    active := .holds .leased
    demand := .forbid (.anyOf [.evict, .suspend])
    unlessCond := .ff
    unlessPower := ["P.VACATE", "P.SUSPEND", "P.ORDER_EVICTION"]
    overriddenBy := []
    breachEstablishedBy := some "P.FIND_UNLAWFUL_EVICTION"
    remedies := [.unlawfulEvictionEstablished, .landlordDepositSlashed, .restorationPermitted] }

/-- Kernel-checked (`rfl`) round-trip proof: `charter_duty` (prohibition with exceptions
and remedies) elaborates to the exact `Charter.Duty` record. -/
theorem surfaceDutyNI_eq_manual : surfaceDutyNoEvict = manualDutyNoEvict := rfl

/-- Prohibition duty with a timed scope exception (`except_when`) and `overridden_by`. -/
def surfaceDutyNotice (noticeWindow : Time) : Duty σ_ex :=
  charter_duty "D.NOTICE" over σ_ex
    from_clause "TEN.2.1" : "may end a tenancy only after providing a contractual notice window"
    owed_by (.only [.landlord])
    owed_to (.only [.tenant])
    active_when (.holds .leased)
    demands (.forbid (.act .endTenancy))
    | except_when (.heldFor .noticeGiven noticeWindow)
    | overridden_by ["D.DEPOSIT"]

def manualDutyNotice (noticeWindow : Time) : Duty σ_ex :=
  { id := "D.NOTICE"
    source := { clause := "TEN.2.1"
                text := "may end a tenancy only after providing a contractual notice window"
                register := .norm
                meaning := ["D.NOTICE"] }
    bearer := .only [.landlord]
    beneficiary := .only [.tenant]
    active := .holds .leased
    demand := .forbid (.act .endTenancy)
    unlessCond := .heldFor .noticeGiven noticeWindow
    overriddenBy := ["D.DEPOSIT"] }

/-- Kernel-checked (`rfl`) round-trip proof for parameterized `charter_duty`. -/
theorem surfaceDutyNotice_eq_manual (w : Time) :
    surfaceDutyNotice w = manualDutyNotice w := rfl

/-- Positive requirement duty with a deadline (`Demand.require`) and zero optional modifiers. -/
def surfaceDutyDeposit (bondDeadline : Time) : Duty σ_ex :=
  charter_duty "D.DEPOSIT" over σ_ex
    from_clause "TEN.2.1" : "Registered landlords must post a security deposit"
    owed_by (.only [.landlord])
    owed_to (.only [.tenant])
    active_when (.holds .landlordRegistered)
    demands (.require (.act .postDeposit) bondDeadline)

def manualDutyDeposit (bondDeadline : Time) : Duty σ_ex :=
  { id := "D.DEPOSIT"
    source := { clause := "TEN.2.1"
                text := "Registered landlords must post a security deposit"
                register := .norm
                meaning := ["D.DEPOSIT"] }
    bearer := .only [.landlord]
    beneficiary := .only [.tenant]
    active := .holds .landlordRegistered
    demand := .require (.act .postDeposit) bondDeadline }

theorem surfaceDutyBond_eq_manual (d : Time) :
    surfaceDutyDeposit d = manualDutyDeposit d := rfl

/-- Duty exercising the `with_source` modifier to attach a custom `Span`. -/
def customDutySpan : Span :=
  { clause := "TEN.2.2", text := "custom duty span", register := .norm, meaning := ["D.CUSTOM", "D.NO_EVICT"] }

def surfaceDutyCustomSource : Duty σ_ex :=
  charter_duty "D.CUSTOM" over σ_ex
    from_clause "TEN.2.2" : "placeholder"
    owed_by (.only [.landlord])
    owed_to (.only [.tenant])
    active_when (.holds .leased)
    demands (.forbid (.act .evict))
    | with_source customDutySpan

theorem surfaceDutyCustomSource_eq_manual :
    surfaceDutyCustomSource =
      { id := "D.CUSTOM"
        source := customDutySpan
        bearer := .only [.landlord]
        beneficiary := .only [.tenant]
        active := .holds .leased
        demand := .forbid (.act .evict) } := rfl

/-! ### 4.3 Power Surface Syntax Examples & Round-Trip Equivalence -/

/-- Power with `valid_when`, `establishes`, and `extinguishes`. -/
def surfacePowerVacate : Power σ_ex :=
  charter_power "P.VACATE" over σ_ex
    from_clause "TEN.5.1" : "Any leased tenant may at any time vacate the premises"
    held_by (.only [.tenant])
    triggered_by (.act .evict)
    | valid_when (.holds .leased)
    | establishes [.vacated]
    | extinguishes [.leased]

def manualPowerVacate : Power σ_ex :=
  { id := "P.VACATE"
    source := { clause := "TEN.5.1"
                text := "Any leased tenant may at any time vacate the premises"
                register := .norm
                meaning := ["P.VACATE"] }
    holder := .only [.tenant]
    trigger := .act .evict
    valid := .holds .leased
    adds := [.vacated]
    removes := [.leased] }

/-- Kernel-checked (`rfl`) round-trip proof: `charter_power` elaborates to the exact
underlying `Charter.Power` record. -/
theorem surfacePowerRevoke_eq_manual : surfacePowerVacate = manualPowerVacate := rfl

/-- Power with time-bounded effects (`establishes_for`) and actor-indexed facts
(`establishes_by_actor`), including the parameterized `.initiator .creditor` fact. -/
def surfacePowerEmergencyStake (freezeWindow : Time) : Power σ_ex :=
  charter_power "P.POST_EMERGENCY_STAKE" over σ_ex
    from_clause "TEN.3.1" : "An initiating party may trigger a brief preliminary freeze by posting a scaled emergency stake"
    held_by .anyone
    triggered_by (.act .postEmergencyStake)
    | valid_when (.holds .leased)
    | establishes [.emergencyStakePosted]
    | establishes_for [(.preliminaryFreeze, freezeWindow)]
    | establishes_by_actor [(.creditor, .initiatedByCreditor), (.creditor, .initiator .creditor)]

def manualPowerEmergencyStake (freezeWindow : Time) : Power σ_ex :=
  { id := "P.POST_EMERGENCY_STAKE"
    source := { clause := "TEN.3.1"
                text := "An initiating party may trigger a brief preliminary freeze by posting a scaled emergency stake"
                register := .norm
                meaning := ["P.POST_EMERGENCY_STAKE"] }
    holder := .anyone
    trigger := .act .postEmergencyStake
    valid := .holds .leased
    adds := [.emergencyStakePosted]
    addsFor := [(.preliminaryFreeze, freezeWindow)]
    addsByActor := [(.creditor, .initiatedByCreditor), (.creditor, .initiator .creditor)] }

theorem surfacePowerEmergencyStake_eq_manual (w : Time) :
    surfacePowerEmergencyStake w = manualPowerEmergencyStake w := rfl

/-- Power with time-bounded effects (`establishes_for`). -/
def surfacePowerSuspend (limit : Time) : Power σ_ex :=
  charter_power "P.SUSPEND" over σ_ex
    from_clause "TEN.3.3" : "Unconfirmed suspension is strictly time-limited"
    held_by (.only [.tribunal])
    triggered_by (.act .suspend)
    | valid_when (.and (.holds .preliminaryFreeze) (.holds .probableCause))
    | establishes_for [(.suspended, limit)]

def manualPowerSuspend (limit : Time) : Power σ_ex :=
  { id := "P.SUSPEND"
    source := { clause := "TEN.3.3"
                text := "Unconfirmed suspension is strictly time-limited"
                register := .norm
                meaning := ["P.SUSPEND"] }
    holder := .only [.tribunal]
    trigger := .act .suspend
    valid := .and (.holds .preliminaryFreeze) (.holds .probableCause)
    addsFor := [(.suspended, limit)] }

theorem surfacePowerSuspend_eq_manual (limit : Time) :
    surfacePowerSuspend limit = manualPowerSuspend limit := rfl

/-- Finding power establishing breach of a duty (`establishes_breach_of`) and
conditional facts (`cond_establishes`). -/
def surfacePowerFindUnlawfulEviction : Power σ_ex :=
  charter_power "P.FIND_UNLAWFUL_EVICTION" over σ_ex
    from_clause "TEN.4.1" : "A verified unlawful eviction by a landlord slashes the landlord's deposit"
    held_by (.only [.tribunal])
    triggered_by (.act .findUnlawfulEviction)
    | valid_when (.holds .leased)
    | establishes_breach_of "D.NO_EVICT"
    | cond_establishes [(.holds .landlordRelatedToCreditor, .directionPresumed)]

def manualPowerFindUnlawfulEviction : Power σ_ex :=
  { id := "P.FIND_UNLAWFUL_EVICTION"
    source := { clause := "TEN.4.1"
                text := "A verified unlawful eviction by a landlord slashes the landlord's deposit"
                register := .norm
                meaning := ["P.FIND_UNLAWFUL_EVICTION"] }
    holder := .only [.tribunal]
    trigger := .act .findUnlawfulEviction
    valid := .holds .leased
    condAdds := [(.holds .landlordRelatedToCreditor, .directionPresumed)]
    establishesBreachOf := some "D.NO_EVICT" }

theorem surfacePowerFindInterference_eq_manual :
    surfacePowerFindUnlawfulEviction = manualPowerFindUnlawfulEviction := rfl

def surfacePowerAffirmPC : Power σ_ex :=
  charter_power "P.AFFIRM_PC" over σ_ex
    from_clause "TEN.3.1" : "preliminary tribunal affirms probable cause"
    held_by (.only [.tribunal])
    triggered_by (.act .affirmProbableCause)
    | valid_when (.holds .preliminaryFreeze)
    | establishes [.probableCause]

def manualPowerAffirmPC : Power σ_ex :=
  { id := "P.AFFIRM_PC"
    source := { clause := "TEN.3.1"
                text := "preliminary tribunal affirms probable cause"
                register := .norm
                meaning := ["P.AFFIRM_PC"] }
    holder := .only [.tribunal]
    trigger := .act .affirmProbableCause
    valid := .holds .preliminaryFreeze
    adds := [.probableCause] }

theorem surfacePowerAffirmPC_eq_manual :
    surfacePowerAffirmPC = manualPowerAffirmPC := rfl

def surfacePowerOrderEviction : Power σ_ex :=
  charter_power "P.ORDER_EVICTION" over σ_ex
    from_clause "TEN.3.5" : "the tribunal may order eviction under the relocation rules"
    held_by (.only [.tribunal])
    triggered_by (.act .evict)
    | valid_when (.holds .suspended)
    | establishes [.evictedByTribunal]
    | extinguishes [.leased]

def manualPowerOrderEviction : Power σ_ex :=
  { id := "P.ORDER_EVICTION"
    source := { clause := "TEN.3.5"
                text := "the tribunal may order eviction under the relocation rules"
                register := .norm
                meaning := ["P.ORDER_EVICTION"] }
    holder := .only [.tribunal]
    trigger := .act .evict
    valid := .holds .suspended
    adds := [.evictedByTribunal]
    removes := [.leased] }

theorem surfacePowerOrderTermination_eq_manual :
    surfacePowerOrderEviction = manualPowerOrderEviction := rfl

def surfacePowerGiveNotice : Power σ_ex :=
  charter_power "P.GIVE_NOTICE" over σ_ex
    from_clause "TEN.2.1" : "after providing a contractual notice window"
    held_by (.only [.landlord])
    triggered_by (.act .giveNotice)
    | establishes [.noticeGiven]

def manualPowerGiveNotice : Power σ_ex :=
  { id := "P.GIVE_NOTICE"
    source := { clause := "TEN.2.1"
                text := "after providing a contractual notice window"
                register := .norm
                meaning := ["P.GIVE_NOTICE"] }
    holder := .only [.landlord]
    trigger := .act .giveNotice
    adds := [.noticeGiven] }

theorem surfacePowerGiveNotice_eq_manual :
    surfacePowerGiveNotice = manualPowerGiveNotice := rfl

/-- Zero-modifier power boundary test, plus `with_source` power modifier test. -/
def surfacePowerBare : Power σ_ex :=
  charter_power "P.BARE" over σ_ex
    from_clause "TEN.2.1" : "bare trigger"
    held_by .anyone
    triggered_by (.act .giveNotice)

theorem surfacePowerBare_eq_manual :
    surfacePowerBare =
      { id := "P.BARE"
        source := { clause := "TEN.2.1", text := "bare trigger", register := .norm, meaning := ["P.BARE"] }
        holder := .anyone
        trigger := .act .giveNotice } := rfl

def customPowerSpan : Span :=
  { clause := "TEN.2.1", text := "custom power span", register := .norm, meaning := ["P.CUSTOM"] }

def surfacePowerCustomSource : Power σ_ex :=
  charter_power "P.CUSTOM" over σ_ex
    from_clause "TEN.2.1" : "placeholder"
    held_by (.only [.landlord])
    triggered_by (.act .giveNotice)
    | with_source customPowerSpan

theorem surfacePowerCustomSource_eq_manual :
    surfacePowerCustomSource =
      { id := "P.CUSTOM"
        source := customPowerSpan
        holder := .only [.landlord]
        trigger := .act .giveNotice } := rfl

/-! ### 4.4 Immunity Surface Syntax Examples & Round-Trip Equivalence -/

def surfaceImmunityNoEvictionOverObjection : Immunity σ_ex :=
  charter_immunity "I.NO_EVICTION_OVER_OBJECTION" over σ_ex
    from_clause "TEN.3.5" : "Notwithstanding the preceding sentence, the tenant is not evicted over its objection"
    held_by (.only [.tenant])
    protected_against ["P.ORDER_EVICTION"]
    active_when (.and (.holds .hazardConfirmed) (.holds .tenantObjectsToEviction))
    | except_when (.holds .premisesUninhabitable)

def manualImmunityNoEvictionOverObjection : Immunity σ_ex :=
  { id := "I.NO_EVICTION_OVER_OBJECTION"
    source := { clause := "TEN.3.5"
                text := "Notwithstanding the preceding sentence, the tenant is not evicted over its objection"
                register := .norm
                meaning := ["I.NO_EVICTION_OVER_OBJECTION"] }
    holder := .only [.tenant]
    against := ["P.ORDER_EVICTION"]
    active := .and (.holds .hazardConfirmed) (.holds .tenantObjectsToEviction)
    unlessCond := .holds .premisesUninhabitable }

/-- Kernel-checked (`rfl`) round-trip proof: `charter_immunity` elaborates to the exact
underlying `Charter.Immunity` record. -/
theorem surfaceImmunity_eq_manual :
    surfaceImmunityNoEvictionOverObjection = manualImmunityNoEvictionOverObjection := rfl

/-- Zero-modifier unconditional immunity boundary test, plus `with_source` immunity modifier test. -/
def surfaceImmunityUnconditional : Immunity σ_ex :=
  charter_immunity "I.UNCOND" over σ_ex
    from_clause "TEN.3.5" : "unconditional immunity"
    held_by (.only [.tenant])
    protected_against ["P.ORDER_EVICTION"]
    active_when (.holds .leased)

theorem surfaceImmunityUnconditional_eq_manual :
    surfaceImmunityUnconditional =
      { id := "I.UNCOND"
        source := { clause := "TEN.3.5", text := "unconditional immunity", register := .norm, meaning := ["I.UNCOND"] }
        holder := .only [.tenant]
        against := ["P.ORDER_EVICTION"]
        active := .holds .leased
        unlessCond := .ff } := rfl

def customImmunitySpan : Span :=
  { clause := "TEN.3.5", text := "custom immunity span", register := .norm, meaning := ["I.CUSTOM"] }

def surfaceImmunityCustomSource : Immunity σ_ex :=
  charter_immunity "I.CUSTOM" over σ_ex
    from_clause "TEN.3.5" : "placeholder"
    held_by (.only [.tenant])
    protected_against ["P.ORDER_EVICTION"]
    active_when (.holds .leased)
    | with_source customImmunitySpan

theorem surfaceImmunityCustomSource_eq_manual :
    surfaceImmunityCustomSource =
      { id := "I.CUSTOM"
        source := customImmunitySpan
        holder := .only [.tenant]
        against := ["P.ORDER_EVICTION"]
        active := .holds .leased
        unlessCond := .ff } := rfl

/-! ### 4.5 End-to-End Law Assembly, Semantic Equivalence, General Theorems & Decided Scenarios -/

def surfaceLaw (noticeWindow bondDeadline freezeWindow suspendLimit : Time) : Law σ_ex :=
  { duties := [surfaceDutyNoEvict, surfaceDutyNotice noticeWindow, surfaceDutyDeposit bondDeadline]
    powers := [surfacePowerVacate, surfacePowerEmergencyStake freezeWindow,
               surfacePowerAffirmPC, surfacePowerSuspend suspendLimit,
               surfacePowerFindUnlawfulEviction, surfacePowerOrderEviction,
               surfacePowerGiveNotice]
    immunities := [surfaceImmunityNoEvictionOverObjection]
    init := [(.leased, 0, none)] }

def manualLaw (noticeWindow bondDeadline freezeWindow suspendLimit : Time) : Law σ_ex :=
  { duties := [manualDutyNoEvict, manualDutyNotice noticeWindow, manualDutyDeposit bondDeadline]
    powers := [manualPowerVacate, manualPowerEmergencyStake freezeWindow,
               manualPowerAffirmPC, manualPowerSuspend suspendLimit,
               manualPowerFindUnlawfulEviction, manualPowerOrderEviction,
               manualPowerGiveNotice]
    immunities := [manualImmunityNoEvictionOverObjection]
    init := [(.leased, 0, none)] }

/-- Full `Law` round-trip theorem: the law assembled from surface declarations
is definitionally equal (`rfl`) to the manually constructed `Law`. -/
theorem surfaceLaw_eq_manualLaw (nw bd fw sl : Time) :
    surfaceLaw nw bd fw sl = manualLaw nw bd fw sl := rfl

/-- Because `surfaceLaw` and `manualLaw` are definitionally equal, every
semantic function (`stateAfter`, `violations`, `Authorized`) is preserved identically. -/
theorem surfaceLaw_semantics_preserved (nw bd fw sl : Time) (tr : Trace σ_ex) :
    stateAfter (surfaceLaw nw bd fw sl) tr = stateAfter (manualLaw nw bd fw sl) tr ∧
    violations (surfaceLaw nw bd fw sl) tr = violations (manualLaw nw bd fw sl) tr ∧
    (Authorized (surfaceLaw nw bd fw sl) tr ↔ Authorized (manualLaw nw bd fw sl) tr) :=
  ⟨rfl, rfl, Iff.rfl⟩

/-- General theorem over `surfaceLaw` (quantified over all parameter values):
landlords and creditors have no institutional power to establish `.vacated`,
`.evictedByTribunal`, or `.suspended`. -/
theorem surfaceLaw_outsiders_disabled (nw bd fw sl : Time) :
    immuneFrom (surfaceLaw nw bd fw sl) .landlord .vacated = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .landlord .evictedByTribunal = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .landlord .suspended = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .creditor .vacated = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .creditor .evictedByTribunal = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .creditor .suspended = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-power `rfl` lookup lemma for `P.VACATE` in `surfaceLaw`. -/
theorem valid_surfacePowerVacate (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.VACATE" =
    (surfacePowerVacate.holder.mem e.who ls e.t &&
     surfacePowerVacate.trigger.matchesAct e &&
     surfacePowerVacate.valid.eval ls e.t && true) := rfl

/-- Per-power `rfl` lookup lemma for `P.SUSPEND` in `surfaceLaw`. -/
theorem valid_surfacePowerSuspend (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.SUSPEND" =
    ((surfacePowerSuspend sl).holder.mem e.who ls e.t &&
     (surfacePowerSuspend sl).trigger.matchesAct e &&
     (surfacePowerSuspend sl).valid.eval ls e.t && true) := rfl

/-- Per-power `rfl` lookup lemma for `P.ORDER_EVICTION` in `surfaceLaw`
(which carries the immunity condition from `I.NO_EVICTION_OVER_OBJECTION`). -/
theorem valid_surfacePowerOrderEviction (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.ORDER_EVICTION" =
    (surfacePowerOrderEviction.holder.mem e.who ls e.t &&
     surfacePowerOrderEviction.trigger.matchesAct e &&
     surfacePowerOrderEviction.valid.eval ls e.t &&
     !((surfaceImmunityNoEvictionOverObjection.active.eval ls e.t &&
        !surfaceImmunityNoEvictionOverObjection.unlessCond.eval ls e.t) || false)) := rfl

/-- General trace theorem over `surfaceLaw`: in any `Authorized` trace of
`surfaceLaw`, if an event at index `i` performs `.evict` while `.leased`
is active, then that event is a valid exercise of `"P.VACATE"` or `"P.ORDER_EVICTION"`. -/
theorem surfaceLaw_evict_only_by_power
    (nw bd fw sl : Time) (tr : Trace σ_ex) (hAuth : Authorized (surfaceLaw nw bd fw sl) tr)
    (i : Nat) (e : Event σ_ex) (hi : tr[i]? = some e)
    (hBound : (stateBefore (surfaceLaw nw bd fw sl) tr i).activeAt e.t .leased = true)
    (hAct : e.act = .evict) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.VACATE" = true ∨
    isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.ORDER_EVICTION" = true := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hAuth i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hNI := hc surfaceDutyNoEvict (by simp [surfaceLaw])
  rw [Bool.not_eq_true'] at hNI
  unfold breaches at hNI
  simp only [surfaceDutyNoEvict, Who.mem, dutyInForce, Cond.eval, hBound, Conduct.eval,
    List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
    hAct, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
  have hS : isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.SUSPEND" = false := by
    rw [valid_surfacePowerSuspend]
    simp [surfacePowerSuspend, Conduct.matchesAct, hAct]
  revert hNI hS
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.VACATE" <;>
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.SUSPEND" <;>
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.ORDER_EVICTION" <;>
  simp

/-- The law assembled from surface-syntax declarations is well-formed:
all cross-referenced IDs resolve, the override graph is acyclic, and IDs are unique. -/
theorem surfaceLaw_wellFormed : (surfaceLaw 10 5 3 20).wellFormed = true := by decide

/-- Reverse provenance holds across the surface-syntax law. -/
theorem surfaceLaw_reverseProvenance :
    let L := surfaceLaw 10 5 3 20
    reverseProvenanceWith [surfaceClauseTen21] L.spans (L.dutyIds ++ L.powerIds ++ L.immunityIds) = true := by
  decide

/-- Decided Scenario 1: Landlord unilaterally evicting a leased tenant breaches `D.NO_EVICT`
and leaves the institutional state unchanged. -/
theorem surfaceScenario_landlordEvictBreach :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [⟨1, .landlord, .evict⟩]
    violations L tr = [(0, "D.NO_EVICT")] ∧ stateAfter L tr = L.init := by
  decide

/-- Decided Scenario 2: Leased tenant exercising `P.VACATE` complies with `D.NO_EVICT`
and transitions institutional state from `.leased` to `.vacated`. -/
theorem surfaceScenario_tenantVacateLawful :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [⟨1, .tenant, .evict⟩]
    violations L tr = [] ∧
    (stateAfter L tr).has .vacated = true ∧
    (stateAfter L tr).has .leased = false := by
  decide

/-- Decided Scenario 3: Two-stage pause (emergency stake -> affirm PC -> suspend)
is lawful and establishes time-bounded `.suspended` which is active at `t = 10`
and expired at `t = 25`, as well as the parameterized `.initiator .creditor` fact. -/
theorem surfaceScenario_twoStageSuspendAndExpiry :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [
      ⟨1, .creditor, .postEmergencyStake⟩,
      ⟨2, .tribunal, .affirmProbableCause⟩,
      ⟨3, .tribunal, .suspend⟩
    ]
    let ls := stateAfter L tr
    violations L tr = [] ∧
    ls.has .initiatedByCreditor = true ∧
    ls.has (.initiator .creditor) = true ∧
    ls.activeAt 10 .suspended = true ∧
    ls.activeAt 25 .suspended = false := by
  decide

/-- Decided Scenario 4: Immunity `I.NO_EVICTION_OVER_OBJECTION` defeats
`P.ORDER_EVICTION` when `.hazardConfirmed` and `.tenantObjectsToEviction`
hold without `.premisesUninhabitable`. -/
theorem surfaceScenario_immunityDefeatsEviction :
    let L0 := surfaceLaw 10 5 3 20
    let L : Law σ_ex := { L0 with init := [
      (.leased, 0, none), (.suspended, 0, none),
      (.hazardConfirmed, 0, none), (.tenantObjectsToEviction, 0, none)
    ] }
    let e : Event σ_ex := ⟨1, .tribunal, .evict⟩
    let tr : Trace σ_ex := [e]
    isValidExerciseOf L L.init e "P.ORDER_EVICTION" = false ∧
    violations L tr = [(0, "D.NO_EVICT")] ∧
    (stateAfter L tr).has .leased = true := by
  decide

/-- Every role in `roleTable.all` round-trips through the automatically derived CLI string table. -/
theorem role_stringTable_roundtrip :
    (roleTable.all.all fun r => roleTable.ofString? (roleTable.toName r) == some r) = true := by
  decide

/-- Every action in `actionTable.all` round-trips through the automatically derived CLI string table. -/
theorem action_stringTable_roundtrip :
    (actionTable.all.all fun a => actionTable.ofString? (actionTable.toName a) == some a) = true := by
  decide

/-- Every fact in `factTable.all` (both parameterized `.initiator r` facts and nullary facts)
round-trips through the derived CLI string table. -/
theorem fact_stringTable_roundtrip :
    (factTable.all.all fun f => factTable.ofString? (factTable.toName f) == some f) = true := by
  decide

/-- Parameterized `PropFact.initiator` entries format as `"initiator.<role>"` and
round-trip by `rfl`. -/
theorem parameterized_fact_stringTable_lookup :
    factTable.toName (.initiator .creditor) = "initiator.creditor" ∧
    factTable.ofString? "initiator.creditor" = some (.initiator .creditor) ∧
    factTable.toName (.initiator .tenant) = "initiator.tenant" ∧
    factTable.ofString? "initiator.tenant" = some (.initiator .tenant) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `emptyRoleTable` (created with `charter_string_table Role []`) has an empty `all` list,
maps every role to `""`, and maps every string to `none`. -/
theorem empty_stringTable_behaves_correctly (r : Role) (s : String) :
    emptyRoleTable.all = [] ∧
    emptyRoleTable.names = [] ∧
    emptyRoleTable.toName r = "" ∧
    emptyRoleTable.ofString? s = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Unknown strings return `none` in the derived CLI string tables. -/
theorem unknown_string_returns_none :
    roleTable.ofString? "nonexistent_role" = none ∧
    actionTable.ofString? "nonexistent_act" = none ∧
    factTable.ofString? "nonexistent_fact" = none := by
  decide

/-- Unified definitional (`rfl`) round-trip equivalence theorem for `charter_clause`,
`charter_duty`, `charter_power`, `charter_immunity`, full `Law` assembly, and `charter_string_table`. -/
theorem surface_syntax_roundtrip (nw bd fw sl : Time) :
    surfaceClauseTen21 = manualClauseTen21 ∧
    surfaceClauseMultiRegister = manualClauseMultiRegister ∧
    surfaceClauseNonNormativeDefaults = manualClauseNonNormativeDefaults ∧
    surfaceClauseAutoSource = manualClauseAutoSource ∧
    surfaceDutyNoEvict = manualDutyNoEvict ∧
    surfaceDutyNotice nw = manualDutyNotice nw ∧
    surfaceDutyDeposit bd = manualDutyDeposit bd ∧
    surfacePowerVacate = manualPowerVacate ∧
    surfacePowerEmergencyStake fw = manualPowerEmergencyStake fw ∧
    surfacePowerSuspend sl = manualPowerSuspend sl ∧
    surfacePowerFindUnlawfulEviction = manualPowerFindUnlawfulEviction ∧
    surfacePowerAffirmPC = manualPowerAffirmPC ∧
    surfacePowerOrderEviction = manualPowerOrderEviction ∧
    surfacePowerGiveNotice = manualPowerGiveNotice ∧
    surfaceImmunityNoEvictionOverObjection = manualImmunityNoEvictionOverObjection ∧
    surfaceLaw nw bd fw sl = manualLaw nw bd fw sl ∧
    factTable.toName (.initiator .creditor) = "initiator.creditor" ∧
    factTable.ofString? "initiator.creditor" = some (.initiator .creditor) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples

export Examples (surface_syntax_roundtrip)

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

open Charter.Surface.Examples

def charterClauseExample : Clause :=
  charter_clause "TEN.2.1" from_text exTen21Source approved_hash 5922915569903263201 where
    | span_norm "Registered landlords must post a security deposit" => ["D.DEPOSIT"]
    | span_norm " and may end a tenancy only after providing a contractual notice window sufficient for the tenant to complete relocation" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def charterDutyExample : Duty σ_ex :=
  charter_duty "D.NO_EVICT" over σ_ex
    from_clause "TEN.2.2" : "No party may unilaterally evict or suspend a leased tenant outside the vacate procedure or tribunal suspension."
    owed_by .anyone
    owed_to (.only [.tenant])
    active_when (.holds .leased)
    demands (.forbid (.anyOf [.evict, .suspend]))
    | except_by_power ["P.VACATE", "P.SUSPEND", "P.ORDER_EVICTION"]
    | breach_by "P.FIND_UNLAWFUL_EVICTION"
    | with_remedies [.unlawfulEvictionEstablished, .landlordDepositSlashed, .restorationPermitted]

def charterPowerExample : Power σ_ex :=
  charter_power "P.VACATE" over σ_ex
    from_clause "TEN.5.1" : "Any leased tenant may at any time vacate the premises"
    held_by (.only [.tenant])
    triggered_by (.act .evict)
    | valid_when (.holds .leased)
    | establishes [.vacated]
    | extinguishes [.leased]

def charterImmunityExample : Immunity σ_ex :=
  charter_immunity "I.NO_EVICTION_OVER_OBJECTION" over σ_ex
    from_clause "TEN.3.5" : "Notwithstanding the preceding sentence, the tenant is not evicted over its objection"
    held_by (.only [.tenant])
    protected_against ["P.ORDER_EVICTION"]
    active_when (.and (.holds .hazardConfirmed) (.holds .tenantObjectsToEviction))
    | except_when (.holds .premisesUninhabitable)

charter_string_table charterRoleTableExample : Role [tenant, landlord, tribunal, creditor]

def charterInstitutionExample (nw bd fw sl : Time) : Law σ_ex :=
  charter_institution over σ_ex
    with_duties [charterDutyExample, surfaceDutyNotice nw, surfaceDutyDeposit bd]
    with_powers [charterPowerExample, surfacePowerEmergencyStake fw,
                 surfacePowerAffirmPC, surfacePowerSuspend sl,
                 surfacePowerFindUnlawfulEviction, surfacePowerOrderEviction,
                 surfacePowerGiveNotice]
    with_immunities [charterImmunityExample]
    with_init [(.leased, 0, none)]

/-- **Definitional Round-Trip Equivalence (`by rfl`) for `charter_*` Macros.**
Every `charter_*` surface declaration elaborates definitionally to the exact
underlying `Charter.Core` record. -/
theorem charter_surface_roundtrip (nw bd fw sl : Time) :
    charterClauseExample = manualClauseTen21 ∧
    charterDutyExample = manualDutyNoEvict ∧
    charterPowerExample = manualPowerVacate ∧
    charterImmunityExample = manualImmunityNoEvictionOverObjection ∧
    charterInstitutionExample nw bd fw sl = manualLaw nw bd fw sl ∧
    charterRoleTableExample.toName .tenant = "tenant" ∧
    charterRoleTableExample.ofString? "tenant" = some .tenant :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MacroRoundTrip

end Charter.Surface

namespace Charter

export Charter.Surface (
  shortCtorName
  StringTable
  OntologyTables
  surface_syntax_roundtrip
  charter_surface_roundtrip
)

end Charter
