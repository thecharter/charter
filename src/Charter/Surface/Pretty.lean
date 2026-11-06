import Charter.Surface.Parser

/-!
# Charter.Surface.Pretty — Canonical AST Formatter and Round-Trip Validator

Formats parsed `Charter.Item` sequences into canonical, deterministic Charter source text
and verifies round-trip AST equivalence (`parseSource (formatItems items)` reproduces the
exact same `Directive` and `Phrase` structures, `docs/spec/020_grammar.md`).
-/

namespace Charter.Pretty

def fmtAtomOrStr (s : String) : String :=
  let chars := s.toList
  match chars with
  | c :: rest =>
    if c.isUpper && (c :: rest).all Lexer.isAtomChar && !Lexer.wordKeywords.contains s && s != "Duration" then s
    else showString s
  | [] => "\"\""

def fmtVars (xs : List Var) : String :=
  ", ".intercalate (xs.map toString)

def wrapUnary (t : Term) (rendered : String) : String :=
  match t with
  | .ref _ | .app _ _ | .intLit _ | .stringLit _ | .boolLit _
  | .present _ | .violated _ | .enabled _ | .project _ _ | .tag _ _ => rendered
  | _ => "(" ++ rendered ++ ")"

def wrapPostfixBase (t : Term) (rendered : String) : String :=
  match t with
  | .ref x => if x.dom.contains ' ' && !x.dom.startsWith "[" then "(" ++ rendered ++ ")" else rendered
  | .app _ _ | .project _ _ | .tag _ _ => rendered
  | _ => "(" ++ rendered ++ ")"

def fmtProjField (x : Var) : String :=
  if x.dom.contains ' ' && !x.dom.startsWith "[" then "(" ++ toString x ++ ")" else toString x

mutual

def fmtTerm : Term → String
  | .not t => "!" ++ wrapUnary t (fmtTerm t)
  | .and a b => "(" ++ fmtTerm a ++ " && " ++ fmtTerm b ++ ")"
  | .or a b => "(" ++ fmtTerm a ++ " || " ++ fmtTerm b ++ ")"
  | .boolLit b => if b then "True" else "False"
  | .leq a b => "(" ++ fmtTerm a ++ " <= " ++ fmtTerm b ++ ")"
  | .geq a b => "(" ++ fmtTerm a ++ " >= " ++ fmtTerm b ++ ")"
  | .ge a b => "(" ++ fmtTerm a ++ " > " ++ fmtTerm b ++ ")"
  | .le a b => "(" ++ fmtTerm a ++ " < " ++ fmtTerm b ++ ")"
  | .sub a b => "(" ++ fmtTerm a ++ " - " ++ fmtTerm b ++ ")"
  | .add a b => "(" ++ fmtTerm a ++ " + " ++ fmtTerm b ++ ")"
  | .mult a b => "(" ++ fmtTerm a ++ " * " ++ fmtTerm b ++ ")"
  | .mod a b => "(" ++ fmtTerm a ++ " % " ++ fmtTerm b ++ ")"
  | .div a b => "(" ++ fmtTerm a ++ " / " ++ fmtTerm b ++ ")"
  | .intLit i => if i < 0 then s!"(0 - {-i})" else toString i
  | .stringLit s => fmtAtomOrStr s
  | .eq a b => "(" ++ fmtTerm a ++ " == " ++ fmtTerm b ++ ")"
  | .neq a b => "(" ++ fmtTerm a ++ " != " ++ fmtTerm b ++ ")"
  | .exists_ xs t => "(Exists " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .forall_ xs t => "(Forall " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .count xs t => "Count(Foreach " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .sum xs t => "Sum(Foreach " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .max xs t => "Max(Foreach " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .min xs t => "Min(Foreach " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"
  | .when t c => "(" ++ fmtTerm t ++ " When " ++ fmtTerm c ++ ")"
  | .present t => "Holds(" ++ fmtTerm t ++ ")"
  | .violated t => "Violated(" ++ fmtTerm t ++ ")"
  | .enabled t => "Enabled(" ++ fmtTerm t ++ ")"
  | .project t x => wrapPostfixBase t (fmtTerm t) ++ "." ++ fmtProjField x
  | .tag t d => wrapPostfixBase t (fmtTerm t) ++ ":" ++ d
  | .untag t => fmtTerm t
  | .ref x => toString x
  | .app d args => d ++ "(" ++ fmtArgs args ++ ")"
  | .currentTime => "Current Time"
  | .heldFor t d => "(Held(" ++ fmtTerm t ++ ") For (" ++ fmtTerm d ++ "))"

def fmtArgs : Args → String
  | .pos ts => fmtTermList ts
  | .named ms => fmtNamedMods ms

def fmtTermList : List Term → String
  | [] => ""
  | [t] => fmtTerm t
  | t :: ts => fmtTerm t ++ ", " ++ fmtTermList ts

def fmtNamedMods : List (Var × Term) → String
  | [] => ""
  | [(x, t)] => toString x ++ " = " ++ fmtTerm t
  | (x, t) :: ms => toString x ++ " = " ++ fmtTerm t ++ ", " ++ fmtNamedMods ms

end

def fmtOptForeach (xs : List Var) (t : Term) : String :=
  if xs.isEmpty then fmtTerm t
  else "(Foreach " ++ fmtVars xs ++ ": " ++ fmtTerm t ++ ")"

def fmtDomain : Domain → String
  | .anyString => "String"
  | .anyInt => "Int"
  | .time => "Time"
  | .duration => "Duration"
  | .strings [] => "'z'..'a'"
  | .strings ss => ", ".intercalate (ss.map fmtAtomOrStr)
  | .ints [] => "1..0"
  | .ints is =>
    -- Negative ints cannot appear directly in `Identified by` lists
    ", ".intercalate (is.map toString)
  | .products [] => "()"
  | .products xs => " * ".intercalate (xs.map toString)

def fmtDerivation : Derivation → String
  | .dv xs t => "Derived from " ++ fmtOptForeach xs t
  | .holdsWhen t => "Holds when " ++ fmtTerm t

def fmtEffect : Effect → String
  | .cAll xs t none => "Creates " ++ fmtOptForeach xs t
  | .cAll xs t (some d) => "Creates " ++ fmtOptForeach xs t ++ " For " ++ fmtTerm d
  | .tAll xs t => "Terminates " ++ fmtOptForeach xs t
  | .oAll xs t => "Obfuscates " ++ fmtOptForeach xs t

def fmtModClause : ModClause → String
  | .conditionedBy [] => "Conditioned by"
  | .conditionedBy ts => "Conditioned by " ++ fmtTermList ts
  | .derivation [] => ""
  | .derivation ds@(.dv _ _ :: _) =>
    "Derived from " ++ ", ".intercalate (ds.map fun
      | .dv xs t => fmtOptForeach xs t
      | .holdsWhen t => fmtTerm t)
  | .derivation ds@(.holdsWhen _ :: _) =>
    "Holds when " ++ ", ".intercalate (ds.map fun
      | .holdsWhen t => fmtTerm t
      | .dv xs t => fmtOptForeach xs t)
  | .postCond [] => ""
  | .postCond effs@(.cAll .. :: _) =>
    "Creates " ++ ", ".intercalate (effs.map fun
      | .cAll xs t none => fmtOptForeach xs t
      | .cAll xs t (some d) => fmtOptForeach xs t ++ " For " ++ fmtTerm d
      | .tAll xs t => fmtOptForeach xs t
      | .oAll xs t => fmtOptForeach xs t)
  | .postCond effs@(.tAll .. :: _) =>
    "Terminates " ++ ", ".intercalate (effs.map fun
      | .tAll xs t => fmtOptForeach xs t
      | _ => "")
  | .postCond effs@(.oAll .. :: _) =>
    "Obfuscates " ++ ", ".intercalate (effs.map fun
      | .oAll xs t => fmtOptForeach xs t
      | _ => "")
  | .sync ss => "Syncs with " ++ ", ".intercalate (ss.map fun s => fmtOptForeach s.xs s.t)
  | .violation ts => "Violated when " ++ fmtTermList ts
  | .enforcingActs as => "Enforced by " ++ ", ".intercalate as
  | .terminatedBy as => "Terminated by " ++ ", ".intercalate as
  | .createdBy as => "Created by " ++ ", ".intercalate as
  | .overriddenBy ds => "Overridden by " ++ ", ".intercalate ds
  | .strings [] => "Domain 'z'..'a'"
  | .strings ss => "Domain " ++ ", ".intercalate (ss.map fmtAtomOrStr)
  | .ints [] => "Domain 1..0"
  | .ints is => "Domain " ++ ", ".intercalate (is.map toString)
  | .close => "Closed"
  | .open => "Open"
  | .validWhen ts => "Valid when " ++ fmtTermList ts
  | .exceptUnder as => "Except under " ++ ", ".intercalate as
  | .against as => "Against " ++ ", ".intercalate as
  | .unlessCond ts => "Unless " ++ fmtTermList ts
  | .dueWithin d => "Due within " ++ fmtTerm d
  | .fromSpan cid txt => "From " ++ cid ++ " " ++ showString txt

def fmtModClauses (indent : String) (cls : List ModClause) : String :=
  let rendered := (cls.map fmtModClause).filter (!·.isEmpty)
  if rendered.isEmpty then ""
  else "\n" ++ "\n".intercalate (rendered.map (indent ++ ·))

def fmtRegister : Register → String
  | .norm => "Norm"
  | .definition => "Definition"
  | .invariant => "Invariant"
  | .acceptance => "Acceptance"
  | .commentary => "Commentary"

def fmtClauseBlock (indent : String) (c : Clause) : String :=
  let app := if c.approvedHash == 0 then "" else s!" Approved {c.approvedHash}"
  let txtLine := s!"{indent}  Text {showString c.source}"
  let spanLines := c.spans.map fun s =>
    let ids := if s.meaning.isEmpty then "" else " => " ++ ", ".intercalate s.meaning
    s!"{indent}  {fmtRegister s.register} {showString s.text}{ids}"
  "\n".intercalate ((s!"{indent}Clause {c.id}{app}") :: txtLine :: spanLines)

def stripPhysicalDefault : List ModClause → List ModClause
  | .derivation [.holdsWhen (.boolLit true)] :: rest => rest
  | cls => cls

def extractInvariantForm : List ModClause → Option (Term × List (ClauseId × String))
  | .derivation [.holdsWhen t] :: rest =>
    let rec takeFroms : List ModClause → Option (List (ClauseId × String))
      | [] => some []
      | .fromSpan c s :: more => (takeFroms more).map ((c, s) :: ·)
      | _ => none
    (takeFroms rest).map (fun fs => (t, fs))
  | _ => none

def fmtTypeDeclAndExt (indent : String) (d : DomId) (t : TypeSpec) (cls : List ModClause) : String :=
  let openPrefix := if t.closed == some false then "Open " else ""
  let wherePart := if reprStr t.domainConstraint == reprStr (Term.boolLit true) then "" else " Where " ++ fmtTerm t.domainConstraint
  let childIndent := indent ++ "  "
  match t.kind with
  | .fact f =>
    if f.invariant && t.domain == .products [] && reprStr t.domainConstraint == reprStr (Term.boolLit true) && t.closed.isNone then
      match extractInvariantForm cls with
      | some (cond, fs) =>
        let fromStr := String.join (fs.map fun (c, s) => s!"\n{childIndent}From {c} {showString s}")
        s!"{indent}Invariant {d} When {fmtTerm cond}{fromStr}"
      | none =>
        s!"{indent}{openPrefix}Bool {d}{fmtModClauses childIndent cls}"
    else if t.restriction.isNone && t.domain == .products [] && reprStr t.domainConstraint == reprStr (Term.boolLit true) then
      s!"{indent}{openPrefix}Bool {d}{fmtModClauses childIndent cls}"
    else
      let kw := match t.restriction with
        | some .var => "Var"
        | some .function => "Function"
        | none => "Fact"
      let domPart := if t.domain == .anyString then "" else " Identified by " ++ fmtDomain t.domain
      s!"{indent}{openPrefix}{kw} {d}{domPart}{wherePart}{fmtModClauses childIndent cls}"
  | .act a =>
    let comps := match t.domain with | .products xs => xs | _ => []
    if a.physical then
      let (actorPart, relPart) := match comps with
        | actV :: objs =>
          let ap := if actV == (⟨"actor", ""⟩ : Var) then "" else " Actor " ++ toString actV
          let rp := if objs.isEmpty then "" else " Related to " ++ fmtVars objs
          (ap, rp)
        | [] => ("", "")
      let cls' := stripPhysicalDefault cls
      s!"{indent}Physical {d}{actorPart}{relPart}{wherePart}{fmtModClauses childIndent cls'}"
    else
      let (actorPart, recipPart, relPart) := match comps with
        | actV :: rest =>
          let ap := if actV == (⟨"actor", ""⟩ : Var) then "" else " Actor " ++ toString actV
          if a.hasRecipient then
            match rest with
            | r :: objs => (ap, " Recipient " ++ toString r, if objs.isEmpty then "" else " Related to " ++ fmtVars objs)
            | [] => (ap, "", "")
          else
            (ap, "", if rest.isEmpty then "" else " Related to " ++ fmtVars rest)
        | [] => ("", "", "")
      s!"{indent}{openPrefix}Act {d}{actorPart}{recipPart}{relPart}{wherePart}{fmtModClauses childIndent cls}"
  | .event _ =>
    let objs := match t.domain with | .products xs => xs | _ => []
    let relPart := if objs.isEmpty then "" else " Related to " ++ fmtVars objs
    s!"{indent}{openPrefix}Event {d}{relPart}{wherePart}{fmtModClauses childIndent cls}"
  | .duty _ =>
    let comps := match t.domain with | .products xs => xs | _ => []
    match comps with
    | h :: c :: objs =>
      let relPart := if objs.isEmpty then "" else " Related to " ++ fmtVars objs
      s!"{indent}{openPrefix}Duty {d} Holder {h} Claimant {c}{relPart}{wherePart}{fmtModClauses childIndent cls}"
    | _ => s!"{indent}{openPrefix}Duty {d}{wherePart}{fmtModClauses childIndent cls}"
  | .immunity _ =>
    let comps := match t.domain with | .products xs => xs | _ => []
    match comps with
    | h :: objs =>
      let relPart := if objs.isEmpty then "" else " Related to " ++ fmtVars objs
      s!"{indent}{openPrefix}Immunity {d} Holder {h}{relPart}{wherePart}{fmtModClauses childIndent cls}"
    | [] => s!"{indent}{openPrefix}Immunity {d}{wherePart}{fmtModClauses childIndent cls}"

def fmtDecls (indent : String) : Nat → List Decl → List String
  | 0, _ => []
  | _, [] => []
  | fuel + 1, .typeDecl d t :: .typeExt d' cls _ :: rest =>
    if d == d' then
      fmtTypeDeclAndExt indent d t cls :: fmtDecls indent fuel rest
    else
      fmtTypeDeclAndExt indent d t [] :: fmtDecls indent fuel (.typeExt d' cls :: rest)
  | fuel + 1, .typeDecl d t :: rest =>
    fmtTypeDeclAndExt indent d t [] :: fmtDecls indent fuel rest
  | fuel + 1, .typeExt d cls extKind :: rest =>
    (s!"{indent}Extend {extKind} {d}{fmtModClauses (indent ++ "  ") cls}") :: fmtDecls indent fuel rest
  | fuel + 1, .placeholder f t :: rest =>
    s!"{indent}Placeholder {f} For {t}" :: fmtDecls indent fuel rest
  | fuel + 1, .clause c :: rest =>
    fmtClauseBlock indent c :: fmtDecls indent fuel rest
  | fuel + 1, .document p :: rest =>
    s!"{indent}Document {showString p}" :: fmtDecls indent fuel rest
  | fuel + 1, .param name dom value :: rest =>
    let tyPart := match dom with
      | .time => " : Time"
      | .duration => " : Duration"
      | _ => ""
    s!"{indent}Param {name}{tyPart} = {value}" :: fmtDecls indent fuel rest
  | fuel + 1, .module name params body :: rest =>
    let inner := fmtDecls (indent ++ "  ") fuel body
    let bodyStr := if inner.isEmpty then "" else "\n" ++ (".\n").intercalate inner ++ "."
    s!"{indent}Module {name}({", ".intercalate params}) \{{bodyStr}\n{indent}}" :: fmtDecls indent fuel rest
  | fuel + 1, .use name args pre :: rest =>
    let asPart := match pre with | some p => s!" As {p}" | none => ""
    s!"{indent}Use {name}({", ".intercalate args}){asPart}" :: fmtDecls indent fuel rest

mutual

def fmtPhrase (indent : String) : Nat → Phrase → String
  | 0, _ => ""
  | _, .trigger xs t => indent ++ fmtOptForeach xs t
  | _, .create xs t => indent ++ "+" ++ fmtOptForeach xs t
  | _, .terminate xs t => indent ++ "-" ++ fmtOptForeach xs t
  | _, .obfuscate xs t => indent ++ "~" ++ fmtOptForeach xs t
  | _, .query t => indent ++ "?" ++ fmtTerm t
  | _, .instQuery false xs t => indent ++ "?-" ++ fmtOptForeach xs t
  | _, .instQuery true xs t => indent ++ "?--" ++ fmtOptForeach xs t
  | fuel + 1, .decls ds => "\n".intercalate (fmtDecls indent (ds.length + fuel + 16) ds)
  | fuel + 1, .par ps =>
    let lines := fmtPhrasesDot (indent ++ "  ") fuel ps
    s!"{indent}\{\n{lines}\n{indent}}"
  | fuel + 1, .scenario name ps spans =>
    let nameStr := fmtAtomOrStr name
    let fromStr := String.join (spans.map fun (c, s) => s!"\n{indent}  From {c} {showString s}")
    let body := fmtScenarioBody (indent ++ "  ") fuel ps
    s!"{indent}Scenario {nameStr}{fromStr} \{\n{body}\n{indent}}"
  | _, .expect w neg t => indent ++ s!"?{if neg then "!" else ""}{w.name} {fmtTerm t}"
  | _, .setTime t => indent ++ s!"@ {fmtTerm t}"
  | _, .tick => indent ++ "tick"
  | _, .why t => indent ++ s!"?why {fmtTerm t}"

def fmtPhrasesDot (indent : String) : Nat → List Phrase → String
  | 0, _ => ""
  | _, [] => ""
  | fuel + 1, [p] => fmtPhrase indent fuel p ++ "."
  | fuel + 1, p :: ps => fmtPhrase indent fuel p ++ ".\n" ++ fmtPhrasesDot indent fuel ps

def fmtScenarioBody (indent : String) : Nat → List Phrase → String
  | 0, _ => ""
  | _, [] => ""
  | fuel + 1, [.par ps] => fmtPhrase indent fuel (.par ps)
  | fuel + 1, [p] => fmtPhrase indent fuel p ++ "."
  | fuel + 1, .par ps :: rest => fmtPhrase indent fuel (.par ps) ++ "\n" ++ fmtScenarioBody indent fuel rest
  | fuel + 1, p :: rest => fmtPhrase indent fuel p ++ ".\n" ++ fmtScenarioBody indent fuel rest

end

/-- Format top-level items into canonical Charter source. -/
def formatItems (items : List Item) : String :=
  let blocks := items.map fun it =>
    match it.val with
    | .inl (.include p) => s!"#include {showString p}."
    | .inl (.require p) => s!"#require {showString p}."
    | .inr (.par ps) => fmtPhrase "" 4096 (.par ps)
    | .inr (.scenario name ps spans) => fmtPhrase "" 4096 (.scenario name ps spans)
    | .inr p => fmtPhrase "" 4096 p ++ "."
  "\n\n".intercalate blocks ++ "\n"

/-- Normalized structural projection of an `Item` (ignoring `Pos` and first-line `text`). -/
def itemDataRepr (items : List Item) : String :=
  reprStr (items.map (·.val))

/-- Format source text and verify round-trip AST preservation before returning. -/
def formatAndVerify (src : String) : Except Diagnostic String := do
  let items ← parseSource src
  let formatted := formatItems items
  let reparsed ← parseSource formatted
  if itemDataRepr items == itemDataRepr reparsed then
    return formatted
  else
    throw (Diagnostic.error "CHR003"
      "internal formatter round-trip mismatch: formatted source re-parsed to a different AST")

end Charter.Pretty
