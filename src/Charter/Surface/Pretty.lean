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
  | .evStatus want t => want.kwName ++ "(" ++ fmtTerm t ++ ")"
  | .hasConflict t => "Conflict(" ++ fmtTerm t ++ ")"
  | .mulDivRound x n d m => "MulDivRound(" ++ fmtTerm x ++ ", " ++ fmtTerm n ++ ", " ++ fmtTerm d ++ ", " ++ m.kwName ++ ")"
  | .fnApp d k => d ++ "(" ++ fmtTerm k ++ ")"

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
  | .money cur sc => s!"Money({cur}, {sc})"
  | .quantity unit => s!"Quantity({unit})"
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
  | .defeasibleDAG _ _ => ""

def fmtEffect : Effect → String
  | .cAll xs t none _ => "Creates " ++ fmtOptForeach xs t
  | .cAll xs t (some d) _ => "Creates " ++ fmtOptForeach xs t ++ " For " ++ fmtTerm d
  | .tAll xs t _ => "Terminates " ++ fmtOptForeach xs t
  | .oAll xs t _ => "Obfuscates " ++ fmtOptForeach xs t
  | .evOp .support xs t _ => "Supports " ++ fmtOptForeach xs t
  | .evOp .rebut xs t _ => "Rebuts " ++ fmtOptForeach xs t
  | .evOp .retract xs t _ => "Retracts " ++ fmtOptForeach xs t
  | .evOp .retractSupport xs t _ => "Retracts " ++ fmtOptForeach xs t
  | .evOp .retractRebut xs t _ => "Retracts !" ++ fmtOptForeach xs t
  | .findingOp pol _ t std =>
    s!"Resolves {if pol then "" else "!"}{fmtTerm t}" ++ (if std == "default" then "" else s!" Standard {fmtAtomOrStr std}")
  | .amendOp _ => ""

def fmtModClause : ModClause → String
  | .conditionedBy [] => "Conditioned by"
  | .conditionedBy ts => "Conditioned by " ++ fmtTermList ts
  | .derivation [] => ""
  | .derivation ds@(.dv _ _ :: _) =>
    "Derived from " ++ ", ".intercalate (ds.map fun
      | .dv xs t => fmtOptForeach xs t
      | .holdsWhen t => fmtTerm t
      | .defeasibleDAG _ _ => "")
  | .derivation ds@(.holdsWhen _ :: _) =>
    "Holds when " ++ ", ".intercalate (ds.map fun
      | .holdsWhen t => fmtTerm t
      | .dv xs t => fmtOptForeach xs t
      | .defeasibleDAG _ _ => "")
  | .derivation (.defeasibleDAG _ _ :: _) => ""
  | .postCond [] => ""
  | .postCond effs@(.cAll .. :: _) =>
    "Creates " ++ ", ".intercalate (effs.map fun
      | .cAll xs t none _ => fmtOptForeach xs t
      | .cAll xs t (some d) _ => fmtOptForeach xs t ++ " For " ++ fmtTerm d
      | .tAll xs t _ => fmtOptForeach xs t
      | .oAll xs t _ => fmtOptForeach xs t
      | .evOp _ xs t _ => fmtOptForeach xs t
      | .findingOp _ xs t _ => fmtOptForeach xs t
      | .amendOp _ => "")
  | .postCond effs@(.tAll .. :: _) =>
    "Terminates " ++ ", ".intercalate (effs.map fun
      | .tAll xs t _ => fmtOptForeach xs t
      | _ => "")
  | .postCond effs@(.oAll .. :: _) =>
    "Obfuscates " ++ ", ".intercalate (effs.map fun
      | .oAll xs t _ => fmtOptForeach xs t
      | _ => "")
  | .postCond (eff :: _) => fmtEffect eff
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
  | .fromSpan cid txt => if txt.isEmpty then "From " ++ cid else "From " ++ cid ++ " " ++ showString txt
  | .evidenced => ""
  | .confidential [] => "Confidential"
  | .confidential auds => "Confidential To " ++ ", ".intercalate auds
  | .resolves pol t => "Resolves " ++ (if pol then "" else "!") ++ fmtTerm t
  | .decides tgt cnd => s!"Decides {fmtTerm tgt} When {fmtTerm cnd}"
  | .standard s => "Standard " ++ fmtAtomOrStr s
  | .evEffect op ts src? =>
    let kw := match op with
      | .support => "Supports "
      | .rebut => "Rebuts "
      | .retract | .retractSupport => "Retracts "
      | .retractRebut => "Retracts !"
    kw ++ ", ".intercalate (ts.map fun (xs, t) => fmtOptForeach xs t)
      ++ (match src? with | some b => " By " ++ fmtTerm b | none => "")
  | .defeasibleRule r =>
    let head := if r.isDefault then s!"Default {r.id}"
      else s!"Exception {r.id} Overrides {", ".intercalate r.overrides}"
    let body := match r.conseq with
      | .holdsBool true => "Holds when " ++ fmtTerm r.cond
      | .holdsBool false => "Rejects when " ++ fmtTerm r.cond
      | .yieldsVal v => "Yields (" ++ fmtTerm v ++ ") When " ++ fmtTerm r.cond
    head ++ " " ++ body
  | .priorityEdge hi los => s!"Priority {hi} Over {", ".intercalate los}"
  | .repeals rs => s!"Repeals {", ".intercalate rs}"
  | .protects ps => s!"Protects {", ".intercalate ps}"
  | .protectsClauses cids => s!"Protects Clause {", ".intercalate cids}"
  | .entrenched => ""
  | .presumed b => s!"Presumed {if b then "True" else "False"}"
  | .excusedWhen ts => "Excused when " ++ fmtTermList ts
  | .overridesDuties targets =>
    "Overrides " ++ ", ".intercalate (targets.map fun (d, args?) =>
      match args? with | none => d | some a => fmtTerm (.app d a))
  | .decidedBy v wf num den vf =>
    let wPart := match wf with | some w => s!" Weighted by {w}" | none => ""
    s!"Decided by {v}{wPart} At least {num}/{den} In {vf}"

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

def takeSpanInits : List Decl → List Term × List Decl
  | .spanInit t :: rest =>
    let (ts, rem) := takeSpanInits rest
    (t :: ts, rem)
  | ds => ([], ds)

def renderSpanMeaning (m : List String) (inits : List Term) : String × List Term :=
  let step (acc : List String × List Term) (id : String) : List String × List Term :=
    let (outRev, rem) := acc
    match rem.findIdx? (fun | .app d _ => d == id | _ => false) with
    | some idx =>
      match rem[idx]? with
      | some tm => (fmtTerm tm :: outRev, rem.eraseIdx idx)
      | none => (id :: outRev, rem)
    | none => (id :: outRev, rem)
  let (revStrs, rem') := m.foldl step ([], inits)
  (if revStrs.isEmpty then "" else " => " ++ ", ".intercalate revStrs.reverse, rem')

def fmtClauseBlockWithInits (indent : String) (c : Clause) (inits : List Term) : String :=
  let inDoc := match c.docId with | some id => s!" In {id}" | none => ""
  let app := match c.approvedSha256 with
    | some hex => s!" Approved {showString hex}"
    | none => if c.approvedHash == 0 then "" else s!" Approved {c.approvedHash}"
  if c.byRef then
    match c.spans with
    | [s] =>
      let regPart := match s.register with
        | .norm => ""
        | .commentary => if s.meaning.isEmpty then "" else " Commentary"
        | r => " " ++ fmtRegister r
      let (ids, _) := renderSpanMeaning s.meaning inits
      s!"{indent}Clause {c.id}{inDoc}{app}{regPart}{ids}"
    | _ => s!"{indent}Clause {c.id}{inDoc}{app}"
  else
    let (spanLinesRev, _) := c.spans.foldl (fun (acc, rem) s =>
      let (ids, rem') := renderSpanMeaning s.meaning rem
      (s!"{indent}  {fmtRegister s.register} {showString s.text}{ids}" :: acc, rem')) ([], inits)
    let spanLines := spanLinesRev.reverse
    let joinedMatches := String.join (c.spans.map (·.text)) == c.source && !c.spans.isEmpty
    let bodyLines := if joinedMatches then spanLines else (s!"{indent}  Text {showString c.source}") :: spanLines
    "\n".intercalate ((s!"{indent}Clause {c.id}{inDoc}{app}") :: bodyLines)

def fmtClauseBlock (indent : String) (c : Clause) : String :=
  fmtClauseBlockWithInits indent c []

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
    let factPrefix := if f.evidenced then "Evidenced " else if f.isInput then "Input " else openPrefix
    if f.invariant && t.domain == .products [] && reprStr t.domainConstraint == reprStr (Term.boolLit true) && t.closed.isNone then
      let entPref := if f.entrenched then "Entrenched " else ""
      match extractInvariantForm cls with
      | some (cond, fs) =>
        let fromStr := String.join (fs.map fun (c, s) => s!"\n{childIndent}From {c} {showString s}")
        s!"{indent}{entPref}Invariant {d} When {fmtTerm cond}{fromStr}"
      | none =>
        s!"{indent}{factPrefix}Bool {d}{fmtModClauses childIndent cls}"
    else if t.restriction.isNone && t.domain == .products [] && reprStr t.domainConstraint == reprStr (Term.boolLit true) then
      s!"{indent}{factPrefix}Bool {d}{fmtModClauses childIndent cls}"
    else
      let kw := match t.restriction with
        | some .var => "Var"
        | some .function => "Function"
        | none => "Fact"
      let domPart := if t.domain == .anyString then "" else " Identified by " ++ fmtDomain t.domain
      s!"{indent}{factPrefix}{kw} {d}{domPart}{wherePart}{fmtModClauses childIndent cls}"
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
      let kw := if a.isFinding then "Finding" else if a.isAmend then "Amend" else if a.isPower then "Power" else "Act"
      s!"{indent}{openPrefix}{kw} {d}{actorPart}{recipPart}{relPart}{wherePart}{fmtModClauses childIndent cls}"
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
  | .immunity im =>
    let kw := if im.isProtection then "Protection" else "Immunity"
    let cls' := if im.isProtection then cls.map (fun
      | .against as => .against as -- rendered below via `For` when `isProtection`
      | c => c) else cls
    let comps := match t.domain with | .products xs => xs | _ => []
    let clauseStr := if im.isProtection then
      let rendered := (cls'.map fun
        | .against as => "For " ++ ", ".intercalate as
        | c => fmtModClause c).filter (!·.isEmpty)
      if rendered.isEmpty then "" else "\n" ++ "\n".intercalate (rendered.map (childIndent ++ ·))
    else fmtModClauses childIndent cls'
    match comps with
    | h :: objs =>
      let relPart := if objs.isEmpty then "" else " Related to " ++ fmtVars objs
      s!"{indent}{openPrefix}{kw} {d} Holder {h}{relPart}{wherePart}{clauseStr}"
    | [] => s!"{indent}{openPrefix}{kw} {d}{wherePart}{clauseStr}"

def fmtTemporalFormula : TemporalFormula → String
  | .always phi => "Always " ++ fmtTerm phi
  | .alwaysNext a b => "Always (" ++ fmtTerm a ++ " => Next " ++ fmtTerm b ++ ")"
  | .alwaysEventually a b => "Always (" ++ fmtTerm a ++ " => Eventually " ++ fmtTerm b ++ ")"
  | .alwaysEventuallyWithin d a b => "Always (" ++ fmtTerm a ++ " => EventuallyWithin (" ++ fmtTerm d ++ ") " ++ fmtTerm b ++ ")"
  | .until_ a b => "Until(" ++ fmtTerm a ++ ", " ++ fmtTerm b ++ ")"
  | .weakUntil a b => "WeakUntil(" ++ fmtTerm a ++ ", " ++ fmtTerm b ++ ")"

def fmtDecls (indent : String) : Nat → List Decl → List String
  | 0, _ => []
  | _, [] => []
  | fuel + 1, .typeDecl d t :: .typeExt d' cls _ :: .amendInstall d'' body :: rest =>
    if d == d' && d == d'' then
      let base := fmtTypeDeclAndExt indent d t cls
      let inner := fmtDecls (indent ++ "    ") fuel body
      let instPart := if inner.isEmpty then "" else s!"\n{indent}  Installs \{\n" ++ (".\n").intercalate inner ++ s!".\n{indent}  }"
      (base ++ instPart) :: fmtDecls indent fuel rest
    else
      fmtTypeDeclAndExt indent d t [] :: fmtDecls indent fuel (.typeExt d' cls "Act" :: .amendInstall d'' body :: rest)
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
    let (inits, rest') := takeSpanInits rest
    fmtClauseBlockWithInits indent c inits :: fmtDecls indent fuel rest'
  | fuel + 1, .document p docId? sha? rank? :: rest =>
    let idPart := match docId? with | some id => s!" {id}" | none => ""
    let shaPart := match sha? with | some h => s!" SHA256 {showString h}" | none => ""
    let rankPart := match rank? with | some r => s!" Rank {r}" | none => ""
    s!"{indent}Document{idPart} {showString p}{shaPart}{rankPart}" :: fmtDecls indent fuel rest
  | fuel + 1, .param name dom value :: rest =>
    let tyPart := match dom with
      | .time => " : Time"
      | .duration => " : Duration"
      | .money cur sc => s!" : Money({cur}, {sc})"
      | .quantity unit => s!" : Quantity({unit})"
      | _ => ""
    s!"{indent}Param {name}{tyPart} = {value}" :: fmtDecls indent fuel rest
  | fuel + 1, .module name params body :: rest =>
    let inner := fmtDecls (indent ++ "  ") fuel body
    let bodyStr := if inner.isEmpty then "" else "\n" ++ (".\n").intercalate inner ++ "."
    s!"{indent}Module {name}({", ".intercalate params}) \{{bodyStr}\n{indent}}" :: fmtDecls indent fuel rest
  | fuel + 1, .use name args pre sps :: rest =>
    let asPart := match pre with | some p => s!" As {p}" | none => ""
    let fromPart := String.join (sps.map fun (c, s) => if s.isEmpty then s!" From {c}" else s!" From {c} {showString s}")
    s!"{indent}Use {name}({", ".intercalate args}){asPart}{fromPart}" :: fmtDecls indent fuel rest
  | fuel + 1, .spanInit t :: rest =>
    -- emitted alongside its `Clause` during initial parsing; rendered as no-op standalone decl if orphaned
    let _ := t
    fmtDecls indent fuel rest
  | fuel + 1, .property tp :: rest =>
    let assPart := if tp.assumptions.isEmpty then "" else " Assumes " ++ ", ".intercalate tp.assumptions
    let fromPart := String.join (tp.spans.map fun (c, s) => if s.isEmpty then s!"\n{indent}  From {c}" else s!"\n{indent}  From {c} {showString s}")
    s!"{indent}Property {tp.name}{assPart} When {fmtTemporalFormula tp.formula}{fromPart}" :: fmtDecls indent fuel rest
  | fuel + 1, .amendInstall actId body :: rest =>
    let inner := fmtDecls (indent ++ "    ") fuel body
    let bodyStr := if inner.isEmpty then "" else "\n" ++ (".\n").intercalate inner ++ "."
    s!"{indent}Extend Amend {actId}\n{indent}  Installs \{{bodyStr}\n{indent}  }" :: fmtDecls indent fuel rest
  | fuel + 1, .regime r :: rest =>
    let rows := r.params.map fun (k, v) => s!"{indent}  {k} = {v}"
    let bodyStr := if rows.isEmpty then "" else "\n" ++ (",\n").intercalate rows ++ "\n" ++ indent
    s!"{indent}Regime {fmtAtomOrStr r.name} \{{bodyStr}}" :: fmtDecls indent fuel rest
  | fuel + 1, .amendProcedure conds :: rest =>
    s!"{indent}Amend Procedure Valid when {fmtTermList conds}" :: fmtDecls indent fuel rest
  | fuel + 1, .amountDef name dom? e :: rest =>
    let tyPart := match dom? with
      | some .time => " : Time"
      | some .duration => " : Duration"
      | some (.money cur sc) => s!" : Money({cur}, {sc})"
      | some (.quantity unit) => s!" : Quantity({unit})"
      | some .anyInt => " : Int"
      | _ => ""
    s!"{indent}Amount {name}{tyPart} Is {fmtTerm e}" :: fmtDecls indent fuel rest

mutual

def fmtPhrase (indent : String) : Nat → Phrase → String
  | 0, _ => ""
  | _, .trigger xs t none => indent ++ fmtOptForeach xs t
  | _, .trigger xs t (some note) => indent ++ fmtOptForeach xs t ++ " Note " ++ showString note
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
  | _, .submitEvidence pol t src =>
    let byPart := if src.isEmpty then "" else " By " ++ showString src
    indent ++ s!"SubmitEvidence {if pol then "" else "!"}{fmtTerm t}{byPart}"
  | _, .retractEvidence t src =>
    let byPart := if src.isEmpty then "" else " By " ++ showString src
    indent ++ s!"RetractEvidence {fmtTerm t}{byPart}"

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
