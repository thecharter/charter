import Charter.Core.Syntax
import Charter.Core.Semantics
import Charter.Core.Provenance
import Charter.Surface.Syntax
import Charter.Surface.Dsl

/-!
# Charter.Surface.Lower — Meaning of a `.charter` Document

A `Charter.Dsl.Doc` is given meaning by lowering it to a `Charter.Law` over the
*dynamic signature* `σ_dyn`, whose actors and acts are declared names and whose
facts are declared names optionally applied to a role. Every projection, view,
explanation, and semantic theorem of the language is polymorphic in the signature,
so a lowered program enjoys all of them with no Lean written by its author.

Lowering is total on validated documents and is written with nothing but structural
recursion over lists and strings, so it reduces inside the kernel: a theorem about a
`.charter` program (well-formedness, provenance, or equality with a hand-written Lean
law) is proved by `decide` on `lowerLaw doc env`.

Parameters: a document's `params` block gives default values; `lowerLaw doc env` takes
the environment explicitly so that a regime (`Doc.regimeEnv`) or a Lean-side parameter
record can be substituted for the defaults.
-/

namespace Charter.Dsl

open Charter Charter.Surface

/-! ## 1. The Dynamic Signature -/

/-- A declared actor or act name. -/
structure Atom where
  name : String
  deriving DecidableEq, BEq, Inhabited, Hashable

instance : Repr Atom := ⟨fun a _ => Std.Format.text a.name⟩
instance : ToString Atom := ⟨(·.name)⟩

/-- A declared fact, optionally applied to a role: `initiator(agent)`. -/
structure DynFact where
  name : String
  arg  : Option String := none
  deriving DecidableEq, BEq, Inhabited, Hashable

def DynFact.render : DynFact → String
  | ⟨n, none⟩ => n
  | ⟨n, some a⟩ => s!"{n}({a})"

instance : Repr DynFact := ⟨fun f _ => Std.Format.text f.render⟩
instance : ToString DynFact := ⟨DynFact.render⟩

/-- The signature every `.charter` program is lowered to. -/
def σ_dyn : Sig := { Actor := Atom, Act := Atom, Fact := DynFact }

instance : Repr σ_dyn.Actor := inferInstanceAs (Repr Atom)
instance : Repr σ_dyn.Act   := inferInstanceAs (Repr Atom)
instance : Repr σ_dyn.Fact  := inferInstanceAs (Repr DynFact)

/-! ## 2. Environments -/

/-- Parameter environment: name → value. -/
abbrev Env := List (String × Nat)

def Env.lookup (env : Env) (name : String) : Nat :=
  match env.find? (·.1 == name) with
  | some (_, v) => v
  | none => 0

/-- Default environment of a document. -/
def Doc.env (d : Doc) : Env := d.params

/-- Environment of a regime: the defaults with the regime's bindings substituted. -/
def Doc.regimeEnv (d : Doc) (r : Regime) : Env :=
  d.params.map fun (n, v) =>
    match r.params.find? (·.1 == n) with
    | some (_, v') => (n, v')
    | none => (n, v)

/-! ## 3. Lowering -/

def lowerNum (env : Env) : NumE → Nat
  | .lit n => n
  | .param p => env.lookup p
  | .add a b => lowerNum env a + lowerNum env b

def lowerFact (f : FactRef) : DynFact := ⟨f.name, f.arg⟩

def lowerWho (roles : List String) : WhoE → Who σ_dyn
  | .anyone => .anyone
  | .only xs => .only (xs.map Atom.mk)
  | .except xs => .except (xs.map Atom.mk)
  | .tagged ps => .tagged (ps.map fun (r, f) => (⟨r⟩, lowerFact f))
  | .taggedAll f => .tagged (roles.map fun r => (⟨r⟩, ⟨f, some r⟩))

def lowerCond (env : Env) : CondE → Cond σ_dyn
  | .tt => .tt
  | .ff => .ff
  | .holds f => .holds (lowerFact f)
  | .heldFor f d => .heldFor (lowerFact f) (lowerNum env d)
  | .countGe f n => .countGe (lowerFact f) (lowerNum env n)
  | .countAtLeast f g => .countAtLeast (lowerFact f) (lowerFact g)
  | .not c => .not (lowerCond env c)
  | .and a b => .and (lowerCond env a) (lowerCond env b)
  | .or a b => .or (lowerCond env a) (lowerCond env b)

def lowerConduct : ConductE → Conduct σ_dyn
  | .act a => .act ⟨a⟩
  | .anyOf as => .anyOf (as.map Atom.mk)
  | .exerciseOf p => .exerciseOf p
  | .not c => .not (lowerConduct c)
  | .and a b => .and (lowerConduct a) (lowerConduct b)
  | .or a b => .or (lowerConduct a) (lowerConduct b)

def lowerDemand (env : Env) : DemandE → Demand σ_dyn
  | .forbid c => .forbid (lowerConduct c)
  | .require c w => .require (lowerConduct c) (lowerNum env w)

/-- The source span of a rule; an omitted `meaning` defaults to the rule's own id. -/
def lowerSource (id : String) (s : SourceE) : Span :=
  { clause := s.clause, text := s.text, register := s.register, meaning := s.meaning.getD [id] }

def ClauseE.concat (c : ClauseE) : String :=
  c.spans.foldl (fun acc sp => acc ++ sp.text) ""

def lowerClause (c : ClauseE) : Clause :=
  { id := c.id
    source := c.text.getD c.concat
    approvedHash := UInt64.ofNat (c.approved.getD 0)
    spans := c.spans.map fun sp =>
      { clause := c.id, text := sp.text, register := sp.register, meaning := sp.meaning } }

def lowerDuty (roles : List String) (env : Env) (d : DutyE) : Duty σ_dyn :=
  { id := d.id
    source := lowerSource d.id d.source
    bearer := lowerWho roles d.bearer
    beneficiary := lowerWho roles d.beneficiary
    active := lowerCond env d.active
    demand := lowerDemand env d.demand
    unlessCond := lowerCond env d.unlessCond
    unlessPower := d.unlessPower
    overriddenBy := d.overriddenBy
    breachEstablishedBy := d.breachBy
    remedies := d.remedies.map lowerFact }

def lowerPower (roles : List String) (env : Env) (p : PowerE) : Power σ_dyn :=
  { id := p.id
    source := lowerSource p.id p.source
    holder := lowerWho roles p.holder
    trigger := lowerConduct p.trigger
    valid := lowerCond env p.valid
    adds := p.adds.map lowerFact
    addsFor := p.addsFor.map fun (f, n) => (lowerFact f, lowerNum env n)
    addsByActor := p.addsByActor.map fun (r, f) => (⟨r⟩, lowerFact f)
    removes := p.removes.map lowerFact
    condAdds := p.condAdds.map fun (c, f) => (lowerCond env c, lowerFact f)
    establishesBreachOf := p.establishesBreachOf }

def lowerImmunity (roles : List String) (env : Env) (i : ImmunityE) : Immunity σ_dyn :=
  { id := i.id
    source := lowerSource i.id i.source
    holder := lowerWho roles i.holder
    against := i.against
    active := lowerCond env i.active
    unlessCond := lowerCond env i.unlessCond }

/-- The law of a document under a parameter environment. -/
def lowerLaw (d : Doc) (env : Env) : Law σ_dyn :=
  { duties := d.duties.map (lowerDuty d.roles env)
    powers := d.powers.map (lowerPower d.roles env)
    immunities := d.immunities.map (lowerImmunity d.roles env)
    init := d.init.map fun f => (lowerFact f, 0, none) }

/-- The clauses of a document. -/
def lowerClauses (d : Doc) : List Clause := d.clauses.map lowerClause

/-! ## 4. String Tables for the Dynamic Signature -/

def atomTable (names : List String) : StringTable Atom :=
  { all := names.map Atom.mk
    toName := (·.name)
    ofString? := fun s => if names.contains s then some ⟨s⟩ else none }

/-- Every fact instance of a document: nullary facts, and each role-taking fact
applied to every role. -/
def Doc.allFacts (d : Doc) : List DynFact :=
  d.facts.flatMap fun f =>
    if f.takesRole then d.roles.map fun r => ⟨f.name, some r⟩ else [⟨f.name, none⟩]

/-- Parse `name`, `name(role)`, or the legacy dotted form `name.role`. -/
def parseFactName (d : Doc) (s : String) : Option DynFact :=
  let cs := s.data
  let base := String.mk (cs.takeWhile (· != '('))
  let rest := cs.dropWhile (· != '(')
  let candidate : DynFact :=
    match rest with
    | '(' :: more => ⟨base, some (String.mk (more.takeWhile (· != ')')))⟩
    | _ =>
      -- dotted fallback: `name.role` when `name` takes a role
      let rev := cs.reverse
      let argRev := rev.takeWhile (· != '.')
      let baseRev := rev.dropWhile (· != '.')
      match baseRev with
      | '.' :: b =>
        let b' := String.mk b.reverse
        match d.facts.find? (·.name == b') with
        | some decl => if decl.takesRole then ⟨b', some (String.mk argRev.reverse)⟩ else ⟨s, none⟩
        | none => ⟨s, none⟩
      | _ => ⟨s, none⟩
  if d.allFacts.contains candidate then some candidate else none

def factTable (d : Doc) : StringTable DynFact :=
  { all := d.allFacts
    toName := DynFact.render
    ofString? := parseFactName d }

def tables (d : Doc) : OntologyTables σ_dyn :=
  { actors := atomTable d.roles, acts := atomTable d.acts, facts := factTable d }

/-! ## 5. A Lowered Program -/

/-- Everything the tooling needs about a document, at its default parameters. -/
structure Lowered where
  doc     : Doc
  law     : Law σ_dyn
  clauses : List Clause
  tables  : OntologyTables σ_dyn

def lower (d : Doc) : Lowered :=
  { doc := d, law := lowerLaw d d.env, clauses := lowerClauses d, tables := tables d }

def Lowered.roles (p : Lowered) : List Atom := p.doc.roles.map Atom.mk

/-- Default actor for `prompt`: the declared one, else the first role. -/
def Lowered.defaultActor (p : Lowered) : Atom :=
  ⟨(p.doc.defaultActor.getD (p.doc.roles.headD "")) ⟩

end Charter.Dsl
