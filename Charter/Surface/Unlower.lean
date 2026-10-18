import Charter.Core.Composition
import Charter.Surface.Lower

/-!
# Charter.Surface.Unlower — From a Lean Law Back to a `.charter` Document

The inverse of `Charter.Surface.Lower` for programs that were first written as Lean
records: given naming functions for a signature, a `Law σ` and its clauses are turned
into a `Charter.Dsl.Doc`, which `Charter.Dsl.render` prints as `.charter` text.

This is how an existing Lean formalization is exported to the DSL once; afterwards the
`.charter` file is the program and the Lean side proves, by `decide`, that lowering it
reproduces the original law (`Law.lift emb L = lowerLaw doc env`).

Parameter names are recovered by *sentinels*: evaluate the Lean law at a parameter
record whose every field holds a distinct power of two far above any real literal
(`sentinelValue i`), and give the exporter the sentinel → name table. A number is
then decoded greedily into the sentinels it contains plus a literal remainder, so
both `p` and `p + q` (+ constant) are recovered; re-lowering with the real defaults
yields the real law.
-/

namespace Charter.Dsl

open Charter

/-- How to spell the constructors of a signature in the DSL. -/
structure Naming (σ : Sig) where
  actor : σ.Actor → String
  act   : σ.Act → String
  fact  : σ.Fact → FactRef

/-- Document-level data that is not derivable from the law itself. -/
structure ExportSpec (σ : Sig) where
  id           : String
  title        : String
  document     : Option String := none
  contract     : Option String := none
  defaultActor : Option String := none
  roles        : List σ.Actor
  acts         : List σ.Act
  /-- Every fact instance (the signature's fact table). -/
  facts        : List σ.Fact
  /-- Default parameter values, in the order the `params` block should list them. -/
  params       : List (String × Nat) := []
  /-- Sentinel value → parameter name. -/
  sentinels    : List (Nat × String) := []
  regimes      : List Regime := []
  modules      : List ModuleUse := []

/-- The `i`-th sentinel value: `2^(24+i)`. -/
def sentinelValue (i : Nat) : Nat := 2 ^ (24 + i)

/-- Greedy decomposition of `n` into sentinels (largest first) and a remainder. -/
def unlowerNumGo (sent : List (Nat × String)) (n : Nat) (acc : Option NumE) : NumE :=
  match sent with
  | [] =>
    match acc with
    | none => .lit n
    | some e => if n == 0 then e else .add e (.lit n)
  | (v, p) :: rest =>
    if v ≤ n then
      let e : NumE := match acc with | none => .param p | some e => .add e (.param p)
      unlowerNumGo rest (n - v) (some e)
    else unlowerNumGo rest n acc

/-- Print a number, naming the parameters it was computed from. `sent` must be
sorted by decreasing sentinel value. -/
def unlowerNum (sent : List (Nat × String)) (n : Nat) : NumE :=
  if n < sentinelValue 0 then .lit n else unlowerNumGo sent n none

/-- Fact declarations from a list of fact references: one per name, marked as
role-taking when any reference carries an argument. -/
def factDeclsOf (refs : List FactRef) : List FactDecl :=
  refs.foldl (fun acc f =>
    if acc.any (·.name == f.name) then acc else acc ++ [⟨f.name, f.arg.isSome⟩]) []

def unlowerWho {σ : Sig} (nm : Naming σ) (roles : List σ.Actor) : Who σ → WhoE
  | .anyone => .anyone
  | .only xs => .only (xs.map nm.actor)
  | .except xs => .except (xs.map nm.actor)
  | .tagged ps =>
    let pairs := ps.map fun (a, f) => (nm.actor a, nm.fact f)
    -- `tagged f` shorthand when the pairs are exactly every role tagged by `f(role)`
    match pairs.head? with
    | some (_, FactRef.mk fname (some _)) =>
      if pairs == roles.map (fun r => (nm.actor r, (⟨fname, some (nm.actor r)⟩ : FactRef)))
      then .taggedAll fname else .tagged pairs
    | _ => .tagged pairs

def unlowerCond {σ : Sig} (nm : Naming σ) (sent : List (Nat × String)) : Cond σ → CondE
  | .tt => .tt
  | .ff => .ff
  | .holds f => .holds (nm.fact f)
  | .heldFor f d => .heldFor (nm.fact f) (unlowerNum sent d)
  | .countGe f n => .countGe (nm.fact f) (unlowerNum sent n)
  | .countAtLeast f g => .countAtLeast (nm.fact f) (nm.fact g)
  | .not c => .not (unlowerCond nm sent c)
  | .and a b => .and (unlowerCond nm sent a) (unlowerCond nm sent b)
  | .or a b => .or (unlowerCond nm sent a) (unlowerCond nm sent b)

def unlowerConduct {σ : Sig} (nm : Naming σ) : Conduct σ → ConductE
  | .act a => .act (nm.act a)
  | .anyOf as => .anyOf (as.map nm.act)
  | .exerciseOf p => .exerciseOf p
  | .not c => .not (unlowerConduct nm c)
  | .and a b => .and (unlowerConduct nm a) (unlowerConduct nm b)
  | .or a b => .or (unlowerConduct nm a) (unlowerConduct nm b)

def unlowerDemand {σ : Sig} (nm : Naming σ) (sent : List (Nat × String)) : Demand σ → DemandE
  | .forbid c => .forbid (unlowerConduct nm c)
  | .require c w => .require (unlowerConduct nm c) (unlowerNum sent w)

def unlowerSource (id : String) (sp : Span) : SourceE :=
  { clause := sp.clause, text := sp.text, register := sp.register
    meaning := if sp.meaning == [id] then none else some sp.meaning }

def unlowerClause (c : Clause) : ClauseE :=
  let spans : List SpanE := c.spans.map fun sp => { register := sp.register, text := sp.text, meaning := sp.meaning }
  let concat := c.spans.foldl (fun acc sp => acc ++ sp.text) ""
  { id := c.id
    text := if concat == c.source then none else some c.source
    approved := if c.approvedHash == 0 then none else some c.approvedHash.toNat
    spans := spans }

def unlowerDuty {σ : Sig} (nm : Naming σ) (roles : List σ.Actor) (sent : List (Nat × String))
    (d : Duty σ) : DutyE :=
  { id := d.id
    source := unlowerSource d.id d.source
    bearer := unlowerWho nm roles d.bearer
    beneficiary := unlowerWho nm roles d.beneficiary
    active := unlowerCond nm sent d.active
    demand := unlowerDemand nm sent d.demand
    unlessCond := unlowerCond nm sent d.unlessCond
    unlessPower := d.unlessPower
    overriddenBy := d.overriddenBy
    breachBy := d.breachEstablishedBy
    remedies := d.remedies.map nm.fact }

def unlowerPower {σ : Sig} (nm : Naming σ) (roles : List σ.Actor) (sent : List (Nat × String))
    (p : Power σ) : PowerE :=
  { id := p.id
    source := unlowerSource p.id p.source
    holder := unlowerWho nm roles p.holder
    trigger := unlowerConduct nm p.trigger
    valid := unlowerCond nm sent p.valid
    adds := p.adds.map nm.fact
    addsFor := p.addsFor.map fun (f, t) => (nm.fact f, unlowerNum sent t)
    addsByActor := p.addsByActor.map fun (a, f) => (nm.actor a, nm.fact f)
    removes := p.removes.map nm.fact
    condAdds := p.condAdds.map fun (c, f) => (unlowerCond nm sent c, nm.fact f)
    establishesBreachOf := p.establishesBreachOf }

def unlowerImmunity {σ : Sig} (nm : Naming σ) (roles : List σ.Actor) (sent : List (Nat × String))
    (i : Immunity σ) : ImmunityE :=
  { id := i.id
    source := unlowerSource i.id i.source
    holder := unlowerWho nm roles i.holder
    against := i.against
    active := unlowerCond nm sent i.active
    unlessCond := unlowerCond nm sent i.unlessCond }

/-- Export a Lean law and its clauses as a `.charter` document. Initial facts are
assumed to be established at time 0 without expiry, as the DSL's `init` means. -/
def unlower {σ : Sig} (spec : ExportSpec σ) (nm : Naming σ) (L : Law σ) (clauses : List Clause) : Doc :=
  { id := spec.id
    title := spec.title
    document := spec.document
    contract := spec.contract
    defaultActor := spec.defaultActor
    roles := spec.roles.map nm.actor
    acts := spec.acts.map nm.act
    facts := factDeclsOf (spec.facts.map nm.fact)
    params := spec.params
    regimes := spec.regimes
    init := L.init.map fun (f, _, _) => nm.fact f
    modules := spec.modules
    clauses := clauses.map unlowerClause
    duties := L.duties.map (unlowerDuty nm spec.roles spec.sentinels)
    powers := L.powers.map (unlowerPower nm spec.roles spec.sentinels)
    immunities := L.immunities.map (unlowerImmunity nm spec.roles spec.sentinels) }

/-- The embedding of a Lean signature into the dynamic signature induced by a naming. -/
def embeddingOf {σ : Sig} (nm : Naming σ) : SigEmbedding σ σ_dyn :=
  { mapActor := fun a => ⟨nm.actor a⟩
    mapAct := fun a => ⟨nm.act a⟩
    mapFact := fun f => lowerFact (nm.fact f) }

end Charter.Dsl
