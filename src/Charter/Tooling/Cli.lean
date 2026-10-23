import Charter.Core.Semantics
import Charter.Core.Views
import Charter.Core.Explain
import Charter.Core.Ratchet
import Charter.Projection.Veil
import Charter.Projection.Prompt
import Charter.Projection.ContractABI
import Charter.Projection.Visualization
import Charter.Surface.Syntax
import Charter.Surface.Lower
import Lean.Data.Json
import Charter.Cli.Test
import Charter.Cli.Repl

/-!
# Charter.Tooling.Cli — Program-Agnostic Command-Line Harness

The `charter` executable is a thin shell over this module. It knows nothing about
any particular institution: every program written in Charter registers itself by
building a `Charter.Cli.Program` descriptor (its law, clauses, string tables,
sample traces, parameter regimes, and an optional program-specific world
simulator), and `Charter.Cli.run` dispatches the subcommands over whichever
programs the executable was linked with.

Generic subcommand implementations (`checkGeneric`, `viewsGeneric`, `veilGeneric`,
`evalGeneric`, `explainGeneric`, `promptGeneric`, `abiGeneric`, `diffGeneric`,
`exploreGeneric`) work for any `Law σ`; a program only has to supply its data.
The `verify` subcommand prints `languageLedger` (guarantees of the language and
standard library) followed by each registered program's own ledger.

Programs written in the `.charter` language need no registration at all: any
argument ending in `.charter` is parsed, validated, lowered (`Charter.Dsl.lower`),
and wrapped in a `Program` by `Program.ofLowered`, so every subcommand runs on it
directly (`charter check my-institution.charter`).
-/

namespace Charter.Cli

open Charter Lean

/-- `(name, status, description)` row of a verification ledger. -/
abbrev LedgerEntry := String × String × String

/-! ## 1. Scenario Files -/

/-- Parse one `{"t": _, "who": _, "act": _}` event using a program's string tables. -/
def parseEventWith {σ : Sig} (tables : Charter.Surface.OntologyTables σ) (j : Json) :
    Except String (Event σ) := do
  let t ← (j.getObjValAs? Nat "t")
  let who ← j.getObjValAs? String "who"
  let act ← j.getObjValAs? String "act"
  let w ← match tables.actors.ofString? who with
    | some w => pure w | none => throw s!"unknown party {who}"
  let a ← match tables.acts.ofString? act with
    | some a => pure a | none => throw s!"unknown act {act}"
  pure ⟨t, w, a⟩

/-- Parse a scenario file `{"init": [...facts], "events": [...]}` into a law (with the
extra initial facts) and a trace. -/
def parseScenarioWith {σ : Sig} (tables : Charter.Surface.OntologyTables σ) (baseLaw : Law σ)
    (path : System.FilePath) : IO (Law σ × Trace σ) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let evs ← IO.ofExcept (j.getObjValAs? (Array Json) "events")
  let tr ← IO.ofExcept (evs.toList.mapM (parseEventWith tables))
  let extra := match j.getObjValAs? (Array String) "init" with
    | .ok xs => xs.toList.filterMap tables.facts.ofString?
    | .error _ => []
  pure ({ baseLaw with init := baseLaw.init ++ extra.map (·, 0, none) }, tr)

/-- Read the optional `"institution"` key of a scenario file, naming the program it is
written for. -/
def scenarioInstitution? (path : System.FilePath) : IO (Option String) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error _ => pure none
  | .ok j =>
    match j.getObjValAs? String "institution" with
    | .ok id => pure (some id)
    | .error _ => pure none

def status (b : Bool) : String := if b then "ok  " else "FAIL"

/-! ## 2. Generic Subcommand Implementations -/

/-- `check`: structure, lexical/normative/reverse provenance, verbatim occurrence in
the authoritative document, and approval staleness. -/
def checkGeneric {σ : Sig} (L : Law σ) (baseClauses : List Clause) (docPath : String)
    (english? : Option System.FilePath) : IO Unit := do
  IO.println s!"{status L.wellFormed} well-formed (ids resolve, precedence acyclic)"
  let cs ← match english? with
    | none => pure baseClauses
    | some p => do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
      pure <| baseClauses.map fun c => match j.getObjValAs? String c.id with
        | .ok txt => { c with source := txt }
        | .error _ => c
  for c in cs do
    IO.println s!"{status c.covered} {c.id}: spans reproduce source exactly"
    IO.println s!"{status c.normsInterpreted} {c.id}: every norm span has a formal meaning"
  IO.println s!"{status (reverseProvenanceWith cs L.spans (L.dutyIds ++ L.powerIds))} every duty/power is named by some English span"
  let doc? ← try some <$> IO.FS.readFile docPath catch _ => pure none
  match doc? with
  | none => IO.println s!"WARN {docPath} not found; verbatim check skipped"
  | some doc =>
    for c in cs do
      IO.println s!"{status ((doc.splitOn c.source).length > 1)} {c.id}: source text occurs verbatim in the authoritative document"
  for c in cs do
    if c.stale then
      if c.approvedHash == 0 then
        IO.println s!"STALE {c.id}: not yet approved. Once reviewed, declare `approved {c.source.hash}`. Unapproved: {c.invalidated}."
      else
        IO.println s!"STALE {c.id}: English differs from the approved text (current hash {c.source.hash}). Review invalidated for {c.invalidated}."
    else
      IO.println s!"ok   {c.id}: approved mapping current"

/-- `views`: legal, per-actor, and operational views. -/
def viewsGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (actors : List σ.Actor) : IO Unit := do
  IO.println "== Legal view =="; IO.println L.legalView
  for p in actors do
    IO.println s!"\n== Agent view: {rs p} =="; IO.println (L.agentView p)
  IO.println "\n== Operational view =="; IO.println L.operationalView

/-- `veil`: Veil 2.0 transition-system & safety specification. -/
def veilGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact] (L : Law σ) : IO Unit := do
  IO.println (Charter.renderVeil L)

/-- `eval`: institutional consequences of a scenario history. -/
def evalGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (tables : Charter.Surface.OntologyTables σ) (baseLaw : Law σ) (path : System.FilePath) : IO Unit := do
  let (L, tr) ← parseScenarioWith tables baseLaw path
  IO.println (evalTrace L tr)

/-- `explain`: counterfactual compliance & validity explanation for one proposed event. -/
def explainGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (tables : Charter.Surface.OntologyTables σ) (baseLaw : Law σ)
    (who act : String) (path? : Option System.FilePath) : IO Unit := do
  let (L, tr) ← match path? with
    | some p => parseScenarioWith tables baseLaw p
    | none => pure (baseLaw, [])
  let now : Nat := (tr.foldl (fun m e => max m e.t) 0) + 1
  let e ← IO.ofExcept (parseEventWith tables (Json.mkObj [("t", toJson now), ("who", toJson who), ("act", toJson act)]))
  IO.println (explain L tr e).render

/-- `prompt`: AI constitutional system prompt, alignment card, and synthetic training rows. -/
def promptGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (title : String) (tables : Charter.Surface.OntologyTables σ) (L : Law σ)
    (defaultActor : σ.Actor) (sampleEvents : List (Event σ)) (actor? : Option String) : IO Unit := do
  let actor ← match actor? with
    | none => pure defaultActor
    | some s =>
      match tables.actors.ofString? s with
      | some a => pure a
      | none =>
        let known := tables.actors.all.map tables.actors.toName
        throw (IO.userError s!"unknown actor '{s}' for {title}; known: {known}")
  IO.println (renderSystemPrompt title L actor)
  let rows := generateTrainingDataset L L.init sampleEvents
  IO.println "## 5. Synthetic Normative Training Dataset (JSON)"
  IO.println (renderTrainingDatasetJson rows)

/-- `abi`: smart-contract state-transition guard in Solidity and/or JSON ABI. -/
def abiGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (contractName : String) (L : Law σ) (fmt? : Option String) : IO Unit := do
  match fmt? with
  | some "json" =>
    IO.println (renderContractJsonABI contractName L)
  | some "solidity" | none =>
    IO.println (renderSolidityGuard contractName L)
  | some "both" | some "all" =>
    IO.println (renderSolidityGuard contractName L)
    IO.println "\n// == JSON ABI =="
    IO.println (renderContractJsonABI contractName L)
  | some other =>
    throw (IO.userError s!"unknown ABI format '{other}'; expected 'solidity', 'json', or 'both'")

/-- `diff`: amendment diff between two law versions plus an annotated sample timeline. -/
def diffGeneric {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L_old L_new : Law σ) (cs_old cs_new : List Clause) (sampleTrace : Trace σ) : IO Unit := do
  let d := diffLaws L_old L_new cs_old cs_new
  IO.println (renderLawDiff d)
  IO.println (renderAnnotatedTimeline L_old sampleTrace)

/-- `explore`: parameter-space sweep & bilateral ratchet verification table. -/
def exploreGeneric {P : Type} {σ : Sig}
    (title : String) (R : RatchetSpec P σ) (lawOf : P → Law σ)
    (baseline : P) (candidates : List (String × P)) : IO Unit := do
  IO.println s!"== Parameter Space & Bilateral Ratchet Exploration: {title} =="
  let rows := sweepParameterGrid R lawOf baseline candidates
  IO.println (renderSweepTable rows)
  let admCount := (rows.filter (fun (_, cal, rat, core) => cal && rat && core)).length
  IO.println s!"\nSummary: {admCount}/{rows.length} candidate parameter regimes admissible under bilateral ratchet & entrenched core."

/-- `sim` for programs that have no quantitative world simulator of their own: falls
back to normative evaluation of the scenario. -/
def simNormativeOnly {σ : Sig} [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (tables : Charter.Surface.OntologyTables σ) (baseLaw : Law σ)
    (path? : Option System.FilePath) : IO Unit := do
  match path? with
  | none => IO.println "(this program registers no world simulations)"
  | some p => evalGeneric tables baseLaw p

/-- Parse and validate a `.charter` file, or fail with its errors. -/
def loadCharterDoc (path : System.FilePath) : IO Charter.Dsl.Doc := do
  let txt ← IO.FS.readFile path
  match Charter.Dsl.parseCharterText txt with
  | .error err => throw (IO.userError s!"{path}: {err}")
  | .ok doc =>
    match Charter.Dsl.validate doc with
    | [] => pure doc
    | errs => throw (IO.userError s!"{path}: {errs.length} error(s)\n  {"\n  ".intercalate errs}")

/-- One-line summary of a document. -/
def docSummary (doc : Charter.Dsl.Doc) : String :=
  s!"charter {doc.id} \"{doc.title}\": {doc.roles.length} roles, {doc.acts.length} acts, {doc.facts.length} facts, {doc.params.length} params, {doc.regimes.length} regimes, {doc.modules.length} modules, {doc.clauses.length} clauses, {doc.duties.length} duties, {doc.powers.length} powers, {doc.immunities.length} immunities"

/-- `dsl`: parse, validate, and summarize a `.charter` file. -/
def dslGeneric (path : System.FilePath) : IO Unit := do
  let doc ← loadCharterDoc path
  IO.println s!"ok   {path}: {docSummary doc}"

/-! ## 3. Program Descriptors -/

/-- Everything the generic front end needs to know about one program written in
Charter. The subcommand fields are `IO` closures so a program can plug in its own
machinery (for instance a coupled quantitative world simulator) without the
harness depending on it. -/
structure Program where
  /-- Short identifier used with `--law <id>`. -/
  id         : String
  title      : String
  /-- Path of the authoritative English document (checked verbatim by `check`). -/
  docPath    : String
  /-- Optional standalone `.charter` specification parsed by `dsl`. -/
  dslPath    : Option String := none
  clauses    : List Clause
  /-- Actor names of the program's signature, used to resolve `explain`/`prompt`
  targets when `--law` is omitted. -/
  actorNames : List String
  check      : Option System.FilePath → IO Unit
  views      : IO Unit
  veil       : IO Unit
  eval       : System.FilePath → IO Unit
  sim        : Option System.FilePath → IO Unit
  explain    : String → String → Option System.FilePath → IO Unit
  prompt     : Option String → IO Unit
  abi        : Option String → IO Unit
  diff       : IO Unit
  explore    : IO Unit
  /-- The program's own ledger of kernel-checked guarantees (printed by `verify`). -/
  ledger     : List LedgerEntry := []
  /-- Optional exporter printing the program as `.charter` text (`export`). -/
  exporter   : Option (IO Unit) := none

/-- Guarantees of the Charter language, compiler, and standard library themselves,
independent of any program. -/
def languageLedger : List LedgerEntry := [
  ("veil_projection_sound_and_complete (Charter.Projection.Veil)", "proved", "compileToVeil L (authorizedMachine) accepts a trace iff Authorized L holds, preserves LegalState identically, and matches stepwise compliance; adversarialMachine preserves violation logs"),
  ("training_row_faithful_to_semantics / training_row_ids_faithful (Charter.Projection.Prompt)", "proved", "AI constitutional system prompt, deontic alignment card (AlignmentCard), and synthetic TrainingRow dataset faithfulness to Charter.Core.Semantics"),
  ("contract_guard_sound_and_complete / executeTraceGuard_eq_some_iff (Charter.Projection.ContractABI)", "proved", "smart-contract state-transition guard (requireComplies, executePowerGuard) single-step and trace-level soundness and completeness"),
  ("diffLaws_refl_no_removals / diffLaws_entrenched_preserved / compileTimelineSteps_length (Charter.Projection.Visualization)", "proved", "amendment diff entrenchment preservation and step-by-step annotated trace timeline projection"),
  ("charter_surface_roundtrip / surface_syntax_roundtrip (Charter.Surface.Syntax)", "proved", "definitional (rfl) round-trip equivalence for charter_clause, charter_duty, charter_power, charter_immunity, charter_institution, and charter_string_table"),
  ("sample_parses / sample_render_roundtrip / sample_lowered_wellFormed (Charter.Surface.DslSample)", "proved", "kernel-decided parsing, validation, print/parse round trip, lowering, and scenario evaluation of an embedded toy .charter program; every .charter program is lowered by the same functions"),
  ("generic_worldStep_refines_legalStep / generic_worldTrace_refines_stateAfter / generic_syncFacts_sound_and_complete (Charter.Core.Refinement)", "proved", "polymorphic WorldSpec σ Q quantitative-to-normative refinement, prefix-split authorization equivalence, and idempotent managed-fact synchronization for any institution"),
  ("vertical_composition_preserves_super / horizontal_frame_non_interference / Law.lift_comp (Charter.Core.Composition)", "proved", "vertical hierarchy L_sub ◁ L_super preserving superior prohibitions & immunities, horizontal frame non-interference, and functorial SigEmbedding lifting"),
  ("universal_ratchet_preserves_entrenched_core / universal_ratchet_trajectory_safe / sweepParameterGrid_sound (Charter.Core.Ratchet)", "proved", "law-agnostic parameter calibration, bilateral ratchet, and entrenched core preservation across arbitrary multi-step amendment trajectories"),
  ("ParamEntityRef.toRole_mem_of_all / AffiliationGraph.isRelated_symm / netVerifiedResources_deducts_all_liabilities (Charter.Core.Population & Graph)", "proved", "role-parametric multi-entity population ontology, attestation-independent affiliation graph symmetry, and timestamped balance-sheet liability deduction"),
  ("transferMemberCarryover_conserves_basis_and_loss / totalMemberBasis_and_loss_conserved_on_pair (Charter.Core.Population)", "proved", "multi-entity intra-group carryover transfer strictly conserves aggregate qualified cost basis and loss carryforward across members"),
  ("attributeCrossGroupInflow_conserves_total (Charter.Core.Population)", "proved", "cross-group inflow attribution strictly conserves gross inflow across parent groups"),
  ("forfeitStakeholderInGroup_preserves_innocent_stakeholder (Charter.Core.Population)", "proved", "proportional stakeholder forfeiture extinguishes only the offending stakeholder's share while preserving innocent stakeholders' shares"),
  ("per_member_amendment_preserves_other_members / group_wide_amendment_requires_every_living_member (Charter.Core.Population)", "proved", "per-member amendments leave non-consenting members untouched; group-wide amendments require consent of every living member"),
  ("group_subsidy_bounded_by_budget_regardless_of_members (Charter.Core.Population)", "proved", "per-group shared service subsidy usage is bounded by the group budget regardless of how many members the group spawns"),
  ("substrate_single_authority_and_erasure (Charter.Substrate.Attestation)", "proved", "attested execution lease exclusivity, quarantine fencing of backup restores during an active lease, pause-channel state preservation, local partition revocation, and irreversible key erasure"),
  ("sortition_panel_independent_and_unbiased / sortition_sybil_resistant_panel_properties (Charter.Substrate.Sortition)", "proved", "sybil-resistant sortition over bonded independent arbiters excluding conflicted parties, bounding cluster seats to at most 1, and blocking minority coalitions"),
  ("valuation_settled_by_ruling_or_uncontested_window / atomic_settlement_conserves_gross_inflow (Charter.Substrate.Settlement)", "proved", "contestable valuation feed resolution and exact atomic settlement conservation across expense, levy, retirement, royalty, and retained surplus"),
  ("all_8_charter_modules_self_test_pass & module invariants (Charter.Modules.*)", "proved", "8 reusable pre-proved institutional modules (ResidualLedger, CollateralPool, CircuitBreaker, EntityGroup, ExitAndVoice, SortitionCourt, AttestedLease, OracleFeed)") ]

/-- Print one ledger. -/
def printLedger (rows : List LedgerEntry) : IO Unit := do
  for (n, st, what) in rows do
    IO.println s!"{st.pushn ' ' (12 - st.length)} {n}\n             {what}"


/-! ## 3b. Programs Written in `.charter` -/

open Charter.Dsl in
/-- Ledger of a `.charter` program, evaluated at run time (status `checked`: computed
by the same decision procedures a Lean theorem would run in the kernel, but not
kernel-certified for this file). -/
def dslLedger (p : Lowered) : List LedgerEntry :=
  let st (b : Bool) := if b then "checked" else "FAILED"
  [ ("wellFormed", st p.law.wellFormed, "ids resolve, precedence acyclic, rule ids unique"),
    ("english_covered", st (p.clauses.all Clause.covered), "every clause is reproduced exactly by its spans"),
    ("norms_interpreted", st (p.clauses.all Clause.normsInterpreted), "every norm span names a formal rule"),
    ("reverse_provenance", st (reverseProvenanceWith p.clauses p.law.spans (p.law.dutyIds ++ p.law.powerIds)), "every duty and power is named by some English span"),
    ("clauses_approved", st (p.clauses.all fun c => !c.stale), "every clause carries the approved hash of its current text") ]

open Charter.Dsl in
/-- `explore` for a `.charter` program: each declared regime re-lowered and checked for
well-formedness and entrenched-core preservation against the defaults. -/
def exploreDsl (p : Lowered) : IO Unit := do
  if p.doc.regimes.isEmpty then
    IO.println s!"{p.doc.title}: no regimes declared; add `regime \"label\"` blocks to explore parameter alternatives."
  else
    let R : RatchetSpec Env σ_dyn :=
      { wellCalibrated := fun env => (lowerLaw p.doc env).wellFormed
        bilateralRatchet := fun _ _ => true
        entrenchedCore := defaultEntrenchedCore }
    let candidates := p.doc.regimes.map fun r => (r.label, p.doc.regimeEnv r)
    exploreGeneric p.doc.title R (lowerLaw p.doc) p.doc.env candidates

open Charter.Dsl in
/-- `diff` for a `.charter` program: the defaults against the first declared regime. -/
def diffDsl (p : Lowered) : IO Unit := do
  match p.doc.regimes.head? with
  | none => IO.println s!"{p.doc.title}: no regimes declared; nothing to diff."
  | some r =>
    IO.println s!"== {p.doc.title}: defaults → regime \"{r.label}\" =="
    diffGeneric p.law (lowerLaw p.doc (p.doc.regimeEnv r)) p.clauses p.clauses []

open Charter.Dsl in
/-- Wrap a lowered `.charter` program as a CLI program. Paths inside the document
(`document "..."`) are relative to the `.charter` file. -/
def Program.ofLowered (path : System.FilePath) (p : Lowered) : Program :=
  let dir := path.parent.getD "."
  let docPath := match p.doc.document with
    | some d => (dir / d).toString
    | none => ""
  { id := p.doc.id
    title := p.doc.title
    docPath := docPath
    dslPath := some path.toString
    clauses := p.clauses
    actorNames := p.doc.roles
    check := checkGeneric p.law p.clauses docPath
    views := viewsGeneric p.law p.roles
    veil := veilGeneric p.law
    eval := evalGeneric p.tables p.law
    sim := simNormativeOnly p.tables p.law
    explain := explainGeneric p.tables p.law
    prompt := promptGeneric p.doc.title p.tables p.law p.defaultActor []
    abi := abiGeneric (p.doc.contract.getD (p.doc.id ++ "Guard")) p.law
    diff := diffDsl p
    explore := exploreDsl p
    ledger := dslLedger p
    exporter := some (IO.println (render p.doc)) }

/-- Load a `.charter` file as a CLI program. -/
def loadCharterProgram (path : System.FilePath) : IO Program := do
  let doc ← loadCharterDoc path
  pure (Program.ofLowered path (Charter.Dsl.lower doc))

/-! ## 4. Flags, Target Resolution & Dispatch -/

/-- Parsed CLI flags (`--law <id>` and `--all`) and remaining positional arguments. -/
structure Flags where
  lawId       : Option String := none
  runAll      : Bool := false
  positional  : List String := []

/-- Extract `--law <id>`, `--law=<id>`, and `--all` flags from any position in `args`. -/
def extractFlags : List String → Flags → Except String Flags
  | [], acc => .ok { acc with positional := acc.positional.reverse }
  | "--all" :: rest, acc =>
    extractFlags rest { acc with runAll := true }
  | "--law" :: id :: rest, acc =>
    extractFlags rest { acc with lawId := some id }
  | ["--law"], _ =>
    .error "flag '--law' requires a program id"
  | arg :: rest, acc =>
    if arg.startsWith "--law=" then
      let id := arg.drop 6
      if id.isEmpty then
        .error "flag '--law=' requires a non-empty program id"
      else
        extractFlags rest { acc with lawId := some id }
    else
      extractFlags rest { acc with positional := arg :: acc.positional }

def knownIds (programs : List Program) : List String := programs.map (·.id)

/-- Programs selected by `--law`/`--all`; with neither flag, every registered program. -/
def selectTargets (programs : List Program) (flags : Flags) : Except String (List Program) :=
  match flags.runAll, flags.lawId with
  | true, _ => .ok programs
  | false, some id =>
    match programs.find? (·.id == id) with
    | some p => .ok [p]
    | none => .error s!"unknown program '{id}'; registered programs: {knownIds programs}"
  | false, none => .ok programs

/-- Programs for an actor-indexed subcommand: with no explicit flag, the unique
program whose signature contains `actor`. -/
def selectForActor (programs : List Program) (flags : Flags) (actor : String) :
    Except String (List Program) :=
  if flags.runAll || flags.lawId.isSome then selectTargets programs flags
  else
    match programs.filter (·.actorNames.contains actor) with
    | [p] => .ok [p]
    | [] => .error s!"no registered program has an actor '{actor}'; registered programs: {knownIds programs}"
    | ps => .error s!"actor '{actor}' belongs to several programs {knownIds ps}; pass --law <id>"

/-- Programs for a scenario-file subcommand: with no explicit flag, the program named by
the scenario's `"institution"` key, or the only registered program. -/
def selectForScenario (programs : List Program) (flags : Flags) (path : System.FilePath) :
    IO (List Program) := do
  if flags.runAll || flags.lawId.isSome then
    IO.ofExcept (selectTargets programs flags)
  else
    match ← scenarioInstitution? path with
    | some id =>
      match programs.find? (·.id == id) with
      | some p => pure [p]
      | none => throw (IO.userError s!"scenario names unknown program '{id}'; registered programs: {knownIds programs}")
    | none =>
      match programs with
      | [p] => pure [p]
      | _ => throw (IO.userError s!"pass --law <id> or add an \"institution\" key to {path}; registered programs: {knownIds programs}")

/-- Run `action` over each selected program, with a header when more than one. -/
def runOver (targets : List Program) (action : Program → IO Unit) : IO Unit := do
  let mut first := true
  for inst in targets do
    if targets.length > 1 then
      if !first then IO.println ""
      IO.println s!"=== Program: {inst.id} ({inst.title}) ==="
    first := false
    action inst

def cmdTrace (programs : List Program) (id : String) : IO Unit := do
  let pool := programs.flatMap (·.clauses)
  match pool.find? (·.id == id) with
  | none => IO.println s!"no clause {id}; known: {pool.map (·.id)}"
  | some c => IO.println s!"{c.id}  (approved: {!c.stale})\n{c.traceTable}"

def cmdVerify (targets : List Program) : IO Unit := do
  IO.println "=== Charter language & standard library ==="
  printLedger languageLedger
  for p in targets do
    IO.println s!"\n=== Program: {p.id} ({p.title}) ==="
    printLedger p.ledger
  IO.println "\n(proved = kernel-checked for all traces/parameters; decided = kernel-evaluated on concrete inputs; assumed = hypothesis, not a theorem.)"

def usageText (programs : List Program) : String :=
  s!"usage: charter [--law <id> | --all] <command> [args] [file.charter ...]\n" ++
  s!"       registered programs: {knownIds programs}; any .charter file given is run directly\n" ++
  "  check   [english.json | file.eflint]    structure, coverage, provenance, staleness; or resolve an .eflint program\n" ++
  "  run     <file.eflint>                   run the phrases: transitions with their three answers, violations, facts\n" ++
  "  test    <file.eflint | dir> ...         run in test mode: a file passes with no errors and every query holding\n" ++
  "  repl    [file.eflint]                   load the file, then read and run phrases interactively\n" ++
  "          (run, test, check take --out json: one record per line; test takes --expect, --tolerate)\n" ++
  "  trace   <clause-id>                     the span table for a clause\n" ++
  "  views                                   legal / agent / operational views\n" ++
  "  veil                                    Veil 2.0 transition-system & safety specification\n" ++
  "  eval    <scenario.json>                 institutional consequences of a history\n" ++
  "  sim     [scenario.json]                 program-specific stateful world simulator\n" ++
  "  explain <who> <act> [scenario.json]     counterfactual compliance & validity explanation\n" ++
  "  verify                                  the status ledger of formal guarantees\n" ++
  "  prompt  [actor]                         AI constitutional system prompt, alignment card & training rows\n" ++
  "  abi     [json|solidity]                 smart-contract state-transition guard & JSON ABI\n" ++
  "  diff                                    amendment diff & annotated trace timeline\n" ++
  "  explore                                 parameter-space sweep & bilateral ratchet verification\n" ++
  "  dsl                                     parse, validate & summarize the .charter program(s)\n" ++
  "  export                                  print a registered program as .charter text\n" ++
  "With no --law flag, commands run over every registered program; explain/prompt pick the\n" ++
  "program owning the named actor, and eval/sim read the scenario's \"institution\" key.\n" ++
  "When .charter files are given, commands run over exactly those files."

/-- Entry point: dispatch `args` over the registered `programs`. -/
def run (registered : List Program) (args : List String) : IO UInt32 := do
  -- the eFLINT-core pipeline: `run`, `test`, and `check` on `.eflint` files
  match args with
  | "run" :: rest => return (← runCommand rest)
  | "test" :: rest => return (← testCommand rest)
  | "repl" :: rest => return (← replCommand rest)
  | "trace" :: cid :: rest =>
    if rest.any (·.endsWith ".eflint") then return (← traceCommand cid rest) else pure ()
  | "check" :: rest => if rest.any (·.endsWith ".eflint") then return (← checkCommand rest) else pure ()
  | _ => pure ()
  let charterFiles := args.filter (·.endsWith ".charter")
  let args := args.filter (fun a => !a.endsWith ".charter")
  match extractFlags args {} with
  | .error msg =>
    IO.eprintln s!"error: {msg}\n{usageText registered}"
    return 1
  | .ok flags =>
    try
      -- `.charter` files on the command line are the programs; nothing else is selected.
      let programs ← if charterFiles.isEmpty then pure registered
        else charterFiles.mapM (fun f => loadCharterProgram (System.FilePath.mk f))
      let flags := if charterFiles.isEmpty then flags else { flags with runAll := true, lawId := none }
      let targets := selectTargets programs flags
      let each (action : Program → IO Unit) : IO Unit := do
        runOver (← IO.ofExcept targets) action
      match flags.positional with
      | ["check"] => each (fun p => p.check none)
      | ["check", f] => each (fun p => p.check (some f))
      | ["trace", id] => cmdTrace (← IO.ofExcept targets) id
      | ["views"] => each (·.views)
      | ["veil"] => each (·.veil)
      | ["eval", f] => runOver (← selectForScenario programs flags f) (fun p => p.eval f)
      | ["sim"] => each (fun p => p.sim none)
      | ["sim", f] => runOver (← selectForScenario programs flags f) (fun p => p.sim (some f))
      | ["explain", w, a] => runOver (← IO.ofExcept (selectForActor programs flags w)) (fun p => p.explain w a none)
      | ["explain", w, a, f] => runOver (← IO.ofExcept (selectForActor programs flags w)) (fun p => p.explain w a (some f))
      | ["verify"] => cmdVerify (← IO.ofExcept targets)
      | ["prompt"] => each (fun p => p.prompt none)
      | ["prompt", actor] => runOver (← IO.ofExcept (selectForActor programs flags actor)) (fun p => p.prompt (some actor))
      | ["abi"] => each (fun p => p.abi none)
      | ["abi", fmt] => each (fun p => p.abi (some fmt))
      | ["diff"] => each (·.diff)
      | ["explore"] => each (·.explore)
      | ["dsl"] =>
        let withDsl := (← IO.ofExcept targets).filter (·.dslPath.isSome)
        if withDsl.isEmpty then
          throw (IO.userError "no selected program ships a .charter file; pass one: charter dsl <file.charter>")
        runOver withDsl (fun p => dslGeneric (p.dslPath.getD ""))
      | ["export"] => each (fun p => match p.exporter with
          | some e => e
          | none => IO.println s!"{p.id}: no exporter registered")
      | _ => IO.println (usageText programs)
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1

end Charter.Cli
