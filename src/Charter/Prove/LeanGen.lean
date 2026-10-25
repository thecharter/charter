import Charter.Prove.Run

/-!
# Charter.Prove.LeanGen — The project `charter prove` writes

A generator, not a mode (plan §3, D9; spec 013.4). From a loaded program it writes one
source file for the checker: the program's phrases **embedded as data** (never as text:
parsing in the kernel is prohibitively slow, 013.4), a **checkpointed chain** of kernel
theorems, one per phrase, and one theorem per claim and per invariant read off the chain's
end.

The chain (ruled 2026-10-25). The kernel keeps its caches for the whole of one
declaration, so a single theorem deciding a program of `P` phrases needs memory
proportional to `P` (about 0.23 GB per phrase of a library program, finding of
2026-10-24), and no program longer than a few dozen phrases is decidable under any cap.
Here the record after every phrase (`Prove.Summary`: the configuration, the verdicts so
far, the invariants found violated) is embedded as data, as the compiled evaluator
produced it, and theorem `step_k : stepSummary S_{k-1} p_k = S_k` asks the kernel to
recompute exactly one phrase. Memory is bounded by one phrase's evaluation whatever the
program's length. Each step theorem is also the Law 9 check for its phrase: if the
kernel computes anything else, that theorem fails and names the phrase.

Scenarios are sub-chains: a scenario forks from the record at its point, its phrases are
checkpointed in turn, its end state is checked for invariants (`viol_k`), and the
configuration is restored (`Prove.foldl_scenario`). The chaining lemmas are proved once
in `Charter.Prove.Run`; the generated proofs only rewrite with them.

The step theorems use `kernel_rfl` (`Charter.Prove.Kernel`): `Eq.refl` handed to the
kernel alone, as `decide +kernel` hands over its decision; plain `rfl` compares the sides
in the elaborator first, which exceeds 6 GB on a one-phrase program where the kernel needs
under a second (013.4, finding of 2026-10-24).
-/

namespace Charter.Prove

/-- One theorem the generator writes about the program's claims. -/
structure Obligation where
  /-- The theorem's identifier in the generated file. -/
  name  : String
  /-- Which question it answers: `holds`, `lawful`, `valid`, `violated`, or `invariant`. -/
  about : String
  /-- The author's text of the claim, or the invariant's name. -/
  text  : String
  /-- The program line the claim is on (0 for an invariant). -/
  line  : Nat
  /-- The verdict the run-time evaluator gave, which the theorem asserts. -/
  expected : Bool
  deriving Repr, Inhabited

/-- One checkpoint theorem of the chain: the kernel's recomputation of one phrase
(`phrase`), of a scenario's end-state check (`scenario`), or of the program's (`program`). -/
structure Step where
  name  : String
  about : String
  /-- The program line of the phrase, or of the scenario; 0 for the program's end. -/
  line  : Nat
  deriving Repr, Inhabited

/-- Where a theorem starts: the module it is in and its line there. -/
abbrev Loc := String × Nat

/-- The generated project: its files and where each theorem starts. The chain is split
into modules of `chunk` phrases each, every one importing the one before it, because the
checker's resident size grows with every declaration it has elaborated and is not given
back between them (measured 2026-10-25: about 30 MB per second of kernel work, monotone
through a whole file); run as separate processes, each module is bounded on its own. -/
structure Project where
  /-- The files in order (module name, source): the checkpoint modules, then the main
  file, which imports the last of them and holds the chain's end, the claims and the
  invariants. Each is written as `<module>.lean` in the project's directory. -/
  files       : List (String × String)
  /-- The theorem about the program's claims and invariants together. -/
  decided     : String × Loc
  /-- The checkpoint theorems, each located at the line its block starts on. -/
  steps       : List (Step × Loc)
  /-- The per-claim and per-invariant theorems. -/
  obligations : List (Obligation × Loc)

/-- A Lean identifier from an author's name: letters, digits and `_`. -/
def ident (s : String) : String :=
  let body := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let body := String.mk body
  if body.isEmpty || (body.get 0).isDigit then "n_" ++ body else body

/-- A value as Lean source, on one line: the derived `Repr`, which spells every
constructor by its full name, is Lean syntax for these records. -/
def reprSource [Repr α] (x : α) : String := (reprPrec x 0).pretty 100000000

def phraseSource (p : Phrase) : String := reprSource p

/-- The source of a list of booleans or strings as a Lean literal. -/
def boolsSource (bs : List Bool) : String := "[" ++ ", ".intercalate (bs.map fun b => if b then "true" else "false") ++ "]"
def stringsSource (ss : List String) : String := "[" ++ ", ".intercalate (ss.map String.quote) ++ "]"

/-- A record as a Lean literal, its configuration by name. -/
def summarySource (cfgName : String) (s : Summary) : String :=
  s!"\{ cfg := {cfgName}, verdicts := {boolsSource s.verdicts}, violated := {stringsSource s.violated} }"

def aboutOf (text : String) : String :=
  if text.startsWith "?lawful" || text.startsWith "?!lawful" then "lawful"
  else if text.startsWith "?valid" || text.startsWith "?!valid" then "valid"
  else if text.startsWith "?violated" || text.startsWith "?!violated" then "violated"
  else "holds"

/-- The generator's running state: the lines written so far, the record and the names of
its constant and its configuration's, and the chain so far. -/
structure Gen where
  /-- The lines of the file being written. -/
  lines   : Array String := #[]
  /-- The module being written; the checkpoint modules are `<stem>_steps_<n>`. -/
  module  : String
  /-- The checkpoint modules closed so far, in order. -/
  files   : Array (String × String) := #[]
  /-- The first line of every file but the first. -/
  comment : String
  /-- Phrases checkpointed in the module being written, and the size of a module. -/
  inChunk : Nat := 0
  chunk   : Nat
  stem    : String
  cur     : Summary := S0
  curName : String := "Charter.Prove.S0"
  cfgName : String := "Charter.Prove.S0.cfg"
  /-- The rewrite that advances the chain past each item, in order. -/
  chain   : Array String := #[]
  /-- The items' sources, in order. -/
  items   : Array String := #[]
  steps   : Array (Step × Loc) := #[]

/-- Where the next pushed line will be (1-based). -/
def Gen.nextLoc (g : Gen) : Loc := (g.module, g.lines.size + 1)

def Gen.push (g : Gen) (ls : List String) : Gen := { g with lines := g.lines ++ ls.toArray }

/-- The imports of a file: the library, and the checkpoint module before it, if any. -/
def importLines (prev : Option String) : List String :=
  ["import Charter.Prove.Run", "import Charter.Prove.Kernel"] ++ (prev.map (fun m => [s!"import {m}"])).getD []
    ++ ["set_option maxRecDepth 100000", ""]

/-- Close the module being written and start the next, which imports it. -/
def Gen.newModule (g : Gen) : Gen :=
  let next := s!"{ident g.stem}_steps_{g.files.size + 2}"
  { g with files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n"),
           module := next, inChunk := 0,
           lines := (g.comment :: importLines (some g.module)).toArray }

/-- Start a new module when the one being written holds a full chunk. -/
def Gen.chunked (g : Gen) : Gen :=
  if g.inChunk ≥ g.chunk && g.chunk > 0 then g.newModule else g

/-- Checkpoint one phrase from the current record: its constant, the record after it, and
the step theorem. Returns the generator and the names of the phrase and the new record. -/
def Gen.checkpoint (g : Gen) (tag : String) (p : Phrase) (line : Nat) (about : String) : Gen × String × String := Id.run do
  let pName := s!"p_{tag}"
  let cfgName := s!"cfg_{tag}"
  let sName := s!"S_{tag}"
  let thm := s!"step_{tag}"
  let next := stepSummary g.cur p
  let start := g.nextLoc
  let g := g.push [
    s!"-- line {line}",
    s!"def {pName} : Charter.Phrase := {phraseSource p}",
    s!"def {cfgName} : Charter.Config := {reprSource next.cfg}",
    s!"def {sName} : Charter.Prove.Summary := {summarySource cfgName next}",
    s!"theorem {thm} : Charter.Prove.stepSummary {g.curName} {pName} = {sName} := by kernel_rfl",
    "" ]
  let g := { g with cur := next, curName := sName, cfgName := cfgName, inChunk := g.inChunk + 1,
                    steps := g.steps.push ({ name := thm, about, line }, start) }
  return (g, pName, sName)

/-- Write the block of one item. -/
def Gen.item (g : Gen) (k : Nat) (it : Item) : Gen :=
  match it.val with
  | .inl _ => g
  | .inr p =>
    let g := g.chunked
    let pos := s!"⟨⟨{it.pos.line}, {it.pos.col}⟩, \"\", Sum.inr"
    match p.scenarioParts with
    | none =>
      let (g, pName, _) := g.checkpoint (toString k) p it.pos.line "phrase"
      { g with chain := g.chain.push s!"Charter.Prove.foldl_phrase step_{k} rfl",
               items := g.items.push s!"{pos} {pName}⟩" }
    | some (name, ps) => Id.run do
      -- the sub-chain forks from the current record and configuration
      let forkName := g.curName
      let forkCfg := g.cfgName
      let forkCur := g.cur
      let mut g := g
      let mut pNames : Array String := #[]
      let mut stepNames : Array String := #[]
      let mut j := 0
      for q in ps do
        j := j + 1
        g := g.chunked -- a sub-chain may span modules; `scen_k` below imports them all
        let (g', pName, _) := g.checkpoint s!"{k}_{j}" q it.pos.line "phrase"
        g := g'
        pNames := pNames.push pName
        stepNames := stepNames.push s!"step_{k}_{j}"
      let endName := g.curName
      let scen := s!"scen_{k}"
      let scenProof := if stepNames.isEmpty then "rfl"
        else "by rw [" ++ ", ".intercalate (stepNames.toList.map fun s => s!"Charter.Prove.foldl_step {s}") ++ ", List.foldl_nil]"
      let viol := addViolated g.cur
      let vName := s!"S_{k}_v"
      let after := afterScenario forkCur viol
      let sName := s!"S_{k}"
      let start := g.nextLoc
      g := g.push [
        s!"theorem {scen} : [{", ".intercalate pNames.toList}].foldl Charter.Prove.stepSummary {forkName} = {endName} := {scenProof}",
        s!"def {vName} : Charter.Prove.Summary := {summarySource g.cfgName viol}",
        s!"theorem viol_{k} : Charter.Prove.addViolated {endName} = {vName} := by kernel_rfl",
        s!"def {sName} : Charter.Prove.Summary := {summarySource forkCfg after}",
        s!"theorem after_{k} : Charter.Prove.afterScenario {forkName} {vName} = {sName} := rfl",
        "" ]
      g := { g with cur := after, curName := sName, cfgName := forkCfg,
                    steps := g.steps.push ({ name := s!"viol_{k}", about := "scenario", line := it.pos.line }, start),
                    chain := g.chain.push s!"Charter.Prove.foldl_scenario {scen} viol_{k} after_{k}",
                    items := g.items.push s!"{pos} (Charter.Phrase.scenario {String.quote name} [{", ".intercalate pNames.toList}])⟩" }
      return g

/-- Generate the project for a loaded program. `program` names it in the file's
comment; `items` are its phrases with directives already inlined. -/
def generate (program stem : String) (items : List Item) (chunk : Nat := 5) : Project := Id.run do
  let items := items.filter fun it => match it.val with | .inr _ => true | .inl _ => false
  let comment := s!"-- Written by `charter prove` for {program}. Do not edit: it is regenerated on every run."
  let header := comment :: importLines none ++ [
    "/-! The chain (013.4): the record after every phrase, as the evaluator produced it, and one",
    "kernel theorem per phrase recomputing it. A failing `step_k` names the phrase the kernel",
    s!"disagrees about (Law 9). The chain is split into modules of {chunk} phrases, each importing",
    "the one before, run as separate processes so that each is bounded on its own. -/",
    "" ]
  let mut g : Gen := { lines := header.toArray, module := s!"{ident stem}_steps_1", comment, chunk, stem }
  let mut k := 0
  for it in items do
    k := k + 1
    g := g.item k it
  -- the main file: the program's end state, the items, the chain, the claims
  g := { g with files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n"),
                module := stem, lines := (comment :: importLines (some g.module)).toArray }
  let fin := addViolated g.cur
  let finStart := g.nextLoc
  g := g.push [
    "-- the program's end state (013.2)",
    s!"def S_fin : Charter.Prove.Summary := {summarySource g.cfgName fin}",
    s!"theorem viol_final : Charter.Prove.addViolated {g.curName} = S_fin := by kernel_rfl",
    "" ]
  g := { g with steps := g.steps.push ({ name := "viol_final", about := "program", line := 0 }, finStart) }
  -- the items and the chain
  let itemLines := match g.items.toList.reverse with
    | [] => ["  ]"]
    | last :: rest => (rest.reverse.map (· ++ ",")).map ("  " ++ ·) ++ ["  " ++ last, "  ]"]
  g := g.push (["/-- The program's phrases, as the parser produced them (directives inlined). -/",
    "def items : List Charter.Item := ["] ++ itemLines ++ [""])
  let chainStart := g.nextLoc
  g := g.push ([
    "-- The chain: every checkpoint in order, then the end state.",
    "theorem run_decided : Charter.Prove.summarize items = S_fin := by",
    "  unfold Charter.Prove.summarize items"] ++
    (g.chain.toList.map fun c => s!"  rw [{c}]") ++ [
    "  rw [List.foldl_nil, viol_final]",
    "",
    s!"theorem program_decided : Charter.Prove.summary items = ({boolsSource fin.verdicts}, {stringsSource fin.violated}) := by",
    "  unfold Charter.Prove.summary",
    "  rw [run_decided]",
    "  exact rfl",
    "#print axioms program_decided",
    "" ])
  -- the claims and invariants
  let labels := claimLabels items
  let claimObls : List Obligation := (labels.zip fin.verdicts).zipIdx.map fun (((line, text), ok), i) =>
    { name := s!"claim_{i + 1}", about := aboutOf (text.trim), text, line, expected := ok }
  let invObls : List Obligation := fin.cfg.spec.invariants.map fun d =>
    { name := s!"invariant_{ident d}", about := "invariant", text := d, line := 0, expected := !fin.violated.contains d }
  let mut obls : Array (Obligation × Loc) := #[]
  for (o, i) in claimObls.zipIdx do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summary items).1[{i}]? = some true := by rw [program_decided]; rfl"
    obls := obls.push (o, (g.module, g.nextLoc.2 + 1))
    g := g.push [s!"-- line {o.line}: {o.text}", stmt, s!"#print axioms {o.name}", ""]
  for o in invObls do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summary items).2.contains {String.quote o.text} = false := by rw [program_decided]; rfl"
    obls := obls.push (o, (g.module, g.nextLoc.2 + 1))
    g := g.push [s!"-- invariant {o.text} holds at the program's end state and at every scenario's (013.2)", stmt, s!"#print axioms {o.name}", ""]
  let files := g.files.push (g.module, "\n".intercalate g.lines.toList ++ "\n")
  return { files := files.toList, decided := ("program_decided", chainStart),
           steps := g.steps.toList, obligations := obls.toList }

end Charter.Prove
