import Charter.Prove.Run

/-!
# Charter.Prove.LeanGen — The project `charter prove` writes

A generator, not a mode (plan §3, D9; spec 013.4). From a loaded program it writes one
source file for the checker: the program's phrases **embedded as data** (never as text:
parsing in the kernel is prohibitively slow, 013.4), one kernel theorem deciding the
program's `Prove.summary` (every claim's verdict and every invariant reported violated),
and one theorem per claim and per invariant read off that decision. The kernel evaluates
the program once; the per-claim theorems are rewrites of the decided equation, so a
claim whose verdict the run-time evaluator already reported false fails at its own
theorem and nowhere else, while a disagreement between the kernel and the run-time
evaluator fails the decided theorem and, with it, every claim, loudly.

The decided theorem uses `decide +kernel`: plain `decide` evaluates the instance in the
elaborator first, which exceeds 6 GB on a one-phrase program where the kernel needs under
a second (013.4, finding of 2026-10-24).
-/

namespace Charter.Prove

/-- One theorem the generator writes. -/
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

/-- The generated project: the source text and where each theorem starts in it. -/
structure Project where
  source      : String
  /-- The one kernel theorem, with its line. -/
  decided     : String × Nat
  /-- The per-claim and per-invariant theorems, with their lines. -/
  obligations : List (Obligation × Nat)

/-- A Lean identifier from an author's name: letters, digits and `_`. -/
def ident (s : String) : String :=
  let body := s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let body := String.mk body
  if body.isEmpty || (body.get 0).isDigit then "n_" ++ body else body

/-- A phrase as Lean source, on one line: the derived `Repr`, which spells every
constructor by its full name, is Lean syntax for these records. -/
def phraseSource (p : Phrase) : String := (reprPrec p 0).pretty 100000000

def itemSource (it : Item) : String :=
  match it.val with
  | .inl _ => "" -- directives were inlined by the loader; none reach here
  | .inr p => s!"  ⟨⟨{it.pos.line}, {it.pos.col}⟩, \"\", Sum.inr ({phraseSource p})⟩"

/-- The source of a list of booleans or strings as a Lean literal. -/
def boolsSource (bs : List Bool) : String := "[" ++ ", ".intercalate (bs.map fun b => if b then "true" else "false") ++ "]"
def stringsSource (ss : List String) : String := "[" ++ ", ".intercalate (ss.map String.quote) ++ "]"

def aboutOf (text : String) : String :=
  if text.startsWith "?lawful" || text.startsWith "?!lawful" then "lawful"
  else if text.startsWith "?valid" || text.startsWith "?!valid" then "valid"
  else if text.startsWith "?violated" || text.startsWith "?!violated" then "violated"
  else "holds"

/-- Generate the project for a loaded program. `program` names it in the file's
comment; `items` are its phrases with directives already inlined. -/
def generate (program : String) (items : List Item) : Project := Id.run do
  let items := items.filter fun it => match it.val with | .inr _ => true | .inl _ => false
  let run := summarize items
  let (verdicts, violated) := (run.verdicts, run.violated)
  let labels := claimLabels items
  let invariants := run.cfg.spec.invariants
  let claimObls : List Obligation := (labels.zip verdicts).zipIdx.map fun (((line, text), ok), k) =>
    { name := s!"claim_{k + 1}", about := aboutOf (text.trim), text, line, expected := ok }
  let invObls : List Obligation := invariants.map fun d =>
    { name := s!"invariant_{ident d}", about := "invariant", text := d, line := 0, expected := !violated.contains d }
  let header := [
    s!"-- Written by `charter prove` for {program}. Do not edit: it is regenerated on every run.",
    "import Charter.Prove.Run",
    "set_option maxRecDepth 100000",
    "open Charter",
    "",
    "/-- The program's phrases, as the parser produced them (directives inlined). -/",
    "def items : List Charter.Item := [" ]
  let itemLines := items.map itemSource
  let itemLines := match itemLines.reverse with
    | [] => ["  ]"]
    | last :: rest => (rest.reverse.map (· ++ ",")) ++ [last, "  ]"]
  let decidedStmt := s!"theorem program_decided : Charter.Prove.summary items = ({boolsSource verdicts}, {stringsSource violated}) := by decide +kernel"
  let pre := header ++ itemLines ++ ["", "-- The one kernel decision: every claim's verdict, and every invariant that does not hold at an end state."]
  let decidedLine := pre.length + 1
  let mut lines := pre ++ [decidedStmt, "#print axioms program_decided", ""]
  let mut obls : List (Obligation × Nat) := []
  for (o, k) in claimObls.zipIdx do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summary items).1[{k}]? = some true := by rw [program_decided]; rfl"
    obls := obls ++ [(o, lines.length + 2)]
    lines := lines ++ [s!"-- line {o.line}: {o.text}", stmt, s!"#print axioms {o.name}", ""]
  for o in invObls do
    let stmt := s!"theorem {o.name} : (Charter.Prove.summary items).2.contains {String.quote o.text} = false := by rw [program_decided]; rfl"
    obls := obls ++ [(o, lines.length + 2)]
    lines := lines ++ [s!"-- invariant {o.text} holds at the program's end state and at every scenario's (013.2)", stmt, s!"#print axioms {o.name}", ""]
  return { source := "\n".intercalate lines ++ "\n", decided := ("program_decided", decidedLine), obligations := obls }

end Charter.Prove
