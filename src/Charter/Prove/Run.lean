import Charter.Eval.Interpreter
import Charter.Surface.Parser

/-!
# Charter.Prove.Run — Running a program without `IO`

`charter prove` (plan §3, D9) needs the evaluator as a pure function the kernel can
run: a program text in, its final configuration and the claims that failed out, with
no file system (so `#include`/`#require` are not followed here; the generator inlines
them). Everything below is structural recursion with fuel, so a theorem about a
concrete program can be settled by `decide` (Law 10: *decided*, kernel-evaluated).
-/

namespace Charter.Prove

/-- The outcome of running a program's phrases in order. -/
structure Outcome where
  cfg          : Config
  failedClaims : Nat
  errors       : Nat

instance : Inhabited Outcome := ⟨⟨{}, 0, 0⟩⟩

def stepOutcome (o : Outcome) (p : Phrase) : Outcome :=
  let (cfg', outs) := runPhrase o.cfg p
  let failed := outs.filter (fun out => match out with
    | .queryRes ok => !ok
    | .expectRes _ _ ok => !ok
    | _ => false) |>.length
  let errs := outs.filter (fun out => match out with
    | .diag d => d.isError
    | _ => false) |>.length
  { cfg := cfg', failedClaims := o.failedClaims + failed, errors := o.errors + errs }

/-- Run the phrases of parsed items (directives ignored). -/
def runItems (items : List Item) : Outcome :=
  items.foldl (fun o it => match it.val with
    | .inr p => stepOutcome o p
    | .inl _ => o) ⟨{}, 0, 0⟩

/-- Parse and run a program text. A parse error counts as one error. -/
def runText (src : String) (eflint : Bool := false) : Outcome :=
  match parseSource src eflint with
  | .ok items => runItems items
  | .error _ => ⟨{}, 0, 1⟩

/-- Whether every claim of the program held and nothing erred. -/
def Outcome.ok (o : Outcome) : Bool := o.failedClaims == 0 && o.errors == 0

/-! ## Claims and invariants, for the generator (013.4)

A program's *claims* are its `?e` and `?lawful`/`?valid`/`?violated` phrases, at top
level and inside `Scenario` blocks (run from the configuration at the scenario's point,
which they leave unchanged, as `charter test` runs them). `summary` gives every claim's
verdict in order and every invariant reported violated after any phrase (013.1); one
kernel decision of `summary` settles every theorem the generator writes. -/

mutual
/-- How many claims a phrase makes: one per `?e`/`?lawful…`, summed through `{ … }`.
Structural (a mutual block with its list helper): a definition the kernel cannot unfold
would leave every theorem of the generator stuck (013.4). -/
def _root_.Charter.Phrase.claimCount : Phrase → Nat
  | .query _ => 1
  | .expect .. => 1
  | .par ps => Phrase.claimCountList ps
  | _ => 0
def _root_.Charter.Phrase.claimCountList : List Phrase → Nat
  | [] => 0
  | p :: ps => Phrase.claimCount p + Phrase.claimCountList ps
end

mutual
/-- The author's text of each claim a phrase makes, in the order of `claimCount`. -/
def _root_.Charter.Phrase.claimTexts : Phrase → List String
  | .query t => [s!"?{t}"]
  | .expect w neg t => [s!"?{if neg then "!" else ""}{w.name} {t}"]
  | .par ps => Phrase.claimTextsList ps
  | _ => []
def _root_.Charter.Phrase.claimTextsList : List Phrase → List String
  | [] => []
  | p :: ps => Phrase.claimTexts p ++ Phrase.claimTextsList ps
end

/-- The verdicts a phrase's outputs carry, one per claim; a claim whose evaluation
reported no verdict (an error instead) is `false`. -/
def claimVerdicts (p : Phrase) (outs : List Output) : List Bool :=
  let vs := outs.filterMap fun
    | .queryRes ok => some ok
    | .expectRes _ _ ok => some ok
    | _ => none
  (List.range p.claimCount).map fun i => vs[i]?.getD false

/-- The record of a run: the configuration, every claim's verdict in order, and every
invariant that does not hold at an end state: the program's, or a scenario's (the states
`charter test --explore` searches from, 013.2). A violation reported in passing after an
earlier phrase (013.1) is not one: genesis builds a state in several phrases. -/
structure Summary where
  cfg      : Config
  verdicts : List Bool
  violated : List DomId

instance : Inhabited Summary := ⟨⟨{}, [], []⟩⟩

/-- Run one phrase from a configuration, recording its claims. -/
def stepSummary (s : Summary) (p : Phrase) : Summary :=
  let (cfg', outs) := runPhrase s.cfg p
  { s with cfg := cfg', verdicts := s.verdicts ++ claimVerdicts p outs }

def addViolated (s : Summary) : Summary :=
  { s with violated := s.violated ++ (Explore.violatedInvariants s.cfg).filter (fun d => !s.violated.contains d) }

/-- Run a program's items: scenarios run from the configuration at their point and
leave it unchanged (011.11), their end states checked for invariants; directives are
ignored (the loader has inlined them). -/
def summarize (items : List Item) : Summary :=
  let s := items.foldl (fun s it => match it.val with
    | .inl _ => s
    | .inr (.scenario _ ps) =>
      let s' := addViolated (ps.foldl stepSummary s)
      { s' with cfg := s.cfg }
    | .inr p => stepSummary s p) ⟨{}, [], []⟩
  addViolated s

/-- The decided data of a program: its claims' verdicts and the invariants that do not
hold at some end state. The generator's one kernel theorem is about this pair. -/
def summary (items : List Item) : List Bool × List DomId :=
  let s := summarize items
  (s.verdicts, s.violated)

/-- The labels of a program's claims, in the order of `summary`: `(file line, text)`;
a scenario's claims carry the scenario's line and name. -/
def claimLabels (items : List Item) : List (Nat × String) :=
  items.flatMap fun it => match it.val with
    | .inl _ => []
    | .inr (.scenario name ps) =>
      (ps.flatMap Phrase.claimTexts).map fun t => (it.pos.line, s!"scenario {name}: {t}")
    | .inr p => p.claimTexts.map fun t => (it.pos.line, if it.text.isEmpty then t else it.text)

/-- Whether a named invariant holds in the final configuration. -/
def Outcome.invariantHolds (o : Outcome) (d : DomId) : Bool :=
  !(Explore.violatedInvariants o.cfg).contains d

end Charter.Prove
