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
  deriving Repr

instance : Inhabited Summary := ⟨⟨{}, [], []⟩⟩

/-- The record before the first phrase. -/
def S0 : Summary := ⟨{}, [], []⟩

/-- Run one phrase from a configuration, recording its claims. -/
def stepSummary (s : Summary) (p : Phrase) : Summary :=
  let (cfg', outs) := runPhrase s.cfg p
  { s with cfg := cfg', verdicts := s.verdicts ++ claimVerdicts p outs }

def addViolated (s : Summary) : Summary :=
  { s with violated := s.violated ++ (Explore.violatedInvariants s.cfg).filter (fun d => !s.violated.contains d) }

/-- A scenario's name and phrases, when a phrase is one. -/
def _root_.Charter.Phrase.scenarioParts : Phrase → Option (String × List Phrase)
  | .scenario name ps => some (name, ps)
  | _ => none

/-- The record after a scenario: its claims and violations kept, the configuration
restored to the one it ran from (011.11). -/
def afterScenario (s s' : Summary) : Summary := { s' with cfg := s.cfg }

/-- One phrase's effect on the record: a scenario runs from the configuration at its
point, its end state is checked for invariants, and the configuration is restored. -/
def stepPhrase (s : Summary) (p : Phrase) : Summary :=
  match p.scenarioParts with
  | some (_, ps) => afterScenario s (addViolated (ps.foldl stepSummary s))
  | none => stepSummary s p

/-- One item's effect on the record; directives are ignored (the loader inlined them). -/
def stepItem (s : Summary) (it : Item) : Summary :=
  match it.val with
  | .inl _ => s
  | .inr p => stepPhrase s p

/-- Run a program's items; the program's end state is checked for invariants. -/
def summarize (items : List Item) : Summary :=
  addViolated (items.foldl stepItem S0)

/-- The decided data of a program: its claims' verdicts and the invariants that do not
hold at some end state. The generator's theorems are about this pair. -/
def summary (items : List Item) : List Bool × List DomId :=
  ((summarize items).verdicts, (summarize items).violated)

/-! ### The chain (013.4)

The generator checkpoints the record after every phrase as data, and the kernel decides
one phrase per theorem (`stepSummary s p = s'`, by `kernel_rfl`), so the memory a decision
needs is bounded by one phrase's evaluation, not the program's. The lemmas below chain
those theorems into `summarize items = s`; they are the only general statements involved,
proved once here by rewriting alone (no `simp`: its closing lemma `eq_self` carries
`propext`, and a decided theorem must depend on no axioms, Law 10). -/

theorem foldl_step {s s' : Summary} {p : Phrase} {ps : List Phrase} (h : stepSummary s p = s') :
    (p :: ps).foldl stepSummary s = ps.foldl stepSummary s' := by
  rw [List.foldl_cons, h]

theorem stepItem_phrase (s : Summary) (pos : Pos) (text : String) (p : Phrase) :
    stepItem s ⟨pos, text, Sum.inr p⟩ = stepPhrase s p := rfl

theorem stepPhrase_of_none {s : Summary} {p : Phrase} (hs : p.scenarioParts = none) :
    stepPhrase s p = stepSummary s p := by
  unfold stepPhrase; rw [hs]

/-- A phrase that is not a scenario advances the chain by its checkpoint theorem. -/
theorem foldl_phrase {s s' : Summary} {pos : Pos} {text : String} {p : Phrase} {rest : List Item}
    (h : stepSummary s p = s') (hs : p.scenarioParts = none) :
    (⟨pos, text, Sum.inr p⟩ :: rest).foldl stepItem s = rest.foldl stepItem s' := by
  rw [List.foldl_cons, stepItem_phrase, stepPhrase_of_none hs, h]

/-- A scenario advances the chain by its own sub-chain (`h`), the check of its end state
(`hv`), and the restored configuration (`hc`, by `rfl` in the generated project). -/
theorem foldl_scenario {s s' s'' s₃ : Summary} {pos : Pos} {text name : String} {ps : List Phrase}
    {rest : List Item} (h : ps.foldl stepSummary s = s') (hv : addViolated s' = s'')
    (hc : afterScenario s s'' = s₃) :
    (⟨pos, text, Sum.inr (.scenario name ps)⟩ :: rest).foldl stepItem s = rest.foldl stepItem s₃ := by
  rw [List.foldl_cons, stepItem_phrase]
  show rest.foldl stepItem (afterScenario s (addViolated (ps.foldl stepSummary s))) = _
  rw [h, hv, hc]

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
