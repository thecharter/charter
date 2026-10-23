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

/-- Whether a named invariant holds in the final configuration. -/
def Outcome.invariantHolds (o : Outcome) (d : DomId) : Bool :=
  !(Explore.violatedInvariants o.cfg).contains d

end Charter.Prove
