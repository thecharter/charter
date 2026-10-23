import Charter.Surface.Program
import Examples.AutonomousCommons.Export

/-!
# Examples.AutonomousCommons.Program — The `.charter` File Is the Commons

`commonsDoc` embeds `autonomous-commons.charter` as a Lean term and
`commons_program_is_companion_law` proves by kernel evaluation that lowering it yields the
Lean law `commonsL0`, so the commons theorems and module simulations are theorems
about the `.charter` file.
-/

namespace AutonomousCommons

open Charter Charter.Dsl

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The Autonomous Compute & Treasury Commons, as written in the Charter language. -/
def commonsDoc : Doc := charter_program "autonomous-commons.charter"

def commonsProgram : Lowered := lower commonsDoc

theorem commons_program_is_companion_law : commonsProgram.law = Law.lift commonsEmbedding commonsL0 := by
  decide +kernel

theorem commons_program_clauses : commonsProgram.clauses = commonsClauses := by
  decide +kernel

theorem commons_program_wellFormed : commonsProgram.law.wellFormed = true := by decide +kernel

theorem commons_program_english_covered : (commonsProgram.clauses.all Clause.covered) = true := by
  decide +kernel

theorem commons_program_approved : (commonsProgram.clauses.all fun c => c.approvedHash != 0) = true := by
  decide +kernel

end AutonomousCommons
