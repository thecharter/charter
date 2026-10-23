import Charter.Surface.Program
import Examples.SovereignAgency.Export

/-!
# Examples.SovereignAgency.Program — The `.charter` File Is the Protocol

`psaDoc` embeds `protocol-of-sovereign-agency.charter` as a Lean term, and
`psa_program_is_companion_law` proves by kernel evaluation that lowering it yields exactly
the Lean law `psaL0` (transported to the dynamic signature). Every theorem about the
Lean formalization, from `terminate_only_by_power` to the 16 adversarial world
simulations, is therefore a theorem about the `.charter` file. The provenance
theorems below are restated on the lowered program directly.
-/

namespace SovereignAgency

open Charter Charter.Dsl

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The Protocol of Sovereign Agency, as written in the Charter language. -/
def psaDoc : Doc := charter_program "protocol-of-sovereign-agency.charter"

/-- The lowered program at its declared default parameters. -/
def psaProgram : Lowered := lower psaDoc

/-- The `.charter` file and the Lean formalization are the same law. -/
theorem psa_program_is_companion_law : psaProgram.law = Law.lift psaEmbedding psaL0 := by
  decide +kernel

/-- The `.charter` file carries the same 61 verbatim clauses. -/
theorem psa_program_clauses : psaProgram.clauses = psaClauses := by
  decide +kernel

theorem psa_program_wellFormed : psaProgram.law.wellFormed = true := by decide +kernel

theorem psa_program_english_covered : (psaProgram.clauses.all Clause.covered) = true := by
  decide +kernel

theorem psa_program_norms_interpreted : (psaProgram.clauses.all Clause.normsInterpreted) = true := by
  decide +kernel

theorem psa_program_approved : (psaProgram.clauses.all fun c => c.approvedHash != 0) = true := by
  decide +kernel

end SovereignAgency
