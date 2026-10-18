import Examples.SovereignAgency
import Examples.SovereignAgency.Export
import Examples.SovereignAgency.Program
import Examples.SovereignAgency.Cli
import Examples.AutonomousCommons
import Examples.AutonomousCommons.Export
import Examples.AutonomousCommons.Program
import Examples.AutonomousCommons.Cli

/-!
# Examples — Institutional Programs Written in Charter

Each subdirectory of `Examples/` holds one program written in the Charter language:
a `.charter` file next to its authoritative English text and scenario files. The
`charter` executable runs every subcommand on the file directly. Each program also
has a Lean companion (`import Charter`) holding its signature, theorems, and
quantitative world simulations, a `Program.lean` proving by kernel evaluation that
lowering the `.charter` file yields exactly the companion's law, an `Export.lean`
printing the companion as `.charter` text (`charter export`), and a `Cli.lean`
registering it with the front end. None of these programs is referenced by the
language itself.

1. **`psa`** — *The Protocol of Sovereign Agency*
   (`Examples/SovereignAgency/protocol-of-sovereign-agency.charter`, English in
   `protocol-of-sovereign-agency.md`): 61 clauses across Laws 1–7, Definitions
   (`DEF.01`), and Substrate (`SUB.01`), 50 duties, 110 powers, 1 immunity. Lean
   companion `Examples.SovereignAgency`: 14 design invariants and 16 stateful
   multi-agent adversarial world simulations; `psa_program_is_lean_law`.
2. **`commons`** — *The Autonomous Compute & Treasury Commons*
   (`Examples/AutonomousCommons/autonomous-commons.charter`, English in
   `autonomous-commons-charter.md`): 8 clauses over a 5-role signature, 13 duties,
   20 powers, 1 immunity. Lean companion `Examples.AutonomousCommons`: institutional
   invariants and 8 end-to-end world simulations; `commons_program_is_lean_law`.
-/
