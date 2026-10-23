import Charter
import Examples

/-!
# `charter` — Command-Line Front End

The executable is the program-agnostic harness in `Charter.Tooling.Cli`. Any
`.charter` file given on the command line is parsed, validated, lowered, and run as
a program; nothing needs to be linked in. The Lean companions of the two shipped
examples are also linked (`registeredPrograms`) so that their coupled world
simulators (`sim`), ratchet specifications (`explore`), and exporters (`export`)
are available.

    charter <command> [args] <file.charter> ...        run on the given .charter programs

    charter [--law <id> | --all] check   [english.json]      structure, coverage, provenance, staleness
    charter [--law <id> | --all] trace   <clause-id>         the span table for a clause
    charter [--law <id> | --all] views                       legal / agent / operational views
    charter [--law <id> | --all] veil                        Veil 2.0 transition-system & safety specification
    charter [--law <id>]         eval    <scenario.json>     institutional consequences of a history
    charter [--law <id> | --all] sim     [scenario.json]     program-specific stateful world simulator
    charter [--law <id>]         explain <who> <act> [scenario.json]   "can X do Y right now, and why?"
    charter [--law <id> | --all] verify                      the status ledger of formal guarantees
    charter [--law <id> | --all] prompt  [actor]             AI constitutional system prompt, alignment card & training rows
    charter [--law <id> | --all] abi     [json|solidity]     smart-contract state-transition guard & JSON ABI
    charter [--law <id> | --all] diff                        amendment diff & annotated trace timeline
    charter [--law <id> | --all] explore                     parameter-space sweep & bilateral ratchet verification
    charter [--law <id> | --all] dsl     [file.charter]      parse & validate a standalone .charter specification
-/

/-- Programs linked into this build of the `charter` executable. -/
def registeredPrograms : List Charter.Cli.Program :=
  [SovereignAgency.cli, AutonomousCommons.cli]

def main (args : List String) : IO UInt32 :=
  Charter.Cli.run registeredPrograms args
