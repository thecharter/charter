import Charter

/-!
# `charter` — Standalone Command-Line Executable

Parses, checks, evaluates, explores, traces, and proves `.charter` and `.eflint` programs
directly, with zero linked application companions (`D10`, `G0-INDEPENDENCE`).
-/

def main (args : List String) : IO UInt32 :=
  Charter.Cli.main args
