import Charter.Cli.Test
import Charter.Cli.Prove
import Charter.Cli.Repl
import Charter.Cli.Fmt
import Charter.Cli.Build
import Charter.Cli.Explore
import Charter.Cli.Verify
import Charter.Cli.Explain

/-!
# Charter.Cli.Main — Standalone Command-Line Dispatcher

Dispatches `charter` subcommands over `.charter` and `.eflint` source programs with zero
linked application companions (`D10`, `G0-INDEPENDENCE`) and zero engine terminology in
user-visible output (`Law 11`).
-/

namespace Charter.Cli

def versionString : String := "charter 0.4.0"

def helpText : String :=
  "usage: charter <command> [args] [file.charter ...]\n" ++
  "  check   <file.charter> ...              resolve phrases and verify clause provenance\n" ++
  "  build   <file.charter> [-o <artifact>]  compile to a SHA-256 content-addressed CIR artifact\n" ++
  "  fmt     [--check] <file.charter> ...    format source canonically with round-trip AST verification\n" ++
  "  run     <file.charter>                  run top-level phrases and report transitions\n" ++
  "  test    <file.charter | dir> ...        run scenarios, provenance checks, and invariant exploration\n" ++
  "  explore [flags] <file.charter> ...      explore lawful, adversarial, or mixed state spaces\n" ++
  "  verify  [flags] <file.charter> ...      verify invariants & temporal properties (finite, smt, inductive)\n" ++
  "  explain <expr> <file.charter> [flags]   emit audience-scoped ReasonGraph with counterfactuals\n" ++
  "  trace   <clause-id> <file.charter>      print the verbatim span table for a clause\n" ++
  "  prove   <file.charter> ...              decide claims and invariants in the proof kernel (see --show-checker)\n" ++
  "  repl    [file.charter]                  interactive institutional session\n" ++
  "  version                                 print version\n" ++
  "  help                                    print this command summary\n" ++
  "Shared flags (check, run, test): --out json, --scenario <name>, --explore <depth>, --explore-domain \"type = values\"\n" ++
  "Assurance gates (check, run, test): --require-provenance, --forbid-midstream-decls, --require-complete-explore, --deny-warnings\n" ++
  "Corpus flags (test): --expect <outcomes>, --tolerate <tolerances.json>"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] =>
    IO.println helpText
    return 0
  | ["version"] | ["--version"] | ["-v"] =>
    IO.println versionString
    return 0
  | "check" :: rest => checkCommand rest
  | "build" :: rest => buildCommand rest
  | "fmt" :: rest => fmtCommand rest
  | "run" :: rest => runCommand rest
  | "test" :: rest => testCommand rest
  | "explore" :: rest => exploreCommand rest
  | "verify" :: rest => verifyCommand rest
  | "explain" :: rest => explainCommand rest
  | "trace" :: cid :: rest => traceCommand cid rest
  | ["trace"] =>
    IO.eprintln "usage: charter trace <clause-id> <file.charter>"
    return 2
  | "prove" :: rest => proveCommand rest
  | "repl" :: rest => replCommand rest
  | cmd :: _ =>
    IO.eprintln s!"charter: unknown command '{cmd}'\n{helpText}"
    return 2

end Charter.Cli
