import Charter.Cli.Test
import Charter.Cli.Analyze
import Charter.Cli.Prove
import Charter.Cli.Repl
import Charter.Cli.Fmt
import Charter.Cli.Build
import Charter.Cli.Explore
import Charter.Cli.Verify
import Charter.Cli.Explain
import Charter.Cli.Plan
import Charter.Cli.Bundle
import Charter.Cli.Diff
import Charter.Cli.Generate
import Charter.Cli.Doc
import Charter.Cli.Init
import Charter.Cli.Doctor
import Charter.Cli.Approve
import Charter.Lsp.Server

/-!
# Charter.Cli.Main — Standalone Command-Line Dispatcher

Dispatches `charter` subcommands over `.charter` and `.eflint` source programs with zero
linked application companions (`D10`, `G0-INDEPENDENCE`) and zero engine terminology in
user-visible output (`Law 11`).
-/

namespace Charter.Cli

def versionString : String := "charter 1.0.0"

def helpText : String :=
  "usage: charter <command> [args] [file.charter ...]\n" ++
  "  init     [<directory>]                  scaffold project, charter.toml, lockfile, and UAT\n" ++
  "  check    <file.charter> ...             resolve phrases and verify clause provenance\n" ++
  "  approve  [--lock] [--restamp] <file>    stamp reviewed clause approvals in lockfile or source\n" ++
  "  build    <file.charter> [-o <artifact>] compile to a signed SHA-256 content-addressed CIR artifact\n" ++
  "  fmt      [--check] <file.charter> ...   format source canonically with round-trip AST verification\n" ++
  "  doc      <file.charter> [-o <out.md>]   emit consolidated legal prose & CIR decision rulebook\n" ++
  "  lsp                                     run Language Server Protocol (stdio JSON-RPC)\n" ++
  "  doctor   [--claims ...] [--lock]        verify claims registry, lockfile digests, and environment\n" ++
  "  run      <file.charter>                 run top-level phrases and report transitions\n" ++
  "  test     <file.charter | dir> ...       run scenarios, provenance checks, and invariant exploration\n" ++
  "  analyze  <file.charter> ...             check dead rules, unranked overlaps, and generated scenarios\n" ++
  "  explore  [flags] <file.charter> ...     explore lawful, adversarial, or mixed state spaces\n" ++
  "  verify   [flags] <file.charter> ...     verify invariants & temporal properties (finite, smt, inductive)\n" ++
  "  explain  <expr> <file.charter> [flags]  emit audience-scoped ReasonGraph with counterfactuals\n" ++
  "  plan     <act> <file.charter> [flags]   find shortest lawful and valid sequence enabling <act>\n" ++
  "  bundle   <subcommand> [flags] [<file>]  sign statements, synthesize, or verify justification bundles\n" ++
  "  inputs   [<act>] <file.charter> [flags] list open/evidenced input schema or missing act inputs\n" ++
  "  diff     <old.charter> <new.charter>    3-view English, CIR rule, and scenario semantic diff\n" ++
  "  generate --target <tgt> <file.charter>  project CIR to solidity, abi, quint, or advisory prompt\n" ++
  "  trace    <clause-id> <file.charter>     print the verbatim span table for a clause\n" ++
  "  prove    <file.charter> ...             decide claims and invariants in the proof kernel (see --show-checker)\n" ++
  "  repl     [file.charter]                 interactive institutional session\n" ++
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
  | "init" :: rest => initCommand rest
  | "check" :: rest => checkCommand rest
  | "approve" :: rest => approveCommand rest
  | "build" :: rest => buildCommand rest
  | "fmt" :: rest => fmtCommand rest
  | "doc" :: rest => docCommand rest
  | "lsp" :: rest => Charter.Lsp.lspCommand rest
  | "doctor" :: rest => doctorCommand rest
  | "run" :: rest => runCommand rest
  | "test" :: rest => testCommand rest
  | "analyze" :: rest => analyzeCommand rest
  | "explore" :: rest => exploreCommand rest
  | "verify" :: rest => verifyCommand rest
  | "explain" :: rest => explainCommand rest
  | "plan" :: rest => planCommand rest
  | "bundle" :: rest => bundleCommand rest
  | "inputs" :: rest => inputsCommand rest
  | "diff" :: rest => diffCommand rest
  | "generate" :: rest => generateCommand rest
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
