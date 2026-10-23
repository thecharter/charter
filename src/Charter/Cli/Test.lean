import Charter.Cli.Run

/-!
# Charter.Cli.Test — `charter test <files or directories>`

Runs every `.eflint` file under the given paths in test mode: a file passes when
it produces no error diagnostic and every query holds (`test/eflint-corpus/README.md`).
Prints one line per file and a summary; exit status is non-zero when any file
fails.
-/

namespace Charter.Cli

def walkEflint (p : System.FilePath) : Nat → IO (List System.FilePath)
  | 0 => return []
  | depth + 1 => do
    if ← p.isDir then
      let entries ← p.readDir
      let sorted := entries.qsort (fun a b => a.path.toString < b.path.toString)
      let mut acc := []
      for e in sorted do acc := acc ++ (← walkEflint e.path depth)
      return acc
    else if p.extension == some "eflint" then return [p]
    else return []

/-- `charter test <paths…>` -/
def testCommand (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: charter test <file.eflint | directory> ..."
    return 2
  let mut files : List System.FilePath := []
  for a in args do files := files ++ (← walkEflint a 32)
  let mut passed := 0
  let mut failed : List String := []
  for f in files do
    let stats ← runProgram true f
    if stats.ok then
      passed := passed + 1
      IO.println s!"ok   {f} ({stats.phrases} phrases)"
    else
      failed := failed ++ [f.toString]
      IO.println s!"FAIL {f}: {stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"}"
  IO.println s!"{passed} passed, {failed.length} failed, {files.length} total"
  return (if failed.isEmpty then 0 else 1)

end Charter.Cli
