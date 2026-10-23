import Charter.Surface.Parser

/-!
# Charter.Cli.Load — Reading a program and its `#include`/`#require` files

A program is the items of its file with every `#include "f"` replaced by the
items of `f` (and `#require "f"` the same, once per file), resolved relative to
the including file's directory and then the working directory, with `.eflint`
appended when the bare name does not exist (eFLINT `Util.hs`, `REPL.hs`).
Diagnostics name the file; a missing file is CHR005.
-/

namespace Charter.Cli

/-- An item with the file it came from. -/
structure Located where
  file : String
  item : Item

def findIncluded (dirs : List System.FilePath) (name : String) : IO (Option System.FilePath) := do
  for dir in dirs do
    let f := dir / name
    if ← f.pathExists then return some f
    let f' := System.FilePath.mk (f.toString ++ ".eflint")
    if ← f'.pathExists then return some f'
  return none

/-- Load a file and expand its directives. `seen` holds every file loaded so far
(for `#require`); `dirs` the include directories accumulated so far (eFLINT adds the
directory of every file it loads, so a file under `usage-control/` that requires
`../access.eflint` can then require `simple-scenario.eflint` from the parent); `depth`
bounds include chains. -/
def loadFile (eflint : Bool) (path : System.FilePath) (seen : List String) (dirs : List System.FilePath) : Nat →
    IO (List Located × List Diagnostic × List String × List System.FilePath)
  | 0 => return ([], [Diagnostic.error "CHR005" s!"include chain too deep at {path}"], seen, dirs)
  | depth + 1 => do
    let pathS := path.toString
    let src ← try IO.FS.readFile path catch _ => pure ""
    if !(← path.pathExists) then
      return ([], [Diagnostic.error "CHR005" s!"cannot read {pathS}"], seen, dirs)
    let seen := seen ++ [pathS]
    let dir := path.parent.getD "."
    let dirs := if dirs.contains dir then dirs else dirs ++ [dir]
    match parseSource src eflint with
    | .error e => return ([], [e.withFile pathS], seen, dirs)
    | .ok items =>
      let mut acc : List Located := []
      let mut diags : List Diagnostic := []
      let mut seen := seen
      let mut dirs := dirs
      for it in items do
        match it.val with
        | .inr _ => acc := acc ++ [⟨pathS, it⟩]
        | .inl d =>
          let (name, once) := match d with
            | .include n => (n, false)
            | .require n => (n, true)
          match ← findIncluded dirs name with
          | none => diags := diags ++ [(Diagnostic.error "CHR005" s!"cannot find {name} (looked in {dirs})" it.pos).withFile pathS]
          | some f =>
            let fS := f.toString
            if once && seen.contains fS then pure ()
            else
              let (its, ds, seen', dirs') ← loadFile eflint f seen dirs depth
              acc := acc ++ its
              diags := diags ++ ds
              seen := seen'
              dirs := dirs'
      return (acc, diags, seen, dirs)

/-- Load a program: its items in order, and the diagnostics of loading. `eflint`
restricts the keywords to eFLINT's (`--eflint`). -/
def loadProgram (path : System.FilePath) (eflint : Bool := false) : IO (List Located × List Diagnostic) := do
  let (its, ds, _, _) ← loadFile eflint path [] ["."] 64
  return (its, ds)

end Charter.Cli
