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

/-- Whether a `.charter` source uses the superseded v0.3 flat `charter <id> "..."` grammar
(kept only for the two legacy companion files until Phase 3's deletions). -/
def isLegacyCharterSrc (src : String) : Bool :=
  let lines := src.splitOn "\n" |>.map String.trim |>.filter (fun l => !l.isEmpty && !l.startsWith "--")
  match lines with
  | first :: _ => first.startsWith "charter "
  | [] => false

/-- Whether `path` is an existing `.charter` file in the superseded v0.3 grammar. -/
def isLegacyCharterFile (path : System.FilePath) : IO Bool := do
  if path.extension != some "charter" then return false
  if !(← path.pathExists) then return false
  let src ← try IO.FS.readFile path catch _ => pure ""
  return isLegacyCharterSrc src

/-- Find the Charter installation/repository root from `start` (for `lib/` and `prove`). -/
partial def findPackageRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  let manifest := dir / "lakefile.toml"
  if ← manifest.pathExists then
    let txt ← try IO.FS.readFile manifest catch _ => pure ""
    if (txt.splitOn "name = \"charter\"").length > 1 then return some dir
  match dir.parent with
  | some p => if p == dir then return none else findPackageRoot p
  | none => return none

/-- Locate the Charter root from the working directory or the running binary's path. -/
def locateCharterRoot : IO (Option System.FilePath) := do
  let cwd ← IO.currentDir
  match ← findPackageRoot cwd with
  | some r => return some r
  | none =>
    let app ← try IO.appPath catch _ => pure "."
    findPackageRoot app

def findIncluded (dirs : List System.FilePath) (name : String) : IO (Option System.FilePath) := do
  for dir in dirs do
    let f := dir / name
    if ← f.pathExists then return some f
    let fc := System.FilePath.mk (f.toString ++ ".charter")
    if (← fc.pathExists) && !(← isLegacyCharterFile fc) then return some fc
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
  let stdDirs ← match ← locateCharterRoot with
    | some r => pure [r, r / "lib"]
    | none => pure []
  let (its, ds, _, _) ← loadFile eflint path [] ("." :: stdDirs) 64
  return (its, ds)

end Charter.Cli
