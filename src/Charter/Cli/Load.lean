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
    if ← fc.pathExists then return some fc
    let f' := System.FilePath.mk (f.toString ++ ".eflint")
    if ← f'.pathExists then return some f'
    if name.endsWith ".eflint" then
      let fSwap := f.withExtension "charter"
      if ← fSwap.pathExists then return some fSwap
  return none

/-- The directory of a file; the working directory for a bare file name. -/
def dirOf (path : System.FilePath) : System.FilePath :=
  match path.parent with
  | some d => if d.toString.isEmpty then "." else d
  | none => "."

/-- Drop the longest common prefix of two component lists. -/
def stripCommonPrefix : List String → List String → List String × List String
  | x :: xs, y :: ys => if x == y then stripCommonPrefix xs ys else (x :: xs, y :: ys)
  | xs, ys => (xs, ys)

/-- The directory `target` as a path relative to the directory `base`, or `none` when it is
`base` itself or either cannot be resolved. -/
def relativeDir (base target : System.FilePath) : IO (Option System.FilePath) := do
  try
    let b ← IO.FS.realPath base
    let t ← IO.FS.realPath target
    let (up, down) := stripCommonPrefix b.components t.components
    let parts := up.map (fun _ => "..") ++ down
    return if parts.isEmpty then none else some (System.mkFilePath parts)
  catch _ => return none

/-- 012.1: a `Document` path is relative to the file that declares it. Every later stage reads
documents relative to the program's own directory, so a document declared in a file loaded
from another directory has that directory (relative to the program's) put in front of it. -/
def rebaseDocuments (rel : System.FilePath) : Phrase → Phrase
  | .decls ds => .decls (ds.map fun
      | .document p docId? sha? rank? =>
        if (System.FilePath.mk p).isAbsolute then .document p docId? sha? rank?
        else .document (rel / p).toString docId? sha? rank?
      | d => d)
  | ph => ph

/-- Load a file and expand its directives. `seen` holds every file loaded so far
(for `#require`); `dirs` the include directories accumulated so far (eFLINT adds the
directory of every file it loads, so a file under `usage-control/` that requires
`../access.eflint` can then require `simple-scenario.eflint` from the parent); `top` is
the directory of the program's own file; `depth` bounds include chains. -/
def loadFile (eflint : Bool) (top path : System.FilePath) (seen : List String) (dirs : List System.FilePath) : Nat →
    IO (List Located × List Diagnostic × List String × List System.FilePath)
  | 0 => return ([], [Diagnostic.error "CHR005" s!"include chain too deep at {path}"], seen, dirs)
  | depth + 1 => do
    let pathS := path.toString
    let src ← try IO.FS.readFile path catch _ => pure ""
    if !(← path.pathExists) then
      return ([], [Diagnostic.error "CHR005" s!"cannot read {pathS}"], seen, dirs)
    let canonPath ← (try (·.toString) <$> IO.FS.realPath path catch _ => pure pathS)
    let seen := if seen.contains canonPath then seen else seen ++ [canonPath]
    let dir := dirOf path
    let dirs := if dirs.contains dir then dirs else dirs ++ [dir]
    let rel? ← relativeDir top dir
    match parseSource src eflint with
    | .error e => return ([], [e.withFile pathS], seen, dirs)
    | .ok items =>
      let mut acc : List Located := []
      let mut diags : List Diagnostic := []
      let mut seen := seen
      let mut dirs := dirs
      for it in items do
        match it.val with
        | .inr ph =>
          let it' := match rel? with
            | some rel => { it with val := .inr (rebaseDocuments rel ph) }
            | none => it
          acc := acc ++ [⟨pathS, it'⟩]
        | .inl d =>
          let (name, once) := match d with
            | .include n => (n, false)
            | .require n => (n, true)
          match ← findIncluded dirs name with
          | none => diags := diags ++ [(Diagnostic.error "CHR005" s!"cannot find {name} (looked in {dirs})" it.pos).withFile pathS]
          | some f =>
            let fCanon ← (try (·.toString) <$> IO.FS.realPath f catch _ => pure f.toString)
            if once && seen.contains fCanon then pure ()
            else
              let (its, ds, seen', dirs') ← loadFile eflint top f seen dirs depth
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
  let (its, ds, _, _) ← loadFile eflint (dirOf path) path [] ("." :: stdDirs) 64
  return (its, ds)

end Charter.Cli
