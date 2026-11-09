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
  | .decls ds =>
    let rec rebOne : Decl → Decl
      | .atPos pos d => .atPos pos (rebOne d)
      | .document p docId? sha? rank? =>
        if (System.FilePath.mk p).isAbsolute then .document p docId? sha? rank?
        else .document (rel / p).toString docId? sha? rank?
      | d => d
    .decls (ds.map rebOne)
  | ph => ph

/-- Recorded `#include`/`#require` edge for `#63` layout verification. -/
structure IncludeEdge where
  parentCanon   : String
  parentDisplay : String
  childCanon    : String
  childDisplay  : String
  pos           : Pos

/-- Metadata of one loaded source file's own items (excluding included children) for `#63`. -/
structure FileMeta where
  canonPath   : String
  displayPath : String
  ownItems    : List Item

def isCaseAllowedMod : ModClause → Bool
  | .atPos _ m => isCaseAllowedMod m
  | .strings _ | .ints _ => true
  | _ => false

def isCaseAllowedDecl (d : Decl) : Bool :=
  match d.stripPos with
  | .typeExt _ mcs _ => mcs.all isCaseAllowedMod
  | _ => false

def declPosOr (fallback : Pos) : Decl → Pos
  | .atPos p _ => if p == {} then fallback else p
  | _ => fallback

/-- Verify `#63` layout rules across loaded files and include/require edges:
- `CHR043`: case files (non-root files requiring a root `Document`) declare no new types, rules, or clauses;
- `CHR044`: one owner per `(docId?, clauseId)` across all loaded files;
- `CHR046`: dependency direction `case -> root -> articles -> modules`. -/
def checkLayoutRules (items : List Located) (metas : List FileMeta) (edges : List IncludeEdge) :
    List Diagnostic := Id.run do
  let mut diags : List Diagnostic := []
  -- 1. Single owner per clause ID (`CHR044`)
  let mut seenClauses : List ((Option String × ClauseId) × String × Pos) := []
  for l in items do
    match l.item.val with
    | .inr (.decls ds) =>
      for rawD in ds do
        let p := declPosOr l.item.pos rawD
        match rawD.stripPos with
        | .clause c =>
          let key := (c.docId, c.id)
          match seenClauses.find? (·.1 == key) with
          | some (_, prevFile, prevPos) =>
            diags := diags ++ [(Diagnostic.error "CHR044"
              s!"duplicate Clause `{c.id}` (already owned at {prevFile}:{prevPos.line}); each clause must have a single owner"
              p).withFile l.file]
          | none =>
            seenClauses := seenClauses ++ [(key, l.file, p)]
        | _ => pure ()
    | _ => pure ()

  -- 2. Classify each file from its own items
  let hasOwnDoc (cPath : String) : Bool :=
    match metas.find? (·.canonPath == cPath) with
    | none => false
    | some fm => fm.ownItems.any fun it => match it.val with
      | .inr (.decls ds) => ds.any fun d => match d.stripPos with | .document .. => true | _ => false
      | _ => false
  let hasOwnClause (cPath : String) : Bool :=
    match metas.find? (·.canonPath == cPath) with
    | none => false
    | some fm => fm.ownItems.any fun it => match it.val with
      | .inr (.decls ds) => ds.any fun d => match d.stripPos with | .clause .. => true | _ => false
      | _ => false
  let hasOwnModule (cPath : String) : Bool :=
    match metas.find? (·.canonPath == cPath) with
    | none => false
    | some fm => fm.ownItems.any fun it => match it.val with
      | .inr (.decls ds) => ds.any fun d => match d.stripPos with | .module .. => true | _ => false
      | _ => false
  let hasOwnScenario (cPath : String) : Bool :=
    match metas.find? (·.canonPath == cPath) with
    | none => false
    | some fm => fm.ownItems.any fun it => match it.val with
      | .inr (.scenario ..) => true
      | _ => false

  let rec reachesOtherDoc (fuel : Nat) (work visited : List String) (origin : String) : Bool :=
    match fuel, work with
    | 0, _ | _, [] => false
    | fuel' + 1, u :: rest =>
      if visited.contains u then reachesOtherDoc fuel' rest visited origin
      else if u != origin && hasOwnDoc u then true
      else
        let nbrs := edges.filterMap fun e => if e.parentCanon == u then some e.childCanon else none
        reachesOtherDoc fuel' (nbrs ++ rest) (u :: visited) origin

  let reachFuel := 2 * edges.length + metas.length + 2
  let requiresRoot (cPath : String) : Bool :=
    reachesOtherDoc reachFuel [cPath] [] cPath

  let fileRole (cPath : String) : String :=
    match hasOwnDoc cPath, hasOwnClause cPath, hasOwnScenario cPath, hasOwnModule cPath, requiresRoot cPath with
    | true, _, _, _, _ => "root"
    | false, true, _, _, _ => "article"
    | false, false, false, true, _ => "module"
    | false, false, true, _, _ => "case"
    | false, false, false, false, true => "case"
    | _, _, _, _, _ => "plain"

  -- `CHR043`: case files declare nothing beyond `Extend ... Identified by ...`
  for fm in metas do
    if !hasOwnDoc fm.canonPath && requiresRoot fm.canonPath then
      let mut reported : Bool := false
      for it in fm.ownItems do
        if !reported then
          match it.val with
          | .inr (.decls ds) =>
            for rawD in ds do
              if !reported && !isCaseAllowedDecl rawD then
                let p := declPosOr it.pos rawD
                diags := diags ++ [(Diagnostic.error "CHR043"
                  "case file declares types, rules, or clauses after requiring a root Document; keep only `Extend ... Identified by ...`, initial state, and `Scenario`s in case files (or declare a specialising `Document`)"
                  p).withFile fm.displayPath]
                reported := true
          | _ => pure ()

  -- 3. Dependency direction: `case -> root -> articles -> modules` (`CHR046`)
  for e in edges do
    let pRole := fileRole e.parentCanon
    let cRole := fileRole e.childCanon
    let bad :=
      (pRole == "root" && cRole == "case") ||
      (pRole == "article" && (cRole == "root" || cRole == "case")) ||
      (pRole == "module" && (cRole == "root" || cRole == "article" || cRole == "case"))
    if bad then
      diags := diags ++ [(Diagnostic.error "CHR046"
        s!"{pRole} file may not require or include {cRole} file `{e.childDisplay}` (expected dependency direction: case -> root -> articles -> modules)"
        e.pos).withFile e.parentDisplay]
  return diags

/-- Load a file and expand its directives. `seen` holds every file loaded so far
(for `#require`); `dirs` the include directories accumulated so far (eFLINT adds the
directory of every file it loads, so a file under `usage-control/` that requires
`../access.eflint` can then require `simple-scenario.eflint` from the parent); `top` is
the directory of the program's own file; `depth` bounds include chains. -/
def loadFile (eflint : Bool) (top path : System.FilePath) (seen : List String) (dirs : List System.FilePath)
    (metas : List FileMeta) (edges : List IncludeEdge) : Nat →
    IO (List Located × List Diagnostic × List String × List System.FilePath × List FileMeta × List IncludeEdge)
  | 0 => return ([], [Diagnostic.error "CHR005" s!"include chain too deep at {path}"], seen, dirs, metas, edges)
  | depth + 1 => do
    let pathS := path.toString
    let src ← try IO.FS.readFile path catch _ => pure ""
    if !(← path.pathExists) then
      return ([], [Diagnostic.error "CHR005" s!"cannot read {pathS}"], seen, dirs, metas, edges)
    let canonPath ← (try (·.toString) <$> IO.FS.realPath path catch _ => pure pathS)
    let seen := if seen.contains canonPath then seen else seen ++ [canonPath]
    let dir := dirOf path
    let dirs := if dirs.contains dir then dirs else dirs ++ [dir]
    let rel? ← relativeDir top dir
    match parseSource src eflint with
    | .error e => return ([], [e.withFile pathS], seen, dirs, metas, edges)
    | .ok items =>
      let metas := if metas.any (·.canonPath == canonPath) then metas
                   else metas ++ [{ canonPath, displayPath := pathS, ownItems := items }]
      let mut acc : List Located := []
      let mut diags : List Diagnostic := []
      let mut seen := seen
      let mut dirs := dirs
      let mut metas := metas
      let mut edges := edges
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
            edges := edges ++ [{ parentCanon := canonPath, parentDisplay := pathS,
                                 childCanon := fCanon, childDisplay := f.toString, pos := it.pos }]
            if once && seen.contains fCanon then pure ()
            else
              let (its, ds, seen', dirs', metas', edges') ← loadFile eflint top f seen dirs metas edges depth
              acc := acc ++ its
              diags := diags ++ ds
              seen := seen'
              dirs := dirs'
              metas := metas'
              edges := edges'
      return (acc, diags, seen, dirs, metas, edges)

/-- Load a program: its items in order, and the diagnostics of loading. `eflint`
restricts the keywords to eFLINT's (`--eflint`). -/
def loadProgram (path : System.FilePath) (eflint : Bool := false) : IO (List Located × List Diagnostic) := do
  let stdDirs ← match ← locateCharterRoot with
    | some r => pure [r, r / "lib"]
    | none => pure []
  let (its, ds, _, _, metas, edges) ← loadFile eflint (dirOf path) path [] ("." :: stdDirs) [] [] 64
  let layoutDiags := if ds.any (·.isError) then [] else checkLayoutRules its metas edges
  return (its, ds ++ layoutDiags)

end Charter.Cli
