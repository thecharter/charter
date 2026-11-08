import Charter.Cli.Run

/-!
# Charter.Cli.Approve — Stamp Clause Approvals in `charter.lock` or Source (`D34`, `#23`, `#32`, `#35`)

`charter approve [--lock] [--restamp] <file.charter> [clause-id ...]`:
- With `--lock` (or automatically when `charter.lock` already exists beside `<file.charter>`),
  records both the verbatim `textSha256` and the formal `rulesSha256` in `charter.lock` (`#23`, `#35`).
- Without `--lock` (when no `charter.lock` is present), stamps `Approved "<textSha256>"` onto
  unapproved `Clause` headers in `<file.charter>` (and drifted ones when `--restamp` is given).
-/

namespace Charter.Cli

open Lean (Json)

structure ApproveOpts where
  useLock : Bool := false
  restamp : Bool := false
  files   : List String := []

def parseApproveArgs : List String → ApproveOpts → Except String ApproveOpts
  | [], o => .ok o
  | "--lock" :: rest, o => parseApproveArgs rest { o with useLock := true }
  | "--restamp" :: rest, o => parseApproveArgs rest { o with restamp := true }
  | "--reviewed" :: rest, o => parseApproveArgs rest { o with restamp := true }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else parseApproveArgs rest { o with files := o.files ++ [a] }

def stampInlineLine (wanted : List (String × String)) (line : String) : String × Option String :=
  let trimmed := line.trimLeft
  if !trimmed.startsWith "Clause " then (line, none)
  else
    let afterClause := (trimmed.drop 7).trimLeft
    let toks := afterClause.splitOn " "
    match toks with
    | [] => (line, none)
    | cid :: restToks =>
      match wanted.find? (·.1 == cid) with
      | none => (line, none)
      | some (_, sha) =>
        let indentLen := line.length - trimmed.length
        let indent := String.mk (line.toList.take indentLen)
        -- preserve `In <DOC>` if present, strip any old `Approved ...`, keep trailing `Definition`/`=> ...`
        let (inPart, rem1) : String × List String := match restToks with
          | "In" :: doc :: r => (s!" In {doc}", r)
          | r => ("", r)
        let rem2 : List String := match rem1 with
          | "Approved" :: _ :: r => r
          | r => r
        let tail := if rem2.isEmpty then "" else " " ++ " ".intercalate rem2
        (s!"{indent}Clause {cid}{inPart} Approved \"{sha}\"{tail}", some cid)

def approveCommand (args : List String) : IO UInt32 := do
  let opts ← match parseApproveArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter approve: {e}"; return 2
  let filePath ← match opts.files with
    | f :: _ => pure f
    | [] =>
      IO.eprintln "usage: charter approve [--lock] [--restamp] <file.charter> [clause-id ...]"
      return 2
  let filterCids := opts.files.drop 1
  let fp := System.FilePath.mk filePath
  let dir := fp.parent.getD "."
  let (items, loadDiags) ← loadProgram fp false
  for d in loadDiags do
    if d.isError then IO.eprintln d.render; return 1
  let mut spec := emptySpec
  for l in items do
    match l.item.val with
    | .inr p =>
      match resolvePhrase spec p with
      | .ok (s', _, _) => spec := s'
      | .error ds =>
        for d in ds do IO.eprintln d.render
        return 1
    | .inl _ => pure ()
  let loadedDocs ← readDocuments spec dir
  spec := hydrateClausesFromDocs spec loadedDocs
  let existingLocks ← readClauseLocks dir
  let lockFile := dir / "charter.lock"
  let lockExists ← lockFile.pathExists
  if opts.useLock || lockExists then
    let mut updatedLocks : List ClauseLockEntry := existingLocks
    let mut count := 0
    for c in spec.clauses do
      if filterCids.isEmpty || filterCids.contains c.id then
        let tsha := Artifact.sha256String c.source
        let rsha := clauseRulesDigest spec c
        let prev? := existingLocks.find? (·.id == c.id)
        let shouldWrite := match prev? with
          | none => true
          | some prev =>
            if prev.textSha256 == tsha && prev.rulesSha256 == some rsha then false
            else opts.restamp
        if shouldWrite then
          updatedLocks := updatedLocks.filter (·.id != c.id) ++ [{ id := c.id, textSha256 := tsha, rulesSha256 := some rsha }]
          count := count + 1
    -- Compute file hashes for `<file>` (relative to `dir`) and declared `Document`s
    let baseName := fp.fileName.getD filePath
    let charterTxt ← IO.FS.readFile fp
    let mut fileEntries : List Json := [
      Json.mkObj [("path", Json.str baseName), ("sha256", Json.str (Artifact.sha256String charterTxt))]
    ]
    for (sd, res) in loadedDocs do
      match res with
      | .ok dtxt =>
        fileEntries := fileEntries ++ [Json.mkObj [("path", Json.str sd.path), ("sha256", Json.str (Artifact.sha256String dtxt))]]
      | .error _ => pure ()
    let clauseEntries : List Json := updatedLocks.map fun le =>
      Json.mkObj ([
        ("id", Json.str le.id),
        ("textSha256", Json.str le.textSha256)
      ] ++ (match le.rulesSha256 with | some r => [("rulesSha256", Json.str r)] | none => []))
    let lockJson := Json.mkObj [
      ("lockVersion", Json.num 1),
      ("files", Json.arr fileEntries.toArray),
      ("clauses", Json.arr clauseEntries.toArray)
    ]
    IO.FS.writeFile lockFile (lockJson.pretty ++ "\n")
    IO.println s!"{lockFile}: approved {count} clause(s)"
    return 0
  else
    let wanted : List (String × String) := spec.clauses.filterMap fun c =>
      if !filterCids.isEmpty && !filterCids.contains c.id then none
      else
        let unset := c.approvedHash == 0 && c.approvedSha256.isNone
        if unset || (opts.restamp && c.stale) then
          some (c.id, Artifact.sha256String c.source)
        else none
    if wanted.isEmpty then
      IO.println s!"{filePath}: 0 unapproved clause(s)"
      return 0
    let src ← IO.FS.readFile fp
    let lines := src.splitOn "\n"
    let mut outLines : List String := []
    let mut stamped := 0
    for line in lines do
      let (line', hit?) := stampInlineLine wanted line
      outLines := outLines ++ [line']
      if hit?.isSome then stamped := stamped + 1
    IO.FS.writeFile fp ("\n".intercalate outLines)
    IO.println s!"{filePath}: stamped {stamped} clause(s)"
    return 0

end Charter.Cli
