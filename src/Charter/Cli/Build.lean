import Charter.Cli.Load
import Charter.Cli.Provenance
import Charter.Artifact.Format

/-!
# Charter.Cli.Build — `charter build <file.charter> [-o <file.artifact>]`

Elaborates a Charter program into validated `CIR` epochs (`ElaborateCIR.elaboratePhrases`),
verifies Law 8 provenance when `Document` / `Clause`s are present, and emits a canonical,
SHA-256 content-addressed `Artifact.Bundle` (`D18`).
-/

namespace Charter.Cli

structure BuildOpts where
  input  : Option String := none
  output : Option String := none

def parseBuildArgs : List String → BuildOpts → Except String BuildOpts
  | [], o => .ok o
  | "-o" :: out :: rest, o => parseBuildArgs rest { o with output := some out }
  | ["-o"], _ => .error "-o needs an output path"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.input.isSome then .error s!"unexpected extra input {a}"
    else parseBuildArgs rest { o with input := some a }

/-- `charter build <file.charter> [-o <file.artifact>]` -/
def buildCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter build <file.charter> [-o <file.artifact>]"
  match parseBuildArgs args {} with
  | .error e => IO.eprintln s!"charter build: {e}\n{usage}"; return 2
  | .ok { input := none, .. } => IO.eprintln usage; return 2
  | .ok { input := some f, output } =>
    let (items, loadDiags) ← loadProgram f
    let mut hasErr := false
    for d in loadDiags do
      IO.eprintln d.render
      if d.isError then hasErr := true
    if hasErr then return 1
    let phrases := items.filterMap fun l => match l.item.val with | .inr p => some p | .inl _ => none
    match CIR.elaboratePhrases phrases with
    | .error ds =>
      for d in ds do IO.eprintln (d.withFile f).render
      return 1
    | .ok prog =>
      for w in prog.warnings do IO.eprintln (w.withFile f).render
      let finalSpec := (prog.epochs.getLast?.map (·.spec)).getD emptySpec
      let dir := (System.FilePath.mk f).parent.getD "."
      let loadedDocs ← readDocuments finalSpec dir
      let provClaims := if finalSpec.clauses.isEmpty && finalSpec.document.isNone && finalSpec.documents.isEmpty then [] else provenanceReportDocs finalSpec loadedDocs
      let cov := computeProvenanceCoverage finalSpec loadedDocs provClaims
      let failedProv := provClaims.filter (!·.ok)
      for c in failedProv do IO.eprintln c.render
      if !failedProv.isEmpty then return 1
      let docTexts : List (SourceDoc × Option String) := loadedDocs.map fun (sd, r) =>
        (sd, match r with | .ok txt => some txt | .error _ => none)
      let bundle := Artifact.buildBundleDocs prog docTexts cov.asString
      let rendered := bundle.toJson.pretty ++ "\n"
      match output with
      | some outPath =>
        let p := System.FilePath.mk outPath
        if let some parent := p.parent then IO.FS.createDirAll parent
        IO.FS.writeFile p rendered
        IO.println s!"built {outPath} (sha256:{bundle.artifactSha256}, {prog.epochs.length} epoch(s))"
      | none =>
        IO.print rendered
      return 0

end Charter.Cli
