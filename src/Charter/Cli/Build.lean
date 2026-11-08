import Charter.Cli.Load
import Charter.Cli.Provenance
import Charter.Eval.Interpreter
import Charter.Artifact.Format

/-!
# Charter.Cli.Build — `charter build <file.charter> [-o <file.artifact>] [--sign-key <key>] [--key-id <id>]`

Elaborates a Charter program into validated `CIR` epochs (`ElaborateCIR.elaboratePhrases`),
evaluates top-level genesis setup phrases into `genesisCfg : Config`, verifies Law 8 provenance,
and emits a signed, SHA-256 content-addressed `Artifact.Bundle` (`D18`, `D27`, `G4.1`).
-/

namespace Charter.Cli

structure BuildOpts where
  input   : Option String := none
  output  : Option String := none
  signKey : String := Artifact.defaultDevSigningKey
  keyId   : String := "local-dev"

def parseBuildArgs : List String → BuildOpts → Except String BuildOpts
  | [], o => .ok o
  | "-o" :: out :: rest, o => parseBuildArgs rest { o with output := some out }
  | ["-o"], _ => .error "-o needs an output path"
  | "--sign-key" :: k :: rest, o => parseBuildArgs rest { o with signKey := k }
  | ["--sign-key"], _ => .error "--sign-key needs a secret key string"
  | "--key-id" :: id :: rest, o => parseBuildArgs rest { o with keyId := id }
  | ["--key-id"], _ => .error "--key-id needs a signer key identifier"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.input.isSome then .error s!"unexpected extra input {a}"
    else parseBuildArgs rest { o with input := some a }

/-- `charter build <file.charter> [-o <file.artifact>] [--sign-key <key>] [--key-id <id>]` -/
def buildCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter build <file.charter> [-o <file.artifact>] [--sign-key <key>] [--key-id <id>]"
  match parseBuildArgs args {} with
  | .error e => IO.eprintln s!"charter build: {e}\n{usage}"; return 2
  | .ok { input := none, .. } => IO.eprintln usage; return 2
  | .ok { input := some f, output, signKey, keyId } =>
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
      let mut genesisCfg : Config := {}
      for p in phrases do
        match p with
        | .scenario _ _ _ => pure ()
        | _ =>
          let (c', outs) := runPhrase genesisCfg p
          for out in outs do
            match out with
            | .diag d =>
              if d.isError then
                IO.eprintln (d.withFile f).render
                hasErr := true
            | _ => pure ()
          genesisCfg := c'
      if hasErr then return 1
      -- Strip scenarios from runtime spec so server artifact stays lean & scenario-free
      let cleanCfg : Config := { genesisCfg with spec := { genesisCfg.spec with scenarios := [] } }
      let finalSpec := (prog.epochs.getLast?.map (·.spec)).getD emptySpec
      let dir := (System.FilePath.mk f).parent.getD "."
      let loadedDocs ← readDocuments finalSpec dir
      let locks ← readClauseLocks dir
      let finalSpec := hydrateClausesFromDocs finalSpec loadedDocs
      let provClaims := if finalSpec.clauses.isEmpty && finalSpec.document.isNone && finalSpec.documents.isEmpty then [] else provenanceReportDocs finalSpec loadedDocs locks
      let cov := computeProvenanceCoverage finalSpec loadedDocs provClaims
      let failedProv := provClaims.filter (!·.ok)
      for c in failedProv do IO.eprintln c.render
      if !failedProv.isEmpty then return 1
      let docTexts : List (SourceDoc × Option String) := loadedDocs.map fun (sd, r) =>
        (sd, match r with | .ok txt => some txt | .error _ => none)
      let bundle := Artifact.buildSignedBundleDocs prog cleanCfg docTexts cov.asString signKey keyId
      let rendered := bundle.toJson.pretty ++ "\n"
      match output with
      | some outPath =>
        let p := System.FilePath.mk outPath
        if let some parent := p.parent then IO.FS.createDirAll parent
        IO.FS.writeFile p rendered
        IO.println s!"built {outPath} (sha256:{bundle.artifactSha256}, {prog.epochs.length} epoch(s), keyId:{keyId})"
      | none =>
        IO.print rendered
      return 0

end Charter.Cli
