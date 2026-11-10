import Charter.Cli.Plan
import Charter.Cli.Build
import Charter.Server.Bundles

/-!
# Charter.Cli.Bundle — Federated Action-Carried Justification Bundles CLI (`charter bundle`, `D43`)

Provides offline signing of actor-attributed statements, minimal justification bundle synthesis,
closed-box bundle verification, and bundle inspection over `.charter` programs.
-/

namespace Charter.Cli

open Lean (Json toJson fromJson?)
open Charter.Server

def bundleUsage : String :=
  "usage: charter bundle <subcommand> [flags] [<file.charter>]\n" ++
  "  sign        --seed <seed> --id <id> --author <actor> --fact <fact> [--args a,b] [--audience r1,r2] [--expires T] [-o out.json] <file.charter>\n" ++
  "  synthesize  --seed <seed> --id <id> --actor <actor> --act <act> [--args a,b] --statements <pool.json> [-o bundle.json] <file.charter>\n" ++
  "  verify      --bundle <bundle.json> [--statements <pool.json>] [--revoked id1,id2] [--out json] <file.charter>\n" ++
  "  inspect     --bundle <bundle.json>\n" ++
  "  self-test   run federated justification, redaction, revocation, and leak-detection self-tests"

structure BundleCliOpts where
  seed       : Option String := none
  id         : String := "id-1"
  author     : Option String := none
  actor      : Option String := none
  fact       : Option String := none
  act        : Option String := none
  csvArgs    : List String := []
  audience   : List String := []
  revoked    : List String := []
  expiresAt  : Option Int := none
  enactedAt  : Int := 0
  stmtsPath  : Option String := none
  bundlePath : Option String := none
  outPath    : Option String := none
  file       : Option String := none
  jsonOut    : Bool := false

def splitCsvNonEmpty (s : String) : List String :=
  (s.splitOn ",").map String.trim |>.filter (!·.isEmpty)

def parseCsvElem (s : String) : Elem :=
  match s.toInt? with
  | some n => .int n
  | none => .str s

def parseBundleFlags : List String → BundleCliOpts → Except String BundleCliOpts
  | [], o => .ok o
  | "--seed" :: v :: r, o => parseBundleFlags r { o with seed := some v }
  | "--id" :: v :: r, o => parseBundleFlags r { o with id := v }
  | "--author" :: v :: r, o => parseBundleFlags r { o with author := some v }
  | "--actor" :: v :: r, o => parseBundleFlags r { o with actor := some v }
  | "--fact" :: v :: r, o => parseBundleFlags r { o with fact := some v }
  | "--act" :: v :: r, o => parseBundleFlags r { o with act := some v }
  | "--args" :: v :: r, o => parseBundleFlags r { o with csvArgs := splitCsvNonEmpty v }
  | "--audience" :: v :: r, o => parseBundleFlags r { o with audience := splitCsvNonEmpty v }
  | "--revoked" :: v :: r, o => parseBundleFlags r { o with revoked := splitCsvNonEmpty v }
  | "--expires" :: v :: r, o =>
    match v.toInt? with
    | some n => parseBundleFlags r { o with expiresAt := some n }
    | none => .error s!"--expires needs an integer timestamp, not `{v}`"
  | "--at" :: v :: r, o =>
    match v.toInt? with
    | some n => parseBundleFlags r { o with enactedAt := n }
    | none => .error s!"--at needs an integer timestamp, not `{v}`"
  | "--statements" :: v :: r, o => parseBundleFlags r { o with stmtsPath := some v }
  | "--bundle" :: v :: r, o => parseBundleFlags r { o with bundlePath := some v }
  | "-o" :: v :: r, o => parseBundleFlags r { o with outPath := some v }
  | "--out" :: "json" :: r, o => parseBundleFlags r { o with jsonOut := true }
  | "--out" :: "text" :: r, o => parseBundleFlags r { o with jsonOut := false }
  | a :: r, o =>
    if a.startsWith "-" then .error s!"unknown flag `{a}`"
    else if o.file.isNone then parseBundleFlags r { o with file := some a }
    else .error s!"unexpected extra argument `{a}`"

def loadSpecAndLawHash (file : String) : IO (Except String (Config × String)) := do
  let (items, diags) ← loadProgram file
  if diags.any (·.isError) then
    let msg := "; ".intercalate (diags.filter (·.isError) |>.map (·.message))
    return .error msg
  match evalToExplainState items none with
  | .error e => return .error e
  | .ok cfg =>
    let lawHash := Artifact.sha256String (toJson cfg.spec.ruleIds).compress
    return .ok (cfg, lawHash)

def readJsonListStmts (path : String) : IO (Except String (List SignedStatement)) := do
  let raw ← try IO.FS.readFile path catch e => return .error s!"could not read `{path}`: {e}"
  return do
    let j ← Json.parse raw
    match fromJson? (α := List SignedStatement) j with
    | .ok xs => .ok xs
    | .error _ =>
      let single ← fromJson? (α := SignedStatement) j
      .ok [single]

def bundleCommand (args : List String) : IO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] =>
    IO.println bundleUsage
    return 0
  | ["self-test"] =>
    if bundleSelfTest then
      IO.println "ok   bundle self-test (authorship reflection, synthesis, leak detection, redacted attestation, granular revocation)"
      return 0
    else
      IO.eprintln "FAIL bundle self-test"
      return 1
  | sub :: rest =>
    let opts ← match parseBundleFlags rest {} with
      | .ok o => pure o
      | .error e => IO.eprintln s!"charter bundle {sub}: {e}\n{bundleUsage}"; return 2
    match sub with
    | "inspect" =>
      let some bp := opts.bundlePath | do IO.eprintln "charter bundle inspect: --bundle <bundle.json> required"; return (2 : UInt32)
      let raw ← try IO.FS.readFile bp catch e => do IO.eprintln s!"charter bundle inspect: {e}"; return (1 : UInt32)
      match (do let j ← Json.parse raw; fromJson? (α := JustificationBundle) j) with
      | .error e => IO.eprintln s!"charter bundle inspect: {e}"; return 1
      | .ok b =>
        let summary := Json.mkObj [
          ("bundleId", Json.str b.bundleId),
          ("actor", Json.str b.actor),
          ("action", Json.str b.action),
          ("basisLawHash", Json.str b.basisLawHash),
          ("enactedAt", Json.num b.enactedAt),
          ("statementCount", Json.num b.statements.length),
          ("attestationCount", Json.num b.attestations.length),
          ("actorSigValid", Json.bool (verifyBundleActorSig b))
        ]
        IO.println summary.pretty
        return 0
    | "sign" =>
      let (some seed, some author, some factName, some file) := (opts.seed, opts.author, opts.fact, opts.file)
        | do IO.eprintln s!"charter bundle sign: --seed, --author, --fact, and <file.charter> required\n{bundleUsage}"; return (2 : UInt32)
      let (_, lawHash) ← match ← loadSpecAndLawHash file with
        | .ok p => pure p
        | .error e => IO.eprintln s!"charter bundle sign: {e}"; return 1
      let aud : AudiencePolicy := if opts.audience.isEmpty then .unrestricted else .restricted opts.audience
      let elArgs := opts.csvArgs.map parseCsvElem
      let stmt := signStatement seed opts.id author lawHash opts.enactedAt opts.expiresAt aud
        [.inputFact factName elArgs true]
      let outTxt := (toJson stmt).pretty ++ "\n"
      if let some op := opts.outPath then
        IO.FS.writeFile op outTxt
      else
        IO.print outTxt
      return 0
    | "synthesize" =>
      let (some seed, some actor, some actName, some sp, some file) :=
          (opts.seed, opts.actor, opts.act, opts.stmtsPath, opts.file)
        | do IO.eprintln s!"charter bundle synthesize: --seed, --actor, --act, --statements, and <file.charter> required\n{bundleUsage}"; return (2 : UInt32)
      let (cfg, lawHash) ← match ← loadSpecAndLawHash file with
        | .ok p => pure p
        | .error e => IO.eprintln s!"charter bundle synthesize: {e}"; return 1
      let cands ← match ← readJsonListStmts sp with
        | .ok xs => pure xs
        | .error e => IO.eprintln s!"charter bundle synthesize: {e}"; return 1
      let net : FedNetwork := { agreedLaws := [lawHash], stated := cands, revokedIds := opts.revoked }
      let elArgs := opts.csvArgs.map parseCsvElem
      match synthesizeBundle cfg net seed opts.id actor actName elArgs lawHash opts.enactedAt cands with
      | none =>
        IO.eprintln s!"FAIL synthesize: no valid justification bundle found for `{actName}`"
        return 1
      | some b =>
        let outTxt := (toJson b).pretty ++ "\n"
        if let some op := opts.outPath then
          IO.FS.writeFile op outTxt
        else
          IO.print outTxt
        return 0
    | "verify" =>
      let (some bp, some file) := (opts.bundlePath, opts.file)
        | do IO.eprintln s!"charter bundle verify: --bundle and <file.charter> required\n{bundleUsage}"; return (2 : UInt32)
      let (cfg, lawHash) ← match ← loadSpecAndLawHash file with
        | .ok p => pure p
        | .error e => IO.eprintln s!"charter bundle verify: {e}"; return (1 : UInt32)
      let rawB ← try IO.FS.readFile bp catch e => do IO.eprintln s!"charter bundle verify: {e}"; return (1 : UInt32)
      let b ← match (do let j ← Json.parse rawB; fromJson? (α := JustificationBundle) j) with
        | .ok x => pure x
        | .error e => IO.eprintln s!"charter bundle verify: {e}"; return (1 : UInt32)
      let statedPool ← match opts.stmtsPath with
        | some sp =>
          match ← readJsonListStmts sp with
          | .ok xs => pure xs
          | .error e => IO.eprintln s!"charter bundle verify: {e}"; return (1 : UInt32)
        | none => pure b.statements
      let net : FedNetwork := { agreedLaws := [lawHash], stated := statedPool, revokedIds := opts.revoked }
      match verifyBundle cfg net b with
      | .error e =>
        if opts.jsonOut then
          IO.println (Json.mkObj [("ok", Json.bool false), ("permitted", Json.bool false), ("reason", Json.str e), ("assurance", Json.str "checked")]).compress
        else
          IO.eprintln s!"FAIL bundle `{b.bundleId}`: {e}"
        return (1 : UInt32)
      | .ok res =>
        let perm := res.lawful == .yes && res.valid == .yes
        if opts.jsonOut then
          IO.println (Json.mkObj [
            ("ok", Json.bool perm),
            ("permitted", Json.bool perm),
            ("bundleId", Json.str b.bundleId),
            ("occurred", Json.str res.occurred),
            ("lawful", Json.str res.lawful.asString),
            ("valid", Json.str res.valid.asString),
            ("outcome", Json.str res.outcome),
            ("effectsOf", toJson res.effectsOf),
            ("assurance", Json.str "checked")
          ]).compress
        else
          IO.println s!"{if perm then "ok  " else "FAIL"} bundle `{b.bundleId}`: occurred={res.occurred}, lawful={res.lawful.asString}, valid={res.valid.asString}, outcome={res.outcome}"
        if perm then return (0 : UInt32) else return (1 : UInt32)
    | _ =>
      IO.eprintln s!"charter bundle: unknown subcommand `{sub}`\n{bundleUsage}"
      return 2

end Charter.Cli
