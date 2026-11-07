import Charter.Server.Api

/-!
# `charter-server` — Operator-Blind Certified Institutional Runtime (`G4`, `D27`, `Law 9`)

Links `Charter.Core`, `Charter.Eval.Eval`, `Charter.Eval.Step`, `Charter.Artifact`, and
`Charter.Server` **only** — zero modules from `Charter.Surface`, `Charter.Resolve`, or
`Charter.Prove` (`test/gates/operator-blind.sh`).
-/

namespace Charter.Server

open Lean (Json fromJson?)

def serverHelp : String :=
  "usage: charter-server <command> [args]\n" ++
  "  verify <file.artifact> [--key <secret>]                       verify SHA-256, certificate, and CIR well-formedness\n" ++
  "  replay <file.artifact> <file.log> [--snapshot <snap>] [--key] recompute every transition & state root offline\n" ++
  "  serve  <file.artifact> [--log <log>] [--snapshot <snap>]      run JSON/stdio & MCP institutional service\n" ++
  "         [--institution <id>] [--max-skew <N>] [--key <secret>]\n" ++
  "  version                                                       print version\n" ++
  "  help                                                          print this summary"

structure ServerCliOpts where
  artifactPath : Option String := none
  logPath      : Option String := none
  snapshotPath : Option String := none
  institution  : String := "default-institution"
  secretKey    : String := Artifact.defaultDevSigningKey
  maxSkew      : Option Int := none

def parseServerOpts : List String → ServerCliOpts → Except String ServerCliOpts
  | [], o => .ok o
  | "--key" :: k :: rest, o => parseServerOpts rest { o with secretKey := k }
  | ["--key"], _ => .error "--key needs a secret key"
  | "--log" :: p :: rest, o => parseServerOpts rest { o with logPath := some p }
  | ["--log"], _ => .error "--log needs a file path"
  | "--snapshot" :: p :: rest, o => parseServerOpts rest { o with snapshotPath := some p }
  | ["--snapshot"], _ => .error "--snapshot needs a file path"
  | "--institution" :: id :: rest, o => parseServerOpts rest { o with institution := id }
  | ["--institution"], _ => .error "--institution needs an identifier"
  | "--max-skew" :: s :: rest, o => match s.toInt? with
    | some n => parseServerOpts rest { o with maxSkew := some n }
    | none => .error s!"--max-skew needs an integer, not {s}"
  | ["--max-skew"], _ => .error "--max-skew needs an integer"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.artifactPath.isNone then parseServerOpts rest { o with artifactPath := some a }
    else if o.logPath.isNone then parseServerOpts rest { o with logPath := some a }
    else .error s!"unexpected extra argument {a}"

partial def serveStdioLoop (stdin : IO.FS.Stream) (rt : InstitutionRuntime) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let trimmed := line.trim
  if trimmed.isEmpty then
    serveStdioLoop stdin rt
  else
    match Json.parse trimmed with
    | .error e =>
      IO.println (envelopeErr rt "parse" s!"invalid JSON request: {e}").compress
      serveStdioLoop stdin rt
    | .ok req =>
      let (rt', resp) ← handleRequest rt req
      IO.println resp.compress
      (← IO.getStdout).flush
      serveStdioLoop stdin rt'

def readFileOpt (cmd p : String) : IO (Option String) := do
  try
    let s ← IO.FS.readFile p
    return some s
  catch e =>
    IO.eprintln s!"charter-server {cmd}: {e}"
    return none

def serverMain (args : List String) : IO UInt32 := do
  match args with
  | [] | ["help"] | ["--help"] | ["-h"] =>
    IO.println serverHelp
    return 0
  | ["version"] | ["--version"] | ["-v"] =>
    IO.println "charter-server 0.4.0"
    return 0
  | "verify" :: rest =>
    match parseServerOpts rest {} with
    | .error e => IO.eprintln s!"charter-server verify: {e}"; return 2
    | .ok { artifactPath := none, .. } => IO.eprintln "usage: charter-server verify <file.artifact> [--key <secret>]"; return 2
    | .ok { artifactPath := some ap, secretKey, .. } =>
      let some raw ← readFileOpt "verify" ap | return 1
      match Artifact.verifyArtifactJson raw secretKey with
      | .error e =>
        IO.eprintln s!"FAIL {ap}: {e}"
        return 1
      | .ok ver =>
        let root := computeStateRoot ver.artifactSha256 ver.genesisConfig
        IO.println s!"ok   {ap}: verified sha256:{ver.artifactSha256} (keyId={ver.certificate.keyId}, coverage={ver.certificate.coverage}, genesisRoot={root})"
        return 0
  | "replay" :: rest =>
    match parseServerOpts rest {} with
    | .error e => IO.eprintln s!"charter-server replay: {e}"; return 2
    | .ok { artifactPath := some ap, logPath := some lp, snapshotPath, secretKey, .. } =>
      let some rawArt ← readFileOpt "replay" ap | return 1
      let ver ← match Artifact.verifyArtifactJson rawArt secretKey with
        | .ok v => pure v
        | .error e => IO.eprintln s!"FAIL {ap}: {e}"; return 1
      let some rawLog ← readFileOpt "replay" lp | return 1
      let entries ← match parseLogLines rawLog with
        | .ok es => pure es
        | .error e => IO.eprintln s!"FAIL {lp}: {e}"; return 1
      let (startCfg, startSeq, startPrev) ← match snapshotPath with
        | none => pure (ver.genesisConfig, 0, "GENESIS")
        | some sp =>
          let some rawSnap ← readFileOpt "replay" sp | return 1
          match (do let j ← Json.parse rawSnap; let sn ← fromJson? (α := Snapshot) j; verifySnapshot secretKey sn; .ok sn) with
          | .error e => IO.eprintln s!"FAIL snapshot {sp}: {e}"; return 1
          | .ok sn => pure (sn.config, sn.nextSeqNo, sn.lastEntryHash)
      match replayEntries secretKey ver.artifactSha256 startCfg startSeq startPrev entries with
      | .error e =>
        IO.eprintln s!"FAIL replay {lp}: {e}"
        return 1
      | .ok (_, finalRoot, lastHash) =>
        let out := Json.mkObj [
          ("ok", Json.bool true),
          ("artifactSha256", Json.str ver.artifactSha256),
          ("replayedEntries", Json.num entries.length),
          ("finalStateRoot", Json.str finalRoot),
          ("lastEntryHash", Json.str lastHash)
        ]
        IO.println out.compress
        return 0
    | .ok _ =>
      IO.eprintln "usage: charter-server replay <file.artifact> <file.log> [--snapshot <snap>] [--key <secret>]"
      return 2
  | "serve" :: rest =>
    match parseServerOpts rest {} with
    | .error e => IO.eprintln s!"charter-server serve: {e}"; return 2
    | .ok { artifactPath := none, .. } => IO.eprintln serverHelp; return 2
    | .ok { artifactPath := some ap, logPath, snapshotPath, institution, secretKey, maxSkew } =>
      let some rawArt ← readFileOpt "serve" ap | return 1
      let ver ← match Artifact.verifyArtifactJson rawArt secretKey with
        | .ok v => pure v
        | .error e => IO.eprintln s!"FAIL certificate-at-office {ap}: {e}"; return 1
      -- Cold-restart recovery (`T36`): restore from verified snapshot + log tail when present!
      let mut cfg := ver.genesisConfig
      let mut seqNo : Nat := 0
      let mut lastHash := "GENESIS"
      if let some sp := snapshotPath then
        if ← (System.FilePath.mk sp).pathExists then
          let rawSnap ← IO.FS.readFile sp
          match (do let j ← Json.parse rawSnap; let sn ← fromJson? (α := Snapshot) j; verifySnapshot secretKey sn; .ok sn) with
          | .error e => IO.eprintln s!"FAIL cold-restart snapshot {sp}: {e}"; return 1
          | .ok sn =>
            cfg := sn.config
            seqNo := sn.nextSeqNo
            lastHash := sn.lastEntryHash
      if let some lp := logPath then
        if ← (System.FilePath.mk lp).pathExists then
          let rawLog ← IO.FS.readFile lp
          match (do let es ← parseLogLines rawLog; replayEntries secretKey ver.artifactSha256 cfg seqNo lastHash es) with
          | .error e => IO.eprintln s!"FAIL cold-restart log replay {lp}: {e}"; return 1
          | .ok (cfgR, _, prevR) =>
            let esLen := ((rawLog.splitOn "\n" |>.map String.trim |>.filter (!·.isEmpty))).length
            cfg := cfgR
            seqNo := esLen
            lastHash := prevR
      let rt0 : InstitutionRuntime := {
        institutionId := institution
        lawHash := ver.artifactSha256
        certificate := ver.certificate
        config := cfg
        seqNo
        lastEntryHash := lastHash
        clockPolicy := { monotonic := true, maxSkew }
        logPath := logPath.map System.FilePath.mk
        snapshotPath := snapshotPath.map System.FilePath.mk
        secretKey
      }
      serveStdioLoop (← IO.getStdin) rt0
  | cmd :: _ =>
    IO.eprintln s!"charter-server: unknown command '{cmd}'\n{serverHelp}"
    return 2

end Charter.Server

def main (args : List String) : IO UInt32 :=
  Charter.Server.serverMain args
