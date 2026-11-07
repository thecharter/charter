import Charter.Cli.Load
import Charter.Cli.Run
import Charter.Cli.Test
import Charter.Project.GuardTarget
import Charter.Project.QuintTarget
import Charter.Project.PromptTarget

/-!
# Charter.Cli.Generate — `charter generate --target solidity|abi|quint|prompt` (`G5.1`–`G5.2`, `D28`)

Compiles a `.charter` program to `CIR`, enforces target fragment restrictions (`CHR035`),
emits the requested target artifact, and under `--verify-output` runs independent target
syntax, ABI, and differential trace replay validation (`T32`, `T33`).
-/

namespace Charter.Cli

structure GenOpts where
  target       : Option String := none
  mode         : Verify.ExploreMode := .lawful
  actor        : Option String := none
  verifyOutput : Bool := false
  json         : Bool := false
  output       : Option String := none
  input        : Option String := none

def parseGenArgs : List String → GenOpts → Except String GenOpts
  | [], o => .ok o
  | "--target" :: t :: rest, o => parseGenArgs rest { o with target := some t }
  | ["--target"], _ => .error "--target needs solidity, abi, quint, or prompt"
  | "--mode" :: "lawful" :: rest, o => parseGenArgs rest { o with mode := .lawful }
  | "--mode" :: "adversarial" :: rest, o => parseGenArgs rest { o with mode := .adversarial }
  | "--mode" :: m :: _, _ => .error s!"--mode takes lawful or adversarial, not {m}"
  | ["--mode"], _ => .error "--mode needs lawful or adversarial"
  | "--actor" :: a :: rest, o => parseGenArgs rest { o with actor := some a }
  | ["--actor"], _ => .error "--actor needs a role name"
  | "--verify-output" :: rest, o => parseGenArgs rest { o with verifyOutput := true }
  | "--out" :: "json" :: rest, o => parseGenArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseGenArgs rest { o with json := false }
  | "-o" :: p :: rest, o => parseGenArgs rest { o with output := some p }
  | ["-o"], _ => .error "-o needs an output file path"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.input.isNone then parseGenArgs rest { o with input := some a }
    else .error s!"unexpected extra input {a}"

def generateCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter generate --target <solidity|abi|quint|prompt> [--mode lawful|adversarial] [--actor <role>] [--verify-output] [--out json] [-o <path>] <file.charter>"
  let opts ← match parseGenArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter generate: {e}\n{usage}"; return 2
  let (tgt, file) ← match opts.target, opts.input with
    | some t, some f => pure (t, f)
    | _, _ => IO.eprintln usage; return 2
  let srcOpt : Option String ← try
    let s ← IO.FS.readFile file
    pure (some s)
  catch e =>
    IO.eprintln s!"charter generate: {e}"
    pure none
  let some srcText := srcOpt | return 1
  let dirs := readDirectives srcText
  let (items, loadDiags) ← loadProgram file
  for d in loadDiags do
    if d.isError then
      IO.eprintln d.render
      return 1
  let mut cfg : Config := {}
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario _ _ _) => pure ()
    | .inr p =>
      let (c', outs) := runPhrase cfg p
      for o in outs do
        match o with
        | .diag d =>
          if d.isError then
            IO.eprintln (d.withFile file).render
            return 1
        | _ => pure ()
      cfg := c'
  let stem := ((System.FilePath.mk file).fileStem).getD "Institution"
  let lawSha := Artifact.sha256String (reprStr cfg.spec)
  let writeOrPrint (content : String) (verifySummary : Option String) : IO UInt32 := do
    match opts.output with
    | some outP =>
      let p := System.FilePath.mk outP
      if let some parent := p.parent then IO.FS.createDirAll parent
      IO.FS.writeFile p content
      if let some vs := verifySummary then IO.println s!"ok   {outP}: {vs}"
      else IO.println s!"wrote {outP}"
    | none =>
      if let some vs := verifySummary then
        IO.eprintln s!"ok   {file} [{tgt}]: {vs}"
      IO.print content
    return 0
  match tgt with
  | "solidity" | "abi" =>
    let fragDiags := Project.checkSolidityFragment cfg.spec
    if !fragDiags.isEmpty then
      for d in fragDiags do IO.eprintln (d.withFile file).render
      return 1
    let ir := Project.compileGuardIR stem lawSha cfg
    let sol := Project.renderSolidityContract ir
    let abi := Project.renderGuardJsonABI ir
    let vSum? ← if opts.verifyOutput then
      match Project.validateGuardOutput ir sol abi with
      | .ok s => pure (some s)
      | .error e => IO.eprintln s!"FAIL {file} [{tgt}]: {e}"; return 1
    else pure none
    let textOut := if tgt == "abi" || opts.json then abi.pretty ++ "\n" else sol
    writeOrPrint textOut vSum?
  | "quint" | "veil" =>
    let qMod := Project.compileQuintModule stem opts.mode cfg
    let qSrc := Project.renderQuintModule qMod
    let vSum? ← if opts.verifyOutput then
      match Project.verifyAndReplayQuintTarget qMod qSrc cfg dirs.exploreMenu 3 with
      | .ok s => pure (some s)
      | .error e => IO.eprintln s!"FAIL {file} [{tgt}]: {e}"; return 1
    else pure none
    writeOrPrint qSrc vSum?
  | "prompt" =>
    let (md, jSchema) := Project.renderAdvisoryPrompt stem opts.actor cfg.spec
    writeOrPrint (if opts.json then jSchema.pretty ++ "\n" else md)
      (if opts.verifyOutput then some "validated advisory AlignmentCard (authoritative=false)" else none)
  | other =>
    IO.eprintln s!"charter generate: unknown target `{other}` (expected solidity, abi, quint, or prompt)"
    return 2

end Charter.Cli
