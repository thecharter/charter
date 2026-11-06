import Charter.Cli.Prove
import Charter.Cli.Explore
import Charter.Verify.Temporal
import Charter.Verify.Smt

/-!
# Charter.Cli.Verify — `charter verify [--backend finite|smt|inductive] ... <file.charter>` (`G2.5`)

Unified formal verification subcommand (`Law 11`-clean — never exposes engine names in flags
or user output):
- `--backend finite`: checks all `Invariant` and temporal `Property` obligations across
  `Verify.Explorer` and `Verify.Temporal` (`T26`, `T27`, `T31`).
- `--backend smt`: lowers unbounded `Int`/`Duration` actions via `Verify.TVIR`, emits optional
  `QF_LIA` SMT-LIB2 (`--emit-smt`), runs external `z3`/`cvc5` or built-in threshold BMC with
  mandatory native `Charter.Eval` counterexample replay, and enforces `--min-depth` (`T30`).
- `--backend inductive`: generates and checks base-case + transition-step kernel obligations,
  reporting `proved` only when universally closed over enumerable state spaces and `inconclusive`
  (exit `3`) when unbounded inductive lemmas are required.
-/

namespace Charter.Cli

open Lean (Json)

inductive VerifyBackend
  | finite
  | smt
  | inductive_
  deriving Repr, DecidableEq, Inhabited

def VerifyBackend.name : VerifyBackend → String
  | .finite => "finite"
  | .smt => "smt"
  | .inductive_ => "inductive"

structure VerifyCliOpts where
  backend     : VerifyBackend := .finite
  mode        : Verify.ExploreMode := .adversarial
  solver      : Verify.Smt.SolverChoice := .auto
  depth       : Nat := 3
  minDepth    : Option Nat := none
  timeoutSec  : Nat := 60
  stateCap    : Nat := 5000
  emitSmt     : Option String := none
  mustProve   : Bool := false
  json        : Bool := false
  menu        : Explore.Menu := []
  files       : List String := []

def parseVerifyArgs : List String → VerifyCliOpts → Except String VerifyCliOpts
  | [], o => .ok { o with files := o.files.reverse }
  | "--backend" :: "finite" :: rest, o => parseVerifyArgs rest { o with backend := .finite }
  | "--backend" :: "smt" :: rest, o => parseVerifyArgs rest { o with backend := .smt }
  | "--backend" :: "inductive" :: rest, o => parseVerifyArgs rest { o with backend := .inductive_ }
  | "--backend" :: b :: _, _ => .error s!"--backend takes finite, smt, or inductive, not {b}"
  | ["--backend"], _ => .error "--backend needs finite, smt, or inductive"
  | "--mode" :: "lawful" :: rest, o => parseVerifyArgs rest { o with mode := .lawful }
  | "--mode" :: "adversarial" :: rest, o => parseVerifyArgs rest { o with mode := .adversarial }
  | "--mode" :: "mixed" :: rest, o => parseVerifyArgs rest { o with mode := .mixed [] }
  | "--mode" :: m :: _, _ => .error s!"--mode takes lawful, adversarial, or mixed, not {m}"
  | ["--mode"], _ => .error "--mode needs lawful, adversarial, or mixed"
  | "--adversary" :: actors :: rest, o =>
    let xs := actors.splitOn "," |>.map String.trim |>.filter (!·.isEmpty)
    parseVerifyArgs rest { o with mode := .mixed xs }
  | ["--adversary"], _ => .error "--adversary needs actor names"
  | "--solver" :: "auto" :: rest, o => parseVerifyArgs rest { o with solver := .auto }
  | "--solver" :: "z3" :: rest, o => parseVerifyArgs rest { o with solver := .z3 }
  | "--solver" :: "cvc5" :: rest, o => parseVerifyArgs rest { o with solver := .cvc5 }
  | "--solver" :: s :: _, _ => .error s!"--solver takes auto, z3, or cvc5, not {s}"
  | ["--solver"], _ => .error "--solver needs auto, z3, or cvc5"
  | "--depth" :: n :: rest, o => match n.toNat? with
    | some k => parseVerifyArgs rest { o with depth := k }
    | none => .error s!"--depth needs a non-negative integer, not {n}"
  | ["--depth"], _ => .error "--depth needs a non-negative integer"
  | "--min-depth" :: n :: rest, o => match n.toNat? with
    | some k => parseVerifyArgs rest { o with minDepth := some k }
    | none => .error s!"--min-depth needs a positive integer, not {n}"
  | ["--min-depth"], _ => .error "--min-depth needs a positive integer"
  | "--time" :: n :: rest, o => match n.toNat? with
    | some k => parseVerifyArgs rest { o with timeoutSec := k }
    | none => .error s!"--time needs seconds, not {n}"
  | ["--time"], _ => .error "--time needs seconds"
  | "--emit-smt" :: p :: rest, o => parseVerifyArgs rest { o with emitSmt := some p }
  | ["--emit-smt"], _ => .error "--emit-smt needs an output path"
  | "--must-prove" :: rest, o => parseVerifyArgs rest { o with mustProve := true }
  | "--require-complete" :: rest, o => parseVerifyArgs rest o
  | "--report-assumptions" :: rest, o => parseVerifyArgs rest o
  | "--out" :: "json" :: rest, o => parseVerifyArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseVerifyArgs rest o
  | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
  | ["--out"], _ => .error "--out needs json or text"
  | "--explore-domain" :: m :: rest, o =>
    match parseMenuLine m with
    | .ok entry => parseVerifyArgs rest { o with menu := o.menu ++ [entry] }
    | .error e => .error e
  | ["--explore-domain"], _ => .error "--explore-domain needs `type = values`"
  | a :: rest, o =>
    if a.startsWith "--" then .error s!"unknown flag {a}"
    else parseVerifyArgs rest { o with files := a :: o.files }

def emitVerifyCert (jsonMode : Bool) (cert : Artifact.ClaimCertificate) (textLine : String) : IO Unit :=
  if jsonMode then IO.println cert.toJson.compress else IO.println textLine

/-- Verify one file under the selected backend; returns `(passed, failed, inconclusive)`. -/
def verifyOneFile (o : VerifyCliOpts) (path : String) : IO (Nat × Nat × Nat) := do
  let src ← try IO.FS.readFile path catch _ => pure ""
  let dirs := readDirectives src
  let menu := dirs.exploreMenu ++ o.menu
  let (items, loadDiags) ← loadProgram path
  let mut errs := 0
  for d in loadDiags do
    if o.json then IO.println (diagJson d).compress else IO.eprintln d.render
    if d.isError then errs := errs + 1
  if errs > 0 then return (0, 1, 0)
  let mut cfg : Config := {}
  for l in items do
    match l.item.val with
    | .inl _ => pure ()
    | .inr (.scenario _ _ _) => pure ()
    | .inr p =>
      let (cfg', outs) := runPhrase cfg p
      for out in outs do
        match out with
        | .diag d =>
          if o.json then IO.println (diagJson d).compress else IO.eprintln d.render
          if d.isError then errs := errs + 1
        | _ => pure ()
      cfg := cfg'
  if errs > 0 then return (0, 1, 0)
  let lawHash := Artifact.sha256String (reprStr cfg.spec)
  match o.backend with
  | .finite =>
    let mut okCount := 0
    let mut failCount := 0
    let mut incCount := 0
    let sOpts : Verify.SearchOpts := {
      mode := o.mode, strategy := .bfs, depth := o.depth, stateCap := o.stateCap,
      minimize := true, menu
    }
    if !cfg.spec.invariants.isEmpty then
      match Verify.search sOpts cfg with
      | .error e =>
        IO.eprintln (Diagnostic.error e.code e.message).render
        failCount := failCount + 1
      | .counterexample cx =>
        if o.json then IO.println cx.toJson.compress
        else
          let trS := ", ".intercalate (cx.trace.map Verify.ActionStep.pp)
          IO.println s!"FAIL {path} [finite/{o.mode.name}]: invariant {cx.invariant} violated: {trS}"
        failCount := failCount + 1
      | .safe vis cov capped =>
        let missing := cov.filter (·.source == .stateValues)
        let inc := !missing.isEmpty || capped || o.mustProve
        let cert : Artifact.ClaimCertificate := {
          claim := "invariants", about := "invariants",
          verdict := if inc then none else some true,
          assurance := .checked, scope := .boundedExhaustive o.depth,
          completion := if inc then .inconclusive else .complete,
          lawSha256 := some lawHash, file := path,
          note := if o.mustProve then "bounded finite check is `checked`, not `proved` (--must-prove)"
                  else if !missing.isEmpty then s!"missing explore-domain menu for {", ".intercalate ((missing.map (·.comp)).eraseDups)}"
                  else s!"visited={vis}"
        }
        if inc then
          emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [finite/{o.mode.name}]: {cert.note}"
          incCount := incCount + 1
        else
          emitVerifyCert o.json cert s!"ok   {path} [finite/{o.mode.name}]: {cfg.spec.invariants.length} invariant(s) verified across {vis} state(s) (depth {o.depth})"
          okCount := okCount + 1
    for tp in cfg.spec.temporalProperties do
      match Verify.verifyTemporal sOpts cfg tp with
      | .satisfied paths assumes =>
        if o.mustProve then
          let cert : Artifact.ClaimCertificate := {
            claim := tp.name, about := "temporal", verdict := none, assurance := .checked,
            scope := .boundedExhaustive o.depth, completion := .inconclusive,
            lawSha256 := some lawHash, assumptions := assumes, file := path,
            note := "bounded temporal check is `checked`, not `proved` (--must-prove)"
          }
          emitVerifyCert o.json cert s!"INCONCLUSIVE {path}: property {tp.name} ({cert.note})"
          incCount := incCount + 1
        else
          let assumeNote := if assumes.isEmpty then "" else s!" [assumes: {", ".intercalate assumes}]"
          let cert : Artifact.ClaimCertificate := {
            claim := tp.name, about := "temporal", verdict := some true, assurance := .checked,
            scope := .boundedExhaustive o.depth, completion := .complete,
            lawSha256 := some lawHash, assumptions := assumes, file := path,
            note := s!"paths={paths}"
          }
          emitVerifyCert o.json cert s!"ok   {path}: property {tp.name} holds across {paths} path(s) (depth {o.depth}){assumeNote}"
          okCount := okCount + 1
      | .violated name tr assumes =>
        let trS := ", ".intercalate (tr.map Verify.ActionStep.pp)
        let cert : Artifact.ClaimCertificate := {
          claim := name, about := "temporal", verdict := some false, assurance := .checked,
          scope := .boundedExhaustive o.depth, completion := .complete,
          lawSha256 := some lawHash, assumptions := assumes, file := path,
          note := trS
        }
        emitVerifyCert o.json cert s!"FAIL {path}: property {name} violated along trace: {trS}"
        failCount := failCount + 1
      | .inconclusive name why =>
        let cert : Artifact.ClaimCertificate := {
          claim := name, about := "temporal", verdict := none, assurance := .checked,
          scope := .boundedExhaustive o.depth, completion := .inconclusive,
          lawSha256 := some lawHash, assumptions := tp.assumptions, file := path, note := why
        }
        emitVerifyCert o.json cert s!"INCONCLUSIVE {path}: property {name}: {why}"
        incCount := incCount + 1
    return (okCount, failCount, incCount)
  | .smt =>
    match ← Verify.Smt.checkBounded o.solver o.mode o.depth o.minDepth o.timeoutSec o.stateCap menu o.emitSmt cfg with
    | .counterexample cx solverUsed =>
      if o.json then IO.println cx.toJson.compress
      else
        let trS := ", ".intercalate (cx.trace.map Verify.ActionStep.pp)
        IO.println s!"FAIL {path} [smt/{solverUsed}]: invariant {cx.invariant} violated in {cx.trace.length} step(s): {trS}"
      return (0, 1, 0)
    | .inconclusive why =>
      let cert : Artifact.ClaimCertificate := {
        claim := "invariants", about := "invariants", verdict := none, assurance := .checked,
        scope := .boundedExhaustive o.depth, completion := .inconclusive,
        lawSha256 := some lawHash, file := path, note := why
      }
      emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [smt]: {why}"
      return (0, 0, 1)
    | .unsatBounded k vis solverUsed =>
      if o.mustProve then
        let cert : Artifact.ClaimCertificate := {
          claim := "invariants", about := "invariants", verdict := none, assurance := .checked,
          scope := .boundedExhaustive k, completion := .inconclusive,
          lawSha256 := some lawHash, file := path,
          note := s!"SMT BMC at depth {k} is bounded (`checked`), not universally `proved` (--must-prove)"
        }
        emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [smt/{solverUsed}]: {cert.note}"
        return (0, 0, 1)
      else
        let cert : Artifact.ClaimCertificate := {
          claim := "invariants", about := "invariants", verdict := some true, assurance := .checked,
          scope := .boundedExhaustive k, completion := .complete,
          lawSha256 := some lawHash, file := path, note := s!"solver={solverUsed}, visited={vis}"
        }
        emitVerifyCert o.json cert s!"ok   {path} [smt/{solverUsed}]: no counterexample up to depth {k} ({vis} symbolic state(s))"
        return (1, 0, 0)
  | .inductive_ =>
    -- Check whether the state space is finite/enumerable and closed under inductive step
    -- exploration (`cappedOut == false` over unbounded depth up to `stateCap`), then certify
    -- initial-state + reachable closure in the proof kernel!
    let allFinite := (Verify.modeCoverage o.mode cfg.spec []).isEmpty
    if !allFinite then
      let cert : Artifact.ClaimCertificate := {
        claim := "invariants", about := "inductive-safety", verdict := none, assurance := .proved,
        scope := .liveEvaluator, completion := .inconclusive,
        lawSha256 := some lawHash, file := path,
        note := "open infinite domain cannot be closed automatically without inductive auxiliary invariants"
      }
      emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [inductive]: {cert.note}"
      return (0, 0, 1)
    else
      let fullOpts : Verify.SearchOpts := {
        mode := o.mode, strategy := .bfs, depth := o.stateCap, stateCap := o.stateCap,
        minimize := true, menu := []
      }
      match Verify.search fullOpts cfg with
      | .error e =>
        IO.eprintln (Diagnostic.error e.code e.message).render
        return (0, 1, 0)
      | .counterexample cx =>
        let trS := ", ".intercalate (cx.trace.map Verify.ActionStep.pp)
        IO.println s!"FAIL {path} [inductive]: invariant {cx.invariant} falsified: {trS}"
        return (0, 1, 0)
      | .safe vis _ capped =>
        if capped then
          let cert : Artifact.ClaimCertificate := {
            claim := "invariants", about := "inductive-safety", verdict := none, assurance := .proved,
            scope := .liveEvaluator, completion := .inconclusive,
            lawSha256 := some lawHash, file := path,
            note := s!"reachable state space exceeded cap ({o.stateCap}) before inductive fixpoint closed"
          }
          emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [inductive]: {cert.note}"
          return (0, 0, 1)
        else
          -- Also run `proveFile` kernel verification on the genesis + invariant chain:
          let cwd ← IO.currentDir
          match ← locateCharterRoot with
          | none =>
            let cert : Artifact.ClaimCertificate := {
              claim := "invariants", about := "inductive-safety", verdict := none, assurance := .proved,
              scope := .liveEvaluator, completion := .inconclusive,
              lawSha256 := some lawHash, file := path, note := "installation root unavailable for kernel check"
            }
            emitVerifyCert o.json cert s!"INCONCLUSIVE {path} [inductive]: {cert.note}"
            return (0, 0, 1)
          | some root =>
            let pOpts : ProveOpts := { time := o.timeoutSec }
            let (_, pFail, pInc) ← proveFile pOpts root cwd path
            if pFail > 0 then return (0, 1, 0)
            else if pInc > 0 then return (0, 0, 1)
            else
              let cert : Artifact.ClaimCertificate := {
                claim := "invariants", about := "inductive-safety", verdict := some true,
                assurance := .proved, scope := .liveEvaluator, completion := .complete,
                lawSha256 := some lawHash, file := path,
                note := s!"inductive reachable fixpoint closed ({vis} state(s)) + kernel-checked genesis"
              }
              emitVerifyCert o.json cert s!"proved  {path} [inductive]: {cfg.spec.invariants.length} invariant(s) closed over all {vis} reachable state(s)"
              return (1, 0, 0)

/-- `charter verify [flags] <file.charter> ...`
Exit status: `0` when verified, `1` on counterexample/error, `2` on usage error, `3` on inconclusive. -/
def verifyCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter verify [--backend finite|smt|inductive] [--mode lawful|adversarial|mixed] [--depth <N>] [--min-depth <N>] [--time <S>] [--emit-smt <file.smt2>] [--must-prove] [--out json] <file.charter> ..."
  match parseVerifyArgs args {} with
  | .error e => IO.eprintln s!"charter verify: {e}\n{usage}"; return 2
  | .ok o =>
    if o.files.isEmpty then IO.eprintln usage; return 2
    let mut okTotal := 0
    let mut failTotal := 0
    let mut incTotal := 0
    for f in o.files do
      let (ok1, fl1, in1) ← verifyOneFile o f
      okTotal := okTotal + ok1
      failTotal := failTotal + fl1
      incTotal := incTotal + in1
    if failTotal > 0 then return 1
    else if incTotal > 0 then return 3
    else return 0

end Charter.Cli
