import Charter.Cli.Load
import Charter.Cli.Provenance
import Charter.Eval.Interpreter
import Lean.Data.Json

/-!
# Charter.Cli.Run — `charter run <file>`, `charter check`, and the shared program driver

`run` executes a program's top-level phrases in order and prints, for each, what
it did: every executed transition with its three answers (Law 2: *occurred*,
*lawful*, *valid*), the violations it caused, the result of each query or
expectation, and the facts that changed. Scenarios (`Scenario name { … }`) are
run by `charter test` from the configuration at their point in the file and leave
it unchanged; `run` only notes them. `test` mode prints only diagnostics, failed
claims, and instance-query results, which is eFLINT's `--test-mode` criterion.

Flags shared by `run`, `test`, `check`: `--out json` makes every report one JSON
object per line (plan §3); `--eflint` restricts the keywords to eFLINT's, so a
corpus file that uses `Valid`, `Against`, or `Scenario` as an atom still reads as
eFLINT reads it.
-/

namespace Charter.Cli

open Lean (Json)

structure RunOpts where
  testMode  : Bool := false
  json      : Bool := false
  eflint    : Bool := false
  /-- Run `Scenario` blocks (test mode) instead of only noting them. -/
  scenarios : Bool := false
  /-- Explore enabled acts from the end state up to this depth (0 = off); plan §2.2.7. -/
  explore   : Nat := 0

structure RunStats where
  phrases       : Nat := 0
  errors        : Nat := 0
  warnings      : Nat := 0
  failedQueries : Nat := 0
  /-- Every diagnostic code produced, in order (for fixture directives). -/
  codes         : List String := []
  deriving Repr

def RunStats.ok (s : RunStats) : Bool := s.errors == 0 && s.failedQueries == 0

def yesNo (b : Bool) : String := if b then "yes" else "no"

/-- Render a transition tree as eFLINT's `showTriggerTree` does, with the three answers. -/
def renderTrans (info : TransInfo) (indent : String) (fuel : Nat) : List String :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let kind := if info.isAction then "act" else "event"
    let lawful := if info.isAction then s!"   lawful: {yesNo (!info.disabled)}" else ""
    let head := s!"{indent}occurred {kind} {info.tagged}{lawful}   valid: {yesNo info.valid}"
    head :: info.syncs.flatMap (renderTrans · (indent ++ "  ") fuel)

def transJson (info : TransInfo) (fuel : Nat) : Json :=
  match fuel with
  | 0 => Json.null
  | fuel + 1 =>
    Json.mkObj ([("act", Json.str info.tagged.pp), ("kind", Json.str (if info.isAction then "act" else "event")),
      ("occurred", Json.bool true), ("valid", Json.bool info.valid)] ++
      (if info.isAction then [("lawful", Json.bool (!info.disabled))] else []) ++
      [("syncs", Json.arr (info.syncs.map (transJson · fuel)).toArray)])

def renderViolation : Violation → String
  | .duty te => s!"violation: duty {te} is violated"
  | .invariant d => s!"violation: invariant {d} does not hold"
  | .trigger info => s!"violation: {if info.isAction then "act" else "event"} {info.tagged} was performed while disabled"

def violationJson : Violation → Json
  | .duty te => Json.mkObj [("kind", "violation"), ("of", "duty"), ("instance", Json.str te.pp)]
  | .invariant d => Json.mkObj [("kind", "violation"), ("of", "invariant"), ("name", Json.str d)]
  | .trigger info => Json.mkObj [("kind", "violation"), ("of", "disabled"), ("instance", Json.str info.tagged.pp)]

def diagJson (d : Diagnostic) : Json :=
  Json.mkObj [("kind", "diagnostic"), ("code", Json.str d.code), ("severity", Json.str (toString d.severity)),
    ("message", Json.str d.message), ("file", Json.str d.file), ("line", Json.num d.pos.line), ("col", Json.num d.pos.col),
    ("notes", Json.arr (d.notes.map Json.str).toArray)]

/-- The fact changes between two states (eFLINT `display_fact_changes`). -/
def factChanges (before after : State) : List (String × Tagged) :=
  let gone := before.contents.filter (fun (te, _) => (after.lookup te).isNone) |>.map fun (te, _) => ("~", te)
  let nowFalse := after.notHoldsList.filter (fun te => !(before.notHoldsList.contains te)) |>.map fun te => ("-", te)
  let nowTrue := after.holdsList.filter (fun te => !(before.holdsList.contains te)) |>.map fun te => ("+", te)
  gone ++ nowFalse ++ nowTrue

def emit (o : RunOpts) (j : Json) (text : String) (toErr : Bool := false) : IO Unit :=
  if o.json then IO.println j.compress
  else if toErr then IO.eprintln text else IO.println text

/-- Print what one phrase reported and update the statistics. -/
def report (o : RunOpts) (file : String) (line : Nat) (text : String) (before after : State)
    (outs : List Output) (stats : RunStats) : IO RunStats := do
  let where_ := s!"{file}:{line}"
  let mut stats := stats
  for out in outs do
    match out with
    | .diag d =>
      let d := (d.withFile file).withPos ⟨line, 0⟩
      stats := { stats with codes := stats.codes ++ [d.code] }
      if d.isError then stats := { stats with errors := stats.errors + 1 }
      else stats := { stats with warnings := stats.warnings + 1 }
      if d.isError || !o.testMode || o.json then emit o (diagJson d) d.render (toErr := true)
    | .queryRes ok =>
      if !ok then stats := { stats with failedQueries := stats.failedQueries + 1 }
      let j := Json.mkObj [("kind", "claim"), ("claim", Json.str text), ("tag", "checked"), ("about", "holds"),
        ("result", Json.bool ok), ("file", Json.str file), ("line", Json.num line)]
      if !ok then emit o j s!"{where_}: query failed: {text}"
      else if !o.testMode then emit o j "  query holds"
    | .expectRes w neg ok =>
      if !ok then stats := { stats with failedQueries := stats.failedQueries + 1 }
      let j := Json.mkObj [("kind", "claim"), ("claim", Json.str text), ("tag", "checked"), ("about", Json.str w.name),
        ("negated", Json.bool neg), ("result", Json.bool ok), ("file", Json.str file), ("line", Json.num line)]
      if !ok then emit o j s!"{where_}: claim failed: {text}"
      else if !o.testMode then emit o j s!"  {if neg then "not " else ""}{w.name}: as claimed"
    | .timeSet t =>
      emit o (Json.mkObj [("kind", "clock"), ("time", Json.num t)]) (if o.testMode then "" else s!"  clock: {t}")
    | .whyRes lines =>
      if o.json then IO.println (Json.mkObj [("kind", "why"), ("claim", Json.str text), ("instances", Json.arr (lines.map Json.str).toArray)]).compress
      else for l in lines do IO.println s!"  {l}"
    | .instQueryRes tes =>
      if o.json then
        IO.println (Json.mkObj [("kind", "instances"), ("claim", Json.str text),
          ("instances", Json.arr (tes.map (fun te => Json.str te.pp)).toArray)]).compress
      else
        for te in tes do IO.println s!"{te}"
        IO.println ""
    | .executed info =>
      if o.json then IO.println (Json.mkObj [("kind", "transition"), ("transition", transJson info 1000)]).compress
      else if !o.testMode then
        for l in renderTrans info "  " 1000 do IO.println l
    | .violation v =>
      if o.json then IO.println (violationJson v).compress
      else if !o.testMode then IO.println s!"  {renderViolation v}"
  if !o.testMode then
    for (ch, te) in factChanges before after do
      emit o (Json.mkObj [("kind", "fact"), ("change", Json.str ch), ("instance", Json.str te.pp)]) s!"  {ch}{te}"
  return stats

/-- Explore from a configuration (plan §2.2.7): a violated invariant within the depth
is a failed claim whose text is the shortest trace. -/
def exploreFrom (o : RunOpts) (where_ : String) (cfg : Config) (stats : RunStats) : IO RunStats := do
  if o.explore == 0 || cfg.spec.invariants.isEmpty then return stats
  match Explore.bfs cfg o.explore 5000 with
  | .error e =>
    let d := Diagnostic.error e.code e.message
    emit o (diagJson d) d.render (toErr := true)
    return { stats with errors := stats.errors + 1, codes := stats.codes ++ [d.code] }
  | .safe n =>
    let j := Json.mkObj [("kind", "claim"), ("tag", "checked"), ("about", "invariants"), ("result", Json.bool true),
      ("depth", Json.num o.explore), ("states", Json.num n)]
    if !o.testMode || o.json then emit o j s!"{where_}: explore: no invariant violated within {o.explore} step(s) ({n} states)"
    return stats
  | .violated d trace n =>
    let traceS := ", ".intercalate (trace.map Tagged.pp)
    let j := Json.mkObj [("kind", "claim"), ("tag", "checked"), ("about", "invariants"), ("result", Json.bool false),
      ("invariant", Json.str d), ("trace", Json.arr (trace.map (fun te => Json.str te.pp)).toArray), ("states", Json.num n)]
    emit o j s!"{where_}: explore: invariant {d} violated after {trace.length} step(s): {if trace.isEmpty then "(already in the end state)" else traceS}"
    return { stats with failedQueries := stats.failedQueries + 1 }

/-- Run a scenario's phrases from `cfg`, reporting under the scenario's name; the
configuration is not changed. -/
def runScenario (o : RunOpts) (file : String) (line : Nat) (name : String) (cfg : Config) (ps : List Phrase)
    (stats : RunStats) : IO RunStats := do
  let mut cfg := cfg
  let mut stats := stats
  let mut k := 0
  for p in ps do
    k := k + 1
    let (cfg', outs) := runPhrase cfg p
    stats := { stats with phrases := stats.phrases + 1 }
    stats ← report o s!"{file} [scenario {name}, phrase {k}]" line s!"scenario {name}, phrase {k}" cfg.state cfg'.state outs stats
    cfg := cfg'
  exploreFrom o s!"{file}:{line} [scenario {name}]" cfg stats

/-- Run one located item. -/
def stepItem (o : RunOpts) (cfg : Config) (stats : RunStats) (l : Located) : IO (Config × RunStats) := do
  let it := l.item
  match it.val with
  | .inl _ => return (cfg, stats)
  | .inr (.scenario name ps) =>
    if o.json then
      IO.println (Json.mkObj [("kind", "scenario"), ("name", Json.str name), ("file", Json.str l.file),
        ("line", Json.num it.pos.line), ("phrases", Json.num ps.length), ("run", Json.bool o.scenarios)]).compress
    else if !o.testMode then
      IO.println s!"{l.file}:{it.pos.line}: Scenario {name} ({ps.length} phrases{if o.scenarios then "" else "; charter test runs it"})"
    if o.scenarios then
      let stats ← runScenario o l.file it.pos.line name cfg ps stats
      return (cfg, stats)
    else return (cfg, stats)
  | .inr p =>
    if !o.testMode && !o.json then
      IO.println s!"{l.file}:{it.pos.line}: {it.text}"
    if o.json then
      IO.println (Json.mkObj [("kind", "phrase"), ("file", Json.str l.file), ("line", Json.num it.pos.line), ("text", Json.str it.text)]).compress
    let (cfg', outs) := runPhrase cfg p
    let stats := { stats with phrases := stats.phrases + 1 }
    let stats ← report o l.file it.pos.line it.text cfg.state cfg'.state outs stats
    return (cfg', stats)

/-- Print the provenance report of a resolved spec (Law 8); returns the number of
failed checks. -/
def reportProvenance (o : RunOpts) (spec : Spec) (programDir : System.FilePath) : IO Nat := do
  if spec.clauses.isEmpty && spec.document.isNone then return 0
  let doc? ← readDocument spec programDir
  let claims := provenanceReport spec doc?
  let mut failed := 0
  for c in claims do
    if !c.ok then failed := failed + 1
    if o.json then IO.println c.json.compress
    else if !c.ok || c.warn || !o.testMode then IO.println c.render
  return failed

/-- Run a whole program. In test mode the provenance checks run at the end and a
failed check is a failed claim. -/
def runProgram (o : RunOpts) (path : System.FilePath) : IO RunStats := do
  let (items, loadDiags) ← loadProgram path o.eflint
  let mut stats : RunStats := {}
  for d in loadDiags do
    emit o (diagJson d) d.render (toErr := true)
    stats := { stats with codes := stats.codes ++ [d.code] }
    if d.isError then stats := { stats with errors := stats.errors + 1 }
  let mut cfg : Config := {}
  for l in items do
    let (cfg', stats') ← stepItem o cfg stats l
    cfg := cfg'
    stats := stats'
  stats ← exploreFrom o s!"{path}" cfg stats
  let failedProv ← reportProvenance o cfg.spec (path.parent.getD ".")
  return { stats with failedQueries := stats.failedQueries + failedProv }

/-- The flags shared by `run`, `test`, `check`: `--out json|text`, `--eflint`. -/
structure RunFlags where
  json    : Bool := false
  eflint  : Bool := false
  explore : Nat := 0
  rest    : List String := []

def takeFlags (args : List String) : Except String RunFlags :=
  let rec go : List String → RunFlags → Except String RunFlags
    | [], f => .ok { f with rest := f.rest.reverse }
    | "--out" :: "json" :: rest, f => go rest { f with json := true }
    | "--out" :: "text" :: rest, f => go rest f
    | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
    | ["--out"], _ => .error "--out needs json or text"
    | "--eflint" :: rest, f => go rest { f with eflint := true }
    | "--explore" :: n :: rest, f => match n.toNat? with
      | some k => go rest { f with explore := k }
      | none => .error s!"--explore needs a depth, not {n}"
    | ["--explore"], _ => .error "--explore needs a depth"
    | a :: rest, f => go rest { f with rest := a :: f.rest }
  go args {}

def summaryJson (stats : RunStats) : Json :=
  Json.mkObj [("kind", "summary"), ("phrases", Json.num stats.phrases), ("errors", Json.num stats.errors),
    ("warnings", Json.num stats.warnings), ("failedQueries", Json.num stats.failedQueries), ("ok", Json.bool stats.ok)]

/-- `charter run <file.eflint> [--out json] [--eflint]` -/
def runCommand (args : List String) : IO UInt32 := do
  match takeFlags args with
  | .error e => IO.eprintln s!"charter run: {e}"; return 2
  | .ok { json, eflint, explore, rest := [f] } =>
    let stats ← runProgram { json, eflint, explore } f
    if json then IO.println (summaryJson stats).compress
    else IO.println s!"{stats.phrases} phrase(s), {stats.errors} error(s), {stats.failedQueries} failed claim(s)"
    return (if stats.ok then 0 else 1)
  | .ok _ =>
    IO.eprintln "usage: charter run <file.eflint> [--out json] [--eflint] [--explore <depth>]"
    return 2

/-- `charter check <file.eflint> ... [--out json] [--eflint]`: resolve every phrase in
order without evaluating anything; report the diagnostics. -/
def checkCommand (args : List String) : IO UInt32 := do
  let fl ← match takeFlags args with
    | .error e => IO.eprintln s!"charter check: {e}"; return 2
    | .ok r => pure r
  let o : RunOpts := { json := fl.json, eflint := fl.eflint }
  let mut status : UInt32 := 0
  for f in fl.rest do
    let (items, loadDiags) ← loadProgram f fl.eflint
    let mut errors := 0
    let mut warnings := 0
    for d in loadDiags do
      emit o (diagJson d) d.render (toErr := true)
      if d.isError then errors := errors + 1 else warnings := warnings + 1
    let mut spec := emptySpec
    for l in items do
      match l.item.val with
      | .inl _ => pure ()
      | .inr p =>
        match resolvePhrase spec p with
        | .error ds =>
          for d in ds do
            let d := (d.withFile l.file).withPos l.item.pos
            emit o (diagJson d) d.render (toErr := true)
            errors := errors + 1
        | .ok (spec', _, ws) =>
          spec := spec'
          for w in ws do
            let w := (w.withFile l.file).withPos l.item.pos
            emit o (diagJson w) w.render (toErr := true)
            warnings := warnings + 1
    let failedProv ← reportProvenance o spec ((System.FilePath.mk f).parent.getD ".")
    errors := errors + failedProv
    let okLine := s!"ok   {f}: {items.length} phrase(s) resolve ({spec.decls.length - 3} declared types, {spec.clauses.length} clauses, {warnings} warning(s))"
    let failLine := s!"FAIL {f}: {errors} error(s) or failed checks, {warnings} warning(s)"
    emit o (Json.mkObj [("kind", "summary"), ("file", Json.str f), ("phrases", Json.num items.length),
      ("errors", Json.num errors), ("warnings", Json.num warnings), ("ok", Json.bool (errors == 0))])
      (if errors == 0 then okLine else failLine)
    if errors != 0 then status := 1
  return status

/-- `charter trace <clause> <file.eflint>`: the span table of one clause. -/
def traceCommand (cid : String) (args : List String) : IO UInt32 := do
  let fl ← match takeFlags args with
    | .error e => IO.eprintln s!"charter trace: {e}"; return 2
    | .ok r => pure r
  match fl.rest with
  | [f] =>
    let (items, loadDiags) ← loadProgram f fl.eflint
    for d in loadDiags do IO.eprintln d.render
    let mut spec := emptySpec
    for l in items do
      match l.item.val with
      | .inr p => match resolvePhrase spec p with
        | .ok (spec', _, _) => spec := spec'
        | .error _ => pure ()
      | .inl _ => pure ()
    match spec.clauses.find? (·.id == cid) with
    | some c => IO.println (traceTable c); return 0
    | none => IO.println s!"no clause {cid}; known: {", ".intercalate (spec.clauses.map (·.id))}"; return 1
  | _ => IO.eprintln "usage: charter trace <clause-id> <file.eflint>"; return 2

end Charter.Cli
