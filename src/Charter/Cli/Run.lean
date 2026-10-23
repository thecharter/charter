import Charter.Cli.Load
import Charter.Eval.Interpreter
import Lean.Data.Json

/-!
# Charter.Cli.Run — `charter run <file>`, `charter check`, and the shared program driver

`run` executes a program's phrases in order and prints, for each, what it did:
every executed transition with its three answers (Law 2: *occurred*, *lawful*,
*valid*; in Phase 1 every act that occurs is valid, D5), the violations it
caused, the result of each query, and the facts that changed. `test` mode
(`Charter.Cli.Test`) prints only diagnostics, failed queries, and instance-query
results, which is eFLINT's `--test-mode` criterion.

With `--out json` every report is one JSON object per line (plan §3: diagnostics
and claims are data): `{"kind":"diagnostic", code, severity, message, file,
line, col}`, `{"kind":"claim", claim, tag:"checked", about:"holds", result, …}`,
`{"kind":"transition", act, occurred, lawful, valid, syncs}`,
`{"kind":"violation", …}`, `{"kind":"fact", change, instance}`, and a final
`{"kind":"summary", …}`.
-/

namespace Charter.Cli

open Lean (Json)

structure RunOpts where
  testMode : Bool := false
  json     : Bool := false

structure RunStats where
  phrases       : Nat := 0
  errors        : Nat := 0
  warnings      : Nat := 0
  failedQueries : Nat := 0
  /-- Every diagnostic code produced, in order (for fixture directives). -/
  codes         : List String := []
  deriving Repr

def RunStats.ok (s : RunStats) : Bool := s.errors == 0 && s.failedQueries == 0

/-- Render a transition tree as eFLINT's `showTriggerTree` does, with the three answers. -/
def renderTrans (info : TransInfo) (indent : String) (fuel : Nat) : List String :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let kind := if info.isAction then "act" else "event"
    let lawful := if info.isAction then (if info.disabled then "   lawful: no" else "   lawful: yes") else ""
    let head := s!"{indent}occurred {kind} {info.tagged}{lawful}   valid: yes"
    head :: info.syncs.flatMap (renderTrans · (indent ++ "  ") fuel)

def transJson (info : TransInfo) (fuel : Nat) : Json :=
  match fuel with
  | 0 => Json.null
  | fuel + 1 =>
    Json.mkObj ([("act", Json.str info.tagged.pp), ("kind", Json.str (if info.isAction then "act" else "event")),
      ("occurred", Json.bool true), ("valid", Json.bool true)] ++
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

/-- Run one located phrase, printing according to the options. -/
def stepItem (o : RunOpts) (cfg : Config) (stats : RunStats) (l : Located) : IO (Config × RunStats) := do
  let it := l.item
  match it.val with
  | .inl _ => return (cfg, stats)
  | .inr p =>
    let where_ := s!"{l.file}:{it.pos.line}"
    let (cfg', outs) := runPhrase cfg p
    let mut stats := { stats with phrases := stats.phrases + 1 }
    if !o.testMode && !o.json then
      IO.println s!"{where_}: {it.text}"
    if o.json then
      IO.println (Json.mkObj [("kind", "phrase"), ("file", Json.str l.file), ("line", Json.num it.pos.line), ("text", Json.str it.text)]).compress
    for out in outs do
      match out with
      | .diag d =>
        let d := (d.withFile l.file).withPos it.pos
        stats := { stats with codes := stats.codes ++ [d.code] }
        if d.isError then stats := { stats with errors := stats.errors + 1 }
        else stats := { stats with warnings := stats.warnings + 1 }
        if d.isError || !o.testMode || o.json then emit o (diagJson d) d.render (toErr := true)
      | .queryRes ok =>
        if !ok then stats := { stats with failedQueries := stats.failedQueries + 1 }
        let j := Json.mkObj [("kind", "claim"), ("claim", Json.str it.text), ("tag", "checked"), ("about", "holds"),
          ("result", Json.bool ok), ("file", Json.str l.file), ("line", Json.num it.pos.line)]
        if !ok then emit o j s!"{where_}: query failed: {it.text}"
        else if !o.testMode then emit o j "  query holds"
      | .instQueryRes tes =>
        if o.json then
          IO.println (Json.mkObj [("kind", "instances"), ("claim", Json.str it.text),
            ("instances", Json.arr (tes.map (fun te => Json.str te.pp)).toArray)]).compress
        else
          for te in tes do IO.println s!"{te}"
          IO.println ""
      | .executed info =>
        if o.json then IO.println (Json.mkObj [("kind", "transition"), ("transition", transJson info 1000)]).compress
        else if !o.testMode then
          for line in renderTrans info "  " 1000 do IO.println line
      | .violation v =>
        if o.json then IO.println (violationJson v).compress
        else if !o.testMode then IO.println s!"  {renderViolation v}"
    if !o.testMode then
      for (ch, te) in factChanges cfg.state cfg'.state do
        emit o (Json.mkObj [("kind", "fact"), ("change", Json.str ch), ("instance", Json.str te.pp)]) s!"  {ch}{te}"
    return (cfg', stats)

/-- Run a whole program. -/
def runProgram (o : RunOpts) (path : System.FilePath) : IO RunStats := do
  let (items, loadDiags) ← loadProgram path
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
  return stats

/-- Split `--out json` off an argument list. -/
def takeOutFlag (args : List String) : Except String (Bool × List String) :=
  let rec go : List String → List String → Except String (Bool × List String)
    | [], acc => .ok (false, acc.reverse)
    | "--out" :: "json" :: rest, acc => (go rest acc).map fun (_, r) => (true, r)
    | "--out" :: "text" :: rest, acc => go rest acc
    | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
    | ["--out"], _ => .error "--out needs json or text"
    | a :: rest, acc => go rest (a :: acc)
  go args []

def summaryJson (stats : RunStats) : Json :=
  Json.mkObj [("kind", "summary"), ("phrases", Json.num stats.phrases), ("errors", Json.num stats.errors),
    ("warnings", Json.num stats.warnings), ("failedQueries", Json.num stats.failedQueries), ("ok", Json.bool stats.ok)]

/-- `charter run <file.eflint> [--out json]` -/
def runCommand (args : List String) : IO UInt32 := do
  match takeOutFlag args with
  | .error e => IO.eprintln s!"charter run: {e}"; return 2
  | .ok (json, [f]) =>
    let stats ← runProgram { json } f
    if json then IO.println (summaryJson stats).compress
    else IO.println s!"{stats.phrases} phrase(s), {stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"}"
    return (if stats.ok then 0 else 1)
  | .ok _ =>
    IO.eprintln "usage: charter run <file.eflint> [--out json]"
    return 2

/-- `charter check <file.eflint> ... [--out json]`: resolve every phrase in order
without evaluating anything; report the diagnostics. -/
def checkCommand (args : List String) : IO UInt32 := do
  let (json, files) ← match takeOutFlag args with
    | .error e => IO.eprintln s!"charter check: {e}"; return 2
    | .ok r => pure r
  let o : RunOpts := { json }
  let mut status : UInt32 := 0
  for f in files do
    let (items, loadDiags) ← loadProgram f
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
    let okLine := s!"ok   {f}: {items.length} phrase(s) resolve ({spec.decls.length - 3} declared types, {warnings} warning(s))"
    let failLine := s!"FAIL {f}: {errors} error(s), {warnings} warning(s)"
    emit o (Json.mkObj [("kind", "summary"), ("file", Json.str f), ("phrases", Json.num items.length),
      ("errors", Json.num errors), ("warnings", Json.num warnings), ("ok", Json.bool (errors == 0))])
      (if errors == 0 then okLine else failLine)
    if errors != 0 then status := 1
  return status

end Charter.Cli
