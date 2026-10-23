import Charter.Cli.Load
import Charter.Eval.Interpreter

/-!
# Charter.Cli.Run — `charter run <file>` and the shared program driver

`run` executes a program's phrases in order and prints, for each, what it did:
every executed transition with its three answers (Law 2: *occurred*, *lawful*,
*valid*; in Phase 1 every act that occurs is valid, D5), the violations it
caused, the result of each query, and the facts that changed. `test` mode
(`Charter.Cli.Test`) prints only diagnostics, failed queries, and instance-query
results, which is eFLINT's `--test-mode` criterion.
-/

namespace Charter.Cli

structure RunStats where
  phrases       : Nat := 0
  errors        : Nat := 0
  failedQueries : Nat := 0
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

def renderViolation : Violation → String
  | .duty te => s!"violation: duty {te} is violated"
  | .invariant d => s!"violation: invariant {d} does not hold"
  | .trigger info => s!"violation: {if info.isAction then "act" else "event"} {info.tagged} was performed while disabled"

/-- The fact changes between two states (eFLINT `display_fact_changes`). -/
def factChanges (before after : State) : List String :=
  let gone := before.contents.filter (fun (te, _) => (after.lookup te).isNone) |>.map fun (te, _) => s!"~{te}"
  let nowFalse := after.notHoldsList.filter (fun te => !(before.notHoldsList.contains te)) |>.map fun te => s!"-{te}"
  let nowTrue := after.holdsList.filter (fun te => !(before.holdsList.contains te)) |>.map fun te => s!"+{te}"
  gone ++ nowFalse ++ nowTrue

/-- Run one located phrase, printing according to `testMode`. -/
def stepItem (testMode : Bool) (cfg : Config) (stats : RunStats) (l : Located) : IO (Config × RunStats) := do
  let it := l.item
  match it.val with
  | .inl _ => return (cfg, stats)
  | .inr p =>
    let where_ := s!"{l.file}:{it.pos.line}"
    let (cfg', outs) := runPhrase cfg p
    let mut stats := { stats with phrases := stats.phrases + 1 }
    if !testMode then
      IO.println s!"{where_}: {it.text}"
    for o in outs do
      match o with
      | .diag d =>
        let d := (d.withFile l.file).withPos it.pos
        if d.isError then stats := { stats with errors := stats.errors + 1 }
        if d.isError || !testMode then IO.eprintln d.render
      | .queryRes ok =>
        if !ok then
          stats := { stats with failedQueries := stats.failedQueries + 1 }
          IO.println s!"{where_}: query failed: {it.text}"
        else if !testMode then IO.println "  query holds"
      | .instQueryRes tes =>
        for te in tes do IO.println s!"{te}"
        IO.println ""
      | .executed info =>
        if !testMode then
          for line in renderTrans info "  " 1000 do IO.println line
      | .violation v =>
        if !testMode then IO.println s!"  {renderViolation v}"
    if !testMode then
      for c in factChanges cfg.state cfg'.state do IO.println s!"  {c}"
    return (cfg', stats)

/-- Run a whole program. -/
def runProgram (testMode : Bool) (path : System.FilePath) : IO RunStats := do
  let (items, loadDiags) ← loadProgram path
  let mut stats : RunStats := {}
  for d in loadDiags do
    IO.eprintln d.render
    if d.isError then stats := { stats with errors := stats.errors + 1 }
  let mut cfg : Config := {}
  for l in items do
    let (cfg', stats') ← stepItem testMode cfg stats l
    cfg := cfg'
    stats := stats'
  return stats

/-- `charter run <file.eflint>` -/
def runCommand (args : List String) : IO UInt32 := do
  match args with
  | [f] =>
    let stats ← runProgram false f
    IO.println s!"{stats.phrases} phrase(s), {stats.errors} error(s), {stats.failedQueries} failed quer{if stats.failedQueries == 1 then "y" else "ies"}"
    return (if stats.ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: charter run <file.eflint>"
    return 2

/-- `charter check <file.eflint>`: resolve every phrase in order without
evaluating anything; report the diagnostics. -/
def checkCommand (args : List String) : IO UInt32 := do
  let mut status : UInt32 := 0
  for f in args do
    let (items, loadDiags) ← loadProgram f
    let mut errors := 0
    let mut warnings := 0
    for d in loadDiags do
      IO.eprintln d.render
      if d.isError then errors := errors + 1 else warnings := warnings + 1
    let mut spec := emptySpec
    for l in items do
      match l.item.val with
      | .inl _ => pure ()
      | .inr p =>
        match resolvePhrase spec p with
        | .error ds =>
          for d in ds do
            IO.eprintln ((d.withFile l.file).withPos l.item.pos).render
            errors := errors + 1
        | .ok (spec', _, ws) =>
          spec := spec'
          for w in ws do
            IO.eprintln ((w.withFile l.file).withPos l.item.pos).render
            warnings := warnings + 1
    if errors == 0 then
      IO.println s!"ok   {f}: {items.length} phrase(s) resolve ({spec.decls.length - 3} declared types, {warnings} warning(s))"
    else
      IO.println s!"FAIL {f}: {errors} error(s), {warnings} warning(s)"
      status := 1
  return status

end Charter.Cli
