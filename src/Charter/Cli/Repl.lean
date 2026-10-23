import Charter.Cli.Run

/-!
# Charter.Cli.Repl — `charter repl [file.eflint]`

Loads the file, if any, as `run` does, then reads phrases from standard input and
runs each against the current configuration, printing what `run` prints. A line is
parsed as a complete input (its final `.` may be omitted). Commands: `:display`
(`:d`) prints every instance that holds, `:help` (`:h`), `:quit` (`:q`). This is
eFLINT's `eflint-repl` without its exploration tree (`:jump`, `:revert`), which
belong to Phase 4's `--itf` traces.
-/

namespace Charter.Cli

def replHelp : String :=
  "commands:\n  :display  :d   every instance that holds\n  :help     :h   this list\n  :quit     :q   leave\nor type a phrase (the final `.` may be omitted)"

def display (cfg : Config) : IO Unit := do
  let hs := cfg.state.holdsList
  if hs.isEmpty then IO.println "(nothing holds)"
  for te in hs do IO.println s!"{te}"

def replLoop (o : RunOpts) (h : IO.FS.Stream) : Nat → Config → RunStats → IO RunStats
  | 0, _, stats => return stats
  | fuel + 1, cfg, stats => do
    IO.print "charter> "
    (← IO.getStdout).flush
    let line ← h.getLine
    if line.isEmpty then IO.println ""; return stats
    let line := line.trimRight
    match line.trim with
    | "" => replLoop o h fuel cfg stats
    | ":q" | ":quit" => return stats
    | ":h" | ":help" => IO.println replHelp; replLoop o h fuel cfg stats
    | ":d" | ":display" => display cfg; replLoop o h fuel cfg stats
    | _ =>
      match parseSource line with
      | .error e => IO.eprintln e.render; replLoop o h fuel cfg stats
      | .ok items =>
        let mut cfg := cfg
        let mut stats := stats
        for it in items do
          let (cfg', stats') ← stepItem o cfg stats ⟨"<repl>", it⟩
          cfg := cfg'
          stats := stats'
        replLoop o h fuel cfg stats

/-- `charter repl [file.eflint]` -/
def replCommand (args : List String) : IO UInt32 := do
  let o : RunOpts := {}
  let mut cfg : Config := {}
  let mut stats : RunStats := {}
  match args with
  | [] => pure ()
  | [f] =>
    let (items, loadDiags) ← loadProgram f
    for d in loadDiags do IO.eprintln d.render
    for l in items do
      let (cfg', stats') ← stepItem o cfg stats l
      cfg := cfg'
      stats := stats'
  | _ => IO.eprintln "usage: charter repl [file.eflint]"; return 2
  IO.println replHelp
  let final ← replLoop o (← IO.getStdin) 1000000 cfg stats
  return (if final.ok then 0 else 1)

end Charter.Cli
