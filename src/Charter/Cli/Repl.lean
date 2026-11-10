import Charter.Cli.Run
import Charter.Verify.Explorer

/-!
# Charter.Cli.Repl — `charter repl [file.charter]`

Loads the file, if any, as `run` does, then reads phrases from standard input and
runs each against the current configuration, maintaining an indexed configuration
history (`D44`, `018.2`). Commands:
- `:display`  (`:d`)       — every instance that holds
- `:options`  (`:o`)       — every currently enabled or valid action instance
- `:duties`                — every holding duty instance (`[active]`, `[late]`, `[VIOLATED]`)
- `:history`  (`:hist`)    — configuration history steps (`*` marks current step)
- `:revert`   (`:r`)       — step back to the previous configuration
- `:jump <n>` (`:j <n>`)   — jump to configuration step `<n>`
- `:help`     (`:h`)       — command list
- `:quit`     (`:q`)       — leave
-/

namespace Charter.Cli

def replHelp : String :=
  "commands:\n" ++
  "  :display   :d      every instance that holds\n" ++
  "  :options   :o      every enabled or valid action instance\n" ++
  "  :duties            every holding duty instance and status\n" ++
  "  :history   :hist   list configuration history steps\n" ++
  "  :revert    :r      revert to previous configuration step\n" ++
  "  :jump <n>  :j <n>  jump to configuration step <n>\n" ++
  "  :help      :h      this list\n" ++
  "  :quit      :q      leave\n" ++
  "or type a phrase (the final `.` may be omitted)"

def display (cfg : Config) : IO Unit := do
  let hs := cfg.state.holdsList
  if hs.isEmpty then IO.println "(nothing holds)"
  for te in hs do IO.println s!"{te}"

def displayOptions (cfg : Config) : IO Unit := do
  let ctx := Ctx.of cfg.spec cfg.state
  match Verify.candidateSteps .adversarial [] cfg with
  | .error e => IO.eprintln s!"error enumerating options: {e.message}"
  | .ok steps =>
    let mut shown := 0
    for st in steps do
      if let .trigger te := st then
        match cfg.spec.findDecl te.2 with
        | some { kind := .act _, .. } =>
          match (M.ignoreMissingInput (M.evalActTri M.fuel te)).run ctx [] with
          | .ok ((lTri, vTri, _) :: _) =>
            if lTri == .yes || vTri == .yes then
              IO.println s!"  {te.pp}  [lawful={lTri.asString}, valid={vTri.asString}]"
              shown := shown + 1
          | _ => pure ()
        | some { kind := .event _, .. } =>
          IO.println s!"  {te.pp}  [event]"
          shown := shown + 1
        | _ => pure ()
    if shown == 0 then IO.println "(no enabled or valid actions)"

def displayDuties (cfg : Config) : IO Unit := do
  let ctx := Ctx.of cfg.spec cfg.state
  let duties := cfg.state.holdsList.filter fun te =>
    match cfg.spec.findDecl te.2 with
    | some { kind := .duty _, .. } => true
    | _ => false
  if duties.isEmpty then
    IO.println "(no active duties)"
  else
    for te in duties do
      let isViol := cfg.violatedDuties.contains te
      let isLate := !isViol && (match cfg.spec.findDecl te.2 with
        | some { kind := .duty ds, .. } =>
          !ds.lateWhen.isEmpty && (match (M.ignoreMissingInput (M.evalViolationCondition M.fuel te (some ds.lateWhen))).run ctx [] with
            | .ok rs => rs.any id | .error _ => false)
        | _ => false)
      let tag := if isViol then "[VIOLATED]" else if isLate then "[late]" else "[active]"
      IO.println s!"  {te.pp}  {tag}"

def displayHistory (hist : Array (Config × String)) (curIdx : Nat) : IO Unit := do
  for idx in List.range hist.size do
    if let some (c, lbl) := hist[idx]? then
      let mark := if idx == curIdx then "*" else " "
      IO.println s!" {mark} [{idx}] time={c.state.time} ({c.state.holdsList.length} holding) — {lbl}"

def replLoop (o : RunOpts) (h : IO.FS.Stream) :
    Nat → Array (Config × String) → Nat → RunStats → IO RunStats
  | 0, _, _, stats => return stats
  | fuel + 1, hist, curIdx, stats => do
    let cfg := (hist[curIdx]?.map (·.1)).getD {}
    IO.print "charter> "
    (← IO.getStdout).flush
    let line ← h.getLine
    if line.isEmpty then IO.println ""; return stats
    let line := line.trimRight
    let cmd := line.trim
    if cmd.isEmpty then
      replLoop o h fuel hist curIdx stats
    else if cmd == ":q" || cmd == ":quit" then
      return stats
    else if cmd == ":h" || cmd == ":help" then
      IO.println replHelp
      replLoop o h fuel hist curIdx stats
    else if cmd == ":d" || cmd == ":display" then
      display cfg
      replLoop o h fuel hist curIdx stats
    else if cmd == ":o" || cmd == ":options" then
      displayOptions cfg
      replLoop o h fuel hist curIdx stats
    else if cmd == ":duties" then
      displayDuties cfg
      replLoop o h fuel hist curIdx stats
    else if cmd == ":history" || cmd == ":hist" then
      displayHistory hist curIdx
      replLoop o h fuel hist curIdx stats
    else if cmd == ":r" || cmd == ":revert" then
      if curIdx == 0 then
        IO.println "(already at initial step 0)"
        replLoop o h fuel hist 0 stats
      else
        let prev := curIdx - 1
        IO.println s!"reverted to step {prev}"
        replLoop o h fuel hist prev stats
    else if cmd.startsWith ":jump " || cmd.startsWith ":j " then
      let argStr := (if cmd.startsWith ":jump " then cmd.drop 6 else cmd.drop 3).trim
      match argStr.toNat? with
      | some target =>
        if target < hist.size then
          IO.println s!"jumped to step {target}"
          replLoop o h fuel hist target stats
        else
          IO.eprintln s!"step {target} out of range (0 .. {hist.size - 1})"
          replLoop o h fuel hist curIdx stats
      | none =>
        IO.eprintln s!"usage: :jump <0..{hist.size - 1}>"
        replLoop o h fuel hist curIdx stats
    else
      match parseSource line with
      | .error e => IO.eprintln e.render; replLoop o h fuel hist curIdx stats
      | .ok items =>
        let mut cfg' := cfg
        let mut stats' := stats
        let mut mutated := false
        for it in items do
          let (cNext, sNext, _, _) ← stepItem o cfg' stats' ⟨"<repl>", it⟩
          if cNext.state.step != cfg'.state.step || cNext.state.time != cfg'.state.time ||
             cNext.state.holdsList.length != cfg'.state.holdsList.length ||
             cNext.spec.decls.length != cfg'.spec.decls.length then
            mutated := true
          cfg' := cNext
          stats' := sNext
        if mutated then
          let prefixHist := (hist.toList.take (curIdx + 1)).toArray
          let hist' := prefixHist.push (cfg', cmd)
          replLoop o h fuel hist' (hist'.size - 1) stats'
        else
          replLoop o h fuel hist curIdx stats'

/-- `charter repl [file.charter]` -/
def replCommand (args : List String) : IO UInt32 := do
  let o : RunOpts := { scenarios := true }
  let mut cfg : Config := {}
  let mut stats : RunStats := {}
  let mut initLabel := "empty"
  match args with
  | [] => pure ()
  | [f] =>
    initLabel := s!"loaded {f}"
    let (items, loadDiags) ← loadProgram f
    for d in loadDiags do IO.eprintln d.render
    for l in items do
      let (cfg', stats', _, _) ← stepItem o cfg stats l
      cfg := cfg'
      stats := stats'
  | _ => IO.eprintln "usage: charter repl [file.charter]"; return 2
  IO.println replHelp
  let final ← replLoop o (← IO.getStdin) 1000000 #[(cfg, initLabel)] 0 stats
  return (if final.ok then 0 else 1)

end Charter.Cli
