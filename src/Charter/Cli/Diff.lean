import Charter.Project.Diff

/-!
# Charter.Cli.Diff — `charter diff <old.charter> <new.charter> [--out json] [--require-approved]`

Runs the 3-view semantic diff (`Charter.Project.Diff`). With `--require-approved`, exits
with status `1` if `reviewRequiredCount > 0` (`T38`) or `entrenchedViolations` is non-empty.
-/

namespace Charter.Cli

structure DiffOpts where
  oldFile         : Option String := none
  newFile         : Option String := none
  json            : Bool := false
  requireApproved : Bool := false
  impact          : Bool := false

def parseDiffArgs : List String → DiffOpts → Except String DiffOpts
  | [], o => .ok o
  | "--out" :: "json" :: rest, o => parseDiffArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parseDiffArgs rest { o with json := false }
  | "--out" :: other :: _, _ => .error s!"--out takes json or text, not {other}"
  | ["--out"], _ => .error "--out needs json or text"
  | "--require-approved" :: rest, o => parseDiffArgs rest { o with requireApproved := true }
  | "--impact" :: rest, o => parseDiffArgs rest { o with impact := true }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag {a}"
    else if o.oldFile.isNone then parseDiffArgs rest { o with oldFile := some a }
    else if o.newFile.isNone then parseDiffArgs rest { o with newFile := some a }
    else .error s!"unexpected extra argument {a}"

def diffCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter diff <old.charter> <new.charter> [--impact] [--out json] [--require-approved]"
  let opts ← match parseDiffArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter diff: {e}\n{usage}"; return 2
  let (oldF, newF) ← match opts.oldFile, opts.newFile with
    | some o, some n => pure (o, n)
    | _, _ => IO.eprintln usage; return 2
  let (oldItems, oldDiags) ← loadProgram oldF
  let (newItems, newDiags) ← loadProgram newF
  for d in oldDiags ++ newDiags do
    if d.isError then
      IO.eprintln d.render
      return 1
  let oldPhrases := oldItems.filterMap fun l => match l.item.val with | .inr p => some p | .inl _ => none
  let newPhrases := newItems.filterMap fun l => match l.item.val with | .inr p => some p | .inl _ => none
  let rep := Project.computeDiff oldF newF oldPhrases newPhrases opts.impact
  if opts.json then IO.println (Project.DiffReport.toJson rep).compress
  else IO.println (Project.DiffReport.renderText rep)
  if !rep.entrenchedViolations.isEmpty then return 1
  if opts.requireApproved && rep.reviewRequiredCount > 0 then return 1
  return 0

end Charter.Cli
