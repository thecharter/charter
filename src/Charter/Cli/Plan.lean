import Charter.Cli.Explain
import Charter.Cli.Test
import Charter.Eval.Plan

/-!
# Charter.Cli.Plan — CLI Goal Planner (`charter plan`, `#70`) & Missing-Input Inspector (`charter inputs`, `#68`)
-/

namespace Charter.Cli

open Lean (Json)

structure PlanCliOpts where
  expr     : Option String := none
  file     : Option String := none
  scenario : Option String := none
  depth    : Nat := 5
  json     : Bool := false

def parsePlanCliArgs : List String → PlanCliOpts → Except String PlanCliOpts
  | [], o => .ok o
  | "--scenario" :: s :: rest, o => parsePlanCliArgs rest { o with scenario := some s }
  | ["--scenario"], _ => .error "--scenario needs a scenario name"
  | "--depth" :: n :: rest, o =>
    match n.toNat? with
    | some k => parsePlanCliArgs rest { o with depth := k }
    | none => .error s!"--depth needs a natural number, not `{n}`"
  | ["--depth"], _ => .error "--depth needs a number"
  | "--out" :: "json" :: rest, o => parsePlanCliArgs rest { o with json := true }
  | "--out" :: "text" :: rest, o => parsePlanCliArgs rest { o with json := false }
  | ["--out"], _ => .error "--out needs `json` or `text`"
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown flag `{a}`"
    else if o.expr.isNone then parsePlanCliArgs rest { o with expr := some a }
    else if o.file.isNone then parsePlanCliArgs rest { o with file := some a }
    else .error s!"unexpected extra argument `{a}`"

def resolveSingleInstance (cfg : Config) (exprSrc : String) : Except String Tagged := do
  let rawTerm ← match parseSource (exprSrc ++ ".") with
    | .ok [it] =>
      match it.val with
      | .inr (.trigger _ t _) => .ok t
      | .inr (.query t) => .ok t
      | _ => .error s!"`{exprSrc}` is not an instance expression"
    | _ => .error s!"could not parse `{exprSrc}`"
  let (_, cp, _) ← match resolvePhrase cfg.spec (.why rawTerm) with
    | .ok r => .ok r
    | .error ds => .error ("; ".intercalate (ds.map (·.message)))
  match cp with
  | .why xs t' =>
    let ctx := Ctx.of cfg.spec cfg.state
    match (M.foreach M.fuel xs (M.whenTagged (M.eval M.fuel t') pure)).run ctx [] with
    | .ok vss =>
      match vss.flatten with
      | te :: _ => .ok te
      | [] => .error s!"`{exprSrc}` produced no instance"
    | .error e => .error e.message
  | _ => .error s!"unexpected compiled query for `{exprSrc}`"

def planStepJson : Plan.PlanStep → Json
  | .act actor te =>
    Json.mkObj [
      ("kind", Json.str "act"),
      ("actor", Json.str actor),
      ("instance", Json.str te.pp)
    ]
  | .wait target delta =>
    Json.mkObj [
      ("kind", Json.str "wait"),
      ("targetTime", Json.num target),
      ("delta", Json.num delta)
    ]

/-- `charter plan <act(args)> <file.charter> [--scenario <name>] [--depth <N>] [--out json]` (`#70`). -/
def planCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter plan \"<act(args)>\" <file.charter> [--scenario <name>] [--depth <N>] [--out json]"
  let opts ← match parsePlanCliArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter plan: {e}\n{usage}"; return 2
  let (exprSrc, file) ← match opts.expr, opts.file with
    | some e, some f => pure (e, f)
    | _, _ => IO.eprintln usage; return 2
  let src ← try IO.FS.readFile file catch _ => pure ""
  let dirs := readDirectives src
  let (items, loadDiags) ← loadProgram file
  if loadDiags.any (·.isError) then
    for d in loadDiags do if d.isError then IO.eprintln d.render
    return 1
  let cfg ← match evalToExplainState items opts.scenario with
    | .ok c => pure c
    | .error e => IO.eprintln s!"charter plan: {e}"; return 1
  let targetTe ← match resolveSingleInstance cfg exprSrc with
    | .ok te => pure te
    | .error e => IO.eprintln s!"charter plan: {e}"; return 1
  let res := Plan.findShortestPlan cfg targetTe opts.depth 600 dirs.exploreMenu
  match res with
  | .alreadyEnabled =>
    if opts.json then
      IO.println (Json.mkObj [
        ("kind", Json.str "plan"),
        ("target", Json.str targetTe.pp),
        ("status", Json.str "AlreadyEnabled"),
        ("steps", Json.arr #[]),
        ("visitedStates", Json.num 1)
      ]).compress
    else
      IO.println s!"plan {targetTe.pp}: already lawful and valid (0 step(s))"
    return 0
  | .found steps visited =>
    if opts.json then
      IO.println (Json.mkObj [
        ("kind", Json.str "plan"),
        ("target", Json.str targetTe.pp),
        ("status", Json.str "PlanFound"),
        ("steps", Json.arr (steps.map planStepJson).toArray),
        ("visitedStates", Json.num visited)
      ]).compress
    else
      IO.println s!"plan {targetTe.pp}: {steps.length} step(s) found ({visited} state(s) searched)"
      let mut idx := 1
      for st in steps do
        IO.println s!"  {idx}. {st.render}"
        idx := idx + 1
    return 0
  | .unreachable visited bound =>
    if opts.json then
      IO.println (Json.mkObj [
        ("kind", Json.str "plan"),
        ("target", Json.str targetTe.pp),
        ("status", Json.str "Unreachable"),
        ("steps", Json.arr #[]),
        ("visitedStates", Json.num visited),
        ("maxDepth", Json.num bound)
      ]).compress
    else
      IO.println s!"plan {targetTe.pp}: no lawful and valid sequence found within {bound} step(s) ({visited} state(s) searched)"
    return 1

def inputSchemaJson (s : Plan.InputTypeSchema) : Json :=
  Json.mkObj [
    ("name", Json.str s.name),
    ("inputKind", Json.str s.inputKind),
    ("confidential", Json.bool s.confidential),
    ("audiences", Json.arr (s.audiences.map Json.str).toArray),
    ("components", Json.arr (s.components.map fun c =>
      Json.mkObj [
        ("param", Json.str c.paramName),
        ("domain", Json.str c.domName),
        ("kind", Json.str c.domKind),
        ("choices", Json.arr (c.choices.map Json.str).toArray)
      ]).toArray)
  ]

/-- `charter inputs [<act(args)>] <file.charter> [--scenario <name>] [--out json]` (`#68`). -/
def inputsCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter inputs [\"<act(args)>\"] <file.charter> [--scenario <name>] [--out json]"
  let opts ← match parsePlanCliArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"charter inputs: {e}\n{usage}"; return 2
  -- When 1 positional arg is passed, it is `<file.charter>` (schema listing); when 2, `<expr>` and `<file.charter>`
  let (actExpr?, file) ← match opts.expr, opts.file with
    | some f, none => pure (none, f)
    | some e, some f => pure (some e, f)
    | _, _ => IO.eprintln usage; return 2
  let (items, loadDiags) ← loadProgram file
  if loadDiags.any (·.isError) then
    for d in loadDiags do if d.isError then IO.eprintln d.render
    return 1
  let cfg ← match evalToExplainState items opts.scenario with
    | .ok c => pure c
    | .error e => IO.eprintln s!"charter inputs: {e}"; return 1
  match actExpr? with
  | none =>
    let schemas := Plan.extractInputSchemas cfg.spec
    if opts.json then
      IO.println (Json.mkObj [
        ("kind", Json.str "input-schema"),
        ("file", Json.str file),
        ("types", Json.arr (schemas.map inputSchemaJson).toArray)
      ]).compress
    else if schemas.isEmpty then
      IO.println s!"{file}: 0 open or evidenced input types"
    else
      for s in schemas do
        let params := ", ".intercalate (s.components.map fun c =>
          let ch := if c.choices.isEmpty then c.domKind else s!"{c.domKind}[{", ".intercalate c.choices}]"
          s!"{c.paramName}: {ch}")
        IO.println s!"{s.inputKind} {s.name}({params})"
    return 0
  | some exprSrc =>
    let targetTe ← match resolveSingleInstance cfg exprSrc with
      | .ok te => pure te
      | .error e => IO.eprintln s!"charter inputs: {e}"; return 1
    let miss := Plan.inspectMissingInputs cfg targetTe
    if opts.json then
      IO.println (Json.mkObj [
        ("kind", Json.str "missing-inputs"),
        ("subject", Json.str miss.subject),
        ("openFacts", Json.arr (miss.openFacts.map Json.str).toArray),
        ("openDomains", Json.arr (miss.openDomains.map Json.str).toArray),
        ("unmetEvidence", Json.arr (miss.unmetEvidence.map fun (f, st) =>
          Json.mkObj [("fact", Json.str f), ("status", Json.str st.asString)]).toArray)
      ]).compress
    else
      IO.println s!"inputs for {miss.subject}:"
      IO.println s!"  open facts: {if miss.openFacts.isEmpty then "(none)" else ", ".intercalate miss.openFacts}"
      IO.println s!"  open domains: {if miss.openDomains.isEmpty then "(none)" else ", ".intercalate miss.openDomains}"
      let evStr := if miss.unmetEvidence.isEmpty then "(none)"
                   else ", ".intercalate (miss.unmetEvidence.map fun (f, st) => s!"{f} ({st.asString})")
      IO.println s!"  unmet evidence: {evStr}"
    return 0

end Charter.Cli
