import Charter.Core.Spec
import Lean.Data.Json

/-!
# Charter.Project.PromptTarget — Advisory Role-Scoped Briefings & Tool Schemas (`G5.1`, §9.7)

Projects live `Core.Spec` (`CIR`) records into human/agent-readable `AlignmentCard` briefings
and JSON tool schemas citing verbatim English `From` spans.

Per `docs/rfc.md` §9.7, every output is explicitly stamped `"advisoryOnly": true` and
`"authoritative": false` — `charter-server` remains the sole authoritative enforcement boundary.
-/

namespace Charter.Project

open Lean (Json)

def renderAdvisoryPrompt (title : String) (actorFilter? : Option String) (spec : Spec) : String × Json :=
  let matchesActor (d : DomId) : Bool :=
    match actorFilter? with
    | none => true
    | some want =>
      match spec.components d with
      | v :: _ => v.dom == want || toString v == want
      | [] => true
  let powers := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .act a => if matchesActor d then some (d, a.isPower, t.spans) else none
    | _ => none
  let duties := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .duty _ => if matchesActor d then some (d, t.spans) else none
    | _ => none
  let immunities := spec.decls.filterMap fun (d, t) =>
    match t.kind with
    | .immunity im => some (d, im.against, t.spans)
    | _ => none
  let header := s!"# Charter Advisory Role Briefing — {title}\n\n" ++
    "> **ADVISORY ARTIFACT (`authoritative = false`)**: This briefing summarizes formal institutional rules and verbatim English spans for planning and explanation only. It is NOT an enforcement boundary; all authoritative legal judgments and execution capabilities are decided by `charter-server` (`docs/rfc.md` §9.7).\n\n"
  let roleLine := match actorFilter? with | some r => s!"Role scope: `{r}`\n\n" | none => "Role scope: all roles\n\n"
  let powSec := "## Actions & Institutional Powers\n" ++ "\n".intercalate (powers.map fun (d, isP, sps) =>
    let kind := if isP then "Power (requires Valid when)" else "Act"
    let sp := if sps.isEmpty then "" else " — " ++ "; ".intercalate (sps.map fun (c, q) => s!"[{c}] {showString q}")
    s!"- `{d}` ({kind}){sp}")
  let dutySec := "## Duties & Deadlines\n" ++ "\n".intercalate (duties.map fun (d, sps) =>
    let sp := if sps.isEmpty then "" else " — " ++ "; ".intercalate (sps.map fun (c, q) => s!"[{c}] {showString q}")
    s!"- `{d}`{sp}")
  let immSec := "## Immunities\n" ++ "\n".intercalate (immunities.map fun (d, ag, sps) =>
    let sp := if sps.isEmpty then "" else " — " ++ "; ".intercalate (sps.map fun (c, q) => s!"[{c}] {showString q}")
    s!"- `{d}` (against: {", ".intercalate ag}){sp}")
  let md := header ++ roleLine ++ powSec ++ "\n\n" ++ dutySec ++ "\n\n" ++ immSec ++ "\n"
  let schema := Json.mkObj [
    ("kind", Json.str "advisory-prompt-bundle"),
    ("title", Json.str title),
    ("authoritative", Json.bool false),
    ("advisoryOnly", Json.bool true),
    ("role", match actorFilter? with | some r => Json.str r | none => Json.null),
    ("tools", Json.arr (powers.map fun (d, isP, _) =>
      Json.mkObj [
        ("name", Json.str d),
        ("institutionalPower", Json.bool isP),
        ("parameters", Json.arr ((spec.components d).map (Json.str ∘ toString)).toArray)
      ]).toArray),
    ("markdown", Json.str md)
  ]
  (md, schema)

end Charter.Project
