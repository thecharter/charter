import Lean.Data.Json

/-!
# Charter.Artifact.Cert — Structured Assurance Certificates (`G1.6`, `D19`, `Law 10`)

Pairs the four canonical `Law 10` assurance tags (`proved`, `decided`, `checked`, `assumed`)
with orthogonal `ClaimScope` and `CompletionStatus` metadata (`docs/assurance-levels.md`,
`docs/rfc.md` §7.1).
-/

namespace Charter.Artifact

open Lean (Json)

/-- Strictly the four `Mission Law 10` assurance tags — never a fifth. -/
inductive AssuranceTag
  | proved
  | decided
  | checked
  | assumed
  deriving Repr, DecidableEq, Inhabited

def AssuranceTag.asString : AssuranceTag → String
  | .proved  => "proved"
  | .decided => "decided"
  | .checked => "checked"
  | .assumed => "assumed"

/-- Orthogonal domain/model scope of a verification claim (`docs/assurance-levels.md` §2.1). -/
inductive ClaimScope
  | liveEvaluator
  | idealizedCoreModel
  | concreteTrace
  | boundedExhaustive (depth : Nat)
  deriving Repr, DecidableEq, Inhabited

def ClaimScope.toJson : ClaimScope → Json
  | .liveEvaluator => Json.mkObj [("kind", Json.str "live-evaluator")]
  | .idealizedCoreModel => Json.mkObj [("kind", Json.str "idealized-core-model")]
  | .concreteTrace => Json.mkObj [("kind", Json.str "concrete-trace")]
  | .boundedExhaustive d => Json.mkObj [("kind", Json.str "bounded-exhaustive"), ("depth", Json.num d)]

/-- Whether checking completed or stopped on a resource/coverage limit (`T44`). -/
inductive CompletionStatus
  | complete
  | inconclusive
  | timeout
  | oom
  deriving Repr, DecidableEq, Inhabited

def CompletionStatus.asString : CompletionStatus → String
  | .complete     => "complete"
  | .inconclusive => "inconclusive"
  | .timeout      => "timeout"
  | .oom          => "oom"

/-- Machine-readable assurance certificate for a single claim or invariant obligation. -/
structure ClaimCertificate where
  claim       : String
  about       : String
  /-- `some true`, `some false`, or `none` when `completion != .complete`. -/
  verdict     : Option Bool
  assurance   : AssuranceTag
  scope       : ClaimScope
  completion  : CompletionStatus
  lawSha256   : Option String := none
  assumptions : List String := []
  file        : String := ""
  line        : Nat := 0
  theoremName : String := ""
  note        : String := ""
  deriving Repr

def ClaimCertificate.toJson (c : ClaimCertificate) : Json :=
  let verdictStr := match c.verdict with
    | some true => "holds"
    | some false => "falsified"
    | none => "inconclusive"
  let base : List (String × Json) := [
    ("kind", Json.str "claim"),
    ("claim", Json.str c.claim),
    ("about", Json.str c.about),
    ("tag", Json.str c.assurance.asString),
    ("assurance", Json.str c.assurance.asString),
    ("verdict", Json.str verdictStr),
    ("result", match c.verdict with | some b => Json.bool b | none => Json.null),
    ("scope", c.scope.toJson),
    ("completion", Json.str c.completion.asString),
    ("assumptions", Json.arr (c.assumptions.map Json.str).toArray)
  ]
  let loc := (if c.file.isEmpty then [] else [("file", Json.str c.file), ("line", Json.num c.line)]) ++
             (if c.theoremName.isEmpty then [] else [("theorem", Json.str c.theoremName)]) ++
             (match c.lawSha256 with | some h => [("lawSha256", Json.str h)] | none => []) ++
             (if c.note.isEmpty then [] else [("note", Json.str c.note)])
  Json.mkObj (base ++ loc)

end Charter.Artifact
