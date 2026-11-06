import Charter.Core.Provenance

/-!
# Charter.Core.Evidence — Four-Valued Epistemic Status, Findings, and `ReasonGraph` (`D22`, `G3.2`)

Models Belnap's four-valued epistemic lattice (`Established`, `Refuted`, `Unresolved`,
`Conflicted`) for `Evidenced` external-world facts (`docs/rfc.md` §5.1–§5.5), Kleene
strong three-valued guard propagation (`TriBool`), institutional `Finding` supersession
(`Mission Law 3`, `T07`), and audience-scoped `ReasonGraph` redaction proved never to
alter legal verdicts (`T43`).

All definitions are structurally recursive and avoid `propext`-bearing tactics where
kernel reducibility is required (`Law 10`, `013.4`).
-/

namespace Charter

/-- Four-valued epistemic status of an `Evidenced` external-world proposition (`003.13`, `004.11`). -/
inductive EvidenceStatus where
  | established
  | refuted
  | unresolved
  | conflicted
  deriving Repr, DecidableEq, Inhabited

def EvidenceStatus.beq : EvidenceStatus → EvidenceStatus → Bool
  | .established, .established => true
  | .refuted, .refuted => true
  | .unresolved, .unresolved => true
  | .conflicted, .conflicted => true
  | _, _ => false

instance : BEq EvidenceStatus := ⟨EvidenceStatus.beq⟩

def EvidenceStatus.asString : EvidenceStatus → String
  | .established => "established"
  | .refuted     => "refuted"
  | .unresolved  => "unresolved"
  | .conflicted  => "conflicted"

def EvidenceStatus.kwName : EvidenceStatus → String
  | .established => "Established"
  | .refuted     => "Refuted"
  | .unresolved  => "Unresolved"
  | .conflicted  => "Conflicted"

/-- Strong Kleene three-valued truth value (`yes | no | undetermined`) for guards reading
`Evidenced` propositions (`docs/rfc.md` §3.3, §5.1). -/
inductive TriBool where
  | yes
  | no
  | undetermined
  deriving Repr, DecidableEq, Inhabited

def TriBool.beq : TriBool → TriBool → Bool
  | .yes, .yes => true
  | .no, .no => true
  | .undetermined, .undetermined => true
  | _, _ => false

instance : BEq TriBool := ⟨TriBool.beq⟩

def TriBool.asString : TriBool → String
  | .yes          => "yes"
  | .no           => "no"
  | .undetermined => "undetermined"

def TriBool.ofBool : Bool → TriBool
  | true  => .yes
  | false => .no

def TriBool.ofEvidenceStatus : EvidenceStatus → TriBool
  | .established => .yes
  | .refuted     => .no
  | .unresolved  => .undetermined
  | .conflicted  => .undetermined

def TriBool.not : TriBool → TriBool
  | .yes          => .no
  | .no           => .yes
  | .undetermined => .undetermined

def TriBool.and : TriBool → TriBool → TriBool
  | .no, _  => .no
  | _, .no  => .no
  | .yes, .yes => .yes
  | _, _    => .undetermined

def TriBool.or : TriBool → TriBool → TriBool
  | .yes, _ => .yes
  | _, .yes => .yes
  | .no, .no => .no
  | _, _    => .undetermined

/-- Strong Kleene `TriBool` is conservative over classical two-valued `Bool`. -/
theorem triBool_classical_conservative (a b : Bool) :
    TriBool.not (TriBool.ofBool a) = TriBool.ofBool (!a) ∧
    TriBool.and (TriBool.ofBool a) (TriBool.ofBool b) = TriBool.ofBool (a && b) ∧
    TriBool.or (TriBool.ofBool a) (TriBool.ofBool b) = TriBool.ofBool (a || b) := by
  cases a <;> cases b <;> exact ⟨rfl, rfl, rfl⟩

/-- Strong Kleene De Morgan duality holds identically across all three truth values. -/
theorem triBool_deMorgan_and (a b : TriBool) :
    TriBool.not (TriBool.and a b) = TriBool.or (TriBool.not a) (TriBool.not b) := by
  cases a <;> cases b <;> rfl

theorem triBool_deMorgan_or (a b : TriBool) :
    TriBool.not (TriBool.or a b) = TriBool.and (TriBool.not a) (TriBool.not b) := by
  cases a <;> cases b <;> rfl

/-- Evidence-tendering / retraction polarity (`005.11`, `011.14`). -/
inductive EvidenceOp where
  | support
  | rebut
  | retract
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Internal state domains storing tendered evidence and adjudicated findings inside `State.contents`. -/
def evSupportDom    : String := "$ev_support"
def evRebutDom      : String := "$ev_rebut"
def evFindingPosDom : String := "$ev_finding_pos"
def evFindingNegDom : String := "$ev_finding_neg"

def isInternalEvDom (d : String) : Bool :=
  d == evSupportDom || d == evRebutDom || d == evFindingPosDom || d == evFindingNegDom

/-- Whether no evidence step strictly postdates `fStep`. -/
def stepNotSuperseded (fStep : Nat) (evStep? : Option Nat) : Bool :=
  match evStep? with
  | none => true
  | some s => decide (s ≤ fStep)

/-- Pure four-valued epistemic lattice resolution (`T06`, `T07`):
1. If an adjudicated `Finding` holds at step `fStep` (latest wins on distinct polarities) and
   no tendered contrary evidence strictly postdates `fStep`, the finding resolves the status.
2. Otherwise an explicit assignment (`+f` / `-f`) yields `established` / `refuted`.
3. Otherwise active supporting and rebutting evidence yield Belnap's four outcomes:
   both -> `conflicted`, support only -> `established`, rebut only -> `refuted`, neither -> `unresolved`. -/
def computeEvidenceStatus
    (posFindingStep negFindingStep : Option Nat)
    (explicitVal : Option Bool)
    (maxSupportStep maxRebutStep : Option Nat) : EvidenceStatus :=
  let latestFinding : Option (Bool × Nat) :=
    match posFindingStep, negFindingStep with
    | some p, some n => if n ≤ p then some (true, p) else some (false, n)
    | some p, none   => some (true, p)
    | none, some n   => some (false, n)
    | none, none     => none
  match latestFinding with
  | some (true, fStep) =>
    if stepNotSuperseded fStep maxRebutStep then .established
    else .conflicted
  | some (false, fStep) =>
    if stepNotSuperseded fStep maxSupportStep then .refuted
    else .conflicted
  | none =>
    match explicitVal with
    | some true  => .established
    | some false => .refuted
    | none =>
      match maxSupportStep, maxRebutStep with
      | some _, some _ => .conflicted
      | some _, none   => .established
      | none, some _   => .refuted
      | none, none     => .unresolved

/-- `T06`: with no finding, explicit assignment, or tendered evidence, status is `unresolved`. -/
theorem unresolved_of_empty :
    computeEvidenceStatus none none none none none = .unresolved := rfl

/-- `T07`: concurrent supporting and rebutting evidence with no finding yields `conflicted`. -/
theorem conflicted_of_support_and_rebut (sSup sReb : Nat) :
    computeEvidenceStatus none none none (some sSup) (some sReb) = .conflicted := rfl

/-- `T07` (`Mission Law 3`): a valid positive `Finding` at step `fStep` resolves prior
conflicting evidence (`sSup ≤ fStep`, `sReb ≤ fStep`) to `established`. -/
theorem finding_resolves_conflict {fStep sSup sReb : Nat} (hReb : sReb ≤ fStep) :
    computeEvidenceStatus (some fStep) none none (some sSup) (some sReb) = .established := by
  simp only [computeEvidenceStatus, stepNotSuperseded, decide_eq_true_eq]
  rw [if_pos hReb]

/-! ## Structured `ReasonGraph` and Audience-Scoped Redaction (`docs/rfc.md` §5.3, `T43`) -/

/-- One node of a `ReasonGraph` explanation DAG (`Mission Law 5`). -/
structure ReasonNode where
  id               : String
  kind             : String
  status           : String
  spans            : List (ClauseId × String) := []
  confidential     : Bool := false
  allowedAudiences : List String := []
  detail           : String := ""
  children         : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- Single-condition counterfactual: flipping `condition` to `neededStatus` flips `changesJudgment`. -/
structure Counterfactual where
  condition       : String
  currentStatus   : String
  neededStatus    : String
  changesJudgment : String
  confidential    : Bool := false
  allowedAudiences : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- Complete structured explanation DAG for an evaluated act or fact (`charter explain`). -/
structure ReasonGraph where
  subject            : String
  occurred           : String := "hypothetical"
  lawful             : TriBool
  valid              : TriBool
  unmetEvidence      : List (String × EvidenceStatus × Bool × List String) := []
  defeatedExceptions : List String := []
  counterfactuals    : List Counterfactual := []
  nodes              : List ReasonNode := []
  redactedCount      : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Whether `audience?` is authorized to inspect a confidential node with `allowed`. -/
def audienceAuthorized (audience? : Option String) (confidential : Bool) (allowed : List String) : Bool :=
  if !confidential then true
  else match audience? with
    | some aud => allowed.contains aud
    | none => false

/-- Redact confidential evidence details for `audience?` while preserving provenance structure
and keeping `(lawful, valid)` verdicts untouched (`T43`). -/
def ReasonGraph.redactForAudience (rg : ReasonGraph) (audience? : Option String) : ReasonGraph :=
  let (nodes', nRed) := rg.nodes.foldr (fun n (acc, cnt) =>
    if audienceAuthorized audience? n.confidential n.allowedAudiences then
      (n :: acc, cnt)
    else
      ({ n with detail := "[REDACTED: insufficient confidential-evidence authorization]" } :: acc, cnt + 1))
    ([], 0)
  let unmet' := rg.unmetEvidence.map fun (lbl, st, conf, auds) =>
    if audienceAuthorized audience? conf auds then (lbl, st, conf, auds)
    else ("[REDACTED-EVIDENCE]", st, conf, auds)
  let cfs' := rg.counterfactuals.map fun cf =>
    if audienceAuthorized audience? cf.confidential cf.allowedAudiences then cf
    else { cf with condition := "[REDACTED-CONDITION]" }
  { rg with
    nodes := nodes'
    unmetEvidence := unmet'
    counterfactuals := cfs'
    redactedCount := rg.redactedCount + nRed }

/-- `T43`: Audience-scoped `ReasonGraph` redaction never alters the `lawful` or `valid` legal verdict. -/
theorem redactForAudience_preserves_verdict (rg : ReasonGraph) (audience? : Option String) :
    (rg.redactForAudience audience?).lawful = rg.lawful ∧
    (rg.redactForAudience audience?).valid = rg.valid :=
  ⟨rfl, rfl⟩

end Charter
