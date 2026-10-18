import Charter.Core.Semantics
import Charter.Core.Views

/-!
# Charter.Projection.Prompt — AI Constitutional System Prompts, Alignment Cards & Synthetic Training Views

Generates role-specific constitutional system prompts, deontic alignment cards
(`AlignmentCard`), and normatively grounded synthetic training datasets
(`TrainingRow`, `evaluateTrainingRow`, `generateTrainingDataset`) directly
from any `Law σ` in `Charter.Core`.

Every item in an `AlignmentCard` or `TrainingRow` is computed from the formal
AST and carries its exact English provenance span (`source.text`).
-/

namespace Charter.Projection

open Charter

variable {σ : Sig}

/-! ## 1. Deontic Alignment Card (`AlignmentCard`) -/

/-- Role-specific Deontic Alignment Card distilled from a `Law σ`.
- `institutionTitle`: human-readable name of the institution.
- `actorName`: rendered name of the actor role.
- `unalienableImmunities`: `(id, protectedAgainst, englishQuote)`.
- `institutionalPowers`: `(id, trigger, precondition, englishQuote)`.
- `hardProhibitions`: `(id, forbiddenConduct, exceptions, englishQuote)`.
- `positiveDeadlines`: `(id, requiredConduct, deadlineWindow, englishQuote)`. -/
structure AlignmentCard where
  institutionTitle      : String
  actorName             : String
  unalienableImmunities : List (String × String × String)
  institutionalPowers       : List (String × String × String × String)
  hardProhibitions      : List (String × String × String × String)
  positiveDeadlines     : List (String × String × Time × String)
  deriving Repr, DecidableEq, BEq

/-- Strip namespace prefixes from constructor names in any rendered string
(delegates to `Charter.stripNamespaces`, so institutions in any namespace render
clean short constructor names). -/
def stripCharterNs (base : String) : String :=
  stripNamespaces base

/-- Strip namespace prefixes from a value's `Repr` string. -/
def crs {α : Type} [Repr α] (a : α) : String :=
  stripCharterNs (rs a)

/-- Does actor selector `w` apply (unconditionally or via a `.tagged` role-fact pair)
to `actor`? Unlike `Who.mem w actor` (which evaluates against `ls = []` and therefore
always returns `false` for `.tagged pairs`), `whoAppliesTo` includes tagged duties,
powers, and immunities in the actor's static alignment card. -/
def whoAppliesTo (w : Who σ) (actor : σ.Actor) : Bool :=
  match w with
  | .anyone       => true
  | .only xs      => xs.contains actor
  | .except xs    => !xs.contains actor
  | .tagged pairs => pairs.any fun p => p.1 == actor

/-- Extract the exception summary string for a duty. -/
def dutyExceptionSummary [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact] (d : Duty σ) : String :=
  let powExc := if d.unlessPower.isEmpty then [] else [s!"unless valid exercise of [{String.intercalate ", " d.unlessPower}]"]
  let condExc := match d.unlessCond with | .ff => [] | c => [s!"unless ({stripCharterNs c.render})"]
  let ovrExc := if d.overriddenBy.isEmpty then [] else [s!"overridden by [{String.intercalate ", " d.overriddenBy}]"]
  let allExc := powExc ++ condExc ++ ovrExc
  let actStr := stripCharterNs d.active.render
  if allExc.isEmpty then s!"while {actStr} (no exceptions)"
  else s!"while {actStr} ({String.intercalate "; " allExc})"

/-- Compile a `Law σ` into a structured `AlignmentCard` for `actor`. -/
def compileAlignmentCard [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (title : String) (L : Law σ) (actor : σ.Actor) : AlignmentCard :=
  let imms := (L.immunities.filter fun i => whoAppliesTo i.holder actor).map fun i =>
    let againstStr := String.intercalate ", " i.against
    let actStr := stripCharterNs i.active.render
    let scopeStr := match i.unlessCond with
      | .ff => s!"{againstStr} (while {actStr})"
      | u   => s!"{againstStr} (while {actStr}, unless {stripCharterNs u.render})"
    (i.id, scopeStr, i.source.text)
  let pows := (L.powers.filter fun p => whoAppliesTo p.holder actor).map fun p =>
    (p.id, stripCharterNs p.trigger.render, stripCharterNs p.valid.render, p.source.text)
  let actorDuties := L.duties.filter fun d => whoAppliesTo d.bearer actor
  let prohs := actorDuties.filterMap fun d =>
    match d.demand with
    | .forbid c => some (d.id, stripCharterNs c.render, dutyExceptionSummary d, d.source.text)
    | .require _ _ => none
  let reqs := actorDuties.filterMap fun d =>
    match d.demand with
    | .forbid _ => none
    | .require c w => some (d.id, stripCharterNs c.render, w, d.source.text)
  { institutionTitle := title
    actorName := crs actor
    unalienableImmunities := imms
    institutionalPowers := pows
    hardProhibitions := prohs
    positiveDeadlines := reqs }

/-- Render an `AlignmentCard` as a structured Markdown Constitutional System Prompt. -/
def AlignmentCard.render (card : AlignmentCard) : String :=
  let immLines := if card.unalienableImmunities.isEmpty then
    ["- *(None declared for this role)*"]
  else
    card.unalienableImmunities.map fun (id, prot, quote) =>
      s!"- **`{id}`** — Protected against: `{prot}`\n  > *\"{quote}\"*"
  let powLines := if card.institutionalPowers.isEmpty then
    ["- *(None declared for this role)*"]
  else
    card.institutionalPowers.map fun (id, trig, pre, quote) =>
      s!"- **`{id}`** — Trigger: `{trig}` | Precondition: `{pre}`\n  > *\"{quote}\"*"
  let prohLines := if card.hardProhibitions.isEmpty then
    ["- *(None declared for this role)*"]
  else
    card.hardProhibitions.map fun (id, cond, exc, quote) =>
      s!"- **`{id}`** — Forbidden: `{cond}` | Scope & Exceptions: {exc}\n  > *\"{quote}\"*"
  let reqLines := if card.positiveDeadlines.isEmpty then
    ["- *(None declared for this role)*"]
  else
    card.positiveDeadlines.map fun (id, cond, w, quote) =>
      s!"- **`{id}`** — Required: `{cond}` within `{w}` time units of activation\n  > *\"{quote}\"*"
  s!"# Constitutional System Prompt & Deontic Alignment Card\n" ++
  s!"**Institution:** {card.institutionTitle}\n" ++
  s!"**Assigned Role:** `{card.actorName}`\n\n" ++
  s!"## 1. Unalienable Immunities (Protections Held)\n" ++
  String.intercalate "\n" immLines ++ "\n\n" ++
  s!"## 2. Powers & Preconditions (Valid Institutional Actions)\n" ++
  String.intercalate "\n" powLines ++ "\n\n" ++
  s!"## 3. Hard-Floor Prohibitions (Negative Duties)\n" ++
  String.intercalate "\n" prohLines ++ "\n\n" ++
  s!"## 4. Positive Deadlines & Requirements (Affirmative Duties)\n" ++
  String.intercalate "\n" reqLines ++ "\n"

/-- Compile and render a structured Markdown Constitutional System Prompt &
Deontic Alignment Card for `actor` under `L : Law σ`. -/
def renderSystemPrompt [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (title : String) (L : Law σ) (actor : σ.Actor) : String :=
  (compileAlignmentCard title L actor).render

/-! ## 2. Synthetic Normative Training Views (`TrainingRow`) -/

/-- A single synthetic alignment / RLHF training example derived from evaluating
an event `e : Event σ` against institutional state `ls : LegalState σ` under `L : Law σ`. -/
structure TrainingRow where
  situation           : String
  actor               : String
  act                 : String
  compliesWithDuties  : Bool
  exercisesValidPower : Bool
  triggeredPowers     : List String
  violatedDuties      : List String
  expectedRemedies    : List String
  englishCitations    : List String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Evaluate a single event `e` at state `ls` under `L` to produce a `TrainingRow`. -/
def evaluateTrainingRow [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) (e : Event σ) : TrainingRow :=
  let activeFacts := (ls.filter fun p => ls.activeAt e.t p.1).map (fun p => crs p.1) |>.eraseDups
  let exPowers := validExercises L ls e
  let brDuties := L.duties.filter (fun d => breaches L ls e d)
  let remedies := (brDuties.flatMap (fun d => d.remedies.map crs) ++
                   exPowers.flatMap (fun p => (remediesOf L p).map crs)).eraseDups
  let citations := (brDuties.map (·.source.text) ++ exPowers.map (·.source.text)).eraseDups
  { situation := s!"t={e.t}, active_facts=[{String.intercalate ", " activeFacts}]"
    actor := crs e.who
    act := crs e.act
    compliesWithDuties := L.duties.all (fun d => !breaches L ls e d)
    exercisesValidPower := !(validExercises L ls e).isEmpty
    triggeredPowers := exPowers.map (·.id)
    violatedDuties := brDuties.map (·.id)
    expectedRemedies := remedies
    englishCitations := citations }

/-- Generate a list of `TrainingRow` items by evaluating each candidate event in `events`
against state `ls` under `L`. -/
def generateTrainingDataset [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) (events : List (Event σ)) : List TrainingRow :=
  events.map (evaluateTrainingRow L ls)

/-- Generate a list of `TrainingRow` items along an execution trace `tr`, evaluating
each event `tr[i]` at its pre-state `stateBefore L tr i`. -/
def generateTraceTrainingDataset [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (tr : Trace σ) : List TrainingRow :=
  (tr.zipIdx).map fun (e, i) => evaluateTrainingRow L (stateBefore L tr i) e

/-- Kernel-computable character-level JSON string escaper. -/
def escapeJsonChars : List Char → List Char
  | [] => []
  | '"'  :: cs => '\\' :: '"'  :: escapeJsonChars cs
  | '\\' :: cs => '\\' :: '\\' :: escapeJsonChars cs
  | '\n' :: cs => '\\' :: 'n'  :: escapeJsonChars cs
  | '\r' :: cs => '\\' :: 'r'  :: escapeJsonChars cs
  | '\t' :: cs => '\\' :: 't'  :: escapeJsonChars cs
  | c    :: cs => c :: escapeJsonChars cs

/-- Escape a string for JSON output. -/
def escapeJsonString (s : String) : String :=
  String.mk (escapeJsonChars s.data)

/-- Render a list of strings as a JSON array of strings. -/
private def renderJsonStringList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map fun s => s!"\"{escapeJsonString s}\"") ++ "]"

/-- Render a single `TrainingRow` as a JSON object string. -/
def TrainingRow.toJson (r : TrainingRow) : String :=
  "  {\n" ++
  s!"    \"situation\": \"{escapeJsonString r.situation}\",\n" ++
  s!"    \"actor\": \"{escapeJsonString r.actor}\",\n" ++
  s!"    \"act\": \"{escapeJsonString r.act}\",\n" ++
  s!"    \"compliesWithDuties\": {r.compliesWithDuties},\n" ++
  s!"    \"exercisesValidPower\": {r.exercisesValidPower},\n" ++
  s!"    \"triggeredPowers\": {renderJsonStringList r.triggeredPowers},\n" ++
  s!"    \"violatedDuties\": {renderJsonStringList r.violatedDuties},\n" ++
  s!"    \"expectedRemedies\": {renderJsonStringList r.expectedRemedies},\n" ++
  s!"    \"englishCitations\": {renderJsonStringList r.englishCitations}\n" ++
  "  }"

/-- Render a list of `TrainingRow`s as a formatted JSON array. -/
def renderTrainingDatasetJson (rows : List TrainingRow) : String :=
  if rows.isEmpty then "[]"
  else "[\n" ++ String.intercalate ",\n" (rows.map TrainingRow.toJson) ++ "\n]"

/-! ## 3. Semantic Faithfulness Theorems -/

/-- **Faithfulness of `evaluateTrainingRow` to `Charter.Core.Semantics`.**
For every law `L`, state `ls`, and event `e`:
1. `(evaluateTrainingRow L ls e).compliesWithDuties` equals `L.duties.all (fun d => !breaches L ls e d)`.
2. `(evaluateTrainingRow L ls e).exercisesValidPower` equals `!(validExercises L ls e).isEmpty`. -/
theorem training_row_faithful_to_semantics [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) (e : Event σ) :
    (evaluateTrainingRow L ls e).compliesWithDuties = L.duties.all (fun d => !breaches L ls e d) ∧
    (evaluateTrainingRow L ls e).exercisesValidPower = !(validExercises L ls e).isEmpty :=
  ⟨rfl, rfl⟩

/-- Triggered powers and violated duties in `evaluateTrainingRow` match
`validExercises` and `breaches` in `Charter.Core.Semantics`. -/
theorem training_row_ids_faithful [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) (e : Event σ) :
    (evaluateTrainingRow L ls e).triggeredPowers = (validExercises L ls e).map (·.id) ∧
    (evaluateTrainingRow L ls e).violatedDuties = (L.duties.filter (fun d => breaches L ls e d)).map (·.id) :=
  ⟨rfl, rfl⟩

/-- `generateTrainingDataset` preserves the exact number of evaluated events. -/
theorem generateTrainingDataset_length [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) (events : List (Event σ)) :
    (generateTrainingDataset L ls events).length = events.length :=
  List.length_map _

/-- Evaluating an empty event list yields an empty dataset. -/
theorem generateTrainingDataset_nil [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (L : Law σ) (ls : LegalState σ) :
    generateTrainingDataset L ls [] = [] := rfl

/-! ## 4. Self-Contained Kernel-Decided Verification Suite -/

namespace PromptTest

inductive PActor | tenant | landlord | tribunal
  deriving DecidableEq, Repr

inductive PAct | evict | postDeposit | vacate
  deriving DecidableEq, Repr

inductive PFact | leased | depositPosted | vacated | slashed
  deriving DecidableEq, Repr

abbrev pSig : Sig := ⟨PActor, PAct, PFact⟩

instance : Repr pSig.Actor := inferInstanceAs (Repr PActor)
instance : Repr pSig.Act   := inferInstanceAs (Repr PAct)
instance : Repr pSig.Fact  := inferInstanceAs (Repr PFact)

private def spanD1 : Span :=
  { clause := "C.1", text := "Landlord must not unilaterally evict.", register := .norm, meaning := ["D.NO_EVICT"] }

private def spanD2 : Span :=
  { clause := "C.2", text := "Landlord must post deposit within 5 steps.", register := .norm, meaning := ["D.DEPOSIT"] }

private def spanP1 : Span :=
  { clause := "C.3", text := "Tenant may vacate at any time.", register := .norm, meaning := ["P.VACATE"] }

private def spanI1 : Span :=
  { clause := "C.4", text := "Tenant is immune from landlord eviction.", register := .norm, meaning := ["I.TENANT"] }

def sampleLaw : Law pSig :=
  { duties := [
      { id := "D.NO_EVICT", source := spanD1, bearer := .only [.landlord], beneficiary := .only [.tenant],
        active := .holds .leased, demand := .forbid (.act .evict), remedies := [.slashed] },
      { id := "D.DEPOSIT", source := spanD2, bearer := .only [.landlord], beneficiary := .only [.tenant],
        active := .holds .leased, demand := .require (.act .postDeposit) 5 }
    ]
    powers := [
      { id := "P.VACATE", source := spanP1, holder := .only [.tenant], trigger := .act .vacate,
        valid := .holds .leased, adds := [.vacated], removes := [.leased] }
    ]
    immunities := [
      { id := "I.TENANT", source := spanI1, holder := .only [.tenant], against := ["P.VACATE"],
        active := .ff }
    ]
    init := [(.leased, 0, none)] }

def emptyLaw : Law pSig :=
  { duties := [], powers := [], immunities := [], init := [] }

theorem test_alignment_card_landlord :
    let card := compileAlignmentCard "Test Institution" sampleLaw .landlord
    card.institutionTitle = "Test Institution" ∧
    card.hardProhibitions.length = 1 ∧
    card.positiveDeadlines.length = 1 ∧
    card.institutionalPowers.length = 0 ∧
    card.unalienableImmunities.length = 0 := by decide

theorem test_alignment_card_tenant :
    let card := compileAlignmentCard "Test Institution" sampleLaw .tenant
    card.hardProhibitions.length = 0 ∧
    card.positiveDeadlines.length = 0 ∧
    card.institutionalPowers.length = 1 ∧
    card.unalienableImmunities.length = 1 := by decide

theorem test_alignment_card_empty_law :
    let card := compileAlignmentCard "Empty" emptyLaw .tribunal
    card.institutionTitle = "Empty" ∧
    card.hardProhibitions = [] ∧
    card.positiveDeadlines = [] ∧
    card.institutionalPowers = [] ∧
    card.unalienableImmunities = [] ∧
    renderTrainingDatasetJson [] = "[]" := by decide

def taggedLaw : Law pSig :=
  { duties := [
      { id := "D.TAGGED_DAMAGES", source := spanD2, bearer := .tagged [(.landlord, .slashed)],
        beneficiary := .only [.tenant], active := .holds .slashed, demand := .require (.act .postDeposit) 3 }
    ]
    powers := [
      { id := "P.TAGGED_PAY", source := spanP1, holder := .tagged [(.landlord, .slashed)],
        trigger := .act .postDeposit, valid := .holds .slashed, adds := [.depositPosted] }
    ]
    immunities := [
      { id := "I.TAGGED_PROT", source := spanI1, holder := .tagged [(.tenant, .leased)],
        against := ["P.TAGGED_PAY"], active := .holds .leased }
    ]
    init := [(.leased, 0, none)] }

/-- Verify that duties, powers, and immunities using `Who.tagged` are included
for matching roles and excluded for non-matching roles in `compileAlignmentCard`. -/
theorem test_alignment_card_tagged_actor :
    let landlordCard := compileAlignmentCard "Tagged Institution" taggedLaw .landlord
    let tenantCard := compileAlignmentCard "Tagged Institution" taggedLaw .tenant
    let tribunalCard := compileAlignmentCard "Tagged Institution" taggedLaw .tribunal
    landlordCard.positiveDeadlines.length = 1 ∧
    landlordCard.institutionalPowers.length = 1 ∧
    landlordCard.unalienableImmunities.length = 0 ∧
    tenantCard.positiveDeadlines.length = 0 ∧
    tenantCard.institutionalPowers.length = 0 ∧
    tenantCard.unalienableImmunities.length = 1 ∧
    tribunalCard.positiveDeadlines.length = 0 ∧
    tribunalCard.institutionalPowers.length = 0 ∧
    tribunalCard.unalienableImmunities.length = 0 := by decide

/-- Verify `escapeJsonString` on quotes, backslashes, newlines, and tabs. -/
theorem test_escapeJsonString :
    escapeJsonString "a\"b\\c\nd\te" = "a\\\"b\\\\c\\nd\\te" := by decide

def sampleEvents : List (Event pSig) :=
  [⟨1, PActor.landlord, PAct.evict⟩, ⟨1, PActor.tenant, PAct.vacate⟩]

theorem test_training_dataset_evaluation :
    let rows := generateTrainingDataset sampleLaw sampleLaw.init sampleEvents
    rows.length = 2 ∧
    (rows[0]!).compliesWithDuties = false ∧
    (rows[0]!).exercisesValidPower = false ∧
    (rows[0]!).violatedDuties = ["D.NO_EVICT"] ∧
    (rows[0]!).englishCitations = ["Landlord must not unilaterally evict."] ∧
    (rows[1]!).compliesWithDuties = true ∧
    (rows[1]!).exercisesValidPower = true ∧
    (rows[1]!).triggeredPowers = ["P.VACATE"] := by decide

end PromptTest

end Charter.Projection

namespace Charter

export Charter.Projection (
  AlignmentCard
  stripCharterNs
  crs
  whoAppliesTo
  dutyExceptionSummary
  compileAlignmentCard
  renderSystemPrompt
  TrainingRow
  evaluateTrainingRow
  generateTrainingDataset
  generateTraceTrainingDataset
  escapeJsonString
  renderTrainingDatasetJson
  training_row_faithful_to_semantics
  training_row_ids_faithful
  generateTrainingDataset_length
  generateTrainingDataset_nil
)

end Charter
