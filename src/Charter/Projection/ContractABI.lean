import Charter.Core.Semantics
import Charter.Core.Views

/-!
# Charter.Projection.ContractABI — Smart-Contract State-Transition Guard & JSON ABI

Lowers any normative specification `L : Law σ` into a deterministic smart-contract
state-transition guard (`ContractGuardSpec σ`, `requireComplies`, `executePowerGuard`),
a standard Ethereum/EVM JSON ABI (`renderContractJsonABI`), and a Solidity `ICharterGuard`
interface and guard contract skeleton (`renderSolidityGuard`).

Proves `contract_guard_sound_and_complete`:
1. `executePowerGuard L ls e = some ls'` if and only if `requireComplies L ls e = true`
   and `ls' = step L ls e`.
2. A trace `tr` is `Authorized L tr` if and only if every step `i < tr.length` satisfies
   `requireComplies L (stateBefore L tr i) tr[i] = true`.
-/

namespace Charter.Projection

open Charter

variable {σ : Sig}

/-! ## 1. Smart-Contract Guard Semantics & Specification -/

/-- Check whether event `e` at institutional state `ls` complies with every duty in `L`.
Used as the deterministic pre-transaction guard (`requireComplies`) in smart-contract targets. -/
def requireComplies (L : Law σ) (ls : LegalState σ) (e : Event σ) : Bool :=
  L.duties.all fun d => !breaches L ls e d

/-- Deterministic guarded state transition: if `requireComplies L ls e` holds,
executes `step L ls e` and returns `some ls'`; otherwise reverts (`none`). -/
def executePowerGuard (L : Law σ) (ls : LegalState σ) (e : Event σ) : Option (LegalState σ) :=
  if requireComplies L ls e then some (step L ls e) else none

/-- Execute a multi-event transaction batch under `executePowerGuard`, reverting (`none`)
if any event in the sequence breaches a duty in force. -/
def executeTraceGuard (L : Law σ) (tr : Trace σ) : Option (LegalState σ) :=
  tr.foldlM (executePowerGuard L) L.init

/-- Lowered smart-contract guard specification for a `Law σ`. -/
structure ContractGuardSpec (σ : Sig) where
  contractName      : String
  law               : Law σ
  dutyIds           : List String
  powerIds          : List String
  immunityIds       : List String

/-- Compile a `Law σ` into a `ContractGuardSpec σ`. -/
def compileContractABI (contractName : String) (L : Law σ) : ContractGuardSpec σ :=
  { contractName := contractName
    law := L
    dutyIds := L.dutyIds
    powerIds := L.powerIds
    immunityIds := L.immunityIds }

/-! ## 2. Soundness and Completeness of the Smart-Contract Guard -/

/-- Single-step soundness and completeness of `executePowerGuard`:
`executePowerGuard L ls e` succeeds with state `ls'` iff `requireComplies L ls e = true`
and `ls' = step L ls e`. -/
theorem executePowerGuard_eq_some_iff (L : Law σ) (ls ls' : LegalState σ) (e : Event σ) :
    executePowerGuard L ls e = some ls' ↔ (requireComplies L ls e = true ∧ ls' = step L ls e) := by
  unfold executePowerGuard
  cases h : requireComplies L ls e
  · simp
  · simp [eq_comm]

/-- Step `i` of a trace `tr` (for `i < tr.length`) satisfies `complies L tr i` iff
`requireComplies L (stateBefore L tr i) tr[i]` is `true`. -/
theorem complies_eq_requireComplies_of_lt (L : Law σ) (tr : Trace σ) (i : Nat) (hi : i < tr.length) :
    complies L tr i = requireComplies L (stateBefore L tr i) tr[i] := by
  unfold complies requireComplies
  rw [List.getElem?_eq_getElem hi]

/-- Trace-level soundness and completeness of `requireComplies`:
`Authorized L tr` holds iff every step `i < tr.length` satisfies `requireComplies`. -/
theorem authorized_iff_requireComplies (L : Law σ) (tr : Trace σ) :
    Authorized L tr ↔ ∀ i (hi : i < tr.length), requireComplies L (stateBefore L tr i) tr[i] = true := by
  unfold Authorized
  constructor
  · intro h i hi
    rw [← complies_eq_requireComplies_of_lt L tr i hi]
    exact h i hi
  · intro h i hi
    rw [complies_eq_requireComplies_of_lt L tr i hi]
    exact h i hi

/-- Helper lemma: executing `foldlM (executePowerGuard L)` over `evs` from starting state `ls`
succeeds with `some ls'` iff every step complies and `ls' = evs.foldl (step L) ls`. -/
private theorem foldlM_executePowerGuard_eq_some_iff (L : Law σ) (ls ls' : LegalState σ) (evs : List (Event σ)) :
    evs.foldlM (executePowerGuard L) ls = some ls' ↔
      ((∀ i (hi : i < evs.length), requireComplies L ((evs.take i).foldl (step L) ls) evs[i] = true) ∧
       ls' = evs.foldl (step L) ls) := by
  induction evs generalizing ls with
  | nil =>
    constructor
    · intro h
      have h' : ls = ls' := Option.some.inj h
      exact ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), h'.symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  | cons e rest ih =>
    simp only [List.foldlM_cons, List.foldl_cons, List.length_cons]
    have hguard : executePowerGuard L ls e = (if requireComplies L ls e then some (step L ls e) else none) := rfl
    rw [hguard]
    cases hreq : requireComplies L ls e
    · simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Option.bind_none, reduceCtorEq, false_iff, not_and]
      intro hall
      have h0 := hall 0 (Nat.zero_lt_succ rest.length)
      simp [hreq] at h0
    · simp only [↓reduceIte, Bind.bind, Option.bind_some]
      rw [ih (step L ls e)]
      constructor
      · rintro ⟨hall, hls⟩
        refine ⟨?_, hls⟩
        intro i hi
        cases i with
        | zero => simpa using hreq
        | succ j =>
          have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
          simpa [List.take_succ_cons] using hall j hj
      · rintro ⟨hall, hls⟩
        refine ⟨?_, hls⟩
        intro j hj
        have hsucc := hall (j + 1) (Nat.succ_lt_succ hj)
        simpa [List.take_succ_cons] using hsucc

/-- Multi-step soundness and completeness of `executeTraceGuard`:
`executeTraceGuard L tr` succeeds with `some ls'` iff `Authorized L tr` holds
and `ls' = stateAfter L tr`. -/
theorem executeTraceGuard_eq_some_iff (L : Law σ) (tr : Trace σ) (ls' : LegalState σ) :
    executeTraceGuard L tr = some ls' ↔ (Authorized L tr ∧ ls' = stateAfter L tr) := by
  unfold executeTraceGuard stateAfter
  rw [foldlM_executePowerGuard_eq_some_iff, authorized_iff_requireComplies]
  rfl

/-- **Soundness and Completeness of the Smart-Contract Guard Projection.**
1. Single-step transition `executePowerGuard` succeeds with `some ls'` iff `requireComplies`
   holds and `ls' = step L ls e`.
2. Trace authorization `Authorized L tr` is equivalent to `requireComplies` holding at every
   step along `tr`. -/
theorem contract_guard_sound_and_complete (L : Law σ) :
    (∀ ls ls' e, executePowerGuard L ls e = some ls' ↔
      (requireComplies L ls e = true ∧ ls' = step L ls e)) ∧
    (∀ tr, Authorized L tr ↔
      ∀ i (hi : i < tr.length), requireComplies L (stateBefore L tr i) tr[i] = true) :=
  ⟨executePowerGuard_eq_some_iff L, authorized_iff_requireComplies L⟩

/-! ## 3. Solidity Identifier Helper & JSON ABI / Solidity Guard Renderers -/

/-- Convert a formal identifier such as `"P.SUSPEND"` or `"D.NO_TERM"` into a valid
lowercase Solidity identifier (`"p_suspend"`, `"d_no_term"`). -/
def solidityIdent (s : String) : String :=
  match s.data.map (fun c => if c.isAlphanum then c.toLower else '_') with
  | [] => "_unnamed"
  | c :: cs =>
    if c.isDigit then String.mk ('_' :: c :: cs)
    else String.mk (c :: cs)

/-- Sanitize a contract name into a valid Solidity contract identifier, preserving
letter case (`"TestGuard"` ↦ `"TestGuard"`, `"Autonomous Commons"` ↦ `"Autonomous_Commons"`). -/
def solidityContractIdent (s : String) : String :=
  match s.data.map (fun c => if c.isAlphanum then c else '_') with
  | [] => "CharterGuard"
  | c :: cs =>
    if c.isDigit then String.mk ('_' :: c :: cs)
    else String.mk (c :: cs)

/-- Strip namespace prefixes from rendered strings (`Charter.stripNamespaces`), so
institutions in any namespace render clean short constructor names. -/
private def abiStripNs (base : String) : String :=
  stripNamespaces base

/-- Kernel-computable character-level JSON escaper. -/
private def abiEscapeJsonChars : List Char → List Char
  | [] => []
  | '"'  :: cs => '\\' :: '"'  :: abiEscapeJsonChars cs
  | '\\' :: cs => '\\' :: '\\' :: abiEscapeJsonChars cs
  | '\n' :: cs => '\\' :: 'n'  :: abiEscapeJsonChars cs
  | '\r' :: cs => '\\' :: 'r'  :: abiEscapeJsonChars cs
  | '\t' :: cs => '\\' :: 't'  :: abiEscapeJsonChars cs
  | c    :: cs => c :: abiEscapeJsonChars cs

/-- Escape a string for JSON embedding. -/
private def abiEscapeJson (s : String) : String :=
  String.mk (abiEscapeJsonChars s.data)

/-- Render the JSON ABI specification for a `Law σ`, including `requireComplies`,
`executePower`, per-duty compliance view functions, per-power validity view functions,
and per-immunity status queries. -/
def renderContractJsonABI [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (name : String) (L : Law σ) : String :=
  let coreEntries : List String := [
    "    {\n" ++
    "      \"type\": \"function\",\n" ++
    "      \"name\": \"requireComplies\",\n" ++
    "      \"stateMutability\": \"view\",\n" ++
    "      \"inputs\": [\n" ++
    "        {\"name\": \"timestamp\", \"type\": \"uint256\"},\n" ++
    "        {\"name\": \"actor\", \"type\": \"uint8\"},\n" ++
    "        {\"name\": \"act\", \"type\": \"uint8\"}\n" ++
    "      ],\n" ++
    "      \"outputs\": [{\"name\": \"complies\", \"type\": \"bool\"}]\n" ++
    "    }",
    "    {\n" ++
    "      \"type\": \"function\",\n" ++
    "      \"name\": \"executePower\",\n" ++
    "      \"stateMutability\": \"nonpayable\",\n" ++
    "      \"inputs\": [\n" ++
    "        {\"name\": \"timestamp\", \"type\": \"uint256\"},\n" ++
    "        {\"name\": \"actor\", \"type\": \"uint8\"},\n" ++
    "        {\"name\": \"act\", \"type\": \"uint8\"}\n" ++
    "      ],\n" ++
    "      \"outputs\": [{\"name\": \"exercisedCount\", \"type\": \"uint256\"}]\n" ++
    "    }"
  ]
  let dutyEntries := L.duties.map fun d =>
    "    {\n" ++
    "      \"type\": \"function\",\n" ++
    s!"      \"name\": \"checkDuty_{solidityIdent d.id}\",\n" ++
    s!"      \"notice\": \"{abiEscapeJson d.id} [{abiEscapeJson d.source.clause}]: {abiEscapeJson (abiStripNs d.demand.render)}\",\n" ++
    "      \"stateMutability\": \"view\",\n" ++
    "      \"inputs\": [\n" ++
    "        {\"name\": \"timestamp\", \"type\": \"uint256\"},\n" ++
    "        {\"name\": \"actor\", \"type\": \"uint8\"},\n" ++
    "        {\"name\": \"act\", \"type\": \"uint8\"}\n" ++
    "      ],\n" ++
    "      \"outputs\": [{\"name\": \"ok\", \"type\": \"bool\"}]\n" ++
    "    }"
  let powerEntries := L.powers.map fun p =>
    "    {\n" ++
    "      \"type\": \"function\",\n" ++
    s!"      \"name\": \"canExercise_{solidityIdent p.id}\",\n" ++
    s!"      \"notice\": \"{abiEscapeJson p.id} [{abiEscapeJson p.source.clause}]: trigger {abiEscapeJson (abiStripNs p.trigger.render)}, valid {abiEscapeJson (abiStripNs p.valid.render)}\",\n" ++
    "      \"stateMutability\": \"view\",\n" ++
    "      \"inputs\": [\n" ++
    "        {\"name\": \"timestamp\", \"type\": \"uint256\"},\n" ++
    "        {\"name\": \"actor\", \"type\": \"uint8\"},\n" ++
    "        {\"name\": \"act\", \"type\": \"uint8\"}\n" ++
    "      ],\n" ++
    "      \"outputs\": [{\"name\": \"valid\", \"type\": \"bool\"}]\n" ++
    "    }"
  let immEntries := L.immunities.map fun i =>
    "    {\n" ++
    "      \"type\": \"function\",\n" ++
    s!"      \"name\": \"immunityActive_{solidityIdent i.id}\",\n" ++
    s!"      \"notice\": \"{abiEscapeJson i.id} [{abiEscapeJson i.source.clause}]: protects {abiEscapeJson (abiStripNs i.holder.render)} against {abiEscapeJson (toString i.against)}\",\n" ++
    "      \"stateMutability\": \"view\",\n" ++
    "      \"inputs\": [{\"name\": \"timestamp\", \"type\": \"uint256\"}],\n" ++
    "      \"outputs\": [{\"name\": \"active\", \"type\": \"bool\"}]\n" ++
    "    }"
  let allEntries := coreEntries ++ dutyEntries ++ powerEntries ++ immEntries
  "{\n" ++
  s!"  \"contractName\": \"{abiEscapeJson name}\",\n" ++
  s!"  \"dutyCount\": {L.duties.length},\n" ++
  s!"  \"powerCount\": {L.powers.length},\n" ++
  s!"  \"immunityCount\": {L.immunities.length},\n" ++
  "  \"abi\": [\n" ++
  String.intercalate ",\n" allEntries ++ "\n" ++
  "  ]\n" ++
  "}"

/-- Alias for `renderContractJsonABI`. -/
abbrev renderJsonABI [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (name : String) (L : Law σ) : String :=
  renderContractJsonABI name L

/-- Render a Solidity `ICharterGuard` interface and state-transition guard skeleton
enumerating all `Duty` checks (`requireComplies`), `Power` transitions (`executePower`),
and `Immunity` overrides for `L : Law σ`. -/
def renderSolidityGuard [Repr σ.Actor] [Repr σ.Act] [Repr σ.Fact]
    (contractName : String) (L : Law σ) : String :=
  let safeContractIdent := solidityContractIdent contractName
  let dutyFns := L.duties.map fun d =>
    let excPow := if d.unlessPower.isEmpty then "none" else String.intercalate ", " d.unlessPower
    s!"    /// @notice [{d.source.clause}] {d.id}: {abiStripNs d.bearer.render} -> {abiStripNs d.beneficiary.render} | {abiStripNs d.demand.render} (unless power: {excPow})\n" ++
    s!"    /// @dev Source: \"{abiEscapeJson d.source.text}\"\n" ++
    s!"    function checkDuty_{solidityIdent d.id}(uint256 timestamp, uint8 actor, uint8 act) public view returns (bool) \{\n" ++
    s!"        return !breachesDuty(\"{d.id}\", timestamp, actor, act);\n" ++
    s!"    }"
  let dutyBoolChecks := L.duties.map fun d =>
    s!"        if (!checkDuty_{solidityIdent d.id}(timestamp, actor, act)) return false;"
  let dutyReverts := L.duties.map fun d =>
    s!"        if (!checkDuty_{solidityIdent d.id}(timestamp, actor, act)) revert DutyBreached(\"{d.id}\");"
  let immFns := L.immunities.map fun i =>
    let ag := String.intercalate ", " i.against
    s!"    /// @notice [{i.source.clause}] {i.id}: holder {abiStripNs i.holder.render} protected against [{ag}] while {abiStripNs i.active.render}\n" ++
    s!"    /// @dev Source: \"{abiEscapeJson i.source.text}\"\n" ++
    s!"    function immunityActive_{solidityIdent i.id}(uint256 timestamp) public view returns (bool) \{\n" ++
    s!"        return evalImmunity(\"{i.id}\", timestamp);\n" ++
    s!"    }"
  let powerFns := L.powers.map fun p =>
    let addsList := abiStripNs (rs (p.adds ++ p.addsFor.map (·.1) ++ remediesOf L p))
    let remsList := abiStripNs (rs p.removes)
    let defeatingImms := (L.immunities.filter fun i => i.against.contains p.id).map (·.id)
    let immChecks := defeatingImms.map fun iid => s!"!immunityActive_{solidityIdent iid}(timestamp)"
    let immExpr := if immChecks.isEmpty then "true" else String.intercalate " && " immChecks
    s!"    /// @notice [{p.source.clause}] {p.id}: holder {abiStripNs p.holder.render}, trigger {abiStripNs p.trigger.render}, valid {abiStripNs p.valid.render}\n" ++
    s!"    /// @dev Effects: +{addsList} -{remsList} | Source: \"{abiEscapeJson p.source.text}\"\n" ++
    s!"    function canExercise_{solidityIdent p.id}(uint256 timestamp, uint8 actor, uint8 act) public view returns (bool) \{\n" ++
    s!"        return evalPowerGuard(\"{p.id}\", timestamp, actor, act) && ({immExpr});\n" ++
    s!"    }"
  let powerExecs := L.powers.map fun p =>
    s!"        if (canExercise_{solidityIdent p.id}(timestamp, actor, act)) \{\n" ++
    s!"            applyPowerEffects(\"{p.id}\", timestamp, actor);\n" ++
    s!"            emit PowerExercised(\"{p.id}\", timestamp, actor, act);\n" ++
    s!"            exercisedCount += 1;\n" ++
    s!"        }"
  "// SPDX-License-Identifier: MIT\n" ++
  "pragma solidity ^0.8.20;\n\n" ++
  "/// @title ICharterGuard — Universal Normative State-Transition Guard Interface\n" ++
  "/// @notice Generated by Charter.Projection.ContractABI (soundness: contract_guard_sound_and_complete)\n" ++
  "interface ICharterGuard {\n" ++
  "    error DutyBreached(string dutyId);\n" ++
  "    event PowerExercised(string indexed powerId, uint256 timestamp, uint8 actor, uint8 act);\n\n" ++
  "    function requireComplies(uint256 timestamp, uint8 actor, uint8 act) external view returns (bool);\n" ++
  "    function executePower(uint256 timestamp, uint8 actor, uint8 act) external returns (uint256 exercisedCount);\n" ++
  "}\n\n" ++
  s!"/// @title {safeContractIdent} — Verified Institutional State-Transition Guard\n" ++
  s!"abstract contract {safeContractIdent} is ICharterGuard \{\n" ++
  "    function breachesDuty(string memory dutyId, uint256 timestamp, uint8 actor, uint8 act) internal view virtual returns (bool);\n" ++
  "    function evalPowerGuard(string memory powerId, uint256 timestamp, uint8 actor, uint8 act) internal view virtual returns (bool);\n" ++
  "    function evalImmunity(string memory immunityId, uint256 timestamp) internal view virtual returns (bool);\n" ++
  "    function applyPowerEffects(string memory powerId, uint256 timestamp, uint8 actor) internal virtual;\n\n" ++
  "    // ------------------------------------------------------------------------\n" ++
  "    // 1. Immunity Overrides\n" ++
  "    // ------------------------------------------------------------------------\n\n" ++
  (if immFns.isEmpty then "    // (No immunities declared)\n\n" else String.intercalate "\n\n" immFns ++ "\n\n") ++
  "    // ------------------------------------------------------------------------\n" ++
  "    // 2. Duty Compliance Checks\n" ++
  "    // ------------------------------------------------------------------------\n\n" ++
  (if dutyFns.isEmpty then "    // (No duties declared)\n\n" else String.intercalate "\n\n" dutyFns ++ "\n\n") ++
  "    // ------------------------------------------------------------------------\n" ++
  "    // 3. Institutional Power Guards\n" ++
  "    // ------------------------------------------------------------------------\n\n" ++
  (if powerFns.isEmpty then "    // (No powers declared)\n\n" else String.intercalate "\n\n" powerFns ++ "\n\n") ++
  "    // ------------------------------------------------------------------------\n" ++
  "    // 4. Deterministic State-Transition Guard Entrypoints\n" ++
  "    // ------------------------------------------------------------------------\n\n" ++
  "    function requireComplies(uint256 timestamp, uint8 actor, uint8 act) public view override returns (bool) {\n" ++
  (if dutyBoolChecks.isEmpty then "" else String.intercalate "\n" dutyBoolChecks ++ "\n") ++
  "        return true;\n" ++
  "    }\n\n" ++
  "    function executePower(uint256 timestamp, uint8 actor, uint8 act) external override returns (uint256 exercisedCount) {\n" ++
  (if dutyReverts.isEmpty then "" else String.intercalate "\n" dutyReverts ++ "\n") ++
  (if powerExecs.isEmpty then "" else String.intercalate "\n" powerExecs ++ "\n") ++
  "    }\n" ++
  "}\n"

/-! ## 4. Self-Contained Kernel-Decided Verification Suite -/

namespace ContractABITest

inductive CActor | tenant | landlord | tribunal
  deriving DecidableEq, Repr

inductive CAct | evict | suspend | vacate
  deriving DecidableEq, Repr

inductive CFact | leased | suspended | vacated | objected
  deriving DecidableEq, Repr

abbrev cSig : Sig := ⟨CActor, CAct, CFact⟩

instance : Repr cSig.Actor := inferInstanceAs (Repr CActor)
instance : Repr cSig.Act   := inferInstanceAs (Repr CAct)
instance : Repr cSig.Fact  := inferInstanceAs (Repr CFact)

private def testSpan : Span :=
  { clause := "ABI.1", text := "No party may evict a leased tenant except by P.VACATE or P.TRIBUNAL_EVICT.", register := .norm, meaning := ["D.NO_EVICT", "P.VACATE", "P.TRIBUNAL_EVICT", "I.OBJ"] }

def testLaw : Law cSig :=
  { duties := [
      { id := "D.NO_EVICT", source := testSpan, bearer := .anyone, beneficiary := .only [.tenant],
        active := .holds .leased, demand := .forbid (.act .evict), unlessPower := ["P.VACATE", "P.TRIBUNAL_EVICT"] }
    ]
    powers := [
      { id := "P.VACATE", source := testSpan, holder := .only [.tenant], trigger := .act .evict,
        valid := .holds .leased, adds := [.vacated], removes := [.leased] },
      { id := "P.TRIBUNAL_EVICT", source := testSpan, holder := .only [.tribunal], trigger := .act .evict,
        valid := .holds .leased, adds := [.vacated], removes := [.leased] }
    ]
    immunities := [
      { id := "I.OBJ", source := testSpan, holder := .only [.tenant], against := ["P.TRIBUNAL_EVICT"],
        active := .holds .objected }
    ]
    init := [(.leased, 0, none)] }

/-- Unlawful landlord eviction causes `executePowerGuard` to return `none` (revert). -/
theorem test_guard_reverts_on_breach :
    requireComplies testLaw testLaw.init ⟨1, .landlord, .evict⟩ = false ∧
    executePowerGuard testLaw testLaw.init ⟨1, .landlord, .evict⟩ = none := by decide

/-- Lawful tenant revocation passes `requireComplies` and transitions state via `executePowerGuard`. -/
theorem test_guard_executes_valid_power :
    requireComplies testLaw testLaw.init ⟨1, .tenant, .evict⟩ = true ∧
    executePowerGuard testLaw testLaw.init ⟨1, .tenant, .evict⟩ =
      some [(.vacated, 1, none)] := by decide

/-- When immunity `I.OBJ` is active, `P.TRIBUNAL_EVICT` is defeated, so tribunal eviction
breaches `D.NO_EVICT` and `executePowerGuard` reverts (`none`). -/
theorem test_guard_reverts_when_immunity_defeats_excepting_power :
    let lsObj : LegalState cSig := [(.leased, 0, none), (.objected, 0, none)]
    requireComplies testLaw lsObj ⟨1, .tribunal, .evict⟩ = false ∧
    executePowerGuard testLaw lsObj ⟨1, .tribunal, .evict⟩ = none := by decide

/-- Multi-step batch execution succeeds on empty/authorized traces and reverts on breaching traces. -/
theorem test_batch_trace_guard :
    executeTraceGuard testLaw [] = some testLaw.init ∧
    executeTraceGuard testLaw [⟨1, .tenant, .evict⟩] = some [(.vacated, 1, none)] ∧
    executeTraceGuard testLaw [⟨1, .landlord, .evict⟩] = none := by decide

/-- `compileContractABI` records the exact duty, power, and immunity IDs, and
`solidityIdent` / `solidityContractIdent` sanitize identifiers cleanly. -/
theorem test_compileContractABI_structure :
    let spec := compileContractABI "TestGuard" testLaw
    spec.contractName = "TestGuard" ∧
    spec.dutyIds = ["D.NO_EVICT"] ∧
    spec.powerIds = ["P.VACATE", "P.TRIBUNAL_EVICT"] ∧
    spec.immunityIds = ["I.OBJ"] ∧
    solidityIdent "P.TRIBUNAL_EVICT" = "p_tribunal_evict" ∧
    solidityContractIdent "Autonomous Commons" = "Autonomous_Commons" ∧
    solidityContractIdent "" = "CharterGuard" ∧
    solidityContractIdent "1Guard" = "_1Guard" := by decide

end ContractABITest

end Charter.Projection

namespace Charter

export Charter.Projection (
  requireComplies
  executePowerGuard
  executeTraceGuard
  ContractGuardSpec
  compileContractABI
  executePowerGuard_eq_some_iff
  complies_eq_requireComplies_of_lt
  authorized_iff_requireComplies
  executeTraceGuard_eq_some_iff
  contract_guard_sound_and_complete
  solidityIdent
  solidityContractIdent
  renderContractJsonABI
  renderJsonABI
  renderSolidityGuard
)

end Charter
