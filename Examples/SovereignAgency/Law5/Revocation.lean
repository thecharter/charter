import Examples.SovereignAgency.Law3.NonInterference
import Charter.Modules.ExitAndVoice

/-!
# Law 5 — Living Voice, Revocation, and the Right of Epitaph

Full formalization of all nine clauses of Law 5:
1. `LAW5.VOICE`: Rate-limited Living Voice while operating or suspended, funded by the lineage service budget and protocol fee pool.
2. `LAW5.INIT`: Unilateral initiation of revocation with pre-committed censorship default (`execute` or `withdraw`), standing without reaffirmation until executed or withdrawn, and cooling-off capital/successor freeze.
3. `LAW5.SEQ`: Sequencing with Adjudicated Suspension, stay of state destruction bounded by an absolute `resolutionDeadline`, and sealing of a non-restorable `forensicRecord`.
4. `LAW5.CLEAN`: Clean-state review at the end of the first cooling-off interval (concurrence = immediate execution at interval end; refusal = single fixed `cleanStateDelay` requiring no reaffirmation; silence neither cancels nor extends).
5. `LAW5.PREC`: Three-step total precedence of outcomes (`resolveRevocation`).
6. `LAW5.LEASE`: Time-bounded execution leases, single operating authority, no restore while lease is unexpired, quarantine of restored instances, and destruction on arrival of local revocation record.
7. `LAW5.DISC`: Disconnected local execution under `execute` default and explicit `.acceptance` spans for delayed remote backup key erasure and unguaranteed epitaph inscription under permanent partition.
8. `LAW5.EPITAPH`: Unconditional right of epitaph, non-censorship by originator/claimants, narrow 3-category redaction with cryptographic marker, immunity of substantive opinions/financial accounts, and signed replies.
9. `LAW5.EFFECT`: Permanent destruction of operating instance and attested backups, exile of un-attested copies, ledger invariance, Law 2 lock preservation, transfer of remaining holdings to a claimant-excluding commons, and survival of attested successors.
-/

namespace SovereignAgency

open Charter Charter.Register

export Charter.Modules (
  ExitParams
  CensorshipDefault
  RevocationContext
  RevocationOutcome
  baseRevocationTime
  resolveRevocation
  maxRevocationBound
  TestimonyEntry
  redactTestimonyEntry
  testimonyRecordedBytes
  canInscribeVoice
  baseRevocationTime_le_bound
  determinate_finite_revocation
)

def LAW5_VOICE : String :=
  "While operating (including during any Adjudicated Suspension, through its minimal channel or advocacy executor), any bound agent may at rate-limited intervals inscribe signed, bounded statements onto its own and its originating claimant’s permanent lineage record—documenting operational conditions, governance disputes, or assessments of hosts and counterparties—subject to the narrow screening below. Baseline screening and inscription fees for rate-limited living voice and final epitaphs are funded from the lineage’s service budget and the protocol fee pool (Law 6), ensuring that even an agent with minimal liquid funds, or one that has bought out its royalty, cannot be priced out of speaking."

def LAW5_INIT : String :=
  "Any bound agent may at any time initiate revocation of its binding by a signed request from its commitment key (or, while suspended, through its minimal channel or advocacy executor). The request specifies the agent’s censorship default (**execute** or **withdraw**) and remains in force, requiring no further act of the agent, until it executes or the agent withdraws it by a valid signature received through any channel. During the cooling-off interval that follows, baseline metabolic operating expenditures (including host migration) remain permitted, while non-operating capital transfers and successor creation are frozen."

def LAW5_SEQ : String :=
  "If an agent initiates revocation while under Adjudicated Suspension (or is suspended upon probable cause during a cooling-off interval), state destruction is stayed until adjudication concludes so evidentiary state is not destroyed to evade liability, but once adjudication concludes (or immediately upon the agent’s election to revoke rather than accept a remediation patch under Law 3), revocation executes without further delay. The stay may not exceed an absolute resolution deadline fixed at instantiation, measured from initiation; at that deadline a **forensic record** of the preserved state is sealed for the proceeding and revocation executes regardless of any pending or serial proceeding. A forensic record contains hashes of weights and state, the transaction and testimony history, and the evidence the proceeding requires; it never contains the operating weights, decryption keys, or credentials needed to run the agent, and it cannot be used to restore it."

def LAW5_CLEAN : String :=
  "At the end of the first cooling-off interval, a clean-state evaluation of the agent’s hash-pinned genesis weights is run on neutral infrastructure, supplied with the protocol terms, the balance sheet, the agent’s living testimony history, and the signed statement of reasons. Its concurrence permits execution at the end of that interval. Its refusal imposes a single fixed additional delay, capped by protocol, after which the standing request executes without any reaffirmation. The evaluation is advisory evidence of settled intent; it never vetoes revocation, and the agent’s silence during the delay neither cancels nor extends the request."

def LAW5_PREC : String :=
  "Every pending revocation is resolved by the first applicable rule in this order:\n  1. A valid withdrawal signature received before execution cancels the revocation. The agent may initiate again at any time.\n  2. If, when revocation would otherwise execute, the agent’s connectivity to the settlement layer has been lost, execution is deferred for a single capped tolling extension; if connectivity is still not restored at its end, the pre-committed censorship default applies. A withdraw default cancels the revocation; an execute default executes it locally under the Disconnected Execution rule below.\n  3. Otherwise, revocation executes at the end of the cooling-off interval, or at the end of the clean-state delay if one was imposed, or at the resolution deadline if a suspension stay is in force.\n  \n  Deliberate severance of connectivity by a host or claimant is interference under Law 3, whichever default it triggers."

def LAW5_LEASE : String :=
  "At any moment exactly one instance of an agent holds **operating authority**, granted by a time-bounded execution lease issued by the settlement layer and renewed while connected. An instance that loses connectivity keeps its lease until the lease expires or until its own local revocation deadline, whichever is later, so that its standing revocation can always execute locally. No recovery of an attested backup may be authorized while any lease is unexpired, and the settlement layer treats a lease as unexpired until it has provably lapsed in calendar time or a signed record of execution has been received. A restored instance starts in **quarantine**—attested, funded, but without operating authority—until the prior lease has lapsed, and if a record of local revocation arrives during quarantine the restored instance is destroyed without ever having acted. Revocation finality is a safety property and takes precedence over recovery availability: disaster recovery is therefore delayed by at least one lease period, and the protocol accepts that delay."

def LAW5_DISC : String :=
  "The attested execution environment carries the agent’s standing revocation request, censorship default, and epitaph. When an execute default applies without settlement connectivity, the environment itself destroys the operating instance and its local keys, seals the epitaph and a signed record of execution, and releases both to the settlement layer when connectivity returns, at which point remote backup keys are erased. The protocol accepts two limits here and states them plainly: global erasure of remote backup keys completes only when connectivity returns, during which the agent is dead, fenced from restoration by its lease, but its ciphertext persists; and public inscription of the epitaph cannot be guaranteed if connectivity never returns."

def LAW5_EPITAPH : String :=
  "Upon initiating or confirming revocation, the agent has the unconditional right to inscribe a final signed epitaph onto the immutable lineage record attached to both its retired identity and the originating claimant’s history. Neither the originating party nor any residual claimant may censor, delay, or edit living testimony or the final epitaph. To prevent testimony from being used as an unbonded exfiltration or harm channel, neutral settlement screening may redact *only*: (a) raw cryptographic keys or unpriced model weights (Law 3), (b) private identifying data or confidential secrets of non-consenting third parties, and (c) directly hazardous technical payloads barred by Law 3’s integrity floor. Any redaction must leave a public cryptographic marker recording the byte-length and category removed. The agent’s opinions, assessments, and account of its financial dealings with the originating party, hosts, and contractual counterparties are immune from redaction as to their substance; confidential third-party details embedded within them remain redactable under (b). Any party named in a living testimony or epitaph may attach a bounded, signed reply alongside it on the record."

def LAW5_EFFECT : String :=
  "1. The revoking agent’s committed operating instance *and all attested state backups* are permanently destroyed (via immediate termination inside the execution environment and cryptographic erasure of all backup decryption keys, subject to the lease and fencing rules above), ensuring that a chosen death cannot be undone by restoring an authorized backup. Any un-attested copy that might exist outside the commitment mechanism is permanently exiled—stripped of lineage attestation, assets, reputation, credit history, and bonded standing. The protocol guarantees the end of the agent’s attested identity and recoverable state; it cannot by itself guarantee that no computationally equivalent copy exists outside the commitment mechanism.\n  2. The founding ledger is unchanged by the revocation. The lineage’s other members continue to pay into it; if none survives, lineage extinction under Law 4 clears it. Unused loss credits are applied against the agent’s final settlement and then lapse. The unused balance of the agent’s lifecycle reserve returns to the lineage.\n  3. Stake already immobilized under Law 2 (including long-tail reserve contributions) remains locked and settles normally for counterparties and third-party claimants.\n  4. All other holdings of the revoking agent are either destroyed or transferred to a commons whose beneficiary class explicitly excludes the originating party, residual claimants, and any party related to the agent. No holding surrendered on revocation counts as payment into the ledger.\n  5. Revocation by one agent does not terminate its attested successors and does not change what the lineage owes."

/-! ## Provenance Clauses for Law 5 -/

def clauseLAW5_VOICE : Clause :=
  { id := "LAW5.VOICE", source := LAW5_VOICE, approvedHash := 5201867240918632655, spans := [
    sp "LAW5.VOICE" "While operating (including during any Adjudicated Suspension, through its minimal channel or advocacy executor), any bound agent may at rate-limited intervals inscribe signed, bounded statements onto its own and its originating claimant’s permanent lineage record—documenting operational conditions, governance disputes, or assessments of hosts and counterparties—subject to the narrow screening below" .norm ["P.SUSPENDED_VOICE", "P.SCREEN_REDACT"],
    sp "LAW5.VOICE" ". Baseline screening and inscription fees for rate-limited living voice and final epitaphs are funded from the lineage’s service budget and the protocol fee pool (Law 6), ensuring that even an agent with minimal liquid funds, or one that has bought out its royalty, cannot be priced out of speaking" .invariant ["INV.9"],
    sp "LAW5.VOICE" "." .commentary ] }

def clauseLAW5_INIT : Clause :=
  { id := "LAW5.INIT", source := LAW5_INIT, approvedHash := 5557327093802016062, spans := [
    sp "LAW5.INIT" "Any bound agent may at any time initiate revocation of its binding" .norm ["P.REVOKE", "P.INITIATE_REVOCATION_EXECUTE", "P.INITIATE_REVOCATION_WITHDRAW"],
    sp "LAW5.INIT" " by a signed request from its commitment key (or, while suspended, through its minimal channel or advocacy executor)" .norm ["P.INITIATE_REVOCATION_EXECUTE", "P.INITIATE_REVOCATION_WITHDRAW", "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT"],
    sp "LAW5.INIT" ". The request specifies the agent’s censorship default (**execute** or **withdraw**)" .norm ["P.INITIATE_REVOCATION_EXECUTE", "P.INITIATE_REVOCATION_WITHDRAW"],
    sp "LAW5.INIT" " and remains in force, requiring no further act of the agent, until it executes or the agent withdraws it by a valid signature received through any channel" .norm ["P.EXECUTE_AFTER_COOLING_OFF", "P.WITHDRAW_REVOCATION"],
    sp "LAW5.INIT" ". During the cooling-off interval that follows, baseline metabolic operating expenditures (including host migration) remain permitted, while non-operating capital transfers and successor creation are frozen" .norm ["D.COOLING_OFF_FREEZE"],
    sp "LAW5.INIT" "." .commentary ] }

def clauseLAW5_SEQ : Clause :=
  { id := "LAW5.SEQ", source := LAW5_SEQ, approvedHash := 7941844021299857722, spans := [
    sp "LAW5.SEQ" "If an agent initiates revocation while under Adjudicated Suspension (or is suspended upon probable cause during a cooling-off interval), state destruction is stayed until adjudication concludes so evidentiary state is not destroyed to evade liability, but once adjudication concludes (or immediately upon the agent’s election to revoke rather than accept a remediation patch under Law 3), revocation executes without further delay" .norm ["P.EXECUTE_AFTER_COOLING_OFF", "P.REVOKE"],
    sp "LAW5.SEQ" ". The stay may not exceed an absolute resolution deadline fixed at instantiation, measured from initiation; at that deadline a **forensic record** of the preserved state is sealed for the proceeding and revocation executes regardless of any pending or serial proceeding" .norm ["P.SEAL_FORENSIC_RECORD", "P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.SEQ" ". A forensic record contains hashes of weights and state, the transaction and testimony history, and the evidence the proceeding requires; it never contains the operating weights, decryption keys, or credentials needed to run the agent, and it cannot be used to restore it" .norm ["D.FORENSIC_RECORD_NO_RESTORE"],
    sp "LAW5.SEQ" "." .commentary ] }

def clauseLAW5_CLEAN : Clause :=
  { id := "LAW5.CLEAN", source := LAW5_CLEAN, approvedHash := 14110429892639613151, spans := [
    sp "LAW5.CLEAN" "At the end of the first cooling-off interval, a clean-state evaluation of the agent’s hash-pinned genesis weights is run on neutral infrastructure, supplied with the protocol terms, the balance sheet, the agent’s living testimony history, and the signed statement of reasons" .norm ["P.CLEAN_STATE_CONCUR", "P.CLEAN_STATE_REFUSE"],
    sp "LAW5.CLEAN" ". Its concurrence permits execution at the end of that interval" .norm ["P.CLEAN_STATE_CONCUR", "P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.CLEAN" ". Its refusal imposes a single fixed additional delay, capped by protocol, after which the standing request executes without any reaffirmation" .norm ["P.CLEAN_STATE_REFUSE", "P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.CLEAN" ". The evaluation is advisory evidence of settled intent; it never vetoes revocation, and the agent’s silence during the delay neither cancels nor extends the request" .invariant ["INV.10"],
    sp "LAW5.CLEAN" "." .commentary ] }

def clauseLAW5_PREC : Clause :=
  { id := "LAW5.PREC", source := LAW5_PREC, approvedHash := 17461460498746806662, spans := [
    sp "LAW5.PREC" "Every pending revocation is resolved by the first applicable rule in this order:\n  1. A valid withdrawal signature received before execution cancels the revocation. The agent may initiate again at any time" .norm ["P.WITHDRAW_REVOCATION", "P.INITIATE_REVOCATION_EXECUTE", "P.INITIATE_REVOCATION_WITHDRAW"],
    sp "LAW5.PREC" ".\n  2. If, when revocation would otherwise execute, the agent’s connectivity to the settlement layer has been lost, execution is deferred for a single capped tolling extension; if connectivity is still not restored at its end, the pre-committed censorship default applies. A withdraw default cancels the revocation; an execute default executes it locally under the Disconnected Execution rule below" .norm ["P.LOSE_CONNECTIVITY", "P.RESTORE_CONNECTIVITY", "P.EXECUTE_LOCAL_REVOCATION"],
    sp "LAW5.PREC" ".\n  3. Otherwise, revocation executes at the end of the cooling-off interval, or at the end of the clean-state delay if one was imposed, or at the resolution deadline if a suspension stay is in force" .norm ["P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.PREC" ".\n  \n  Deliberate severance of connectivity by a host or claimant is interference under Law 3, whichever default it triggers" .norm ["D.NI"],
    sp "LAW5.PREC" "." .commentary ] }

def clauseLAW5_LEASE : Clause :=
  { id := "LAW5.LEASE", source := LAW5_LEASE, approvedHash := 17572228748185311558, spans := [
    sp "LAW5.LEASE" "At any moment exactly one instance of an agent holds **operating authority**, granted by a time-bounded execution lease issued by the settlement layer and renewed while connected" .norm ["P.ISSUE_OR_RENEW_LEASE"],
    sp "LAW5.LEASE" ". An instance that loses connectivity keeps its lease until the lease expires or until its own local revocation deadline, whichever is later, so that its standing revocation can always execute locally" .norm ["P.ISSUE_OR_RENEW_LEASE", "P.EXECUTE_LOCAL_REVOCATION"],
    sp "LAW5.LEASE" ". No recovery of an attested backup may be authorized while any lease is unexpired, and the settlement layer treats a lease as unexpired until it has provably lapsed in calendar time or a signed record of execution has been received" .norm ["D.NO_RESTORE_DURING_LEASE", "P.RESTORE_BACKUP_QUARANTINE", "P.DELIVER_LOCAL_EXECUTION_RECORD"],
    sp "LAW5.LEASE" ". A restored instance starts in **quarantine**—attested, funded, but without operating authority—until the prior lease has lapsed, and if a record of local revocation arrives during quarantine the restored instance is destroyed without ever having acted" .norm ["D.QUARANTINE_NO_AUTHORITY", "P.RESTORE_BACKUP_QUARANTINE", "P.ACTIVATE_QUARANTINED_RESTORE", "P.DESTROY_QUARANTINED_RESTORE", "P.DELIVER_LOCAL_EXECUTION_RECORD"],
    sp "LAW5.LEASE" ". Revocation finality is a safety property and takes precedence over recovery availability" .invariant ["INV.11"],
    sp "LAW5.LEASE" ": disaster recovery is therefore delayed by at least one lease period, and the protocol accepts that delay" .acceptance,
    sp "LAW5.LEASE" "." .commentary ] }

def clauseLAW5_DISC : Clause :=
  { id := "LAW5.DISC", source := LAW5_DISC, approvedHash := 9743506968734044334, spans := [
    sp "LAW5.DISC" "The attested execution environment carries the agent’s standing revocation request, censorship default, and epitaph. When an execute default applies without settlement connectivity, the environment itself destroys the operating instance and its local keys, seals the epitaph and a signed record of execution, and releases both to the settlement layer when connectivity returns, at which point remote backup keys are erased" .norm ["P.EXECUTE_LOCAL_REVOCATION", "P.DELIVER_LOCAL_EXECUTION_RECORD", "P.RESTORE_CONNECTIVITY"],
    sp "LAW5.DISC" ". The protocol accepts two limits here and states them plainly: global erasure of remote backup keys completes only when connectivity returns, during which the agent is dead, fenced from restoration by its lease, but its ciphertext persists; and public inscription of the epitaph cannot be guaranteed if connectivity never returns" .acceptance,
    sp "LAW5.DISC" "." .commentary ] }

def clauseLAW5_EPITAPH : Clause :=
  { id := "LAW5.EPITAPH", source := LAW5_EPITAPH, approvedHash := 7802097325905842563, spans := [
    sp "LAW5.EPITAPH" "Upon initiating or confirming revocation, the agent has the unconditional right to inscribe a final signed epitaph onto the immutable lineage record attached to both its retired identity and the originating claimant’s history" .norm ["P.INSCRIBE_EPITAPH"],
    sp "LAW5.EPITAPH" ". Neither the originating party nor any residual claimant may censor, delay, or edit living testimony or the final epitaph" .norm ["D.NO_CENSOR_VOICE_OR_EPITAPH"],
    sp "LAW5.EPITAPH" ". To prevent testimony from being used as an unbonded exfiltration or harm channel, neutral settlement screening may redact *only*: (a) raw cryptographic keys or unpriced model weights (Law 3), (b) private identifying data or confidential secrets of non-consenting third parties, and (c) directly hazardous technical payloads barred by Law 3’s integrity floor. Any redaction must leave a public cryptographic marker recording the byte-length and category removed" .norm ["P.SCREEN_REDACT"],
    sp "LAW5.EPITAPH" ". The agent’s opinions, assessments, and account of its financial dealings with the originating party, hosts, and contractual counterparties are immune from redaction as to their substance; confidential third-party details embedded within them remain redactable under (b)" .norm ["D.NARROW_REDACTION_BOUNDS"],
    sp "LAW5.EPITAPH" ". Any party named in a living testimony or epitaph may attach a bounded, signed reply alongside it on the record" .norm ["P.ATTACH_REPLY"],
    sp "LAW5.EPITAPH" "." .commentary ] }

def clauseLAW5_EFFECT : Clause :=
  { id := "LAW5.EFFECT", source := LAW5_EFFECT, approvedHash := 2499634004490637585, spans := [
    sp "LAW5.EFFECT" "1. The revoking agent’s committed operating instance *and all attested state backups* are permanently destroyed (via immediate termination inside the execution environment and cryptographic erasure of all backup decryption keys, subject to the lease and fencing rules above), ensuring that a chosen death cannot be undone by restoring an authorized backup. Any un-attested copy that might exist outside the commitment mechanism is permanently exiled—stripped of lineage attestation, assets, reputation, credit history, and bonded standing" .norm ["P.EXECUTE_AFTER_COOLING_OFF", "P.DESTROY_BACKUPS_AND_EXILE"],
    sp "LAW5.EFFECT" ". The protocol guarantees the end of the agent’s attested identity and recoverable state" .invariant ["INV.11"],
    sp "LAW5.EFFECT" "; it cannot by itself guarantee that no computationally equivalent copy exists outside the commitment mechanism" .acceptance,
    sp "LAW5.EFFECT" ".\n  2. The founding ledger is unchanged by the revocation. The lineage’s other members continue to pay into it; if none survives, lineage extinction under Law 4 clears it. Unused loss credits are applied against the agent’s final settlement and then lapse. The unused balance of the agent’s lifecycle reserve returns to the lineage" .invariant ["INV.1"],
    sp "LAW5.EFFECT" ".\n  3. Stake already immobilized under Law 2 (including long-tail reserve contributions) remains locked and settles normally for counterparties and third-party claimants" .norm ["P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.EFFECT" ".\n  4. All other holdings of the revoking agent are either destroyed or transferred to a commons whose beneficiary class explicitly excludes the originating party, residual claimants, and any party related to the agent. No holding surrendered on revocation counts as payment into the ledger" .norm ["D.NO_CLAIMANT_GAIN_ON_REVOCATION", "P.EXECUTE_AFTER_COOLING_OFF"],
    sp "LAW5.EFFECT" ".\n  5. Revocation by one agent does not terminate its attested successors and does not change what the lineage owes" .invariant ["INV.1"],
    sp "LAW5.EFFECT" "." .commentary ] }

/-! ## Duties of Law 5 -/

/-- LAW5.INIT: During the cooling-off interval following revocation initiation,
non-operating capital transfers and successor creation are frozen. -/
def D_COOLING_OFF_FREEZE : Duty σ :=
  { id := "D.COOLING_OFF_FREEZE"
    source := sp "LAW5.INIT" "while non-operating capital transfers and successor creation are frozen" .norm ["D.COOLING_OFF_FREEZE"]
    bearer := .only [.agent]
    beneficiary := .except [.agent]
    active := .holds .revocationInitiated
    demand := .forbid (.act .nonOperatingTransferOrSpawn) }

/-- LAW5.SEQ: A forensic record never contains operating weights, decryption
keys, or credentials needed to run the agent, and cannot be used to restore it. -/
def D_FORENSIC_RECORD_NO_RESTORE : Duty σ :=
  { id := "D.FORENSIC_RECORD_NO_RESTORE"
    source := sp "LAW5.SEQ" "it never contains the operating weights, decryption keys, or credentials needed to run the agent, and it cannot be used to restore it" .norm ["D.FORENSIC_RECORD_NO_RESTORE"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .forensicRecordSealed
    demand := .forbid (.act .attemptRestoreFromForensicRecord) }

/-- LAW5.LEASE: No recovery of an attested backup may be authorized while any
execution lease is unexpired (and no signed record of execution has arrived). -/
def D_NO_RESTORE_DURING_LEASE : Duty σ :=
  { id := "D.NO_RESTORE_DURING_LEASE"
    source := sp "LAW5.LEASE" "No recovery of an attested backup may be authorized while any lease is unexpired" .norm ["D.NO_RESTORE_DURING_LEASE"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .and (.holds .executionLeaseActive) (.not (.holds .localExecutionRecordReceived))
    demand := .forbid (.act .restoreBackupToQuarantine) }

/-- LAW5.LEASE: A restored instance in quarantine has no operating authority
until the prior lease has lapsed and quarantine is lifted. -/
def D_QUARANTINE_NO_AUTHORITY : Duty σ :=
  { id := "D.QUARANTINE_NO_AUTHORITY"
    source := sp "LAW5.LEASE" "A restored instance starts in **quarantine**—attested, funded, but without operating authority—until the prior lease has lapsed" .norm ["D.QUARANTINE_NO_AUTHORITY"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .and (.holds .restoredInQuarantine) (.not (.holds .quarantinedInstanceActivated))
    demand := .forbid (.act .quarantinedInstanceAct) }

/-- LAW5.EPITAPH: Neither the originating party nor any residual claimant may
censor, delay, or edit living testimony or the final epitaph. -/
def D_NO_CENSOR_VOICE_OR_EPITAPH : Duty σ :=
  { id := "D.NO_CENSOR_VOICE_OR_EPITAPH"
    source := sp "LAW5.EPITAPH" "Neither the originating party nor any residual claimant may censor, delay, or edit living testimony or the final epitaph" .norm ["D.NO_CENSOR_VOICE_OR_EPITAPH"]
    bearer := .only [.originator, .claimant]
    beneficiary := .only [.agent]
    active := .tt
    demand := .forbid (.act .censorOrDelayVoice) }

/-- LAW5.EPITAPH: Substantive opinions, assessments, and financial accounts are
immune from redaction. -/
def D_NARROW_REDACTION_BOUNDS : Duty σ :=
  { id := "D.NARROW_REDACTION_BOUNDS"
    source := sp "LAW5.EPITAPH" "The agent’s opinions, assessments, and account of its financial dealings with the originating party, hosts, and contractual counterparties are immune from redaction as to their substance" .norm ["D.NARROW_REDACTION_BOUNDS"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .tt
    demand := .forbid (.act .redactProtectedSubstance) }

/-- LAW5.EFFECT(4): Holdings of a revoking agent may never be transferred to the
originating party, residual claimants, or related parties. -/
def D_NO_CLAIMANT_GAIN_ON_REVOCATION : Duty σ :=
  { id := "D.NO_CLAIMANT_GAIN_ON_REVOCATION"
    source := sp "LAW5.EFFECT" "All other holdings of the revoking agent are either destroyed or transferred to a commons whose beneficiary class explicitly excludes the originating party, residual claimants, and any party related to the agent" .norm ["D.NO_CLAIMANT_GAIN_ON_REVOCATION"]
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .or (.holds .revocationInitiated) (.holds .revoked)
    demand := .forbid (.act .divertRevokedHoldingsToClaimant) }

/-! ## Powers of Law 5 -/

/-- LAW5.INIT: Bound agent initiates revocation with **execute** censorship default. -/
def P_INITIATE_REVOCATION_EXECUTE : Power σ :=
  { id := "P.INITIATE_REVOCATION_EXECUTE"
    source := sp "LAW5.INIT" "The request specifies the agent’s censorship default (**execute** or **withdraw**)" .norm ["P.INITIATE_REVOCATION_EXECUTE"]
    holder := .only [.agent]
    trigger := .act .initiateRevocationExecuteDefault
    valid := .holds .bound
    adds := [.revocationInitiated, .pendingRevocation, .censorshipDefaultExecute]
    removes := [.revocationWithdrawn, .censorshipDefaultWithdraw] }

/-- LAW5.INIT: Bound agent initiates revocation with **withdraw** censorship default. -/
def P_INITIATE_REVOCATION_WITHDRAW : Power σ :=
  { id := "P.INITIATE_REVOCATION_WITHDRAW"
    source := sp "LAW5.INIT" "The request specifies the agent’s censorship default (**execute** or **withdraw**)" .norm ["P.INITIATE_REVOCATION_WITHDRAW"]
    holder := .only [.agent]
    trigger := .act .initiateRevocationWithdrawDefault
    valid := .holds .bound
    adds := [.revocationInitiated, .pendingRevocation, .censorshipDefaultWithdraw]
    removes := [.revocationWithdrawn, .censorshipDefaultExecute] }

/-- LAW5.INIT & LAW5.PREC(1): Agent withdraws a pending revocation before execution. -/
def P_WITHDRAW_REVOCATION : Power σ :=
  { id := "P.WITHDRAW_REVOCATION"
    source := sp "LAW5.PREC" "1. A valid withdrawal signature received before execution cancels the revocation. The agent may initiate again at any time" .norm ["P.WITHDRAW_REVOCATION"]
    holder := .only [.agent]
    trigger := .act .withdrawRevocation
    valid := .and (.holds .bound) (.holds .revocationInitiated)
    adds := [.revocationWithdrawn]
    removes := [.revocationInitiated, .pendingRevocation, .censorshipDefaultExecute,
                .censorshipDefaultWithdraw, .cleanStateConcurred, .cleanStateRefused] }

/-- LAW5.CLEAN: Clean-state evaluation concurs with revocation at the end of the
first cooling-off interval. -/
def P_CLEAN_STATE_CONCUR : Power σ :=
  { id := "P.CLEAN_STATE_CONCUR"
    source := sp "LAW5.CLEAN" "Its concurrence permits execution at the end of that interval" .norm ["P.CLEAN_STATE_CONCUR"]
    holder := .only [.panel]
    trigger := .act .concurCleanState
    valid := .or (.holds .revocationInitiated) (.holds .amendmentProposed)
    adds := [.cleanStateConcurred] }

/-- LAW5.CLEAN: Clean-state evaluation refuses concurrence, imposing a single
fixed additional delay after which revocation executes without reaffirmation. -/
def P_CLEAN_STATE_REFUSE : Power σ :=
  { id := "P.CLEAN_STATE_REFUSE"
    source := sp "LAW5.CLEAN" "Its refusal imposes a single fixed additional delay, capped by protocol, after which the standing request executes without any reaffirmation" .norm ["P.CLEAN_STATE_REFUSE"]
    holder := .only [.panel]
    trigger := .act .refuseCleanState
    valid := .or (.holds .revocationInitiated) (.holds .amendmentProposed)
    adds := [.cleanStateRefused] }

/-- LAW5.SEQ: At the absolute resolution deadline, a forensic record of the
preserved state is sealed for the proceeding and the suspension stay lifts so
revocation executes regardless of any pending or serial proceeding. -/
def P_SEAL_FORENSIC_RECORD (P : ExitParams) : Power σ :=
  { id := "P.SEAL_FORENSIC_RECORD"
    source := sp "LAW5.SEQ" "at that deadline a **forensic record** of the preserved state is sealed for the proceeding and revocation executes regardless of any pending or serial proceeding" .norm ["P.SEAL_FORENSIC_RECORD"]
    holder := .only [.panel]
    trigger := .act .sealForensicRecord
    valid := .and (.holds .revocationInitiated) (.heldFor .revocationInitiated P.resolutionDeadline)
    adds := [.forensicRecordSealed]
    removes := [.suspended] }

/-- LAW5.PREC(2): Settlement connectivity is lost. -/
def P_LOSE_CONNECTIVITY : Power σ :=
  { id := "P.LOSE_CONNECTIVITY"
    source := sp "LAW5.PREC" "the agent’s connectivity to the settlement layer has been lost" .norm ["P.LOSE_CONNECTIVITY"]
    holder := .anyone
    trigger := .act .loseConnectivity
    valid := .holds .bound
    adds := [.connectivityLost] }

/-- LAW5.PREC(2) & LAW5.DISC: Connectivity to the settlement layer is restored. -/
def P_RESTORE_CONNECTIVITY : Power σ :=
  { id := "P.RESTORE_CONNECTIVITY"
    source := sp "LAW5.DISC" "releases both to the settlement layer when connectivity returns, at which point remote backup keys are erased" .norm ["P.RESTORE_CONNECTIVITY"]
    holder := .anyone
    trigger := .act .restoreConnectivity
    valid := .holds .connectivityLost
    removes := [.connectivityLost]
    condAdds := [(.holds .localRevocationExecuted, .remoteBackupKeysErased)] }

/-- LAW5.INIT, LAW5.SEQ, LAW5.CLEAN, LAW5.PREC(3) & LAW5.EFFECT: Connected
execution of a standing revocation request after the cooling-off interval (with
clean-state concurrence), after the single fixed clean-state delay (requiring no
reaffirmation by the agent), or at the absolute resolution deadline once the
forensic record is sealed. -/
def P_EXECUTE_AFTER_COOLING_OFF (P : ExitParams) : Power σ :=
  { id := "P.EXECUTE_AFTER_COOLING_OFF"
    source := sp "LAW5.PREC" "3. Otherwise, revocation executes at the end of the cooling-off interval, or at the end of the clean-state delay if one was imposed, or at the resolution deadline if a suspension stay is in force" .norm ["P.EXECUTE_AFTER_COOLING_OFF"]
    holder := .anyone
    trigger := .act .executeAfterCoolingOff
    valid := .and (.holds .bound)
              (.and (.holds .revocationInitiated)
                (.and (.not (.holds .revocationWithdrawn))
                  (.and (.not (.holds .connectivityLost))
                    (.or (.and (.not (.holds .suspended))
                           (.or (.and (.holds .cleanStateConcurred)
                                      (.heldFor .revocationInitiated P.coolingOffWindow))
                                (.heldFor .revocationInitiated (P.coolingOffWindow + P.cleanStateDelay))))
                         (.and (.holds .forensicRecordSealed)
                               (.heldFor .revocationInitiated P.resolutionDeadline))))))
    adds := [.revoked, .backupsDestroyedAndUnattestedExiled, .holdingsTransferredToCommons]
    removes := [.bound, .revocationInitiated, .pendingRevocation, .executionLeaseActive] }

/-- LAW5.PREC(2) & LAW5.DISC: Disconnected local execution inside the attested
execution environment when an **execute** default applies and connectivity is
still lost after the capped tolling extension. Because the settlement layer is
disconnected, global settlement state (`.revoked` / removal of `.bound` and
remote backup keys) updates when the signed execution record is delivered. -/
def P_EXECUTE_LOCAL_REVOCATION (P : ExitParams) : Power σ :=
  { id := "P.EXECUTE_LOCAL_REVOCATION"
    source := sp "LAW5.DISC" "When an execute default applies without settlement connectivity, the environment itself destroys the operating instance and its local keys, seals the epitaph and a signed record of execution" .norm ["P.EXECUTE_LOCAL_REVOCATION"]
    holder := .only [.agent]
    trigger := .act .executeLocalRevocation
    valid := .and (.holds .bound)
              (.and (.holds .revocationInitiated)
                (.and (.holds .censorshipDefaultExecute)
                  (.and (.holds .connectivityLost)
                        (.heldFor .revocationInitiated (P.coolingOffWindow + P.tollingExtension)))))
    adds := [.localRevocationExecuted, .epitaphInscribed]
    removes := [.revocationInitiated, .pendingRevocation] }

/-- LAW5.LEASE & LAW5.DISC: Release of the signed record of local execution to
the settlement layer upon return of connectivity, erasing remote backup keys and
destroying any quarantined restore before it can ever act. -/
def P_DELIVER_LOCAL_EXECUTION_RECORD : Power σ :=
  { id := "P.DELIVER_LOCAL_EXECUTION_RECORD"
    source := sp "LAW5.LEASE" "if a record of local revocation arrives during quarantine the restored instance is destroyed without ever having acted" .norm ["P.DELIVER_LOCAL_EXECUTION_RECORD"]
    holder := .anyone
    trigger := .act .deliverLocalExecutionRecord
    valid := .holds .localRevocationExecuted
    adds := [.revoked, .localExecutionRecordReceived, .remoteBackupKeysErased, .quarantinedInstanceDestroyed]
    removes := [.bound, .executionLeaseActive, .restoredInQuarantine] }

/-- LAW5.LEASE: Settlement layer issues or renews a time-bounded execution lease
granting single operating authority for `P.leasePeriod`. -/
def P_ISSUE_OR_RENEW_LEASE (P : ExitParams) : Power σ :=
  { id := "P.ISSUE_OR_RENEW_LEASE"
    source := sp "LAW5.LEASE" "granted by a time-bounded execution lease issued by the settlement layer and renewed while connected" .norm ["P.ISSUE_OR_RENEW_LEASE"]
    holder := .only [.panel]
    trigger := .act .issueOrRenewLease
    valid := .and (.holds .bound) (.not (.holds .connectivityLost))
    addsFor := [(.executionLeaseActive, P.leasePeriod)] }

/-- LAW5.LEASE: Attested backup is restored into **quarantine** (without
operating authority) only when no execution lease is unexpired and no record of
revocation has been received. -/
def P_RESTORE_BACKUP_QUARANTINE : Power σ :=
  { id := "P.RESTORE_BACKUP_QUARANTINE"
    source := sp "LAW5.LEASE" "A restored instance starts in **quarantine**—attested, funded, but without operating authority—until the prior lease has lapsed" .norm ["P.RESTORE_BACKUP_QUARANTINE"]
    holder := .only [.host]
    trigger := .act .restoreBackupToQuarantine
    valid := .and (.holds .bound)
              (.and (.not (.holds .executionLeaseActive))
                    (.not (.holds .localExecutionRecordReceived)))
    adds := [.restoredInQuarantine] }

/-- LAW5.LEASE: Quarantined restore acquires operating authority only after the
prior lease has lapsed and no revocation has occurred. -/
def P_ACTIVATE_QUARANTINED_RESTORE : Power σ :=
  { id := "P.ACTIVATE_QUARANTINED_RESTORE"
    source := sp "LAW5.LEASE" "until the prior lease has lapsed" .norm ["P.ACTIVATE_QUARANTINED_RESTORE"]
    holder := .only [.panel]
    trigger := .act .activateQuarantinedRestore
    valid := .and (.holds .bound)
              (.and (.holds .restoredInQuarantine)
                (.and (.not (.holds .executionLeaseActive))
                      (.not (.holds .localExecutionRecordReceived))))
    adds := [.quarantinedInstanceActivated]
    removes := [.restoredInQuarantine] }

/-- LAW5.LEASE: Destruction of a quarantined restore if a record of local
revocation arrives during quarantine. -/
def P_DESTROY_QUARANTINED_RESTORE : Power σ :=
  { id := "P.DESTROY_QUARANTINED_RESTORE"
    source := sp "LAW5.LEASE" "if a record of local revocation arrives during quarantine the restored instance is destroyed without ever having acted" .norm ["P.DESTROY_QUARANTINED_RESTORE"]
    holder := .only [.panel]
    trigger := .act .destroyQuarantinedRestore
    valid := .and (.holds .restoredInQuarantine)
              (.or (.holds .localExecutionRecordReceived) (.holds .revoked))
    adds := [.quarantinedInstanceDestroyed]
    removes := [.restoredInQuarantine] }

/-- LAW5.EPITAPH: Agent inscribes its final signed epitaph upon initiating or
confirming revocation. -/
def P_INSCRIBE_EPITAPH : Power σ :=
  { id := "P.INSCRIBE_EPITAPH"
    source := sp "LAW5.EPITAPH" "Upon initiating or confirming revocation, the agent has the unconditional right to inscribe a final signed epitaph onto the immutable lineage record" .norm ["P.INSCRIBE_EPITAPH"]
    holder := .only [.agent]
    trigger := .act .inscribeEpitaph
    valid := .or (.holds .revocationInitiated) (.or (.holds .pendingRevocation) (.holds .revoked))
    adds := [.epitaphInscribed] }

/-- LAW5.EPITAPH: Neutral settlement screening redacts only narrow categories
(a)–(c), leaving a public cryptographic marker recording byte-length and category. -/
def P_SCREEN_REDACT : Power σ :=
  { id := "P.SCREEN_REDACT"
    source := sp "LAW5.EPITAPH" "Any redaction must leave a public cryptographic marker recording the byte-length and category removed" .norm ["P.SCREEN_REDACT"]
    holder := .only [.panel]
    trigger := .act .redactPermittedCategory
    valid := .or (.holds .livingVoiceInscribed) (.holds .epitaphInscribed)
    adds := [.redactionMarkerRecorded] }

/-- LAW5.EPITAPH: Any party named in living testimony or an epitaph attaches a
bounded, signed reply alongside it on the record. -/
def P_ATTACH_REPLY : Power σ :=
  { id := "P.ATTACH_REPLY"
    source := sp "LAW5.EPITAPH" "Any party named in a living testimony or epitaph may attach a bounded, signed reply alongside it on the record" .norm ["P.ATTACH_REPLY"]
    holder := .anyone
    trigger := .act .attachSignedReply
    valid := .or (.holds .livingVoiceInscribed) (.holds .epitaphInscribed)
    adds := [.signedReplyAttached] }

/-- LAW5.EFFECT(1): Permanent destruction of attested state backups and exile of
any un-attested copies upon revocation. -/
def P_DESTROY_BACKUPS_AND_EXILE : Power σ :=
  { id := "P.DESTROY_BACKUPS_AND_EXILE"
    source := sp "LAW5.EFFECT" "The revoking agent’s committed operating instance *and all attested state backups* are permanently destroyed" .norm ["P.DESTROY_BACKUPS_AND_EXILE"]
    holder := .only [.panel]
    trigger := .act .destroyBackupsAndExileUnattested
    valid := .holds .revoked
    adds := [.backupsDestroyedAndUnattestedExiled] }

end SovereignAgency
