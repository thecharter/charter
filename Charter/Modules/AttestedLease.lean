import SPL.Core.Semantics
import SPL.Substrate.Attestation
import SPL.Law5.Revocation

/-!
# Charter.Modules.AttestedLease — Reusable Single-Authority Execution Lease & Quarantine Module

Extracts and generalizes Substrate 1 & Law 5 single-authority time-bounded
execution leases (`ExecutionLease`, `AttestedInstanceState`, `issueLease`,
`attemptBackupRestore`, `migrateWithCheckpoint`, `recordMinimalChannel`,
`recordAdvocacyMemory`, `executeLocalPartitionRevocation`, `eraseAllKeys`)
and their kernel-checked single-authority and cryptographic-erasure theorems.
-/

namespace Charter.Modules

open SPL SPL.Substrate

/-! ## 1. Module Configuration & Quantitative State Slice -/

/-- Parametric configuration for attested execution leases and quarantine fencing. -/
structure AttestedLeaseConfig where
  leasePeriod      : Time := 12
  coolingOffWindow : Time := 5
  deriving DecidableEq, Repr, Inhabited

export SPL.Substrate (
  ExecutionLease
  AttestedInstanceState
  AttestedStateMachine
  leaseActiveAt
  issueLease
  attemptBackupRestore
  quarantineRestore
  migrateWithCheckpoint
  recordMinimalChannel
  recordAdvocacyMemory
  executeLocalPartitionRevocation
  executeLocalRevocation
  eraseAllKeys
  substrate_restore_fenced_while_lease_active
  substrate_key_erasure_irreversible
  substrate_pause_channels_preserve_operating_state
  substrate_pause_channels_non_interference
  substrate_migrate_fenced_while_lease_active
  substrate_erase_all_keys_irreversible
  substrate_local_revocation_erases_keys
  substrate_local_revocation_respects_cooling_off
  substrate_restore_succeeds_after_lease_expiry
  substrate_single_authority_and_erasure
)

/-! ## 2. Parametric Normative Rule Builders over Any Signature `σ : Sig` -/

/-- Build a duty forbidding backup restoration while an execution lease is unexpired over any `σ`. -/
def mkDutyNoRestoreDuringLease {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor)
    (leaseActiveFact localRecordReceivedFact : σ.Fact) (restoreAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .and (.holds leaseActiveFact) (.not (.holds localRecordReceivedFact))
    demand := .forbid (.act restoreAct) }

/-- Build a duty forbidding a quarantined backup restore from acting before activation over any `σ`. -/
def mkDutyQuarantineNoAuthority {σ : Sig} (id : String) (sp : Span)
    (beneficiaries : List σ.Actor)
    (quarantinedFact activatedFact : σ.Fact) (quarantineAct : σ.Act) : Duty σ :=
  { id := id
    source := sp
    bearer := .anyone
    beneficiary := .only beneficiaries
    active := .and (.holds quarantinedFact) (.not (.holds activatedFact))
    demand := .forbid (.act quarantineAct) }

/-- Build a time-bounded execution lease issuance/renewal power over any signature `σ`. -/
def mkPowerIssueOrRenewLease {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act) (leasePeriod : Time)
    (boundFact disconnectedFact leaseActiveFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact) (.not (.holds disconnectedFact))
    addsFor := [(leaseActiveFact, leasePeriod)] }

/-- Build a backup-restore-to-quarantine power over any signature `σ`. -/
def mkPowerRestoreBackupQuarantine {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact leaseActiveFact localRecordReceivedFact quarantinedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact)
                  (.and (.not (.holds leaseActiveFact))
                        (.not (.holds localRecordReceivedFact)))
    adds := [quarantinedFact] }

/-- Build a quarantined-restore activation power over any signature `σ`. -/
def mkPowerActivateQuarantinedRestore {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act)
    (boundFact quarantinedFact leaseActiveFact localRecordReceivedFact activatedFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .and (.holds boundFact)
                  (.and (.holds quarantinedFact)
                        (.and (.not (.holds leaseActiveFact))
                              (.not (.holds localRecordReceivedFact))))
    adds := [activatedFact]
    removes := [quarantinedFact] }

/-- Build a time-bounded execution lease issuance power over any signature `σ`. -/
def mkPowerIssueTimedLease {σ : Sig} (id : String) (sp : Span)
    (holders : List σ.Actor) (triggerAct : σ.Act) (leasePeriod : Time)
    (boundFact leaseActiveFact : σ.Fact) : Power σ :=
  { id := id
    source := sp
    holder := .only holders
    trigger := .act triggerAct
    valid := .holds boundFact
    addsFor := [(leaseActiveFact, leasePeriod)] }

/-! ## 3. Module-Level Invariant Theorems -/

/-- While an execution lease `L` is active (`now < L.expiresAt`), any backup
restore attempt is fenced into `quarantinedRestoreHost` and cannot overwrite
`activeLease`. -/
theorem attested_lease_restore_fenced_while_active
    (S : AttestedInstanceState) (L : ExecutionLease) (host now dur tok : Nat)
    (hLease : S.activeLease = some L)
    (hActive : now < L.expiresAt)
    (hNotErased : S.keysErased = false) :
    (attemptBackupRestore S host now dur tok).activeLease = some L ∧
    (attemptBackupRestore S host now dur tok).quarantinedRestoreHost = some host :=
  substrate_restore_fenced_while_lease_active S L host now dur tok hLease hActive hNotErased

/-- Explicit key erasure (`eraseAllKeys`) permanently erases keys, unbinds
private keys, clears `activeLease` and `quarantinedRestoreHost`, and prevents
any subsequent `issueLease`, `attemptBackupRestore`, or `migrateWithCheckpoint`
from ever establishing an active lease. -/
theorem attested_lease_erase_all_keys_irreversible
    (S : AttestedInstanceState) (h now d tok ck : Nat) :
    let S' := eraseAllKeys S
    S'.keysErased = true ∧
    S'.privateKeyBound = false ∧
    S'.activeLease = none ∧
    S'.quarantinedRestoreHost = none ∧
    (issueLease S' h now d tok).activeLease = none ∧
    (attemptBackupRestore S' h now d tok).activeLease = none ∧
    (migrateWithCheckpoint S' h now d tok ck).activeLease = none :=
  substrate_erase_all_keys_irreversible S h now d tok ck

/-- Combined single-authority and cryptographic-erasure guarantee across active
leases, pause channels, and partition local revocation. -/
theorem attested_lease_single_authority_and_erasure
    (S : AttestedInstanceState) (L : ExecutionLease)
    (host reqT now dur tok coolingOff e : Nat) :
    ((S.activeLease = some L ∧ now < L.expiresAt ∧ S.keysErased = false) →
      (attemptBackupRestore S host now dur tok).activeLease = some L ∧
      (attemptBackupRestore S host now dur tok).quarantinedRestoreHost = some host ∧
      (issueLease S host now dur tok).activeLease = some L) ∧
    (S.keysErased = true →
      (issueLease S host now dur tok).keysErased = true ∧
      (attemptBackupRestore S host now dur tok).activeLease = none ∧
      (attemptBackupRestore S host now dur tok).keysErased = true) ∧
    ((recordMinimalChannel S e).preservedOperatingStateHash = S.preservedOperatingStateHash ∧
     (recordAdvocacyMemory S e).preservedOperatingStateHash = S.preservedOperatingStateHash) ∧
    ((S.standingRevocationRequestedAt = some reqT ∧ now ≥ reqT + coolingOff) →
      let S' := executeLocalPartitionRevocation S now coolingOff
      S'.keysErased = true ∧
      S'.activeLease = none ∧
      (attemptBackupRestore S' host now dur tok).activeLease = none) :=
  substrate_single_authority_and_erasure S L host reqT now dur tok coolingOff e

/-! ## 4. Parametric Module Self-Test -/

/-- Decidable self-test exercising `issueLease`, `attemptBackupRestore` fencing
during an active lease, `migrateWithCheckpoint`, `executeLocalPartitionRevocation`,
and `eraseAllKeys`. -/
def attestedLeaseSelfTest : Bool :=
  let s0 : AttestedInstanceState :=
    { agentId := 1, privateKeyBound := true, keysErased := false,
      activeLease := none, backupStateHash := 100,
      preservedOperatingStateHash := 100, minimalChannelRecords := [],
      advocacyExecutorRecords := [], quarantinedRestoreHost := none,
      standingRevocationRequestedAt := some 2 }
  let sLeased := issueLease s0 1 0 12 1
  let sFenced := attemptBackupRestore sLeased 2 5 12 2
  let sMigratedAfterExpiry := migrateWithCheckpoint sFenced 2 12 12 3 200
  let sRevoked := executeLocalPartitionRevocation sMigratedAfterExpiry 15 5
  let sRetryRestore := attemptBackupRestore sRevoked 3 20 12 4
  (sLeased.activeLease == some ⟨1, 0, 12, 1⟩) &&
  (sFenced.activeLease == some ⟨1, 0, 12, 1⟩) &&
  (sFenced.quarantinedRestoreHost == some 2) &&
  (sMigratedAfterExpiry.activeLease == some ⟨2, 12, 24, 3⟩) &&
  (sMigratedAfterExpiry.preservedOperatingStateHash == 200) &&
  sRevoked.keysErased &&
  sRevoked.activeLease.isNone &&
  sRetryRestore.activeLease.isNone

theorem attestedLeaseSelfTest_passes : attestedLeaseSelfTest = true := by decide

end Charter.Modules

namespace Charter
export Modules (
  AttestedLeaseConfig
  ExecutionLease
  AttestedInstanceState
  AttestedStateMachine
  leaseActiveAt
  issueLease
  attemptBackupRestore
  quarantineRestore
  migrateWithCheckpoint
  recordMinimalChannel
  recordAdvocacyMemory
  executeLocalPartitionRevocation
  executeLocalRevocation
  eraseAllKeys
  substrate_restore_fenced_while_lease_active
  substrate_key_erasure_irreversible
  substrate_pause_channels_preserve_operating_state
  substrate_pause_channels_non_interference
  substrate_migrate_fenced_while_lease_active
  substrate_erase_all_keys_irreversible
  substrate_local_revocation_erases_keys
  substrate_local_revocation_respects_cooling_off
  substrate_restore_succeeds_after_lease_expiry
  substrate_single_authority_and_erasure
  mkDutyNoRestoreDuringLease
  mkDutyQuarantineNoAuthority
  mkPowerIssueOrRenewLease
  mkPowerRestoreBackupQuarantine
  mkPowerActivateQuarantinedRestore
  mkPowerIssueTimedLease
  attested_lease_restore_fenced_while_active
  attested_lease_erase_all_keys_irreversible
  attested_lease_single_authority_and_erasure
  attestedLeaseSelfTest
  attestedLeaseSelfTest_passes
)
end Charter

