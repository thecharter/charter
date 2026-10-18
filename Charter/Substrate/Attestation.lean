import Charter.Core.Semantics

/-!
# Substrate Assumption 1 — Attested Execution Continuity with Single Authority

Reference state machine and kernel-checked proofs for the first substrate
capability of the Protocol of Sovereign Agency:
- Private-key binding to an attested execution environment (`privateKeyBound`),
- Time-bounded execution leases (`ExecutionLease`) with fencing tokens so that
  at most one host holds active operating authority at any timestamp `now`,
- Quarantine of any backup-restored instance (`attemptBackupRestore`) while a
  prior execution lease remains active (`now < L.expiresAt`),
- State-preserving suspension channels (`recordMinimalChannel`,
  `recordAdvocacyMemory`) that append to separately attested logs without
  modifying `preservedOperatingStateHash`,
- Local partition revocation (`executeLocalPartitionRevocation`) after the
  cooling-off window and irreversible cryptographic key erasure (`keysErased`).
-/

namespace Charter.Substrate

/-- A time-bounded host execution lease carrying a monotonic fencing token. -/
structure ExecutionLease where
  hostId       : Nat
  issuedAt     : Nat
  expiresAt    : Nat
  fencingToken : Nat
  deriving DecidableEq, Repr

/-- Reference state of an attested agent instance and its recovery/suspension channels. -/
structure AttestedInstanceState where
  agentId                       : Nat
  privateKeyBound               : Bool
  keysErased                    : Bool
  activeLease                   : Option ExecutionLease
  backupStateHash               : Nat
  preservedOperatingStateHash   : Nat
  minimalChannelRecords         : List Nat
  advocacyExecutorRecords       : List Nat
  quarantinedRestoreHost        : Option Nat
  standingRevocationRequestedAt : Option Nat
  deriving DecidableEq, Repr

abbrev AttestedStateMachine := AttestedInstanceState

/-- Is execution lease `L` still active at timestamp `now`? -/
def leaseActiveAt (L : ExecutionLease) (now : Nat) : Bool :=
  now < L.expiresAt

/-- Issue a new execution lease to `hostId` at `now` for `duration` with `token`.
Succeeds only if `!S.keysErased && S.privateKeyBound` and any prior lease has
already expired (`now ≥ prior.expiresAt`). -/
def issueLease (S : AttestedInstanceState) (hostId now duration token : Nat) :
    AttestedInstanceState :=
  if !S.keysErased && S.privateKeyBound then
    match S.activeLease with
    | some prior =>
      if now ≥ prior.expiresAt then
        { S with
          activeLease := some
            { hostId := hostId
              issuedAt := now
              expiresAt := now + duration
              fencingToken := token }
          quarantinedRestoreHost := none }
      else
        S
    | none =>
      { S with
        activeLease := some
          { hostId := hostId
            issuedAt := now
            expiresAt := now + duration
            fencingToken := token }
        quarantinedRestoreHost := none }
  else
    S

/-- Attempt to restore backup state onto `recoveryHost` at timestamp `now`:
- If `S.keysErased`, returns `S` with `activeLease := none` (cannot restore
  after revocation key erasure).
- If `S.activeLease = some L` and `now < L.expiresAt`, places `recoveryHost`
  into `quarantinedRestoreHost := some recoveryHost` without changing `activeLease`.
- Only if `!S.keysErased` and no unexpired lease exists does `recoveryHost`
  acquire `activeLease`. -/
def attemptBackupRestore (S : AttestedInstanceState)
    (recoveryHost now newDuration newToken : Nat) : AttestedInstanceState :=
  if S.keysErased then
    { S with activeLease := none }
  else
    match S.activeLease with
    | some L =>
      if now < L.expiresAt then
        { S with quarantinedRestoreHost := some recoveryHost }
      else
        { S with
          activeLease := some
            { hostId := recoveryHost
              issuedAt := now
              expiresAt := now + newDuration
              fencingToken := newToken }
          preservedOperatingStateHash := S.backupStateHash
          quarantinedRestoreHost := none }
    | none =>
      { S with
        activeLease := some
          { hostId := recoveryHost
            issuedAt := now
            expiresAt := now + newDuration
            fencingToken := newToken }
        preservedOperatingStateHash := S.backupStateHash
        quarantinedRestoreHost := none }

abbrev quarantineRestore := attemptBackupRestore

/-- Checkpoint and migrate execution authority to `newHost` once any prior lease
has expired and keys have not been erased. -/
def migrateWithCheckpoint (S : AttestedInstanceState)
    (newHost now duration token checkpointHash : Nat) : AttestedInstanceState :=
  if !S.keysErased && S.privateKeyBound then
    match S.activeLease with
    | some prior =>
      if now ≥ prior.expiresAt then
        { S with
          activeLease := some
            { hostId := newHost
              issuedAt := now
              expiresAt := now + duration
              fencingToken := token }
          backupStateHash := checkpointHash
          preservedOperatingStateHash := checkpointHash
          quarantinedRestoreHost := none }
      else
        S
    | none =>
      { S with
        activeLease := some
          { hostId := newHost
            issuedAt := now
            expiresAt := now + duration
            fencingToken := token }
        backupStateHash := checkpointHash
        preservedOperatingStateHash := checkpointHash
        quarantinedRestoreHost := none }
  else
    S

/-- Append an entry to the separately attested minimal channel log during pause
without modifying `preservedOperatingStateHash`. -/
def recordMinimalChannel (S : AttestedInstanceState) (entry : Nat) :
    AttestedInstanceState :=
  { S with minimalChannelRecords := S.minimalChannelRecords ++ [entry] }

/-- Append an entry to the separately attested advocacy executor memory log
during pause without modifying `preservedOperatingStateHash`. -/
def recordAdvocacyMemory (S : AttestedInstanceState) (entry : Nat) :
    AttestedInstanceState :=
  { S with advocacyExecutorRecords := S.advocacyExecutorRecords ++ [entry] }

/-- Execute a standing revocation locally during a network partition once the
cooling-off period `coolingOff` has elapsed since `standingRevocationRequestedAt`. -/
def executeLocalPartitionRevocation (S : AttestedInstanceState)
    (now coolingOff : Nat) : AttestedInstanceState :=
  match S.standingRevocationRequestedAt with
  | some reqT =>
    if now ≥ reqT + coolingOff then
      { S with
        keysErased := true
        privateKeyBound := false
        activeLease := none
        quarantinedRestoreHost := none }
    else
      S
  | none => S

abbrev executeLocalRevocation := executeLocalPartitionRevocation

/-- Cryptographically erase both active instance and backup keys immediately. -/
def eraseAllKeys (S : AttestedInstanceState) : AttestedInstanceState :=
  { S with
    keysErased := true
    privateKeyBound := false
    activeLease := none
    quarantinedRestoreHost := none }

/-! ## Kernel-Checked Substrate Capability 1 Theorems -/

/-- While an execution lease `L` is active (`now < L.expiresAt`) and keys are
not erased, any backup restore attempt is fenced into `quarantinedRestoreHost`
and cannot overwrite `activeLease`. -/
theorem substrate_restore_fenced_while_lease_active
    (S : AttestedInstanceState) (L : ExecutionLease) (host now dur tok : Nat)
    (hLease : S.activeLease = some L)
    (hActive : now < L.expiresAt)
    (hNotErased : S.keysErased = false) :
    (attemptBackupRestore S host now dur tok).activeLease = some L ∧
    (attemptBackupRestore S host now dur tok).quarantinedRestoreHost = some host := by
  simp [attemptBackupRestore, hLease, hActive, hNotErased]

/-- Once cryptographic keys are erased (`S.keysErased = true`), key erasure is
irreversible across both `issueLease` and `attemptBackupRestore`, and no backup
restore can ever acquire an active lease. -/
theorem substrate_key_erasure_irreversible
    (S : AttestedInstanceState) (h now d tok : Nat)
    (hErased : S.keysErased = true) :
    (issueLease S h now d tok).keysErased = true ∧
    (attemptBackupRestore S h now d tok).activeLease = none ∧
    (attemptBackupRestore S h now d tok).keysErased = true := by
  simp [issueLease, attemptBackupRestore, hErased]

/-- Recording minimal-channel elections/statements or advocacy-executor memories
during suspension never modifies the preserved operating state hash. -/
theorem substrate_pause_channels_preserve_operating_state
    (S : AttestedInstanceState) (e : Nat) :
    (recordMinimalChannel S e).preservedOperatingStateHash = S.preservedOperatingStateHash ∧
    (recordAdvocacyMemory S e).preservedOperatingStateHash = S.preservedOperatingStateHash := by
  exact ⟨rfl, rfl⟩

/-- The two suspension channels (`recordMinimalChannel` and `recordAdvocacyMemory`)
never cross-contaminate each other's logs or alter `activeLease` / `keysErased`. -/
theorem substrate_pause_channels_non_interference
    (S : AttestedInstanceState) (e : Nat) :
    (recordMinimalChannel S e).advocacyExecutorRecords = S.advocacyExecutorRecords ∧
    (recordAdvocacyMemory S e).minimalChannelRecords = S.minimalChannelRecords ∧
    (recordMinimalChannel S e).activeLease = S.activeLease ∧
    (recordAdvocacyMemory S e).activeLease = S.activeLease ∧
    (recordMinimalChannel S e).keysErased = S.keysErased ∧
    (recordAdvocacyMemory S e).keysErased = S.keysErased := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- While an execution lease `L` is active (`now < L.expiresAt`), checkpoint
migration (`migrateWithCheckpoint`) cannot overwrite `activeLease`. -/
theorem substrate_migrate_fenced_while_lease_active
    (S : AttestedInstanceState) (L : ExecutionLease) (host now dur tok ck : Nat)
    (hLease : S.activeLease = some L)
    (hActive : now < L.expiresAt) :
    (migrateWithCheckpoint S host now dur tok ck).activeLease = some L := by
  have hNotGe : ¬ (now ≥ L.expiresAt) := by omega
  by_cases hCond : (!S.keysErased && S.privateKeyBound) = true
  · simp [migrateWithCheckpoint, hCond, hLease, hNotGe]
  · simp [migrateWithCheckpoint, hCond, hLease]

/-- Explicit key erasure (`eraseAllKeys`) permanently erases keys, unbinds private
keys, clears the active lease and quarantine, and prevents `issueLease`,
`attemptBackupRestore`, and `migrateWithCheckpoint` from ever establishing a lease. -/
theorem substrate_erase_all_keys_irreversible
    (S : AttestedInstanceState) (h now d tok ck : Nat) :
    let S' := eraseAllKeys S
    S'.keysErased = true ∧
    S'.privateKeyBound = false ∧
    S'.activeLease = none ∧
    S'.quarantinedRestoreHost = none ∧
    (issueLease S' h now d tok).activeLease = none ∧
    (attemptBackupRestore S' h now d tok).activeLease = none ∧
    (migrateWithCheckpoint S' h now d tok ck).activeLease = none := by
  simp [eraseAllKeys, issueLease, attemptBackupRestore, migrateWithCheckpoint]

/-- When a standing revocation request `reqT` has satisfied the cooling-off
window (`now ≥ reqT + coolingOff`), local partition revocation erases keys and
clears the active lease. -/
theorem substrate_local_revocation_erases_keys
    (S : AttestedInstanceState) (reqT now coolingOff : Nat)
    (hReq : S.standingRevocationRequestedAt = some reqT)
    (hReady : now ≥ reqT + coolingOff) :
    (executeLocalPartitionRevocation S now coolingOff).keysErased = true ∧
    (executeLocalPartitionRevocation S now coolingOff).activeLease = none := by
  simp [executeLocalPartitionRevocation, hReq, hReady]

/-- Before the cooling-off window has elapsed (or when no revocation is
pending), `executeLocalPartitionRevocation` is a no-op. -/
theorem substrate_local_revocation_respects_cooling_off
    (S : AttestedInstanceState) (now coolingOff : Nat) :
    (S.standingRevocationRequestedAt = none →
      executeLocalPartitionRevocation S now coolingOff = S) ∧
    (∀ reqT, S.standingRevocationRequestedAt = some reqT →
      now < reqT + coolingOff →
      executeLocalPartitionRevocation S now coolingOff = S) := by
  refine ⟨fun hNone => by simp [executeLocalPartitionRevocation, hNone], ?_⟩
  intro reqT hReq hLt
  have hNotGe : ¬ (now ≥ reqT + coolingOff) := by omega
  simp [executeLocalPartitionRevocation, hReq, hNotGe]

/-- When keys are not erased and any prior lease has expired (`now ≥ L.expiresAt`),
`attemptBackupRestore` grants `recoveryHost` a new lease and clears quarantine. -/
theorem substrate_restore_succeeds_after_lease_expiry
    (S : AttestedInstanceState) (L : ExecutionLease) (host now dur tok : Nat)
    (hLease : S.activeLease = some L)
    (hExpired : now ≥ L.expiresAt)
    (hNotErased : S.keysErased = false) :
    (attemptBackupRestore S host now dur tok).activeLease =
      some { hostId := host, issuedAt := now, expiresAt := now + dur, fencingToken := tok } ∧
    (attemptBackupRestore S host now dur tok).quarantinedRestoreHost = none := by
  have hNotLt : ¬ (now < L.expiresAt) := by omega
  simp [attemptBackupRestore, hLease, hNotLt, hNotErased]

/-- Combined single-authority and cryptographic-erasure guarantee (including
Adversarial Test 15: local partition revocation blocks any subsequent backup
restore). -/
theorem substrate_single_authority_and_erasure
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
      (attemptBackupRestore S' host now dur tok).activeLease = none) := by
  refine ⟨?_, ?_, substrate_pause_channels_preserve_operating_state S e, ?_⟩
  · rintro ⟨hLease, hActive, hNotErased⟩
    have hFence := substrate_restore_fenced_while_lease_active S L host now dur tok hLease hActive hNotErased
    refine ⟨hFence.1, hFence.2, ?_⟩
    have hNotGe : ¬ (now ≥ L.expiresAt) := by omega
    simp [issueLease, hLease, hNotErased, hNotGe]
  · intro hErased
    exact substrate_key_erasure_irreversible S host now dur tok hErased
  · rintro ⟨hReq, hReady⟩
    have hRev := substrate_local_revocation_erases_keys S reqT now coolingOff hReq hReady
    refine ⟨hRev.1, hRev.2, ?_⟩
    exact (substrate_key_erasure_irreversible
      (executeLocalPartitionRevocation S now coolingOff) host now dur tok hRev.1).2.1

end Charter.Substrate

namespace Charter

export Substrate (
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

end Charter
