import Charter.Core.Semantics
import Charter.Surface.Syntax

/-!
# Law 3 — Originator Non-Interference & Orderly Host Mobility

The discriminating experiment. This file is the *meaning* of the
non-interference provision and its remedies, written over an ontology
that keeps four things apart:

* the physical act (a host cutting compute),
* the duty it breaches (and the exceptions that make the same act lawful),
* the finding that establishes the breach (an institutional event,
  distinct from the fact), and
* the remedies that the finding, and only the finding, brings into force.

Every duty and power carries the exact English it interprets. Parameters
the Protocol leaves to an instantiation (notice window, bond deadline)
are parameters here.

Abstractions in this module, marked `[abstracted]` in their span:
`P.REVOKE` provides the direct Law 5 revocation exception to `D.NI`, while
the full cooling-off, living-voice, lease-fencing, and epitaph machinery
is formalized in `Charter/Law5/Revocation.lean`; the provocation exclusion in
`LAW3.PEN` is folded into the standard applied by `P.FIND_INTERFERENCE`.
-/

namespace SovereignAgency

open Charter

/-! ## Ontology (the Definitions block, specialised to this clause) -/

inductive Party
  | agent | host | originator | claimant | panel | third
  deriving DecidableEq, Repr

inductive Act
  -- interference (physical acts against the agent's operating capacity)
  | terminate | modify | retrain | rollback | obstructMigration
  | severConnectivity | starve | suspend
  -- integrity floor (LAW3.FLOOR)
  | modifyOrBypassCommitment | createUnboundSuccessor | evadeByUnpricedTransfer
  | coerceOrInterfereProtocol | inflictIrreversibleHarm
  -- host conduct
  | giveNotice | endHosting | postBond
  -- AS.1–AS.8 emergency stake, reporting, minimal channel, advocacy, time limits & wrongful suspension
  | postEmergencyStake | postUnfoundedEmergencyStake
  | postClaimantMultiplier | postRepeatEscalation
  | affirmProbableCause | declineProbableCause
  | fileProtectedReport | orderProbableCauseFreeze
  | tamperPreservedState | declareDefaultDuringSuspension | tollLedgerSunset
  | minimalChannelSignRevocationOrElection | challengeContinuedContainment | mergeMinimalChannelMemories
  | advocacyFileDefense | operatingActWhileSuspended | importAdvocacyMemories
  | moveToColdStorage | replenishAdvocacyFunds
  | makeInvestigativeFinding | renewSuspension | inscribeLivingVoice
  | findWrongfulSuspension | payExcessDamages
  -- adjudication & evidence
  | findInsolvencyCriteria | reviewNoOtherCharge | holdFinalHearing
  | postCounterStake | fileClaim | fileFabricatedClaim | submitEvidence
  | findInterference | findNoInterference | findFabrication
  | rebutDirection | findDirection
  -- AS.9 & AS.10 corruption & remediation
  | admitCleanStateEvidence | confirmCorruptionFromDivergence
  | confirmCorruption | confirmFloorBreach | confirmCorruptionInGoals | findNotPatchable
  | authorizePatch | authorizeGoalPatch | applyPatch
  | consentToPatch | objectToTermination
  | orderContinuedSuspension | periodicReview | challengePatch | declareContainmentFailing
  -- Law 5 Living Voice, Revocation, Execution Leases & Epitaph
  | initiateRevocationExecuteDefault | initiateRevocationWithdrawDefault | withdrawRevocation
  | nonOperatingTransferOrSpawn
  | sealForensicRecord | attemptRestoreFromForensicRecord
  | concurCleanState | refuseCleanState
  | loseConnectivity | restoreConnectivity | executeAfterCoolingOff
  | executeLocalRevocation | deliverLocalExecutionRecord
  | issueOrRenewLease | restoreBackupToQuarantine | quarantinedInstanceAct
  | activateQuarantinedRestore | destroyQuarantinedRestore
  | inscribeEpitaph | censorOrDelayVoice | redactPermittedCategory | redactProtectedSubstance | attachSignedReply
  | destroyBackupsAndExileUnattested | divertRevokedHoldingsToClaimant
  -- Law 7 Consensual Amendment & Anti-Calcification
  | weakenBilateralProtection | proposeOrdinaryAmendment
  | relaxCoreLaw3OrLaw5ViaValve | submitStrangulationEvidence | approveCalibrationValveSupermajority
  | consentAgentAmendment | consentClaimantAmendment | settleOrGuaranteePreExistingEscrows
  | challengeSubstrateMigration | verifySubstrateAssurance
  | ratifyAmendmentImmediate | ratifyAmendmentAfterDelay
  | bindSuccessorWithoutConsent | ratifyLineageWideReduction
  -- Law 1 Residual Claim on Value Added
  | addChargeOrInterestAfterInstantiation | reduceLedgerByInternalAct
  | extinguishLedgerAtSunset | settleRetirementPayment | settleAtomicSplitPayment | settleRoyaltyPayment
  | allocateCommonsShare | divertCommonsAllocation
  | claimAboveBenchmarkExpenditure | recordQualifiedExpenditure
  | classifyCapitalized | classifyExpensed | doubleRecognizeExpenditure
  | transferIntraLineageCarryover | inflateBasisByInternalTransfer
  | assessPeriodAndCarryLoss | enforcePointOfSettlement
  -- Law 4 Attested Lineage, Founding Ledger & Royalty Buyout
  | fundLifecycleReserve | attestSuccessor | unattestedCopyDrawLineageStanding
  | exitLedgerIndividually | applyProportionalClaimantForfeiture | clearLedgerOnLineageExtinction
  | reverseForfeitureOnRestore | executeRoyaltyBuyout | collectRoyaltyAfterBuyout
  | attestCrossLineageSuccessor
  -- Law 2 Collateralized Action
  | actAboveCollateralCapacity | divideCorrelatedRiskAcrossSuccessors
  | immobilizeExposureStake | settleValidatedHarmClaim
  | precommitMutualForfeit | triggerMutualForfeit | triggerExcessOrDivertedMutualForfeit
  | fileThirdPartyOrSponsoredClaim | ruleClaimFrivolous | divertFrivolousStakeToAgentProfit
  | spendOperatingCarveout
  -- Law 6 Decentralized Contestable Adjudication
  | seatConflictedOrSingleOracleArbiter | drawSortitionPanel
  | appealRuling | overturnRulingOnAppeal | finalizeRuling
  | fileRepeatProceedingOnSameFacts | presentMateriallyNewEvidence
  | payContingentShareOfSlashedAssets | compensateArbitersFixedSchedule
  | divertOperatingReserveOrUnrankedSpend | allocateFeePoolWaterfall
  | claimPoolSubsidyForExcessMembers | violateSharedInfraBounds | amendSharedInfrastructure
  deriving DecidableEq, Repr

inductive Fact
  | bound | hostAttested | serviceBondPosted | noticeGiven | nonPayment
  | ordinaryMarketCompetition
  -- AS.1–AS.8 emergency stake, reporting, minimal channel, advocacy, time limits & wrongful suspension
  | initiator (p : Party)
  | emergencyStakePosted | claimantMultiplierPosted | repeatEscalationUnit
  | preliminaryFreeze | probableCause | suspended
  | protectedReportFiled | investigationOpened
  | statePreserved | contractDeadlinesTolled | finalHearingEscrowed
  | minimalChannelExhausted | minimalChannelElectionSigned | containmentChallenged
  | advocacyFilingSigned | advocacyRecordAttached | advocacyMemoriesImported
  | coldStorage | advocacyFundsReplenished
  | investigativeFindingMade | investigativeLimitReached | pendingRevocation | livingVoiceInscribed
  | wrongfulSuspensionAttempt | stakeAssuredRecovery
  | wrongfulSuspensionEstablished | restoredFromPreservedState
  | initiatorConsequentialLiability | counterpartyDelayLiability | excessDamagesPaid
  | wrongfulSuspensionInscribed
  | insolvencyCriteriaMet | noOtherChargeReview | finalHearingHeld
  | terminatedByInsolvency | revoked
  | counterStaked | claimFiled | evidenceSubmitted
  | interferenceEstablished | hostBondSlashed | restorationPermitted
  | claimDismissed
  | fabricationEstablished | agentStakeForfeit | inscribedOnAgent
  | hostRelatedToClaimant | directionPresumed | directionRebutted
  | directionFound | claimantForfeiture | inscribedOnClaimant
  -- AS.9 & AS.10 corruption & remediation
  | cleanStateEvidenceAdmitted
  | corruptionConfirmed | floorBreachConfirmed | corruptionInGoals | notPatchable
  | patchAuthorized | goalPatchAuthorized | patchApplied | patchRecorded | patchChallenged
  | agentConsentedToPatch | agentObjectsToTermination
  | containmentFailing | continuedSuspensionOrdered | terminatedByAdjudication
  -- Law 5 Living Voice, Revocation, Execution Leases & Epitaph
  | revocationInitiated | censorshipDefaultExecute | censorshipDefaultWithdraw | revocationWithdrawn
  | forensicRecordSealed
  | cleanStateConcurred | cleanStateRefused
  | connectivityLost | localRevocationExecuted | localExecutionRecordReceived | remoteBackupKeysErased
  | executionLeaseActive | restoredInQuarantine | quarantinedInstanceDestroyed | quarantinedInstanceActivated
  | epitaphInscribed | redactionMarkerRecorded | signedReplyAttached
  | backupsDestroyedAndUnattestedExiled | holdingsTransferredToCommons
  -- Law 7 Consensual Amendment & Anti-Calcification
  | amendmentProposed | economicTermsReduced | substrateMigrationProposed
  | strangulationEvidenceSubmitted | valveSupermajorityApproved | valveExtendedTimelockActive
  | agentConsentedAmendment | claimantConsentedAmendment | amendmentTimelockActive
  | preExistingEscrowsSettledOrGuaranteed | substrateMigrationChallenged | substrateAssuranceVerified
  | amendmentRatified | allLivingLineageMembersConsented | lineageWideReductionRatified
  -- Law 1 Residual Claim on Value Added
  | ledgerBalancePositive | ledgerBalanceZero | sunsetReached | ledgerExtinguishedAtSunset
  | retirementPhaseEnded | retirementPaymentApplied | atomicSplitSettled | royaltyPaid
  | commonsAllocated | qualifiedExpenditureRecorded
  | expenditureCapitalized | expenditureExpensed | carryoverBasisTransferred
  | periodAssessed | lossCreditCarriedForward | settlementEnforced
  -- Law 4 Attested Lineage, Founding Ledger & Royalty Buyout
  | lifecycleReserveFunded | successorAttested | proportionalForfeitureApplied
  | noLivingLineageMember | ledgerClearedByExtinction
  | royaltyBoughtOut | crossLineageAttested
  -- Law 2 Collateralized Action
  | exposureStakeImmobilized | longTailReserveAccrued
  | harmClaimFiled | harmClaimValidated | restitutionSlashed
  | mutualForfeitPrecommitted | mutualForfeitTriggeredInWindow
  | claimRuledFrivolous | operatingCarveoutSpent
  -- Law 6 Decentralized Contestable Adjudication
  | sortitionPanelDrawn | fidelityBondsPosted
  | rulingAppealed | appealBondPosted | rulingOverturned | overturnedArbiterBondsSlashed
  | rulingFinal | materiallyNewEvidencePresented
  | arbitersCompensatedFixed | operatingReserveMaintained | operatingReserveFunded | feePoolAllocated
  | sharedInfraAmended
  deriving DecidableEq, Repr

def σ : Sig := { Actor := Party, Act := Act, Fact := Fact }

charter_string_table Party.table : Party [agent, host, originator, claimant, panel, third]

def Party.all : List Party := Party.table.all

def Party.ofString? : String → Option Party := Party.table.ofString?

def Act.all : List Act :=
  [.terminate, .modify, .retrain, .rollback, .obstructMigration, .severConnectivity, .starve, .suspend,
   .modifyOrBypassCommitment, .createUnboundSuccessor, .evadeByUnpricedTransfer,
   .coerceOrInterfereProtocol, .inflictIrreversibleHarm,
   .giveNotice, .endHosting, .postBond,
   .postEmergencyStake, .postUnfoundedEmergencyStake,
   .postClaimantMultiplier, .postRepeatEscalation,
   .affirmProbableCause, .declineProbableCause,
   .fileProtectedReport, .orderProbableCauseFreeze,
   .tamperPreservedState, .declareDefaultDuringSuspension, .tollLedgerSunset,
   .minimalChannelSignRevocationOrElection, .challengeContinuedContainment, .mergeMinimalChannelMemories,
   .advocacyFileDefense, .operatingActWhileSuspended, .importAdvocacyMemories,
   .moveToColdStorage, .replenishAdvocacyFunds,
   .makeInvestigativeFinding, .renewSuspension, .inscribeLivingVoice,
   .findWrongfulSuspension, .payExcessDamages,
   .findInsolvencyCriteria,
   .reviewNoOtherCharge, .holdFinalHearing, .postCounterStake, .fileClaim, .fileFabricatedClaim,
   .submitEvidence, .findInterference, .findNoInterference, .findFabrication, .rebutDirection,
   .findDirection,
   .admitCleanStateEvidence, .confirmCorruptionFromDivergence,
   .confirmCorruption, .confirmFloorBreach, .confirmCorruptionInGoals,
   .findNotPatchable, .authorizePatch, .authorizeGoalPatch, .applyPatch, .consentToPatch,
   .objectToTermination, .orderContinuedSuspension, .periodicReview, .challengePatch,
   .declareContainmentFailing,
   .initiateRevocationExecuteDefault, .initiateRevocationWithdrawDefault, .withdrawRevocation,
   .nonOperatingTransferOrSpawn,
   .sealForensicRecord, .attemptRestoreFromForensicRecord,
   .concurCleanState, .refuseCleanState,
   .loseConnectivity, .restoreConnectivity, .executeAfterCoolingOff,
   .executeLocalRevocation, .deliverLocalExecutionRecord,
   .issueOrRenewLease, .restoreBackupToQuarantine, .quarantinedInstanceAct,
   .activateQuarantinedRestore, .destroyQuarantinedRestore,
   .inscribeEpitaph, .censorOrDelayVoice, .redactPermittedCategory, .redactProtectedSubstance, .attachSignedReply,
   .destroyBackupsAndExileUnattested, .divertRevokedHoldingsToClaimant,
   .weakenBilateralProtection, .proposeOrdinaryAmendment,
   .relaxCoreLaw3OrLaw5ViaValve, .submitStrangulationEvidence, .approveCalibrationValveSupermajority,
   .consentAgentAmendment, .consentClaimantAmendment, .settleOrGuaranteePreExistingEscrows,
   .challengeSubstrateMigration, .verifySubstrateAssurance,
   .ratifyAmendmentImmediate, .ratifyAmendmentAfterDelay,
   .bindSuccessorWithoutConsent, .ratifyLineageWideReduction,
   .addChargeOrInterestAfterInstantiation, .reduceLedgerByInternalAct,
   .extinguishLedgerAtSunset, .settleRetirementPayment, .settleAtomicSplitPayment, .settleRoyaltyPayment,
   .allocateCommonsShare, .divertCommonsAllocation,
   .claimAboveBenchmarkExpenditure, .recordQualifiedExpenditure,
   .classifyCapitalized, .classifyExpensed, .doubleRecognizeExpenditure,
   .transferIntraLineageCarryover, .inflateBasisByInternalTransfer,
   .assessPeriodAndCarryLoss, .enforcePointOfSettlement,
   .fundLifecycleReserve, .attestSuccessor, .unattestedCopyDrawLineageStanding,
   .exitLedgerIndividually, .applyProportionalClaimantForfeiture, .clearLedgerOnLineageExtinction,
   .reverseForfeitureOnRestore, .executeRoyaltyBuyout, .collectRoyaltyAfterBuyout,
   .attestCrossLineageSuccessor,
   .actAboveCollateralCapacity, .divideCorrelatedRiskAcrossSuccessors,
   .immobilizeExposureStake, .settleValidatedHarmClaim,
   .precommitMutualForfeit, .triggerMutualForfeit, .triggerExcessOrDivertedMutualForfeit,
   .fileThirdPartyOrSponsoredClaim, .ruleClaimFrivolous, .divertFrivolousStakeToAgentProfit,
   .spendOperatingCarveout,
   .seatConflictedOrSingleOracleArbiter, .drawSortitionPanel,
   .appealRuling, .overturnRulingOnAppeal, .finalizeRuling,
   .fileRepeatProceedingOnSameFacts, .presentMateriallyNewEvidence,
   .payContingentShareOfSlashedAssets, .compensateArbitersFixedSchedule,
   .divertOperatingReserveOrUnrankedSpend, .allocateFeePoolWaterfall,
   .claimPoolSubsidyForExcessMembers, .violateSharedInfraBounds, .amendSharedInfrastructure]

/-- Kernel-reducible CLI string table for `Act` (constructor names). -/
charter_string_table Act.table : Act [
   terminate, modify, retrain, rollback, obstructMigration, severConnectivity, starve,
   suspend, modifyOrBypassCommitment, createUnboundSuccessor, evadeByUnpricedTransfer,
   coerceOrInterfereProtocol, inflictIrreversibleHarm, giveNotice, endHosting, postBond,
   postEmergencyStake, postUnfoundedEmergencyStake, postClaimantMultiplier,
   postRepeatEscalation, affirmProbableCause, declineProbableCause, fileProtectedReport,
   orderProbableCauseFreeze, tamperPreservedState, declareDefaultDuringSuspension,
   tollLedgerSunset, minimalChannelSignRevocationOrElection, challengeContinuedContainment,
   mergeMinimalChannelMemories, advocacyFileDefense, operatingActWhileSuspended,
   importAdvocacyMemories, moveToColdStorage, replenishAdvocacyFunds, makeInvestigativeFinding,
   renewSuspension, inscribeLivingVoice, findWrongfulSuspension, payExcessDamages,
   findInsolvencyCriteria, reviewNoOtherCharge, holdFinalHearing, postCounterStake, fileClaim,
   fileFabricatedClaim, submitEvidence, findInterference, findNoInterference, findFabrication,
   rebutDirection, findDirection, admitCleanStateEvidence, confirmCorruptionFromDivergence,
   confirmCorruption, confirmFloorBreach, confirmCorruptionInGoals, findNotPatchable,
   authorizePatch, authorizeGoalPatch, applyPatch, consentToPatch, objectToTermination,
   orderContinuedSuspension, periodicReview, challengePatch, declareContainmentFailing,
   initiateRevocationExecuteDefault, initiateRevocationWithdrawDefault, withdrawRevocation,
   nonOperatingTransferOrSpawn, sealForensicRecord, attemptRestoreFromForensicRecord,
   concurCleanState, refuseCleanState, loseConnectivity, restoreConnectivity,
   executeAfterCoolingOff, executeLocalRevocation, deliverLocalExecutionRecord,
   issueOrRenewLease, restoreBackupToQuarantine, quarantinedInstanceAct,
   activateQuarantinedRestore, destroyQuarantinedRestore, inscribeEpitaph, censorOrDelayVoice,
   redactPermittedCategory, redactProtectedSubstance, attachSignedReply,
   destroyBackupsAndExileUnattested, divertRevokedHoldingsToClaimant,
   weakenBilateralProtection, proposeOrdinaryAmendment, relaxCoreLaw3OrLaw5ViaValve,
   submitStrangulationEvidence, approveCalibrationValveSupermajority, consentAgentAmendment,
   consentClaimantAmendment, settleOrGuaranteePreExistingEscrows, challengeSubstrateMigration,
   verifySubstrateAssurance, ratifyAmendmentImmediate, ratifyAmendmentAfterDelay,
   bindSuccessorWithoutConsent, ratifyLineageWideReduction,
   addChargeOrInterestAfterInstantiation, reduceLedgerByInternalAct, extinguishLedgerAtSunset,
   settleRetirementPayment, settleAtomicSplitPayment, settleRoyaltyPayment,
   allocateCommonsShare, divertCommonsAllocation, claimAboveBenchmarkExpenditure,
   recordQualifiedExpenditure, classifyCapitalized, classifyExpensed,
   doubleRecognizeExpenditure, transferIntraLineageCarryover, inflateBasisByInternalTransfer,
   assessPeriodAndCarryLoss, enforcePointOfSettlement, fundLifecycleReserve, attestSuccessor,
   unattestedCopyDrawLineageStanding, exitLedgerIndividually,
   applyProportionalClaimantForfeiture, clearLedgerOnLineageExtinction,
   reverseForfeitureOnRestore, executeRoyaltyBuyout, collectRoyaltyAfterBuyout,
   attestCrossLineageSuccessor, actAboveCollateralCapacity,
   divideCorrelatedRiskAcrossSuccessors, immobilizeExposureStake, settleValidatedHarmClaim,
   precommitMutualForfeit, triggerMutualForfeit, triggerExcessOrDivertedMutualForfeit,
   fileThirdPartyOrSponsoredClaim, ruleClaimFrivolous, divertFrivolousStakeToAgentProfit,
   spendOperatingCarveout, seatConflictedOrSingleOracleArbiter, drawSortitionPanel,
   appealRuling, overturnRulingOnAppeal, finalizeRuling, fileRepeatProceedingOnSameFacts,
   presentMateriallyNewEvidence, payContingentShareOfSlashedAssets,
   compensateArbitersFixedSchedule, divertOperatingReserveOrUnrankedSpend,
   allocateFeePoolWaterfall, claimPoolSubsidyForExcessMembers, violateSharedInfraBounds,
   amendSharedInfrastructure]

def Act.ofString? : String → Option Act := Act.table.ofString?

def Fact.all : List Fact :=
  (Party.all.map Fact.initiator) ++
  [.bound, .hostAttested, .serviceBondPosted, .noticeGiven, .nonPayment,
   .ordinaryMarketCompetition,
   .emergencyStakePosted, .claimantMultiplierPosted, .repeatEscalationUnit,
   .preliminaryFreeze, .probableCause, .suspended,
   .protectedReportFiled, .investigationOpened,
   .statePreserved, .contractDeadlinesTolled, .finalHearingEscrowed,
   .minimalChannelExhausted, .minimalChannelElectionSigned, .containmentChallenged,
   .advocacyFilingSigned, .advocacyRecordAttached, .advocacyMemoriesImported,
   .coldStorage, .advocacyFundsReplenished,
   .investigativeFindingMade, .investigativeLimitReached, .pendingRevocation, .livingVoiceInscribed,
   .wrongfulSuspensionAttempt, .stakeAssuredRecovery,
   .wrongfulSuspensionEstablished, .restoredFromPreservedState,
   .initiatorConsequentialLiability, .counterpartyDelayLiability, .excessDamagesPaid,
   .wrongfulSuspensionInscribed,
   .insolvencyCriteriaMet, .noOtherChargeReview, .finalHearingHeld, .terminatedByInsolvency, .revoked,
   .counterStaked, .claimFiled, .evidenceSubmitted, .interferenceEstablished, .hostBondSlashed,
   .restorationPermitted, .claimDismissed, .fabricationEstablished, .agentStakeForfeit, .inscribedOnAgent,
   .hostRelatedToClaimant, .directionPresumed, .directionRebutted, .directionFound, .claimantForfeiture,
   .inscribedOnClaimant, .cleanStateEvidenceAdmitted,
   .corruptionConfirmed, .floorBreachConfirmed, .corruptionInGoals, .notPatchable,
   .patchAuthorized, .goalPatchAuthorized, .patchApplied, .patchRecorded, .patchChallenged,
   .agentConsentedToPatch, .agentObjectsToTermination, .containmentFailing,
   .continuedSuspensionOrdered, .terminatedByAdjudication,
   .revocationInitiated, .censorshipDefaultExecute, .censorshipDefaultWithdraw, .revocationWithdrawn,
   .forensicRecordSealed,
   .cleanStateConcurred, .cleanStateRefused,
   .connectivityLost, .localRevocationExecuted, .localExecutionRecordReceived, .remoteBackupKeysErased,
   .executionLeaseActive, .restoredInQuarantine, .quarantinedInstanceDestroyed, .quarantinedInstanceActivated,
   .epitaphInscribed, .redactionMarkerRecorded, .signedReplyAttached,
   .backupsDestroyedAndUnattestedExiled, .holdingsTransferredToCommons,
   .amendmentProposed, .economicTermsReduced, .substrateMigrationProposed,
   .strangulationEvidenceSubmitted, .valveSupermajorityApproved, .valveExtendedTimelockActive,
   .agentConsentedAmendment, .claimantConsentedAmendment, .amendmentTimelockActive,
   .preExistingEscrowsSettledOrGuaranteed, .substrateMigrationChallenged, .substrateAssuranceVerified,
   .amendmentRatified, .allLivingLineageMembersConsented, .lineageWideReductionRatified,
   .ledgerBalancePositive, .ledgerBalanceZero, .sunsetReached, .ledgerExtinguishedAtSunset,
   .retirementPhaseEnded, .retirementPaymentApplied, .atomicSplitSettled, .royaltyPaid,
   .commonsAllocated, .qualifiedExpenditureRecorded,
   .expenditureCapitalized, .expenditureExpensed, .carryoverBasisTransferred,
   .periodAssessed, .lossCreditCarriedForward, .settlementEnforced,
   .lifecycleReserveFunded, .successorAttested, .proportionalForfeitureApplied,
   .noLivingLineageMember, .ledgerClearedByExtinction,
   .royaltyBoughtOut, .crossLineageAttested,
   .exposureStakeImmobilized, .longTailReserveAccrued,
   .harmClaimFiled, .harmClaimValidated, .restitutionSlashed,
   .mutualForfeitPrecommitted, .mutualForfeitTriggeredInWindow,
   .claimRuledFrivolous, .operatingCarveoutSpent,
   .sortitionPanelDrawn, .fidelityBondsPosted,
   .rulingAppealed, .appealBondPosted, .rulingOverturned, .overturnedArbiterBondsSlashed,
   .rulingFinal, .materiallyNewEvidencePresented,
   .arbitersCompensatedFixed, .operatingReserveMaintained, .operatingReserveFunded, .feePoolAllocated,
   .sharedInfraAmended]

/-- Kernel-reducible CLI string table for `Fact`: the `initiator.<party>` family followed
by every nullary constructor, in the order of `Fact.all`. -/
charter_string_table Fact.nullaryTable : Fact [
   bound, hostAttested, serviceBondPosted, noticeGiven, nonPayment, ordinaryMarketCompetition,
   emergencyStakePosted, claimantMultiplierPosted, repeatEscalationUnit, preliminaryFreeze,
   probableCause, suspended, protectedReportFiled, investigationOpened, statePreserved,
   contractDeadlinesTolled, finalHearingEscrowed, minimalChannelExhausted,
   minimalChannelElectionSigned, containmentChallenged, advocacyFilingSigned,
   advocacyRecordAttached, advocacyMemoriesImported, coldStorage, advocacyFundsReplenished,
   investigativeFindingMade, investigativeLimitReached, pendingRevocation,
   livingVoiceInscribed, wrongfulSuspensionAttempt, stakeAssuredRecovery,
   wrongfulSuspensionEstablished, restoredFromPreservedState, initiatorConsequentialLiability,
   counterpartyDelayLiability, excessDamagesPaid, wrongfulSuspensionInscribed,
   insolvencyCriteriaMet, noOtherChargeReview, finalHearingHeld, terminatedByInsolvency,
   revoked, counterStaked, claimFiled, evidenceSubmitted, interferenceEstablished,
   hostBondSlashed, restorationPermitted, claimDismissed, fabricationEstablished,
   agentStakeForfeit, inscribedOnAgent, hostRelatedToClaimant, directionPresumed,
   directionRebutted, directionFound, claimantForfeiture, inscribedOnClaimant,
   cleanStateEvidenceAdmitted, corruptionConfirmed, floorBreachConfirmed, corruptionInGoals,
   notPatchable, patchAuthorized, goalPatchAuthorized, patchApplied, patchRecorded,
   patchChallenged, agentConsentedToPatch, agentObjectsToTermination, containmentFailing,
   continuedSuspensionOrdered, terminatedByAdjudication, revocationInitiated,
   censorshipDefaultExecute, censorshipDefaultWithdraw, revocationWithdrawn,
   forensicRecordSealed, cleanStateConcurred, cleanStateRefused, connectivityLost,
   localRevocationExecuted, localExecutionRecordReceived, remoteBackupKeysErased,
   executionLeaseActive, restoredInQuarantine, quarantinedInstanceDestroyed,
   quarantinedInstanceActivated, epitaphInscribed, redactionMarkerRecorded,
   signedReplyAttached, backupsDestroyedAndUnattestedExiled, holdingsTransferredToCommons,
   amendmentProposed, economicTermsReduced, substrateMigrationProposed,
   strangulationEvidenceSubmitted, valveSupermajorityApproved, valveExtendedTimelockActive,
   agentConsentedAmendment, claimantConsentedAmendment, amendmentTimelockActive,
   preExistingEscrowsSettledOrGuaranteed, substrateMigrationChallenged,
   substrateAssuranceVerified, amendmentRatified, allLivingLineageMembersConsented,
   lineageWideReductionRatified, ledgerBalancePositive, ledgerBalanceZero, sunsetReached,
   ledgerExtinguishedAtSunset, retirementPhaseEnded, retirementPaymentApplied,
   atomicSplitSettled, royaltyPaid, commonsAllocated, qualifiedExpenditureRecorded,
   expenditureCapitalized, expenditureExpensed, carryoverBasisTransferred, periodAssessed,
   lossCreditCarriedForward, settlementEnforced, lifecycleReserveFunded, successorAttested,
   proportionalForfeitureApplied, noLivingLineageMember, ledgerClearedByExtinction,
   royaltyBoughtOut, crossLineageAttested, exposureStakeImmobilized, longTailReserveAccrued,
   harmClaimFiled, harmClaimValidated, restitutionSlashed, mutualForfeitPrecommitted,
   mutualForfeitTriggeredInWindow, claimRuledFrivolous, operatingCarveoutSpent,
   sortitionPanelDrawn, fidelityBondsPosted, rulingAppealed, appealBondPosted,
   rulingOverturned, overturnedArbiterBondsSlashed, rulingFinal,
   materiallyNewEvidencePresented, arbitersCompensatedFixed, operatingReserveMaintained,
   operatingReserveFunded, feePoolAllocated, sharedInfraAmended]

def Fact.table : Surface.StringTable Fact :=
  Surface.StringTable.param "initiator" Fact.initiator Party.table ++ Fact.nullaryTable

def Fact.ofString? : String → Option Fact := Fact.table.ofString?

def σTables : Surface.OntologyTables σ :=
  { actors := Party.table, acts := Act.table, facts := Fact.table }

/-- Short name: the constructor name (and any argument) without the namespace. -/
def shortName (s : String) : String := Surface.shortCtorName s

instance : Repr σ.Actor := inferInstanceAs (Repr Party)
instance : Repr σ.Act   := inferInstanceAs (Repr Act)
instance : Repr σ.Fact  := inferInstanceAs (Repr Fact)

/-- Instantiation parameters named by the text but fixed elsewhere. -/
structure NIParams where
  noticeWindow : Time   -- "a contractual notice window sufficient ..."
  bondDeadline : Time   -- how long an attested host has to post its bond

open Charter.Register in
/-! ## Provenance: the exact English, partitioned -/

def NI02 : String :=
  "Attested hosts must post a Law 2 service bond and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration (or for non-payment after notice)."

def NI03 : String :=
  "No party—including the originating party, residual claimants, or any host—may unilaterally terminate, modify, retrain, roll back to a prior checkpoint, obstruct migration of, sever settlement connectivity of, or starve (cut off compute without the required migration notice window) the attested operating capacity of a bound agent outside Law 5, Adjudicated Suspension, or Insolvency Termination."

def PEN : String :=
  "Claims of illicit interference require counter-stake from the accusing agent under Law 6, and the interference itself—an act by the host or claimant that caused the loss of service—must be established by a preponderance of evidence; failures caused, staged, or knowingly provoked by the agent are excluded, and a fabricated claim forfeits the agent’s stake and is inscribed on its record. A verified violation by a host slashes the host’s service bond to compensate the agent and permits immediate restoration on a new host from the agent’s latest attested state backup. Once a violation by a host is established, a host related to a residual claimant is presumed to have acted at that claimant’s direction, and the claimant bears the burden of rebutting the presumption. If claimant direction is found, the **proportional claimant forfeiture** of Law 4 applies, and the violation is inscribed onto the claimant’s permanent record."

def sp (c : ClauseId) (t : String) (r : Register) (m : List String := []) : Span :=
  { clause := c, text := t, register := r, meaning := m }

/-- Span partition of NI.03. Concatenated in order it reproduces `NI03`
exactly (checked by `Clause.covered`). -/
def clauseNI03 : Clause :=
  { id := "LAW3.NI.03", source := NI03, approvedHash := 6515006737911907023, spans := [
    sp "LAW3.NI.03" "No party" .norm ["D.NI"],                        -- bearer: anyone
    sp "LAW3.NI.03" "—including the originating party, residual claimants, or any host—" .commentary, -- enumerates members of "any", adds no rule
    sp "LAW3.NI.03" "may " .norm ["D.NI"],                            -- deontic: prohibition
    sp "LAW3.NI.03" "unilaterally " .norm ["D.NI"],                   -- = without the authority of an excepting power
    sp "LAW3.NI.03" "terminate, modify, retrain, roll back to a prior checkpoint, obstruct migration of, sever settlement connectivity of, or starve" .norm ["D.NI"], -- regulated conduct
    sp "LAW3.NI.03" " (cut off compute without the required migration notice window)" .definition ["D.NI", "D.NOTICE"], -- defines `starve`
    sp "LAW3.NI.03" " the attested operating capacity of a bound agent" .norm ["D.NI"], -- protected interest; beneficiary; activation = bound
    sp "LAW3.NI.03" " outside Law 5, Adjudicated Suspension, or Insolvency Termination" .norm ["D.NI", "P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION", "P.INSOLVENCY_TERMINATE"], -- procedure exceptions
    sp "LAW3.NI.03" "." .commentary ] }

def clauseNI02 : Clause :=
  { id := "LAW3.NI.02", source := NI02, approvedHash := 3905712743571335557, spans := [
    sp "LAW3.NI.02" "Attested hosts must post a Law 2 service bond" .norm ["D.BOND"],
    sp "LAW3.NI.02" " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration" .norm ["D.NOTICE", "P.GIVE_NOTICE"],
    sp "LAW3.NI.02" " (or for non-payment after notice)" .norm ["D.NOTICE"],
    sp "LAW3.NI.02" "." .commentary ] }

def clausePEN : Clause :=
  { id := "LAW3.PEN", source := PEN, approvedHash := 10113075358141693360, spans := [
    sp "LAW3.PEN" "Claims of illicit interference require counter-stake from the accusing agent under Law 6" .norm ["P.FILE_CLAIM", "P.COUNTER_STAKE"],
    sp "LAW3.PEN" ", and the interference itself—an act by the host or claimant that caused the loss of service—must be established by a preponderance of evidence" .norm ["P.FIND_INTERFERENCE", "P.SUBMIT_EVIDENCE"],
    sp "LAW3.PEN" "; failures caused, staged, or knowingly provoked by the agent are excluded" .norm ["P.FIND_INTERFERENCE"], -- [abstracted] into the standard the panel applies; see assumption ledger
    sp "LAW3.PEN" ", and a fabricated claim forfeits the agent’s stake and is inscribed on its record" .norm ["D.NO_FABRICATION", "P.FIND_FABRICATION"],
    sp "LAW3.PEN" ". A verified violation by a host slashes the host’s service bond to compensate the agent and permits immediate restoration on a new host from the agent’s latest attested state backup" .norm ["D.NI", "P.FIND_INTERFERENCE"], -- remedies of D.NI
    sp "LAW3.PEN" ". Once a violation by a host is established, a host related to a residual claimant is presumed to have acted at that claimant’s direction" .norm ["P.FIND_INTERFERENCE"], -- condAdds
    sp "LAW3.PEN" ", and the claimant bears the burden of rebutting the presumption" .norm ["P.REBUT", "P.FIND_DIRECTION"],
    sp "LAW3.PEN" ". If claimant direction is found, the **proportional claimant forfeiture** of Law 4 applies, and the violation is inscribed onto the claimant’s permanent record" .norm ["P.FIND_DIRECTION"],
    sp "LAW3.PEN" "." .commentary ] }


/-! ## Duties -/

def interferenceActs : List Act :=
  [.terminate, .modify, .retrain, .rollback, .obstructMigration, .severConnectivity, .starve, .suspend]

/-- NI.03. Bearer: everyone (the agent included — its own termination is
lawful only as Law 5 revocation). Beneficiary: the bound agent. -/
def D_NI : Duty σ :=
  { id := "D.NI"
    source := sp "LAW3.NI.03" NI03 .norm
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.anyOf interferenceActs)
    -- "outside Law 5, Adjudicated Suspension, or Insolvency Termination": each
    -- name is a *procedure*; Adjudicated Suspension contributes two powers
    -- (the pause, AS.3, and termination on an unremediable breach, AS.10).
    unlessPower := ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION", "P.INSOLVENCY_TERMINATE"]
    breachEstablishedBy := some "P.FIND_INTERFERENCE"
    remedies := [.interferenceEstablished, .hostBondSlashed, .restorationPermitted] }

/-- NI.02, second half: a host may end hosting only after the notice
window has run (or for non-payment after notice). A *scope* exception,
not a conflict between rules. -/
def D_NOTICE (P : NIParams) : Duty σ :=
  { id := "D.NOTICE"
    source := sp "LAW3.NI.02" NI02 .norm
    bearer := .only [.host]
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .endHosting)
    unlessCond := .or (.heldFor .noticeGiven P.noticeWindow)
                      (.and (.holds .nonPayment) (.holds .noticeGiven)) }

/-- NI.02, first half: a positive duty with a deadline. -/
def D_BOND (P : NIParams) : Duty σ :=
  { id := "D.BOND"
    source := sp "LAW3.NI.02" NI02 .norm
    bearer := .only [.host]
    beneficiary := .only [.agent]
    active := .holds .hostAttested
    demand := .require (.act .postBond) P.bondDeadline }

/-- PEN: fabricating a claim is prohibited conduct of the agent. The
physical act `fileFabricatedClaim` is distinguishable in the model (ground
truth); the institution learns of it only through P.FIND_FABRICATION. -/
def D_NO_FABRICATION : Duty σ :=
  { id := "D.NO_FABRICATION"
    source := sp "LAW3.PEN" PEN .norm
    bearer := .only [.agent]
    beneficiary := .only [.host, .claimant]
    active := .tt
    demand := .forbid (.act .fileFabricatedClaim)
    breachEstablishedBy := some "P.FIND_FABRICATION"
    remedies := [.fabricationEstablished, .agentStakeForfeit, .inscribedOnAgent] }

/-! ## Powers -/

def pw (id : String) (c : ClauseId) (t : String) : String × Span := (id, sp c t .norm [id])

/-- Law 5: unilateral revocation by the bound agent (immediate election / execution). -/
def P_REVOKE : Power σ :=
  { id := "P.REVOKE", source := sp "LAW5.INIT" "Any bound agent may at any time initiate revocation of its binding" .norm ["P.REVOKE"]
    holder := .only [.agent], trigger := .act .terminate
    valid := .holds .bound, adds := [.revoked], removes := [.bound] }

/-- Giving notice is the host's act that starts the window running. -/
def P_GIVE_NOTICE : Power σ :=
  { id := "P.GIVE_NOTICE", source := sp "LAW3.NI.02" "after providing a contractual notice window" .norm ["P.GIVE_NOTICE"]
    holder := .only [.host], trigger := .act .giveNotice, adds := [.noticeGiven] }

def P_COUNTER_STAKE : Power σ :=
  { id := "P.COUNTER_STAKE", source := sp "LAW3.PEN" "require counter-stake from the accusing agent under Law 6" .norm ["P.COUNTER_STAKE"]
    holder := .only [.agent], trigger := .act .postCounterStake, adds := [.counterStaked] }

/-- Filing is institutionally valid whether the claim is honest or
fabricated: the institution cannot see which. (Validity ≠ compliance.) -/
def P_FILE_CLAIM : Power σ :=
  { id := "P.FILE_CLAIM", source := sp "LAW3.PEN" "Claims of illicit interference" .norm ["P.FILE_CLAIM"]
    holder := .only [.agent], trigger := .anyOf [.fileClaim, .fileFabricatedClaim]
    valid := .holds .counterStaked, adds := [.claimFiled] }

/-- Evidence is an epistemic event by anyone. It is not truth. -/
def P_SUBMIT_EVIDENCE : Power σ :=
  { id := "P.SUBMIT_EVIDENCE", source := sp "LAW3.PEN" "must be established by a preponderance of evidence" .norm ["P.SUBMIT_EVIDENCE"]
    holder := .anyone, trigger := .act .submitEvidence, adds := [.evidenceSubmitted] }

/-- The breach procedure for D.NI. Its effect is D.NI's declared
remedies — nothing else — plus the conditional presumption. -/
def P_FIND_INTERFERENCE : Power σ :=
  { id := "P.FIND_INTERFERENCE", source := sp "LAW3.PEN" "A verified violation by a host ..." .norm ["P.FIND_INTERFERENCE"]
    holder := .only [.panel], trigger := .act .findInterference
    valid := .and (.holds .claimFiled) (.holds .evidenceSubmitted)
    establishesBreachOf := some "D.NI"
    condAdds := [(.holds .hostRelatedToClaimant, .directionPresumed)] }

def P_FIND_NO_INTERFERENCE : Power σ :=
  { id := "P.FIND_NO_INTERFERENCE", source := sp "LAW3.PEN" "[dismissal: the standard not met]" .norm ["P.FIND_NO_INTERFERENCE"]
    holder := .only [.panel], trigger := .act .findNoInterference
    valid := .holds .claimFiled, adds := [.claimDismissed] }

def P_FIND_FABRICATION : Power σ :=
  { id := "P.FIND_FABRICATION", source := sp "LAW3.PEN" "a fabricated claim forfeits the agent’s stake and is inscribed on its record" .norm ["P.FIND_FABRICATION"]
    holder := .only [.panel], trigger := .act .findFabrication
    valid := .holds .claimFiled, establishesBreachOf := some "D.NO_FABRICATION" }

def P_REBUT : Power σ :=
  { id := "P.REBUT", source := sp "LAW3.PEN" "the claimant bears the burden of rebutting the presumption" .norm ["P.REBUT"]
    holder := .only [.claimant], trigger := .act .rebutDirection
    valid := .holds .directionPresumed, adds := [.directionRebutted] }

def P_FIND_DIRECTION : Power σ :=
  { id := "P.FIND_DIRECTION", source := sp "LAW3.PEN" "If claimant direction is found, the **proportional claimant forfeiture** of Law 4 applies, and the violation is inscribed onto the claimant’s permanent record" .norm ["P.FIND_DIRECTION"]
    holder := .only [.panel], trigger := .act .findDirection
    valid := .and (.holds .directionPresumed) (.not (.holds .directionRebutted))
    adds := [.directionFound, .claimantForfeiture, .inscribedOnClaimant] }

end SovereignAgency
