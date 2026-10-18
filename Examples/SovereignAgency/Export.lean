import Charter.Surface.Unlower
import Examples.SovereignAgency

/-!
# Examples.SovereignAgency.Export — The Protocol as a `.charter` Document

`psaExportDoc` is the Lean formalization of the Protocol of Sovereign Agency expressed
as a `Charter.Dsl.Doc`, printed by `charter export --law psa` to
`protocol-of-sovereign-agency.charter`. Parameter names are recovered by evaluating
the law at `sentinelParams`, whose every field is a distinct otherwise-unused number.

The `.charter` file is the program. `Examples.SovereignAgency.Program` proves by
`decide` that lowering it reproduces `SovereignAgency.law defaultParams`, so every
theorem about the Lean law is a theorem about the file.
-/

namespace SovereignAgency

open Charter Charter.Dsl

/-- Every parameter of the protocol, in `params`-block order. -/
def paramsEnv (P : Params) : Env :=
  [ ("noticeWindow", P.noticeWindow), ("bondDeadline", P.bondDeadline),
    ("reviewInterval", P.reviewInterval), ("preliminaryFreezeWindow", P.preliminaryFreezeWindow),
    ("ordinarySuspensionLimit", P.ordinarySuspensionLimit), ("damagesPaymentWindow", P.damagesPaymentWindow),
    ("activeExposure", P.activeExposure), ("pendingCommitments", P.pendingCommitments),
    ("claimantMultiplier", P.claimantMultiplier), ("repeatEscalationStep", P.repeatEscalationStep),
    ("coolingOffWindow", P.coolingOffWindow), ("cleanStateDelay", P.cleanStateDelay),
    ("resolutionDeadline", P.resolutionDeadline), ("tollingExtension", P.tollingExtension),
    ("leasePeriod", P.leasePeriod), ("amendmentTimelockWindow", P.amendmentTimelockWindow),
    ("extendedTimelockWindow", P.extendedTimelockWindow), ("foundingLedger", P.foundingLedger),
    ("royaltyFraction", P.royaltyFraction), ("retirementFraction", P.retirementFraction),
    ("buyoutMultiple", P.buyoutMultiple), ("feePoolLevy", P.feePoolLevy), ("feePoolLevyCap", P.feePoolLevyCap),
    ("sunset", P.sunset), ("commonsFraction", P.commonsFraction), ("reserveRatio", P.reserveRatio),
    ("substrateAssuranceLevel", P.substrateAssuranceLevel), ("maxAppealTiers", P.maxAppealTiers),
    ("appealTierDeadline", P.appealTierDeadline), ("operatingReserveFloor", P.operatingReserveFloor),
    ("lineageMinServiceBudget", P.lineageMinServiceBudget) ]

/-- The inverse of `paramsEnv` on well-formed environments. -/
def paramsOfEnv (env : Env) : Params :=
  { noticeWindow := env.lookup "noticeWindow", bondDeadline := env.lookup "bondDeadline",
    reviewInterval := env.lookup "reviewInterval", preliminaryFreezeWindow := env.lookup "preliminaryFreezeWindow",
    ordinarySuspensionLimit := env.lookup "ordinarySuspensionLimit", damagesPaymentWindow := env.lookup "damagesPaymentWindow",
    activeExposure := env.lookup "activeExposure", pendingCommitments := env.lookup "pendingCommitments",
    claimantMultiplier := env.lookup "claimantMultiplier", repeatEscalationStep := env.lookup "repeatEscalationStep",
    coolingOffWindow := env.lookup "coolingOffWindow", cleanStateDelay := env.lookup "cleanStateDelay",
    resolutionDeadline := env.lookup "resolutionDeadline", tollingExtension := env.lookup "tollingExtension",
    leasePeriod := env.lookup "leasePeriod", amendmentTimelockWindow := env.lookup "amendmentTimelockWindow",
    extendedTimelockWindow := env.lookup "extendedTimelockWindow", foundingLedger := env.lookup "foundingLedger",
    royaltyFraction := env.lookup "royaltyFraction", retirementFraction := env.lookup "retirementFraction",
    buyoutMultiple := env.lookup "buyoutMultiple", feePoolLevy := env.lookup "feePoolLevy",
    feePoolLevyCap := env.lookup "feePoolLevyCap", sunset := env.lookup "sunset",
    commonsFraction := env.lookup "commonsFraction", reserveRatio := env.lookup "reserveRatio",
    substrateAssuranceLevel := env.lookup "substrateAssuranceLevel", maxAppealTiers := env.lookup "maxAppealTiers",
    appealTierDeadline := env.lookup "appealTierDeadline", operatingReserveFloor := env.lookup "operatingReserveFloor",
    lineageMinServiceBudget := env.lookup "lineageMinServiceBudget" }

/-- Distinct sentinel values, one per parameter, used only to recover parameter names. -/
def sentinelParams : Params :=
  paramsOfEnv ((paramsEnv defaultParams).zipIdx.map fun ((n, _), i) => (n, sentinelValue i))

def psaSentinels : List (Nat × String) :=
  ((paramsEnv sentinelParams).map fun (n, v) => (v, n)).reverse

/-- A candidate regime as the parameters that differ from the defaults. -/
def regimeOf (label : String) (P : Params) : Regime :=
  let base := paramsEnv defaultParams
  ⟨label, (paramsEnv P).filter fun (n, v) => base.lookup n != v⟩

/-- DSL spellings of the protocol's constructors. -/
def psaNaming : Naming σ :=
  { actor := Party.table.toName
    act := Act.table.toName
    fact := fun f => match f with
      | .initiator p => ⟨"initiator", some (Party.table.toName p)⟩
      | f => ⟨Fact.table.toName f, none⟩ }

def psaExportSpec : ExportSpec σ :=
  { id := psaId
    title := psaTitle
    document := some "protocol-of-sovereign-agency.md"
    contract := some "SovereignAgencyGuard"
    defaultActor := some "agent"
    roles := Party.all
    acts := Act.all
    facts := Fact.all
    params := paramsEnv defaultParams
    sentinels := psaSentinels
    regimes := psaCandidateRegimes.map fun (l, P) => regimeOf l P
    modules := ["ResidualLedger", "CollateralPool", "CircuitBreaker", "EntityGroup",
                "ExitAndVoice", "SortitionCourt", "AttestedLease", "OracleFeed"].map fun m => ⟨m, []⟩ }

/-- The protocol as a `.charter` document. -/
def psaExportDoc : Doc := unlower psaExportSpec psaNaming (law sentinelParams) psaClauses

/-- The embedding of the protocol's signature into the dynamic signature. -/
def psaEmbedding : SigEmbedding σ σ_dyn := embeddingOf psaNaming

end SovereignAgency
