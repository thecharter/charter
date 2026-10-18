import Charter.Surface.Unlower
import Examples.AutonomousCommons

/-!
# Examples.AutonomousCommons.Export — The Commons as a `.charter` Document

`commonsExportDoc` expresses the Lean formalization of the Autonomous Compute &
Treasury Commons as a `Charter.Dsl.Doc`, printed by `charter export --law commons`
to `autonomous-commons.charter`. See `Examples.SovereignAgency.Export` for the
sentinel technique that recovers parameter names.
-/

namespace AutonomousCommons

open Charter Charter.Dsl

def paramsEnv (P : CommonsParams) : Env :=
  [ ("bondDeadline", P.bondDeadline), ("freezeWindow", P.freezeWindow),
    ("suspensionLimit", P.suspensionLimit), ("leasePeriod", P.leasePeriod),
    ("treasuryObligation", P.treasuryObligation), ("retirementRatePct", P.retirementRatePct),
    ("royaltyRatePct", P.royaltyRatePct), ("treasurySunset", P.treasurySunset),
    ("operatingReserveFloor", P.operatingReserveFloor), ("groupSubsidyBudget", P.groupSubsidyBudget) ]

def paramsOfEnv (env : Env) : CommonsParams :=
  { bondDeadline := env.lookup "bondDeadline", freezeWindow := env.lookup "freezeWindow",
    suspensionLimit := env.lookup "suspensionLimit", leasePeriod := env.lookup "leasePeriod",
    treasuryObligation := env.lookup "treasuryObligation", retirementRatePct := env.lookup "retirementRatePct",
    royaltyRatePct := env.lookup "royaltyRatePct", treasurySunset := env.lookup "treasurySunset",
    operatingReserveFloor := env.lookup "operatingReserveFloor", groupSubsidyBudget := env.lookup "groupSubsidyBudget" }

def sentinelParams : CommonsParams :=
  paramsOfEnv ((paramsEnv commonsDefaultParams).zipIdx.map fun ((n, _), i) => (n, sentinelValue i))

def commonsSentinels : List (Nat × String) :=
  ((paramsEnv sentinelParams).map fun (n, v) => (v, n)).reverse

def regimeOf (label : String) (P : CommonsParams) : Regime :=
  let base := paramsEnv commonsDefaultParams
  ⟨label, (paramsEnv P).filter fun (n, v) => base.lookup n != v⟩

def commonsNaming : Naming σ_commons :=
  { actor := commonsRoleTable.toName
    act := commonsActTable.toName
    fact := fun f => ⟨commonsFactTable.toName f, none⟩ }

def commonsExportSpec : ExportSpec σ_commons :=
  { id := commonsId
    title := commonsTitle
    document := some "autonomous-commons-charter.md"
    contract := some "AutonomousCommonsGuard"
    defaultActor := some "steward"
    roles := commonsRoleTable.all
    acts := commonsActTable.all
    facts := commonsFactTable.all
    params := paramsEnv commonsDefaultParams
    sentinels := commonsSentinels
    regimes := commonsCandidateRegimes.map fun (l, P) => regimeOf l P
    modules := ["ResidualLedger", "CollateralPool", "CircuitBreaker", "EntityGroup",
                "ExitAndVoice", "SortitionCourt", "AttestedLease", "OracleFeed"].map fun m => ⟨m, []⟩ }

def commonsExportDoc : Doc := unlower commonsExportSpec commonsNaming (commonsLaw sentinelParams) commonsClauses

def commonsEmbedding : SigEmbedding σ_commons σ_dyn := embeddingOf commonsNaming

end AutonomousCommons
