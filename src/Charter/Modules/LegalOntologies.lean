/-!
# Charter.Modules.LegalOntologies — Kernel-Checked Backing Theorems for `G3.6` Modules (`D8`, `D26`)

Proves the mathematical conservation, boundedness, and non-double-counting invariants
backing `lib/contract_lifecycle.charter`, `lib/agency_mandate.charter`,
`lib/monetary_estate.charter`, and `lib/jurisdiction.charter` (`T09`, `T12`–`T20`, `T24`).
-/

namespace Charter.Modules.LegalOntologies

/-- `contract_lifecycle` (`T19`): partial performance `paid` (`0 ≤ paid ≤ rem`) leaves
non-negative remaining obligation `rem - paid ≥ 0` and preserves total debt `done + rem`. -/
theorem partial_performance_conserves_obligation (done rem paid : Int)
    (hPaidNonNeg : 0 ≤ paid) (hPaidBound : paid ≤ rem) :
    done ≤ done + paid ∧ 0 ≤ rem - paid ∧ (done + paid) + (rem - paid) = done + rem := by
  omega

/-- `monetary_estate` (`T09`): serializable reservation lock `req ≤ balance - reserved`
guarantees aggregate reservations never exceed `balance` (`reserved + req ≤ balance`). -/
theorem reservation_lock_prevents_overdraw (balance reserved req : Int)
    (hPos : 0 ≤ req) (hAvail : req ≤ balance - reserved) :
    reserved ≤ reserved + req ∧ reserved + req ≤ balance := by
  omega

/-- `monetary_estate` (`T13`): collateral pledge guard `pledged + req ≤ value` guarantees
remaining unencumbered capacity stays non-negative (`0 ≤ value - (pledged + req)`). -/
theorem collateral_pledge_capacity_sound (value pledged req : Int)
    (hGuard : pledged + req ≤ value) :
    0 ≤ value - (pledged + req) := by
  omega

/-- `monetary_estate` (`T14`): consolidated net-asset elimination subtracts intercompany
subsidiary equity `subEquity` (`0 ≤ subEquity ≤ parentGross`) so underlying subsidiary
assets `subUnderlying` are counted once, never twice. -/
theorem consolidated_eliminates_double_count (parentExSub subEquity subUnderlying : Int)
    (hParentGross : parentGross = parentExSub + subEquity) :
    (parentGross + subUnderlying) - subEquity = parentExSub + subUnderlying := by
  omega

/-- `agency_mandate` (`T15`, `T17`): absent apparent authority (e.g., once revocation notice
is received), principal-binding recognition holds only when express mandate authority is active
and `exposure + amount ≤ cap`. -/
theorem mandate_binding_bounded (expressActive apparentApplies : Bool) (exposure amount cap : Int)
    (hNoApparent : apparentApplies = false)
    (hValid : ((expressActive && decide (exposure + amount ≤ cap)) || apparentApplies) = true) :
    expressActive = true ∧ exposure + amount ≤ cap := by
  simp [hNoApparent] at hValid
  exact hValid

end Charter.Modules.LegalOntologies
