import Charter.Verify.Explorer

/-!
# Charter.Verify.Temporal — Safety, Bounded-Response, and Fairness-Gated Liveness (`G2.3`, `D20`)

Evaluates `TemporalSpec` declarations (`Always`, `AlwaysNext`, `AlwaysEventually`,
`AlwaysEventuallyWithin`, `Until`, `WeakUntil`) over explored execution trees while keeping
`Charter.Eval`'s single-step TCB untouched.

Key soundness discipline (`T31`): unbounded liveness (`AlwaysEventually` and strong `Until`)
is **never** reported as unconditionally satisfied unless the property explicitly declares a
fairness / progress assumption in `Assumes ...` (such as `scheduler-fairness` or `clock-progress`),
and every emitted `ClaimCertificate` carries those declared assumptions verbatim.
-/

namespace Charter.Verify

open M

/-- Pure path-level semantics of `WeakUntil` over a boolean pair trace `[(φ₀, ψ₀), ...]`. -/
def evalWeakUntilTrace : List (Bool × Bool) → Bool
  | [] => true
  | (_, true) :: _ => true
  | (false, false) :: _ => false
  | (true, false) :: rest => evalWeakUntilTrace rest

/-- Pure path-level semantics of `EventuallyWithin Δ` from a trigger timestamp `t0` over
timed boolean states `[(t, respHolds), ...]`: fails once time reaches `t0 + Δ` without
`respHolds` having occurred on `[t0, t0 + Δ]`. -/
def evalWithinWindow (t0 delta : Int) : List (Int × Bool) → Bool
  | [] => true
  | (t, true) :: _ => decide (t ≤ t0 + delta)
  | (t, false) :: rest => if t ≥ t0 + delta then false else evalWithinWindow t0 delta rest

/-- Kernel-checked temporal lemma (`G2.3`): if `φ` holds at every step along a trace,
`WeakUntil(φ, ψ)` holds regardless of whether `ψ` ever occurs. -/
theorem weakUntil_of_always_true :
    ∀ (tr : List (Bool × Bool)), (∀ p ∈ tr, p.1 = true) → evalWeakUntilTrace tr = true
  | [], _ => rfl
  | (b1, b2) :: rest, hall => by
    have hb1 : b1 = true := hall (b1, b2) (List.mem_cons_self ..)
    subst hb1
    cases b2
    · exact weakUntil_of_always_true rest (fun p hp => hall p (List.mem_cons_of_mem _ hp))
    · rfl

/-- Kernel-checked temporal monotonicity (`G2.3`): widening a bounded-response deadline
from `d₁` to `d₂ ≥ d₁` preserves satisfaction of `evalWithinWindow`. -/
theorem eventuallyWithin_monotone (t0 d₁ d₂ : Int) (hle : d₁ ≤ d₂) :
    ∀ (tr : List (Int × Bool)),
      evalWithinWindow t0 d₁ tr = true → evalWithinWindow t0 d₂ tr = true
  | [], _ => rfl
  | (t, true) :: _, h => by
    simp only [evalWithinWindow, decide_eq_true_eq] at h ⊢
    omega
  | (t, false) :: rest, h => by
    simp only [evalWithinWindow] at h ⊢
    by_cases ht1 : t ≥ t0 + d₁
    · rw [if_pos ht1] at h; cases h
    · rw [if_neg ht1] at h
      have ht2 : ¬(t ≥ t0 + d₂) := by omega
      rw [if_neg ht2]
      exact eventuallyWithin_monotone t0 d₁ d₂ hle rest h

/-- Evaluate a closed boolean `Term` in `cfg`. -/
def evalStateBool (cfg : Config) (t : Term) : Bool :=
  let ctx := Ctx.of cfg.spec cfg.state
  match (ignoreMissingInput (eval M.fuel t)).run ctx [] with
  | .ok vs => vs.all (· == .bool true) && !vs.isEmpty
  | .error _ => false

/-- Evaluate an integer/duration `Term` in `cfg`. -/
def evalStateInt (cfg : Config) (t : Term) : Option Int :=
  let ctx := Ctx.of cfg.spec cfg.state
  match (ignoreMissingInput (eval M.fuel t)).run ctx [] with
  | .ok [.int n] => some n
  | _ => none

/-- Whether a `TemporalSpec` declares an explicit fairness or clock-progress assumption (`T31`). -/
def hasFairnessAssumption (tp : TemporalSpec) : Bool :=
  tp.assumptions.any fun a =>
    (a.splitOn "fair").length > 1 || (a.splitOn "progress").length > 1 || (a.splitOn "live").length > 1

/-- Check one `TemporalFormula` along a concrete execution path `(cfg₀, [(step₁, cfg₁), ...])`
that is maximal up to `depth`. Returns `true` when satisfied on this path. -/
def checkPathFormula (isMaximal : Bool) (tf : TemporalFormula)
    (cfg₀ : Config) (steps : List (ActionStep × Config)) : Bool :=
  let states : List Config := cfg₀ :: steps.map (·.2)
  match tf with
  | .always phi =>
    states.all (fun c => evalStateBool c phi)
  | .alwaysNext ante post =>
    let pairs := states.zip (steps.map (·.2))
    pairs.all fun (pre, nxt) => if evalStateBool pre ante then evalStateBool nxt post else true
  | .alwaysEventually req resp =>
    if !isMaximal then true
    else
      let rec suffixes : List Config → Bool
        | [] => true
        | c :: rest =>
          let ok := if evalStateBool c req then (c :: rest).any (fun c' => evalStateBool c' resp) else true
          ok && suffixes rest
      suffixes states
  | .alwaysEventuallyWithin boundTerm req resp =>
    let delta := (evalStateInt cfg₀ boundTerm).getD 0
    let rec suffixesWithin : List Config → Bool
      | [] => true
      | c :: rest =>
        let ok :=
          if evalStateBool c req then
            let timed := (c :: rest).map fun c' => (c'.state.time, evalStateBool c' resp)
            evalWithinWindow c.state.time delta timed
          else true
        ok && suffixesWithin rest
    suffixesWithin states
  | .until_ phi psi =>
    if !isMaximal then true
    else
      let rec checkUntil : List Config → Bool
        | [] => false
        | c :: rest =>
          if evalStateBool c psi then true
          else if evalStateBool c phi then checkUntil rest
          else false
      checkUntil states
  | .weakUntil phi psi =>
    evalWeakUntilTrace (states.map fun c => (evalStateBool c phi, evalStateBool c psi))

inductive TemporalOutcome
  | satisfied (visitedPaths : Nat) (assumptions : List String)
  | violated (propName : DomId) (trace : List ActionStep) (assumptions : List String)
  | inconclusive (propName : DomId) (reason : String)

/-- Enumerate execution paths up to `depth` under `opts` and verify `tp` (`G2.3`). -/
def verifyTemporal (opts : SearchOpts) (cfg₀ : Config) (tp : TemporalSpec) : TemporalOutcome :=
  let needsFairness := match tp.formula with
    | .alwaysEventually _ _ | .until_ _ _ => true
    | _ => false
  if needsFairness && !hasFairnessAssumption tp then
    .inconclusive tp.name
      "unbounded liveness requires an explicit fairness/progress assumption (`Assumes scheduler-fairness` or `clock-progress`, T31)"
  else
    let cov := modeCoverage opts.mode cfg₀.spec opts.menu
    let missing := cov.filter (·.source == .stateValues)
    if !missing.isEmpty then
      .inconclusive tp.name
        s!"missing explore-domain menu for {", ".intercalate ((missing.map (·.comp)).eraseDups)}"
    else
      let rec dfsPaths (fuel : Nat) (cur : Config) (prefixSteps : List (ActionStep × Config)) :
          Nat × Option (List ActionStep) :=
        match fuel with
        | 0 => (1, none)
        | fuel + 1 =>
          if prefixSteps.length ≥ opts.depth then
            if checkPathFormula true tp.formula cfg₀ prefixSteps then (1, none)
            else (1, some (prefixSteps.map (·.1)))
          else
            match candidateSteps opts.mode opts.menu cur with
            | .error _ => (1, none)
            | .ok cands =>
              if cands.isEmpty then
                if checkPathFormula true tp.formula cfg₀ prefixSteps then (1, none)
                else (1, some (prefixSteps.map (·.1)))
              else
                -- Check prefix safety/bounded-response immediately too
                if !checkPathFormula false tp.formula cfg₀ prefixSteps then
                  (1, some (prefixSteps.map (·.1)))
                else
                  let rec branch : List ActionStep → Nat → Nat × Option (List ActionStep)
                    | [], count => (count, none)
                    | st :: rest, count =>
                      if count ≥ opts.stateCap then (count, none)
                      else
                        match stepConfig cur st with
                        | .error _ => branch rest count
                        | .ok nxt =>
                          let (subCount, viol?) := dfsPaths fuel nxt (prefixSteps ++ [(st, nxt)])
                          match viol? with
                          | some tr => (count + subCount, some tr)
                          | none => branch rest (count + subCount)
                  branch cands 0
      let (pathsChecked, viol?) := dfsPaths (opts.depth + 2) cfg₀ []
      match viol? with
      | some tr => .violated tp.name tr tp.assumptions
      | none =>
        if pathsChecked ≥ opts.stateCap then
          .inconclusive tp.name s!"path budget ({opts.stateCap}) exhausted before completing temporal horizon"
        else
          .satisfied pathsChecked tp.assumptions

end Charter.Verify
