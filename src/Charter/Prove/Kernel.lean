import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.AuxLemma

/-!
# Charter.Prove.Kernel — `kernel_rfl`

The one tactic the project `charter prove` writes uses for its checkpoint theorems
(spec 013.4). `kernel_rfl` closes a goal `a = b` with `Eq.refl`, and hands that proof to
the kernel directly, the way `decide +kernel` hands over its `decide p = true`: the
elaborator never compares the two sides itself. Plain `rfl` compares them in the
elaborator first, which exceeds 6 GB on a one-phrase program where the kernel needs under
a second (finding of 2026-10-24); `decide +kernel` needs a `DecidableEq` instance, which
Lean cannot derive for the nested inductives (`Term`, `Elem`) a configuration carries.

The proof is `Eq.refl` alone, so a theorem closed this way depends on no axioms (Law 10),
and the kernel's own definitional unfolding is the only evaluator involved (Law 9: the
checkpoint it is compared with is what the compiled evaluator produced).

This module imports the elaborator and is imported by the generated project only, never
by the `charter` executable (it is a separate root of the `Charter` library).
-/

namespace Charter.Prove

open Lean Elab Tactic Meta

/-- `kernel_rfl` proves `a = b` by `Eq.refl`, checked by the kernel alone. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

@[tactic kernelRfl] def evalKernelRfl : Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext do
    let t ← instantiateMVars (← goal.getType)
    let some (α, _, b) := t.eq?
      | throwError "kernel_rfl: the goal is not an equation"
    if t.hasFVar || t.hasMVar then
      throwError "kernel_rfl: the equation must be closed (no hypotheses, no metavariables)"
    let u ← getLevel α
    let pf := mkApp2 (mkConst ``Eq.refl [u]) α b
    let levels := (collectLevelParams {} t).params.toList
    let lemmaName ←
      try
        withOptions (Elab.async.set · false) do mkAuxLemma levels t pf
      catch _ =>
        throwError "kernel_rfl: the kernel did not find the two sides equal"
    goal.assign (mkConst lemmaName (levels.map .param))

end Charter.Prove
