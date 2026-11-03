import UpperTailMultipodality.Preliminaries.Graphons.Bipodal

/-!
# Constant graphons and the upper-tail variational problem

This file defines the constant graphon `W ≡ r`, the moments `∫∫ W^d`, the feasibility
predicate `t(H,W) ≥ r^m` and the upper-tail variational value
`Φ_H(p,r) = inf { I_p(W) : t(H,W) ≥ r^m }`, the case `s = 1` of
`eq:joint-variational-problem`.
-/

namespace UpperTailMultipodality

open MeasureTheory Real

/-- The constant graphon `W ≡ r`. -/
noncomputable def constGraphon (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) : Graphon where
  toFun := fun _ _ => r
  symm' := by intro x y; rfl
  meas' := by fun_prop
  nonneg' := by intro x y; exact hr.1
  le_one' := by intro x y; exact hr.2

@[simp] theorem constGraphon_apply (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) (x y : ℝ) :
    (constGraphon r hr).toFun x y = r := rfl

namespace Graphon

/-- The `d`-th moment of a graphon is nonnegative. -/
theorem Wmoment_nonneg (W : Graphon) (d : ℕ) : 0 ≤ W.Wmoment d := by
  unfold Graphon.Wmoment
  exact integral_nonneg (fun z => pow_nonneg (W.nonneg' z.1 z.2) d)

end Graphon

/-- Feasibility for the upper-tail problem: `t(H,W) ≥ r^{e(H)}`. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : ℝ) (W : Graphon) : Prop := r ^ (H.edgeFinset.card) ≤ W.tDensity H

/-- The upper-tail variational value `Φ_H(p,r) = inf { I_p(W) : t(H,W) ≥ r^m }`. -/
noncomputable def phiVar {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p r : ℝ) : ℝ :=
  sInf {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y}

end UpperTailMultipodality
