import UpperTailMultipodality.RowCriterion.Defs
import UpperTailMultipodality.Preliminaries.Perturbation
import UpperTailMultipodality.UpperTail.Support.Multiplier

/-!
# Basic properties of upper-tail minimizers (`sec:upper-tail-interiority`)

`lem:upper-tail-basic`, and the multiplier part of `lem:upper-tail-multiplier`.
The paper states both for a finite family of upper-tail constraints; here they
are specialized to one constraint.  The family
versions are `joint_ae_ge`, `joint_exists_active`, `joint_exists_ae_le_one_sub`
and `joint_multiplier`, in `UpperTail/Joint/`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:upper-tail-basic`.**  A minimizer satisfies `W ≥ p` almost everywhere, the constraint
is active, and `W ≤ 1 - γ` almost everywhere for some `γ > 0`. -/
theorem upper_tail_basic (H : SimpleGraph V) [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card)
    {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1) {W : Graphon} (hW : Feasible H r W)
    (hmin : W.Ip p = phiVar H p r) :
    (∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2) ∧ W.tDensity H = r ^ H.edgeFinset.card ∧
      ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - γ := by
  have hlow := UpperTailSupport.ae_ge_of_minimizer H hp0 (lt_trans hpr hr1) hW hmin
  have hact := UpperTailSupport.tDensity_eq_of_minimizer H hm hp0 hpr hr1 hW hmin
  exact ⟨hlow, hact,
    UpperTailSupport.exists_ae_le_one_sub_of_minimizer H hm hp0 hpr hr1 hmin hlow hact⟩

/-- **The multiplier part of `lem:upper-tail-multiplier`, for a single constraint.**  A minimizer
satisfies `J_p'(W) = μ𝒟_W` almost everywhere, `lem:upper-tail-multiplier`(i), for some `μ > 0`,
and takes
values in a compact subinterval of `(p,1)`. -/
theorem upper_tail_multiplier (H : SimpleGraph V) [DecidableRel H.Adj]
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    {W : Graphon} (hW : Feasible H r W) (hmin : W.Ip p = phiVar H p r) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = μ * derivKernel H W z.1 z.2) ∧
      ∃ a b : ℝ, p < a ∧ a ≤ b ∧ b < 1 ∧ ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b := by
  obtain ⟨hlow, hact, γ, hγ, hup⟩ := upper_tail_basic H hm hp0 hpr hr1 hW hmin
  exact UpperTailSupport.multiplier_of_bounds H hm hp0 hpr hr1 hmin hlow hact hγ hup

end UpperTailMultipodality
