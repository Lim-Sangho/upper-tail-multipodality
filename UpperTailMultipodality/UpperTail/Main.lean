import UpperTailMultipodality.RowCriterion.Main
import UpperTailMultipodality.UpperTail.Insertion
import UpperTailMultipodality.UpperTail.Support.Matching

/-!
# The upper-tail problem for one constraint (`sec:upper-tail-row-minimality`)

For `0 < p < r < 1`, the minimizers of `eq:joint-variational-problem` with `s = 1` are the
feasible graphons `W` with `I_p(W) = Φ_H(p,r)`.  This file specializes `thm:joint-upper-tail` to
one constraint.  When `H` has maximum degree at most one the minimizer is the constant `r`,
which is `UpperTailSupport.ae_eq_of_degree_le_one`; the paper derives that identification inside
the proof of `thm:joint-upper-tail`, and the theorem below uses it only to get one block.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:joint-upper-tail` for one constraint.**  Let `H` have at least one edge and
`0 < p < r < 1`.  Every minimizer of `eq:joint-variational-problem` with `s = 1` is multipodal
with ordered blocks. -/
theorem upper_tail (H : SimpleGraph V) [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card)
    {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1) {W : Graphon} (hW : Feasible H r W)
    (hmin : W.Ip p = phiVar H p r) :
    IsOrderedMultipodal W := by
  have hp1 : p < 1 := lt_trans hpr hr1
  by_cases hΔ : ∃ v, 2 ≤ H.degree v
  · -- `Δ(H) ≥ 2`: the row criterion with `q = p`, `α = 0`, `ω = p`
    obtain ⟨hlow, -, -⟩ := upper_tail_basic H hm hp0 hpr hr1 hW hmin
    obtain ⟨μ, hμ, hEL, -⟩ := upper_tail_multiplier H hm hp0 hpr hr1 hW hmin
    obtain ⟨hrow_low, hrows⟩ := upper_tail_insertion H hm hp0 hpr hr1 hW hmin hμ hEL
    refine (row_criterion H hΔ W hp0 hp1 hμ hp0 hlow hrow_low).2.2 ?_
    filter_upwards [hrows] with x hx
    exact ⟨⟨W.meas'.of_uncurry_left, fun y => W.mem_Icc x y⟩, hx⟩
  · -- `Δ(H) ≤ 1`: the minimizer is the constant graphon `r`, hence has one block
    have hdeg : ∀ v, H.degree v ≤ 1 := fun v => by
      by_contra h
      exact hΔ ⟨v, by omega⟩
    exact UpperTailSupport.isOrderedMultipodal_of_ae_const ⟨(hp0.trans hpr).le, hr1.le⟩
      (UpperTailSupport.ae_eq_of_degree_le_one H hdeg hm hp0 hpr hr1 hW hmin)

end UpperTailMultipodality
