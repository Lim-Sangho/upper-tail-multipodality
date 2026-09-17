import UpperTailMultipodality.RowCriterion.Main
import UpperTailMultipodality.UpperTail.Insertion
import UpperTailMultipodality.UpperTail.Support.Matching

/-!
# The upper-tail problem (`sec:upper-tail`)

For `0 < p < r < 1`, the minimizers of `eq:graphon-variational-problem` are the feasible graphons
`W` with `I_p(W) = Φ_H(p,r)`.  This file states the three lemmas of `sec:upper-tail` and
`thm:upper-tail`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:upper-tail`.**  Let `H` have at least one edge and `0 < p < r < 1`.  Every minimizer
of `eq:graphon-variational-problem` is multipodal.  If `H` has a vertex of degree at least two,
its blocks are ordered; otherwise (a perfect matching, possibly with isolated vertices) the
unique minimizer is the constant graphon `W ≡ r`. -/
theorem upper_tail (H : SimpleGraph V) [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card)
    {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1) {W : Graphon} (hW : Feasible H r W)
    (hmin : W.Ip p = phiVar H p r) :
    IsMultipodal W ∧ ((∃ v, 2 ≤ H.degree v) → IsOrderedMultipodal W) ∧
      ((∀ v, H.degree v ≤ 1) → ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) := by
  have hp1 : p < 1 := lt_trans hpr hr1
  by_cases hΔ : ∃ v, 2 ≤ H.degree v
  · -- `Δ(H) ≥ 2`: the row criterion with `q = p`, `α = 0`, `ω = p`
    obtain ⟨hlow, -, -⟩ := upper_tail_basic H hm hp0 hpr hr1 hW hmin
    obtain ⟨μ, hμ, hEL, -⟩ := upper_tail_multiplier H hm hp0 hpr hr1 hW hmin
    obtain ⟨hrow_low, hrows⟩ := upper_tail_insertion H hm hp0 hpr hr1 hW hmin hμ hEL
    have hcrit := row_criterion H hΔ W hp0 hp1 hμ hp0 hlow hrow_low
    have hord : IsOrderedMultipodal W := by
      refine hcrit.2.2 ?_
      filter_upwards [hrows] with x hx
      exact ⟨⟨W.meas'.of_uncurry_left, fun y => W.mem_Icc x y⟩, hx⟩
    refine ⟨hord.isMultipodal, fun _ => hord, fun hdeg => ?_⟩
    obtain ⟨v, hv⟩ := hΔ
    have := hdeg v
    omega
  · -- `Δ(H) ≤ 1`: the constant graphon `r` is the unique minimizer
    have hdeg : ∀ v, H.degree v ≤ 1 := fun v => by
      by_contra h
      exact hΔ ⟨v, by omega⟩
    have hae := UpperTailSupport.ae_eq_of_degree_le_one H hdeg hm hp0 hpr hr1 hW hmin
    have hord := UpperTailSupport.isOrderedMultipodal_of_ae_const
      ⟨(hp0.trans hpr).le, hr1.le⟩ hae
    exact ⟨hord.isMultipodal, fun h => absurd h hΔ, fun _ => hae⟩

end UpperTailMultipodality
