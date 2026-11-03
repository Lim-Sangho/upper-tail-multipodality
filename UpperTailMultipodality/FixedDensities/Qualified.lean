import UpperTailMultipodality.FixedDensities.Insertion
import UpperTailMultipodality.FixedDensities.Degenerate

/-!
# Multipodality under the constraint qualification (`prop:nondegenerate-multipodality`)

Under `def:constraint-qualification` the two constraints of `eq:fixed-problem` can be corrected
independently of each other.  `lem:fixed-multiplier` then produces the Lagrange multipliers,
`lem:fixed-insertion` turns them into the insertion inequality, and `sec:row-criterion` applies
to the rows.  This is the first of the three stages of `thm:fixed-densities`, which is proved
in `FixedDensities/Main.lean`.
Throughout, `H` has a vertex of degree at least two, `ε ∈ (0,1)`, and `ε^m < τ < τ_max(ε)`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`prop:nondegenerate-multipodality`.**  Every maximizer of `eq:entropy-maximization` that satisfies the
constraint qualification is multipodal with ordered blocks.  `fixed_densities` drops the
qualification. -/
theorem fixed_densities_of_cq (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hcq : ConstraintQualification H W) :
    IsOrderedMultipodal W := by
  have hmin := (isEntropyMaximizer_iff H hε0 hε1 W).mp hW
  obtain ⟨γ, hγ, hγW⟩ := fixed_interior H hΔ hε0 hε1 hτ0 hτ1 hmin hcq
  obtain ⟨α, μ, hμ, hEL⟩ := fixed_multiplier H hΔ hε0 hε1 hτ0 hτ1 hmin hcq
  obtain ⟨hlow, hrows⟩ := fixed_insertion H hΔ hε0 hε1 hτ0 hτ1 hmin hcq hμ hEL
  refine (row_criterion H hΔ W hε0 hε1 hμ hγ (hγW.mono fun z hz => hz.1) hlow).2.2 ?_
  filter_upwards [hrows] with x hx
  exact ⟨⟨W.meas'.comp measurable_prodMk_left, fun y => W.mem_Icc x y⟩, hx⟩

end UpperTailMultipodality
