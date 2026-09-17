import UpperTailMultipodality.FixedDensities.Insertion
import UpperTailMultipodality.FixedDensities.Degenerate

/-!
# Prescribed edge and subgraph densities (`sec:fixed-densities`)

The lemmas of `sec:fixed-densities`, `thm:fixed-densities` and `cor:almost-every-tau`.
Throughout, `H` has a vertex of degree at least two, `ε ∈ (0,1)`, and `ε^m < τ < τ_max(ε)`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:fixed-densities`.**  Every maximizer of `eq:entropy-maximization` that satisfies the
constraint qualification is multipodal with ordered blocks. -/
theorem fixed_densities (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
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
