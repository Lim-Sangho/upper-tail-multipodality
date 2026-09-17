import UpperTailMultipodality.FixedDensities.Main

/-!
# Multipodality for almost every value of the subgraph density (`cor:almost-every-tau`)
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`cor:almost-every-tau`.**  The values `τ ∈ (ε^m, τ_max(ε))` for which some maximizer violates
the constraint qualification form a null set.  Consequently, for almost every such `τ`, every
maximizer is multipodal with ordered blocks. -/
theorem almost_every_tau (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.volume {τ : ℝ | τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) ∧
        ∃ W : Graphon, IsEntropyMaximizer H ε τ W ∧ ¬ ConstraintQualification H W} = 0 ∧
      ∀ᵐ τ ∂MeasureTheory.volume, τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) →
        ∀ W : Graphon, IsEntropyMaximizer H ε τ W → IsOrderedMultipodal W := by
  -- `Ψ_ε` is monotone on the interval, hence differentiable almost everywhere on it
  have hmono : MonotoneOn (fixedValue H ε)
      (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) :=
    (fixed_monotone H hΔ hε0 hε1).1.monotoneOn
  have hdiff : ∀ᵐ τ : ℝ, τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) →
      DifferentiableWithinAt ℝ (fixedValue H ε)
        (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) τ :=
    hmono.ae_differentiableWithinAt_of_mem
  -- at a point of differentiability there is no degenerate maximizer
  have hbad : MeasureTheory.volume {τ : ℝ | τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) ∧
      ∃ W : Graphon, IsEntropyMaximizer H ε τ W ∧ ¬ ConstraintQualification H W} = 0 := by
    refine measure_mono_null (fun τ hτ => ?_) (MeasureTheory.ae_iff.mp hdiff)
    obtain ⟨hτS, W, hWmax, hWdeg⟩ := hτ
    intro hd
    have hdiffAt : DifferentiableAt ℝ (fixedValue H ε) τ :=
      (hd hτS).differentiableAt (isOpen_Ioo.mem_nhds hτS)
    have hslope : Tendsto (slope (fixedValue H ε) τ) (𝓝[≠] τ) (𝓝 (deriv (fixedValue H ε) τ)) :=
      hasDerivAt_iff_tendsto_slope.mp hdiffAt.hasDerivAt
    have hlt : Tendsto (slope (fixedValue H ε) τ) (𝓝[<] τ)
        (𝓝 (deriv (fixedValue H ε) τ)) :=
      hslope.mono_left (nhdsWithin_mono τ fun x hx => ne_of_lt hx)
    have hev : ∀ᶠ τ' in 𝓝[<] τ,
        slope (fixedValue H ε) τ τ' < deriv (fixedValue H ε) τ + 1 :=
      hlt.eventually (eventually_lt_nhds (lt_add_one _))
    have hfr := degenerate_slope H hΔ hε0 hε1 hτS.1 hτS.2 hWmax hWdeg
      (deriv (fixedValue H ε) τ + 1)
    obtain ⟨τ', hτ'1, hτ'2⟩ := (hfr.and_eventually hev).exists
    rw [slope_def_field] at hτ'2
    rw [show fixedValue H ε τ - fixedValue H ε τ'
        = -(fixedValue H ε τ' - fixedValue H ε τ) by ring,
      show τ - τ' = -(τ' - τ) by ring, neg_div_neg_eq] at hτ'1
    exact absurd hτ'1 (not_lt.mpr hτ'2.le)
  refine ⟨hbad, ?_⟩
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun τ hτ => ?_) hbad
  have hτ' : ¬ (τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) →
    ∀ W : Graphon, IsEntropyMaximizer H ε τ W → IsOrderedMultipodal W) := hτ
  rw [Classical.not_imp] at hτ'
  obtain ⟨hτS, hne⟩ := hτ'
  obtain ⟨W, hW2⟩ := not_forall.mp hne
  obtain ⟨hWmax, hWnot⟩ := Classical.not_imp.mp hW2
  refine ⟨hτS, W, hWmax, fun hcq => hWnot ?_⟩
  exact fixed_densities H hΔ hε0 hε1 hτS.1 hτS.2 hWmax hcq

end UpperTailMultipodality
