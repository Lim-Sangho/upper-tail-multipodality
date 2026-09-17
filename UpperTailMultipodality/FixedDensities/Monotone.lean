import UpperTailMultipodality.FixedDensities.Defs
import UpperTailMultipodality.FixedDensities.Support.Existence

/-!
# Monotonicity of the value function (`lem:fixed-monotone`)
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:fixed-monotone`.**  `Ψ_ε` is strictly increasing on `(ε^m, τ_max(ε))`, and a minimizer
at `τ` minimizes `I_ε` over all graphons with `e(U) = ε` and `t(H,U) ≥ τ`. -/
theorem fixed_monotone (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    StrictMonoOn (fixedValue H ε) (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) ∧
      ∀ τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε), ∀ W : Graphon,
        W.edgeDensity = ε → W.tDensity H = τ → W.Ip ε = fixedValue H ε τ →
          ∀ U : Graphon, U.edgeDensity = ε → τ ≤ U.tDensity H → W.Ip ε ≤ U.Ip ε := by
  -- the degree hypothesis is not needed for monotonicity
  obtain ⟨-, -⟩ := hΔ
  refine ⟨fun τ₁ hτ₁ τ₂ hτ₂ h12 => ?_, fun τ hτ W he ht hW U hUe hUt => ?_⟩
  · -- a minimizer at `τ₂`, mixed down to `τ₁`
    obtain ⟨W₂, he₂, ht₂, hW₂⟩ :=
      exists_fixedMinimizer H hε0 hε1 (exists_feasible H hε0 hε1 hτ₂.1.le hτ₂.2)
    obtain ⟨θ, hθ, hθeq⟩ := exists_mix_tDensity_eq H W₂ hε0 hε1 hτ₁.1.le (ht₂ ▸ h12.le)
    have hθ1 : θ < 1 := by
      refine lt_of_le_of_ne hθ.2 fun h => ?_
      subst h
      have : (Wmix W₂ ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) 1 hθ).tDensity H = W₂.tDensity H := by
        rw [← mixTDensity_eq_tDensity W₂ _ H hθ, mixTDensity_one]
      linarith
    have hpos : 0 < W₂.Ip ε :=
      Ip_pos_of_tDensity_ne H W₂ hε0 hε1 (by rw [ht₂]; exact hτ₂.1.ne')
    have hmixe : (Wmix W₂ ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).edgeDensity = ε := by
      rw [edgeDensity_Wmix, he₂]; ring
    calc fixedValue H ε τ₁ ≤ (Wmix W₂ ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).Ip ε :=
          fixedValue_le H hε0 hε1 hmixe hθeq
      _ ≤ θ * W₂.Ip ε := Ip_Wmix_le W₂ hε0 hε1 hθ
      _ < W₂.Ip ε := by nlinarith
      _ = fixedValue H ε τ₂ := hW₂
  · -- mix `U` down to the value `τ`
    obtain ⟨θ, hθ, hθeq⟩ := exists_mix_tDensity_eq H U hε0 hε1 hτ.1.le hUt
    have hmixe : (Wmix U ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).edgeDensity = ε := by
      rw [edgeDensity_Wmix, hUe]; ring
    calc W.Ip ε = fixedValue H ε τ := hW
      _ ≤ (Wmix U ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).Ip ε :=
          fixedValue_le H hε0 hε1 hmixe hθeq
      _ ≤ θ * U.Ip ε := Ip_Wmix_le U hε0 hε1 hθ
      _ ≤ U.Ip ε := by nlinarith [Ip_nonneg U hε0 hε1, hθ.2]

end UpperTailMultipodality
