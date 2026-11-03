import UpperTailMultipodality.FixedDensities.Defs
import UpperTailMultipodality.FixedDensities.Support.Existence

/-!
# Monotonicity of the value function (`lem:fixed-monotonicity`)

`lem:fixed-monotonicity` states that the value function `Ψ_ε` of `eq:fixed-problem` is strictly
increasing on `(ε^m, τ_max(ε))` (`fixedValue_strictMonoOn`), and, more precisely, that every
graphon `U` with `e(U) = ε` and `t(H,U) ≥ τ` costs at least `Ψ_ε(τ)`, strictly more when
`t(H,U) > τ` (`fixedValue_le_Ip`).  So the equality constraint of `eq:fixed-problem` may be
relaxed to an inequality; `fixed_inequality_minimality` is that reading, phrased at a minimizer.

The proof mixes the competitor down to the constrained density along `ε + θ(U - ε)`, which
preserves the edge density and scales the cost by at most `θ`.

`fixed_monotone` bundles the two statements in the form the rest of the development uses.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:fixed-monotonicity`, the comparison with `Ψ_ε`.**  Every graphon `U` with `e(U) = ε`
and `t(H,U) ≥ τ` satisfies `I_ε(U) ≥ Ψ_ε(τ)`, strictly if `t(H,U) > τ`. -/
theorem fixedValue_le_Ip (H : SimpleGraph V) [DecidableRel H.Adj] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) {U : Graphon}
    (hUe : U.edgeDensity = ε) (hUt : τ ≤ U.tDensity H) :
    fixedValue H ε τ ≤ U.Ip ε ∧ (τ < U.tDensity H → fixedValue H ε τ < U.Ip ε) := by
  obtain ⟨θ, hθ, hθeq⟩ := exists_mix_tDensity_eq H U hε0 hε1 hτ.1.le hUt
  have hmixe : (Wmix U ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).edgeDensity = ε := by
    rw [edgeDensity_Wmix, hUe]; ring
  have hbase : fixedValue H ε τ ≤ θ * U.Ip ε :=
    (fixedValue_le H hε0 hε1 hmixe hθeq).trans (Ip_Wmix_le U hε0 hε1 hθ)
  refine ⟨?_, fun hlt => ?_⟩
  · calc fixedValue H ε τ ≤ θ * U.Ip ε := hbase
      _ ≤ U.Ip ε := by nlinarith [Ip_nonneg U hε0 hε1, hθ.2]
  · -- a strict excess forces `θ < 1`, and the cost at `U` is positive
    have hθ1 : θ < 1 := by
      refine lt_of_le_of_ne hθ.2 fun h => ?_
      subst h
      have h1 : (Wmix U ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) 1 hθ).tDensity H = U.tDensity H := by
        rw [← mixTDensity_eq_tDensity U _ H hθ, mixTDensity_one]
      rw [h1] at hθeq
      linarith
    have hUpos : 0 < U.Ip ε :=
      Ip_pos_of_tDensity_ne H U hε0 hε1 (by intro hcon; rw [hcon] at hlt; linarith [hτ.1])
    calc fixedValue H ε τ ≤ θ * U.Ip ε := hbase
      _ < U.Ip ε := by nlinarith

/-- **`lem:fixed-monotonicity`, read at a minimizer.**  A minimizer `W` of `eq:fixed-problem` at
`τ` also minimizes `I_ε` over the larger set `{e(U) = ε, t(H,U) ≥ τ}`, strictly when
`t(H,U) > τ`.  This is the form the insertion arguments use: it is enough to move in a direction
that does not decrease the constrained densities. -/
theorem fixed_inequality_minimality (H : SimpleGraph V) [DecidableRel H.Adj] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) {W : Graphon}
    (hW : W.Ip ε = fixedValue H ε τ) {U : Graphon} (hUe : U.edgeDensity = ε)
    (hUt : τ ≤ U.tDensity H) :
    W.Ip ε ≤ U.Ip ε ∧ (τ < U.tDensity H → W.Ip ε < U.Ip ε) := by
  rw [hW]
  exact fixedValue_le_Ip H hε0 hε1 hτ hUe hUt

/-- **`lem:fixed-monotonicity`, the strict monotonicity of `Ψ_ε`** on `(ε^m, τ_max(ε))`.  A
minimizer `W₂` at `τ₂ > τ₁` is an admissible competitor at `τ₁` with a strict density excess. -/
theorem fixedValue_strictMonoOn (H : SimpleGraph V) [DecidableRel H.Adj] {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    StrictMonoOn (fixedValue H ε) (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) := by
  intro τ₁ hτ₁ τ₂ hτ₂ h12
  obtain ⟨W₂, he₂, ht₂, hW₂⟩ :=
    exists_fixedMinimizer H hε0 hε1 (exists_feasible H hε0 hε1 hτ₂.1.le hτ₂.2)
  have hstrict := (fixedValue_le_Ip H hε0 hε1 hτ₁ he₂ (by rw [ht₂]; exact h12.le)).2
    (by rw [ht₂]; exact h12)
  rwa [hW₂] at hstrict

/-- **`lem:fixed-monotonicity`**, bundled in the form used by `FixedDensities/Main.lean` and
`FixedDensities/Support/Lagrange.lean`. -/
theorem fixed_monotone (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    StrictMonoOn (fixedValue H ε) (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) ∧
      ∀ τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε), ∀ W : Graphon,
        W.edgeDensity = ε → W.tDensity H = τ → W.Ip ε = fixedValue H ε τ →
          ∀ U : Graphon, U.edgeDensity = ε → τ ≤ U.tDensity H → W.Ip ε ≤ U.Ip ε := by
  -- the degree hypothesis is not needed
  obtain ⟨-, -⟩ := hΔ
  exact ⟨fixedValue_strictMonoOn H hε0 hε1, fun τ hτ W _ _ hW U hUe hUt =>
    (fixed_inequality_minimality H hε0 hε1 hτ hW hUe hUt).1⟩

end UpperTailMultipodality
