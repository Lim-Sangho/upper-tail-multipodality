import UpperTailMultipodality.FixedDensities.OrderedNondegenerate
import UpperTailMultipodality.FixedDensities.Support.OrderedCompact
import UpperTailMultipodality.FixedDensities.Support.L1Continuity

/-!
# Fixed edge and subgraph densities (`thm:fixed-densities`)

`prop:nondegenerate-multipodality` leaves the degenerate maximizers, at which the two constraints cannot be
corrected independently, and `cor:almost-every-tau` shows that they occur for at most a null set
of densities.  This file removes that exceptional set.

Suppose a degenerate maximizer exists at `τ`.  Densities `τ_n ↑ τ` at which every maximizer is
multipodal with ordered blocks are supplied by `exists_good_seq`; choosing maximizers there and
listing their blocks in order gives graphons `U_n` with ordered rows
(`exists_hasOrderedRows_of_isOrderedMultipodal`), and `ordered_compact` extracts an `L¹` limit
`W_*` with ordered rows.  The three functionals pass to the limit — `abs_edgeDensity_sub_le`,
`abs_tDensity_sub_le` and `tendsto_Ip_of_tendsto_L1` — so `W_*` is feasible at `τ` and
`I_ε(W_*) = lim Ψ_ε(τ_n) ≤ Ψ_ε(τ)`, whence `W_*` attains `Ψ_ε(τ)`.  By
`ordered_nondegenerate` it satisfies the constraint qualification, and correcting each `U_n`
along the directions of `W_*` bounds the left difference quotients of `Ψ_ε` at `τ`
(`lem:uniform-density-restoration`, as `exists_uniform_upward_correction`).  That contradicts `degenerate_slope`, which makes those
quotients tend to `+∞`.
Throughout, `H` has a vertex of degree at least two, `ε ∈ (0,1)`, and `ε^m < τ < τ_max(ε)`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`prop:optimizer-nondegeneracy`.**  Every maximizer of `eq:entropy-maximization` at an
interior subgraph density satisfies the constraint qualification: the exceptional set of
`cor:almost-every-tau` is empty.  This is the argument described in the module docstring. -/
theorem optimizer_nondegeneracy (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ0 : ε ^ H.edgeFinset.card < τ) (hτ1 : τ < tauMax H ε) {W : Graphon}
    (hW : IsEntropyMaximizer H ε τ W) :
    ConstraintQualification H W := by
  classical
  by_contra hdeg
  -- densities `τ_n ↑ τ` at which every maximizer is multipodal with ordered blocks
  obtain ⟨tn, htmem, httend, hgood⟩ := exists_good_seq H hΔ hε0 hε1 hτ0 hτ1
  have hmemτ : ∀ n, tn n ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) := fun n =>
    ⟨(htmem n).1, (htmem n).2.trans hτ1⟩
  -- maximizers there, relabelled to have ordered rows
  have hex : ∀ n, ∃ Un : Graphon, HasOrderedRows Un ∧ Un.edgeDensity = ε ∧
      Un.tDensity H = tn n ∧ Un.Ip ε = fixedValue H ε (tn n) := by
    intro n
    obtain ⟨Wn, hWn⟩ := exists_fixedMinimizer H hε0 hε1
      (exists_feasible H hε0 hε1 (htmem n).1.le (hmemτ n).2)
    obtain ⟨Un, hord, he, ht, hI⟩ := exists_hasOrderedRows_of_isOrderedMultipodal (p := ε) H
      (hgood n Wn ((isEntropyMaximizer_iff H hε0 hε1 Wn).mpr hWn))
    exact ⟨Un, hord, by rw [he, hWn.1], by rw [ht, hWn.2.1], by rw [hI, hWn.2.2]⟩
  choose U hUord hUe hUt hUI using hex
  -- the `L¹` limit along a subsequence still has ordered rows
  obtain ⟨φ, Wstar, hφ, hstarord, hL1⟩ := ordered_compact U hUord
  have hsub : ∀ n, tn (φ n) < τ := fun n => (htmem (φ n)).2
  have httend' : Tendsto (fun n => tn (φ n)) atTop (𝓝 τ) := httend.comp hφ.tendsto_atTop
  -- the edge density passes to the limit
  have hWe : Wstar.edgeDensity = ε := by
    have h0 : Tendsto (fun n => |(U (φ n)).edgeDensity - Wstar.edgeDensity|) atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun n => abs_edgeDensity_sub_le _ _) hL1
    have hconv : Tendsto (fun n => (U (φ n)).edgeDensity) atTop (𝓝 Wstar.edgeDensity) := by
      rw [tendsto_iff_dist_tendsto_zero]
      simpa [Real.dist_eq] using h0
    refine tendsto_nhds_unique hconv ?_
    simp only [hUe]
    exact tendsto_const_nhds
  -- so does the `H`-density
  have hWt : Wstar.tDensity H = τ := by
    have h0 : Tendsto (fun n => |(U (φ n)).tDensity H - Wstar.tDensity H|) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => abs_nonneg _) (fun n => abs_tDensity_sub_le H _ _) ?_
      simpa using hL1.const_mul (H.edgeFinset.card : ℝ)
    have hconv : Tendsto (fun n => (U (φ n)).tDensity H) atTop (𝓝 (Wstar.tDensity H)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      simpa [Real.dist_eq] using h0
    refine tendsto_nhds_unique hconv ?_
    simp only [hUt]
    exact httend'
  -- and the rate functional, so `W_*` attains `Ψ_ε(τ)`
  have hIp : Tendsto (fun n => (U (φ n)).Ip ε) atTop (𝓝 (Wstar.Ip ε)) :=
    tendsto_Ip_of_tendsto_L1 hε0 hε1 (fun n => U (φ n)) Wstar hL1
  have hmono : MonotoneOn (fixedValue H ε) (Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) :=
    (fixed_monotone H hΔ hε0 hε1).1.monotoneOn
  have hstarmax : IsEntropyMaximizer H ε τ Wstar := by
    refine (isEntropyMaximizer_iff H hε0 hε1 Wstar).mpr ⟨hWe, hWt, le_antisymm ?_ ?_⟩
    · refine le_of_tendsto hIp (Eventually.of_forall fun n => ?_)
      rw [hUI]
      exact hmono (hmemτ (φ n)) ⟨hτ0, hτ1⟩ (hsub n).le
    · exact fixedValue_le H hε0 hε1 hWe hWt
  -- an ordered maximizer is nondegenerate, so the corrections along `W_*` are uniform
  obtain ⟨C, hC⟩ := exists_uniform_upward_correction H hε0 hε1 (fun n => U (φ n))
    (fun n => tn (φ n)) (fun n => ⟨hUe _, hUt _⟩) (fun n => hUI _) hsub httend' Wstar hL1
    (ordered_nondegenerate H hΔ hε0 hε1 hτ0 hτ1 hstarmax hstarord)
  -- but at a degenerate maximizer the left difference quotients of `Ψ_ε` blow up
  have hslope := (degenerate_slope H hΔ hε0 hε1 hτ0 hτ1 hW hdeg).comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ httend'
      (Eventually.of_forall fun n => hsub n))
  rw [tendsto_atTop] at hslope
  obtain ⟨n, hn1, hn2⟩ := ((hslope (C + 1)).and hC).exists
  have hpos : 0 < τ - tn (φ n) := by linarith [hsub n]
  have hquot : (C + 1) * (τ - tn (φ n)) ≤ fixedValue H ε τ - fixedValue H ε (tn (φ n)) := by
    rw [← le_div_iff₀ hpos]
    exact hn1
  linarith

/-- **`thm:fixed-densities`.**  Every maximizer of `eq:entropy-maximization` at an interior
subgraph density is multipodal with ordered blocks, with no constraint qualification and no
exceptional set of densities. -/
theorem fixed_densities (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W) :
    IsOrderedMultipodal W :=
  fixed_densities_of_cq H hΔ hε0 hε1 hτ0 hτ1 hW
    (optimizer_nondegeneracy H hΔ hε0 hε1 hτ0 hτ1 hW)

end UpperTailMultipodality
