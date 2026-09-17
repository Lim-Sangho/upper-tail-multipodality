import UpperTailMultipodality.FixedDensities.Support.KernelFacts
import UpperTailMultipodality.FixedDensities.Support.JpBounds

/-!
# Feasibility, mixing and existence of minimizers for `eq:fixed-problem`

* `fixedValue_bddBelow`, `fixedValue_le` — `Ψ_ε(τ)` is an infimum bounded below by `0`;
* `edgeDensity_Wmix`, `Ip_Wmix_le` — along `ε + θ(W - ε)` the edge density is preserved and
  `I_ε` is at most `θ I_ε(W)`;
* `Ip_pos_of_tDensity_ne` — `I_ε(W) > 0` unless `t(H,W) = ε^m`;
* `exists_mix_tDensity_eq` — every value between `ε^m` and `t(H,W)` is attained on the segment;
* `exists_feasible` — the constraint set of `eq:fixed-problem` is nonempty for
  `ε^m ≤ τ < τ_max(ε)`;
* `exists_fixedMinimizer` — minimizers exist (the direct method with cut compactness).
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The costs in `eq:fixed-problem` are bounded below by `0`. -/
theorem fixedValue_bddBelow (H : SimpleGraph V) [DecidableRel H.Adj] {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (τ : ℝ) :
    BddBelow {y | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.Ip ε = y} :=
  ⟨0, by rintro y ⟨W, -, -, rfl⟩; exact Ip_nonneg W hε0 hε1⟩

/-- `Ψ_ε(τ) ≤ I_ε(W)` for every feasible `W`. -/
theorem fixedValue_le (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {W : Graphon} (he : W.edgeDensity = ε) (ht : W.tDensity H = τ) :
    fixedValue H ε τ ≤ W.Ip ε :=
  csInf_le (fixedValue_bddBelow H hε0 hε1 τ) ⟨W, he, ht, rfl⟩

/-- The edge density along the mixing path. -/
theorem edgeDensity_Wmix (W : Graphon) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    (Wmix W p hp θ hθ).edgeDensity = (1 - θ) * p + θ * W.edgeDensity := by
  unfold Graphon.edgeDensity
  show ∫ z, (1 - θ) * p + θ * W.toFun z.1 z.2 ∂gμ = _
  rw [integral_add (integrable_const _) (W.integrable_self.const_mul θ), integral_const,
    integral_const_mul]
  simp

/-- **Mixing lowers the cost.**  `I_ε(ε + θ(W - ε)) ≤ θ I_ε(W)` for `θ ∈ [0,1]`. -/
theorem Ip_Wmix_le (W : Graphon) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    (Wmix W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).Ip ε ≤ θ * W.Ip ε := by
  unfold Graphon.Ip
  show ∫ z, Jp ε ((1 - θ) * ε + θ * W.toFun z.1 z.2) ∂gμ ≤ _
  rw [← integral_const_mul]
  refine integral_mono ((Wmix W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).integrable_comp
    (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1))
    ((W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)).const_mul θ) fun z => ?_
  have h := Jp_mix_le hε0 hε1 (W.mem_Icc z.1 z.2) (θ := 1 - θ) ⟨by linarith [hθ.2], by
    linarith [hθ.1]⟩
  rw [show (1 - (1 - θ)) * W.toFun z.1 z.2 + (1 - θ) * ε = (1 - θ) * ε + θ * W.toFun z.1 z.2 by
    ring, show 1 - (1 - θ) = θ by ring] at h
  exact h

/-- If `I_ε(W) = 0` then `W = ε` almost everywhere. -/
theorem ae_eq_of_Ip_eq_zero (W : Graphon) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (h : W.Ip ε = 0) : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = ε := by
  have hint := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hnn : 0 ≤ fun z : ℝ × ℝ => Jp ε (W.toFun z.1 z.2) := fun z => by
    rcases eq_or_ne (W.toFun z.1 z.2) ε with h' | h'
    · simp only [Pi.zero_apply, h', Jp_self hε0 hε1, le_refl]
    · exact (Jp_pos_of_ne hε0 hε1 (W.nonneg' _ _) (W.le_one' _ _) h').le
  have := (integral_eq_zero_iff_of_nonneg hnn hint).mp h
  filter_upwards [this] with z hz
  exact Jp_eq_zero_imp hε0 hε1 (W.nonneg' _ _) (W.le_one' _ _) hz

/-- `I_ε(W) > 0` unless `t(H,W) = ε^m`. -/
theorem Ip_pos_of_tDensity_ne (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (h : W.tDensity H ≠ ε ^ H.edgeFinset.card) : 0 < W.Ip ε := by
  rcases (Ip_nonneg W hε0 hε1).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (tDensity_ae_const W H (ae_eq_of_Ip_eq_zero W hε0 hε1 heq.symm)) h

/-- **Intermediate values along the mixing path.** -/
theorem exists_mix_tDensity_eq (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε τ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (h0 : ε ^ H.edgeFinset.card ≤ τ) (h1 : τ ≤ W.tDensity H) :
    ∃ θ : ℝ, ∃ hθ : θ ∈ Set.Icc (0:ℝ) 1,
      (Wmix W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ).tDensity H = τ := by
  have hcont := mixTDensity_continuousOn W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) H
  have hivt := intermediate_value_Icc (zero_le_one' ℝ) hcont
  rw [mixTDensity_zero, mixTDensity_one] at hivt
  obtain ⟨θ, hθ, hθeq⟩ := hivt ⟨h0, h1⟩
  refine ⟨θ, hθ, ?_⟩
  rw [← mixTDensity_eq_tDensity W (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) H hθ]
  exact hθeq

/-- **The constraint set is nonempty** for `ε^m ≤ τ < τ_max(ε)`. -/
theorem exists_feasible (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card ≤ τ) (hτ1 : τ < tauMax H ε) :
    ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ := by
  have hne : {τ | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ}.Nonempty :=
    ⟨_, constGraphon ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩),
      edgeDensity_ae_const _ (ae_of_all _ fun _ => rfl), rfl⟩
  obtain ⟨τ', ⟨W, he, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hτ1
  obtain ⟨θ, hθ, hθeq⟩ := exists_mix_tDensity_eq H W hε0 hε1 hτ0 hlt.le
  refine ⟨_, ?_, hθeq⟩
  rw [edgeDensity_Wmix, he]; ring

/-- **Existence of minimizers** of `eq:fixed-problem` (the direct method). -/
theorem exists_fixedMinimizer (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hne : ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ) :
    ∃ W : Graphon, IsFixedMinimizer H ε τ W := by
  have hbdd := fixedValue_bddBelow H hε0 hε1 τ
  obtain ⟨W₀, he₀, ht₀⟩ := hne
  have hSne : {y | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.Ip ε = y}.Nonempty :=
    ⟨_, W₀, he₀, ht₀, rfl⟩
  have hex : ∀ n : ℕ, ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧
      W.Ip ε < fixedValue H ε τ + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨W, he, ht, rfl⟩, hy⟩ := exists_lt_of_csInf_lt hSne
      (show fixedValue H ε τ < fixedValue H ε τ + 1 / ((n : ℝ) + 1) by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
    exact ⟨W, he, ht, hy⟩
  choose W hWe hWt hWub using hex
  obtain ⟨φ, Wlim, hφ, hcut⟩ := cut_seqCompact W
  have he : Wlim.edgeDensity = ε :=
    tendsto_nhds_unique (edgeDensity_cutContinuous hcut)
      (by simp only [hWe]; exact tendsto_const_nhds)
  have ht : Wlim.tDensity H = τ :=
    tendsto_nhds_unique (tDensity_cutContinuous H hcut)
      (by simp only [hWt]; exact tendsto_const_nhds)
  refine ⟨Wlim, he, ht, le_antisymm ?_ (fixedValue_le H hε0 hε1 he ht)⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  refine Ip_cut_lowerSemicontinuous hε0 hε1 hcut ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with k hk
  have hφk : N ≤ φ k := hk.trans (hφ.id_le k)
  have h1 : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hφk 1)
  linarith [hWub (φ k)]

end FixedDensities

end UpperTailMultipodality
