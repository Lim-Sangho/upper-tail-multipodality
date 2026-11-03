import UpperTailMultipodality.FixedDensities.Support.UniformCorrection
import UpperTailMultipodality.FixedDensities.AlmostEvery

/-!
# `L¹` continuity of the constraints and the cost, and good values of `τ`

The last step of `thm:fixed-densities` takes a sequence of maximizers at values `τ_n ↑ τ` at
which `cor:almost-every-tau` applies, and passes to an `L¹` limit.  Two things are needed for
the limit to be a maximizer at `τ`, and one to produce the sequence.

* `abs_edgeDensity_sub_le` and `abs_tDensity_sub_le` — the two constraints are Lipschitz in `L¹`
  (the second is the counting lemma, with constant `m = |E(H)|`);
* `tendsto_Ip_of_tendsto_L1` — the cost is continuous along `L¹`-convergent graphons.  It is not
  Lipschitz, because `J_ε'` blows up at `0` and `1`, but `J_ε` is uniformly continuous on
  `[0,1]`, and `L¹` convergence gives convergence in measure;
* `exists_good_seq` — the values of `τ` to which `cor:almost-every-tau` applies accumulate at
  `τ` from the left, because the exceptional ones form a null set.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The absolute difference of two graphons is integrable. -/
theorem integrable_abs_sub_graphon (W W' : Graphon) :
    Integrable (fun z : ℝ × ℝ => |W.toFun z.1 z.2 - W'.toFun z.1 z.2|) gμ :=
  (W.integrable_self.sub W'.integrable_self).abs

/-- **The edge density is Lipschitz in `L¹`.** -/
theorem abs_edgeDensity_sub_le (W W' : Graphon) :
    |W.edgeDensity - W'.edgeDensity| ≤ ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := by
  unfold Graphon.edgeDensity
  rw [← integral_sub W.integrable_self W'.integrable_self]
  exact abs_integral_le_integral_abs

/-- **The counting lemma in `L¹`.**  `|t(H,W) - t(H,W')| ≤ m ‖W - W'‖₁`. -/
theorem abs_tDensity_sub_le (H : SimpleGraph V) [DecidableRel H.Adj] (W W' : Graphon) :
    |W.tDensity H - W'.tDensity H|
      ≤ (H.edgeFinset.card : ℝ) * ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := ⟨_, rfl⟩
  -- the `L¹` distance of two edge factors is `d`
  have hedge : ∀ e ∈ H.edgeFinset,
      ∫ ξ : V → ℝ, |edgeVal W.toFun W.symm' ξ e - edgeVal W'.toFun W'.symm' ξ e|
        ∂(Measure.pi fun _ : V => unitμ) = d := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rw [hd]
    exact integral_pair_eq hadj.ne ((W.measurable_uncurry.sub W'.measurable_uncurry).abs)
  have habs : ∀ e : Sym2 V, Integrable
      (fun ξ : V → ℝ => |edgeVal W.toFun W.symm' ξ e - edgeVal W'.toFun W'.symm' ξ e|)
      (Measure.pi fun _ : V => unitμ) := fun e =>
    (((IsBddMeas.of_mem_Icc (measurable_edgeVal W.symm' W.meas' e)
        fun x => edgeVal_mem_Icc W x e).sub
      (IsBddMeas.of_mem_Icc (measurable_edgeVal W'.symm' W'.meas' e)
        fun x => edgeVal_mem_Icc W' x e)).abs).integrable
  have hi1 := (isBddMeas_prod_edgeVal W H.edgeFinset).integrable
    (μ := Measure.pi fun _ : V => unitμ)
  have hi2 := (isBddMeas_prod_edgeVal W' H.edgeFinset).integrable
    (μ := Measure.pi fun _ : V => unitμ)
  have hT : ∀ Z : Graphon, Z.tDensity H
      = ∫ ξ : V → ℝ, ∏ e ∈ H.edgeFinset, edgeVal Z.toFun Z.symm' ξ e
        ∂(Measure.pi fun _ : V => unitμ) := fun _ => rfl
  rw [hT W, hT W', ← integral_sub hi1 hi2]
  calc |∫ ξ : V → ℝ, ((∏ e ∈ H.edgeFinset, edgeVal W.toFun W.symm' ξ e)
            - ∏ e ∈ H.edgeFinset, edgeVal W'.toFun W'.symm' ξ e)
          ∂(Measure.pi fun _ : V => unitμ)|
      ≤ ∫ ξ : V → ℝ, |(∏ e ∈ H.edgeFinset, edgeVal W.toFun W.symm' ξ e)
            - ∏ e ∈ H.edgeFinset, edgeVal W'.toFun W'.symm' ξ e|
          ∂(Measure.pi fun _ : V => unitμ) := abs_integral_le_integral_abs
    _ ≤ ∫ ξ : V → ℝ, ∑ e ∈ H.edgeFinset,
            |edgeVal W.toFun W.symm' ξ e - edgeVal W'.toFun W'.symm' ξ e|
          ∂(Measure.pi fun _ : V => unitμ) := by
        refine integral_mono ((hi1.sub hi2).abs)
          (integrable_finsetSum _ fun e _ => habs e) fun ξ => ?_
        refine abs_prod_sub_prod_le _ _ _ (fun e _ => ?_) (fun e _ => ?_)
        · obtain ⟨h0, h1⟩ := edgeVal_mem_Icc W ξ e
          rw [abs_of_nonneg h0]; exact h1
        · obtain ⟨h0, h1⟩ := edgeVal_mem_Icc W' ξ e
          rw [abs_of_nonneg h0]; exact h1
    _ = ∑ e ∈ H.edgeFinset, d := by
        rw [integral_finsetSum _ fun e _ => habs e]
        exact Finset.sum_congr rfl hedge
    _ = (H.edgeFinset.card : ℝ) * d := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (H.edgeFinset.card : ℝ) * ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := by
        rw [hd]


/-- **The cost is continuous along `L¹`-convergent graphons.** -/
theorem tendsto_Ip_of_tendsto_L1 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (Wn : ℕ → Graphon)
    (W : Graphon)
    (hL1 : Tendsto (fun n => ∫ z, |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2| ∂gμ) atTop (𝓝 0)) :
    Tendsto (fun n => (Wn n).Ip ε) atTop (𝓝 (W.Ip ε)) := by
  -- a uniform bound for `J_ε` on `[0,1]`
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0:ℝ) 1, |Jp ε t| ≤ C := by
    obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) (continuousOn_Jp_Icc hε0 hε1).abs
    refine ⟨|Jp ε t₀| + 1, by positivity, fun t ht => ?_⟩
    have h := hmax ht
    simp only [Set.mem_ofPred_eq] at h
    linarith
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- uniform continuity of `J_ε` on `[0,1]`
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      |s - t| < ρ → |Jp ε s - Jp ε t| < δ / 2 := by
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous (continuousOn_Jp_Icc hε0 hε1)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨ρ, hρ0, hρ⟩ := huc (δ / 2) (by linarith)
    exact ⟨ρ, hρ0, fun s hs t ht hst => by
      simpa [Real.dist_eq] using hρ s hs t ht (by simpa [Real.dist_eq] using hst)⟩
  -- the bad set has small measure once the `L¹` distance is small
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL1 (ρ * (δ / (4 * C))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (ℝ × ℝ), A =
      {z : ℝ × ℝ | ρ ≤ |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2|} := ⟨_, rfl⟩
  have hAm : MeasurableSet A := by
    rw [hA]
    exact measurableSet_le measurable_const
      (((Wn n).measurable_uncurry.sub W.measurable_uncurry).abs)
  have hL1n : ∫ z, |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2| ∂gμ < ρ * (δ / (4 * C)) := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun z => abs_nonneg _)] at this
    exact this
  have hAsmall : gμ.real A < δ / (4 * C) := by
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (μ := gμ) (f := fun z : ℝ × ℝ => |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2|)
      (ae_of_all _ fun z => abs_nonneg _) (integrable_abs_sub_graphon (Wn n) W) ρ
    rw [hA]
    have hlt : ρ * gμ.real {z : ℝ × ℝ | ρ ≤ |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2|}
        < ρ * (δ / (4 * C)) := lt_of_le_of_lt (by nlinarith [hmk]) hL1n
    exact lt_of_mul_lt_mul_left hlt hρ0.le
  -- split the integral over the bad set and its complement
  have hint1 := (Wn n).integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hint2 := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hsplit : |(Wn n).Ip ε - W.Ip ε|
      ≤ ∫ z, |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)| ∂gμ := by
    unfold Graphon.Ip
    rw [← integral_sub hint1 hint2]
    exact abs_integral_le_integral_abs
  have hbound : ∫ z, |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)| ∂gμ
      ≤ δ / 2 + 2 * C * gμ.real A := by
    have hgint : Integrable
        (fun z : ℝ × ℝ => |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)|) gμ :=
      (hint1.sub hint2).abs
    have hptw : ∀ z : ℝ × ℝ,
        |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)|
          ≤ δ / 2 + 2 * C * Set.indicator A (fun _ => (1:ℝ)) z := by
      intro z
      by_cases hz : z ∈ A
      · have h1 : |Jp ε ((Wn n).toFun z.1 z.2)| ≤ C := hC _ ((Wn n).mem_Icc z.1 z.2)
        have h2 : |Jp ε (W.toFun z.1 z.2)| ≤ C := hC _ (W.mem_Icc z.1 z.2)
        rw [Set.indicator_of_mem hz]
        calc |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)|
            ≤ |Jp ε ((Wn n).toFun z.1 z.2)| + |Jp ε (W.toFun z.1 z.2)| := abs_sub _ _
          _ ≤ C + C := by linarith
          _ ≤ δ / 2 + 2 * C * 1 := by linarith
      · have hlt : |(Wn n).toFun z.1 z.2 - W.toFun z.1 z.2| < ρ := by
          rw [hA] at hz; exact not_le.mp hz
        have := hρ _ ((Wn n).mem_Icc z.1 z.2) _ (W.mem_Icc z.1 z.2) hlt
        rw [Set.indicator_of_notMem hz]
        have hC0' : (0:ℝ) ≤ 2 * C * 0 := by simp
        linarith
    have hind : Integrable (fun z : ℝ × ℝ => δ / 2 + 2 * C * Set.indicator A (fun _ => (1:ℝ)) z)
        gμ := by
      exact (integrable_const _).add
        (Integrable.const_mul ((integrable_const (1:ℝ)).indicator hAm) _)
    calc ∫ z, |Jp ε ((Wn n).toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)| ∂gμ
        ≤ ∫ z, (δ / 2 + 2 * C * Set.indicator A (fun _ => (1:ℝ)) z) ∂gμ :=
          integral_mono hgint hind hptw
      _ = δ / 2 + 2 * C * gμ.real A := by
          rw [integral_add (integrable_const _)
            (Integrable.const_mul ((integrable_const (1:ℝ)).indicator hAm) _),
            integral_const, integral_const_mul, integral_indicator_const _ hAm]
          simp [measureReal_def]
  rw [Real.dist_eq]
  have hfin : 2 * C * gμ.real A < δ / 2 := by
    have h := mul_lt_mul_of_pos_left hAsmall (by positivity : (0:ℝ) < 2 * C)
    rwa [show 2 * C * (δ / (4 * C)) = δ / 2 from by field_simp; ring] at h
  linarith [hsplit, hbound]

/-- **Good values of `τ` accumulate at `τ` from the left.**  By `cor:almost-every-tau` the
values admitting a degenerate maximizer form a null set, so every interval to the left of `τ`
contains a value at which every maximizer is multipodal with ordered blocks. -/
theorem exists_good_seq (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) :
    ∃ tn : ℕ → ℝ, (∀ n, tn n ∈ Ioo (ε ^ H.edgeFinset.card) τ) ∧
      Tendsto tn atTop (𝓝 τ) ∧
      ∀ n, ∀ W : Graphon, IsEntropyMaximizer H ε (tn n) W → IsOrderedMultipodal W := by
  classical
  obtain ⟨-, hae⟩ := almost_every_tau H hΔ hε0 hε1
  rw [ae_iff] at hae
  obtain ⟨Bad, hBad⟩ : ∃ Bad : Set ℝ, Bad = {τ' : ℝ | ¬ (τ' ∈ Ioo (ε ^ H.edgeFinset.card)
      (tauMax H ε) → ∀ W : Graphon, IsEntropyMaximizer H ε τ' W → IsOrderedMultipodal W)} :=
    ⟨_, rfl⟩
  have hBad0 : volume Bad = 0 := by rw [hBad]; exact hae
  -- every interval to the left of `τ` meets the complement of `Bad`
  have hstep : ∀ n : ℕ, ∃ t : ℝ, t ∈ Ioo (max (ε ^ H.edgeFinset.card) (τ - 1 / ((n : ℝ) + 1))) τ
      ∧ ∀ W : Graphon, IsEntropyMaximizer H ε t W → IsOrderedMultipodal W := by
    intro n
    obtain ⟨a, ha⟩ : ∃ a, a = max (ε ^ H.edgeFinset.card) (τ - 1 / ((n : ℝ) + 1)) := ⟨_, rfl⟩
    have hlt : a < τ := by
      have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [ha]
      exact max_lt hτ0 (by linarith)
    by_contra hc
    have hsub : Ioo a τ ⊆ Bad := by
      intro t ht
      rw [hBad]
      intro himp
      have ht1 : max (ε ^ H.edgeFinset.card) (τ - 1 / ((n : ℝ) + 1)) < t := by
        rw [← ha]; exact ht.1
      have htmem : t ∈ Ioo (ε ^ H.edgeFinset.card) (tauMax H ε) :=
        ⟨lt_of_le_of_lt (le_max_left _ _) ht1, lt_trans ht.2 hτ1⟩
      exact hc ⟨t, ⟨ht1, ht.2⟩, himp htmem⟩
    have hpos : 0 < volume (Ioo a τ) := by
      rw [Real.volume_Ioo]
      simpa using (ENNReal.ofReal_pos).mpr (by linarith : (0:ℝ) < τ - a)
    exact absurd (measure_mono_null hsub hBad0) (ne_of_gt hpos)
  refine ⟨fun n => (hstep n).choose, fun n => ?_, ?_, fun n W hW => ?_⟩
  · obtain ⟨hmem, -⟩ := (hstep n).choose_spec
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hmem.1, hmem.2⟩
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hmem, -⟩ := (hstep n).choose_spec
    have h1 : τ - 1 / ((n : ℝ) + 1) < (hstep n).choose :=
      lt_of_le_of_lt (le_max_right _ _) hmem.1
    have h2 : (hstep n).choose < τ := hmem.2
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [Real.dist_eq, abs_of_neg (by linarith : (hstep n).choose - τ < 0)]
    linarith
  · obtain ⟨-, hgood⟩ := (hstep n).choose_spec
    exact hgood W hW

end FixedDensities

end UpperTailMultipodality
