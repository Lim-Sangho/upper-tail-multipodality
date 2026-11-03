import UpperTailMultipodality.RowCriterion.Rows.Derivative

/-!
# Tools for `lem:row-interior`

* `exists_Jp'_margin` — the singularities of `J_q'` at `0` and `1` give `δ ∈ (0,1/2)` with
  `J_q' < α - K` on `(0,δ)` and `J_q' > α + K` on `(1-δ,1)`;
* `Jp_sub_lt_of_deriv_lt`, `lt_Jp_sub_of_lt_deriv` — the mean value theorem for `J_q`;
* `rowFunctional_lt_of_pointwise` — comparison of `ℱ_W` at two rows through
  `eq:rooted-lipschitz`;
* `hasDerivAt_rowFunctional_line` — the first variation of `ℱ_W` in a bounded direction.
-/

namespace UpperTailMultipodality.Rows

open MeasureTheory Filter

/-- **The singularities of `J_q'`.**  For every `α` and `K` there is `δ ∈ (0,1/2)` such that
`J_q'(z) < α - K` for `0 < z < δ` and `J_q'(z) > α + K` for `1 - δ < z < 1`. -/
theorem exists_Jp'_margin {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (α K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ (∀ z, 0 < z → z < δ → Jp' q z < α - K) ∧
      (∀ z, 1 - δ < z → z < 1 → α + K < Jp' q z) := by
  obtain ⟨E₁, hE₁⟩ : ∃ E, E = Real.exp (α - K) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E, E = Real.exp (α + K) := ⟨_, rfl⟩
  have hE₁0 : 0 < E₁ := hE₁ ▸ Real.exp_pos _
  have hE₂0 : 0 < E₂ := hE₂ ▸ Real.exp_pos _
  have h1q : 0 < 1 - q := by linarith
  have hd₁ : 0 < E₁ * q / (2 * (1 - q)) := by positivity
  have hd₂ : 0 < (1 - q) / (2 * q * E₂) := by positivity
  refine ⟨min (1 / 4) (min (E₁ * q / (2 * (1 - q))) ((1 - q) / (2 * q * E₂))),
    lt_min (by norm_num) (lt_min hd₁ hd₂), (min_le_left _ _).trans_lt (by norm_num), ?_, ?_⟩
  · intro z hz0 hzδ
    have hz4 : z < 1 / 4 := hzδ.trans_le (min_le_left _ _)
    have hzE : z < E₁ * q / (2 * (1 - q)) :=
      hzδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ (by positivity)] at hzE
    have hden : 0 < (1 - z) * q := mul_pos (by linarith) hq0
    have hX : 0 < z * (1 - q) / ((1 - z) * q) := div_pos (mul_pos hz0 h1q) hden
    unfold Jp'
    rw [Real.log_lt_iff_lt_exp hX, ← hE₁, div_lt_iff₀ hden]
    nlinarith [mul_pos hE₁0 hq0]
  · intro z hzδ hz1
    have hz4 : 3 / 4 < z := by
      have := min_le_left (1 / 4 : ℝ) (min (E₁ * q / (2 * (1 - q))) ((1 - q) / (2 * q * E₂)))
      linarith
    have hzE : 1 - z < (1 - q) / (2 * q * E₂) := by
      have := (min_le_right (1 / 4 : ℝ) (min (E₁ * q / (2 * (1 - q)))
        ((1 - q) / (2 * q * E₂)))).trans (min_le_right _ _)
      linarith
    rw [lt_div_iff₀ (by positivity)] at hzE
    have hden : 0 < (1 - z) * q := mul_pos (by linarith) hq0
    have hX : 0 < z * (1 - q) / ((1 - z) * q) := div_pos (mul_pos (by linarith) h1q) hden
    unfold Jp'
    rw [Real.lt_log_iff_exp_lt hX, ← hE₂, lt_div_iff₀ hden]
    nlinarith [mul_pos hE₂0 hq0]

/-- **Mean value theorem for `J_q`, upper bound.** -/
theorem Jp_sub_lt_of_deriv_lt {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (h : ∀ z, a < z → z < b → Jp' q z < c) :
    Jp q b - Jp q a < c * (b - a) := by
  have hcont : ContinuousOn (Jp q) (Set.Icc a b) :=
    (continuousOn_Jp_Icc hq0 hq1).mono (Set.Icc_subset_Icc ha hb)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (Jp q) (Jp' q) hab hcont
    fun z hz => hasDerivAt_Jp hq0 hq1 (by linarith [hz.1]) (by linarith [hz.2])
  have hlt := h ξ hξ.1 hξ.2
  rw [hslope, div_lt_iff₀ (by linarith)] at hlt
  exact hlt

/-- **Mean value theorem for `J_q`, lower bound.** -/
theorem lt_Jp_sub_of_lt_deriv {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (h : ∀ z, a < z → z < b → c < Jp' q z) :
    c * (b - a) < Jp q b - Jp q a := by
  have hcont : ContinuousOn (Jp q) (Set.Icc a b) :=
    (continuousOn_Jp_Icc hq0 hq1).mono (Set.Icc_subset_Icc ha hb)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (Jp q) (Jp' q) hab hcont
    fun z hz => hasDerivAt_Jp hq0 hq1 (by linarith [hz.1]) (by linarith [hz.2])
  have hlt := h ξ hξ.1 hξ.2
  rw [hslope, lt_div_iff₀ (by linarith)] at hlt
  exact hlt

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Comparison of `ℱ_W` at two rows.**  If the pointwise integrand
`2(J_q(v) - J_q(u)) - 2α(v - u) + 2M_*|v - u|` is nonpositive, and negative on a set of positive
measure, then `ℱ_W(v) < ℱ_W(u)`.  This combines `eq:combined-lipschitz` with `μ_j ≥ 0`. -/
theorem rowFunctional_lt_of_pointwise {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) {q α : ℝ} {μ : ι → ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j) {u v : ℝ → ℝ} (hu : IsRow u)
    (hv : IsRow v) {s : Set ℝ} (hs : 0 < unitμ s)
    (hle : ∀ y, 2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
      + 2 * combinedEdgeCard Hs μ * |v y - u y| ≤ 0)
    (hlt : ∀ y ∈ s, 2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
      + 2 * combinedEdgeCard Hs μ * |v y - u y| < 0) :
    combinedRowFunctional Hs W q α μ v < combinedRowFunctional Hs W q α μ u := by
  have iJu := integrable_Jp_row hq0 hq1 hu
  have iJv := integrable_Jp_row hq0 hq1 hv
  have iu := integrable_of_isRow hu
  have iv := integrable_of_isRow hv
  have iabs : Integrable (fun y => |v y - u y|) unitμ := (iv.sub iu).abs
  have hΦint : Integrable (fun y => 2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
      + 2 * combinedEdgeCard Hs μ * |v y - u y|) unitμ :=
    (((iJv.sub iJu).const_mul 2).sub ((iv.sub iu).const_mul (2 * α))).add
      (iabs.const_mul _)
  have hΦ : ∫ y, (2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
      + 2 * combinedEdgeCard Hs μ * |v y - u y|) ∂unitμ
      = 2 * ((∫ y, Jp q (v y) ∂unitμ) - ∫ y, Jp q (u y) ∂unitμ)
        - 2 * α * ((∫ y, v y ∂unitμ) - ∫ y, u y ∂unitμ)
        + 2 * combinedEdgeCard Hs μ * ∫ y, |v y - u y| ∂unitμ := by
    have i₁ : Integrable (fun y => 2 * (Jp q (v y) - Jp q (u y))) unitμ :=
      (iJv.sub iJu).const_mul 2
    have i₂ : Integrable (fun y => 2 * α * (v y - u y)) unitμ := (iv.sub iu).const_mul (2 * α)
    have i₃ : Integrable (fun y => 2 * combinedEdgeCard Hs μ * |v y - u y|) unitμ :=
      iabs.const_mul _
    have i₁₂ : Integrable (fun y => 2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y))
        unitμ := i₁.sub i₂
    rw [integral_add i₁₂ i₃, integral_sub i₁ i₂, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_sub iJv iJu, integral_sub iv iu]
  have hneg : ∫ y, (2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
      + 2 * combinedEdgeCard Hs μ * |v y - u y|) ∂unitμ < 0 := by
    have hpos : 0 < ∫ y, -(2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
        + 2 * combinedEdgeCard Hs μ * |v y - u y|) ∂unitμ := by
      have hneg' : Integrable (fun y => -(2 * (Jp q (v y) - Jp q (u y)) - 2 * α * (v y - u y)
          + 2 * combinedEdgeCard Hs μ * |v y - u y|)) unitμ := hΦint.neg
      rw [integral_pos_iff_support_of_nonneg (fun y => neg_nonneg.mpr (hle y)) hneg']
      refine hs.trans_le (measure_mono fun y hy => ?_)
      exact Function.mem_support.mpr (neg_ne_zero.mpr (hlt y hy).ne)
    rw [integral_neg] at hpos
    linarith
  have hlip := combined_lipschitz Hs W hμ hv hu
  have hR : -(combinedRooted Hs W μ v - combinedRooted Hs W μ u)
      ≤ 2 * combinedEdgeCard Hs μ * ∫ y, |v y - u y| ∂unitμ := (neg_le_abs _).trans hlip
  unfold combinedRowFunctional
  nlinarith [hΦ, hneg, hR]

/-- **The first variation of `ℱ_W`.**  Under the hypotheses of
`hasDerivAt_integral_Jp_line`, `t ↦ ℱ_W(u + t h)` has derivative
`2∫J_q'(u) h - 2α∫h - ∑_j μ_j ∫∇ℛ_{H_j,W}(u) h` at `0`. -/
theorem hasDerivAt_rowFunctional_line {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) {q α δ : ℝ} {μ : ι → ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hδ : 0 < δ) {u h : ℝ → ℝ} (hu : IsRow u)
    (hh : Measurable h) (hhb : ∀ y, |h y| ≤ 1)
    (hsupp : ∀ y, h y ≠ 0 → δ ≤ u y ∧ u y ≤ 1 - δ) :
    HasDerivAt (fun t : ℝ => combinedRowFunctional Hs W q α μ (fun y => u y + t * h y))
      (2 * ∫ y, Jp' q (u y) * h y ∂unitμ - 2 * α * ∫ y, h y ∂unitμ
        - ∑ j, μ j * ∫ y, rootedGradient (Hs j) W u y * h y ∂unitμ) 0 := by
  have hJ := hasDerivAt_integral_Jp_line hq0 hq1 hδ hu hh hhb hsupp
  have hR := hasDerivAt_combinedRooted_line Hs W μ hu hh hhb
  have ih : Integrable h unitμ := integrable_of_abs_le hh 1 hhb
  have hfun : (fun t : ℝ => ∫ y, (u y + t * h y) ∂unitμ)
      = fun t => (∫ y, u y ∂unitμ) + t * ∫ y, h y ∂unitμ := by
    funext t
    rw [integral_add (integrable_of_isRow hu) (ih.const_mul t), integral_const_mul]
  have hlin : HasDerivAt (fun t : ℝ => ∫ y, (u y + t * h y) ∂unitμ) (∫ y, h y ∂unitμ) 0 := by
    rw [hfun]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∫ y, h y ∂unitμ)).const_add
      (∫ y, u y ∂unitμ)
  exact ((hJ.const_mul 2).sub (hlin.const_mul (2 * α))).sub hR

end UpperTailMultipodality.Rows
