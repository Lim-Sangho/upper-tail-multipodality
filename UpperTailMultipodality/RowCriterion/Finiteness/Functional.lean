import UpperTailMultipodality.RowCriterion.Finiteness.Gradient
import UpperTailMultipodality.RowCriterion.Finiteness.Scalar

/-!
# The row functional on bounded measurable functions

`rowFunctionalE` is the row functional `ℱ_W` of `eq:row-functional` restricted to `BddMeas`.  At a
function with values in a compact subinterval of `(0,1)` it is Fréchet differentiable, with
derivative `k ↦ ∫ (2J_q'(u) - 2α - μ∇ℛ_W(u)) k` (`hasFDerivAt_rowFunctionalE`).  At a global
minimizer satisfying the Euler–Lagrange equation `eq:row-euler`, the second variation
`Q_u(h) = 2∫J_q''(u)h² - μ∫D∇ℛ_W(u)[h] h` is nonnegative (`secondVariation_nonneg`), the
second-order necessary condition used in the proof of `lem:coercive`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology Asymptotics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Second-order necessary condition in one variable.**  If `φ` has a local minimum at `0`,
with derivative `ψ` near `0`, `ψ 0 = 0`, and `ψ` has derivative `a` at `0`, then `0 ≤ a`. -/
theorem nonneg_of_isLocalMin_deriv {φ ψ : ℝ → ℝ} {t₀ a : ℝ} (ht₀ : 0 < t₀)
    (hmin : ∀ t, |t| < t₀ → φ 0 ≤ φ t) (hφ : ∀ t, |t| < t₀ → HasDerivAt φ (ψ t) t)
    (hψ0 : ψ 0 = 0) (hψ : HasDerivAt ψ a 0) : 0 ≤ a := by
  by_contra hcon
  have ha : a < 0 := lt_of_not_ge hcon
  have hslope := hψ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (ψ (0 + t) - ψ 0) < 0 :=
    hslope (Iio_mem_nhds ha)
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set t₁ := min (δ / 2) (t₀ / 2) with ht₁
  have ht₁pos : 0 < t₁ := lt_min (by linarith) (by linarith)
  have hψneg : ∀ t ∈ Set.Ioo 0 t₁, ψ t < 0 := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans_le ((min_le_left _ _).trans (by linarith))
    have h := hδev hdist ht.1
    rw [zero_add, hψ0, sub_zero, smul_eq_mul] at h
    nlinarith [inv_pos.mpr ht.1]
  have hcont : ContinuousOn φ (Set.Icc 0 t₁) := fun t ht =>
    (hφ t (by rw [abs_of_nonneg ht.1]; exact ht.2.trans_lt ((min_le_right _ _).trans_lt
      (by linarith)))).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo 0 t₁, HasDerivAt φ (ψ t) t := fun t ht =>
    hφ t (by rw [abs_of_pos ht.1]; exact ht.2.trans ((min_le_right _ _).trans_lt (by linarith)))
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ ψ ht₁pos hcont hderiv
  have hlt : φ t₁ < φ 0 := by
    have h1 := hψneg ξ hξ
    rw [hξeq, div_neg_iff] at h1
    rcases h1 with h1 | h1
    · linarith [h1.2]
    · linarith [h1.1]
  have hge := hmin t₁ (by rw [abs_of_pos ht₁pos]; exact (min_le_right _ _).trans_lt (by linarith))
  linarith

variable (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (q α μ : ℝ)

/-- **The row functional `ℱ_W` on `BddMeas`.** -/
noncomputable def rowFunctionalE (u : BddMeas) : ℝ := rowFunctional H W q α μ u

/-- The entropy term `u ↦ ∫ J_q(u)`. -/
noncomputable def entropyE (u : BddMeas) : ℝ := ∫ y, Jp q (u y) ∂unitμ

variable {H W q α μ}

/-- The row functional in terms of its three terms. -/
theorem rowFunctionalE_eq (u : BddMeas) :
    rowFunctionalE H W q α μ u
      = 2 * entropyE q u - 2 * α * BddMeas.integ u - μ * rootedE H W u := by
  rw [rowFunctionalE, rowFunctional, entropyE, BddMeas.integ_apply, rootedE_eq]

/-- `J_q ∘ u` is integrable for bounded measurable `u`. -/
theorem integrable_Jp_comp {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (u : BddMeas) :
    Integrable (fun y => Jp q (u y)) unitμ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -‖u‖) (b := ‖u‖)).exists_bound_of_continuousOn
    (continuous_Jp hq0 hq1).continuousOn
  refine integrable_of_abs_le ((measurable_Jp q).comp u.measurable) C fun y => ?_
  have h := hC (u y) (abs_le.mp (u.abs_apply_le_norm y))
  rwa [Real.norm_eq_abs] at h

/-- Pointwise values are bounded by the norm. -/
theorem abs_le_of_norm_le {k : BddMeas} {r : ℝ} (hk : ‖k‖ ≤ r) (y : ℝ) : |k y| ≤ r :=
  (k.abs_apply_le_norm y).trans hk

/-- Values of `u + k` stay in `[c - r, d + r]`. -/
theorem add_mem_Icc_of_norm_le {u k : BddMeas} {c d r : ℝ} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hk : ‖k‖ ≤ r) (y : ℝ) : (u + k) y ∈ Set.Icc (c - r) (d + r) := by
  have h := abs_le.mp (abs_le_of_norm_le (k := k) hk y)
  rw [BddMeas.add_apply]
  exact ⟨by linarith [(hu y).1, h.1], by linarith [(hu y).2, h.2]⟩

/-- **The first variation of the entropy term** at a function with values in `[c,d] ⊆ (0,1)`. -/
theorem hasFDerivAt_entropyE (hq0 : 0 < q) (hq1 : q < 1) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d) {g : BddMeas} (hg : ∀ y, g y = Jp' q (u y)) :
    HasFDerivAt (entropyE q) (BddMeas.integ.comp (BddMeas.mulLeftCLM g)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  set r := min c (1 - d) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hc (by linarith))
  have hc' : 0 < c - r := by
    have : r ≤ c / 2 := by rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    linarith
  have hd' : d + r < 1 := by
    have : r ≤ (1 - d) / 2 := by
      rw [hr]; exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
    linarith
  set L := 1 / ((c - r) * (1 - (d + r))) with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  refine IsBigO.trans_isLittleO (g := fun k : BddMeas => ‖k‖ ^ 2) ?_
    (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound L ?_
  filter_upwards [Metric.ball_mem_nhds (0 : BddMeas) hr0] with k hk
  rw [Metric.mem_ball, dist_zero_right] at hk
  have hkr : ‖k‖ ≤ r := hk.le
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  have hpt : ∀ y, |Jp q (u y + k y) - Jp q (u y) - g y * k y| ≤ L * ‖k‖ ^ 2 := by
    intro y
    have hmem1 : u y ∈ Set.Icc (c - r) (d + r) :=
      ⟨by linarith [(hu y).1], by linarith [(hu y).2]⟩
    have hmem2 : u y + k y ∈ Set.Icc (c - r) (d + r) := add_mem_Icc_of_norm_le hu hkr y
    rw [hg]
    refine (abs_Jp_sub_sub_le hq0 hq1 hc' hd' hmem1 hmem2).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hL0
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (k.abs_apply_le_norm y) 2
  have hint1 : Integrable (fun y => Jp q (u y + k y)) unitμ := integrable_Jp_comp hq0 hq1 (u + k)
  have hint2 : Integrable (fun y => Jp q (u y)) unitμ := integrable_Jp_comp hq0 hq1 u
  have hint3 : Integrable (fun y => g y * k y) unitμ := (g * k).integrable
  have heq : entropyE q (u + k) - entropyE q u - (BddMeas.integ.comp (BddMeas.mulLeftCLM g)) k
      = ∫ y, (Jp q (u y + k y) - Jp q (u y) - g y * k y) ∂unitμ := by
    have e1 : ∫ y, (Jp q (u y + k y) - Jp q (u y) - g y * k y) ∂unitμ
        = (∫ y, (Jp q (u y + k y) - Jp q (u y)) ∂unitμ) - ∫ y, g y * k y ∂unitμ :=
      integral_sub (hint1.sub hint2) hint3
    have e2 : ∫ y, (Jp q (u y + k y) - Jp q (u y)) ∂unitμ
        = (∫ y, Jp q (u y + k y) ∂unitμ) - ∫ y, Jp q (u y) ∂unitμ := integral_sub hint1 hint2
    rw [e1, e2]
    simp only [entropyE, ContinuousLinearMap.comp_apply, BddMeas.mulLeftCLM_apply,
      BddMeas.integ_apply, BddMeas.add_apply, BddMeas.mul_apply]
  rw [heq]
  calc |∫ y, (Jp q (u y + k y) - Jp q (u y) - g y * k y) ∂unitμ|
      ≤ ∫ y, |Jp q (u y + k y) - Jp q (u y) - g y * k y| ∂unitμ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, L * ‖k‖ ^ 2 ∂unitμ :=
        integral_mono ((hint1.sub hint2).sub hint3).abs (integrable_const _) hpt
    _ = L * ‖k‖ ^ 2 := by simp

/-- **The first variation of `ℱ_W`** at a function with values in `[c,d] ⊆ (0,1)`:
`Dℱ_W(u)[k] = ∫ g k` with `g = 2J_q'(u) - 2α - μ∇ℛ_W(u)`. -/
theorem hasFDerivAt_rowFunctionalE (hq0 : 0 < q) (hq1 : q < 1) {c d : ℝ} (hc : 0 < c)
    (hd : d < 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d) {g : BddMeas}
    (hg : ∀ y, g y = 2 * Jp' q (u y) - 2 * α - μ * gradE H W u y) :
    HasFDerivAt (rowFunctionalE H W q α μ) (BddMeas.integ.comp (BddMeas.mulLeftCLM g)) u := by
  set gJ : BddMeas := (1 / 2 : ℝ) • (g + algebraMap ℝ BddMeas (2 * α) + μ • gradE H W u)
    with hgJ
  have hgJ' : ∀ y, gJ y = Jp' q (u y) := by
    intro y
    rw [hgJ, BddMeas.smul_apply, BddMeas.add_apply, BddMeas.add_apply, hg, BddMeas.smul_apply,
      BddMeas.coe_algebraMap]
    ring
  have h1 := hasFDerivAt_entropyE hq0 hq1 hc hd hu hgJ'
  have h2 := BddMeas.integ.hasFDerivAt (x := u)
  have h3 := hasFDerivAt_rootedE (H := H) (W := W) u
  have h := ((h1.const_smul (2:ℝ)).sub (h2.const_smul (2 * α))).sub (h3.const_smul μ)
  have hfun : rowFunctionalE H W q α μ
      = fun u => (2:ℝ) • entropyE q u - (2 * α) • BddMeas.integ u - μ • rootedE H W u := by
    funext u; rw [rowFunctionalE_eq]; simp only [smul_eq_mul]
  rw [hfun]
  refine h.congr_fderiv ?_
  ext k
  simp only [_root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, BddMeas.mulLeftCLM_apply, smul_eq_mul]
  rw [BddMeas.integ_apply, BddMeas.integ_apply, BddMeas.integ_apply, BddMeas.integ_apply,
    ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub, ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [BddMeas.mul_apply, hgJ', hg]
    ring
  · exact ((gJ * k).integrable.const_mul 2).sub (k.integrable.const_mul _)
  · exact (gradE H W u * k).integrable.const_mul _
  · exact (gJ * k).integrable.const_mul 2
  · exact k.integrable.const_mul _

/-- The derivative of `t ↦ ∫ J_q'(u + tk) k` at `t = 0`. -/
theorem hasDerivAt_integral_Jp'_line (hq0 : 0 < q) (hq1 : q < 1) {c d : ℝ} (hc : 0 < c)
    (hd : d < 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d) (k : BddMeas) :
    HasDerivAt (fun t : ℝ => ∫ y, Jp' q (u y + t * k y) * k y ∂unitμ)
      (∫ y, Jp'' (u y) * k y ^ 2 ∂unitμ) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  set r := min c (1 - d) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hc (by linarith))
  have hc' : 0 < c - r := by
    have : r ≤ c / 2 := by rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    linarith
  have hd' : d + r < 1 := by
    have : r ≤ (1 - d) / 2 := by
      rw [hr]; exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
    linarith
  set L := 1 / ((c - r) * (1 - (d + r))) ^ 2 with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  -- boundedness of `J_q'` and `J_q''` on `[c - r, d + r]`
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := c - r) (b := d + r)).exists_bound_of_continuousOn
    (f := Jp' q) (fun z hz => (hasDerivAt_Jp' hq0 hq1 (hc'.trans_le hz.1)
      (hz.2.trans_lt hd')).continuousAt.continuousWithinAt)
  have hmeasJ' : Measurable (Jp' q) := by unfold Jp'; fun_prop
  have hmeasJ'' : Measurable Jp'' := by unfold Jp''; fun_prop
  refine IsBigO.trans_isLittleO (g := fun t : ℝ => ‖t‖ ^ 2) ?_ (isLittleO_norm_pow_id one_lt_two)
  refine IsBigO.of_bound (L * ‖k‖ ^ 3) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hr0 (by positivity : (0:ℝ) < ‖k‖ + 1))]
    with t ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
  have htk : ∀ y, |t * k y| ≤ r := by
    intro y
    rw [abs_mul]
    calc |t| * |k y| ≤ r / (‖k‖ + 1) * (‖k‖ + 1) :=
          mul_le_mul ht.le ((k.abs_apply_le_norm y).trans (by linarith)) (abs_nonneg _)
            (by positivity)
      _ = r := div_mul_cancel₀ _ (by positivity)
  have hmem1 : ∀ y, u y ∈ Set.Icc (c - r) (d + r) := fun y =>
    ⟨by linarith [(hu y).1], by linarith [(hu y).2]⟩
  have hmem2 : ∀ y, u y + t * k y ∈ Set.Icc (c - r) (d + r) := fun y => by
    have h := abs_le.mp (htk y)
    exact ⟨by linarith [(hu y).1, h.1], by linarith [(hu y).2, h.2]⟩
  have hbd : ∀ z ∈ Set.Icc (c - r) (d + r), |Jp' q z| ≤ C₁ := fun z hz => by
    have := hC₁ z hz; rwa [Real.norm_eq_abs] at this
  have hint1 : Integrable (fun y => Jp' q (u y + t * k y) * k y) unitμ :=
    integrable_of_abs_le ((hmeasJ'.comp (u.measurable.add (k.measurable.const_mul t))).mul
      k.measurable) (C₁ * ‖k‖) fun y => by
        rw [abs_mul]
        exact mul_le_mul (hbd _ (hmem2 y)) (k.abs_apply_le_norm y) (abs_nonneg _)
          ((abs_nonneg _).trans (hbd _ (hmem2 y)))
  have hint2 : Integrable (fun y => Jp' q (u y) * k y) unitμ :=
    integrable_of_abs_le ((hmeasJ'.comp u.measurable).mul k.measurable) (C₁ * ‖k‖) fun y => by
      rw [abs_mul]
      exact mul_le_mul (hbd _ (hmem1 y)) (k.abs_apply_le_norm y) (abs_nonneg _)
        ((abs_nonneg _).trans (hbd _ (hmem1 y)))
  have hint3 : Integrable (fun y => Jp'' (u y) * k y ^ 2) unitμ :=
    integrable_of_abs_le ((hmeasJ''.comp u.measurable).mul (k.measurable.pow_const 2))
      (1 / (c * (1 - d)) * ‖k‖ ^ 2) fun y => by
        rw [abs_mul, abs_pow]
        have hJ := Jp''_mem_of_mem_Icc hc hd (hu y)
        rw [abs_of_pos hJ.1]
        exact mul_le_mul hJ.2 (pow_le_pow_left₀ (abs_nonneg _) (k.abs_apply_le_norm y) 2)
          (by positivity) (hJ.1.le.trans hJ.2)
  have e1 : ∫ y, (Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y
        - t * (Jp'' (u y) * k y ^ 2)) ∂unitμ
      = (∫ y, (Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y) ∂unitμ)
        - ∫ y, t * (Jp'' (u y) * k y ^ 2) ∂unitμ :=
    integral_sub (hint1.sub hint2) (hint3.const_mul t)
  have e2 : ∫ y, (Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y) ∂unitμ
      = (∫ y, Jp' q (u y + t * k y) * k y ∂unitμ) - ∫ y, Jp' q (u y) * k y ∂unitμ :=
    integral_sub hint1 hint2
  have e3 : ∫ y, t * (Jp'' (u y) * k y ^ 2) ∂unitμ = t * ∫ y, Jp'' (u y) * k y ^ 2 ∂unitμ :=
    integral_const_mul t _
  simp only [zero_mul, add_zero, zero_add, smul_eq_mul, Real.norm_eq_abs, norm_pow, sq_abs]
  rw [← e3, ← e2, ← e1]
  have hpt : ∀ y, |Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y - t * (Jp'' (u y) * k y ^ 2)|
      ≤ L * ‖k‖ ^ 3 * t ^ 2 := by
    intro y
    have h := abs_Jp'_sub_sub_le hq0 hq1 hc' hd' (hmem1 y) (hmem2 y)
    have heq : Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y - t * (Jp'' (u y) * k y ^ 2)
        = (Jp' q (u y + t * k y) - Jp' q (u y) - Jp'' (u y) * (t * k y)) * k y := by ring
    rw [heq, abs_mul]
    calc |Jp' q (u y + t * k y) - Jp' q (u y) - Jp'' (u y) * (t * k y)| * |k y|
        ≤ L * (t * k y) ^ 2 * ‖k‖ :=
          mul_le_mul h (k.abs_apply_le_norm y) (abs_nonneg _) (by positivity)
      _ = L * t ^ 2 * (k y ^ 2 * ‖k‖) := by ring
      _ ≤ L * t ^ 2 * (‖k‖ ^ 2 * ‖k‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
            (by positivity)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (k.abs_apply_le_norm y) 2
      _ = L * ‖k‖ ^ 3 * t ^ 2 := by ring
  calc |∫ y, (Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y - t * (Jp'' (u y) * k y ^ 2)) ∂unitμ|
      ≤ ∫ y, |Jp' q (u y + t * k y) * k y - Jp' q (u y) * k y - t * (Jp'' (u y) * k y ^ 2)|
          ∂unitμ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, L * ‖k‖ ^ 3 * t ^ 2 ∂unitμ :=
        integral_mono ((hint1.sub hint2).sub (hint3.const_mul t)).abs (integrable_const _) hpt
    _ = L * ‖k‖ ^ 3 * t ^ 2 := by simp

variable (H W μ) in
/-- **The second variation** `Q_u(h) = 2∫J_q''(u)h² - μ∫D∇ℛ_W(u)[h] h`. -/
noncomputable def secondVariation (u h : BddMeas) : ℝ :=
  2 * ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ - μ * BddMeas.integ (gradDeriv H W u h * h)

/-- **Second-order necessary condition**: at a global minimizer of `ℱ_W` over rows, with values
in `[c,d] ⊆ (0,1)` and satisfying `eq:row-euler` everywhere, `Q_u(h) ≥ 0` for every bounded
measurable `h`. -/
theorem secondVariation_nonneg (hq0 : 0 < q) (hq1 : q < 1) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE H W q α μ u ≤ rowFunctionalE H W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = μ * gradE H W u y) (h : BddMeas) :
    0 ≤ secondVariation H W μ u h := by
  set r := min c (1 - d) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hc (by linarith))
  have hc' : 0 < c - r := by
    have : r ≤ c / 2 := by rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    linarith
  have hd' : d + r < 1 := by
    have : r ≤ (1 - d) / 2 := by
      rw [hr]; exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
    linarith
  set t₀ := r / (‖h‖ + 1) with ht₀
  have ht₀pos : 0 < t₀ := div_pos hr0 (by positivity)
  have hnorm : ∀ t : ℝ, |t| < t₀ → ‖t • h‖ ≤ r := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖h‖ ≤ t₀ * (‖h‖ + 1) := mul_le_mul ht.le (by linarith) (norm_nonneg _) ht₀pos.le
      _ = r := div_mul_cancel₀ _ (by positivity)
  have hmemt : ∀ t : ℝ, |t| < t₀ → ∀ y, (u + t • h) y ∈ Set.Icc (c - r) (d + r) :=
    fun t ht => add_mem_Icc_of_norm_le hu (hnorm t ht)
  -- `J_q'` along the line, as an element of `BddMeas`
  have hJex : ∀ t : ℝ, |t| < t₀ → ∃ G : BddMeas, ∀ y, G y = Jp' q ((u + t • h) y) := by
    intro t ht
    obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := c - r) (b := d + r)).exists_bound_of_continuousOn
      (f := Jp' q) (fun z hz => (hasDerivAt_Jp' hq0 hq1 (hc'.trans_le hz.1)
        (hz.2.trans_lt hd')).continuousAt.continuousWithinAt)
    have hmeasJ' : Measurable (Jp' q) := by unfold Jp'; fun_prop
    refine ⟨BddMeas.mk (fun y => Jp' q ((u + t • h) y))
      (hmeasJ'.comp (u + t • h).measurable) C₁ (fun y => ?_), fun y => rfl⟩
    have := hC₁ _ (hmemt t ht y); rwa [Real.norm_eq_abs] at this
  choose! G hG using hJex
  set g : ℝ → BddMeas := fun t =>
    (2:ℝ) • G t - algebraMap ℝ BddMeas (2 * α) - μ • gradE H W (u + t • h) with hgdef
  have hg : ∀ t, |t| < t₀ → ∀ y,
      g t y = 2 * Jp' q ((u + t • h) y) - 2 * α - μ * gradE H W (u + t • h) y := by
    intro t ht y
    rw [hgdef]
    simp only [BddMeas.sub_apply, BddMeas.smul_apply, BddMeas.coe_algebraMap, hG t ht y]
  set φ : ℝ → ℝ := fun t => rowFunctionalE H W q α μ (u + t • h) with hφ
  set ψ : ℝ → ℝ := fun t => 2 * (∫ y, Jp' q (u y + t * h y) * h y ∂unitμ)
    - 2 * α * BddMeas.integ h - μ * BddMeas.integ (gradE H W (u + t • h) * h) with hψ
  have hψeq : ∀ t, |t| < t₀ → BddMeas.integ (g t * h) = ψ t := by
    intro t ht
    have hGh : BddMeas.integ (G t * h) = ∫ y, Jp' q (u y + t * h y) * h y ∂unitμ := by
      rw [BddMeas.integ_apply]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      rw [BddMeas.mul_apply, hG t ht y]
      rfl
    have hsplit : g t * h
        = (2:ℝ) • (G t * h) - (2 * α) • h - μ • (gradE H W (u + t • h) * h) := by
      rw [hgdef]
      ext y
      simp only [BddMeas.mul_apply, BddMeas.sub_apply, BddMeas.smul_apply,
        BddMeas.coe_algebraMap]
      ring
    rw [hsplit, map_sub, map_sub, map_smul, map_smul, map_smul, hGh, hψ]
    simp only [smul_eq_mul]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u + t • h) h t := by
    intro t
    have := ((hasDerivAt_id t).smul_const h).const_add u
    simpa using this
  have hφderiv : ∀ t, |t| < t₀ → HasDerivAt φ (ψ t) t := by
    intro t ht
    have hF := hasFDerivAt_rowFunctionalE (H := H) (W := W) (α := α) (μ := μ) hq0 hq1 hc' hd'
      (hmemt t ht) (hg t ht)
    have hcomp := hF.comp_hasDerivAt t (hline t)
    rw [← hψeq t ht]
    exact hcomp
  have hu0 : u + (0:ℝ) • h = u := by
    ext z; simp only [BddMeas.add_apply, BddMeas.smul_apply, zero_mul, add_zero]
  have hψ0 : ψ 0 = 0 := by
    rw [← hψeq 0 (by rwa [abs_zero])]
    have hg0 : g 0 = 0 := by
      ext y
      rw [hg 0 (by rwa [abs_zero]) y, BddMeas.zero_apply, hu0, hEL y]
      ring
    rw [hg0, zero_mul, map_zero]
  have hψderiv : HasDerivAt ψ (secondVariation H W μ u h) 0 := by
    have h1 := (hasDerivAt_integral_Jp'_line hq0 hq1 hc hd hu h).const_mul 2
    have h2 : HasDerivAt (fun t : ℝ => BddMeas.integ (gradE H W (u + t • h) * h))
        (BddMeas.integ (gradDeriv H W u h * h)) 0 := by
      have hgrad : HasFDerivAt (gradE H W) (gradDeriv H W u) (u + (0:ℝ) • h) := by
        rw [hu0]; exact hasFDerivAt_gradE u
      have hchain := hgrad.comp_hasDerivAt (0:ℝ) (hline 0)
      have hclm : HasFDerivAt (fun w : BddMeas => BddMeas.integ (h * w))
          (BddMeas.integ.comp (BddMeas.mulLeftCLM h))
          (gradE H W (u + (0:ℝ) • h)) :=
        (BddMeas.integ.comp (BddMeas.mulLeftCLM h)).hasFDerivAt
      have hres := hclm.comp_hasDerivAt (0:ℝ) hchain
      have hfun : (fun t : ℝ => BddMeas.integ (h * gradE H W (u + t • h)))
          = fun t : ℝ => BddMeas.integ (gradE H W (u + t • h) * h) := by
        funext t; rw [mul_comm]
      simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
        BddMeas.mulLeftCLM_apply] at hres
      rw [hfun] at hres
      rw [mul_comm]
      exact hres
    have h3 := (h1.sub_const (2 * α * BddMeas.integ h)).sub (h2.const_mul μ)
    rw [secondVariation]
    exact h3
  refine nonneg_of_isLocalMin_deriv ht₀pos (fun t ht => ?_) hφderiv hψ0 hψderiv
  have h0 : φ 0 = rowFunctionalE H W q α μ u := by
    rw [hφ]; simp only [hu0]
  rw [h0]
  exact hmin _ fun y => by
    have hm := hmemt t ht y
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

end UpperTailMultipodality
