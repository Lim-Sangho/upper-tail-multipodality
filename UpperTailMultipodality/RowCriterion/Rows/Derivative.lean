import UpperTailMultipodality.RowCriterion.Rows.Resampling

/-!
# First variation of the row functional along bounded directions

For a row `u` and a bounded measurable direction `h`:

* `hasDerivAt_totalRootedDensity_line` — `t ↦ ℛ_W(u + t h)` has derivative `∫ ∇ℛ_W(u) h`
  at `t = 0`;
* `hasDerivAt_integral_Jp_line` — if `u ∈ [δ, 1-δ]` wherever `h ≠ 0`, then
  `t ↦ ∫ J_q(u + t h)` has derivative `∫ J_q'(u) h` at `t = 0`.
-/

namespace UpperTailMultipodality.Rows

open MeasureTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A finite product of factors bounded by `2` in absolute value is bounded by `2 ^ card`. -/
theorem abs_prod_le_two_pow {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ 2) : |∏ i ∈ S, f i| ≤ 2 ^ S.card := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hf

/-- **The first variation of one rooted density.**  For a row `u` and a measurable `h` with
`|h| ≤ 1`, `t ↦ ℛ_{v,W}(u + t h)` has derivative `∑_{z₀ ∈ N(v)} ∫ G_{v,z₀}(u) h` at `0`. -/
theorem hasDerivAt_rootedDensity_line (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) {u h : ℝ → ℝ} (hu : IsRow u) (hh : Measurable h) (hhb : ∀ y, |h y| ≤ 1) :
    HasDerivAt (fun t : ℝ => rootedDensity H W v (fun y => u y + t * h y))
      (∑ z₀ ∈ H.neighborFinset v, ∫ y, rootedGradientTerm H W v z₀ u y * h y ∂unitμ) 0 := by
  obtain ⟨N, hN⟩ : ∃ N, N = H.neighborFinset v := ⟨_, rfl⟩
  have hub : ∀ y, |u y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hu.2 y).1]; exact (hu.2 y).2
  -- the integrand and its `t`-derivative
  let F : ℝ → (V → ℝ) → ℝ := fun t ξ =>
    (∏ z ∈ N, (u (ξ z) + t * h (ξ z))) * avoidingProduct H W v ξ
  let F' : ℝ → (V → ℝ) → ℝ := fun t ξ =>
    (∑ z₀ ∈ N, (∏ z ∈ N.erase z₀, (u (ξ z) + t * h (ξ z))) * h (ξ z₀))
      * avoidingProduct H W v ξ
  have hderiv : ∀ ξ t, HasDerivAt (fun t => F t ξ) (F' t ξ) t := by
    intro ξ t
    have hprod := HasDerivAt.fun_finsetProd (u := N)
      (f := fun z t => u (ξ z) + t * h (ξ z)) (f' := fun z => h (ξ z)) (x := t)
      (fun z _ => by
        simpa using ((hasDerivAt_id t).mul_const (h (ξ z))).const_add (u (ξ z)))
    simpa [F, F', smul_eq_mul] using hprod.mul_const (avoidingProduct H W v ξ)
  have hfac : ∀ ξ : V → ℝ, ∀ t ∈ Metric.ball (0:ℝ) 1, ∀ z, |u (ξ z) + t * h (ξ z)| ≤ 2 := by
    intro ξ t ht z
    have ht' : |t| < 1 := by simpa using ht
    calc |u (ξ z) + t * h (ξ z)| ≤ |u (ξ z)| + |t| * |h (ξ z)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 + 1 * 1 :=
          add_le_add (hub _) (mul_le_mul ht'.le (hhb _) (abs_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  have hbound : ∀ ξ : V → ℝ, ∀ t ∈ Metric.ball (0:ℝ) 1,
      ‖F' t ξ‖ ≤ N.card * 2 ^ N.card := by
    intro ξ t ht
    have hA := avoidingProduct_mem_Icc H W v ξ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA.1]
    calc |∑ z₀ ∈ N, (∏ z ∈ N.erase z₀, (u (ξ z) + t * h (ξ z))) * h (ξ z₀)|
          * avoidingProduct H W v ξ
        ≤ |∑ z₀ ∈ N, (∏ z ∈ N.erase z₀, (u (ξ z) + t * h (ξ z))) * h (ξ z₀)| * 1 :=
          mul_le_mul_of_nonneg_left hA.2 (abs_nonneg _)
      _ ≤ ∑ _z₀ ∈ N, (2:ℝ) ^ N.card := by
          rw [mul_one]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ _ => ?_)
          rw [abs_mul]
          calc |∏ z ∈ N.erase z₀, (u (ξ z) + t * h (ξ z))| * |h (ξ z₀)|
              ≤ 2 ^ (N.erase z₀).card * 1 :=
                mul_le_mul (abs_prod_le_two_pow _ _ fun z _ => hfac ξ t ht z) (hhb _)
                  (abs_nonneg _) (by positivity)
            _ ≤ 2 ^ N.card := by
                rw [mul_one]
                exact pow_le_pow_right₀ (by norm_num) (Finset.card_erase_le)
      _ = N.card * 2 ^ N.card := by simp
  have hmeasF : ∀ t, Measurable (F t) := fun t =>
    (Finset.measurable_prod _ fun z _ =>
      (hu.1.comp (measurable_pi_apply z)).add
        ((hh.comp (measurable_pi_apply z)).const_mul t)).mul
      (measurable_avoidingProduct H W v)
  have hmeasF' : Measurable (F' 0) :=
    (Finset.measurable_sum _ fun z₀ _ =>
      (Finset.measurable_prod _ fun z _ =>
        (hu.1.comp (measurable_pi_apply z)).add
          ((hh.comp (measurable_pi_apply z)).const_mul 0)).mul
        (hh.comp (measurable_pi_apply z₀))).mul
      (measurable_avoidingProduct H W v)
  have hint0 : Integrable (F 0) (Measure.pi fun _ : V => unitμ) := by
    refine integrable_pi_of_abs_le (hmeasF 0) (2 ^ N.card) fun ξ => ?_
    have hA := avoidingProduct_mem_Icc H W v ξ
    rw [abs_mul, abs_of_nonneg hA.1]
    calc |∏ z ∈ N, (u (ξ z) + 0 * h (ξ z))| * avoidingProduct H W v ξ
        ≤ 2 ^ N.card * 1 :=
          mul_le_mul (abs_prod_le_two_pow _ _ fun z _ => hfac ξ 0 (by simp) z) hA.2 hA.1
            (by positivity)
      _ = 2 ^ N.card := mul_one _
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Measure.pi fun _ : V => unitμ) (F := F) (F' := F') (x₀ := 0)
    (bound := fun _ => (N.card : ℝ) * 2 ^ N.card) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable) hint0
    hmeasF'.aestronglyMeasurable (Eventually.of_forall fun ξ t ht => hbound ξ t ht)
    (integrable_const _) (Eventually.of_forall fun ξ t _ => hderiv ξ t)
  -- identify the derivative
  have hval : ∫ ξ, F' 0 ξ ∂(Measure.pi fun _ : V => unitμ)
      = ∑ z₀ ∈ N, ∫ y, rootedGradientTerm H W v z₀ u y * h y ∂unitμ := by
    have hpt : ∀ ξ : V → ℝ, F' 0 ξ = ∑ z₀ ∈ N,
        h (ξ z₀) * ((∏ z ∈ N.erase z₀, u (ξ z)) * avoidingProduct H W v ξ) := by
      intro ξ
      simp only [F', zero_mul, add_zero, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z₀ _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_finsetSum _ fun z₀ _ => ?_]
    · refine Finset.sum_congr rfl fun z₀ _ => ?_
      have hmeasG := measurable_rootedIntegrand H W v hu.1 (N.erase z₀)
      have hbG : ∀ ξ : V → ℝ,
          |(∏ z ∈ N.erase z₀, u (ξ z)) * avoidingProduct H W v ξ| ≤ 1 := fun ξ => by
        have hI := rootedIntegrand_mem_Icc H W v hu.2 (N.erase z₀) ξ ξ
        rw [abs_of_nonneg hI.1]; exact hI.2
      rw [← integral_mul_update z₀ hmeasG hh hbG hhb, hN]
      rfl
    · refine integrable_pi_of_abs_le ((hh.comp (measurable_pi_apply z₀)).mul
        (measurable_rootedIntegrand H W v hu.1 (N.erase z₀))) 1 fun ξ => ?_
      have hI := rootedIntegrand_mem_Icc H W v hu.2 (N.erase z₀) ξ ξ
      rw [abs_mul, abs_of_nonneg hI.1]
      calc |h (ξ z₀)| * ((∏ z ∈ N.erase z₀, u (ξ z)) * avoidingProduct H W v ξ)
          ≤ 1 * 1 := mul_le_mul (hhb _) hI.2 hI.1 zero_le_one
        _ = 1 := one_mul 1
  rw [hval, hN] at hD
  subst hN
  exact hD

/-- **The first variation of `ℛ_W`.**  For a row `u` and a measurable `h` with `|h| ≤ 1`,
`t ↦ ℛ_W(u + t h)` has derivative `∫ ∇ℛ_W(u) h` at `0`. -/
theorem hasDerivAt_totalRootedDensity_line (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) {u h : ℝ → ℝ} (hu : IsRow u) (hh : Measurable h) (hhb : ∀ y, |h y| ≤ 1) :
    HasDerivAt (fun t : ℝ => totalRootedDensity H W (fun y => u y + t * h y))
      (∫ y, rootedGradient H W u y * h y ∂unitμ) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun v t => rootedDensity H W v (fun y => u y + t * h y))
    (fun v _ => hasDerivAt_rootedDensity_line H W v hu hh hhb)
  have hint : ∀ v z₀, Integrable (fun y => rootedGradientTerm H W v z₀ u y * h y) unitμ := by
    intro v z₀
    refine integrable_of_abs_le ((measurable_rootedGradientTerm H W v z₀ hu.1).mul hh) 1
      fun y => ?_
    have hG := rootedGradientTerm_mem_Icc H W v z₀ hu.2 y
    rw [abs_mul, abs_of_nonneg hG.1]
    calc rootedGradientTerm H W v z₀ u y * |h y| ≤ 1 * 1 :=
          mul_le_mul hG.2 (hhb y) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hval : ∫ y, rootedGradient H W u y * h y ∂unitμ
      = ∑ v, ∑ z₀ ∈ H.neighborFinset v, ∫ y, rootedGradientTerm H W v z₀ u y * h y ∂unitμ := by
    unfold rootedGradient
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun z₀ _ => hint v z₀]
    exact Finset.sum_congr rfl fun v _ => integral_finsetSum _ fun z₀ _ => hint v z₀
  rw [hval]
  exact hsum

/-! ## The entropy term -/

/-- `J_q'` is measurable. -/
theorem measurable_Jp' (q : ℝ) : Measurable (Jp' q) := by
  unfold Jp'
  fun_prop

/-- `J_q` is bounded on `[0,1]`. -/
theorem exists_abs_Jp_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ C, ∀ z ∈ Set.Icc (0:ℝ) 1, |Jp q z| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Jp_Icc hq0 hq1)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

/-- `J_q'` is bounded on every compact subinterval `[a,b]` of `(0,1)`. -/
theorem exists_abs_Jp'_le {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 < a) (hb : b < 1) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ Set.Icc a b, |Jp' q z| ≤ C := by
  have hcont : ContinuousOn (Jp' q) (Set.Icc a b) := fun z hz =>
    (hasDerivAt_Jp' hq0 hq1 (ha.trans_le hz.1) (hz.2.trans_lt hb)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  exact (by simpa [Real.norm_eq_abs] using hC z hz : |Jp' q z| ≤ C).trans (le_max_left _ _)

/-- For a row `u`, `J_q ∘ u` is integrable. -/
theorem integrable_Jp_row {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ → ℝ} (hu : IsRow u) :
    Integrable (fun y => Jp q (u y)) unitμ := by
  obtain ⟨C, hC⟩ := exists_abs_Jp_le hq0 hq1
  exact integrable_of_abs_le ((measurable_Jp q).comp hu.1) C fun y => hC _ (hu.2 y)

/-- **The first variation of `∫ J_q(u)`.**  If `u` is a row, `|h| ≤ 1`, and `δ ≤ u ≤ 1-δ`
wherever `h ≠ 0`, then `t ↦ ∫ J_q(u + t h)` has derivative `∫ J_q'(u) h` at `0`. -/
theorem hasDerivAt_integral_Jp_line {q δ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ)
    {u h : ℝ → ℝ} (hu : IsRow u) (hh : Measurable h) (hhb : ∀ y, |h y| ≤ 1)
    (hsupp : ∀ y, h y ≠ 0 → δ ≤ u y ∧ u y ≤ 1 - δ) :
    HasDerivAt (fun t : ℝ => ∫ y, Jp q (u y + t * h y) ∂unitμ)
      (∫ y, Jp' q (u y) * h y ∂unitμ) 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_Jp'_le (a := δ / 2) (b := 1 - δ / 2) hq0 hq1
    (by linarith) (by linarith)
  -- where `h ≠ 0`, the perturbed values stay in `[δ/2, 1-δ/2]`
  have hmem : ∀ y, h y ≠ 0 → ∀ t ∈ Metric.ball (0:ℝ) (δ / 2),
      u y + t * h y ∈ Set.Icc (δ / 2) (1 - δ / 2) := by
    intro y hy t ht
    have ht' : |t| < δ / 2 := by simpa using ht
    have hth : |t * h y| ≤ δ / 2 := by
      rw [abs_mul]
      calc |t| * |h y| ≤ δ / 2 * 1 := mul_le_mul ht'.le (hhb y) (abs_nonneg _) (by linarith)
        _ = δ / 2 := mul_one _
    have h1 := (abs_le.mp hth).1
    have h2 := (abs_le.mp hth).2
    obtain ⟨hu1, hu2⟩ := hsupp y hy
    exact ⟨by linarith, by linarith⟩
  have hderiv : ∀ y, ∀ t ∈ Metric.ball (0:ℝ) (δ / 2),
      HasDerivAt (fun t => Jp q (u y + t * h y)) (Jp' q (u y + t * h y) * h y) t := by
    intro y t ht
    by_cases hy : h y = 0
    · rw [hy]
      simpa using hasDerivAt_const t (Jp q (u y))
    · have hz := hmem y hy t ht
      have hin : HasDerivAt (fun t => u y + t * h y) (h y) t := by
        simpa using ((hasDerivAt_id t).mul_const (h y)).const_add (u y)
      exact (hasDerivAt_Jp hq0 hq1 (by linarith [hz.1]) (by linarith [hz.2])).comp t hin
  have hbound : ∀ y, ∀ t ∈ Metric.ball (0:ℝ) (δ / 2), ‖Jp' q (u y + t * h y) * h y‖ ≤ C := by
    intro y t ht
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : h y = 0
    · rw [hy]; simpa using hC0
    · calc |Jp' q (u y + t * h y)| * |h y| ≤ C * 1 :=
            mul_le_mul (hC _ (hmem y hy t ht)) (hhb y) (abs_nonneg _) hC0
        _ = C := mul_one C
  have hmeasF : ∀ t : ℝ, Measurable fun y => Jp q (u y + t * h y) := fun t =>
    (measurable_Jp q).comp (hu.1.add (hh.const_mul t))
  have hint0 : Integrable (fun y => Jp q (u y + 0 * h y)) unitμ := by
    simpa using integrable_Jp_row hq0 hq1 hu
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := unitμ) (F := fun t y => Jp q (u y + t * h y))
    (F' := fun t y => Jp' q (u y + t * h y) * h y) (x₀ := 0) (bound := fun _ => C)
    (Metric.ball_mem_nhds 0 (by linarith : (0:ℝ) < δ / 2))
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable) hint0
    (((measurable_Jp' q).comp (hu.1.add (hh.const_mul 0))).mul hh).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => hbound y t ht) (integrable_const _)
    (Eventually.of_forall fun y t ht => hderiv y t ht)
  simpa using hD

end UpperTailMultipodality.Rows
