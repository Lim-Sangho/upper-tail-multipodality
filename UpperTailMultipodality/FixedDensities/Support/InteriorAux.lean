import UpperTailMultipodality.FixedDensities.Support.Perturb

/-!
# The cost estimate behind `lem:fixed-interior`

`interior_side_null`: for a minimizer `W` satisfying the constraint qualification there is a
threshold `N` such that no symmetric set `E` of positive measure, disjoint from the supports of
`U₁, U₂`, can have the property that moving `W` by `σθ` on `E` (with `|σ| = 1`) lowers `J_ε` by at
least `Nθ` pointwise.  Indeed, inserting `σθ 1_E` and restoring both constraints along `U₁, U₂`
(`exists_correction`) would lower `I_ε` by `θ|E|/2` to first order.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Pointwise Taylor bound on the support of the corrections.** -/
theorem Jp_sub_le_of_mem_Ioo {ε η L w h q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (hL : ∀ u ∈ Icc (η / 2) (1 - η / 2), |Jp' ε u| ≤ L) (hw : w ∈ Ioo η (1 - η))
    (hh : |h| ≤ q) (hq : q ≤ η / 2) :
    w + h ∈ Icc (0:ℝ) 1 ∧
      Jp ε (w + h) - Jp ε w ≤ L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2 := by
  have hh' := abs_le.mp hh
  have hx : w + h ∈ Icc (η / 2) (1 - η / 2) := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hy : w ∈ Icc (η / 2) (1 - η / 2) := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  refine ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  have ht := (abs_le.mp (Jp_taylor_box (half_pos hη) hε0 hε1 hx hy)).2
  have hM0 : 0 ≤ 1 / ((η / 2) * (1 - η / 2)) := by
    have : 0 < 1 - η / 2 := by linarith [hw.1, hw.2]
    positivity
  have hq0 : 0 ≤ q := (abs_nonneg _).trans hh
  have h1 : Jp' ε w * (w + h - w) ≤ L * q := by
    rw [show w + h - w = h by ring]
    calc Jp' ε w * h ≤ |Jp' ε w * h| := le_abs_self _
      _ = |Jp' ε w| * |h| := abs_mul _ _
      _ ≤ L * q := mul_le_mul (hL w hy) hh (abs_nonneg _) ((abs_nonneg _).trans (hL w hy))
  have h2 : (w + h - w) ^ 2 ≤ q ^ 2 := by
    rw [show w + h - w = h by ring, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hh 2
  nlinarith [mul_le_mul_of_nonneg_left h2 hM0]

/-- **The cost of inserting `σθ 1_E` and correcting.**  If `W` is a minimizer, `E` is disjoint
from the supports of `U₁, U₂`, moving `W` by `σθ` on `E` lowers `J_ε` by at least `Nθ`, and
the correction `ξ₁U₁ + ξ₂U₂` of size `q ≤ η/2` restores both constraints, then
`0 ≤ -Nθ|E| + Lq + Mq²`. -/
theorem interior_cost_nonneg (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {W : Graphon} (hW : IsFixedMinimizer H ε τ W) {η : ℝ} (hη : 0 < η)
    (hη2 : η < 1 / 2) {U₁ U₂ Z : Kernel} (hU₁ : SupportedIn W η U₁) (hU₂ : SupportedIn W η U₂)
    {C₁ C₂ L N q : ℝ} (hC₁ : ∀ x y, |U₁.toFun x y| ≤ C₁) (hC₂ : ∀ x y, |U₂.toFun x y| ≤ C₂)
    (hL0 : 0 ≤ L) (hL : ∀ u ∈ Icc (η / 2) (1 - η / 2), |Jp' ε u| ≤ L)
    {E : Set (ℝ × ℝ)} (hEm : MeasurableSet E) {σ θ ξ₁ ξ₂ : ℝ}
    (hZ : ∀ x y, Z.toFun x y = E.indicator (fun _ => σ) (x, y))
    (hEU : ∀ z ∈ E, U₁.toFun z.1 z.2 = 0 ∧ U₂.toFun z.1 z.2 = 0)
    (hEJ : ∀ z ∈ E, W.toFun z.1 z.2 + σ * θ ∈ Icc (0:ℝ) 1 ∧
        Jp ε (W.toFun z.1 z.2 + σ * θ) - Jp ε (W.toFun z.1 z.2) ≤ -(N * θ))
    (hq0 : 0 ≤ q) (hqξ : |ξ₁| * C₁ + |ξ₂| * C₂ ≤ q) (hq : q ≤ η / 2)
    (hce : (corrKernel W Z U₁ U₂ θ ξ₁ ξ₂).edgeDensity = W.edgeDensity)
    (hct : (corrKernel W Z U₁ U₂ θ ξ₁ ξ₂).tDensity H = W.tDensity H) :
    0 ≤ gμ.real E * -(N * θ) + (L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2) := by
  obtain ⟨he, ht, hmin⟩ := hW
  have hM0 : 0 ≤ 1 / ((η / 2) * (1 - η / 2)) := by
    have : 0 < 1 - η / 2 := by linarith
    positivity
  have hpt : ∀ x y, (corrKernel W Z U₁ U₂ θ ξ₁ ξ₂).toFun x y ∈ Icc (0:ℝ) 1 ∧
      Jp ε ((corrKernel W Z U₁ U₂ θ ξ₁ ξ₂).toFun x y) - Jp ε (W.toFun x y)
        ≤ E.indicator (fun _ => -(N * θ)) (x, y)
          + (L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2) := by
    intro x y
    have hLqM : 0 ≤ L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2 := by positivity
    rw [corrKernel_apply, hZ]
    by_cases hxy : (x, y) ∈ E
    · obtain ⟨hU1, hU2⟩ := hEU (x, y) hxy
      obtain ⟨hmem, hJ⟩ := hEJ (x, y) hxy
      simp only at hU1 hU2 hmem hJ
      simp only [Set.indicator_of_mem hxy, hU1, hU2, mul_zero, add_zero, mul_comm θ σ]
      exact ⟨hmem, by linarith⟩
    · simp only [Set.indicator_of_notMem hxy, mul_zero, add_zero, zero_add]
      have hh : |ξ₁ * U₁.toFun x y + ξ₂ * U₂.toFun x y| ≤ q := by
        calc |ξ₁ * U₁.toFun x y + ξ₂ * U₂.toFun x y|
            ≤ |ξ₁ * U₁.toFun x y| + |ξ₂ * U₂.toFun x y| := abs_add_le _ _
          _ = |ξ₁| * |U₁.toFun x y| + |ξ₂| * |U₂.toFun x y| := by rw [abs_mul, abs_mul]
          _ ≤ |ξ₁| * C₁ + |ξ₂| * C₂ :=
              add_le_add (mul_le_mul_of_nonneg_left (hC₁ x y) (abs_nonneg _))
                (mul_le_mul_of_nonneg_left (hC₂ x y) (abs_nonneg _))
          _ ≤ q := hqξ
      by_cases hU : U₁.toFun x y = 0 ∧ U₂.toFun x y = 0
      · simp only [hU.1, hU.2, mul_zero, add_zero, sub_self]
        exact ⟨W.mem_Icc x y, hLqM⟩
      · have hw : W.toFun x y ∈ Ioo η (1 - η) := by
          rcases not_and_or.mp hU with h | h
          · exact hU₁ x y h
          · exact hU₂ x y h
        have := Jp_sub_le_of_mem_Ioo hε0 hε1 hη hL hw hh hq
        rw [add_assoc]
        exact this
  obtain ⟨G, hG⟩ := exists_graphon_of_mem _ fun x y => (hpt x y).1
  have hGe : G.edgeDensity = ε := by
    rw [← he, ← hce]
    exact integral_congr_ae (ae_of_all _ fun z => hG z.1 z.2)
  have hGt : G.tDensity H = τ := by
    rw [← ht, ← hct, ← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H hG
  have hle : W.Ip ε ≤ G.Ip ε := hmin ▸ fixedValue_le H hε0 hε1 hGe hGt
  have hIG := G.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hIW := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hint : ∫ z, (Jp ε (G.toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)) ∂gμ
      ≤ ∫ z, (E.indicator (fun _ => -(N * θ)) z
        + (L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2)) ∂gμ :=
    integral_mono (hIG.sub hIW) (((integrable_const _).indicator hEm).add (integrable_const _))
      fun z => by rw [hG]; exact (hpt z.1 z.2).2
  rw [integral_sub hIG hIW, integral_add ((integrable_const _).indicator hEm) (integrable_const _),
    integral_indicator_const _ hEm, integral_const] at hint
  simp only [smul_eq_mul, probReal_univ, one_mul] at hint
  have h2 : G.Ip ε - W.Ip ε
      ≤ gμ.real E * -(N * θ) + (L * q + (1 / ((η / 2) * (1 - η / 2))) * q ^ 2) := hint
  linarith

/-- Arithmetic for the choice of the small parameter `δ'` in `interior_side_null`. -/
theorem interior_delta_bounds {e L C : ℝ} (he : 0 < e) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    e / (4 * (L + 1) * (C + 1)) * C ≤ e / 4 ∧ L * (e / (4 * (L + 1) * (C + 1)) * C) ≤ e / 4 := by
  have hL1 : 0 < L + 1 := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hfac1 : C / (C + 1) ≤ 1 := (div_le_one hC1).mpr (by linarith)
  have hfac2 : L / (L + 1) ≤ 1 := (div_le_one hL1).mpr (by linarith)
  have hfac3 : 1 / (L + 1) ≤ 1 := (div_le_one hL1).mpr (by linarith)
  have e1 : e / (4 * (L + 1) * (C + 1)) * C = e / 4 * (1 / (L + 1)) * (C / (C + 1)) := by
    field_simp
  have e2 : L * (e / (4 * (L + 1) * (C + 1)) * C) = e / 4 * (L / (L + 1)) * (C / (C + 1)) := by
    field_simp
  have he4 : 0 ≤ e / 4 := by positivity
  constructor
  · rw [e1]
    calc e / 4 * (1 / (L + 1)) * (C / (C + 1)) ≤ e / 4 * 1 * 1 := by
          gcongr
      _ = e / 4 := by ring
  · rw [e2]
    calc e / 4 * (L / (L + 1)) * (C / (C + 1)) ≤ e / 4 * 1 * 1 := by
          gcongr
      _ = e / 4 := by ring

/-- `|ξ| ≤ θ|v| + δθ` from `|ξ - θv| ≤ δθ`. -/
theorem abs_le_of_abs_sub_le {ξ θ v δ : ℝ} (hθ : 0 < θ) (h : |ξ - θ * v| ≤ δ * θ) :
    |ξ| ≤ θ * |v| + δ * θ := by
  calc |ξ| = |(ξ - θ * v) + θ * v| := by ring_nf
    _ ≤ |ξ - θ * v| + |θ * v| := abs_add_le _ _
    _ ≤ δ * θ + θ * |v| := by rw [abs_mul, abs_of_pos hθ]; linarith
    _ = θ * |v| + δ * θ := by ring

/-- **The interior cost estimate.** -/
theorem interior_side_null (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {W : Graphon} (hW : IsFixedMinimizer H ε τ W) {η : ℝ} (hη : 0 < η)
    {U₁ U₂ : Kernel} (hU₁ : SupportedIn W η U₁) (hU₂ : SupportedIn W η U₂)
    (hdet : cqDet H W U₁ U₂ ≠ 0) :
    ∃ N : ℝ, ∀ (E : Set (ℝ × ℝ)) (σ s : ℝ), MeasurableSet E →
      (∀ x y, (x, y) ∈ E → (y, x) ∈ E) → |σ| = 1 → 0 < s →
      (∀ z ∈ E, U₁.toFun z.1 z.2 = 0 ∧ U₂.toFun z.1 z.2 = 0) →
      (∀ z ∈ E, ∀ θ, 0 < θ → θ ≤ s → W.toFun z.1 z.2 + σ * θ ∈ Icc (0:ℝ) 1 ∧
        Jp ε (W.toFun z.1 z.2 + σ * θ) - Jp ε (W.toFun z.1 z.2) ≤ -(N * θ)) →
      gμ E = 0 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := kernel_bound U₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := kernel_bound U₂
  obtain ⟨L, hL0, hL⟩ := Jp'_bdd_box (half_pos hη) hε0 hε1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = H.edgeFinset.card := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = ∫ z, U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = ∫ z, U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = ∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, b = ∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = cqDet H W U₁ U₂ := ⟨_, rfl⟩
  have hd0 : 0 < |d| := abs_pos.mpr (hd ▸ hdet)
  obtain ⟨K, hK⟩ : ∃ K, K = ((|b₂| + m * |a₂|) * C₁ + (|b₁| + m * |a₁|) * C₂) / |d| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨M, hM⟩ : ∃ M, M = 1 / ((η / 2) * (1 - η / 2)) := ⟨_, rfl⟩
  have hη2 : η < 1 / 2 := by
    by_contra hη2
    have h0 : ∀ U : Kernel, SupportedIn W η U → ∀ x y, U.toFun x y = 0 := fun U hU x y => by
      by_contra hne
      have := hU x y hne
      linarith [this.1, this.2, not_lt.mp hη2]
    apply hdet
    simp only [cqDet, h0 U₁ hU₁, h0 U₂ hU₂, mul_zero, integral_zero, sub_self]
  have hM0 : 0 ≤ M := by
    rw [hM]; have : 0 < 1 - η / 2 := by linarith
    positivity
  refine ⟨L * K + 1, fun E σ s hEm hEsymm hσ hs hEU hEJ => ?_⟩
  by_contra hE0
  obtain ⟨e, he_def⟩ : ∃ e, e = gμ.real E := ⟨_, rfl⟩
  have he0 : 0 < e := by
    rw [he_def, measureReal_def]
    exact ENNReal.toReal_pos hE0 (measure_ne_top _ _)
  -- the direction `Z = σ 1_E` and its first variations
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = indicatorKernel E hEm hEsymm σ := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a, a = ∫ z, Z.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b, b = ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  have ha₀e : |a₀| = e := by
    rw [ha₀, hZ, integral_indicatorKernel, abs_mul, hσ, one_mul, ← he_def, abs_of_pos he0]
  have hb₀e : |b₀| ≤ m * e := by
    have hbd : ∀ z : ℝ × ℝ, |derivKernel H W z.1 z.2 * Z.toFun z.1 z.2|
        ≤ E.indicator (fun _ => m) z := by
      intro z
      rw [hZ, indicatorKernel_apply, Prod.mk.eta, abs_mul]
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hσ, mul_one, hm]
        exact abs_derivKernel_le H W _ _
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, abs_zero, mul_zero]
    calc |b₀| ≤ ∫ z, |derivKernel H W z.1 z.2 * Z.toFun z.1 z.2| ∂gμ := by
          rw [hb₀]; exact abs_integral_le_integral_abs
      _ ≤ ∫ z, E.indicator (fun _ => m) z ∂gμ :=
          integral_mono (integrable_derivKernel_mul H W Z).abs
            ((integrable_const m).indicator hEm) hbd
      _ = m * e := by rw [integral_indicator_const m hEm, smul_eq_mul, he_def, mul_comm]
  -- the correction
  obtain ⟨ξ₁, ξ₂, hξ₁0, hξ₂0, hξ₁d, hξ₂d, hev⟩ := exists_correction H W Z U₁ U₂ hdet
  simp only [← ha₀, ← hb₀, ← ha₁, ← ha₂, ← hb₁, ← hb₂, ← hd] at hξ₁d hξ₂d
  obtain ⟨v₁, hv₁⟩ : ∃ v, v = (-a₀ * b₂ + a₂ * b₀) / d := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, v = (-a₁ * b₀ + a₀ * b₁) / d := ⟨_, rfl⟩
  rw [← hv₁] at hξ₁d
  rw [← hv₂] at hξ₂d
  have hvK : |v₁| * C₁ + |v₂| * C₂ ≤ K * e := by
    have h1 : |v₁| ≤ e * (|b₂| + m * |a₂|) / |d| := by
      rw [hv₁, abs_div]
      refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
      calc |-a₀ * b₂ + a₂ * b₀| ≤ |a₀| * |b₂| + |a₂| * |b₀| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg]
        _ ≤ e * |b₂| + |a₂| * (m * e) := by
            rw [ha₀e]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hb₀e (abs_nonneg _))
        _ = e * (|b₂| + m * |a₂|) := by ring
    have h2 : |v₂| ≤ e * (|b₁| + m * |a₁|) / |d| := by
      rw [hv₂, abs_div]
      refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
      calc |-a₁ * b₀ + a₀ * b₁| ≤ |a₁| * |b₀| + |a₀| * |b₁| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg]
        _ ≤ |a₁| * (m * e) + e * |b₁| := by
            rw [ha₀e]; exact add_le_add (mul_le_mul_of_nonneg_left hb₀e (abs_nonneg _)) le_rfl
        _ = e * (|b₁| + m * |a₁|) := by ring
    calc |v₁| * C₁ + |v₂| * C₂
        ≤ e * (|b₂| + m * |a₂|) / |d| * C₁ + e * (|b₁| + m * |a₁|) / |d| * C₂ :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hC₁0) (mul_le_mul_of_nonneg_right h2 hC₂0)
      _ = K * e := by rw [hK]; field_simp
  -- small parameters
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = e / (4 * (L + 1) * (C₁ + C₂ + 1)) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  obtain ⟨hδ'C, hδ'LC⟩ := interior_delta_bounds he0 hL0 (add_nonneg hC₁0 hC₂0)
  rw [← hδ'] at hδ'C hδ'LC
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = K * e + e := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = min s (min (η / 2 / Q) (e / (4 * (M * Q ^ 2 + 1)))) := ⟨_, rfl⟩
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀]; exact lt_min hs (lt_min (by positivity) (by positivity))
  have hevξ₁ := eventually_abs_sub_le_of_hasDerivAt hξ₁d hδ'0
  have hevξ₂ := eventually_abs_sub_le_of_hasDerivAt hξ₂d hδ'0
  rw [hξ₁0] at hevξ₁
  rw [hξ₂0] at hevξ₂
  have hevθ : ∀ᶠ θ in 𝓝[>] (0:ℝ), θ ∈ Ioc 0 θ₀ := Ioc_mem_nhdsGT hθ₀pos
  obtain ⟨θ, ⟨hc, hξ1, hξ2⟩, hθpos, hθle⟩ :=
    (((hev.and (hevξ₁.and hevξ₂)).filter_mono nhdsWithin_le_nhds).and hevθ).exists
  simp only [sub_zero, abs_of_pos hθpos] at hξ1 hξ2
  have hθs : θ ≤ s := hθle.trans (hθ₀ ▸ min_le_left _ _)
  have hθQ : θ * Q ≤ η / 2 := by
    have : θ ≤ η / 2 / Q := hθle.trans (hθ₀ ▸ (min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ hQ0] at this
  have hθM : M * (θ * Q) ^ 2 ≤ θ * e / 4 := by
    have h1 : θ ≤ e / (4 * (M * Q ^ 2 + 1)) :=
      hθle.trans (hθ₀ ▸ (min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : M * (θ * Q) ^ 2 = θ * (θ * (M * Q ^ 2)) := by ring
    have h3 : θ * (M * Q ^ 2) ≤ e / 4 := by
      have h4 : θ * (M * Q ^ 2) ≤ θ * (M * Q ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) hθpos.le
      linarith only [h4, h1]
    rw [h2]
    calc θ * (θ * (M * Q ^ 2)) ≤ θ * (e / 4) := mul_le_mul_of_nonneg_left h3 hθpos.le
      _ = θ * e / 4 := by ring
  -- the size of the correction
  obtain ⟨q, hq⟩ : ∃ q, q = |ξ₁ θ| * C₁ + |ξ₂ θ| * C₂ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqθ : q ≤ θ * (K * e) + θ * (δ' * (C₁ + C₂)) := by
    have h1 := abs_le_of_abs_sub_le hθpos hξ1
    have h2 := abs_le_of_abs_sub_le hθpos hξ2
    rw [hq]
    calc |ξ₁ θ| * C₁ + |ξ₂ θ| * C₂ ≤ (θ * |v₁| + δ' * θ) * C₁ + (θ * |v₂| + δ' * θ) * C₂ :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hC₁0) (mul_le_mul_of_nonneg_right h2 hC₂0)
      _ = θ * (|v₁| * C₁ + |v₂| * C₂) + θ * (δ' * (C₁ + C₂)) := by ring
      _ ≤ θ * (K * e) + θ * (δ' * (C₁ + C₂)) := by gcongr
  have hqQ : q ≤ θ * Q := by
    have : θ * (δ' * (C₁ + C₂)) ≤ θ * e :=
      mul_le_mul_of_nonneg_left (by linarith only [hδ'C, he0]) hθpos.le
    rw [hQ]; linarith only [this, hqθ]
  have hqη : q ≤ η / 2 := hqQ.trans hθQ
  have hLq : L * q ≤ θ * (L * K * e) + θ * (e / 4) := by
    have h1 := mul_le_mul_of_nonneg_left hqθ hL0
    have h2 := mul_le_mul_of_nonneg_left hδ'LC hθpos.le
    have h3 : L * (θ * (K * e) + θ * (δ' * (C₁ + C₂)))
        = θ * (L * K * e) + θ * (L * (δ' * (C₁ + C₂))) := by
      ring
    linarith only [h1, h2, h3]
  have hMq : M * q ^ 2 ≤ θ * e / 4 := by
    have : q ^ 2 ≤ (θ * Q) ^ 2 := pow_le_pow_left₀ hq0 hqQ 2
    exact (mul_le_mul_of_nonneg_left this hM0).trans hθM
  -- the cost estimate gives a contradiction
  have hcost := interior_cost_nonneg H hε0 hε1 hW hη hη2 hU₁ hU₂ hC₁ hC₂ hL0 hL hEm
    (N := L * K + 1) (σ := σ) (θ := θ) (ξ₁ := ξ₁ θ) (ξ₂ := ξ₂ θ)
    (fun x y => by rw [hZ, indicatorKernel_apply]) hEU
    (fun z hz => hEJ z hz θ hθpos hθs) hq0 hq.ge hqη hc.1 hc.2
  rw [← hM, ← he_def] at hcost
  have h4 : e * -((L * K + 1) * θ) = -(θ * (L * K * e)) - θ * e := by ring
  have h5 : 0 < θ * e := mul_pos hθpos he0
  linarith only [hcost, h4, h5, hLq, hMq]

end FixedDensities

end UpperTailMultipodality
