import UpperTailMultipodality.Preliminaries.Perturbation

/-!
# One-variable analysis for the upper-tail lemmas

Elementary facts used in `lem:upper-tail-basic` and `lem:upper-tail-multiplier`:

* `convexOn_tangent_le`, `Jp_tangent_le` — the tangent line lies below a convex function;
* `exists_Jp'_eq` — every real number is a value of `J_p'` on `(0,1)`;
* `exists_pos_lt_of_hasDerivAt_pos`, `nonneg_of_hasDerivAt_of_le` — the sign of a derivative at
  `0` and one-sided comparisons near `0`.
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory Filter Topology Set

/-- **The tangent line lies below a convex function.** -/
theorem convexOn_tangent_le {S : Set ℝ} {f : ℝ → ℝ} {f' x₀ : ℝ}
    (hfc : ConvexOn ℝ S f) (hx₀ : x₀ ∈ S) (hderiv : HasDerivAt f f' x₀) :
    ∀ y ∈ S, f x₀ + f' * (y - x₀) ≤ f y := by
  intro y hy
  rcases lt_trichotomy x₀ y with hlt | heq | hgt
  · have h := hfc.le_slope_of_hasDerivAt hx₀ hy hlt hderiv
    rw [slope_def_field] at h
    have hpos : 0 < y - x₀ := by linarith
    rw [le_div_iff₀ hpos] at h
    linarith
  · subst heq; simp
  · have h := hfc.slope_le_of_hasDerivAt hy hx₀ hgt hderiv
    rw [slope_def_field] at h
    have hpos : 0 < x₀ - y := by linarith
    rw [div_le_iff₀ hpos] at h
    linarith

/-- The tangent line of `J_p` at an interior point lies below `J_p` on `[0,1]`. -/
theorem Jp_tangent_le {p t y : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hy : y ∈ Icc (0:ℝ) 1) : Jp p t + Jp' p t * (y - t) ≤ Jp p y :=
  convexOn_tangent_le (convexOn_Jp hp0 hp1) ⟨ht0.le, ht1.le⟩ (hasDerivAt_Jp hp0 hp1 ht0 ht1) y hy

/-- **Moving down by `θ`.**  If `0 < w - θ` and `c ≤ J_p'(w - θ)`, then
`J_p(w - θ) ≤ J_p(w) - θc`. -/
theorem Jp_sub_le {p w θ c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hw1 : w ≤ 1) (hθ : 0 < θ)
    (ht0 : 0 < w - θ) (hc : c ≤ Jp' p (w - θ)) : Jp p (w - θ) ≤ Jp p w - θ * c := by
  have h := Jp_tangent_le hp0 hp1 ht0 (by linarith) ⟨by linarith, hw1⟩ (p := p) (y := w)
  have : θ * c ≤ θ * Jp' p (w - θ) := mul_le_mul_of_nonneg_left hc hθ.le
  nlinarith

/-- **Moving up by `h`.**  If `w + h < 1` and `J_p'(w + h) ≤ C`, then
`J_p(w + h) ≤ J_p(w) + hC`. -/
theorem Jp_add_le {p w h C : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hw0 : 0 ≤ w) (hh : 0 < h)
    (hwh : w + h < 1) (hC : Jp' p (w + h) ≤ C) : Jp p (w + h) ≤ Jp p w + h * C := by
  have h1 := Jp_tangent_le hp0 hp1 (by linarith) hwh ⟨hw0, by linarith⟩ (p := p) (y := w)
  have : h * Jp' p (w + h) ≤ h * C := mul_le_mul_of_nonneg_left hC hh.le
  nlinarith

/-- `J_p'(p) = 0`. -/
theorem Jp'_self {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Jp' p p = 0 := by
  unfold Jp'
  have h : p * (1 - p) / ((1 - p) * p) = 1 := by
    rw [mul_comm p (1 - p)]
    exact div_self (mul_ne_zero (by linarith) hp0.ne')
  rw [h, Real.log_one]

/-- **Every real number is a value of `J_p'` on `(0,1)`**, attained at
`t = e^c p / (1 - p + e^c p)`; the point lies to the right of `p` when `c > 0`. -/
theorem exists_Jp'_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c : ℝ) :
    ∃ t, 0 < t ∧ t < 1 ∧ Jp' p t = c ∧ (0 < c → p < t) := by
  have he : 0 < Real.exp c := Real.exp_pos c
  have h1p : 0 < 1 - p := by linarith
  have hden : 0 < 1 - p + Real.exp c * p := by positivity
  refine ⟨Real.exp c * p / (1 - p + Real.exp c * p), by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_one hden]; linarith
  · unfold Jp'
    have h1t : 1 - Real.exp c * p / (1 - p + Real.exp c * p)
        = (1 - p) / (1 - p + Real.exp c * p) := by
      field_simp; ring
    rw [h1t]
    have : Real.exp c * p / (1 - p + Real.exp c * p) * (1 - p)
        / ((1 - p) / (1 - p + Real.exp c * p) * p) = Real.exp c := by
      field_simp
    rw [this, Real.log_exp]
  · intro hc
    have he1 : 1 < Real.exp c := Real.one_lt_exp_iff.mpr hc
    rw [lt_div_iff₀ hden]
    nlinarith [mul_pos h1p hp0]

/-- **A positive derivative at `0` forces `f θ > f 0` for small `θ > 0`.** -/
theorem exists_pos_lt_of_hasDerivAt_pos {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (hpos : 0 < f') : ∃ ε > 0, ∀ θ, 0 < θ → θ < ε → f 0 < f θ := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hs' : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 f') :=
    hs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hev : ∀ᶠ θ in 𝓝[>] (0:ℝ), 0 < slope f 0 θ := hs'.eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, hεs⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hev
  refine ⟨ε, hε, fun θ hθ hθε => ?_⟩
  have h := hεs ⟨hθ, hθε⟩
  rw [slope_def_field, sub_zero] at h
  have := (div_pos_iff_of_pos_right hθ).mp h
  linarith

/-- **One-sided minimality at `0` forces a nonnegative derivative.** -/
theorem nonneg_of_hasDerivAt_of_le {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0) {ε : ℝ}
    (hε : 0 < ε) (hle : ∀ θ, 0 < θ → θ < ε → f 0 ≤ f θ) : 0 ≤ f' := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hs' : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 f') :=
    hs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine ge_of_tendsto hs' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with θ hθ
  rw [slope_def_field, sub_zero]
  exact div_nonneg (by linarith [hle θ hθ.1 hθ.2]) hθ.1.le

end UpperTailSupport

end UpperTailMultipodality
