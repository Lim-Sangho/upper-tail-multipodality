import UpperTailMultipodality.Preliminaries.Graphons.JpConvexity

/-!
# Scalar bounds for the binomial relative entropy `J_p`

Elementary estimates on `J_p` used in `sec:fixed-densities`:

* `Jp'_lipschitz_box`, `Jp_taylor_box` — Lipschitz bound for `J_p'` and the first-order Taylor
  bound for `J_p` on `[β, 1-β]`;
* `Jp'_bdd_box` — `J_p'` is bounded on `[β, 1-β]`;
* `Jp'_strictMonoOn` — `J_p'` is strictly increasing on `(0,1)`;
* `Jp_add_sub_le`, `Jp_sub_sub_le` — secant bounds by the derivative at the far endpoint;
* `Jp'_le_neg_of_small`, `Jp'_ge_of_near_one` — `J_p' → ∓∞` at `0` and `1`;
* `Jp_mix_le` — `J_p((1-θ)z + θp) ≤ (1-θ)J_p(z)`;
* `Jp_zero_sub_ge`, `Jp_one_sub_ge` — the `θ log(1/θ)` gain at the endpoints.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open Real Set

/-- `J_p` is continuous at every point of `(0,1)`. -/
theorem continuousAt_Jp {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    ContinuousAt (Jp p) u :=
  (hasDerivAt_Jp hp0 hp1 hu0 hu1).continuousAt

/-- **Lipschitz bound for `J_p'`** on `[β, 1-β]`. -/
theorem Jp'_lipschitz_box {β p x y : ℝ} (hβ : 0 < β) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc β (1 - β)) (hy : y ∈ Icc β (1 - β)) :
    |Jp' p x - Jp' p y| ≤ (1 / (β * (1 - β))) * |x - y| := by
  have hderiv : ∀ t ∈ Icc β (1 - β), HasDerivWithinAt (Jp' p) (Jp'' t) (Icc β (1 - β)) t := by
    intro t ht
    exact (hasDerivAt_Jp' hp0 hp1 (lt_of_lt_of_le hβ ht.1) (by linarith [ht.2])).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc β (1 - β), ‖Jp'' t‖ ≤ 1 / (β * (1 - β)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hβ ht.1
    have ht1 : t < 1 := by linarith [ht.2]
    have hβpos : 0 < β * (1 - β) := by nlinarith [ht.1, ht.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (Jp''_pos ht0 ht1).le]
    unfold Jp''
    exact one_div_le_one_div_of_le hβpos (by nlinarith [ht.1, ht.2])
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc β (1 - β))
    hy hx
  simpa [Real.norm_eq_abs] using this

/-- **First-order Taylor bound for `J_p`** on `[β, 1-β]`. -/
theorem Jp_taylor_box {β p x y : ℝ} (hβ : 0 < β) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Icc β (1 - β)) (hy : y ∈ Icc β (1 - β)) :
    |Jp p x - Jp p y - Jp' p y * (x - y)| ≤ (1 / (β * (1 - β))) * (x - y) ^ 2 := by
  have hsub : uIcc x y ⊆ Icc β (1 - β) := uIcc_subset_Icc hx hy
  have hderiv : ∀ t ∈ uIcc x y,
      HasDerivWithinAt (fun t => Jp p t - Jp' p y * t) (Jp' p t - Jp' p y) (uIcc x y) t := by
    intro t ht
    have htbox := hsub ht
    have h1 : HasDerivAt (Jp p) (Jp' p t) t :=
      hasDerivAt_Jp hp0 hp1 (lt_of_lt_of_le hβ htbox.1) (by linarith [htbox.2])
    have h2 : HasDerivAt (fun t : ℝ => Jp' p y * t) (Jp' p y) t := by
      simpa using (hasDerivAt_id t).const_mul (Jp' p y)
    exact (h1.sub h2).hasDerivWithinAt
  have hpos : (0:ℝ) ≤ 1 / (β * (1 - β)) := by
    have : 0 < β * (1 - β) := by nlinarith [hx.1, hx.2]
    positivity
  have hbound : ∀ t ∈ uIcc x y, ‖Jp' p t - Jp' p y‖ ≤ (1 / (β * (1 - β))) * |x - y| := by
    intro t ht
    rw [Real.norm_eq_abs]
    have hty : |t - y| ≤ |x - y| := by
      rcases mem_uIcc.mp ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [abs_le] <;>
        constructor <;> rcases abs_cases (x - y) with h | h <;> linarith [h.1, h.2]
    exact (Jp'_lipschitz_box hβ hp0 hp1 (hsub ht) hy).trans
      (mul_le_mul_of_nonneg_left hty hpos)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc x y) right_mem_uIcc left_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hexp : (Jp p x - Jp' p y * x) - (Jp p y - Jp' p y * y)
      = Jp p x - Jp p y - Jp' p y * (x - y) := by ring
  rw [hexp] at hmvt
  calc |Jp p x - Jp p y - Jp' p y * (x - y)|
      ≤ (1 / (β * (1 - β))) * |x - y| * |x - y| := hmvt
    _ = (1 / (β * (1 - β))) * (x - y) ^ 2 := by
        rw [mul_assoc, ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]

/-- `J_p'` is bounded on `[β, 1-β]`. -/
theorem Jp'_bdd_box {β p : ℝ} (hβ : 0 < β) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Icc β (1 - β), |Jp' p u| ≤ L := by
  have hcont : ContinuousOn (Jp' p) (Icc β (1 - β)) := by
    intro t ht
    exact (hasDerivAt_Jp' hp0 hp1 (lt_of_lt_of_le hβ ht.1)
      (by linarith [ht.2])).continuousAt.continuousWithinAt
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max L 0, le_max_right _ _, fun u hu => by
    have := hL u hu; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩

/-- `J_p'` is strictly increasing on `(0,1)`. -/
theorem Jp'_strictMonoOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (Jp' p) (Ioo 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  · intro t ht
    exact (hasDerivAt_Jp' hp0 hp1 ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(hasDerivAt_Jp' hp0 hp1 ht.1 ht.2).deriv]
    exact Jp''_pos ht.1 ht.2

/-- **Secant bound, moving up.**  For `0 ≤ z`, `θ > 0` and `z + θ < 1`,
`J_p(z+θ) - J_p(z) ≤ θ J_p'(z+θ)`. -/
theorem Jp_add_sub_le {p z θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 ≤ z) (hθ : 0 < θ)
    (hzθ : z + θ < 1) : Jp p (z + θ) - Jp p z ≤ θ * Jp' p (z + θ) := by
  have hlt : z < z + θ := by linarith
  have hcont : ContinuousOn (Jp p) (Icc z (z + θ)) :=
    (continuousOn_Jp_Icc hp0 hp1).mono (Icc_subset_Icc hz hzθ.le)
  have hderiv : ∀ x ∈ Ioo z (z + θ), HasDerivAt (Jp p) (Jp' p x) x := fun x hx =>
    hasDerivAt_Jp hp0 hp1 (lt_of_le_of_lt hz hx.1) (lt_trans hx.2 hzθ)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (Jp p) (Jp' p) hlt hcont hderiv
  have hmono : Jp' p c ≤ Jp' p (z + θ) :=
    (Jp'_strictMonoOn hp0 hp1).monotoneOn ⟨lt_of_le_of_lt hz hc.1, lt_trans hc.2 hzθ⟩
      ⟨by linarith, hzθ⟩ hc.2.le
  have hsl : Jp p (z + θ) - Jp p z = θ * Jp' p c := by
    rw [hceq, show z + θ - z = θ by ring, mul_div_cancel₀ _ hθ.ne']
  rw [hsl]
  exact mul_le_mul_of_nonneg_left hmono hθ.le

/-- **Secant bound, moving down.**  For `z ≤ 1`, `θ > 0` and `0 < z - θ`,
`J_p(z-θ) - J_p(z) ≤ -θ J_p'(z-θ)`. -/
theorem Jp_sub_sub_le {p z θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz : z ≤ 1) (hθ : 0 < θ)
    (hzθ : 0 < z - θ) : Jp p (z - θ) - Jp p z ≤ -θ * Jp' p (z - θ) := by
  have hlt : z - θ < z := by linarith
  have hcont : ContinuousOn (Jp p) (Icc (z - θ) z) :=
    (continuousOn_Jp_Icc hp0 hp1).mono (Icc_subset_Icc hzθ.le hz)
  have hderiv : ∀ x ∈ Ioo (z - θ) z, HasDerivAt (Jp p) (Jp' p x) x := fun x hx =>
    hasDerivAt_Jp hp0 hp1 (lt_trans hzθ hx.1) (lt_of_lt_of_le hx.2 hz)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (Jp p) (Jp' p) hlt hcont hderiv
  have hmono : Jp' p (z - θ) ≤ Jp' p c :=
    (Jp'_strictMonoOn hp0 hp1).monotoneOn ⟨hzθ, by linarith⟩
      ⟨lt_trans hzθ hc.1, lt_of_lt_of_le hc.2 hz⟩ hc.1.le
  have hsl : Jp p (z - θ) - Jp p z = -θ * Jp' p c := by
    rw [hceq, show z - (z - θ) = θ by ring, neg_mul, mul_div_cancel₀ _ hθ.ne']; ring
  rw [hsl]
  nlinarith

/-- `J_p'(u) → -∞` as `u → 0`: for every `N` there is `δ ∈ (0, 1/2]` with `J_p'(u) ≤ -N` on
`(0, δ]`. -/
theorem Jp'_le_neg_of_small {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (N : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ u, 0 < u → u ≤ δ → Jp' p u ≤ -N := by
  refine ⟨min (1 / 2) (p * Real.exp (-N) / 2), lt_min (by norm_num) (by positivity),
    min_le_left _ _, fun u hu0 huδ => ?_⟩
  have hu12 : u ≤ 1 / 2 := huδ.trans (min_le_left _ _)
  have hue : u ≤ p * Real.exp (-N) / 2 := huδ.trans (min_le_right _ _)
  have h1u : 0 < 1 - u := by linarith
  have h1p : 0 < 1 - p := by linarith
  have harg : 0 < u * (1 - p) / ((1 - u) * p) := by positivity
  have hle : u * (1 - p) / ((1 - u) * p) ≤ Real.exp (-N) := by
    rw [div_le_iff₀ (by positivity)]
    have : u * (1 - p) ≤ u := by nlinarith
    have : Real.exp (-N) * ((1 - u) * p) ≥ Real.exp (-N) * (p / 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; nlinarith
    nlinarith
  unfold Jp'
  calc Real.log (u * (1 - p) / ((1 - u) * p)) ≤ Real.log (Real.exp (-N)) :=
        Real.log_le_log harg hle
    _ = -N := Real.log_exp _

/-- `J_p'(u) → +∞` as `u → 1`: for every `N` there is `δ ∈ (0, 1/2]` with `J_p'(u) ≥ N` on
`[1-δ, 1)`. -/
theorem Jp'_ge_of_near_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (N : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ u, u < 1 → 1 - δ ≤ u → N ≤ Jp' p u := by
  have h1p : 0 < 1 - p := by linarith
  refine ⟨min (1 / 2) ((1 - p) * Real.exp (-N) / 2), lt_min (by norm_num) (by positivity),
    min_le_left _ _, fun u hu1 huδ => ?_⟩
  have hδ12 : min (1 / 2) ((1 - p) * Real.exp (-N) / 2) ≤ 1 / 2 := min_le_left _ _
  have hδe : min (1 / 2) ((1 - p) * Real.exp (-N) / 2) ≤ (1 - p) * Real.exp (-N) / 2 :=
    min_le_right _ _
  have hu12 : 1 / 2 ≤ u := by linarith
  have h1u : 0 < 1 - u := by linarith
  have h1ue : 1 - u ≤ (1 - p) * Real.exp (-N) / 2 := by linarith
  have harg : 0 < u * (1 - p) / ((1 - u) * p) := by
    have : 0 < u := by linarith
    positivity
  have hge : Real.exp N ≤ u * (1 - p) / ((1 - u) * p) := by
    rw [le_div_iff₀ (by positivity)]
    have hexp : Real.exp N * Real.exp (-N) = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp N * (1 - u) ≤ (1 - p) / 2 := by
      calc Real.exp N * (1 - u) ≤ Real.exp N * ((1 - p) * Real.exp (-N) / 2) :=
            mul_le_mul_of_nonneg_left h1ue (Real.exp_pos _).le
        _ = (1 - p) / 2 * (Real.exp N * Real.exp (-N)) := by ring
        _ = (1 - p) / 2 := by rw [hexp, mul_one]
    have h3 : Real.exp N * ((1 - u) * p) ≤ (1 - p) / 2 := by
      calc Real.exp N * ((1 - u) * p) = (Real.exp N * (1 - u)) * p := by ring
        _ ≤ (Real.exp N * (1 - u)) * 1 :=
            mul_le_mul_of_nonneg_left hp1.le (by positivity)
        _ ≤ (1 - p) / 2 := by rw [mul_one]; exact h2
    nlinarith
  unfold Jp'
  calc N = Real.log (Real.exp N) := (Real.log_exp _).symm
    _ ≤ Real.log (u * (1 - p) / ((1 - u) * p)) := Real.log_le_log (Real.exp_pos _) hge

/-- **Mixing towards the background density.**  For `z ∈ [0,1]` and `θ ∈ [0,1]`,
`J_p((1-θ)z + θp) ≤ (1-θ)J_p(z)`. -/
theorem Jp_mix_le {p z θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hz : z ∈ Icc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) 1) : Jp p ((1 - θ) * z + θ * p) ≤ (1 - θ) * Jp p z := by
  have h := (convexOn_Jp hp0 hp1).2 hz ⟨hp0.le, hp1.le⟩ (by linarith [hθ.2] : (0:ℝ) ≤ 1 - θ)
    hθ.1 (by ring)
  simp only [smul_eq_mul, Jp_self hp0 hp1, mul_zero, add_zero] at h
  exact h

/-- **The gain at `0`.**  For `θ ∈ (0,1)`, `J_p(0) - J_p(θp) ≥ p θ log(1/θ)`. -/
theorem Jp_zero_sub_ge {p θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    p * θ * Real.log (1 / θ) ≤ Jp p 0 - Jp p (θ * p) := by
  have h1p : 0 < 1 - p := by linarith
  have hθp : θ * p < 1 := by nlinarith
  have h1θp : 0 < 1 - θ * p := by linarith
  have hlog1 : Real.log (1 - θ * p) ≤ 0 := Real.log_nonpos h1θp.le (by nlinarith)
  have hlog2 : Real.log (1 - p) ≤ 0 := Real.log_nonpos h1p.le (by linarith)
  have hJ0 : Jp p 0 = -Real.log (1 - p) := Jp_zero p
  have hJθ : Jp p (θ * p) = θ * p * Real.log θ
      + (1 - θ * p) * (Real.log (1 - θ * p) - Real.log (1 - p)) := by
    unfold Jp
    rw [show θ * p / p = θ by field_simp, Real.log_div h1θp.ne' h1p.ne']
  rw [hJ0, hJθ, one_div, Real.log_inv]
  nlinarith [mul_nonneg h1θp.le (neg_nonneg.mpr hlog1), mul_nonneg (mul_nonneg hθ0.le hp0.le)
    (neg_nonneg.mpr hlog2)]

/-- **The gain at `1`.**  For `θ ∈ (0,1)`, `J_p(1) - J_p(1 - θ(1-p)) ≥ (1-p) θ log(1/θ)`. -/
theorem Jp_one_sub_ge {p θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (1 - p) * θ * Real.log (1 / θ) ≤ Jp p 1 - Jp p (1 - θ * (1 - p)) := by
  have h1p : 0 < 1 - p := by linarith
  have hw0 : 0 < 1 - θ * (1 - p) := by nlinarith
  have hw1 : 1 - θ * (1 - p) ≤ 1 := by nlinarith
  have hlogp : Real.log p ≤ 0 := Real.log_nonpos hp0.le hp1.le
  have hlogw : Real.log (1 - θ * (1 - p)) ≤ 0 := Real.log_nonpos hw0.le hw1
  have hJ1 : Jp p 1 = -Real.log p := by
    unfold Jp; simp [Real.log_inv]
  have hJw : Jp p (1 - θ * (1 - p)) = (1 - θ * (1 - p)) * (Real.log (1 - θ * (1 - p)) - Real.log p)
      + θ * (1 - p) * Real.log θ := by
    unfold Jp
    rw [show 1 - (1 - θ * (1 - p)) = θ * (1 - p) by ring,
      show θ * (1 - p) / (1 - p) = θ by field_simp, Real.log_div hw0.ne' hp0.ne']
  rw [hJ1, hJw, one_div, Real.log_inv]
  nlinarith [mul_nonneg hw0.le (neg_nonneg.mpr hlogw), mul_nonneg (mul_nonneg hθ0.le h1p.le)
    (neg_nonneg.mpr hlogp)]

end FixedDensities

end UpperTailMultipodality
