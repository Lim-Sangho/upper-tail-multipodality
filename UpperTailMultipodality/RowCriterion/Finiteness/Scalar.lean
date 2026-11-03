import UpperTailMultipodality.RowCriterion.Finiteness.BoundedMeasurable

/-!
# Scalar estimates for `J_q` and the logistic function

* `abs_sub_sub_le_of_lipschitz_deriv` — a quadratic Taylor remainder bound;
* Lipschitz bounds for `J_q'` and `J_q''` on compact subintervals of `(0,1)`;
* the logistic function `σ` inverts `J_q'` up to the shift `logit q`:
  `J_q'(σ(t)) = t - logit q`, which turns `eq:row-euler` into its fixed-point form.
-/

namespace UpperTailMultipodality

open Real

/-- **Quadratic remainder bound.**  If `g' ` is `L`-Lipschitz on `[c,d]` and is the derivative of
`g` there, then `|g(z+t) - g(z) - g'(z) t| ≤ L t²` for `z, z+t ∈ [c,d]`. -/
theorem abs_sub_sub_le_of_lipschitz_deriv {g g' : ℝ → ℝ} {c d L : ℝ} (hL0 : 0 ≤ L)
    (hg : ∀ x ∈ Set.Icc c d, HasDerivAt g (g' x) x)
    (hL : ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, |g' x - g' y| ≤ L * |x - y|)
    {z t : ℝ} (hz : z ∈ Set.Icc c d) (hzt : z + t ∈ Set.Icc c d) :
    |g (z + t) - g z - g' z * t| ≤ L * t ^ 2 := by
  have hmem : ∀ τ ∈ Set.uIcc 0 t, z + τ ∈ Set.Icc c d := by
    intro τ hτ
    rcases le_total 0 t with h | h
    · rw [Set.uIcc_of_le h] at hτ
      exact ⟨by linarith [hτ.1, hz.1], by linarith [hτ.2, hzt.2]⟩
    · rw [Set.uIcc_of_ge h] at hτ
      exact ⟨by linarith [hτ.1, hzt.1], by linarith [hτ.2, hz.2]⟩
  let h : ℝ → ℝ := fun τ => g (z + τ) - g z - g' z * τ
  have hderiv : ∀ τ ∈ Set.uIcc 0 t,
      HasDerivWithinAt h (g' (z + τ) - g' z) (Set.uIcc 0 t) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ => g (z + τ)) (g' (z + τ)) τ := by
      exact (hg (z + τ) (hmem τ hτ)).comp_const_add z τ
    have h2 : HasDerivAt (fun τ => g' z * τ) (g' z) τ := by
      simpa using (hasDerivAt_id τ).const_mul (g' z)
    exact ((h1.sub_const (g z)).sub h2).hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.uIcc 0 t, ‖g' (z + τ) - g' z‖ ≤ L * |t| := by
    intro τ hτ
    rw [Real.norm_eq_abs]
    refine (hL _ (hmem τ hτ) _ hz).trans ?_
    have : |z + τ - z| ≤ |t| := by
      rw [add_sub_cancel_left]
      have := Set.abs_sub_left_of_mem_uIcc hτ
      simpa using this
    exact mul_le_mul_of_nonneg_left this hL0
  have hmvt := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [h, Real.norm_eq_abs, add_zero, mul_zero, sub_zero, sub_self] at hmvt
  calc |g (z + t) - g z - g' z * t| ≤ L * |t| * |t| := hmvt
    _ = L * t ^ 2 := by rw [mul_assoc, ← abs_mul, abs_mul_self, sq]

section Entropy

variable {c d : ℝ}

/-- On `[c,d] ⊆ (0,1)`, `x(1-x)` is bounded below by `c(1-d)`. -/
theorem mul_one_sub_ge_of_mem_Icc (hc : 0 < c) (hd : d < 1) {x : ℝ} (hx : x ∈ Set.Icc c d) :
    c * (1 - d) ≤ x * (1 - x) :=
  mul_le_mul hx.1 (by linarith [hx.2]) (by linarith [hx.2.trans hd.le]) (hc.le.trans hx.1)

/-- **The entropy curvature is at least `4`** on `(0,1)`, which is the first inequality of
`eq:row-entropy-curvature`: since `x(1-x) ≤ 1/4`, one has `J_q''(x) = 1/(x(1-x)) ≥ 4`. -/
theorem four_le_Jp'' {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 4 ≤ Jp'' x := by
  have hxx : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hle : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  rw [Jp'', le_div_iff₀ hxx]
  linarith

/-- Bounds for `J_q''` on a compact subinterval of `(0,1)`. -/
theorem Jp''_mem_of_mem_Icc (hc : 0 < c) (hd : d < 1) {x : ℝ} (hx : x ∈ Set.Icc c d) :
    0 < Jp'' x ∧ Jp'' x ≤ 1 / (c * (1 - d)) := by
  have hcd : 0 < c * (1 - d) := mul_pos hc (by linarith)
  have hxx := mul_one_sub_ge_of_mem_Icc hc hd hx
  unfold Jp''
  exact ⟨one_div_pos.mpr (hcd.trans_le hxx), one_div_le_one_div_of_le hcd hxx⟩

/-- `J_q'` is Lipschitz on `[c,d] ⊆ (0,1)`. -/
theorem abs_Jp'_sub_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) (hd : d < 1) {x y : ℝ}
    (hx : x ∈ Set.Icc c d) (hy : y ∈ Set.Icc c d) :
    |Jp' q x - Jp' q y| ≤ 1 / (c * (1 - d)) * |x - y| := by
  have hderiv : ∀ z ∈ Set.Icc c d, HasDerivWithinAt (Jp' q) (Jp'' z) (Set.Icc c d) z := fun z hz =>
    (hasDerivAt_Jp' hq0 hq1 (hc.trans_le hz.1) (hz.2.trans_lt hd)).hasDerivWithinAt
  have hbound : ∀ z ∈ Set.Icc c d, ‖Jp'' z‖ ≤ 1 / (c * (1 - d)) := fun z hz => by
    rw [Real.norm_eq_abs, abs_of_pos (Jp''_mem_of_mem_Icc hc hd hz).1]
    exact (Jp''_mem_of_mem_Icc hc hd hz).2
  have := (convex_Icc c d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy hx
  simpa [Real.norm_eq_abs] using this

/-- `J_q''` is Lipschitz on `[c,d] ⊆ (0,1)`. -/
theorem abs_Jp''_sub_le (hc : 0 < c) (hd : d < 1) {x y : ℝ} (hx : x ∈ Set.Icc c d)
    (hy : y ∈ Set.Icc c d) :
    |Jp'' x - Jp'' y| ≤ 1 / (c * (1 - d)) ^ 2 * |x - y| := by
  have hcd : 0 < c * (1 - d) := mul_pos hc (by linarith)
  have hxx := mul_one_sub_ge_of_mem_Icc hc hd hx
  have hyy := mul_one_sub_ge_of_mem_Icc hc hd hy
  have hxpos : 0 < x * (1 - x) := hcd.trans_le hxx
  have hypos : 0 < y * (1 - y) := hcd.trans_le hyy
  unfold Jp''
  rw [div_sub_div _ _ hxpos.ne' hypos.ne', abs_div, abs_of_pos (mul_pos hxpos hypos)]
  have hnum : |1 * (y * (1 - y)) - x * (1 - x) * 1| ≤ |x - y| := by
    have : 1 * (y * (1 - y)) - x * (1 - x) * 1 = (x - y) * (x + y - 1) := by ring
    rw [this, abs_mul]
    have h1 : |x + y - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, hc, hd]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  rw [div_le_iff₀ (mul_pos hxpos hypos)]
  calc |1 * (y * (1 - y)) - x * (1 - x) * 1| ≤ |x - y| := hnum
    _ = 1 / (c * (1 - d)) ^ 2 * |x - y| * (c * (1 - d)) ^ 2 := by
        rw [one_div_mul_eq_div, div_mul_cancel₀ _ (by positivity)]
    _ ≤ 1 / (c * (1 - d)) ^ 2 * |x - y| * (x * (1 - x) * (y * (1 - y))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sq]; exact mul_le_mul hxx hyy hcd.le hxpos.le

/-- Quadratic remainder for `J_q`. -/
theorem abs_Jp_sub_sub_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) (hd : d < 1) {z t : ℝ}
    (hz : z ∈ Set.Icc c d) (hzt : z + t ∈ Set.Icc c d) :
    |Jp q (z + t) - Jp q z - Jp' q z * t| ≤ 1 / (c * (1 - d)) * t ^ 2 := by
  have hcd : 0 < c * (1 - d) := mul_pos hc (by linarith)
  refine abs_sub_sub_le_of_lipschitz_deriv (by positivity) (fun x hx => ?_) (fun x hx y hy => ?_)
    hz hzt
  · exact hasDerivAt_Jp hq0 hq1 (hc.trans_le hx.1) (hx.2.trans_lt hd)
  · exact abs_Jp'_sub_le hq0 hq1 hc hd hx hy

/-- Quadratic remainder for `J_q'`. -/
theorem abs_Jp'_sub_sub_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) (hd : d < 1)
    {z t : ℝ} (hz : z ∈ Set.Icc c d) (hzt : z + t ∈ Set.Icc c d) :
    |Jp' q (z + t) - Jp' q z - Jp'' z * t| ≤ 1 / (c * (1 - d)) ^ 2 * t ^ 2 := by
  have hcd : 0 < c * (1 - d) := mul_pos hc (by linarith)
  refine abs_sub_sub_le_of_lipschitz_deriv (by positivity) (fun x hx => ?_) (fun x hx y hy => ?_)
    hz hzt
  · exact hasDerivAt_Jp' hq0 hq1 (hc.trans_le hx.1) (hx.2.trans_lt hd)
  · exact abs_Jp''_sub_le hc hd hx hy

/-- `u log(u/r) = u log u - u log r`, with the convention `0 log 0 = 0`. -/
theorem mul_log_div_eq (u r : ℝ) (hr : r ≠ 0) :
    u * Real.log (u / r) = u * Real.log u - u * Real.log r := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [Real.log_div hu hr]; ring

/-- `J_q` is continuous on `ℝ`. -/
theorem continuous_Jp {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : Continuous (Jp q) := by
  have h : Jp q = fun u => (u * Real.log u - u * Real.log q)
      + ((1 - u) * Real.log (1 - u) - (1 - u) * Real.log (1 - q)) := by
    funext u
    unfold Jp
    rw [mul_log_div_eq u q hq0.ne', mul_log_div_eq (1 - u) (1 - q) (by linarith)]
  rw [h]
  have h1 : Continuous fun u : ℝ => u * Real.log u := Real.continuous_mul_log
  have h2 : Continuous fun u : ℝ => (1 - u) * Real.log (1 - u) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  fun_prop

end Entropy

/-! ### The logistic function -/

/-- The logit `log(q/(1-q))`. -/
noncomputable def logit (q : ℝ) : ℝ := Real.log (q / (1 - q))

/-- The logistic function as an inverse. -/
theorem logistic_eq_inv : BddMeas.logistic = fun t => (1 + Real.exp (-t))⁻¹ := by
  funext t; rw [BddMeas.logistic, one_div]

/-- `1 - σ(t) = e^{-t}/(1+e^{-t})`. -/
theorem one_sub_logistic (t : ℝ) :
    1 - BddMeas.logistic t = Real.exp (-t) / (1 + Real.exp (-t)) := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  rw [BddMeas.logistic]
  field_simp
  ring

/-- The derivative of the logistic function is `σ(1-σ)`. -/
theorem hasDerivAt_logistic (t : ℝ) :
    HasDerivAt BddMeas.logistic (BddMeas.logistic t * (1 - BddMeas.logistic t)) t := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  have hd : HasDerivAt (fun t => 1 + Real.exp (-t)) (-Real.exp (-t)) t := by
    have := ((hasDerivAt_neg t).exp).const_add 1
    simpa using this
  have h : HasDerivAt (fun t => (1 + Real.exp (-t))⁻¹)
      (-(-Real.exp (-t)) / (1 + Real.exp (-t)) ^ 2) t := hd.inv hpos.ne'
  have hval : BddMeas.logistic t * (1 - BddMeas.logistic t)
      = -(-Real.exp (-t)) / (1 + Real.exp (-t)) ^ 2 := by
    rw [one_sub_logistic, BddMeas.logistic]; field_simp
  rw [hval, logistic_eq_inv]
  exact h

/-- `σ(1-σ) ≤ 1/4`. -/
theorem logistic_mul_one_sub_le (t : ℝ) :
    BddMeas.logistic t * (1 - BddMeas.logistic t) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (BddMeas.logistic t - 1 / 2)]

/-- The logistic function is `1/4`-Lipschitz. -/
theorem abs_logistic_sub_le (s t : ℝ) :
    |BddMeas.logistic s - BddMeas.logistic t| ≤ 1 / 4 * |s - t| := by
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt BddMeas.logistic
      (BddMeas.logistic z * (1 - BddMeas.logistic z)) Set.univ z :=
    fun z _ => (hasDerivAt_logistic z).hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ),
      ‖BddMeas.logistic z * (1 - BddMeas.logistic z)‖ ≤ 1 / 4 := fun z _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (BddMeas.logistic_pos z).le
      (by linarith [BddMeas.logistic_lt_one z]))]
    exact logistic_mul_one_sub_le z
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using this

/-- The logistic function is monotone. -/
theorem logistic_monotone : Monotone BddMeas.logistic := by
  intro s t hst
  unfold BddMeas.logistic
  have h1 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **`J_q'` inverts the logistic function up to a shift**: `J_q'(σ(t)) = t - logit q`. -/
theorem Jp'_logistic {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) :
    Jp' q (BddMeas.logistic t) = t - logit q := by
  have hσ0 := BddMeas.logistic_pos t
  have hσ1 := BddMeas.logistic_lt_one t
  have hratio : BddMeas.logistic t / (1 - BddMeas.logistic t) = Real.exp t := by
    rw [one_sub_logistic, BddMeas.logistic]
    have hpos : 0 < 1 + Real.exp (-t) := by positivity
    have hne : Real.exp (-t) ≠ 0 := (Real.exp_pos _).ne'
    rw [Real.exp_neg] at hpos hne ⊢
    field_simp
  unfold Jp' logit
  have h1q : (0:ℝ) < 1 - q := by linarith
  rw [show BddMeas.logistic t * (1 - q) / ((1 - BddMeas.logistic t) * q)
      = (BddMeas.logistic t / (1 - BddMeas.logistic t)) / (q / (1 - q)) by
        field_simp,
    hratio, Real.log_div (Real.exp_pos t).ne' (by positivity), Real.log_exp]

/-- **The logistic function inverts `J_q'`**: `σ(J_q'(z) + logit q) = z` for `z ∈ (0,1)`. -/
theorem logistic_Jp' {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    BddMeas.logistic (Jp' q z + logit q) = z := by
  unfold BddMeas.logistic Jp' logit
  have h1q : (0:ℝ) < 1 - q := by linarith
  have h1z : (0:ℝ) < 1 - z := by linarith
  rw [← Real.log_mul (by positivity) (by positivity), Real.exp_neg,
    Real.exp_log (by positivity)]
  field_simp
  ring

end UpperTailMultipodality
