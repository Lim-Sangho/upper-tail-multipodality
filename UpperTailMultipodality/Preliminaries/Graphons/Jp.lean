import Mathlib

/-!
# The binomial relative entropy `J_p`

For `0 < p < 1` and `z ∈ [0,1]` (with the convention `0 * log 0 = 0`, which is automatic in
Mathlib because `Real.log 0 = 0`),
$$ J_p(z) = z \log\frac{z}{p} + (1-z)\log\frac{1-z}{1-p}. $$
This file defines `J_p` and its first two derivatives, valid on `0 < z < 1`:
$$ J_p'(z) = \log\frac{z(1-p)}{(1-z)p}, \qquad J_p''(z) = \frac{1}{z(1-z)}. $$

The Lean definitions below name the variable `u`.
-/

namespace UpperTailMultipodality

open Real

/-- The binomial relative entropy `J_p(z)`. -/
noncomputable def Jp (p u : ℝ) : ℝ :=
  u * Real.log (u / p) + (1 - u) * Real.log ((1 - u) / (1 - p))

/-- First derivative of `J_p`, in the closed form `log (u(1-p)/((1-u)p))`. -/
noncomputable def Jp' (p u : ℝ) : ℝ :=
  Real.log (u * (1 - p) / ((1 - u) * p))

/-- Second derivative of `J_p`: `1/(u(1-u))`. -/
noncomputable def Jp'' (u : ℝ) : ℝ := 1 / (u * (1 - u))

/-- `J_p(p) = 0`: the constant graphon at the background density has zero cost. -/
@[simp] theorem Jp_self {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Jp p p = 0 := by
  unfold Jp
  have h1 : p / p = 1 := div_self (ne_of_gt hp0)
  have h2 : (1 - p) / (1 - p) = 1 := div_self (ne_of_gt (by linarith : (0:ℝ) < 1 - p))
  rw [h1, h2, Real.log_one]
  ring

/-- `J_p(0) = -log(1 - p)`: the cost of the empty graphon.  Unconditional, because
`Real.log 0 = 0` absorbs the vanishing first term. -/
theorem Jp_zero (p : ℝ) : Jp p 0 = -Real.log (1 - p) := by
  simp [Jp]

/-- `J_p''(u) > 0` on `(0,1)`. -/
theorem Jp''_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < Jp'' u := by
  unfold Jp''
  have : 0 < u * (1 - u) := by
    have : (0:ℝ) < 1 - u := by linarith
    positivity
  positivity

/-- The inner log term `log (y/p)` has derivative `1/u` at `u`. -/
private theorem hasDerivAt_logA {p u : ℝ} (hp0 : 0 < p) (hu0 : 0 < u) :
    HasDerivAt (fun y : ℝ => Real.log (y / p)) (1 / u) u := by
  have hd : HasDerivAt (fun y : ℝ => y / p) (1 / p) u := by
    simpa using (hasDerivAt_id u).div_const p
  have := hd.log (by positivity)
  convert this using 1
  field_simp

/-- The inner log term `log ((1-y)/(1-p))` has derivative `-(1/(1-u))` at `u`. -/
private theorem hasDerivAt_logB {p u : ℝ} (hp1 : p < 1) (hu1 : u < 1) :
    HasDerivAt (fun y : ℝ => Real.log ((1 - y) / (1 - p))) (-(1 / (1 - u))) u := by
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  have hd : HasDerivAt (fun y : ℝ => (1 - y) / (1 - p)) (-1 / (1 - p)) u := by
    have : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 1
    simpa using this.div_const (1 - p)
  have := hd.log (div_ne_zero h1une h1pne)
  convert this using 1
  field_simp

/-- On `(0,1)`, `J_p'` equals the difference of logs `log(u/p) - log((1-u)/(1-p))`. -/
theorem Jp'_eq_sub {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    Jp' p u = Real.log (u / p) - Real.log ((1 - u) / (1 - p)) := by
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  unfold Jp'
  rw [← Real.log_div (by positivity) (div_ne_zero h1une h1pne)]
  congr 1
  field_simp

/-- The first derivative of `J_p` on `(0,1)`. -/
theorem hasDerivAt_Jp {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (Jp p) (Jp' p u) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hlog1 := hasDerivAt_logA hp0 hu0
  have hlog2 := hasDerivAt_logB hp1 hu1
  -- product rule for the two terms
  have hA : HasDerivAt (fun y : ℝ => y * Real.log (y / p))
      (Real.log (u / p) + u * (1 / u)) u := by
    have h := (hasDerivAt_id u).mul hlog1
    simp only [id_eq, one_mul] at h
    exact h
  have hB : HasDerivAt (fun y : ℝ => (1 - y) * Real.log ((1 - y) / (1 - p)))
      ((-1) * Real.log ((1 - u) / (1 - p)) + (1 - u) * (-(1 / (1 - u)))) u := by
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 1
    exact hsub.mul hlog2
  have hsum := hA.add hB
  have hfun : ((fun y : ℝ => y * Real.log (y / p)) +
      fun y : ℝ => (1 - y) * Real.log ((1 - y) / (1 - p))) = Jp p := by
    funext y; rfl
  rw [hfun] at hsum
  have hval : Real.log (u / p) + u * (1 / u) +
      ((-1) * Real.log ((1 - u) / (1 - p)) + (1 - u) * (-(1 / (1 - u)))) = Jp' p u := by
    have e1 : u * (1 / u) = 1 := by field_simp
    have e2 : (1 - u) * (-(1 / (1 - u))) = -1 := by field_simp
    rw [e1, e2, Jp'_eq_sub hp0 hp1 hu0 hu1]; ring
  rw [← hval]
  exact hsum

/-- The second derivative of `J_p` on `(0,1)`. -/
theorem hasDerivAt_Jp' {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (Jp' p) (Jp'' u) u := by
  have hune : u ≠ 0 := ne_of_gt hu0
  have h1une : (1 - u) ≠ 0 := ne_of_gt (by linarith)
  have hlog1 := hasDerivAt_logA hp0 hu0
  have hlog2 := hasDerivAt_logB hp1 hu1
  have hdiff := hlog1.sub hlog2
  -- `Jp' p` agrees with the difference of logs on the neighbourhood `(0,1)` of `u`
  have hagree : Jp' p =ᶠ[nhds u]
      (fun y : ℝ => Real.log (y / p) - Real.log ((1 - y) / (1 - p))) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact Jp'_eq_sub hp0 hp1 hy.1 hy.2
  have hres := hdiff.congr_of_eventuallyEq hagree
  have hval : Jp'' u = 1 / u - -(1 / (1 - u)) := by
    unfold Jp''
    field_simp
    ring
  rw [hval]
  exact hres

/-- `J_p'` is measurable. -/
theorem measurable_Jp' (p : ℝ) : Measurable (Jp' p) := by
  unfold Jp'
  fun_prop

/-- `J_p'` is strictly increasing on `(0,1)`. -/
theorem Jp'_strictMonoOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (Jp' p) (Set.Ioo 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  · intro u hu
    exact (hasDerivAt_Jp' hp0 hp1 hu.1 hu.2).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    rw [(hasDerivAt_Jp' hp0 hp1 hu.1 hu.2).deriv]
    exact Jp''_pos hu.1 hu.2

/-- `J_p'(u) > 0` for `p < u < 1`: the slope of the relative entropy is positive to
the right of the background density. -/
theorem Jp'_pos_of_gt {p u : ℝ} (hp0 : 0 < p) (hpu : p < u) (hu1 : u < 1) :
    0 < Jp' p u := by
  unfold Jp'
  apply Real.log_pos
  rw [lt_div_iff₀ (mul_pos (by linarith) hp0)]
  nlinarith [hpu, hp0]

/-- `J_p'(u) < 0` for `0 < u < p`: the slope of the relative entropy is negative to
the left of the background density. -/
theorem Jp'_neg_of_lt {p u : ℝ} (hu0 : 0 < u) (hup : u < p) (hp1 : p < 1) :
    Jp' p u < 0 := by
  have hp0 : (0:ℝ) < p := lt_trans hu0 hup
  unfold Jp'
  apply Real.log_neg
  · exact div_pos (mul_pos hu0 (by linarith)) (mul_pos (by linarith) hp0)
  · rw [div_lt_one (mul_pos (by linarith) hp0)]
    nlinarith [hup, hu0]

/-- **Strict positivity of the binomial relative entropy** on `(p,1)`: `0 < J_p(u)`
for `p < u < 1`.  Proved by the mean value theorem on `[p,u]` (where `J_p(p) = 0` and
`J_p' > 0` on the interior). -/
theorem Jp_pos_of_gt {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpu : p < u) (hu1 : u < 1) :
    0 < Jp p u := by
  have hcont : ContinuousOn (Jp p) (Set.Icc p u) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hp0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hu1
    exact (hasDerivAt_Jp hp0 hp1 hx0 hx1).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo p u, HasDerivAt (Jp p) (deriv (Jp p) x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hp0 hx.1
    have hx1 : x < 1 := lt_trans hx.2 hu1
    have h := hasDerivAt_Jp hp0 hp1 hx0 hx1
    rw [h.deriv]; exact h
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (Jp p) (deriv (Jp p)) hpu hcont hderiv
  have hξ0 : 0 < ξ := lt_trans hp0 hξ.1
  have hξ1 : ξ < 1 := lt_trans hξ.2 hu1
  have hderivξ : deriv (Jp p) ξ = Jp' p ξ := (hasDerivAt_Jp hp0 hp1 hξ0 hξ1).deriv
  have hJp'pos : 0 < Jp' p ξ := Jp'_pos_of_gt hp0 hξ.1 hξ1
  rw [hderivξ, Jp_self hp0 hp1, sub_zero] at hξeq
  have hupos : 0 < u - p := by linarith
  have h2 : 0 < Jp p u / (u - p) := hξeq ▸ hJp'pos
  rw [lt_div_iff₀ hupos, zero_mul] at h2
  exact h2

/-- **Strict positivity of the binomial relative entropy** on `(0,p)`: `0 < J_p(u)`
for `0 < u < p`.  Mean value theorem on `[u,p]`. -/
theorem Jp_pos_of_lt {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hup : u < p) :
    0 < Jp p u := by
  have hcont : ContinuousOn (Jp p) (Set.Icc u p) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hp1
    exact (hasDerivAt_Jp hp0 hp1 hx0 hx1).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo u p, HasDerivAt (Jp p) (deriv (Jp p) x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hu0 hx.1
    have hx1 : x < 1 := lt_trans hx.2 hp1
    have h := hasDerivAt_Jp hp0 hp1 hx0 hx1
    rw [h.deriv]; exact h
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (Jp p) (deriv (Jp p)) hup hcont hderiv
  have hξ0 : 0 < ξ := lt_trans hu0 hξ.1
  have hξ1 : ξ < 1 := lt_trans hξ.2 hp1
  have hderivξ : deriv (Jp p) ξ = Jp' p ξ := (hasDerivAt_Jp hp0 hp1 hξ0 hξ1).deriv
  have hJp'neg : Jp' p ξ < 0 := Jp'_neg_of_lt hξ0 hξ.2 hp1
  rw [hderivξ, Jp_self hp0 hp1] at hξeq
  -- hξeq : Jp' p ξ = (0 - Jp p u)/(p - u)
  have hupos : 0 < p - u := by linarith
  have hneg : (0 - Jp p u) / (p - u) < 0 := hξeq ▸ hJp'neg
  rw [div_lt_iff₀ hupos, zero_mul] at hneg
  linarith

/-- The binomial relative entropy is strictly positive off the background density:
`0 < J_p(u)` for `u ∈ (0,1)`, `u ≠ p`. -/
theorem Jp_pos {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hne : u ≠ p) : 0 < Jp p u := by
  rcases lt_trichotomy u p with h | h | h
  · exact Jp_pos_of_lt hp0 hp1 hu0 h
  · exact absurd h hne
  · exact Jp_pos_of_gt hp0 hp1 h hu1

end UpperTailMultipodality
