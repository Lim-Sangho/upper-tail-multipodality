import UpperTailMultipodality.Preliminaries.Graphons.Basic

/-!
# Convexity, monotonicity and the zero set of `J_p`

* `convexOn_Jp` / `strictConvexOn_Jp` — `J_p` is (strictly) convex on `[0,1]`, from
  `J_p'' = 1/(u(1-u)) > 0`;
* `Jp_zero_pos`, `Jp_one_pos`, `Jp_pos_of_ne`, `Jp_eq_zero_imp` — the values of `J_p` at the
  endpoints and its zero set: on `[0,1]`, `J_p(u) = 0` if and only if `u = p`;
* `Jp_nonneg_of_mem` — `J_p ≥ 0` on `[0,1]`;
* `Jp_strictMonoOn_right` — `J_p` is strictly increasing on `[p,1]`.
-/

namespace UpperTailMultipodality

open Real Set

/-- On the open interval `(0,1)`, `deriv (J_p) = J_p'`. -/
theorem deriv_Jp_eq {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    deriv (Jp p) u = Jp' p u := (hasDerivAt_Jp hp0 hp1 hu0 hu1).deriv

/-- On the open interval `(0,1)`, the second derivative of `J_p` equals `J_p''`. -/
theorem deriv2_Jp_eq {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    deriv (deriv (Jp p)) u = Jp'' u := by
  have hEq : deriv (Jp p) =ᶠ[nhds u] Jp' p := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
    exact (hasDerivAt_Jp hp0 hp1 hy.1 hy.2).deriv
  rw [hEq.deriv_eq]
  exact (hasDerivAt_Jp' hp0 hp1 hu0 hu1).deriv

/-- **`J_p` is strictly convex on `[0,1]`** (its second derivative is positive on the
interior). -/
theorem strictConvexOn_Jp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictConvexOn ℝ (Set.Icc 0 1) (Jp p) := by
  refine strictConvexOn_of_deriv2_pos (convex_Icc 0 1) (continuousOn_Jp_Icc hp0 hp1) ?_
  intro x hx
  rw [interior_Icc] at hx
  show 0 < deriv (deriv (Jp p)) x
  rw [deriv2_Jp_eq hp0 hp1 hx.1 hx.2]
  exact Jp''_pos hx.1 hx.2

/-- **`J_p` is convex on `[0,1]`.** -/
theorem convexOn_Jp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ConvexOn ℝ (Set.Icc 0 1) (Jp p) := (strictConvexOn_Jp hp0 hp1).convexOn

/-- `J_p(0) = -log(1-p) > 0`. -/
theorem Jp_zero_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < Jp p 0 := by
  have h1p : (0:ℝ) < 1 - p := by linarith
  unfold Jp
  simp only [zero_mul, zero_add, sub_zero, one_mul]
  apply Real.log_pos
  rw [lt_div_iff₀ h1p, one_mul]
  linarith

/-- `J_p(1) = -log p > 0`. -/
theorem Jp_one_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < Jp p 1 := by
  unfold Jp
  simp only [one_mul, sub_self, zero_mul, add_zero]
  apply Real.log_pos
  rw [lt_div_iff₀ hp0, one_mul]
  exact hp1

/-- **Strict positivity off the background density, including the endpoints**: for
`u ∈ [0,1]` with `u ≠ p`, `0 < J_p(u)`. -/
theorem Jp_pos_of_ne {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hne : u ≠ p) : 0 < Jp p u := by
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · rw [← h0]; exact Jp_zero_pos hp0 hp1
  · rcases eq_or_lt_of_le hu1 with h1 | h1
    · rw [h1]; exact Jp_one_pos hp0 hp1
    · exact Jp_pos hp0 hp1 h0 h1 hne

/-- **Zero set of `J_p` on `[0,1]`**: `J_p(u) = 0` forces `u = p`. -/
theorem Jp_eq_zero_imp {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h : Jp p u = 0) : u = p := by
  by_contra hne
  exact absurd h (ne_of_gt (Jp_pos_of_ne hp0 hp1 hu0 hu1 hne))

/-- `J_p ≥ 0` on `[0,1]`. -/
theorem Jp_nonneg_of_mem {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ Jp p u := by
  rcases eq_or_ne u p with h | h
  · rw [h, Jp_self hp0 hp1]
  · exact (Jp_pos_of_ne hp0 hp1 hu0 hu1 h).le

/-- **`J_p` is strictly increasing on `[p,1]`.** -/
theorem Jp_strictMonoOn_right {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (Jp p) (Set.Icc p 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc p 1)
    ((continuousOn_Jp_Icc hp0 hp1).mono (Set.Icc_subset_Icc hp0.le le_rfl)) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_Jp_eq hp0 hp1 (lt_trans hp0 hx.1) hx.2]
  exact Jp'_pos_of_gt hp0 hx.1 hx.2

end UpperTailMultipodality
