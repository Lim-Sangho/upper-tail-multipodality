import UpperTailMultipodality.FixedDensities.Monotone
import UpperTailMultipodality.FixedDensities.Support.Perturb

/-!
# First-order conditions at an interior minimizer of `eq:fixed-problem`

Let `W` be a minimizer with `γ ≤ W ≤ 1-γ` almost everywhere and let `U₁, U₂` be directions with
`cqDet H W U₁ U₂ ≠ 0`.  Write `g = J_ε'(W)`.

* `lagrange_step` — for every bounded symmetric direction `Z`, inserting `θZ` and restoring both
  constraints along `U₁, U₂` (`exists_correction`) cannot lower `I_ε` to first order, so
  `∫∫ gZ + ξ₁'(0) ∫∫ gU₁ + ξ₂'(0) ∫∫ gU₂ = 0`.  This is the finite-direction form of the
  Lagrange multiplier rule.
* `lagrange_nonneg` — if `∫∫ Y = 0` and `∫∫ 𝒟_W Y > 0`, then `W + θY` is admissible for the
  second claim of `lem:fixed-monotone` for small `θ > 0`, so `∫∫ gY ≥ 0`.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `|θ| ≤ r` for `θ` near `0`. -/
theorem eventually_abs_le {r : ℝ} (hr : 0 < r) : ∀ᶠ θ in 𝓝 (0:ℝ), |θ| ≤ r :=
  Metric.eventually_nhds_iff.mpr ⟨r, hr, fun {y} hy => by
    rw [Real.dist_eq, sub_zero] at hy; exact hy.le⟩

/-- The integral `∫∫ J_ε'(W)(K - W)` for `K = W + θZ + ξ₁U₁ + ξ₂U₂`. -/
theorem integral_Jp'_mul_corr (W : Graphon) {ε γ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hγ : 0 < γ)
    (hγW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ) (Z U₁ U₂ : Kernel)
    (θ x₁ x₂ : ℝ) :
    ∫ z, Jp' ε (W.toFun z.1 z.2) * ((corrKernel W Z U₁ U₂ θ x₁ x₂).toFun z.1 z.2
        - W.toFun z.1 z.2) ∂gμ
      = θ * (∫ z, Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ)
        + x₁ * (∫ z, Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2 ∂gμ)
        + x₂ * (∫ z, Jp' ε (W.toFun z.1 z.2) * U₂.toFun z.1 z.2 ∂gμ) := by
  have hZ := (integrable_Jp'_mul W hε0 hε1 hγ hγW Z).const_mul θ
  have h1 := (integrable_Jp'_mul W hε0 hε1 hγ hγW U₁).const_mul x₁
  have h2 := (integrable_Jp'_mul W hε0 hε1 hγ hγW U₂).const_mul x₂
  have hfun : ∀ z : ℝ × ℝ, Jp' ε (W.toFun z.1 z.2) * ((corrKernel W Z U₁ U₂ θ x₁ x₂).toFun z.1 z.2
        - W.toFun z.1 z.2)
      = θ * (Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2)
        + x₁ * (Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2)
        + x₂ * (Jp' ε (W.toFun z.1 z.2) * U₂.toFun z.1 z.2) := fun z => by
    rw [corrKernel_apply]; ring
  have hZ1 : Integrable (fun z : ℝ × ℝ => θ * (Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2)
      + x₁ * (Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2)) gμ := hZ.add h1
  simp_rw [hfun]
  rw [integral_add hZ1 h2, integral_add hZ h1, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- **The finite-direction Lagrange condition.** -/
theorem lagrange_step (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {W : Graphon} (hW : IsFixedMinimizer H ε τ W) {γ : ℝ} (hγ : 0 < γ)
    (hγW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ)
    {U₁ U₂ : Kernel} (hdet : cqDet H W U₁ U₂ ≠ 0) (Z : Kernel) :
    (∫ z, Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ)
      + ((-(∫ z, Z.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)
          + (∫ z, U₂.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ))
          / cqDet H W U₁ U₂) * (∫ z, Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2 ∂gμ)
      + ((-(∫ z, U₁.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
          + (∫ z, Z.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ))
          / cqDet H W U₁ U₂) * (∫ z, Jp' ε (W.toFun z.1 z.2) * U₂.toFun z.1 z.2 ∂gμ) = 0 := by
  obtain ⟨he, ht, hmin⟩ := hW
  obtain ⟨ξ₁, ξ₂, hξ₁0, hξ₂0, hξ₁d, hξ₂d, hev⟩ := exists_correction H W Z U₁ U₂ hdet
  generalize ((-(∫ z, Z.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)
    + (∫ z, U₂.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ))
    / cqDet H W U₁ U₂) = v₁ at hξ₁d ⊢
  generalize ((-(∫ z, U₁.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
    + (∫ z, Z.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ))
    / cqDet H W U₁ U₂) = v₂ at hξ₂d ⊢
  have hlin := integral_Jp'_mul_corr W hε0 hε1 hγ hγW Z U₁ U₂
  generalize (∫ z, Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ) = cZ at hlin ⊢
  generalize (∫ z, Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2 ∂gμ) = c₁ at hlin ⊢
  generalize (∫ z, Jp' ε (W.toFun z.1 z.2) * U₂.toFun z.1 z.2 ∂gμ) = c₂ at hlin ⊢
  obtain ⟨CZ, hCZ0, hCZ⟩ := kernel_bound Z
  obtain ⟨C₁, hC₁0, hC₁⟩ := kernel_bound U₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := kernel_bound U₂
  obtain ⟨M, hM⟩ : ∃ M, M = 1 / ((γ / 2) * (1 - γ / 2)) := ⟨_, rfl⟩
  have hγ2 : γ ≤ 1 / 2 := by
    obtain ⟨z, hz⟩ := hγW.exists
    linarith [hz.1, hz.2]
  have hM0 : 0 ≤ M := by
    rw [hM]; have : 0 < 1 - γ / 2 := by linarith
    positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = CZ + (|v₁| + 1) * C₁ + (|v₂| + 1) * C₂ := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine eq_zero_of_forall_eventually fun δ hδ => ?_
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁, δ₁ = min 1 (δ / (2 * (|c₁| + |c₂| + 1))) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; exact lt_min one_pos (by positivity)
  have hδ₁1 : δ₁ ≤ 1 := hδ₁ ▸ min_le_left _ _
  have hδ₁c : δ₁ * (|c₁| + |c₂|) ≤ δ / 2 := by
    have h1 : δ₁ ≤ δ / (2 * (|c₁| + |c₂| + 1)) := hδ₁ ▸ min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg c₁, abs_nonneg c₂]
  have hev1 := eventually_abs_sub_le_of_hasDerivAt hξ₁d hδ₁0
  have hev2 := eventually_abs_sub_le_of_hasDerivAt hξ₂d hδ₁0
  have hevθ := eventually_abs_le (r := min (γ / 2 / (Q + 1)) (δ / 2 / (M * (Q + 1) ^ 2 + 1)))
    (lt_min (by positivity) (by positivity))
  filter_upwards [hev, hev1, hev2, hevθ] with θ ⟨hce, hct⟩ h1 h2 h3
  rw [hξ₁0, sub_zero] at h1
  rw [hξ₂0, sub_zero] at h2
  have hθQ : |θ| * Q ≤ γ / 2 := by
    have : |θ| ≤ γ / 2 / (Q + 1) := h3.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg θ]
  have hθM : M * (|θ| * Q) ^ 2 ≤ δ / 2 * |θ| := by
    have : |θ| ≤ δ / 2 / (M * (Q + 1) ^ 2 + 1) := h3.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    have hQQ : Q ^ 2 ≤ (Q + 1) ^ 2 := by nlinarith
    have h4 : M * Q ^ 2 * |θ| ≤ δ / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hQQ hM0, abs_nonneg θ]
    calc M * (|θ| * Q) ^ 2 = (M * Q ^ 2 * |θ|) * |θ| := by ring
      _ ≤ δ / 2 * |θ| := mul_le_mul_of_nonneg_right h4 (abs_nonneg θ)
  have hξ1 : |ξ₁ θ| ≤ (|v₁| + 1) * |θ| := by
    calc |ξ₁ θ| = |(ξ₁ θ - θ * v₁) + θ * v₁| := by ring_nf
      _ ≤ |ξ₁ θ - θ * v₁| + |θ * v₁| := abs_add_le _ _
      _ ≤ δ₁ * |θ| + |θ| * |v₁| := by rw [abs_mul]; linarith
      _ ≤ (|v₁| + 1) * |θ| := by nlinarith [abs_nonneg θ]
  have hξ2 : |ξ₂ θ| ≤ (|v₂| + 1) * |θ| := by
    calc |ξ₂ θ| = |(ξ₂ θ - θ * v₂) + θ * v₂| := by ring_nf
      _ ≤ |ξ₂ θ - θ * v₂| + |θ * v₂| := abs_add_le _ _
      _ ≤ δ₁ * |θ| + |θ| * |v₂| := by rw [abs_mul]; linarith
      _ ≤ (|v₂| + 1) * |θ| := by nlinarith [abs_nonneg θ]
  have hK : ∀ x y, |(corrKernel W Z U₁ U₂ θ (ξ₁ θ) (ξ₂ θ)).toFun x y - W.toFun x y|
      ≤ |θ| * Q := by
    intro x y
    rw [corrKernel_apply, show W.toFun x y + θ * Z.toFun x y + ξ₁ θ * U₁.toFun x y
      + ξ₂ θ * U₂.toFun x y - W.toFun x y
      = θ * Z.toFun x y + ξ₁ θ * U₁.toFun x y + ξ₂ θ * U₂.toFun x y by ring]
    calc |θ * Z.toFun x y + ξ₁ θ * U₁.toFun x y + ξ₂ θ * U₂.toFun x y|
        ≤ |θ| * |Z.toFun x y| + |ξ₁ θ| * |U₁.toFun x y| + |ξ₂ θ| * |U₂.toFun x y| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |θ| * CZ + ((|v₁| + 1) * |θ|) * C₁ + ((|v₂| + 1) * |θ|) * C₂ := by
          gcongr
          · exact hCZ x y
          · exact hC₁ x y
          · exact hC₂ x y
      _ = |θ| * Q := by rw [hQ]; ring
  obtain ⟨G, hGe, hGt, hGI⟩ := Ip_sub_le_taylor H W hε0 hε1 hγ hγW _ hθQ hK
  rw [← hM, hlin] at hGI
  have hle : W.Ip ε ≤ G.Ip ε :=
    hmin ▸ fixedValue_le H hε0 hε1 (hGe.trans (hce.trans he)) (hGt.trans (hct.trans ht))
  have hsplit : θ * cZ + ξ₁ θ * c₁ + ξ₂ θ * c₂
      = θ * (cZ + v₁ * c₁ + v₂ * c₂) + ((ξ₁ θ - θ * v₁) * c₁ + (ξ₂ θ - θ * v₂) * c₂) := by ring
  have herr : (ξ₁ θ - θ * v₁) * c₁ + (ξ₂ θ - θ * v₂) * c₂ ≤ δ / 2 * |θ| := by
    have e1 : (ξ₁ θ - θ * v₁) * c₁ ≤ δ₁ * |θ| * |c₁| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
    have e2 : (ξ₂ θ - θ * v₂) * c₂ ≤ δ₁ * |θ| * |c₂| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    have e3 : δ₁ * |θ| * |c₁| + δ₁ * |θ| * |c₂| = (δ₁ * (|c₁| + |c₂|)) * |θ| := by ring
    have e4 := mul_le_mul_of_nonneg_right hδ₁c (abs_nonneg θ)
    linarith
  linarith

/-- **Positivity of the multiplier direction.**  If `∫∫ Y = 0` and `∫∫ 𝒟_W Y > 0`, then
`∫∫ J_ε'(W) Y ≥ 0`. -/
theorem lagrange_nonneg (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsFixedMinimizer H ε τ W) {γ : ℝ} (hγ : 0 < γ)
    (hγW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ) (Y : Kernel)
    (hY0 : ∫ z, Y.toFun z.1 z.2 ∂gμ = 0)
    (hYD : 0 < ∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ) :
    0 ≤ ∫ z, Jp' ε (W.toFun z.1 z.2) * Y.toFun z.1 z.2 ∂gμ := by
  obtain ⟨he, ht, hmin⟩ := hW
  generalize hb : (∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ) = b at hYD
  generalize hc : (∫ z, Jp' ε (W.toFun z.1 z.2) * Y.toFun z.1 z.2 ∂gμ) = c
  -- `θ ↦ t(H, W + θY)` has derivative `b > 0` at `0`
  have hTs := hasStrictFDerivAt_tDensity_corrKernel H W Y Y Y
  have hinl : HasFDerivAt (fun θ : ℝ => ((θ, (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) 0 :=
    (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hf : HasDerivAt (fun θ : ℝ => (corrKernel W Y Y Y θ 0 0).tDensity H) b 0 := by
    have h := (hTs.hasFDerivAt.comp (0 : ℝ) (by simpa using hinl)).hasDerivAt
    have hval : ((linFun3 (∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ)).comp
        (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1 = b := by simp [hb]
    rw [hval] at h
    exact h
  have hf0 : (corrKernel W Y Y Y 0 0 0).tDensity H = τ := by
    rw [← ht, ← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  obtain ⟨CY, hCY0, hCY⟩ := kernel_bound Y
  obtain ⟨M, hM⟩ : ∃ M, M = 1 / ((γ / 2) * (1 - γ / 2)) := ⟨_, rfl⟩
  have hγ2 : γ ≤ 1 / 2 := by
    obtain ⟨z, hz⟩ := hγW.exists
    linarith [hz.1, hz.2]
  have hM0 : 0 ≤ M := by
    rw [hM]; have : 0 < 1 - γ / 2 := by linarith
    positivity
  refine nonneg_of_forall_eventually fun δ hδ => ?_
  have hev1 := eventually_abs_sub_le_of_hasDerivAt hf (half_pos hYD)
  have hevθ := eventually_abs_le (r := min (γ / 2 / (CY + 1)) (δ / (M * (CY + 1) ^ 2 + 1)))
    (lt_min (by positivity) (by positivity))
  filter_upwards [(hev1.and hevθ).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with θ ⟨h1, h2⟩ hθ
  have hθ0 : 0 < θ := hθ
  rw [abs_of_pos hθ0] at h1 h2
  rw [hf0] at h1
  have htgt : τ ≤ (corrKernel W Y Y Y θ 0 0).tDensity H := by
    have := (abs_le.mp h1).1
    nlinarith
  have hθC : θ * CY ≤ γ / 2 := by
    have : θ ≤ γ / 2 / (CY + 1) := h2.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hK : ∀ x y, |(corrKernel W Y Y Y θ 0 0).toFun x y - W.toFun x y| ≤ θ * CY := by
    intro x y
    rw [corrKernel_apply, zero_mul, add_zero, add_zero, add_sub_cancel_left, abs_mul,
      abs_of_pos hθ0]
    exact mul_le_mul_of_nonneg_left (hCY x y) hθ0.le
  obtain ⟨G, hGe, hGt, hGI⟩ := Ip_sub_le_taylor H W hε0 hε1 hγ hγW _ hθC hK
  rw [← hM, integral_Jp'_mul_corr W hε0 hε1 hγ hγW, hc, zero_mul, add_zero,
    add_zero] at hGI
  have hGe' : G.edgeDensity = ε := by
    rw [hGe, edgeDensity_corrKernel, hY0, he]; ring
  have hle : W.Ip ε ≤ G.Ip ε :=
    (fixed_monotone H hΔ hε0 hε1).2 τ ⟨hτ0, hτ1⟩ W he ht hmin G hGe' (hGt ▸ htgt)
  have hθM : M * (θ * CY) ^ 2 ≤ δ * θ := by
    have : θ ≤ δ / (M * (CY + 1) ^ 2 + 1) := h2.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    have hCC : CY ^ 2 ≤ (CY + 1) ^ 2 := by nlinarith
    have h4 : M * CY ^ 2 * θ ≤ δ := by
      nlinarith [mul_le_mul_of_nonneg_left hCC hM0]
    calc M * (θ * CY) ^ 2 = (M * CY ^ 2 * θ) * θ := by ring
      _ ≤ δ * θ := mul_le_mul_of_nonneg_right h4 hθ0.le
  linarith

end FixedDensities

end UpperTailMultipodality
