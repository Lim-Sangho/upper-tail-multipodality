import UpperTailMultipodality.FixedDensities.Monotone
import UpperTailMultipodality.FixedDensities.Support.InteriorAux
import UpperTailMultipodality.FixedDensities.Support.Lagrange

/-!
# Interiority and positive multipliers for fixed densities

`lem:fixed-interior` and `lem:fixed-multiplier`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:fixed-interior`.**  A minimizer of `eq:fixed-problem` that satisfies the constraint
qualification takes values in `[γ, 1-γ]` almost everywhere for some `γ > 0`. -/
theorem fixed_interior (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsFixedMinimizer H ε τ W)
    (hcq : ConstraintQualification H W) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ := by
  -- only `ε ∈ (0,1)` and the constraint qualification enter the interiority argument
  obtain ⟨-, -⟩ := hΔ
  have _ := hτ0.trans hτ1
  obtain ⟨η, hη, U₁, U₂, hU₁, hU₂, hdet⟩ := hcq
  obtain ⟨N, hN⟩ := interior_side_null H hε0 hε1 hW hη hU₁ hU₂ hdet
  obtain ⟨δ₀, hδ₀, hδ₀2, hJ'₀⟩ := Jp'_le_neg_of_small hε0 hε1 N
  obtain ⟨δ₁, hδ₁, hδ₁2, hJ'₁⟩ := Jp'_ge_of_near_one hε0 hε1 N
  obtain ⟨s₀, hs₀⟩ : ∃ s, s = min (δ₀ / 2) (η / 2) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s, s = min (δ₁ / 2) (η / 2) := ⟨_, rfl⟩
  have hs₀pos : 0 < s₀ := by rw [hs₀]; exact lt_min (half_pos hδ₀) (half_pos hη)
  have hs₁pos : 0 < s₁ := by rw [hs₁]; exact lt_min (half_pos hδ₁) (half_pos hη)
  have hs₀δ : s₀ ≤ δ₀ / 2 := hs₀ ▸ min_le_left _ _
  have hs₀η : s₀ ≤ η / 2 := hs₀ ▸ min_le_right _ _
  have hs₁δ : s₁ ≤ δ₁ / 2 := hs₁ ▸ min_le_left _ _
  have hs₁η : s₁ ≤ η / 2 := hs₁ ▸ min_le_right _ _
  -- values near `0`
  have hlow : ∀ᵐ z ∂gμ, s₀ ≤ W.toFun z.1 z.2 := by
    have hE := hN {z | W.toFun z.1 z.2 < s₀} 1 s₀ (measurableSet_lt W.meas' measurable_const)
      (fun x y h => by change W.toFun y x < s₀; rw [W.symm']; exact h)
      (by simp) hs₀pos
      (fun z hz => by
        change W.toFun z.1 z.2 < s₀ at hz
        refine ⟨by_contra fun h => ?_, by_contra fun h => ?_⟩
        · linarith [(hU₁ z.1 z.2 h).1]
        · linarith [(hU₂ z.1 z.2 h).1])
      (fun z hz θ hθ hθs => by
        change W.toFun z.1 z.2 < s₀ at hz
        have hW0 := W.nonneg' z.1 z.2
        rw [one_mul]
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have h1 := Jp_add_sub_le hε0 hε1 hW0 hθ (by linarith)
        have h2 := hJ'₀ (W.toFun z.1 z.2 + θ) (by linarith) (by linarith)
        nlinarith)
    rw [ae_iff]
    simpa only [not_le] using hE
  -- values near `1`
  have hhigh : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - s₁ := by
    have hE := hN {z | 1 - s₁ < W.toFun z.1 z.2} (-1) s₁
      (measurableSet_lt measurable_const W.meas')
      (fun x y h => by change 1 - s₁ < W.toFun y x; rw [W.symm']; exact h)
      (by simp) hs₁pos
      (fun z hz => by
        change 1 - s₁ < W.toFun z.1 z.2 at hz
        refine ⟨by_contra fun h => ?_, by_contra fun h => ?_⟩
        · linarith [(hU₁ z.1 z.2 h).2]
        · linarith [(hU₂ z.1 z.2 h).2])
      (fun z hz θ hθ hθs => by
        change 1 - s₁ < W.toFun z.1 z.2 at hz
        have hW1 := W.le_one' z.1 z.2
        rw [neg_one_mul, ← sub_eq_add_neg]
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have h1 := Jp_sub_sub_le hε0 hε1 hW1 hθ (by linarith)
        have h2 := hJ'₁ (W.toFun z.1 z.2 - θ) (by linarith) (by linarith)
        nlinarith)
    rw [ae_iff]
    simpa only [not_le] using hE
  refine ⟨min s₀ s₁, lt_min hs₀pos hs₁pos, ?_⟩
  filter_upwards [hlow, hhigh] with z h0 h1
  exact ⟨(min_le_left _ _).trans h0, h1.trans (by linarith [min_le_right s₀ s₁])⟩

/-- **`lem:fixed-multiplier`.**  A minimizer of `eq:fixed-problem` that satisfies the constraint
qualification satisfies `J_ε'(W) = α + μ𝒟_W` almost everywhere, `eq:fixed-stationarity`, for some `α` and
some `μ > 0`. -/
theorem fixed_multiplier (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsFixedMinimizer H ε τ W)
    (hcq : ConstraintQualification H W) :
    ∃ α μ : ℝ, 0 < μ ∧
      ∀ᵐ z ∂gμ, Jp' ε (W.toFun z.1 z.2) = α + μ * derivKernel H W z.1 z.2 := by
  obtain ⟨γ, hγ, hγW⟩ := fixed_interior H hΔ hε0 hε1 hτ0 hτ1 hW hcq
  obtain ⟨η, -, U₁, U₂, -, -, hdet⟩ := hcq
  have hγ2 : γ ≤ 1 / 2 := by
    obtain ⟨z, hz⟩ := hγW.exists
    linarith [hz.1, hz.2]
  -- names for the entries of `Γ_W(U₁,U₂)` and the first variations of `I_ε`
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = ∫ z, U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = ∫ z, U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = ∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, b = ∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = ∫ z, Jp' ε (W.toFun z.1 z.2) * U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = ∫ z, Jp' ε (W.toFun z.1 z.2) * U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = cqDet H W U₁ U₂ := ⟨_, rfl⟩
  have hdab : d = a₁ * b₂ - a₂ * b₁ := by rw [hd, cqDet, ha₁, ha₂, hb₁, hb₂]
  have hd0 : d ≠ 0 := hd ▸ hdet
  -- the Lagrange identity for every direction
  have hlag : ∀ Z : Kernel, (∫ z, Jp' ε (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ)
      = (b₂ * c₁ - b₁ * c₂) / d * (∫ z, Z.toFun z.1 z.2 ∂gμ)
        + (a₁ * c₂ - a₂ * c₁) / d * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ) := by
    intro Z
    have h := lagrange_step H hε0 hε1 hW hγ hγW hdet Z
    rw [← ha₁, ← ha₂, ← hb₁, ← hb₂, ← hc₁, ← hc₂, ← hd] at h
    field_simp
    field_simp at h
    linear_combination h
  generalize (b₂ * c₁ - b₁ * c₂) / d = α at hlag
  generalize (a₁ * c₂ - a₂ * c₁) / d = μ at hlag
  -- the Euler–Lagrange equation, tested against `1_{γ ≤ W ≤ 1-γ}(J_ε'(W) - α - μ𝒟_W)`
  have hEL : ∀ᵐ z ∂gμ, Jp' ε (W.toFun z.1 z.2) = α + μ * derivKernel H W z.1 z.2 := by
    obtain ⟨L, hL0, hL⟩ := Jp'_bdd_box hγ hε0 hε1
    have hSm : MeasurableSet {z : ℝ × ℝ | γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ} :=
      (measurableSet_le measurable_const W.meas').inter (measurableSet_le W.meas' measurable_const)
    have hFm : Measurable fun z : ℝ × ℝ =>
        Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2 :=
      (((measurable_Jp' ε).comp W.meas').sub measurable_const).sub
        (measurable_const.mul (measurable_derivKernel H W))
    let Z₀ : Kernel :=
      { toFun := fun x y => if γ ≤ W.toFun x y ∧ W.toFun x y ≤ 1 - γ then
            Jp' ε (W.toFun x y) - α - μ * derivKernel H W x y else 0
        symm' := fun x y => by simp only [W.symm' x y, derivKernel_symm H W x y]
        meas' := Measurable.ite hSm hFm measurable_const
        bdd' := ⟨L + |α| + |μ| * H.edgeFinset.card, fun x y => by
          split_ifs with h
          · have h1 := hL _ ⟨h.1, h.2⟩
            have h2 : |μ * derivKernel H W x y| ≤ |μ| * H.edgeFinset.card := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (abs_derivKernel_le H W x y) (abs_nonneg _)
            calc |Jp' ε (W.toFun x y) - α - μ * derivKernel H W x y|
                ≤ |Jp' ε (W.toFun x y)| + |α| + |μ * derivKernel H W x y| :=
                  (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
              _ ≤ L + |α| + |μ| * H.edgeFinset.card := by gcongr
          · rw [abs_zero]; positivity⟩ }
    have hZ₀ := hlag Z₀
    have hint : ∫ z, (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
        * Z₀.toFun z.1 z.2 ∂gμ = 0 := by
      have hfun : ∀ z : ℝ × ℝ, (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
          * Z₀.toFun z.1 z.2 = Jp' ε (W.toFun z.1 z.2) * Z₀.toFun z.1 z.2
            - α * Z₀.toFun z.1 z.2 - μ * (derivKernel H W z.1 z.2 * Z₀.toFun z.1 z.2) :=
        fun z => by ring
      have hi1 := integrable_Jp'_mul W Z₀ hε0 hε1 hγ (by linarith) hγW
      have hi2 := (kernel_integrable Z₀).const_mul α
      have hi3 := (integrable_derivKernel_mul H W Z₀).const_mul μ
      have hi12 : Integrable (fun z : ℝ × ℝ => Jp' ε (W.toFun z.1 z.2) * Z₀.toFun z.1 z.2
          - α * Z₀.toFun z.1 z.2) gμ := hi1.sub hi2
      simp_rw [hfun]
      rw [integral_sub hi12 hi3, integral_sub hi1 hi2, integral_const_mul, integral_const_mul,
        hZ₀]
      ring
    have hnn : 0 ≤ fun z : ℝ × ℝ => (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
        * Z₀.toFun z.1 z.2 := fun z => by
      show 0 ≤ (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
        * (if γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ then
            Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2 else 0)
      split_ifs
      · exact mul_self_nonneg _
      · rw [mul_zero]
    have hintg : Integrable (fun z : ℝ × ℝ =>
        (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2) * Z₀.toFun z.1 z.2) gμ := by
      obtain ⟨C, -, hC⟩ := kernel_bound Z₀
      refine integrable_mul_of_ae_bdd hFm Z₀.meas' (L := L + |α| + |μ| * H.edgeFinset.card)
        ?_ (ae_of_all _ fun z => hC z.1 z.2)
      filter_upwards [hγW] with z hz
      have h1 := hL _ ⟨hz.1, hz.2⟩
      have h2 : |μ * derivKernel H W z.1 z.2| ≤ |μ| * H.edgeFinset.card := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_derivKernel_le H W _ _) (abs_nonneg _)
      calc |Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2|
          ≤ |Jp' ε (W.toFun z.1 z.2)| + |α| + |μ * derivKernel H W z.1 z.2| :=
            (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ L + |α| + |μ| * H.edgeFinset.card := by gcongr
    have hzero := (integral_eq_zero_iff_of_nonneg hnn hintg).mp hint
    filter_upwards [hzero, hγW] with z hz hzγ
    have : (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
        * (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2) = 0 := by
      have h := hz
      simp only [Pi.zero_apply] at h
      change (Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2)
        * (if γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ then
            Jp' ε (W.toFun z.1 z.2) - α - μ * derivKernel H W z.1 z.2 else 0) = 0 at h
      rwa [if_pos hzγ] at h
    have := mul_self_eq_zero.mp this
    linarith
  refine ⟨α, μ, ?_, hEL⟩
  -- `μ ≥ 0` from the direction `Y = d(a₁U₂ - a₂U₁)`
  have hμ0 : 0 ≤ μ := by
    let Y : Kernel := (-(d * a₂)) • U₁ + (d * a₁) • U₂
    have hYapply : ∀ x y, Y.toFun x y = -(d * a₂) * U₁.toFun x y + d * a₁ * U₂.toFun x y :=
      fun x y => rfl
    have hY0 : ∫ z, Y.toFun z.1 z.2 ∂gμ = 0 := by
      simp_rw [hYapply]
      rw [integral_add ((kernel_integrable U₁).const_mul _) ((kernel_integrable U₂).const_mul _),
        integral_const_mul, integral_const_mul, ← ha₁, ← ha₂]
      ring
    have hYD : ∫ z, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2 ∂gμ = d * d := by
      have hfun : ∀ z : ℝ × ℝ, derivKernel H W z.1 z.2 * Y.toFun z.1 z.2
          = -(d * a₂) * (derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2)
            + d * a₁ * (derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2) := fun z => by
        rw [hYapply]; ring
      simp_rw [hfun]
      rw [integral_add ((integrable_derivKernel_mul H W U₁).const_mul _)
        ((integrable_derivKernel_mul H W U₂).const_mul _), integral_const_mul, integral_const_mul,
        ← hb₁, ← hb₂]
      rw [hdab]; ring
    have hpos : 0 < d * d := mul_self_pos.mpr hd0
    have hnn := lagrange_nonneg H hΔ hε0 hε1 hτ0 hτ1 hW hγ hγW Y hY0 (hYD ▸ hpos)
    rw [hlag Y, hY0, hYD, mul_zero, zero_add] at hnn
    exact nonneg_of_mul_nonneg_left hnn hpos
  refine lt_of_le_of_ne hμ0 fun hμ => ?_
  -- if `μ = 0`, then `J_ε'(W)` and hence `W` are constant
  subst hμ
  have hae0 : ∀ᵐ z ∂gμ, Jp' ε (W.toFun z.1 z.2) = α ∧ γ ≤ W.toFun z.1 z.2 ∧
      W.toFun z.1 z.2 ≤ 1 - γ := by
    filter_upwards [hEL, hγW] with z h1 h2
    exact ⟨by rw [h1]; ring, h2⟩
  obtain ⟨z₀, hz₀⟩ := hae0.exists
  have hconst : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W.toFun z₀.1 z₀.2 := by
    filter_upwards [hae0] with z hz
    exact (Jp'_strictMonoOn hε0 hε1).injOn ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
      ⟨by linarith [hz₀.2.1], by linarith [hz₀.2.2]⟩ (hz.1.trans hz₀.1.symm)
  obtain ⟨he, ht, -⟩ := hW
  have he' := edgeDensity_ae_const W hconst
  have ht' := tDensity_ae_const W H hconst
  rw [he] at he'
  rw [ht, ← he'] at ht'
  exact absurd ht' hτ0.ne'

end UpperTailMultipodality
