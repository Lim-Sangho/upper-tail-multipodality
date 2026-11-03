import UpperTailMultipodality.RowCriterion.Finiteness.Functional

/-!
# A positive lower bound for the second variation (`lem:row-lower-bound`)

At a global minimizer `u` of `ℱ_W` the second variation `Q_u` is nonnegative
(`secondVariation_nonneg`).  This file upgrades that to the quantitative bound of
`lem:row-lower-bound`: there is `c_u > 0` with `Q_u(h) ≥ c_u ‖h‖₂²` for every mean-zero `h`
(`exists_secondVariation_lower_bound`).

The paper gets the uniform constant from weak `L²` compactness and the compactness of `T_{K_u}`.
Here it comes from combining two elementary estimates, which avoids weak compactness entirely.
Writing `h = h₊ - h₋` with disjoint supports, `secondVariation_split` gives

`Q_u(h) = Q_u(h₊) + Q_u(h₋) + D²𝒫_W(u)[h₊,h₋] + D²𝒫_W(u)[h₋,h₊]`,

so discarding the two nonnegative diagonal terms and bounding the mixed ones below with
`integ_combinedGradDeriv_mul_ge` gives a multiple of the *`L¹`* norm squared
(`secondVariation_ge_L1_sq`):

* (A) `Q_u(h) ≥ (κ/2) ‖h‖₁²`, where `κ := μ_{j₀} c^N ω^{m_{j₀}} > 0`.

In the opposite regime, where `h` is concentrated and `‖h‖₁` is small, the entropy term wins:
`J_q'' ≥ 4` (`four_le_Jp''`, the first half of `eq:row-entropy-curvature`) together with the
`L¹`-to-pointwise bound `abs_combinedGradDeriv_apply_le` gives (`secondVariation_ge_sq_sub`)

* (B) `Q_u(h) ≥ 8 ‖h‖₂² - C ‖h‖₁²`, where `C := combinedLipConst Hs μ ≥ 0`.

Adding `2C` times (A) to `κ` times (B) cancels `‖h‖₁²` exactly and leaves

`(2C + κ) Q_u(h) ≥ 8κ ‖h‖₂²`,

which is `lem:row-lower-bound` with the explicit constant `c_u = 8κ/(2C + κ)`.  Strict positivity
at a nonzero mean-zero direction (`secondVariation_pos`), which is what `lem:bordered` uses for
injectivity, is now a corollary.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {W : Graphon} {q α : ℝ} {μ : ι → ℝ}

/-- The integrand of the entropy part of the second variation is integrable. -/
theorem integrable_Jpp_mul_sq {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (k : BddMeas) :
    Integrable (fun y => Jp'' (u y) * k y ^ 2) unitμ := by
  have hmeasJ'' : Measurable Jp'' := by unfold Jp''; fun_prop
  refine integrable_of_abs_le ((hmeasJ''.comp u.measurable).mul (k.measurable.pow_const 2))
    (1 / (c * (1 - d)) * ‖k‖ ^ 2) fun y => ?_
  rw [abs_mul, abs_pow]
  have hJ := Jp''_mem_of_mem_Icc hc hd (hu y)
  rw [abs_of_pos hJ.1]
  exact mul_le_mul hJ.2 (pow_le_pow_left₀ (abs_nonneg _) (k.abs_apply_le_norm y) 2)
    (by positivity) (hJ.1.le.trans hJ.2)

/-- The splitting of the second variation along the positive and negative parts. -/
theorem secondVariation_split {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    secondVariation Hs W μ u h
      = secondVariation Hs W μ u (BddMeas.posPart h)
        + secondVariation Hs W μ u (BddMeas.negPart h)
        + (BddMeas.integ (combinedGradDeriv Hs W μ u (BddMeas.posPart h) * BddMeas.negPart h)
          + BddMeas.integ (combinedGradDeriv Hs W μ u (BddMeas.negPart h)
            * BddMeas.posPart h)) := by
  set a := BddMeas.posPart h with ha
  set b := BddMeas.negPart h with hb
  have hab : a * b = 0 := BddMeas.posPart_mul_negPart h
  have hh : h = a - b := (BddMeas.posPart_sub_negPart h).symm
  -- the entropy part splits pointwise
  have hsq : ∀ y, h y ^ 2 = a y ^ 2 + b y ^ 2 := by
    intro y
    have h0 : a y * b y = 0 := by
      have := congrArg (fun f : BddMeas => f y) hab
      simpa [BddMeas.mul_apply] using this
    have : h y = a y - b y := by rw [hh]; rfl
    rw [this]; nlinarith [h0]
  have hentropy : ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ
      = (∫ y, Jp'' (u y) * a y ^ 2 ∂unitμ) + ∫ y, Jp'' (u y) * b y ^ 2 ∂unitμ := by
    rw [← integral_add (integrable_Jpp_mul_sq hc hd hu a) (integrable_Jpp_mul_sq hc hd hu b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Jp'' (u y) * h y ^ 2 = Jp'' (u y) * a y ^ 2 + Jp'' (u y) * b y ^ 2
    rw [hsq y]; ring
  -- the gradient part splits by bilinearity
  have hgrad : combinedGradDeriv Hs W μ u h * h
      = combinedGradDeriv Hs W μ u a * a + combinedGradDeriv Hs W μ u b * b
        - (combinedGradDeriv Hs W μ u a * b + combinedGradDeriv Hs W μ u b * a) := by
    rw [hh, map_sub]
    ring
  rw [secondVariation, secondVariation, secondVariation, hentropy, hgrad, map_sub, map_add,
    map_add]
  ring

/-- For a mean-zero direction the two parts have equal integral, half of its `L¹` norm. -/
theorem integ_posPart_negPart_of_mean_zero {h : BddMeas} (hmean : BddMeas.integ h = 0) :
    BddMeas.integ (BddMeas.posPart h) = (∫ y, |h y| ∂unitμ) / 2 ∧
      BddMeas.integ (BddMeas.negPart h) = (∫ y, |h y| ∂unitμ) / 2 := by
  have hsub : BddMeas.integ (BddMeas.posPart h) - BddMeas.integ (BddMeas.negPart h) = 0 := by
    rw [← map_sub, BddMeas.posPart_sub_negPart h, hmean]
  have habs : BddMeas.integ (BddMeas.posPart h) + BddMeas.integ (BddMeas.negPart h)
      = ∫ y, |h y| ∂unitμ := by
    rw [← map_add, BddMeas.integ_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (BddMeas.posPart h + BddMeas.negPart h) y = |h y|
    rw [BddMeas.add_apply, BddMeas.posPart_apply, BddMeas.negPart_apply]
    rcases le_total (h y) 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (by linarith : (0:ℝ) ≤ -h y), abs_of_nonpos hy]
      ring
    · rw [max_eq_left hy, max_eq_right (by linarith : -h y ≤ 0), abs_of_nonneg hy]
      ring
  constructor <;> linarith

/-- **The mixed second variation is bounded from `L¹ × L¹`.**  This is the upper counterpart of
`integ_combinedGradDeriv_mul_ge`, obtained from the pointwise bound
`abs_combinedGradDeriv_apply_le`. -/
theorem abs_integ_combinedGradDeriv_mul_le (hμ : ∀ j, 0 ≤ μ j) {u : BddMeas}
    (hu : UnitValued u) (a b : BddMeas) :
    |BddMeas.integ (combinedGradDeriv Hs W μ u a * b)|
      ≤ combinedLipConst Hs μ * (∫ y, |a y| ∂unitμ) * ∫ y, |b y| ∂unitμ := by
  rw [BddMeas.integ_apply]
  have h1 : |∫ y, (combinedGradDeriv Hs W μ u a * b) y ∂unitμ|
      ≤ ∫ y, |(combinedGradDeriv Hs W μ u a * b) y| ∂unitμ := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := unitμ)
        (f := fun y => (combinedGradDeriv Hs W μ u a * b) y)
  have h2 : ∫ y, |(combinedGradDeriv Hs W μ u a * b) y| ∂unitμ
      ≤ ∫ y, (combinedLipConst Hs μ * ∫ t, |a t| ∂unitμ) * |b y| ∂unitμ := by
    refine integral_mono (combinedGradDeriv Hs W μ u a * b).integrable.abs
      (b.integrable.abs.const_mul _) fun y => ?_
    rw [BddMeas.mul_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_combinedGradDeriv_apply_le hμ hu a y) (abs_nonneg _)
  rw [integral_const_mul] at h2
  exact h1.trans h2

/-- **Estimate (B).**  The entropy curvature `J_q'' ≥ 4` dominates the rooted-density term up to a
multiple of the squared `L¹` norm: `Q_u(h) ≥ 8‖h‖₂² - C‖h‖₁²`. -/
theorem secondVariation_ge_sq_sub (hμ : ∀ j, 0 ≤ μ j) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    8 * (∫ y, h y ^ 2 ∂unitμ)
        - combinedLipConst Hs μ * (∫ y, |h y| ∂unitμ) * ∫ y, |h y| ∂unitμ
      ≤ secondVariation Hs W μ u h := by
  have hU : UnitValued u := fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩
  have hsq : Integrable (fun y => h y ^ 2) unitμ :=
    (h * h).integrable.congr (Filter.Eventually.of_forall fun y => by
      show (h * h) y = h y ^ 2
      rw [BddMeas.mul_apply]; ring)
  have hentropy : 8 * (∫ y, h y ^ 2 ∂unitμ) ≤ 2 * ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ := by
    have h4 : ∫ y, 4 * h y ^ 2 ∂unitμ ≤ ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ := by
      refine integral_mono (hsq.const_mul 4) (integrable_Jpp_mul_sq hc hd hu h) fun y => ?_
      exact mul_le_mul_of_nonneg_right
        (four_le_Jp'' (hc.trans_le (hu y).1) ((hu y).2.trans_lt hd)) (sq_nonneg _)
    rw [integral_const_mul] at h4
    linarith
  have hgrad := abs_le.mp
    (abs_integ_combinedGradDeriv_mul_le (Hs := Hs) (W := W) (μ := μ) hμ hU h h)
  simp only [secondVariation]
  linarith [hgrad.2]

/-- **Estimate (A).**  Discarding the two nonnegative diagonal terms of `secondVariation_split`
and bounding the mixed ones below gives `Q_u(h) ≥ (κ/2)‖h‖₁²` for mean-zero `h`, with
`κ = μ_{j₀} c^N ω^{m_{j₀}}`. -/
theorem secondVariation_ge_L1_sq {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y)
    {h : BddMeas} (hmean : BddMeas.integ h = 0) :
    μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card) / 2
        * ((∫ y, |h y| ∂unitμ) * ∫ y, |h y| ∂unitμ)
      ≤ secondVariation Hs W μ u h := by
  obtain ⟨hia, hib⟩ := integ_posPart_negPart_of_mean_zero hmean
  have hane : ∀ y, 0 ≤ BddMeas.posPart h y := BddMeas.posPart_nonneg h
  have hbne : ∀ y, 0 ≤ BddMeas.negPart h y := BddMeas.negPart_nonneg h
  have hQa := secondVariation_nonneg (Hs := Hs) (W := W) (α := α) (μ := μ) hq0 hq1 hc hd hu hmin
    hEL (BddMeas.posPart h)
  have hQb := secondVariation_nonneg (Hs := Hs) (W := W) (α := α) (μ := μ) hq0 hq1 hc hd hu hmin
    hEL (BddMeas.negPart h)
  have hcross : ∀ x y : BddMeas, (∀ t, 0 ≤ x t) → (∀ t, 0 ≤ y t) →
      μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card)
          * BddMeas.integ x * BddMeas.integ y
        ≤ BddMeas.integ (combinedGradDeriv Hs W μ u x * y) := by
    intro x y hx hy
    exact integ_combinedGradDeriv_mul_ge hμ hΔ hω0.le hω1 hWω hc.le hc1
      (fun t => (hu t).1) hx hy
  have h1 := hcross _ _ hane hbne
  have h2 := hcross _ _ hbne hane
  rw [hia, hib] at h1 h2
  rw [secondVariation_split hc hd hu h]
  nlinarith [h1, h2, hQa, hQb]

/-- **`lem:row-lower-bound`.**  At a global minimizer `u` of `ℱ_W` over rows with values in
`[c,d] ⊆ (0,1)` satisfying `eq:row-euler`, there is `c_u > 0` such that `Q_u(h) ≥ c_u ‖h‖₂²` for
every direction `h` of mean zero.  The explicit constant is `8κ/(2C + κ)` with
`κ = μ_{j₀} c^N ω^{m_{j₀}}` and `C = combinedLipConst Hs μ`. -/
theorem exists_secondVariation_lower_bound {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    ∃ cu : ℝ, 0 < cu ∧ ∀ h : BddMeas, BddMeas.integ h = 0 →
      cu * (∫ y, h y ^ 2 ∂unitμ) ≤ secondVariation Hs W μ u h := by
  have hκpos : 0 < μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card) := by positivity
  have hCnonneg : 0 ≤ combinedLipConst Hs μ := combinedLipConst_nonneg hμ
  have hden : 0 < 2 * combinedLipConst Hs μ
      + μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card) := by linarith
  refine ⟨8 * (μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card))
    / (2 * combinedLipConst Hs μ
      + μ j₀ * (c ^ Fintype.card V * ω ^ (Hs j₀).edgeFinset.card)), by positivity,
    fun h hmean => ?_⟩
  have hA := secondVariation_ge_L1_sq (Hs := Hs) (W := W) (q := q) (α := α) (μ := μ) (j₀ := j₀)
    hμ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL hmean
  have hB := secondVariation_ge_sq_sub (Hs := Hs) (W := W) (μ := μ) hμ hc hd hu h
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hA, hB]

/-- **Strict positivity of the second variation on mean-zero directions.**  A corollary of
`exists_secondVariation_lower_bound`: at a global minimizer `u` of `ℱ_W` over rows with values in
`[c,d] ⊆ (0,1)` satisfying `eq:row-euler`, `Q_u(h) > 0` for every `h` of mean zero that does not
vanish almost everywhere.  This is the form `lem:bordered` uses for injectivity. -/
theorem secondVariation_pos {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y)
    {h : BddMeas} (hmean : BddMeas.integ h = 0) (hne : ¬ (⇑h =ᵐ[unitμ] 0)) :
    0 < secondVariation Hs W μ u h := by
  obtain ⟨cu, hcu, hbound⟩ := exists_secondVariation_lower_bound (Hs := Hs) (W := W) (q := q)
    (α := α) (μ := μ) (j₀ := j₀) hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL
  have hsq : Integrable (fun y => h y ^ 2) unitμ :=
    (h * h).integrable.congr (Filter.Eventually.of_forall fun y => by
      show (h * h) y = h y ^ 2
      rw [BddMeas.mul_apply]; ring)
  have hpos : 0 < ∫ y, h y ^ 2 ∂unitμ := by
    rcases lt_or_eq_of_le (integral_nonneg (f := fun y => h y ^ 2) fun y => sq_nonneg _) with
      hgt | hzero
    · exact hgt
    · exact absurd (by
        filter_upwards [(integral_eq_zero_iff_of_nonneg (f := fun y => h y ^ 2)
          (fun y => sq_nonneg _) hsq).mp hzero.symm] with y hy
        simpa [pow_eq_zero_iff] using hy) hne
  exact lt_of_lt_of_le (by positivity) (hbound h hmean)

end UpperTailMultipodality
