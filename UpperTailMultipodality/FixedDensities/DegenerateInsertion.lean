import UpperTailMultipodality.FixedDensities.Degenerate
import UpperTailMultipodality.FixedDensities.Support.DegenerateInsertionAux

/-!
# Insertion at a degenerate minimizer (`lem:degenerate-insertion`)

At a degenerate minimizer `W` of `eq:fixed-problem` the first variations of the two constraints
are proportional on `Ω = {0 < W < 1}`, with the constant `a` of `lem:degenerate-forms` (the
paper's `κ`), so an
insertion can be combined with an interior correction in only one way.  The resulting first-order
change of the `H`-density is

`ℬ_W(u) = ℛ_W(u) - N τ - 2a(∫u - ε)`,

and `eq:degenerate-insertion` says that it is nonpositive on every row, with equality for almost
every row of `W`.

The proof follows the insertion of a block of measure `s` with row `u` and internal value `ε`
into the smoothed graphon `W_θ = (1-θ)W + θε`, corrected by a multiple `ζ V` of the indicator of
`Ω_η(W)`.  Unlike the argument in the paper, the two constraints are not solved simultaneously:
the edge constraint is affine in `ζ`, so the choice `ζ = g(s) = s/(1-s)` for the direction
`Z = -2(∫u - ε)|Ω_η(W)|^{-1} V` restores the edge density *exactly*, and the `H`-density
constraint is then reached by the intermediate value theorem in `θ`, using `insertionPoly_taylor`
to see that the increment of the `H`-density is at least `b s` with `b = ℬ_W(u)/2`.  The deficit
`d_θ = τ - t(H,W_θ)` of the smoothing therefore satisfies `d_θ ≥ b s`, while the cost of the
insertion and of the correction is `O(s)`; since the smoothing gain dominates, `degenerate_gain`
produces a feasible competitor of strictly smaller cost.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 800000 in
/-- **`lem:degenerate-insertion`, `eq:degenerate-insertion`.**  With `a` the constant of
`lem:degenerate-forms`, the functional `ℬ_W(u) = ℛ_W(u) - Nτ - 2a(∫u - ε)` is nonpositive on
every row, and almost every row of `W` makes it vanish. -/
theorem degenerate_insertion (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ a : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hdeg : ¬ ConstraintQualification H W)
    (ha : ∀ᵐ z ∂gμ, 0 < W.toFun z.1 z.2 → W.toFun z.1 z.2 < 1 → derivKernel H W z.1 z.2 = a) :
    (∀ u : ℝ → ℝ, IsRow u →
        totalRootedDensity H W u - (Fintype.card V : ℝ) * τ
          - 2 * a * ((∫ y, u y ∂unitμ) - ε) ≤ 0) ∧
      (∀ᵐ x ∂unitμ, totalRootedDensity H W (W.row x) - (Fintype.card V : ℝ) * τ
          - 2 * a * ((∫ y, W.row x y ∂unitμ) - ε) = 0) := by
  obtain ⟨he, ht, hI⟩ := (isEntropyMaximizer_iff H hε0 hε1 W).mp hW
  have hqε : ε ∈ Set.Icc (0:ℝ) 1 := ⟨hε0.le, hε1.le⟩
  have hm0 : (0:ℝ) ≤ (H.edgeFinset.card : ℝ) := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmpos : (0:ℝ) < (H.edgeFinset.card : ℝ) + 1 := by linarith
  -- the interior window `Ω_η(W)`
  obtain ⟨η, hη0, hηpos⟩ := exists_interior_window H hε0 hε1 hτ0.le hτ1 ⟨he, ht, hI⟩
  obtain ⟨A, hAdef⟩ :
      ∃ A, A = {z : ℝ × ℝ | η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η} := ⟨_, rfl⟩
  have hAm : MeasurableSet A := by
    rw [hAdef]
    exact (measurableSet_lt measurable_const W.meas').inter
      (measurableSet_lt W.meas' measurable_const)
  have hAsymm : ∀ x y, (x, y) ∈ A → (y, x) ∈ A := by
    intro x y h
    rw [hAdef] at h ⊢
    simpa only [Set.mem_ofPred_eq, W.symm' y x] using h
  have hc0 : 0 < gμ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAdef ▸ hηpos) (measure_ne_top _ _)
  obtain ⟨Vk, hVkdef⟩ : ∃ K : Kernel, K = indicatorKernel A hAm hAsymm 1 := ⟨_, rfl⟩
  have hVkzero : ∀ x y, (x, y) ∉ A → Vk.toFun x y = 0 := by
    intro x y h
    rw [hVkdef, indicatorKernel_apply]
    exact Set.indicator_of_notMem h _
  have hVkabs : ∀ x y, |Vk.toFun x y| ≤ 1 := by
    intro x y
    rw [hVkdef, indicatorKernel_apply]
    by_cases h : (x, y) ∈ A
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num
  have hVkint : ∫ z, Vk.toFun z.1 z.2 ∂gμ = gμ.real A := by
    rw [hVkdef, integral_indicatorKernel, one_mul]
  have hVkD : ∫ z, derivKernel H W z.1 z.2 * Vk.toFun z.1 z.2 ∂gμ = a * gμ.real A := by
    have hcongr : ∀ᵐ z ∂gμ, derivKernel H W z.1 z.2 * Vk.toFun z.1 z.2
        = a * Vk.toFun z.1 z.2 := by
      filter_upwards [ha] with z hz
      by_cases hmem : z ∈ A
      · have h1 : η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η := by
          rw [hAdef] at hmem; exact hmem
        rw [hz (lt_trans hη0 h1.1) (by linarith [h1.2])]
      · have hz0 : Vk.toFun z.1 z.2 = 0 := hVkzero z.1 z.2 (by
          intro hh; exact hmem (by simpa using hh))
        rw [hz0]; ring
    rw [integral_congr_ae hcongr, integral_const_mul, hVkint]
  -- the window in which the correction keeps the graphon interior
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min η (min ε (1 - ε)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]; exact lt_min hη0 (lt_min hε0 (by linarith))
  have hκη : κ ≤ η := hκdef ▸ min_le_left _ _
  have hκε : κ ≤ ε := le_trans (hκdef ▸ min_le_right _ _) (min_le_left _ _)
  have hκε' : κ ≤ 1 - ε := le_trans (hκdef ▸ min_le_right _ _) (min_le_right _ _)
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_Jp (p := ε) hε0 hε1
    (show (0:ℝ) < κ / 2 by positivity) (show 1 - κ / 2 < 1 by linarith)
  obtain ⟨MJ, hMJ0, hMJ⟩ := exists_bound_integral_Jp (p := ε) hε0 hε1
  -- the smoothing path
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ → Graphon,
      M = fun θ => clampGraphon (Kernel.ofGraphon W + θ • constSubKernel W ε) := ⟨_, rfl⟩
  have hMval : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ x y,
      (M θ).toFun x y = (1 - θ) * W.toFun x y + θ * ε := by
    intro θ hθ x y
    have hmem : W.toFun x y + θ * (ε - W.toFun x y) ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨?_, ?_⟩ <;>
        nlinarith [W.nonneg' x y, W.le_one' x y, hθ.1, hθ.2, hε0.le, hε1.le]
    rw [hMdef]
    show max 0 (min 1 (W.toFun x y + θ * (ε - W.toFun x y))) = (1 - θ) * W.toFun x y + θ * ε
    rw [min_eq_right hmem.2, max_eq_right hmem.1]
    ring
  have hMe : ∀ θ ∈ Set.Icc (0:ℝ) 1, (M θ).edgeDensity = ε := by
    intro θ hθ
    have hcongr : ∀ᵐ z ∂gμ, (M θ).toFun z.1 z.2 = (1 - θ) * W.toFun z.1 z.2 + θ * ε :=
      ae_of_all _ fun z => hMval θ hθ z.1 z.2
    show (∫ z, (M θ).toFun z.1 z.2 ∂gμ) = ε
    rw [integral_congr_ae hcongr, integral_add (W.integrable_self.const_mul _)
      (integrable_const _), integral_const_mul, integral_const]
    simp only [smul_eq_mul, probReal_univ, one_mul]
    rw [← Graphon.edgeDensity, he]
    ring
  have hMLip : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ x y, |(M θ).toFun x y - W.toFun x y| ≤ θ := by
    intro θ hθ x y
    rw [hMval θ hθ x y]
    have hE : (1 - θ) * W.toFun x y + θ * ε - W.toFun x y = θ * (ε - W.toFun x y) := by ring
    rw [hE, abs_mul, abs_of_nonneg hθ.1]
    have h3 : |ε - W.toFun x y| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [W.le_one' x y, hε0], by linarith [W.nonneg' x y, hε1]⟩
    nlinarith [hθ.1]
  have hMLip2 : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ θ' ∈ Set.Icc (0:ℝ) 1, ∀ x y,
      |(M θ).toFun x y - (M θ').toFun x y| ≤ |θ - θ'| := by
    intro θ hθ θ' hθ' x y
    rw [hMval θ hθ x y, hMval θ' hθ' x y]
    have hE : (1 - θ) * W.toFun x y + θ * ε - ((1 - θ') * W.toFun x y + θ' * ε)
        = (θ - θ') * (ε - W.toFun x y) := by ring
    rw [hE, abs_mul]
    have h3 : |ε - W.toFun x y| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [W.le_one' x y, hε0], by linarith [W.nonneg' x y, hε1]⟩
    nlinarith [abs_nonneg (θ - θ'), abs_nonneg (ε - W.toFun x y)]
  have hMwin : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ x y, (x, y) ∈ A →
      (M θ).toFun x y ∈ Set.Icc κ (1 - κ) := by
    intro θ hθ x y hxy
    have h1 : η < W.toFun x y ∧ W.toFun x y < 1 - η := by rw [hAdef] at hxy; exact hxy
    rw [hMval θ hθ x y]
    refine ⟨?_, ?_⟩
    · nlinarith [hθ.1, hθ.2, h1.1]
    · nlinarith [hθ.1, hθ.2, h1.2]
  have hM0 : (M 0).tDensity H = τ := by
    rw [← ht]
    refine graphon_tDensity_congr_ae H (ae_of_all _ fun z => ?_)
    rw [hMval 0 ⟨le_rfl, zero_le_one⟩ z.1 z.2]; ring
  -- the reparametrization `g(s) = s/(1-s)`
  have hζ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 0 ≤ s / (1 - s) ∧ s / (1 - s) ≤ 2 * s := by
    intro s hs0 hs2
    have hs1 : (0:ℝ) < 1 - s := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hs1]
    nlinarith
  /- The insertion inequality on rows. -/
  have hrow : ∀ u : ℝ → ℝ, IsRow u →
      totalRootedDensity H W u - (Fintype.card V : ℝ) * τ
        - 2 * a * ((∫ y, u y ∂unitμ) - ε) ≤ 0 := by
    intro u hu
    by_contra hcon
    push Not at hcon
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (∫ y, u y ∂unitμ) - ε := ⟨_, rfl⟩
    obtain ⟨Bq, hBqdef⟩ : ∃ B : ℝ,
        B = totalRootedDensity H W u - (Fintype.card V : ℝ) * τ - 2 * a * E := ⟨_, rfl⟩
    have hBq0 : 0 < Bq := by rw [hBqdef, hEdef]; exact hcon
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Bq / 2 := ⟨_, rfl⟩
    have hb0 : 0 < b := by rw [hbdef]; positivity
    have hBb : Bq = 2 * b := by rw [hbdef]; ring
    -- the correction direction
    obtain ⟨vc, hvcdef⟩ : ∃ v : ℝ, v = -2 * E / gμ.real A := ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ K : Kernel, K = vc • Vk := ⟨_, rfl⟩
    obtain ⟨cz, hczdef⟩ : ∃ c : ℝ, c = |vc| := ⟨_, rfl⟩
    have hcz0 : 0 ≤ cz := by rw [hczdef]; exact abs_nonneg _
    have hZval : ∀ x y, Z.toFun x y = vc * Vk.toFun x y := by
      intro x y; rw [hZdef]; rfl
    have hcz : ∀ x y, |Z.toFun x y| ≤ cz := by
      intro x y
      rw [hZval, abs_mul, hczdef]
      nlinarith [hVkabs x y, abs_nonneg vc, abs_nonneg (Vk.toFun x y)]
    have hZsupp : ∀ x y, Z.toFun x y ≠ 0 → (x, y) ∈ A := by
      intro x y hne
      by_contra hmem
      exact hne (by rw [hZval, hVkzero x y hmem]; ring)
    have hZint : ∫ z, Z.toFun z.1 z.2 ∂gμ = -2 * E := by
      have h : ∫ z, Z.toFun z.1 z.2 ∂gμ = vc * gμ.real A := by
        rw [← hVkint, ← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun z => hZval z.1 z.2)
      rw [h, hvcdef]
      field_simp
    have hZD : ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ = -2 * E * a := by
      have h : ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ
          = vc * (a * gμ.real A) := by
        rw [← hVkD, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        show derivKernel H W z.1 z.2 * Z.toFun z.1 z.2
          = vc * (derivKernel H W z.1 z.2 * Vk.toFun z.1 z.2)
        rw [hZval]; ring
      rw [h, hvcdef]
      field_simp
    have hBeq : Bq = (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        + totalRootedDensity H W u - (Fintype.card V : ℝ) * τ := by
      rw [hZD, hBqdef]; ring
    -- admissibility of the correction
    have hadm : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s * cz ≤ κ / 2 →
        ∀ x y, (M θ).toFun x y + s / (1 - s) * Z.toFun x y ∈ Set.Icc (0:ℝ) 1 := by
      intro θ hθ s hs0 hs2 hsκ x y
      have hζ' := hζ s hs0 hs2
      have hsmall : |s / (1 - s) * Z.toFun x y| ≤ κ / 2 := by
        rw [abs_mul, abs_of_nonneg hζ'.1]
        calc s / (1 - s) * |Z.toFun x y| ≤ (2 * s) * cz :=
              mul_le_mul hζ'.2 (hcz x y) (abs_nonneg _) (by linarith)
          _ ≤ κ / 2 := hsκ
      rw [abs_le] at hsmall
      by_cases hxy : Z.toFun x y = 0
      · rw [hxy, mul_zero, add_zero]; exact (M θ).mem_Icc x y
      · have hwin := hMwin θ hθ x y (hZsupp x y hxy)
        exact ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
    -- the uniform expansion of the insertion polynomial
    obtain ⟨Ctay, hCtay0, hCtay⟩ := insertionPoly_taylor H hqε hu Z hcz0 hcz
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ → ℝ → ℝ,
        P = fun θ s => insertionPoly H ε u (M θ) Z (fun t => t / (1 - t)) s := ⟨_, rfl⟩
    have hPval : ∀ θ s : ℝ, P θ s = insertionPoly H ε u (M θ) Z (fun t => t / (1 - t)) s := by
      intro θ s; rw [hPdef]
    have hP0 : ∀ θ : ℝ, P θ 0 = (M θ).tDensity H := by
      intro θ
      rw [hPval]
      exact insertionPoly_zero H ε u (M θ) Z (by norm_num)
    obtain ⟨Bf, hBfdef⟩ : ∃ Bf : ℝ → ℝ, Bf = fun θ =>
        (∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
          + totalRootedDensity H (M θ) u - (Fintype.card V : ℝ) * (M θ).tDensity H := ⟨_, rfl⟩
    have hBfval : ∀ θ : ℝ, Bf θ = (∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        + totalRootedDensity H (M θ) u - (Fintype.card V : ℝ) * (M θ).tDensity H := by
      intro θ; rw [hBfdef]
    have hCtay' : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s * cz ≤ κ / 2 →
        |P θ s - P θ 0 - s * Bf θ| ≤ Ctay * s ^ 2 := by
      intro θ hθ s hs0 hs2 hsκ
      have h := hCtay (M θ) s hs0 hs2 (hadm θ hθ s hs0 hs2 hsκ)
      rw [← hBfval θ, ← hP0 θ, ← hPval] at h
      exact h
    obtain ⟨CB, hCBdef⟩ : ∃ c : ℝ, c = (H.edgeFinset.card : ℝ) ^ 2 * cz
      + 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ) := ⟨_, rfl⟩
    have hCB0 : 0 ≤ CB := by
      have h1 : (0:ℝ) ≤ (H.edgeFinset.card : ℝ) ^ 2 * cz := mul_nonneg (sq_nonneg _) hcz0
      have h2 : (0:ℝ) ≤ 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) hN0) hm0
      rw [hCBdef]; linarith
    have hBθ : ∀ θ ∈ Set.Icc (0:ℝ) 1, |Bf θ - Bq| ≤ CB * θ := by
      intro θ hθ
      have h1 : |(∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
          - ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ|
          ≤ (H.edgeFinset.card : ℝ) ^ 2 * θ * cz := by
        have hL1 : (∫ z, |(M θ).toFun z.1 z.2 - W.toFun z.1 z.2| ∂gμ) ≤ θ := by
          have h := integral_mono (((M θ).integrable_self.sub W.integrable_self).abs)
            (integrable_const (μ := gμ) θ) fun z => hMLip θ hθ z.1 z.2
          simpa using h
        have hgen := abs_integral_derivKernel_mul_sub_le H (M θ) W Z hcz
        have hmm : (0:ℝ) ≤ (H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * cz :=
          mul_nonneg (mul_nonneg hm0 hm0) hcz0
        nlinarith [hgen, mul_le_mul_of_nonneg_left hL1 hmm]
      have h2 : |totalRootedDensity H (M θ) u - totalRootedDensity H W u|
          ≤ (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * θ) :=
        abs_totalRootedDensity_sub_le_graphon H hu (hMLip θ hθ)
      have h3 : |(M θ).tDensity H - τ| ≤ (H.edgeFinset.card : ℝ) * θ := by
        have h := abs_kernel_tDensity_sub_le H (K := Kernel.ofGraphon (M θ))
          (L := Kernel.ofGraphon W) (fun x y => (M θ).mem_Icc x y)
          (fun x y => W.mem_Icc x y) (hMLip θ hθ)
        rwa [Kernel.tDensity_ofGraphon, Kernel.tDensity_ofGraphon, ht] at h
      have h4 : |(Fintype.card V : ℝ) * ((M θ).tDensity H - τ)|
          ≤ (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * θ) := by
        rw [abs_mul, abs_of_nonneg hN0]
        exact mul_le_mul_of_nonneg_left h3 hN0
      have hid : Bf θ - Bq
          = ((∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
              - ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
            + (totalRootedDensity H (M θ) u - totalRootedDensity H W u)
            - (Fintype.card V : ℝ) * ((M θ).tDensity H - τ) := by
        rw [hBfval θ, hBeq]; ring
      rw [hid, hCBdef]
      calc |((∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
                - ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
              + (totalRootedDensity H (M θ) u - totalRootedDensity H W u)
              - (Fintype.card V : ℝ) * ((M θ).tDensity H - τ)|
          ≤ |(∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
                - ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ|
              + |totalRootedDensity H (M θ) u - totalRootedDensity H W u|
              + |(Fintype.card V : ℝ) * ((M θ).tDensity H - τ)| := by
            refine (abs_sub _ _).trans ?_
            linarith [abs_add_le ((∫ z, derivKernel H (M θ) z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
                - ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
              (totalRootedDensity H (M θ) u - totalRootedDensity H W u)]
        _ ≤ (H.edgeFinset.card : ℝ) ^ 2 * θ * cz
              + (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * θ)
              + (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * θ) :=
            add_le_add (add_le_add h1 h2) h4
        _ = ((H.edgeFinset.card : ℝ) ^ 2 * cz
              + 2 * (Fintype.card V : ℝ) * (H.edgeFinset.card : ℝ)) * θ := by ring
    -- the lower and upper bounds for the increment of the `H`-density
    have hN1 : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s * cz ≤ κ / 2 →
        Ctay * s + CB * θ ≤ b → b * s ≤ P θ s - P θ 0 := fun θ hθ s hs0 hs2 hsκ hsmall =>
      taylor_lower_bound (hCtay' θ hθ s hs0 hs2 hsκ) (hBθ θ hθ) hs0 hBb hsmall
    obtain ⟨C₂, hC₂def⟩ : ∃ c : ℝ, c = Ctay + (|Bq| + CB) := ⟨_, rfl⟩
    have hC₂0 : 0 ≤ C₂ := by
      rw [hC₂def]; linarith [hCtay0, abs_nonneg Bq, hCB0]
    have hN2 : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s * cz ≤ κ / 2 →
        |P θ s - P θ 0| ≤ C₂ * s := by
      intro θ hθ s hs0 hs2 hsκ
      have hBabs : |Bf θ| ≤ |Bq| + CB := by
        have h5 := abs_sub_abs_le_abs_sub (Bf θ) Bq
        have h6 : CB * θ ≤ CB := by
          have h7 := mul_le_mul_of_nonneg_left hθ.2 hCB0
          rw [mul_one] at h7
          exact h7
        linarith [hBθ θ hθ]
      rw [hC₂def]
      exact taylor_upper_bound (hCtay' θ hθ s hs0 hs2 hsκ) hBabs hs0
        (le_trans hs2 (by norm_num)) hCtay0
    -- continuity in the smoothing parameter
    have hPcont : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s * cz ≤ κ / 2 →
        ContinuousOn (fun θ => P θ s) (Set.Icc (0:ℝ) 1) := by
      intro s hs0 hs2 hsκ
      have hlip : ∀ θ ∈ Set.Icc (0:ℝ) 1, ∀ θ' ∈ Set.Icc (0:ℝ) 1,
          |P θ s - P θ' s| ≤ (H.edgeFinset.card : ℝ) * |θ - θ'| := by
        intro θ hθ θ' hθ'
        rw [hPval, hPval]
        exact abs_insertionPoly_sub_le H hqε hu Z (fun t => t / (1 - t)) hs0
          (le_trans hs2 (by norm_num)) (hadm θ hθ s hs0 hs2 hsκ) (hadm θ' hθ' s hs0 hs2 hsκ)
          (hMLip2 θ hθ θ' hθ')
      rw [Metric.continuousOn_iff]
      intro θ₀ hθ₀ δ hδ
      refine ⟨δ / ((H.edgeFinset.card : ℝ) + 1),
        div_pos hδ hmpos, fun θ hθ hd => ?_⟩
      rw [Real.dist_eq] at hd ⊢
      have h := hlip θ hθ θ₀ hθ₀
      have hdd : |θ - θ₀| * ((H.edgeFinset.card : ℝ) + 1) < δ := by
        rw [← lt_div_iff₀ hmpos]
        exact hd
      have hd2 : (H.edgeFinset.card : ℝ) * |θ - θ₀|
          ≤ |θ - θ₀| * ((H.edgeFinset.card : ℝ) + 1) := by
        have h0 := abs_nonneg (θ - θ₀)
        nlinarith
      exact lt_of_le_of_lt (h.trans hd2) hdd
    -- the smoothing gain
    obtain ⟨CI, hCIdef⟩ : ∃ c : ℝ, c = 2 * MJ + 2 * L * cz := ⟨_, rfl⟩
    have hCI0 : 0 ≤ CI := by
      have h1 : (0:ℝ) ≤ 2 * L * cz := mul_nonneg (mul_nonneg (by norm_num) hL0) hcz0
      rw [hCIdef]; linarith
    have hgain := degenerate_gain H hΔ hε0 hε1 hτ0 hτ1 hW hdeg (CI / b)
    obtain ⟨θg, hθgmem, hgsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgain
    have hθg0 : (0:ℝ) < θg := hθgmem
    -- the choice of parameters
    obtain ⟨θ₂, hθ₂def⟩ : ∃ t : ℝ, t = min (1 / 2) (b / (2 * (CB + 1))) := ⟨_, rfl⟩
    have hθ₂0 : 0 < θ₂ := by
      rw [hθ₂def]; exact lt_min (by norm_num) (div_pos hb0 (by linarith))
    obtain ⟨θ₁, hθ₁def⟩ : ∃ t : ℝ, t = min θ₂ (θg / 2) := ⟨_, rfl⟩
    have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; exact lt_min hθ₂0 (half_pos hθg0)
    have hθ₁2 : θ₁ ≤ θ₂ := hθ₁def ▸ min_le_left _ _
    have hθ₁g : θ₁ < θg := lt_of_le_of_lt (hθ₁def ▸ min_le_right _ _) (by linarith)
    have hθ₁half : θ₁ ≤ 1 / 2 := le_trans hθ₁2 (hθ₂def ▸ min_le_left _ _)
    have hθ₁mem : θ₁ ∈ Set.Icc (0:ℝ) 1 := ⟨hθ₁0.le, by linarith⟩
    have hCBθ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₁ → CB * θ ≤ b / 2 := by
      intro θ hθ0 hθ1
      have h1 : θ ≤ b / (2 * (CB + 1)) := le_trans hθ1 (le_trans hθ₁2
        (hθ₂def ▸ min_le_right _ _))
      have h2 : (0:ℝ) < 2 * (CB + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      linarith
    obtain ⟨hd₁0, -⟩ := hgsub ⟨hθ₁0, hθ₁g⟩ (M θ₁) (hMval θ₁ hθ₁mem)
    obtain ⟨d₁, hd₁def⟩ : ∃ d : ℝ, d = τ - (M θ₁).tDensity H := ⟨_, rfl⟩
    have hd₁pos : 0 < d₁ := hd₁def ▸ hd₁0
    obtain ⟨s₀, hs₀def⟩ : ∃ s : ℝ, s = min (min (1 / 2) (b / (2 * (Ctay + 1))))
      (min (κ / (8 * (cz + 1))) (d₁ / (2 * (C₂ + 1)))) := ⟨_, rfl⟩
    have hs₀0 : 0 < s₀ := by
      rw [hs₀def]
      exact lt_min (lt_min (by norm_num) (div_pos hb0 (by linarith)))
        (lt_min (div_pos hκ0 (by linarith)) (div_pos hd₁pos (by linarith)))
    have hs₀half : s₀ ≤ 1 / 2 :=
      le_trans (hs₀def ▸ min_le_left _ _) (min_le_left _ _)
    have hs₀Ctay : Ctay * s₀ ≤ b / 2 := by
      have h1 : s₀ ≤ b / (2 * (Ctay + 1)) :=
        le_trans (hs₀def ▸ min_le_left _ _) (min_le_right _ _)
      have h2 : (0:ℝ) < 2 * (Ctay + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      linarith
    have hs₀κ : 2 * s₀ * cz ≤ κ / 2 := by
      have h1 : s₀ ≤ κ / (8 * (cz + 1)) :=
        le_trans (hs₀def ▸ min_le_right _ _) (min_le_left _ _)
      have h2 : (0:ℝ) < 8 * (cz + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      linarith [hs₀0.le]
    have hs₀C₂ : C₂ * s₀ < d₁ := by
      have h1 : s₀ ≤ d₁ / (2 * (C₂ + 1)) :=
        le_trans (hs₀def ▸ min_le_right _ _) (min_le_right _ _)
      have h2 : (0:ℝ) < 2 * (C₂ + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      linarith
    -- the intermediate value theorem in the smoothing parameter
    have hF0 : τ < P 0 s₀ := by
      have h := hN1 0 ⟨le_rfl, zero_le_one⟩ s₀ hs₀0.le hs₀half hs₀κ (by
        rw [mul_zero, add_zero]; linarith)
      rw [hP0 0, hM0] at h
      linarith [mul_pos hb0 hs₀0]
    have hF1 : P θ₁ s₀ < τ := by
      have h := hN2 θ₁ hθ₁mem s₀ hs₀0.le hs₀half hs₀κ
      rw [abs_le, hP0 θ₁] at h
      linarith [h.2]
    obtain ⟨θs, hθsmem, hθseq0⟩ := intermediate_value_Icc' hθ₁0.le
      ((hPcont s₀ hs₀0.le hs₀half hs₀κ).mono (Set.Icc_subset_Icc le_rfl (by linarith)))
      (show τ ∈ Set.Icc ((fun θ => P θ s₀) θ₁) ((fun θ => P θ s₀) 0) from ⟨hF1.le, hF0.le⟩)
    have hθseq : P θs s₀ = τ := hθseq0
    have hθs0 : 0 < θs := by
      rcases lt_or_eq_of_le hθsmem.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hθseq
        linarith
    have hθsmem' : θs ∈ Set.Icc (0:ℝ) 1 := ⟨hθsmem.1, by linarith [hθsmem.2, hθ₁half]⟩
    -- the deficit of the smoothing at `θs` is at least `b s₀`
    have hdefs : b * s₀ ≤ τ - (M θs).tDensity H := by
      have h := hN1 θs hθsmem' s₀ hs₀0.le hs₀half hs₀κ (by
        have h6 := hCBθ θs hθsmem.1 hθsmem.2
        linarith)
      rw [hP0 θs, hθseq] at h
      linarith
    obtain ⟨-, hgainθs⟩ := hgsub ⟨hθs0, lt_of_le_of_lt hθsmem.2 hθ₁g⟩ (M θs) (hMval θs hθsmem')
    have hgainval : CI * s₀ < W.Ip ε - (M θs).Ip ε := by
      have h1 : CI * s₀ ≤ CI / b * (τ - (M θs).tDensity H) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
        calc CI * s₀ * b = CI * (b * s₀) := by ring
          _ ≤ CI * (τ - (M θs).tDensity H) := mul_le_mul_of_nonneg_left hdefs hCI0
      linarith
    -- the competitor: feasible, with strictly smaller cost
    have hs₀1 : s₀ < 1 := by linarith
    obtain ⟨W', hW't, hW'e, hW'I⟩ := exists_insertGraphon H (M θs) Z
      (ζ := s₀ / (1 - s₀)) (hadm θs hθsmem' s₀ hs₀0.le hs₀half hs₀κ) hqε hu hs₀0 hs₀1
    have hW'tτ : W'.tDensity H = τ := by
      rw [hW't, ← hθseq, hPval]
      rfl
    have hW'eε : W'.edgeDensity = ε := by
      have h1 : (1:ℝ) - s₀ ≠ 0 := by linarith
      have hu' : ∫ y, u y ∂unitμ = E + ε := by rw [hEdef]; ring
      rw [hW'e, hMe θs hθsmem', hZint, hu']
      field_simp
      ring
    have hW'Ile : W'.Ip ε ≤ (M θs).Ip ε + CI * s₀ := by
      have hline : (Kernel.ofGraphon (M θs) + (s₀ / (1 - s₀)) • Z).Ip ε
          ≤ (M θs).Ip ε + L * (2 * s₀ * cz) := by
        refine Ip_line_le (M θs) Z hε0 hε1 hκ0 hL0
          (mul_nonneg (mul_nonneg (by norm_num) hs₀0.le) hcz0) hL ?_ ?_ hs₀κ
          (hadm θs hθsmem' s₀ hs₀0.le hs₀half hs₀κ)
        · exact fun x y hne => hMwin θs hθsmem' x y (hZsupp x y hne)
        · intro x y
          have hζ' := hζ s₀ hs₀0.le hs₀half
          rw [abs_mul, abs_of_nonneg hζ'.1]
          exact mul_le_mul hζ'.2 (hcz x y) (abs_nonneg _) (by linarith)
      have hlinenn : 0 ≤ (Kernel.ofGraphon (M θs) + (s₀ / (1 - s₀)) • Z).Ip ε := by
        refine integral_nonneg fun z => ?_
        have hz := hadm θs hθsmem' s₀ hs₀0.le hs₀half hs₀κ z.1 z.2
        exact Jp_nonneg_of_mem hε0 hε1 hz.1 hz.2
      obtain ⟨hJu0, hJuM⟩ := hMJ u hu
      rw [hW'I ε hε0 hε1, Jp_self hε0 hε1, hCIdef]
      exact insertion_cost_le hs₀0.le (le_trans hs₀half (by norm_num)) hJu0 hJuM hlinenn hline
    have hfv : fixedValue H ε τ ≤ W'.Ip ε := fixedValue_le H hε0 hε1 hW'eε hW'tτ
    rw [← hI] at hfv
    linarith
  refine ⟨hrow, ?_⟩
  /- Integrating the insertion inequality over the rows: the average vanishes by
  `eq:rooted-average` and `∫∫ W = ε`, so the nonpositive integrand vanishes almost
  everywhere. -/
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun x => totalRootedDensity H W (W.row x)
    - (Fintype.card V : ℝ) * τ - 2 * a * ((∫ y, W.row x y ∂unitμ) - ε) := ⟨_, rfl⟩
  have hi1 : Integrable (fun x => totalRootedDensity H W (W.row x)) unitμ :=
    integrable_totalRootedDensity_row H W
  have hi2 : Integrable (fun x => ∫ y, W.row x y ∂unitμ) unitμ :=
    W.integrable_self.integral_prod_left
  have hi3 : Integrable (fun x => totalRootedDensity H W (W.row x)
      - (Fintype.card V : ℝ) * τ) unitμ := hi1.sub (integrable_const _)
  have hi4 : Integrable (fun x => (∫ y, W.row x y ∂unitμ) - ε) unitμ :=
    hi2.sub (integrable_const _)
  have hi5 : Integrable (fun x => 2 * a * ((∫ y, W.row x y ∂unitμ) - ε)) unitμ :=
    hi4.const_mul _
  have hiG : Integrable G unitμ := by rw [hGdef]; exact hi3.sub hi5
  have hR : ∫ x, totalRootedDensity H W (W.row x) ∂unitμ = (Fintype.card V : ℝ) * τ := by
    rw [rooted_average, ht]
  have he2 : ∫ x, (∫ y, W.row x y ∂unitμ) ∂unitμ = ε := by
    rw [← he]
    exact (integral_prod _ W.integrable_self).symm
  have hGx : ∀ x : ℝ, G x = totalRootedDensity H W (W.row x) - (Fintype.card V : ℝ) * τ
      - 2 * a * ((∫ y, W.row x y ∂unitμ) - ε) := by
    intro x; rw [hGdef]
  have hGval : ∫ x, G x ∂unitμ = 0 := by
    have h1 : ∫ x, G x ∂unitμ
        = (∫ x, (totalRootedDensity H W (W.row x) - (Fintype.card V : ℝ) * τ) ∂unitμ)
          - ∫ x, 2 * a * ((∫ y, W.row x y ∂unitμ) - ε) ∂unitμ := by
      rw [hGdef]; exact integral_sub hi3 hi5
    have h2 : ∫ x, (totalRootedDensity H W (W.row x) - (Fintype.card V : ℝ) * τ) ∂unitμ
        = (∫ x, totalRootedDensity H W (W.row x) ∂unitμ) - (Fintype.card V : ℝ) * τ := by
      rw [integral_sub hi1 (integrable_const _), integral_const]
      simp only [smul_eq_mul, probReal_univ, one_mul]
    have h3 : ∫ x, 2 * a * ((∫ y, W.row x y ∂unitμ) - ε) ∂unitμ
        = 2 * a * ((∫ x, (∫ y, W.row x y ∂unitμ) ∂unitμ) - ε) := by
      rw [integral_const_mul, integral_sub hi2 (integrable_const _), integral_const]
      simp only [smul_eq_mul, probReal_univ, one_mul]
    rw [h1, h2, h3, hR, he2]
    ring
  have hnn : 0 ≤ᵐ[unitμ] fun x => -G x :=
    ae_of_all _ fun x => by
      have h := hrow (W.row x) (isRow_row W x)
      show (0:ℝ) ≤ -G x
      rw [hGx x]
      linarith
  have hzero : ∫ x, (-G x) ∂unitμ = 0 := by rw [integral_neg, hGval, neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hiG.neg).1 hzero
  filter_upwards [hae] with x hx
  have hx' : -G x = 0 := hx
  rw [hGx x] at hx'
  linarith

end UpperTailMultipodality
