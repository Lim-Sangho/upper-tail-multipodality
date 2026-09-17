import UpperTailMultipodality.UpperTail.Support.Basic

/-!
# The upper bound of `lem:upper-tail-basic`

A minimizer `W` with `W ≥ p` almost everywhere and `t(H,W) = r^m` is essentially bounded away
from `1` (`exists_ae_le_one_sub_of_minimizer`).

If not, let `E = {W > 1 - δ}` (positive measure for every `δ > 0`) and `A = {W ≤ 1 - γ₀}` (positive
measure for some `γ₀`, since `t(H,W) < 1`).  Along `U = -1_E + κ1_A` with
`κ = 2∫_E 𝒟_W / ∫_A 𝒟_W` the first variation of `t(H,·)` is `∫_E 𝒟_W > 0`, so `W + θU` is
feasible for small `θ > 0`.  The tangent lines of `J_p` give
`I_p(W + θU) ≤ I_p(W) + θκC|A| - θJ_p'(1 - 2δ)|E|`, and `κ|A| ≤ 2p^{1-m}|E|`, so the right side
is `< I_p(W)` once `J_p'(1 - 2δ)` is large.
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory Filter Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If `t(H,W) < 1`, then `W ≤ 1 - γ₀` on a set of positive measure, for some `γ₀ ∈ (0,1]`. -/
theorem exists_measure_le_one_sub_ne_zero (H : SimpleGraph V) [DecidableRel H.Adj] {W : Graphon}
    (ht : W.tDensity H < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ gμ {z : ℝ × ℝ | W.toFun z.1 z.2 ≤ 1 - γ} ≠ 0 := by
  by_contra hcon
  have hnull : ∀ n : ℕ, gμ {z : ℝ × ℝ | W.toFun z.1 z.2 ≤ 1 - 1 / ((n:ℝ) + 1)} = 0 := by
    intro n
    by_contra hne
    refine hcon ⟨1 / ((n:ℝ) + 1), by positivity, ?_, hne⟩
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hU := measure_iUnion_null hnull
  have hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hU
    simp only [mem_ofPred_eq] at hz
    have hlt : W.toFun z.1 z.2 < 1 := lt_of_le_of_ne (W.le_one' _ _) hz
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    exact mem_iUnion.mpr ⟨n, by simp only [mem_ofPred_eq]; linarith⟩
  rw [tDensity_ae_const W H hae, one_pow] at ht
  exact lt_irrefl _ ht

/-- The set `{W > 1 - δ}`. -/
def nearOneSet (W : Graphon) (δ : ℝ) : Set (ℝ × ℝ) := {z | 1 - δ < W.toFun z.1 z.2}

/-- The set `{W ≤ 1 - γ}`. -/
def belowSet (W : Graphon) (γ : ℝ) : Set (ℝ × ℝ) := {z | W.toFun z.1 z.2 ≤ 1 - γ}

/-- `{W > 1 - δ}` is measurable. -/
theorem measurableSet_nearOneSet (W : Graphon) (δ : ℝ) : MeasurableSet (nearOneSet W δ) :=
  measurableSet_lt measurable_const W.measurable_uncurry

/-- `{W ≤ 1 - γ}` is measurable. -/
theorem measurableSet_belowSet (W : Graphon) (γ : ℝ) : MeasurableSet (belowSet W γ) :=
  measurableSet_le W.measurable_uncurry measurable_const

/-- The two sets are disjoint when `δ < γ`. -/
theorem not_mem_belowSet_of_mem_nearOneSet {W : Graphon} {δ γ : ℝ} (hδγ : δ < γ) {z : ℝ × ℝ}
    (hz : z ∈ nearOneSet W δ) : z ∉ belowSet W γ := fun hz' => by
  have h1 : 1 - δ < W.toFun z.1 z.2 := hz
  have h2 : W.toFun z.1 z.2 ≤ 1 - γ := hz'
  linarith

/-- An indicator with value `1` takes values in `[0,1]`. -/
theorem indicator_one_mem_Icc (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) :
    S.indicator (1 : ℝ × ℝ → ℝ) z ∈ Icc (0:ℝ) 1 := by
  by_cases hz : z ∈ S
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- The bounded symmetric direction `-1_{W > 1 - δ} + κ 1_{W ≤ 1 - γ}`. -/
noncomputable def shiftKernel (W : Graphon) (δ γ κ : ℝ) : Kernel where
  toFun x y := -((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
    + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)
  symm' x y := by
    classical
    have hE : (x, y) ∈ nearOneSet W δ ↔ (y, x) ∈ nearOneSet W δ := by
      simp only [nearOneSet, mem_ofPred_eq, W.symm' x y]
    have hA : (x, y) ∈ belowSet W γ ↔ (y, x) ∈ belowSet W γ := by
      simp only [belowSet, mem_ofPred_eq, W.symm' x y]
    show -((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
        + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)
      = -((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (y, x))
        + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (y, x)
    simp only [Set.indicator_apply, hE, hA, Pi.one_apply]
  meas' := by
    show Measurable fun z : ℝ × ℝ => -((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (z.1, z.2))
      + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (z.1, z.2)
    exact (measurable_one.indicator (measurableSet_nearOneSet W δ)).neg.add
      ((measurable_one.indicator (measurableSet_belowSet W γ)).const_mul κ)
  bdd' := ⟨1 + |κ|, fun x y => by
    have h1 := indicator_one_mem_Icc (nearOneSet W δ) (x, y)
    have h2 := indicator_one_mem_Icc (belowSet W γ) (x, y)
    have h3 : |κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)| ≤ |κ| := by
      rw [abs_mul, abs_of_nonneg h2.1]
      exact mul_le_of_le_one_right (abs_nonneg κ) h2.2
    calc |-((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
          + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)|
        ≤ |-((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))|
          + |κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)| := abs_add_le _ _
      _ ≤ 1 + |κ| := by
          rw [abs_neg, abs_of_nonneg h1.1]
          exact add_le_add h1.2 h3⟩

/-- The values of `shiftKernel`. -/
theorem shiftKernel_apply (W : Graphon) (δ γ κ : ℝ) (z : ℝ × ℝ) :
    (shiftKernel W δ γ κ).toFun z.1 z.2 = -((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z)
      + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) z := rfl

/-- `W + θU = W - θ` on `{W > 1 - δ}`. -/
theorem shift_apply_of_mem_nearOneSet {W : Graphon} {δ γ κ θ : ℝ} (hδγ : δ < γ) {x y : ℝ}
    (hz : (x, y) ∈ nearOneSet W δ) :
    (Kernel.ofGraphon W + θ • shiftKernel W δ γ κ).toFun x y = W.toFun x y - θ := by
  show W.toFun x y + θ * (-((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
    + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)) = _
  rw [Set.indicator_of_mem hz, Set.indicator_of_notMem (not_mem_belowSet_of_mem_nearOneSet hδγ hz)]
  simp only [Pi.one_apply]; ring

/-- `W + θU = W + κθ` on `{W ≤ 1 - γ}`. -/
theorem shift_apply_of_mem_belowSet {W : Graphon} {δ γ κ θ : ℝ} (hδγ : δ < γ) {x y : ℝ}
    (hz : (x, y) ∈ belowSet W γ) :
    (Kernel.ofGraphon W + θ • shiftKernel W δ γ κ).toFun x y = W.toFun x y + κ * θ := by
  show W.toFun x y + θ * (-((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
    + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)) = _
  rw [Set.indicator_of_mem hz,
    Set.indicator_of_notMem fun h => not_mem_belowSet_of_mem_nearOneSet hδγ h hz]
  simp only [Pi.one_apply]; ring

/-- `W + θU = W` off both sets. -/
theorem shift_apply_of_not_mem {W : Graphon} {δ γ κ θ : ℝ} {x y : ℝ}
    (hE : (x, y) ∉ nearOneSet W δ) (hA : (x, y) ∉ belowSet W γ) :
    (Kernel.ofGraphon W + θ • shiftKernel W δ γ κ).toFun x y = W.toFun x y := by
  show W.toFun x y + θ * (-((nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) (x, y))
    + κ * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) (x, y)) = _
  rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hA]
  ring

/-- For admissible step sizes, `W + θU` takes values in `[0,1]`. -/
theorem shift_mem_Icc {W : Graphon} {δ γ κ θ : ℝ} (hδγ : δ < γ) (hθ0 : 0 ≤ θ) (hθδ : θ ≤ δ)
    (hδ : 2 * δ ≤ 1) (hκθ0 : 0 ≤ κ * θ) (hκθ : κ * θ ≤ γ) (x y : ℝ) :
    (Kernel.ofGraphon W + θ • shiftKernel W δ γ κ).toFun x y ∈ Icc (0:ℝ) 1 := by
  by_cases hzE : (x, y) ∈ nearOneSet W δ
  · have hw : 1 - δ < W.toFun x y := hzE
    rw [shift_apply_of_mem_nearOneSet hδγ hzE]
    exact ⟨by linarith, by linarith [W.le_one' x y]⟩
  · by_cases hzA : (x, y) ∈ belowSet W γ
    · have hw : W.toFun x y ≤ 1 - γ := hzA
      rw [shift_apply_of_mem_belowSet hδγ hzA]
      exact ⟨by linarith [W.nonneg' x y], by linarith⟩
    · rw [shift_apply_of_not_mem hzE hzA]
      exact W.mem_Icc x y

/-- **The pointwise cost of the shift.** -/
theorem Jp_shift_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {W : Graphon} {δ γ κ θ C : ℝ}
    (hδγ : δ < γ) (hγ1 : γ ≤ 1) (hθ0 : 0 < θ) (hθδ : θ ≤ δ) (hδ : 2 * δ < 1)
    (hκθ0 : 0 < κ * θ) (hκθ : κ * θ ≤ γ / 2) (hC : Jp' p (1 - γ / 2) ≤ C) (z : ℝ × ℝ) :
    Jp p ((Kernel.ofGraphon W + θ • shiftKernel W δ γ κ).toFun z.1 z.2)
      ≤ Jp p (W.toFun z.1 z.2) + θ * κ * C * (belowSet W γ).indicator (1 : ℝ × ℝ → ℝ) z
        - θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z := by
  have hmono := (Jp'_strictMonoOn hp0 hp1).monotoneOn
  have hγ0 : 0 < γ := lt_of_le_of_lt (by nlinarith) hδγ
  by_cases hzE : z ∈ nearOneSet W δ
  · have hw : 1 - δ < W.toFun z.1 z.2 := hzE
    rw [shift_apply_of_mem_nearOneSet hδγ hzE, Set.indicator_of_mem hzE,
      Set.indicator_of_notMem (not_mem_belowSet_of_mem_nearOneSet hδγ hzE)]
    simp only [Pi.one_apply, mul_zero, add_zero, mul_one]
    refine Jp_sub_le hp0 hp1 (W.le_one' _ _) hθ0 (by linarith) ?_
    exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [W.le_one' z.1 z.2]⟩
      (by linarith)
  · by_cases hzA : z ∈ belowSet W γ
    · have hw : W.toFun z.1 z.2 ≤ 1 - γ := hzA
      rw [shift_apply_of_mem_belowSet hδγ hzA, Set.indicator_of_mem hzA,
        Set.indicator_of_notMem hzE]
      simp only [Pi.one_apply, mul_zero, sub_zero, mul_one]
      have hw0 := W.nonneg' z.1 z.2
      have hle := Jp_add_le hp0 hp1 hw0 hκθ0 (by linarith)
        (le_trans (hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)) hC)
      calc Jp p (W.toFun z.1 z.2 + κ * θ) ≤ Jp p (W.toFun z.1 z.2) + κ * θ * C := hle
        _ = _ := by ring
    · rw [shift_apply_of_not_mem hzE hzA, Set.indicator_of_notMem hzA,
        Set.indicator_of_notMem hzE]
      simp

/-- The final inequality of the upper-bound argument, as plain real arithmetic. -/
theorem upper_bound_arith {θ κ C mA mE DE DA c₀ m K cδ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hmE : 0 < mE) (hc₀ : 0 < c₀) (hDA : 0 < DA) (hκ : κ = 2 * DE / DA)
    (hDE : DE ≤ m * mE) (hDA_ge : c₀ * mA ≤ DA) (hDE0 : 0 ≤ DE)
    (hK : K = 2 * m * C / c₀) (hcδ : K + 1 ≤ cδ) :
    θ * κ * C * mA - θ * cδ * mE < 0 := by
  have hκmA : κ * mA ≤ 2 * m * mE / c₀ := by
    rw [hκ, div_mul_eq_mul_div, div_le_div_iff₀ hDA hc₀]
    calc 2 * DE * mA * c₀ = 2 * DE * (c₀ * mA) := by ring
      _ ≤ 2 * DE * DA := by gcongr
      _ ≤ 2 * (m * mE) * DA := by gcongr
      _ = _ := by ring
  have hkey : θ * κ * C * mA ≤ θ * K * mE := by
    calc θ * κ * C * mA = θ * C * (κ * mA) := by ring
      _ ≤ θ * C * (2 * m * mE / c₀) := by gcongr
      _ = θ * K * mE := by rw [hK]; ring
  have hkey2 : θ * (K + 1) * mE ≤ θ * cδ * mE := by gcongr
  nlinarith [mul_pos hθ hmE]

/-- **Upper bound of `lem:upper-tail-basic`.**  A minimizer with `W ≥ p` almost everywhere and
an active constraint satisfies `W ≤ 1 - γ` almost everywhere for some `γ > 0`. -/
theorem exists_ae_le_one_sub_of_minimizer (H : SimpleGraph V) [DecidableRel H.Adj]
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    {W : Graphon} (hmin : W.Ip p = phiVar H p r)
    (hlow : ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2) (hact : W.tDensity H = r ^ H.edgeFinset.card) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - γ := by
  have hp1 : p < 1 := lt_trans hpr hr1
  have hr0 : 0 < r := lt_trans hp0 hpr
  have hmne : H.edgeFinset.card ≠ 0 := by omega
  have ht1 : W.tDensity H < 1 := by rw [hact]; exact pow_lt_one₀ hr0.le hr1 hmne
  obtain ⟨γ₀, hγ₀, hγ₀1, hA0⟩ := exists_measure_le_one_sub_ne_zero H ht1
  by_contra hcon
  have hEpos : ∀ δ : ℝ, 0 < δ → gμ (nearOneSet W δ) ≠ 0 := by
    intro δ hδ hzero
    refine hcon ⟨δ, hδ, ae_iff.mpr ?_⟩
    have hset : {a : ℝ × ℝ | ¬W.toFun a.1 a.2 ≤ 1 - δ} = nearOneSet W δ := by
      ext z; simp only [nearOneSet, mem_ofPred_eq, not_le]
    rw [hset]; exact hzero
  -- constants
  have hmR : (0:ℝ) < H.edgeFinset.card := by exact_mod_cast (by omega : 0 < H.edgeFinset.card)
  obtain ⟨c₀, hc₀_def⟩ : ∃ c₀ : ℝ, c₀ = (H.edgeFinset.card : ℝ) * p ^ (H.edgeFinset.card - 1) :=
    ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by rw [hc₀_def]; positivity
  have hD_ge : ∀ᵐ z ∂gμ, c₀ ≤ derivKernel H W z.1 z.2 := by
    rw [hc₀_def]; exact derivKernel_ge H W hp0.le hlow
  have hD_mem := derivKernel_mem_Icc H W
  obtain ⟨C₁, hC₁_def⟩ : ∃ C₁ : ℝ, C₁ = max (Jp' p (1 - γ₀ / 2)) 0 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := hC₁_def ▸ le_max_right _ _
  have hC₁ : Jp' p (1 - γ₀ / 2) ≤ C₁ := hC₁_def ▸ le_max_left _ _
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = 2 * H.edgeFinset.card * C₁ / c₀ := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀0, ht₀1, ht₀eq, -⟩ := exists_Jp'_eq hp0 hp1 (K + 1)
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = min (γ₀ / 2) ((1 - t₀) / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ_def ▸ lt_min (by linarith) (by linarith)
  have hδγ : δ ≤ γ₀ / 2 := hδ_def ▸ min_le_left _ _
  have hδt : δ ≤ (1 - t₀) / 2 := hδ_def ▸ min_le_right _ _
  have hδγ' : δ < γ₀ := by linarith
  have hδ1 : 2 * δ < 1 := by linarith
  have hcδ : K + 1 ≤ Jp' p (1 - 2 * δ) := by
    rw [← ht₀eq]
    exact (Jp'_strictMonoOn hp0 hp1).monotoneOn ⟨ht₀0, ht₀1⟩ ⟨by linarith, by linarith⟩
      (by linarith)
  -- integrals over `E = {W > 1 - δ}` and `A = {W ≤ 1 - γ₀}`
  have hEm := measurableSet_nearOneSet W δ
  have hAm := measurableSet_belowSet W γ₀
  have hDm := measurable_derivKernel H W
  have hind_int : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      Integrable (S.indicator (1 : ℝ × ℝ → ℝ)) gμ := fun S hS =>
    integrable_of_abs_le (measurable_one.indicator hS) 1 fun z => by
      rw [abs_of_nonneg (indicator_one_mem_Icc S z).1]; exact (indicator_one_mem_Icc S z).2
  have hDind_int : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2 * S.indicator 1 z) gμ :=
    fun S hS => integrable_of_abs_le (hDm.mul (measurable_one.indicator hS))
      H.edgeFinset.card fun z => by
        rw [abs_mul, abs_of_nonneg (hD_mem z.1 z.2).1, abs_of_nonneg (indicator_one_mem_Icc S z).1]
        calc derivKernel H W z.1 z.2 * S.indicator 1 z ≤ H.edgeFinset.card * 1 :=
              mul_le_mul (hD_mem z.1 z.2).2 (indicator_one_mem_Icc S z).2
                (indicator_one_mem_Icc S z).1 hmR.le
          _ = _ := mul_one _
  have hmeas_pos : ∀ S : Set (ℝ × ℝ), MeasurableSet S → gμ S ≠ 0 →
      0 < ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ := by
    intro S hS hne
    rw [integral_indicator_one hS, measureReal_def]
    exact ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hD_lower : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      c₀ * ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ
        ≤ ∫ z, derivKernel H W z.1 z.2 * S.indicator 1 z ∂gμ := by
    intro S hS
    rw [← integral_const_mul]
    refine integral_mono_ae ((hind_int S hS).const_mul c₀) (hDind_int S hS) ?_
    filter_upwards [hD_ge] with z hz
    exact mul_le_mul_of_nonneg_right hz (indicator_one_mem_Icc S z).1
  have hD_upper : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      ∫ z, derivKernel H W z.1 z.2 * S.indicator 1 z ∂gμ
        ≤ H.edgeFinset.card * ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ := by
    intro S hS
    rw [← integral_const_mul]
    refine integral_mono (hDind_int S hS) ((hind_int S hS).const_mul _) fun z => ?_
    exact mul_le_mul_of_nonneg_right (hD_mem z.1 z.2).2 (indicator_one_mem_Icc S z).1
  obtain ⟨mE, hmE_def⟩ : ∃ x : ℝ, x = ∫ z, (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z ∂gμ :=
    ⟨_, rfl⟩
  obtain ⟨mA, hmA_def⟩ : ∃ x : ℝ, x = ∫ z, (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z ∂gμ :=
    ⟨_, rfl⟩
  obtain ⟨DE, hDE_def⟩ : ∃ x : ℝ,
      x = ∫ z, derivKernel H W z.1 z.2 * (nearOneSet W δ).indicator 1 z ∂gμ := ⟨_, rfl⟩
  obtain ⟨DA, hDA_def⟩ : ∃ x : ℝ,
      x = ∫ z, derivKernel H W z.1 z.2 * (belowSet W γ₀).indicator 1 z ∂gμ := ⟨_, rfl⟩
  have hmE : 0 < mE := hmE_def ▸ hmeas_pos _ hEm (hEpos δ hδ0)
  have hmA : 0 < mA := hmA_def ▸ hmeas_pos _ hAm hA0
  have hDE_ge : c₀ * mE ≤ DE := hmE_def ▸ hDE_def ▸ hD_lower _ hEm
  have hDA_ge : c₀ * mA ≤ DA := hmA_def ▸ hDA_def ▸ hD_lower _ hAm
  have hDE_le : DE ≤ H.edgeFinset.card * mE := hmE_def ▸ hDE_def ▸ hD_upper _ hEm
  have hDE_pos : 0 < DE := lt_of_lt_of_le (mul_pos hc₀ hmE) hDE_ge
  have hDA_pos : 0 < DA := lt_of_lt_of_le (mul_pos hc₀ hmA) hDA_ge
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 2 * DE / DA := ⟨_, rfl⟩
  have hκ : 0 < κ := hκ_def ▸ by positivity
  -- the first variation along `U`
  have hDU : ∫ z, derivKernel H W z.1 z.2 * (shiftKernel W δ γ₀ κ).toFun z.1 z.2 ∂gμ = DE := by
    have h1 : ∀ z : ℝ × ℝ, derivKernel H W z.1 z.2 * (shiftKernel W δ γ₀ κ).toFun z.1 z.2
        = -(derivKernel H W z.1 z.2 * (nearOneSet W δ).indicator 1 z)
          + κ * (derivKernel H W z.1 z.2 * (belowSet W γ₀).indicator 1 z) := fun z => by
      rw [shiftKernel_apply]; ring
    simp_rw [h1]
    rw [integral_add (hDind_int _ hEm).fun_neg ((hDind_int _ hAm).const_mul κ), integral_neg,
      integral_const_mul, ← hDE_def, ← hDA_def, hκ_def]
    field_simp
    ring
  obtain ⟨ε, hε, hεf⟩ := exists_pos_lt_of_hasDerivAt_pos
    (first_variation H W (shiftKernel W δ γ₀ κ)) (hDU ▸ hDE_pos)
  have hf0 : (Kernel.ofGraphon W + (0:ℝ) • shiftKernel W δ γ₀ κ).tDensity H = W.tDensity H :=
    kernel_tDensity_congr_ae H (L := Kernel.ofGraphon W) (ae_of_all _ fun z => by simp)
  -- the step size
  obtain ⟨θ, hθ_def⟩ : ∃ θ : ℝ, θ = min (ε / 2) (min δ (γ₀ / (2 * κ))) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hθ_def ▸ lt_min (by linarith) (lt_min hδ0 (by positivity))
  have hθε : θ < ε := hθ_def ▸ (min_le_left _ _).trans_lt (by linarith)
  have hθδ : θ ≤ δ := hθ_def ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hθκ : κ * θ ≤ γ₀ / 2 := by
    have h : θ ≤ γ₀ / (2 * κ) := hθ_def ▸ (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hκθ0 : 0 < κ * θ := mul_pos hκ hθ0
  have hmemI := shift_mem_Icc (W := W) (κ := κ) hδγ' hθ0.le hθδ hδ1.le hκθ0.le (by linarith)
  let Vθ : Graphon := (Kernel.ofGraphon W + θ • shiftKernel W δ γ₀ κ).toGraphon
    (fun x y => (hmemI x y).1) (fun x y => (hmemI x y).2)
  -- `Vθ` is feasible, hence `I_p(W) ≤ I_p(Vθ)`
  have hfeas : Feasible H r Vθ := by
    have h := hεf θ hθ0 hθε
    rw [hf0, hact] at h
    exact h.le
  have hge : W.Ip p ≤ Vθ.Ip p := hmin ▸ phiVar_le_of_feasible H hp0 hp1 hfeas
  -- integrate the pointwise comparison of `J_p`
  have hpt : ∀ z : ℝ × ℝ, Jp p (Vθ.toFun z.1 z.2)
      ≤ Jp p (W.toFun z.1 z.2) + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z
        - θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z :=
    Jp_shift_le hp0 hp1 hδγ' hγ₀1 hθ0 hθδ hδ1 hκθ0 hθκ hC₁
  have hiW := W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hiV := Vθ.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hIV : Vθ.Ip p ≤ W.Ip p + θ * κ * C₁ * mA - θ * Jp' p (1 - 2 * δ) * mE := by
    have hi1 : Integrable (fun z : ℝ × ℝ => Jp p (W.toFun z.1 z.2)
        + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z) gμ :=
      hiW.add ((hind_int _ hAm).const_mul (θ * κ * C₁))
    have hi2 : Integrable (fun z : ℝ × ℝ =>
        θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z) gμ :=
      (hind_int _ hEm).const_mul (θ * Jp' p (1 - 2 * δ))
    have h : ∫ z, Jp p (Vθ.toFun z.1 z.2) ∂gμ ≤ ∫ z, (Jp p (W.toFun z.1 z.2)
        + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z
        - θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z) ∂gμ :=
      integral_mono hiV (hi1.sub hi2) hpt
    rw [integral_sub hi1 hi2, integral_add hiW ((hind_int _ hAm).const_mul _),
      integral_const_mul, integral_const_mul, ← hmA_def, ← hmE_def] at h
    exact h
  have hfinal := upper_bound_arith hθ0 hC₁0 hmE hc₀ hDA_pos hκ_def hDE_le hDA_ge hDE_pos.le
    hK_def hcδ
  linarith

end UpperTailSupport

end UpperTailMultipodality
