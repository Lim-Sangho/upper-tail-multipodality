import UpperTailMultipodality.FixedDensities.Support.Perturb
import UpperTailMultipodality.FixedDensities.Support.Existence

/-!
# Auxiliary results for degenerate minimizers

* `ae_const_on_of_not_cq` — if `W` violates the constraint qualification, then on every set
  `Ω_η(W)` of positive measure the derivative kernel `𝒟_W` is almost everywhere constant.  This
  is the computation `det Γ_W(1_A, (𝒟_W - D̄)1_A) = |A| ∫_A (𝒟_W - D̄)²` of `lem:degenerate-forms`;
* `Ip_mix_gain` — the `θ log(1/θ)` gain of the mixing path on `{W = 0} ∪ {W = 1}`;
* `tDensity_line_isBigO_sq` — if the first variation of `t(H,·)` along `U` vanishes, then
  `t(H, W + θU) - t(H,W) = O(θ²)`.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The kernel `(𝒟_W - D̄)1_A`. -/
noncomputable def centeredDerivKernel (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (A : Set (ℝ × ℝ)) (hAm : MeasurableSet A) (hAsymm : ∀ x y, (x, y) ∈ A → (y, x) ∈ A)
    (Dbar : ℝ) : Kernel where
  toFun x y := A.indicator (fun z => derivKernel H W z.1 z.2 - Dbar) (x, y)
  symm' x y := by
    by_cases h : (x, y) ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hAsymm x y h)]
      simp only
      rw [derivKernel_symm H W x y]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (hAsymm y x h')]
  meas' := by
    show Measurable fun z : ℝ × ℝ => A.indicator (fun z => derivKernel H W z.1 z.2 - Dbar) z
    exact ((measurable_derivKernel H W).sub measurable_const).indicator hAm
  bdd' := ⟨H.edgeFinset.card + |Dbar|, fun x y => by
    by_cases h : (x, y) ∈ A
    · rw [Set.indicator_of_mem h]
      exact (abs_sub _ _).trans (add_le_add (abs_derivKernel_le H W _ _) le_rfl)
    · rw [Set.indicator_of_notMem h, abs_zero]
      positivity⟩

/-- The value of the kernel `(𝒟_W - D̄)1_A`. -/
theorem centeredDerivKernel_apply (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (A : Set (ℝ × ℝ)) (hAm : MeasurableSet A) (hAsymm : ∀ x y, (x, y) ∈ A → (y, x) ∈ A)
    (Dbar x y : ℝ) :
    (centeredDerivKernel H W A hAm hAsymm Dbar).toFun x y
      = A.indicator (fun z => derivKernel H W z.1 z.2 - Dbar) (x, y) := rfl

/-- **`lem:degenerate-forms`, the determinant computation.**  If `W` violates the constraint
qualification and `Ω_η(W)` has positive measure, then `𝒟_W` is almost everywhere constant on
`Ω_η(W)`. -/
theorem ae_const_on_of_not_cq (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (hdeg : ¬ ConstraintQualification H W) {η : ℝ} (hη : 0 < η)
    (hpos : gμ {z : ℝ × ℝ | η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η} ≠ 0) :
    ∃ c : ℝ, ∀ᵐ z ∂gμ, η < W.toFun z.1 z.2 → W.toFun z.1 z.2 < 1 - η →
      derivKernel H W z.1 z.2 = c := by
  obtain ⟨A, hA⟩ : ∃ A, A = {z : ℝ × ℝ | η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η} :=
    ⟨_, rfl⟩
  have hAm : MeasurableSet A := by
    rw [hA]
    exact (measurableSet_lt measurable_const W.meas').inter
      (measurableSet_lt W.meas' measurable_const)
  have hAsymm : ∀ x y, (x, y) ∈ A → (y, x) ∈ A := by
    intro x y h
    rw [hA] at h ⊢
    simpa only [Set.mem_ofPred_eq, W.symm' y x] using h
  have hApos : 0 < gμ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hA ▸ hpos) (measure_ne_top _ _)
  obtain ⟨Dbar, hDbar⟩ : ∃ D, D = (∫ z in A, derivKernel H W z.1 z.2 ∂gμ) / gμ.real A := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U, U = indicatorKernel A hAm hAsymm 1 := ⟨_, rfl⟩
  obtain ⟨U₂, hU₂⟩ : ∃ U, U = centeredDerivKernel H W A hAm hAsymm Dbar := ⟨_, rfl⟩
  have hs₁ : SupportedIn W η U₁ := by
    intro x y hne
    rw [hU₁, indicatorKernel_apply] at hne
    by_contra h
    exact hne (Set.indicator_of_notMem (fun hm => h (by rw [hA] at hm; exact hm)) _)
  have hs₂ : SupportedIn W η U₂ := by
    intro x y hne
    rw [hU₂, centeredDerivKernel_apply] at hne
    by_contra h
    exact hne (Set.indicator_of_notMem (fun hm => h (by rw [hA] at hm; exact hm)) _)
  have hdet : cqDet H W U₁ U₂ = 0 := by
    by_contra h
    exact hdeg ⟨η, hη, U₁, U₂, hs₁, hs₂, h⟩
  -- the four integrals
  have hi1 : ∫ z, U₁.toFun z.1 z.2 ∂gμ = gμ.real A := by
    rw [hU₁, integral_indicatorKernel, one_mul]
  have hiD : Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2) gμ :=
    integrable_of_abs_le (measurable_derivKernel H W) H.edgeFinset.card
      fun z => abs_derivKernel_le H W _ _
  have hi2 : ∫ z, U₂.toFun z.1 z.2 ∂gμ = 0 := by
    rw [hU₂]
    simp only [centeredDerivKernel_apply, Prod.mk.eta]
    rw [integral_indicator hAm, integral_sub hiD.integrableOn
      (integrableOn_const (C := Dbar) (measure_ne_top _ _)), setIntegral_const, hDbar,
      smul_eq_mul]
    field_simp
    ring
  have hi3 : ∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ
      = ∫ z, U₂.toFun z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ := by
    have hfun : ∀ z : ℝ × ℝ, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2
        = U₂.toFun z.1 z.2 * U₂.toFun z.1 z.2 + Dbar * U₂.toFun z.1 z.2 := by
      intro z
      rw [hU₂, centeredDerivKernel_apply, Prod.mk.eta]
      by_cases h : z ∈ A
      · rw [Set.indicator_of_mem h]; ring
      · rw [Set.indicator_of_notMem h]; ring
    have hsq : Integrable (fun z : ℝ × ℝ => U₂.toFun z.1 z.2 * U₂.toFun z.1 z.2) gμ := by
      obtain ⟨C, hC0, hC⟩ := kernel_bound U₂
      exact integrable_mul_of_ae_bdd U₂.meas' U₂.meas' (ae_of_all _ fun z => hC z.1 z.2)
        (ae_of_all _ fun z => hC z.1 z.2)
    simp_rw [hfun]
    rw [integral_add hsq ((kernel_integrable U₂).const_mul Dbar), integral_const_mul, hi2,
      mul_zero, add_zero]
  -- the determinant vanishes, hence `U₂ = 0` almost everywhere
  have hzero : ∫ z, U₂.toFun z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ = 0 := by
    rw [cqDet, hi1, hi2, hi3, zero_mul, sub_zero] at hdet
    rcases mul_eq_zero.mp hdet with h | h
    · exact absurd h hApos.ne'
    · exact h
  have hsq : Integrable (fun z : ℝ × ℝ => U₂.toFun z.1 z.2 * U₂.toFun z.1 z.2) gμ := by
    obtain ⟨C, hC0, hC⟩ := kernel_bound U₂
    exact integrable_mul_of_ae_bdd U₂.meas' U₂.meas' (ae_of_all _ fun z => hC z.1 z.2)
      (ae_of_all _ fun z => hC z.1 z.2)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg _) hsq).mp hzero
  refine ⟨Dbar, ?_⟩
  filter_upwards [hae] with z hz h1 h2
  have hmem : z ∈ A := by rw [hA]; exact ⟨h1, h2⟩
  have : U₂.toFun z.1 z.2 = 0 := by
    have := mul_self_eq_zero.mp hz
    exact this
  rw [hU₂, centeredDerivKernel_apply, Prod.mk.eta, Set.indicator_of_mem hmem] at this
  linarith

/-- If `A` has positive measure and `p` holds almost everywhere on `A`, then some point of `A`
satisfies `p`. -/
theorem exists_mem_of_measure_ne_zero {A : Set (ℝ × ℝ)} (h : gμ A ≠ 0) {p : ℝ × ℝ → Prop}
    (hp : ∀ᵐ z ∂gμ, z ∈ A → p z) : ∃ z ∈ A, p z := by
  by_contra hc
  have hnot : ∀ z ∈ A, ¬ p z := by
    intro z hz hpz
    exact hc ⟨z, hz, hpz⟩
  have hae : ∀ᵐ z ∂gμ, z ∉ A := by
    filter_upwards [hp] with z hz hzA
    exact hnot z hzA (hz hzA)
  exact h (by simpa [ae_iff] using hae)

/-! ### The mixing path towards the constant graphon -/

/-- The kernel `ε - W`. -/
noncomputable def constSubKernel (W : Graphon) (ε : ℝ) : Kernel where
  toFun x y := ε - W.toFun x y
  symm' x y := by rw [W.symm']
  meas' := measurable_const.sub W.meas'
  bdd' := ⟨|ε| + 1, fun x y => (abs_sub _ _).trans (add_le_add le_rfl (by
    rw [abs_of_nonneg (W.nonneg' x y)]; exact W.le_one' x y))⟩

/-- The value of the kernel `ε - W`. -/
@[simp] theorem constSubKernel_apply (W : Graphon) (ε x y : ℝ) :
    (constSubKernel W ε).toFun x y = ε - W.toFun x y := rfl

/-- **The mixing path `(1-θ)W + θε`.**  It has edge density `ε`, `H`-density
`t(H, W + θ(ε - W))` and cost at most `(1-θ)I_ε(W)`. -/
theorem exists_mix (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε θ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he : W.edgeDensity = ε) :
    ∃ V : Graphon, (∀ x y, V.toFun x y = (1 - θ) * W.toFun x y + θ * ε) ∧ V.edgeDensity = ε ∧
      V.tDensity H = (Kernel.ofGraphon W + θ • constSubKernel W ε).tDensity H ∧
      V.Ip ε ≤ (1 - θ) * W.Ip ε := by
  have hθ' : 1 - θ ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  refine ⟨Wmix W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) (1 - θ) hθ', fun x y => by
    rw [Wmix_apply]; ring, ?_, ?_, Ip_Wmix_le W hε0 hε1 hθ'⟩
  · rw [edgeDensity_Wmix, he]; ring
  · rw [← Kernel.tDensity_ofGraphon]
    refine kernel_tDensity_congr H fun x y => ?_
    show (1 - (1 - θ)) * ε + (1 - θ) * W.toFun x y = W.toFun x y + θ * (ε - W.toFun x y)
    ring

/-- **The `θ log(1/θ)` gain at the endpoints.**  If `V = (1-θ)W + θε`, then `I_ε(W) - I_ε(V)` is
at least `|{W = 0} ∪ {W = 1}| · min(ε, 1-ε) · θ log(1/θ)`. -/
theorem Ip_mix_gain (W : Graphon) {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {V : Graphon} (hV : ∀ x y, V.toFun x y = (1 - θ) * W.toFun x y + θ * ε) :
    gμ.real {z : ℝ × ℝ | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1}
        * (min ε (1 - ε) * (θ * Real.log (1 / θ))) ≤ W.Ip ε - V.Ip ε := by
  obtain ⟨B, hB⟩ : ∃ B, B = {z : ℝ × ℝ | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    rw [hB]
    exact (measurableSet_eq_fun W.meas' measurable_const).union
      (measurableSet_eq_fun W.meas' measurable_const)
  have hlog : 0 ≤ Real.log (1 / θ) := by
    rw [one_div]
    exact Real.log_nonneg (by rw [le_inv_comm₀ one_pos hθ0]; linarith)
  have hκ : 0 < min ε (1 - ε) := lt_min hε0 (by linarith)
  have hpt : ∀ z : ℝ × ℝ, B.indicator (fun _ => min ε (1 - ε) * (θ * Real.log (1 / θ))) z
      ≤ Jp ε (W.toFun z.1 z.2) - Jp ε (V.toFun z.1 z.2) := by
    intro z
    have hnn : 0 ≤ Jp ε (W.toFun z.1 z.2) - Jp ε (V.toFun z.1 z.2) := by
      have h1 : Jp ε (V.toFun z.1 z.2) ≤ (1 - θ) * Jp ε (W.toFun z.1 z.2) := by
        rw [hV]
        exact Jp_mix_le hε0 hε1 (W.mem_Icc z.1 z.2) (Set.mem_Icc.mpr ⟨hθ0.le, hθ1.le⟩)
      have h2 : 0 ≤ Jp ε (W.toFun z.1 z.2) := by
        rcases eq_or_ne (W.toFun z.1 z.2) ε with h | h
        · rw [h, Jp_self hε0 hε1]
        · exact (Jp_pos_of_ne hε0 hε1 (W.nonneg' _ _) (W.le_one' _ _) h).le
      nlinarith
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      rw [hB] at hz
      rcases hz with h0 | h1
      · have hVz : V.toFun z.1 z.2 = θ * ε := by rw [hV, h0]; ring
        have := Jp_zero_sub_ge hε0 hε1 hθ0 hθ1
        rw [h0, hVz]
        calc min ε (1 - ε) * (θ * Real.log (1 / θ)) ≤ ε * (θ * Real.log (1 / θ)) := by
              have := min_le_left ε (1 - ε)
              nlinarith [mul_nonneg hθ0.le hlog]
          _ = ε * θ * Real.log (1 / θ) := by ring
          _ ≤ Jp ε 0 - Jp ε (θ * ε) := this
      · have hVz : V.toFun z.1 z.2 = 1 - θ * (1 - ε) := by rw [hV, h1]; ring
        have := Jp_one_sub_ge hε0 hε1 hθ0 hθ1
        rw [h1, hVz]
        calc min ε (1 - ε) * (θ * Real.log (1 / θ)) ≤ (1 - ε) * (θ * Real.log (1 / θ)) := by
              have := min_le_right ε (1 - ε)
              nlinarith [mul_nonneg hθ0.le hlog]
          _ = (1 - ε) * θ * Real.log (1 / θ) := by ring
          _ ≤ Jp ε 1 - Jp ε (1 - θ * (1 - ε)) := this
    · rw [Set.indicator_of_notMem hz]
      exact hnn
  have hIW := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hIV := V.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hint : ∫ z, B.indicator (fun _ => min ε (1 - ε) * (θ * Real.log (1 / θ))) z ∂gμ
      ≤ ∫ z, (Jp ε (W.toFun z.1 z.2) - Jp ε (V.toFun z.1 z.2)) ∂gμ :=
    integral_mono ((integrable_const _).indicator hBm) (hIW.sub hIV) hpt
  rw [integral_indicator_const _ hBm, integral_sub hIW hIV, smul_eq_mul, hB] at hint
  exact hint

/-- **A vanishing first variation gives a quadratic bound.**  If `∫∫ 𝒟_W U = 0`, then
`t(H, W + θU) - t(H,W) = O(θ²)` as `θ → 0`. -/
theorem tDensity_line_isBigO_sq (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (U : Kernel) (hd0 : (∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ θ in 𝓝 (0:ℝ),
      |(Kernel.ofGraphon W + θ • U).tDensity H - W.tDensity H| ≤ K * θ ^ 2 := by
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun θ : ℝ => (Kernel.ofGraphon W + θ • U).tDensity H :=
    ⟨_, rfl⟩
  have hf0 : f 0 = W.tDensity H := by
    rw [hfdef]
    show (Kernel.ofGraphon W + (0:ℝ) • U).tDensity H = W.tDensity H
    rw [← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  have hderiv : HasDerivAt f 0 0 := by
    have h := first_variation H W U
    rw [hd0] at h
    rw [hfdef]
    exact h
  -- `f` is analytic at `0`
  have hg : AnalyticAt ℝ (fun s : Fin 1 → ℝ => ((Kernel.ofGraphon W).lincomb ![U] s).tDensity H)
      0 := analyticOnNhd_tDensity_lincomb H (Kernel.ofGraphon W) ![U] 0 trivial
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ →L[ℝ] (Fin 1 → ℝ), ∀ θ : ℝ, L1 θ = fun _ : Fin 1 => θ :=
    ⟨ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ, fun θ => rfl⟩
  have hcomp : AnalyticAt ℝ f 0 := by
    have hlin : AnalyticAt ℝ (fun θ : ℝ => L1 θ) 0 := L1.analyticAt 0
    have h0 : L1 0 = 0 := map_zero L1
    have := (h0 ▸ hg).comp hlin
    refine this.congr ?_
    filter_upwards with θ
    rw [hfdef, Function.comp_apply, hL1]
    refine kernel_tDensity_congr H fun x y => ?_
    simp [Kernel.lincomb]
  obtain ⟨p, hp⟩ := hcomp
  have hcoeff : p.coeff 1 = 0 := hp.hasDerivAt.unique hderiv
  have hbigO := hp.isBigO_sub_partialSum_pow 2
  have hpart : ∀ y : ℝ, p.partialSum 2 y = f 0 := by
    intro y
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_one,
      hp.coeff_zero, p.apply_eq_pow_smul_coeff, hcoeff]
    simp
  obtain ⟨K, hK0, hK⟩ := hbigO.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hK
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hK] with y hy
  rw [hpart, zero_add] at hy
  have hfy : f y = (Kernel.ofGraphon W + y • U).tDensity H := by rw [hfdef]
  rw [← hfy, ← hf0]
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y), sq_abs] using hy

/-- **`θ ↦ t(H, W + θU)` is continuous.**  It is a polynomial in `θ`, by
`analyticOnNhd_tDensity_lincomb`.  Only continuity is needed, to hit every value slightly below
`t(H,W)` by the intermediate value theorem. -/
theorem continuous_tDensity_line (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (U : Kernel) :
    Continuous fun θ : ℝ => (Kernel.ofGraphon W + θ • U).tDensity H := by
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ →L[ℝ] (Fin 1 → ℝ), ∀ θ : ℝ, L1 θ = fun _ : Fin 1 => θ :=
    ⟨ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ, fun θ => rfl⟩
  have hg : Continuous fun s : Fin 1 → ℝ =>
      ((Kernel.ofGraphon W).lincomb ![U] s).tDensity H :=
    continuousOn_univ.mp
      (analyticOnNhd_tDensity_lincomb H (Kernel.ofGraphon W) ![U]).continuousOn
  refine (hg.comp L1.continuous).congr fun θ => ?_
  rw [Function.comp_apply, hL1]
  refine kernel_tDensity_congr H fun x y => ?_
  simp [Kernel.lincomb]

end FixedDensities

end UpperTailMultipodality
