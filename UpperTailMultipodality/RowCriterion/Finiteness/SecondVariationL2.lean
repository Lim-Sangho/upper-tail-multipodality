import UpperTailMultipodality.RowCriterion.Finiteness.Bordered

/-!
# The second variation on `L²([0,1])` (`lem:row-lower-bound`)

`secondVariation` of `Finiteness/Functional.lean` is the second variation `Q_u` on bounded
directions, which is where the paper defines it.  Before `lem:row-lower-bound` the paper observes
that the kernel representation extends `Q_u` continuously to `L²([0,1])`, and states the lower
bound there.  This file carries out that extension and transfers the bound.

Following the convention of `BddMeas`, the extension is stated for genuine square-integrable
measurable functions rather than almost-everywhere classes: `secondVariationFun u h` is `Q_u(h)`
for measurable `h` with `h² ∈ L¹`, and it agrees with `secondVariation` on bounded directions
(`secondVariationFun_coe`).  The unweighted linearisation `D∇𝒫_W(u)` is obtained from the
weighted `combinedLinFun` of `Finiteness/Bordered.lean` by the identity
`weight u · J_q''(u) = 1`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

/-! ### Cauchy–Schwarz helpers -/

/-- `|fg|` is integrable when `f` and `g` are square-integrable. -/
theorem integrable_abs_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν) : Integrable (fun x => |f x| * |g x|) ν := by
  refine Integrable.mono' ((hf2.add hg2).const_mul (1 / 2))
    (hfm.abs.mul hgm.abs).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
  show |f x| * |g x| ≤ 1 / 2 * (f x ^ 2 + g x ^ 2)
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

/-- **Cauchy–Schwarz**: `∫|f||g| ≤ (∫f²)^{1/2}(∫g²)^{1/2}`. -/
theorem integral_abs_mul_le_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν) :
    ∫ x, |f x| * |g x| ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) * Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
  have hsq : ∀ h : α → ℝ, ∫ x, |h x| ^ 2 ∂ν = ∫ x, h x ^ 2 ∂ν :=
    fun h => integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs _)
  have := integral_mul_le_sqrt_mul_sqrt (f := fun x => |f x|) (g := fun x => |g x|)
    (by simpa [hsq] using hf2) (by simpa [hsq] using hg2)
    (integrable_abs_mul hfm hgm hf2 hg2)
  rwa [hsq, hsq] at this

/-- On a probability space, `∫|f| ≤ (∫f²)^{1/2}`. -/
theorem integral_abs_le_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2) ν) :
    ∫ x, |f x| ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) := by
  have hone : Integrable (fun _ : α => (1:ℝ) ^ 2) ν := by
    simp only [one_pow]; exact integrable_const (1:ℝ)
  have h := integral_abs_mul_le_sqrt (ν := ν) (f := f) (g := fun _ => (1:ℝ)) hfm
    measurable_const hf2 hone
  simpa using h

/-! ### Additivity of the kernel operator -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- The integrand of a kernel operator is integrable. -/
theorem integrable_mul_kernel {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ p, |Φ p| ≤ C) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f unitμ) (y : ℝ) :
    Integrable (fun x => f (e x) * Φ (x, y)) ν := by
  have hfe : Integrable (fun x => f (e x)) ν := he.integrable_comp_of_integrable hf
  have hΦy : Measurable fun x => Φ (x, y) := hΦm.comp (measurable_id.prodMk measurable_const)
  refine Integrable.mono' (hfe.abs.const_mul C)
    ((hfm.comp he.measurable).mul hΦy).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |f (e x)| * |Φ (x, y)| ≤ |f (e x)| * C :=
        mul_le_mul_of_nonneg_left (hΦb (x, y)) (abs_nonneg _)
    _ = C * |f (e x)| := by ring

omit [IsProbabilityMeasure ν] in
/-- **The kernel operator is additive** on integrable functions. -/
theorem kernelFun_sub {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ p, |Φ p| ≤ C) {f g : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f unitμ) (hgm : Measurable g) (hg : Integrable g unitμ) (y : ℝ) :
    kernelFun ν e Φ (f - g) y = kernelFun ν e Φ f y - kernelFun ν e Φ g y := by
  simp only [kernelFun]
  rw [← integral_sub (integrable_mul_kernel he hΦm hΦb hfm hf y)
    (integrable_mul_kernel he hΦm hΦb hgm hg y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (f - g) (e x) * Φ (x, y) = _
  simp only [Pi.sub_apply]
  ring

/-! ### Additivity of the linearisation -/

section Family

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {W : Graphon} {q α : ℝ} {μ : ι → ℝ}

/-- The single-graph linearisation is additive on integrable functions. -/
theorem linFun_sub {H : SimpleGraph V} [DecidableRel H.Adj] {m : ℝ} {u : BddMeas}
    (hu : UnitValued u) {f g : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f unitμ)
    (hgm : Measurable g) (hg : Integrable g unitμ) (y : ℝ) :
    linFun H W m u (f - g) y = linFun H W m u f y - linFun H W m u g y := by
  simp only [linFun, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z₀ _ =>
    Finset.sum_congr rfl fun i _ => ?_
  exact kernelFun_sub (measurePreserving_coord (V := V) (i : V))
    (measurable_linKernel (H := H) (W := W) (μ := m) u v z₀ i) (abs_linKernel_le hu v z₀ i)
    hfm hf hgm hg y

/-- **The linearisation of the family is additive** on integrable functions. -/
theorem combinedLinFun_sub {u : BddMeas} (hu : UnitValued u) {f g : ℝ → ℝ}
    (hfm : Measurable f) (hf : Integrable f unitμ) (hgm : Measurable g)
    (hg : Integrable g unitμ) (y : ℝ) :
    combinedLinFun Hs W μ u (f - g) y
      = combinedLinFun Hs W μ u f y - combinedLinFun Hs W μ u g y := by
  simp only [combinedLinFun, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => linFun_sub hu hfm hf hgm hg y

/-- The `L¹`-to-pointwise bound for the linearisation of the family, with the constant named. -/
theorem exists_abs_combinedLinFun_le (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) (μ : ι → ℝ) {u : BddMeas} (hu : UnitValued u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ, Measurable f → Integrable f unitμ → ∀ y,
      |combinedLinFun Hs W μ u f y| ≤ C * ∫ t, |f t| ∂unitμ := by
  classical
  refine ⟨∑ j, ∑ _v : V, ∑ _z₀ : Nbr (Hs j) _v, ∑ _i : Nbr (Hs j) _v, |μ j| / 2, ?_,
    fun f hfm hf y => ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun v _ => Finset.sum_nonneg
      fun z₀ _ => Finset.sum_nonneg fun i _ => by positivity
  · refine (abs_combinedLinFun_le hu hfm hf y).trans_eq ?_
    simp only [Finset.sum_mul]

/-! ### The second variation on square-integrable directions -/

variable (Hs W μ) in
/-- **`Q_u` on square-integrable directions**, the continuous extension of `secondVariation`
asserted before `lem:row-lower-bound`.  Only the almost everywhere class of `h` matters, by
`combinedLinFun_congr`. -/
noncomputable def secondVariationFun (u : BddMeas) (h : ℝ → ℝ) : ℝ :=
  2 * ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ
    - 2 * ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u h y * h y ∂unitμ

/-- **The extension agrees with `secondVariation` on bounded directions.** -/
theorem secondVariationFun_coe {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    secondVariationFun Hs W μ u ⇑h = secondVariation Hs W μ u h := by
  have hUV : UnitValued u := fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩
  have hpt : ∀ y, 2 * (Jp'' (u y) * combinedLinFun Hs W μ u ⇑h y * h y)
      = (combinedGradDeriv Hs W μ u h * h) y := by
    intro y
    rw [congrFun (combinedLinFun_coe hUV h) y, BddMeas.mul_apply, BddMeas.mul_apply,
      BddMeas.smul_apply]
    have hw := weight_mul_Jpp hc hd hu y
    linear_combination (((combinedGradDeriv Hs W μ u) h) y * h y) * hw
  have h2 : 2 * ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u ⇑h y * h y ∂unitμ
      = ∫ y, (combinedGradDeriv Hs W μ u h * h) y ∂unitμ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [secondVariationFun, secondVariation, BddMeas.integ_apply, h2]

/-- **`Q_u` only depends on the almost everywhere class of the direction.** -/
theorem secondVariationFun_congr (u : BddMeas) {f h : ℝ → ℝ} (hfh : f =ᵐ[unitμ] h) :
    secondVariationFun Hs W μ u f = secondVariationFun Hs W μ u h := by
  have e1 : ∫ y, Jp'' (u y) * f y ^ 2 ∂unitμ = ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ :=
    integral_congr_ae (hfh.mono fun y hy => by
      show Jp'' (u y) * f y ^ 2 = Jp'' (u y) * h y ^ 2
      rw [hy])
  have e2 : ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u f y * f y ∂unitμ
      = ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u h y * h y ∂unitμ := by
    rw [combinedLinFun_congr u hfh]
    exact integral_congr_ae (hfh.mono fun y hy => by
      show Jp'' (u y) * combinedLinFun Hs W μ u h y * f y
          = Jp'' (u y) * combinedLinFun Hs W μ u h y * h y
      rw [hy])
  simp only [secondVariationFun, e1, e2]

variable (Hs W μ) in
/-- **`Q_u` as a function on `L^2([0,1])`**, which is the space the paper states
`lem:row-lower-bound` on.  Evaluating at the representative of a class is unambiguous by
`secondVariationFun_congr`. -/
noncomputable def secondVariationL2 (u : BddMeas) (h : Lp ℝ 2 unitμ) : ℝ :=
  secondVariationFun Hs W μ u ⇑h

/-- The value on `L^2([0,1])` is computed by any representative. -/
theorem secondVariationL2_toLp (u : BddMeas) {h : ℝ → ℝ} (hh : MemLp h 2 unitμ) :
    secondVariationL2 Hs W μ u (hh.toLp h) = secondVariationFun Hs W μ u h :=
  secondVariationFun_congr u hh.coeFn_toLp

/-- On bounded directions the form on `L^2([0,1])` is `secondVariation`. -/
theorem secondVariationL2_toL2 {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    secondVariationL2 Hs W μ u (toL2 h) = secondVariation Hs W μ u h := by
  rw [secondVariationL2, secondVariationFun_congr u (coeFn_toL2 h),
    secondVariationFun_coe hc hd hu]

/-! ### Integrability -/

/-- `J_q''` is measurable. -/
theorem measurable_Jp'' : Measurable Jp'' := by unfold Jp''; fun_prop

/-- A square-integrable function on `[0,1]` is integrable. -/
theorem integrable_of_integrable_sq {h : ℝ → ℝ} (hm : Measurable h)
    (h2 : Integrable (fun y => h y ^ 2) unitμ) : Integrable h unitμ := by
  refine Integrable.mono' ((h2.add (integrable_const 1)).const_mul (1 / 2))
    hm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  show |h y| ≤ 1 / 2 * (h y ^ 2 + 1)
  nlinarith [sq_nonneg (|h y| - 1), sq_abs (h y), abs_nonneg (h y)]

/-- The difference of two square-integrable functions is square-integrable. -/
theorem integrable_sq_sub_fun {f h : ℝ → ℝ} (hfm : Measurable f) (hm : Measurable h)
    (hf2 : Integrable (fun y => f y ^ 2) unitμ) (h2 : Integrable (fun y => h y ^ 2) unitμ) :
    Integrable (fun y => (f y - h y) ^ 2) unitμ := by
  refine Integrable.mono' ((hf2.add h2).const_mul 2)
    ((hfm.sub hm).pow_const 2).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (f y - h y) ^ 2 ≤ 2 * (f y ^ 2 + h y ^ 2)
  nlinarith [sq_nonneg (f y + h y)]

section Bounds

variable {c d : ℝ} {u : BddMeas}

/-- `J_q''(u)` is bounded on a compact subinterval of `(0,1)`. -/
theorem abs_Jpp_comp_le (hc : 0 < c) (hd : d < 1) (hu : ∀ y, u y ∈ Set.Icc c d) (y : ℝ) :
    |Jp'' (u y)| ≤ 1 / (c * (1 - d)) := by
  have h := Jp''_mem_of_mem_Icc hc hd (hu y)
  rw [abs_of_pos h.1]; exact h.2

/-- The entropy integrand of `secondVariationFun` is integrable. -/
theorem integrable_Jpp_mul_sq_fun (hc : 0 < c) (hd : d < 1) (hu : ∀ y, u y ∈ Set.Icc c d)
    {h : ℝ → ℝ} (hm : Measurable h) (h2 : Integrable (fun y => h y ^ 2) unitμ) :
    Integrable (fun y => Jp'' (u y) * h y ^ 2) unitμ := by
  refine Integrable.mono' (h2.const_mul (1 / (c * (1 - d))))
    ((measurable_Jp''.comp u.measurable).mul (hm.pow_const 2)).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (h y))]
  exact mul_le_mul_of_nonneg_right (abs_Jpp_comp_le hc hd hu y) (sq_nonneg _)

/-- The bilinear integrand of `secondVariationFun` is integrable. -/
theorem integrable_Jpp_mul_lin_mul (hc : 0 < c) (hd : d < 1) (hu : ∀ y, u y ∈ Set.Icc c d)
    {C : ℝ}
    (hC : ∀ f : ℝ → ℝ, Measurable f → Integrable f unitμ → ∀ y,
      |combinedLinFun Hs W μ u f y| ≤ C * ∫ t, |f t| ∂unitμ)
    {f h : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f unitμ)
    (hm : Measurable h) (hh : Integrable h unitμ) :
    Integrable (fun y => Jp'' (u y) * combinedLinFun Hs W μ u f y * h y) unitμ := by
  refine Integrable.mono'
    (hh.abs.const_mul (1 / (c * (1 - d)) * (C * ∫ t, |f t| ∂unitμ)))
    (((measurable_Jp''.comp u.measurable).mul
      (measurable_combinedLinFun u hfm)).mul hm).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |Jp'' (u y)| * |combinedLinFun Hs W μ u f y|
      ≤ 1 / (c * (1 - d)) * (C * ∫ t, |f t| ∂unitμ) := by
    have hM : (0:ℝ) ≤ 1 / (c * (1 - d)) := by
      have : 0 < c * (1 - d) := mul_pos hc (by linarith)
      positivity
    exact mul_le_mul (abs_Jpp_comp_le hc hd hu y) (hC f hfm hf y) (abs_nonneg _) hM
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-! ### Continuity for the `L²` seminorm -/

/-- **`Q_u` is continuous for the `L²` seminorm.**  This is the assertion that the kernel
representation "extends `Q_u` continuously to `L²([0,1])`", made just before
`lem:row-lower-bound`.  Both summands of `Q_u` are controlled by the `L²` norm of the difference
times the `L²` norms of the arguments: the entropy term through `f² - h² = (f-h)(f+h)`, and the
bilinear term through the additivity of `combinedLinFun` and its `L¹`-to-pointwise bound. -/
theorem exists_abs_secondVariationFun_sub_le (hc : 0 < c) (hd : d < 1)
    (hu : ∀ y, u y ∈ Set.Icc c d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f h : ℝ → ℝ, Measurable f → Integrable (fun y => f y ^ 2) unitμ →
      Measurable h → Integrable (fun y => h y ^ 2) unitμ →
      |secondVariationFun Hs W μ u f - secondVariationFun Hs W μ u h|
        ≤ K * Real.sqrt (∫ y, (f y - h y) ^ 2 ∂unitμ)
            * (Real.sqrt (∫ y, f y ^ 2 ∂unitμ) + Real.sqrt (∫ y, h y ^ 2 ∂unitμ)) := by
  have hUV : UnitValued u := fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩
  obtain ⟨C, hC0, hC⟩ := exists_abs_combinedLinFun_le Hs W μ hUV
  have hcd : 0 < c * (1 - d) := mul_pos hc (by linarith)
  have hM0 : (0:ℝ) ≤ 1 / (c * (1 - d)) := by positivity
  refine ⟨2 * (1 / (c * (1 - d))) * (1 + C), by positivity, fun f h hfm hf2 hm h2 => ?_⟩
  set M : ℝ := 1 / (c * (1 - d)) with hMdef
  have hem : Measurable (f - h) := hfm.sub hm
  have he2 : Integrable (fun y => (f - h) y ^ 2) unitμ := integrable_sq_sub_fun hfm hm hf2 h2
  have hfi : Integrable f unitμ := integrable_of_integrable_sq hfm hf2
  have hhi : Integrable h unitμ := integrable_of_integrable_sq hm h2
  have hei : Integrable (f - h) unitμ := integrable_of_integrable_sq hem he2
  set Sf := Real.sqrt (∫ y, f y ^ 2 ∂unitμ) with hSfdef
  set Sh := Real.sqrt (∫ y, h y ^ 2 ∂unitμ) with hShdef
  set Se := Real.sqrt (∫ y, (f y - h y) ^ 2 ∂unitμ) with hSedef
  have hSf : 0 ≤ Sf := Real.sqrt_nonneg _
  have hSh : 0 ≤ Sh := Real.sqrt_nonneg _
  have hSe : 0 ≤ Se := Real.sqrt_nonneg _
  have hef : ∫ y, |(f - h) y| * |f y| ∂unitμ ≤ Se * Sf :=
    integral_abs_mul_le_sqrt hem hfm he2 hf2
  have heh : ∫ y, |(f - h) y| * |h y| ∂unitμ ≤ Se * Sh :=
    integral_abs_mul_le_sqrt hem hm he2 h2
  have hL1e : ∫ y, |(f - h) y| ∂unitμ ≤ Se := integral_abs_le_sqrt hem he2
  have hL1f : ∫ y, |f y| ∂unitμ ≤ Sf := integral_abs_le_sqrt hfm hf2
  have hL1h : ∫ y, |h y| ∂unitμ ≤ Sh := integral_abs_le_sqrt hm h2
  -- the entropy term
  have hA : |(∫ y, Jp'' (u y) * f y ^ 2 ∂unitμ) - ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ|
      ≤ M * (Se * Sf + Se * Sh) := by
    rw [← integral_sub (integrable_Jpp_mul_sq_fun hc hd hu hfm hf2)
      (integrable_Jpp_mul_sq_fun hc hd hu hm h2)]
    have hbound : ∀ y, |Jp'' (u y) * f y ^ 2 - Jp'' (u y) * h y ^ 2|
        ≤ M * (|(f - h) y| * |f y| + |(f - h) y| * |h y|) := by
      intro y
      have h1 : Jp'' (u y) * f y ^ 2 - Jp'' (u y) * h y ^ 2
          = Jp'' (u y) * ((f - h) y * (f y + h y)) := by
        show _ = Jp'' (u y) * ((f y - h y) * (f y + h y))
        ring
      rw [h1, abs_mul, abs_mul]
      calc |Jp'' (u y)| * (|(f - h) y| * |f y + h y|)
          ≤ M * (|(f - h) y| * (|f y| + |h y|)) := by
            refine mul_le_mul (abs_Jpp_comp_le hc hd hu y) ?_ (by positivity) hM0
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        _ = M * (|(f - h) y| * |f y| + |(f - h) y| * |h y|) := by ring
    have hint1 : Integrable
        (fun y => M * (|(f - h) y| * |f y| + |(f - h) y| * |h y|)) unitμ :=
      ((integrable_abs_mul hem hfm he2 hf2).add (integrable_abs_mul hem hm he2 h2)).const_mul M
    calc |∫ y, (Jp'' (u y) * f y ^ 2 - Jp'' (u y) * h y ^ 2) ∂unitμ|
        ≤ ∫ y, |Jp'' (u y) * f y ^ 2 - Jp'' (u y) * h y ^ 2| ∂unitμ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, M * (|(f - h) y| * |f y| + |(f - h) y| * |h y|) ∂unitμ :=
          integral_mono ((integrable_Jpp_mul_sq_fun hc hd hu hfm hf2).sub
            (integrable_Jpp_mul_sq_fun hc hd hu hm h2)).abs hint1 hbound
      _ = M * ((∫ y, |(f - h) y| * |f y| ∂unitμ) + ∫ y, |(f - h) y| * |h y| ∂unitμ) := by
          rw [integral_const_mul, integral_add (integrable_abs_mul hem hfm he2 hf2)
            (integrable_abs_mul hem hm he2 h2)]
      _ ≤ M * (Se * Sf + Se * Sh) := mul_le_mul_of_nonneg_left (by linarith) hM0
  -- the bilinear term, through additivity of the linearisation
  have hBint : ∀ {g k : ℝ → ℝ}, Measurable g → Integrable g unitμ → Measurable k →
      Integrable k unitμ →
      Integrable (fun y => Jp'' (u y) * combinedLinFun Hs W μ u g y * k y) unitμ :=
    fun hgm hg hkm hk => integrable_Jpp_mul_lin_mul hc hd hu hC hgm hg hkm hk
  have hBbound : ∀ {g k : ℝ → ℝ} {Sg Sk : ℝ}, Measurable g → Integrable g unitμ →
      Measurable k → Integrable k unitμ → (∫ y, |g y| ∂unitμ) ≤ Sg →
      (∫ y, |k y| ∂unitμ) ≤ Sk → 0 ≤ Sg → 0 ≤ Sk →
      |∫ y, Jp'' (u y) * combinedLinFun Hs W μ u g y * k y ∂unitμ| ≤ M * C * (Sg * Sk) := by
    intro g k Sg Sk hgm hg hkm hk hSg hSk hSg0 hSk0
    have hg0 : (0:ℝ) ≤ ∫ t, |g t| ∂unitμ := integral_nonneg fun t => abs_nonneg _
    have hk0 : (0:ℝ) ≤ ∫ y, |k y| ∂unitμ := integral_nonneg fun y => abs_nonneg _
    have hb : ∀ y, |Jp'' (u y) * combinedLinFun Hs W μ u g y * k y|
        ≤ (M * (C * ∫ t, |g t| ∂unitμ)) * |k y| := by
      intro y
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact mul_le_mul (abs_Jpp_comp_le hc hd hu y) (hC g hgm hg y) (abs_nonneg _) hM0
    calc |∫ y, Jp'' (u y) * combinedLinFun Hs W μ u g y * k y ∂unitμ|
        ≤ ∫ y, |Jp'' (u y) * combinedLinFun Hs W μ u g y * k y| ∂unitμ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, (M * (C * ∫ t, |g t| ∂unitμ)) * |k y| ∂unitμ :=
          integral_mono (hBint hgm hg hkm hk).abs (hk.abs.const_mul _) hb
      _ = (M * (C * ∫ t, |g t| ∂unitμ)) * ∫ y, |k y| ∂unitμ := integral_const_mul _ _
      _ ≤ (M * (C * Sg)) * ∫ y, |k y| ∂unitμ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSg hC0) hM0) hk0
      _ ≤ (M * (C * Sg)) * Sk :=
          mul_le_mul_of_nonneg_left hSk (by positivity)
      _ = M * C * (Sg * Sk) := by ring
  have hpt : ∀ y, Jp'' (u y) * combinedLinFun Hs W μ u f y * f y
      - Jp'' (u y) * combinedLinFun Hs W μ u h y * h y
      = Jp'' (u y) * combinedLinFun Hs W μ u (f - h) y * f y
        + Jp'' (u y) * combinedLinFun Hs W μ u h y * (f - h) y := by
    intro y
    have hlin := combinedLinFun_sub (Hs := Hs) (W := W) (μ := μ) hUV hfm hfi hm hhi y
    show _ = Jp'' (u y) * combinedLinFun Hs W μ u (f - h) y * f y
      + Jp'' (u y) * combinedLinFun Hs W μ u h y * (f y - h y)
    rw [hlin]; ring
  have hB : |(∫ y, Jp'' (u y) * combinedLinFun Hs W μ u f y * f y ∂unitμ)
      - ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u h y * h y ∂unitμ|
      ≤ M * C * (Se * Sf) + M * C * (Sh * Se) := by
    rw [← integral_sub (hBint hfm hfi hfm hfi) (hBint hm hhi hm hhi),
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add (hBint hem hei hfm hfi) (hBint hm hhi hem hei)]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact hBbound hem hei hfm hfi hL1e hL1f hSe hSf
    · exact hBbound hm hhi hem hei hL1h hL1e hSh hSe
  -- combine the two parts
  rw [secondVariationFun, secondVariationFun]
  set Af := ∫ y, Jp'' (u y) * f y ^ 2 ∂unitμ with hAfdef
  set Ah := ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ with hAhdef
  set Bf := ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u f y * f y ∂unitμ with hBfdef
  set Bh := ∫ y, Jp'' (u y) * combinedLinFun Hs W μ u h y * h y ∂unitμ with hBhdef
  have h2A : |2 * (Af - Ah)| ≤ 2 * (M * (Se * Sf + Se * Sh)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h2B : |2 * (Bf - Bh)| ≤ 2 * (M * C * (Se * Sf) + M * C * (Sh * Se)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have hring : (2 * Af - 2 * Bf) - (2 * Ah - 2 * Bh) = 2 * (Af - Ah) - 2 * (Bf - Bh) := by ring
  rw [hring]
  calc |2 * (Af - Ah) - 2 * (Bf - Bh)| ≤ |2 * (Af - Ah)| + |2 * (Bf - Bh)| := abs_sub _ _
    _ ≤ 2 * (M * (Se * Sf + Se * Sh))
        + 2 * (M * C * (Se * Sf) + M * C * (Sh * Se)) := add_le_add h2A h2B
    _ = 2 * M * (1 + C) * Se * (Sf + Sh) := by ring

/-! ### Mean-zero bounded approximation -/

/-- **Truncation.**  A square-integrable mean-zero function is the `L²` limit of mean-zero
bounded measurable functions, as in the proof of `lem:row-lower-bound`: truncate on
`{|h| ≤ n}` and subtract the (vanishing) mean. -/
theorem exists_bddMeas_approx {h : ℝ → ℝ} (hm : Measurable h)
    (h2 : Integrable (fun y => h y ^ 2) unitμ) (hmean : ∫ y, h y ∂unitμ = 0) :
    ∃ g : ℕ → BddMeas, (∀ n, BddMeas.integ (g n) = 0) ∧
      Tendsto (fun n => ∫ y, ((g n) y - h y) ^ 2 ∂unitμ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ y, (g n) y ^ 2 ∂unitμ) atTop (𝓝 (∫ y, h y ^ 2 ∂unitμ)) := by
  classical
  have hhi : Integrable h unitμ := integrable_of_integrable_sq hm h2
  -- the truncations `h · 1_{|h| ≤ n}`
  have htm : ∀ n : ℕ, Measurable (fun y => if |h y| ≤ (n:ℝ) then h y else 0) := fun n =>
    Measurable.ite (measurableSet_le hm.abs measurable_const) hm measurable_const
  set t : ℕ → ℝ → ℝ := fun n y => if |h y| ≤ (n:ℝ) then h y else 0 with htdef
  have htap : ∀ n y, t n y = if |h y| ≤ (n:ℝ) then h y else 0 := fun _ _ => rfl
  have htabs : ∀ n y, |t n y| ≤ |h y| := by
    intro n y
    rw [htap]; split_ifs with hy
    · exact le_refl _
    · simp
  have htb : ∀ n y, |t n y| ≤ (n:ℝ) := by
    intro n y
    rw [htap]; split_ifs with hy
    · exact hy
    · simp
  have htle : ∀ n y, |t n y - h y| ≤ |h y| := by
    intro n y
    rw [htap]; split_ifs with hy
    · simp
    · simp
  have httend : ∀ y, Tendsto (fun n => t n y) atTop (𝓝 (h y)) := by
    intro y
    obtain ⟨N, hN⟩ := exists_nat_ge |h y|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [htap, if_pos (hN.trans (Nat.cast_le.mpr hn))]
  have hti : ∀ n, Integrable (t n) unitμ := fun n => integrable_of_abs_le (htm n) (n:ℝ) (htb n)
  have hti2 : ∀ n, Integrable (fun y => t n y ^ 2) unitμ := fun n =>
    Integrable.mono' h2 ((htm n).pow_const 2).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (t n y), ← sq_abs (h y)]
      exact pow_le_pow_left₀ (abs_nonneg _) (htabs n y) 2)
  -- `∫ (t n - h)² → 0`
  have hsqtend : Tendsto (fun n => ∫ y, (t n y - h y) ^ 2 ∂unitμ) atTop (𝓝 0) := by
    have hdc := tendsto_integral_of_dominated_convergence (μ := unitμ)
      (F := fun n y => (t n y - h y) ^ 2) (f := fun _ => (0:ℝ)) (bound := fun y => h y ^ 2)
      (fun n => (((htm n).sub hm).pow_const 2).aestronglyMeasurable) h2
      (fun n => ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (t n y - h y),
          ← sq_abs (h y)]
        exact pow_le_pow_left₀ (abs_nonneg _) (htle n y) 2)
      (ae_of_all _ fun y => by
        have hd : Tendsto (fun n => t n y - h y) atTop (𝓝 0) := by
          simpa using (httend y).sub (tendsto_const_nhds (x := h y))
        simpa using hd.pow 2)
    simpa using hdc
  -- `∫ t n → 0` and `∫ t n² → ∫ h²`
  have hmtend : Tendsto (fun n => ∫ y, t n y ∂unitμ) atTop (𝓝 0) := by
    have hdc := tendsto_integral_of_dominated_convergence (μ := unitμ) (F := t) (f := h)
      (bound := fun y => |h y|) (fun n => (htm n).aestronglyMeasurable) hhi.abs
      (fun n => ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact htabs n y)
      (ae_of_all _ httend)
    rwa [hmean] at hdc
  have htsqtend : Tendsto (fun n => ∫ y, t n y ^ 2 ∂unitμ) atTop (𝓝 (∫ y, h y ^ 2 ∂unitμ)) :=
    tendsto_integral_of_dominated_convergence (μ := unitμ) (F := fun n y => t n y ^ 2)
      (f := fun y => h y ^ 2) (bound := fun y => h y ^ 2)
      (fun n => ((htm n).pow_const 2).aestronglyMeasurable) h2
      (fun n => ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (t n y), ← sq_abs (h y)]
        exact pow_le_pow_left₀ (abs_nonneg _) (htabs n y) 2)
      (ae_of_all _ fun y => (httend y).pow 2)
  -- the mean-corrected truncations
  refine ⟨fun n => BddMeas.mk (fun y => t n y - ∫ z, t n z ∂unitμ)
    ((htm n).sub measurable_const) ((n:ℝ) + |∫ z, t n z ∂unitμ|) (fun y => ?_), ?_, ?_, ?_⟩
  · calc |t n y - ∫ z, t n z ∂unitμ| ≤ |t n y| + |∫ z, t n z ∂unitμ| := abs_sub _ _
      _ ≤ (n:ℝ) + |∫ z, t n z ∂unitμ| := by linarith [htb n y]
  all_goals
    simp only [BddMeas.mk_apply]
  · -- the means vanish
    intro n
    rw [BddMeas.integ_apply]
    simp only [BddMeas.mk_apply]
    rw [integral_sub (hti n) (integrable_const _), integral_const]
    simp
  · -- `L²` convergence
    have hbd : ∀ n, ∫ y, ((t n y - ∫ z, t n z ∂unitμ) - h y) ^ 2 ∂unitμ
        ≤ 2 * (∫ y, (t n y - h y) ^ 2 ∂unitμ) + 2 * (∫ z, t n z ∂unitμ) ^ 2 := by
      intro n
      have hsq1 : Integrable (fun y => (t n y - h y) ^ 2) unitμ :=
        integrable_sq_sub_fun (htm n) hm (hti2 n) h2
      have hi1 : Integrable (fun y => ((t n y - ∫ z, t n z ∂unitμ) - h y) ^ 2) unitμ :=
        integrable_sq_sub_fun ((htm n).sub measurable_const) hm
          (integrable_sq_sub_fun (htm n) measurable_const (hti2 n)
            (by simp)) h2
      have hi2 : Integrable
          (fun y => 2 * (t n y - h y) ^ 2 + 2 * (∫ z, t n z ∂unitμ) ^ 2) unitμ :=
        (hsq1.const_mul 2).add (integrable_const _)
      calc ∫ y, ((t n y - ∫ z, t n z ∂unitμ) - h y) ^ 2 ∂unitμ
          ≤ ∫ y, (2 * (t n y - h y) ^ 2 + 2 * (∫ z, t n z ∂unitμ) ^ 2) ∂unitμ :=
            integral_mono hi1 hi2 fun y => by
              nlinarith [sq_nonneg ((t n y - h y) + ∫ z, t n z ∂unitμ)]
        _ = 2 * (∫ y, (t n y - h y) ^ 2 ∂unitμ) + 2 * (∫ z, t n z ∂unitμ) ^ 2 := by
            rw [integral_add (hsq1.const_mul 2) (integrable_const _), integral_const_mul,
              integral_const]
            simp
    refine squeeze_zero (fun n => integral_nonneg fun y => sq_nonneg _) hbd ?_
    simpa using (hsqtend.const_mul 2).add ((hmtend.pow 2).const_mul 2)
  · -- the `L²` norms converge
    have hexp : ∀ n, ∫ y, (t n y - ∫ z, t n z ∂unitμ) ^ 2 ∂unitμ
        = (∫ y, t n y ^ 2 ∂unitμ) - (∫ z, t n z ∂unitμ) ^ 2 := by
      intro n
      set m := ∫ z, t n z ∂unitμ with hmdef
      have hpt : ∀ y, (t n y - m) ^ 2 = t n y ^ 2 - 2 * m * t n y + m ^ 2 := fun y => by ring
      have hi1 : Integrable (fun y => t n y ^ 2 - 2 * m * t n y) unitμ :=
        (hti2 n).sub ((hti n).const_mul (2 * m))
      have e1 : ∫ y, (t n y ^ 2 - 2 * m * t n y + m ^ 2) ∂unitμ
          = (∫ y, (t n y ^ 2 - 2 * m * t n y) ∂unitμ) + ∫ _y : ℝ, m ^ 2 ∂unitμ :=
        integral_add hi1 (integrable_const _)
      have e2 : ∫ y, (t n y ^ 2 - 2 * m * t n y) ∂unitμ
          = (∫ y, t n y ^ 2 ∂unitμ) - ∫ y, 2 * m * t n y ∂unitμ :=
        integral_sub (hti2 n) ((hti n).const_mul (2 * m))
      have e3 : ∫ y, 2 * m * t n y ∂unitμ = 2 * m * m := by
        rw [integral_const_mul, ← hmdef]
      have e4 : ∫ _y : ℝ, m ^ 2 ∂unitμ = m ^ 2 := by rw [integral_const]; simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), e1, e2, e3, e4]
      ring
    rw [show (fun n => ∫ y, (t n y - ∫ z, t n z ∂unitμ) ^ 2 ∂unitμ)
        = fun n => (∫ y, t n y ^ 2 ∂unitμ) - (∫ z, t n z ∂unitμ) ^ 2 from funext hexp]
    simpa using htsqtend.sub (hmtend.pow 2)

/-- A bounded measurable function is square-integrable. -/
theorem integrable_sq_bddMeas (b : BddMeas) : Integrable (fun y => b y ^ 2) unitμ :=
  integrable_of_abs_le (b.measurable.pow_const 2) (‖b‖ ^ 2) fun y => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (b y)]
    exact pow_le_pow_left₀ (abs_nonneg _) (b.abs_apply_le_norm y) 2

/-! ### The lower bound on `L²` -/

/-- **`lem:row-lower-bound`, on `L²([0,1])`.**  At a global minimizer `u` of `ℱ_W` over rows with
values in `[c,d] ⊆ (0,1)` satisfying `eq:row-euler`, there is `c_u > 0` such that
`Q_u(h) ≥ c_u ‖h‖₂²` for every square-integrable `h` of mean zero — the statement of
`lem:row-lower-bound` as the paper makes it.  The bounded case is
`exists_secondVariation_lower_bound`; the two are joined by the `L²`-continuity of `Q_u`
(`exists_abs_secondVariationFun_sub_le`) and the truncation `exists_bddMeas_approx`.  The
constant is the same as in the bounded case. -/
theorem exists_secondVariationFun_lower_bound {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    ∃ cu : ℝ, 0 < cu ∧ ∀ h : ℝ → ℝ, Measurable h → Integrable (fun y => h y ^ 2) unitμ →
      (∫ y, h y ∂unitμ) = 0 →
        cu * (∫ y, h y ^ 2 ∂unitμ) ≤ secondVariationFun Hs W μ u h := by
  obtain ⟨cu, hcu, hbound⟩ := exists_secondVariation_lower_bound (Hs := Hs) (W := W) (q := q)
    (α := α) (μ := μ) (j₀ := j₀) hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL
  obtain ⟨K, hK0, hK⟩ :=
    exists_abs_secondVariationFun_sub_le (Hs := Hs) (W := W) (μ := μ) hc hd hu
  refine ⟨cu, hcu, fun h hm h2 hmean => ?_⟩
  obtain ⟨g, hg0, hgL2, hgsq⟩ := exists_bddMeas_approx hm h2 hmean
  -- the bounded bound holds along the approximating sequence
  have hstep : ∀ n, cu * (∫ y, (g n) y ^ 2 ∂unitμ)
      ≤ secondVariationFun Hs W μ u ⇑(g n) := fun n => by
    rw [secondVariationFun_coe hc hd hu]
    exact hbound (g n) (hg0 n)
  -- the values converge, by `L²`-continuity
  have hQtend : Tendsto (fun n => secondVariationFun Hs W μ u ⇑(g n)) atTop
      (𝓝 (secondVariationFun Hs W μ u h)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun n => K * Real.sqrt (∫ y, ((g n) y - h y) ^ 2 ∂unitμ)
        * (Real.sqrt (∫ y, (g n) y ^ 2 ∂unitμ) + Real.sqrt (∫ y, h y ^ 2 ∂unitμ)))
      (fun n => dist_nonneg) (fun n => ?_) ?_
    · rw [Real.dist_eq]
      exact hK _ h (g n).measurable (integrable_sq_bddMeas (g n)) hm h2
    · have h1 : Tendsto (fun n => Real.sqrt (∫ y, ((g n) y - h y) ^ 2 ∂unitμ)) atTop (𝓝 0) := by
        have hcc := (Real.continuous_sqrt.tendsto 0).comp hgL2
        simp only [Function.comp_def, Real.sqrt_zero] at hcc
        exact hcc
      have h2' : Tendsto (fun n => Real.sqrt (∫ y, (g n) y ^ 2 ∂unitμ)
            + Real.sqrt (∫ y, h y ^ 2 ∂unitμ)) atTop
          (𝓝 (Real.sqrt (∫ y, h y ^ 2 ∂unitμ) + Real.sqrt (∫ y, h y ^ 2 ∂unitμ))) :=
        by
        have hs : Tendsto (fun n => Real.sqrt (∫ y, (g n) y ^ 2 ∂unitμ)) atTop
            (𝓝 (Real.sqrt (∫ y, h y ^ 2 ∂unitμ))) := by
          have hcc := (Real.continuous_sqrt.tendsto (∫ y, h y ^ 2 ∂unitμ)).comp hgsq
          simp only [Function.comp_def] at hcc
          exact hcc
        exact hs.add tendsto_const_nhds
      simpa using ((tendsto_const_nhds (x := K) (f := atTop)).mul h1).mul h2'
  exact le_of_tendsto_of_tendsto' (hgsq.const_mul cu) hQtend hstep

/-! ### `lem:row-lower-bound` on `L^2([0,1])` -/

/-- **`lem:row-lower-bound` in the paper's form.**  For a minimizing row `u` with values in a
compact subinterval of `(0,1)` there is `c_u > 0` with `Q_u(h) ≥ c_u‖h‖₂²` for every
`h ∈ L^2([0,1])` of mean zero.  The constant is the one of
`exists_secondVariation_lower_bound`, and the mean-zero hypothesis is the only restriction on
`h`. -/
theorem exists_secondVariationL2_lower_bound {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    ∃ cu : ℝ, 0 < cu ∧ ∀ h : Lp ℝ 2 unitμ, (∫ y, h y ∂unitμ) = 0 →
      cu * ‖h‖ ^ 2 ≤ secondVariationL2 Hs W μ u h := by
  obtain ⟨cu, hcu, hbound⟩ := exists_secondVariationFun_lower_bound (Hs := Hs) (W := W) (q := q)
    (α := α) (μ := μ) (j₀ := j₀) hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL
  refine ⟨cu, hcu, fun h hmean => ?_⟩
  rw [Lp_norm_sq_eq_integral h, secondVariationL2]
  exact hbound _ (Lp.stronglyMeasurable h).measurable (Lp.memLp h).integrable_sq hmean

end Bounds

end Family

end UpperTailMultipodality
