import UpperTailMultipodality.RowCriterion.Finiteness.ProductDensity
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Integral operators with bounded kernels on `L²`

For a probability space `(X,ν)`, a measure-preserving `e : X → [0,1]` and a bounded measurable
kernel `Φ` on `X × [0,1]`, the operator

`(K f)(y) = ∫ f(e x) Φ(x,y) dν(x)`

is bounded on `L²([0,1])` with `‖K‖ ≤ ‖Φ‖_{L²}`, and it is compact (`isCompactOperator_kernelOp`):
it is a norm limit of the finite-rank operators attached to the finite sums of products supplied by
`exists_isProdSimple_approx`.  This is the Hilbert–Schmidt compactness that the paper uses in
`lem:row-compact`; here it is used for the surjectivity half of `lem:bordered`, while
`lem:row-compact` is obtained from the mean parametrization instead (`Finiteness/Compact.lean`).
-/

namespace UpperTailMultipodality

open MeasureTheory

/-! ## Cauchy–Schwarz for the Bochner integral -/

/-- The scalar step of Cauchy–Schwarz. -/
private theorem cs_aux {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : Real.sqrt A * Real.sqrt B * C ≤ A * B) (hz : A * B = 0 → C ≤ 0) :
    C ≤ Real.sqrt A * Real.sqrt B := by
  have hsq : Real.sqrt A * Real.sqrt B * (Real.sqrt A * Real.sqrt B) = A * B := by
    rw [← pow_two, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  rcases eq_or_lt_of_le (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)) with hk | hk
  · exact le_trans (hz (by rw [← hsq, ← hk]; ring)) (le_of_eq hk)
  · exact le_of_mul_le_mul_left (by rw [hsq]; exact h) hk

/-- **Cauchy–Schwarz for the Bochner integral**: `∫ f·g ≤ (∫f²)^{1/2}(∫g²)^{1/2}`. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hA : (0:ℝ) ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : (0:ℝ) ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  refine cs_aux hA hB ?_ ?_
  · have h0 : (0:ℝ) ≤ ∫ x, (Real.sqrt (∫ t, g t ^ 2 ∂μ) * f x
        - Real.sqrt (∫ t, f t ^ 2 ∂μ) * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e1 : Real.sqrt (∫ t, f t ^ 2 ∂μ) ^ 2 = ∫ t, f t ^ 2 ∂μ := Real.sq_sqrt hA
    have e2 : Real.sqrt (∫ t, g t ^ 2 ∂μ) ^ 2 = ∫ t, g t ^ 2 ∂μ := Real.sq_sqrt hB
    have hpt : ∀ x, (Real.sqrt (∫ t, g t ^ 2 ∂μ) * f x - Real.sqrt (∫ t, f t ^ 2 ∂μ) * g x) ^ 2
        = (∫ t, g t ^ 2 ∂μ) * f x ^ 2
          - 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ)) * (f x * g x)
          + (∫ t, f t ^ 2 ∂μ) * g x ^ 2 := by
      intro x
      linear_combination (f x ^ 2) * e2 + (g x ^ 2) * e1
    have hi1 : Integrable (fun x => (∫ t, g t ^ 2 ∂μ) * f x ^ 2) μ := hf2.const_mul _
    have hi2 : Integrable (fun x => 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ)
        * Real.sqrt (∫ t, g t ^ 2 ∂μ)) * (f x * g x)) μ := hfg.const_mul _
    have hi3 : Integrable (fun x => (∫ t, f t ^ 2 ∂μ) * g x ^ 2) μ := hg2.const_mul _
    have hi12 : Integrable (fun x => (∫ t, g t ^ 2 ∂μ) * f x ^ 2
        - 2 * (Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ))
          * (f x * g x)) μ := hi1.sub hi2
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hi12 hi3, integral_sub hi1 hi2, integral_const_mul,
      integral_const_mul, integral_const_mul] at h0
    nlinarith [h0]
  · intro hAB
    have key : ∀ {p q : α → ℝ}, Integrable (fun x => p x ^ 2) μ → (∫ x, p x ^ 2 ∂μ) = 0 →
        (fun x => p x * q x) =ᵐ[μ] 0 := by
      intro p q hp2 hp
      have hp0 : (fun x => p x ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hp2).mp hp
      filter_upwards [hp0] with x hx
      have hx' : p x ^ 2 = 0 := by simpa using hx
      have hx0 : p x = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hx'
      simp [hx0]
    rcases mul_eq_zero.mp hAB with h | h
    · rw [integral_congr_ae (key hf2 h)]; simp
    · have h' : (fun x => g x * f x) =ᵐ[μ] 0 := key hg2 h
      have h'' : (fun x => f x * g x) =ᵐ[μ] 0 := by
        filter_upwards [h'] with x hx
        simpa [mul_comm] using hx
      rw [integral_congr_ae h'']; simp

/-- The squared form of Cauchy–Schwarz. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hA : (0:ℝ) ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : (0:ℝ) ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h1 := integral_mul_le_sqrt_mul_sqrt hf2 hg2 hfg
  have h2 : ∫ x, (-f x) * g x ∂μ
      ≤ Real.sqrt (∫ x, (-f x) ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    refine integral_mul_le_sqrt_mul_sqrt ?_ hg2 ?_
    · simpa using hf2
    · simpa using hfg.neg
  have hneg : ∫ x, (-f x) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ := by simp
  have hneg2 : ∫ x, (-f x) * g x ∂μ = -∫ x, f x * g x ∂μ := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hneg, hneg2] at h2
  have habs : |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) :=
    abs_le.mpr ⟨by linarith, h1⟩
  have := mul_self_le_mul_self (abs_nonneg _) habs
  rw [abs_mul_abs_self] at this
  calc (∫ x, f x * g x ∂μ) ^ 2 = (∫ x, f x * g x ∂μ) * (∫ x, f x * g x ∂μ) := sq _
    _ ≤ (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ))
        * (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)) := this
    _ = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
        rw [show Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)
            * (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ))
            = (Real.sqrt (∫ x, f x ^ 2 ∂μ) ^ 2) * (Real.sqrt (∫ x, g x ^ 2 ∂μ) ^ 2) by ring,
          Real.sq_sqrt hA, Real.sq_sqrt hB]

/-! ## The `L²` norm as an integral -/

/-- The squared `L²` norm as an integral. -/
theorem Lp_norm_sq_eq_integral (f : Lp ℝ 2 unitμ) : ‖f‖ ^ 2 = ∫ y, (f y) ^ 2 ∂unitμ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
    simp [sq])

/-- A bound on the squared `L²` norm bounds the norm. -/
theorem norm_le_of_sq_le {f : Lp ℝ 2 unitμ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∫ y, (f y) ^ 2 ∂unitμ ≤ c ^ 2) : ‖f‖ ≤ c := by
  have h1 : ‖f‖ ^ 2 ≤ c ^ 2 := by rw [Lp_norm_sq_eq_integral]; exact h
  nlinarith [norm_nonneg f]

/-! ## Integral operators -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- The kernel operator, acting on functions. -/
noncomputable def kernelFun (ν : Measure X) (e : X → ℝ) (Φ : X × ℝ → ℝ) (f : ℝ → ℝ) (y : ℝ) :
    ℝ := ∫ x, f (e x) * Φ (x, y) ∂ν

omit [IsProbabilityMeasure ν] in
/-- The kernel operator depends only on the almost everywhere class. -/
theorem kernelFun_congr {e : X → ℝ} (he : MeasurePreserving e ν unitμ) (Φ : X × ℝ → ℝ)
    {f g : ℝ → ℝ} (hfg : f =ᵐ[unitμ] g) : kernelFun ν e Φ f = kernelFun ν e Φ g := by
  funext y
  refine integral_congr_ae ?_
  filter_upwards [he.quasiMeasurePreserving.ae hfg] with x hx
  rw [hx]

/-- The kernel operator produces measurable functions. -/
theorem measurable_kernelFun {e : X → ℝ} (he : Measurable e) {Φ : X × ℝ → ℝ}
    (hΦ : Measurable Φ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (kernelFun ν e Φ f) := by
  have hjoint : Measurable fun p : X × ℝ => f (e p.1) * Φ p :=
    ((hf.comp he).comp measurable_fst).mul hΦ
  exact (hjoint.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable

omit [IsProbabilityMeasure ν] in
/-- The kernel operator is bounded by the supremum of the kernel times the `L¹` norm. -/
theorem abs_kernelFun_le {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ p, |Φ p| ≤ C) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f unitμ) (y : ℝ) :
    |kernelFun ν e Φ f y| ≤ C * ∫ t, |f t| ∂unitμ := by
  have hfe : Integrable (fun x => f (e x)) ν := he.integrable_comp_of_integrable hf
  have hmeas : Measurable fun x => f (e x) * Φ (x, y) :=
    ((hfm.comp he.measurable)).mul (hΦm.comp (measurable_id.prodMk measurable_const))
  have hbound : ∀ x, |f (e x) * Φ (x, y)| ≤ C * |f (e x)| := by
    intro x
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hΦb (x, y)) (abs_nonneg _)
  have hint : Integrable (fun x => f (e x) * Φ (x, y)) ν :=
    Integrable.mono' (hfe.abs.const_mul C) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbound x)
  have hmarg : ∫ x, |f (e x)| ∂ν = ∫ t, |f t| ∂unitμ := by
    have h := integral_map (μ := ν) (φ := e) he.measurable.aemeasurable (f := fun t => |f t|)
      (by rw [he.map_eq]; exact hf.abs.aestronglyMeasurable)
    rw [he.map_eq] at h
    exact h.symm
  calc |kernelFun ν e Φ f y| ≤ ∫ x, |f (e x) * Φ (x, y)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * |f (e x)| ∂ν := integral_mono hint.abs (hfe.abs.const_mul C) hbound
    _ = C * ∫ t, |f t| ∂unitμ := by rw [integral_const_mul, hmarg]

/-- The `L²` bound for the kernel operator: `∫ (K f)² ≤ (∫∫ Φ²)(∫ f²)`. -/
theorem integral_sq_kernelFun_le {e : X → ℝ} (he : MeasurePreserving e ν unitμ)
    {Φ : X × ℝ → ℝ} (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ p, |Φ p| ≤ C) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun y => f y ^ 2) unitμ)
    (hf : Integrable f unitμ) :
    ∫ y, (kernelFun ν e Φ f y) ^ 2 ∂unitμ
      ≤ (∫ p, (Φ p) ^ 2 ∂(ν.prod unitμ)) * ∫ y, (f y) ^ 2 ∂unitμ := by
  have hfe2 : Integrable (fun x => f (e x) ^ 2) ν := by
    have := he.integrable_comp_of_integrable hf2
    exact this
  have hΦ2 : ∀ y, Integrable (fun x => Φ (x, y) ^ 2) ν := fun y =>
    integrable_of_abs_le (((hΦm.comp (measurable_id.prodMk measurable_const))).pow_const 2)
      (C ^ 2) fun x => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hΦb (x, y)) 2
  have hprod : ∀ y, Integrable (fun x => f (e x) * Φ (x, y)) ν := by
    intro y
    have hfe : Integrable (fun x => f (e x)) ν := he.integrable_comp_of_integrable hf
    refine Integrable.mono' (hfe.abs.const_mul C)
      (((hfm.comp he.measurable).mul (hΦm.comp (measurable_id.prodMk measurable_const)))
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hΦb (x, y)) (abs_nonneg _)
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ y, (kernelFun ν e Φ f y) ^ 2
      ≤ (∫ y', (f y') ^ 2 ∂unitμ) * ∫ x, (Φ (x, y)) ^ 2 ∂ν := by
    intro y
    have h := sq_integral_mul_le hfe2 (hΦ2 y) (hprod y)
    have hmarg : ∫ x, f (e x) ^ 2 ∂ν = ∫ y', (f y') ^ 2 ∂unitμ := by
      have hmap := integral_map (μ := ν) (φ := e) he.measurable.aemeasurable
        (f := fun t => (f t) ^ 2) (by rw [he.map_eq]; exact hf2.aestronglyMeasurable)
      rw [he.map_eq] at hmap
      exact hmap.symm
    rw [hmarg] at h
    exact h
  have hfin : ∫ y, ((∫ y', (f y') ^ 2 ∂unitμ) * ∫ x, (Φ (x, y)) ^ 2 ∂ν) ∂unitμ
      = (∫ p, (Φ p) ^ 2 ∂(ν.prod unitμ)) * ∫ y, (f y) ^ 2 ∂unitμ := by
    rw [integral_const_mul]
    have hint : Integrable (fun p : X × ℝ => (Φ p) ^ 2) (ν.prod unitμ) :=
      integrable_of_abs_le (hΦm.pow_const 2) (C ^ 2) fun p => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hΦb p) 2
    rw [integral_prod_symm _ hint]
    ring
  have hintK : Integrable (fun y => (kernelFun ν e Φ f y) ^ 2) unitμ := by
    refine integrable_of_abs_le ((measurable_kernelFun he.measurable hΦm hfm).pow_const 2)
      ((C * ∫ t, |f t| ∂unitμ) ^ 2) fun y => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_kernelFun_le he hΦm hΦb hfm hf y) 2
  calc ∫ y, (kernelFun ν e Φ f y) ^ 2 ∂unitμ
      ≤ ∫ y, ((∫ y', (f y') ^ 2 ∂unitμ) * ∫ x, (Φ (x, y)) ^ 2 ∂ν) ∂unitμ := by
        refine integral_mono hintK ?_ hpt
        have hint : Integrable (fun p : X × ℝ => (Φ p) ^ 2) (ν.prod unitμ) :=
          integrable_of_abs_le (hΦm.pow_const 2) (C ^ 2) fun p => by
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hΦb p) 2
        exact (hint.swap.integral_prod_left).const_mul _
    _ = _ := hfin

/-! ### The operator on `L²` -/

/-- The kernel operator produces `L²` functions. -/
theorem memLp_kernelFun {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hΦb : ∀ p, |Φ p| ≤ C) (f : Lp ℝ 2 unitμ) :
    MemLp (kernelFun ν e Φ f) 2 unitμ := by
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hf : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  refine MemLp.of_bound ((measurable_kernelFun he.measurable hΦm hfm)).aestronglyMeasurable
    (C * ∫ t, |f t| ∂unitμ) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_kernelFun_le he hΦm hΦb hfm hf y


/-- The `L¹` norm is at most the `L²` norm on a probability space. -/
theorem integral_abs_le_norm (f : Lp ℝ 2 unitμ) : ∫ y, |f y| ∂unitμ ≤ ‖f‖ := by
  have hf2 : Integrable (fun y => (f y) ^ 2) unitμ := (Lp.memLp f).integrable_sq
  have hf : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  have h := integral_mul_le_sqrt_mul_sqrt (μ := unitμ) (f := fun y => |f y|)
    (g := fun _ => (1:ℝ)) (by simpa [sq_abs] using hf2) (by simp) (by simpa using hf.abs)
  simp only [mul_one, one_pow, sq_abs] at h
  have h1 : ∫ _y : ℝ, (1:ℝ) ∂unitμ = 1 := by simp
  rw [h1, Real.sqrt_one, mul_one] at h
  refine h.trans (le_of_eq ?_)
  have hnn : 0 ≤ ‖f‖ := norm_nonneg f
  rw [← Lp_norm_sq_eq_integral f, Real.sqrt_sq hnn]

/-- **The kernel operator on `L²`.** -/
noncomputable def kernelOp {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hΦb : ∀ p, |Φ p| ≤ C) :
    Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_kernelFun he hΦm hΦb f).toLp _
      map_add' := by
        intro f g
        refine Lp.ext ?_
        have h1 := (memLp_kernelFun he hΦm hΦb (f + g)).coeFn_toLp
        have h2 := (memLp_kernelFun he hΦm hΦb f).coeFn_toLp
        have h3 := (memLp_kernelFun he hΦm hΦb g).coeFn_toLp
        have hfg : kernelFun ν e Φ (⇑(f + g)) = kernelFun ν e Φ (⇑f + ⇑g) :=
          kernelFun_congr he Φ (Lp.coeFn_add f g)
        have hsplit : kernelFun ν e Φ (⇑f + ⇑g)
            = kernelFun ν e Φ ⇑f + kernelFun ν e Φ ⇑g := by
          funext y
          have hf : Integrable (fun x => f (e x) * Φ (x, y)) ν := by
            refine Integrable.mono' ((he.integrable_comp_of_integrable
              ((Lp.memLp f).integrable (by norm_num))).abs.const_mul C)
              ((((Lp.stronglyMeasurable f).measurable.comp he.measurable).mul
                (hΦm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
              (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hΦb (x, y)) (abs_nonneg _)
          have hg : Integrable (fun x => g (e x) * Φ (x, y)) ν := by
            refine Integrable.mono' ((he.integrable_comp_of_integrable
              ((Lp.memLp g).integrable (by norm_num))).abs.const_mul C)
              ((((Lp.stronglyMeasurable g).measurable.comp he.measurable).mul
                (hΦm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
              (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hΦb (x, y)) (abs_nonneg _)
          show ∫ x, (⇑f + ⇑g) (e x) * Φ (x, y) ∂ν
              = kernelFun ν e Φ ⇑f y + kernelFun ν e Φ ⇑g y
          have hadd : kernelFun ν e Φ ⇑f y + kernelFun ν e Φ ⇑g y
              = ∫ x, (f (e x) * Φ (x, y) + g (e x) * Φ (x, y)) ∂ν :=
            (integral_add hf hg).symm
          rw [hadd]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [Pi.add_apply]; ring)
        calc ⇑((memLp_kernelFun he hΦm hΦb (f + g)).toLp _)
            =ᵐ[unitμ] kernelFun ν e Φ (⇑(f + g)) := h1
          _ = kernelFun ν e Φ ⇑f + kernelFun ν e Φ ⇑g := by rw [hfg, hsplit]
          _ =ᵐ[unitμ] ⇑((memLp_kernelFun he hΦm hΦb f).toLp _)
              + ⇑((memLp_kernelFun he hΦm hΦb g).toLp _) := (h2.add h3).symm
          _ =ᵐ[unitμ] ⇑((memLp_kernelFun he hΦm hΦb f).toLp _
              + (memLp_kernelFun he hΦm hΦb g).toLp _) := (Lp.coeFn_add _ _).symm
      map_smul' := by
        intro c f
        refine Lp.ext ?_
        have h1 := (memLp_kernelFun he hΦm hΦb (c • f)).coeFn_toLp
        have h2 := (memLp_kernelFun he hΦm hΦb f).coeFn_toLp
        have hcf : kernelFun ν e Φ (⇑(c • f)) = kernelFun ν e Φ (c • ⇑f) :=
          kernelFun_congr he Φ (Lp.coeFn_smul c f)
        have hsplit : kernelFun ν e Φ (c • ⇑f) = c • kernelFun ν e Φ ⇑f := by
          funext y
          show ∫ x, (c • ⇑f) (e x) * Φ (x, y) ∂ν = c • ∫ x, f (e x) * Φ (x, y) ∂ν
          rw [smul_eq_mul, ← integral_const_mul]
          
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, smul_eq_mul]; ring)
        calc ⇑((memLp_kernelFun he hΦm hΦb (c • f)).toLp _)
            =ᵐ[unitμ] kernelFun ν e Φ (⇑(c • f)) := h1
          _ = c • kernelFun ν e Φ ⇑f := by rw [hcf, hsplit]
          _ =ᵐ[unitμ] c • ⇑((memLp_kernelFun he hΦm hΦb f).toLp _) := (h2.const_smul c).symm
          _ =ᵐ[unitμ] ⇑(c • (memLp_kernelFun he hΦm hΦb f).toLp _) := (Lp.coeFn_smul _ _).symm }
    C (fun f => by
      refine norm_le_of_sq_le (by positivity) ?_
      have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
      have hf : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
      have hcoe := (memLp_kernelFun he hΦm hΦb f).coeFn_toLp
      have hbound : ∀ᵐ y ∂unitμ,
          (((memLp_kernelFun he hΦm hΦb f).toLp _) y) ^ 2 ≤ (C * ‖f‖) ^ 2 := by
        filter_upwards [hcoe] with y hy
        rw [hy]
        have h1 : |kernelFun ν e Φ (⇑f) y| ≤ C * ‖f‖ :=
          (abs_kernelFun_le he hΦm hΦb hfm hf y).trans
            (mul_le_mul_of_nonneg_left (integral_abs_le_norm f) hC0)
        calc (kernelFun ν e Φ (⇑f) y) ^ 2 = |kernelFun ν e Φ (⇑f) y| ^ 2 := (sq_abs _).symm
          _ ≤ (C * ‖f‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc ∫ y, (((memLp_kernelFun he hΦm hΦb f).toLp _) y) ^ 2 ∂unitμ
          ≤ ∫ _y, (C * ‖f‖) ^ 2 ∂unitμ :=
            integral_mono_ae (Lp.memLp _).integrable_sq (integrable_const _) hbound
        _ = (C * ‖f‖) ^ 2 := by simp)

/-- The kernel operator on `L²` is computed by `kernelFun`. -/
theorem coeFn_kernelOp {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hΦb : ∀ p, |Φ p| ≤ C) (f : Lp ℝ 2 unitμ) :
    ⇑(kernelOp he hΦm hC0 hΦb f) =ᵐ[unitμ] kernelFun ν e Φ ⇑f :=
  (memLp_kernelFun he hΦm hΦb f).coeFn_toLp


/-- The operator norm is bounded by the `L²` norm of the kernel. -/
theorem norm_kernelOp_le {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hΦb : ∀ p, |Φ p| ≤ C) :
    ‖kernelOp he hΦm hC0 hΦb‖ ≤ Real.sqrt (∫ p, (Φ p) ^ 2 ∂(ν.prod unitμ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun f => ?_
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hf : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  have hf2 : Integrable (fun y => (f y) ^ 2) unitμ := (Lp.memLp f).integrable_sq
  refine norm_le_of_sq_le (by positivity) ?_
  have hcoe := coeFn_kernelOp he hΦm hC0 hΦb f
  have h1 : ∫ y, (kernelOp he hΦm hC0 hΦb f y) ^ 2 ∂unitμ
      = ∫ y, (kernelFun ν e Φ ⇑f y) ^ 2 ∂unitμ := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with y hy
    rw [hy]
  rw [h1]
  refine (integral_sq_kernelFun_le he hΦm hΦb hfm hf2 hf).trans ?_
  have hnn : 0 ≤ ∫ p, (Φ p) ^ 2 ∂(ν.prod unitμ) := integral_nonneg fun p => sq_nonneg _
  rw [mul_pow, Real.sq_sqrt hnn, Lp_norm_sq_eq_integral f]

/-- The kernel operator is additive in the kernel. -/
theorem kernelOp_sub {e : X → ℝ} (he : MeasurePreserving e ν unitμ) {Φ Ψ : X × ℝ → ℝ}
    (hΦm : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hΦb : ∀ p, |Φ p| ≤ C)
    (hΨm : Measurable Ψ) {D : ℝ} (hD0 : 0 ≤ D) (hΨb : ∀ p, |Ψ p| ≤ D)
    (hsm : Measurable fun p => Φ p - Ψ p) (hs0 : 0 ≤ C + D)
    (hsb : ∀ p, |Φ p - Ψ p| ≤ C + D) :
    kernelOp he hΦm hC0 hΦb - kernelOp he hΨm hD0 hΨb = kernelOp he hsm hs0 hsb := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  have h1 := coeFn_kernelOp he hΦm hC0 hΦb f
  have h2 := coeFn_kernelOp he hΨm hD0 hΨb f
  have h3 := coeFn_kernelOp he hsm hs0 hsb f
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hf : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  have hfe : Integrable (fun x => f (e x)) ν := he.integrable_comp_of_integrable hf
  have hint : ∀ (K : X × ℝ → ℝ), Measurable K → ∀ (M : ℝ), (∀ p, |K p| ≤ M) → ∀ y,
      Integrable (fun x => f (e x) * K (x, y)) ν := by
    intro K hK M hM y
    refine Integrable.mono' (hfe.abs.const_mul M)
      (((hfm.comp he.measurable).mul (hK.comp (measurable_id.prodMk measurable_const)))
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM (x, y)) (abs_nonneg _)
  have hpt : kernelFun ν e (fun p => Φ p - Ψ p) ⇑f
      = fun y => kernelFun ν e Φ ⇑f y - kernelFun ν e Ψ ⇑f y := by
    funext y
    have hsub : kernelFun ν e Φ ⇑f y - kernelFun ν e Ψ ⇑f y
        = ∫ x, (f (e x) * Φ (x, y) - f (e x) * Ψ (x, y)) ∂ν :=
      (integral_sub (hint Φ hΦm C hΦb y) (hint Ψ hΨm D hΨb y)).symm
    rw [hsub]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  calc ⇑(kernelOp he hΦm hC0 hΦb f - kernelOp he hΨm hD0 hΨb f)
      =ᵐ[unitμ] ⇑(kernelOp he hΦm hC0 hΦb f) - ⇑(kernelOp he hΨm hD0 hΨb f) := Lp.coeFn_sub _ _
    _ =ᵐ[unitμ] kernelFun ν e Φ ⇑f - kernelFun ν e Ψ ⇑f := h1.sub h2
    _ = kernelFun ν e (fun p => Φ p - Ψ p) ⇑f := by rw [hpt]; rfl
    _ =ᵐ[unitμ] ⇑(kernelOp he hsm hs0 hsb f) := h3.symm

/-- **The kernel operator of a finite sum of products is compact**: its range lies in the span of
finitely many functions. -/
theorem isCompactOperator_kernelOp_isProdSimple {e : X → ℝ} (he : MeasurePreserving e ν unitμ)
    {Ψ : X × ℝ → ℝ} (hΨ : IsProdSimple Ψ) (hΨm : Measurable Ψ) {D : ℝ} (hD0 : 0 ≤ D)
    (hΨb : ∀ p, |Ψ p| ≤ D) : IsCompactOperator (kernelOp he hΨm hD0 hΨb) := by
  classical
  obtain ⟨ι, hι, a, b, ham, hbm, hab, hbb, hΨeq⟩ := hΨ
  choose A hA using hab
  choose B hB using hbb
  -- the finitely many `L²` functions spanning the range
  have hBmem : ∀ i, MemLp (b i) 2 unitμ := fun i =>
    MemLp.of_bound (hbm i).aestronglyMeasurable (B i)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB i y)
  set Bi : ι → Lp ℝ 2 unitμ := fun i => (hBmem i).toLp (b i) with hBi
  set Λ : (ι → ℝ) → Lp ℝ 2 unitμ := fun c => ∑ i, c i • Bi i with hΛ
  have hΛcont : Continuous Λ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  set Box : Set (ι → ℝ) := Set.univ.pi fun i => Set.Icc (-(|A i|)) (|A i|) with hBox
  have hBoxc : IsCompact Box := isCompact_univ_pi fun i => isCompact_Icc
  have hSc : IsCompact (Λ '' Box) := hBoxc.image hΛcont
  refine ⟨Λ '' Box, hSc, Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) ?_⟩
  rintro f hf
  rw [Metric.mem_closedBall, dist_zero_right] at hf
  rw [Set.mem_preimage]
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hfi : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  have hfe : Integrable (fun x => f (e x)) ν := he.integrable_comp_of_integrable hfi
  have hmarg : ∫ x, |f (e x)| ∂ν = ∫ t, |f t| ∂unitμ := by
    have h := integral_map (μ := ν) (φ := e) he.measurable.aemeasurable (f := fun t => |f t|)
      (by rw [he.map_eq]; exact hfi.abs.aestronglyMeasurable)
    rw [he.map_eq] at h
    exact h.symm
  set c : ι → ℝ := fun i => ∫ x, f (e x) * a i x ∂ν with hc
  have hcbound : ∀ i, |c i| ≤ |A i| := by
    intro i
    have hint : Integrable (fun x => f (e x) * a i x) ν := by
      refine Integrable.mono' (hfe.abs.const_mul (|A i|))
        (((hfm.comp he.measurable).mul (ham i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hA i x).trans (le_abs_self _)) (abs_nonneg _)
    calc |c i| ≤ ∫ x, |f (e x) * a i x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, |A i| * |f (e x)| ∂ν := by
          refine integral_mono hint.abs (hfe.abs.const_mul _) fun x => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right ((hA i x).trans (le_abs_self _)) (abs_nonneg _)
      _ = |A i| * ∫ t, |f t| ∂unitμ := by rw [integral_const_mul, hmarg]
      _ ≤ |A i| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (integral_abs_le_norm f).trans hf
      _ = |A i| := mul_one _
  refine ⟨c, fun i _ => ⟨neg_le_of_abs_le (hcbound i), le_of_abs_le (hcbound i)⟩, ?_⟩
  -- the operator value equals `Λ c`
  refine (Lp.ext ?_).symm
  have hΛc : ⇑(Λ c) =ᵐ[unitμ] fun y => ∑ i, c i * b i y := by
    have h1 : ⇑(Λ c) =ᵐ[unitμ] fun y => ∑ i, (c i • Bi i) y := by
      rw [hΛ]
      exact (Lp.coeFn_finsetSum _ _).mono fun y hy => by rw [hy, Finset.sum_apply]
    refine h1.trans ?_
    have h2 : ∀ i, ⇑(c i • Bi i) =ᵐ[unitμ] fun y => c i * b i y := by
      intro i
      refine (Lp.coeFn_smul (c i) (Bi i)).trans ?_
      filter_upwards [(hBmem i).coeFn_toLp] with y hy
      simp only [Pi.smul_apply, smul_eq_mul, hBi]
      rw [hy]
    have h3 : ∀ᵐ y ∂unitμ, ∀ i, (c i • Bi i) y = c i * b i y := by
      rw [ae_all_iff]
      exact fun i => h2 i
    filter_upwards [h3] with y hy
    exact Finset.sum_congr rfl fun i _ => hy i
  have hKf : ⇑(kernelOp he hΨm hD0 hΨb f) =ᵐ[unitμ] fun y => ∑ i, c i * b i y := by
    refine (coeFn_kernelOp he hΨm hD0 hΨb f).trans ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have hint : ∀ i, Integrable (fun x => f (e x) * a i x * b i y) ν := by
      intro i
      refine Integrable.mono' (hfe.abs.const_mul (|A i| * |B i|))
        ((((hfm.comp he.measurable).mul (ham i))).aestronglyMeasurable.mul_const _)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |f (e x)| * |a i x| * |b i y| ≤ |f (e x)| * |A i| * |B i| := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left ((hA i x).trans (le_abs_self _))
              (abs_nonneg _)) ((hB i y).trans (le_abs_self _)) (abs_nonneg _) ?_
            exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
        _ = |A i| * |B i| * |f (e x)| := by ring
    show kernelFun ν e Ψ ⇑f y = _
    have hsplit : kernelFun ν e Ψ ⇑f y = ∫ x, ∑ i, f (e x) * a i x * b i y ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show f (e x) * Ψ (x, y) = ∑ i, f (e x) * a i x * b i y
      rw [hΨeq (x, y), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]
  exact hKf.trans hΛc.symm

/-- **Compactness of the kernel operator** (Hilbert–Schmidt). -/
theorem isCompactOperator_kernelOp {e : X → ℝ} (he : MeasurePreserving e ν unitμ)
    {Φ : X × ℝ → ℝ} (hΦm : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hΦb : ∀ p, |Φ p| ≤ C) :
    IsCompactOperator (kernelOp he hΦm hC0 hΦb) := by
  classical
  -- finite-rank approximations
  have happrox : ∀ n : ℕ, ∃ T : Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ, IsCompactOperator T ∧
      ‖kernelOp he hΦm hC0 hΦb - T‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨Ψ, hΨ, hΨε⟩ := exists_isProdSimple_approx (ν := ν) hΦm hΦb
      (ε := (1 / (n + 1 : ℝ)) ^ 2) (by positivity)
    obtain ⟨D, hD⟩ := hΨ.exists_bound
    have hD0 : 0 ≤ max D 0 := le_max_right _ _
    have hDb : ∀ p, |Ψ p| ≤ max D 0 := fun p => (hD p).trans (le_max_left _ _)
    have hΨm := hΨ.measurable
    refine ⟨kernelOp he hΨm hD0 hDb,
      isCompactOperator_kernelOp_isProdSimple he hΨ hΨm hD0 hDb, ?_⟩
    have hsm : Measurable fun p => Φ p - Ψ p := hΦm.sub hΨm
    have hs0 : 0 ≤ C + max D 0 := by positivity
    have hsb : ∀ p, |Φ p - Ψ p| ≤ C + max D 0 := fun p =>
      (abs_sub _ _).trans (add_le_add (hΦb p) (hDb p))
    rw [kernelOp_sub he hΦm hC0 hΦb hΨm hD0 hDb hsm hs0 hsb]
    refine (norm_kernelOp_le he hsm hs0 hsb).trans ?_
    have hle : ∫ p, (Φ p - Ψ p) ^ 2 ∂(ν.prod unitμ) ≤ (1 / (n + 1 : ℝ)) ^ 2 := hΨε.le
    calc Real.sqrt (∫ p, (Φ p - Ψ p) ^ 2 ∂(ν.prod unitμ))
        ≤ Real.sqrt ((1 / (n + 1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 1 / (n + 1 : ℝ) := Real.sqrt_sq (by positivity)
  choose T hTc hTle using happrox
  refine isCompactOperator_of_tendsto (l := Filter.atTop) (F := T) ?_
    (Filter.Eventually.of_forall hTc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [← norm_neg]
  simpa using hTle n


end UpperTailMultipodality
