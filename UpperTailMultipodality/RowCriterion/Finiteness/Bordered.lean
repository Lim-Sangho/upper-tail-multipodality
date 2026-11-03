import UpperTailMultipodality.RowCriterion.Finiteness.Positivity
import UpperTailMultipodality.RowCriterion.Finiteness.KernelOperator

/-!
# The bordered second variation is an isomorphism

At a global minimizer `u` of `ℱ_W` satisfying `eq:row-euler`, the linearisation of the
fixed-point form `u = σ(ℓ(q) + α + λ/2 + (1/2)∇𝒫_W(u))` of the Euler–Lagrange equation,
bordered by the mean constraint,

`(h, λ) ↦ (h - u(1-u)((1/2) D∇𝒫_W(u)[h] + λ/2), ∫h)`,

is a bounded isomorphism of `BddMeas × ℝ` (`borderedEquiv`), which is `lem:bordered`.
Injectivity is the strict positivity of the second variation on mean-zero functions
(`secondVariation_pos`); surjectivity is the Fredholm alternative on `L²` for the compact
operator `h ↦ u(1-u)(1/2) D∇𝒫_W(u)[h]`, a finite sum of the compact operators
`isCompactOperator_kernelOp` attached to the single graphs, followed by the observation that a
solution in `L²` is automatically bounded.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The multiplier `u(1-u) = σ'(σ⁻¹(u))` of the linearised Euler–Lagrange equation. -/
noncomputable def weight (u : BddMeas) : BddMeas := u * (1 - u)

/-- The value of `u(1-u)` at a point. -/
theorem weight_apply (u : BddMeas) (y : ℝ) : weight u y = u y * (1 - u y) := by
  rw [weight, BddMeas.mul_apply, BddMeas.sub_apply, BddMeas.one_apply]

/-- `u(1-u)` is positive for `u` in a compact subinterval of `(0,1)`. -/
theorem weight_pos {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (y : ℝ) : 0 < weight u y := by
  rw [weight_apply]
  have h1 := (hu y).1
  have h2 := (hu y).2
  have : 0 < 1 - u y := by linarith
  nlinarith

/-- `u(1-u)J_q''(u) = 1`. -/
theorem weight_mul_Jpp {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (y : ℝ) : weight u y * Jp'' (u y) = 1 := by
  rw [weight_apply, Jp'']
  have h := weight_pos hc hd hu y
  rw [weight_apply] at h
  rw [mul_one_div, div_self h.ne']
section SingleGraph

variable {H : SimpleGraph V} [DecidableRel H.Adj] {W : Graphon} {μ : ℝ}

/-! ### The linearised operator as an integral operator -/

variable (H W μ) in
/-- The kernel of the linearised operator attached to the triple `(v, z₀, i)`. -/
noncomputable def linKernel (u : BddMeas) (v : V) (z₀ i : Nbr H v) : ((V → ℝ) × ℝ) → ℝ :=
  fun p => if i = z₀ then 0 else
    weight u p.2 * (μ / 2) *
      ((∏ j ∈ Finset.univ.erase i,
          (Function.update (fun _ => u) z₀ (1 : BddMeas)) j (Function.update p.1 (z₀ : V) p.2 j))
        * avoidingProduct H W v (Function.update p.1 (z₀ : V) p.2))

/-- The kernel of the linearised operator is measurable. -/
theorem measurable_linKernel (u : BddMeas) (v : V) (z₀ i : Nbr H v) :
    Measurable (linKernel H W μ u v z₀ i) := by
  classical
  unfold linKernel
  refine Measurable.ite (by simp) measurable_const ?_
  have hupd : Measurable fun p : (V → ℝ) × ℝ => Function.update p.1 (z₀ : V) p.2 :=
    measurable_update_pair (z₀ : V)
  refine ((((weight u).measurable.comp measurable_snd)).mul measurable_const).mul ?_
  refine Measurable.mul ?_ ((measurable_avoidingProduct H W v).comp hupd)
  exact Finset.measurable_prod _ fun j _ =>
    ((Function.update (fun _ => u) z₀ (1 : BddMeas)) j).measurable.comp
      ((measurable_pi_apply (j : V)).comp hupd)

/-- The kernel of the linearised operator is bounded. -/
theorem abs_linKernel_le {u : BddMeas} (hu : UnitValued u) (v : V) (z₀ i : Nbr H v)
    (p : (V → ℝ) × ℝ) : |linKernel H W μ u v z₀ i p| ≤ |μ| / 2 := by
  classical
  unfold linKernel
  split_ifs with hi
  · simp only [abs_zero]
    positivity
  · have hslope : |weight u p.2| ≤ 1 := by
      rw [weight_apply, abs_mul]
      have h1 := hu p.2
      have h2 : |u p.2| ≤ 1 := by rw [abs_of_nonneg h1.1]; exact h1.2
      have h3 : |1 - u p.2| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [h1.2])]; linarith [h1.1]
      calc |u p.2| * |1 - u p.2| ≤ 1 * 1 := mul_le_mul h2 h3 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hP := avoidingProduct_mem_Icc H W v (Function.update p.1 (z₀ : V) p.2)
    have hprod : |(∏ j ∈ Finset.univ.erase i,
        (Function.update (fun _ => u) z₀ (1 : BddMeas)) j (Function.update p.1 (z₀ : V) p.2 j))
          * avoidingProduct H W v (Function.update p.1 (z₀ : V) p.2)| ≤ 1 := by
      rw [abs_mul]
      have h1 : |∏ j ∈ Finset.univ.erase i,
          (Function.update (fun _ => u) z₀ (1 : BddMeas)) j
            (Function.update p.1 (z₀ : V) p.2 j)| ≤ 1 := by
        rw [Finset.abs_prod]
        refine Finset.prod_le_one (fun j _ => abs_nonneg _) fun j _ => ?_
        have := unitValued_update_one hu z₀ j (Function.update p.1 (z₀ : V) p.2 j)
        rw [abs_of_nonneg this.1]
        exact this.2
      have h2 : |avoidingProduct H W v (Function.update p.1 (z₀ : V) p.2)| ≤ 1 := by
        rw [abs_of_nonneg hP.1]; exact hP.2
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [abs_mul, abs_mul]
    calc |weight u p.2| * |μ / 2| * _ ≤ 1 * (|μ| / 2) * 1 := by
          refine mul_le_mul (mul_le_mul hslope (le_of_eq ?_) (abs_nonneg _) zero_le_one) hprod
            (abs_nonneg _) (by positivity)
          rw [abs_div]
          norm_num
      _ = |μ| / 2 := by ring

variable (H W μ) in
/-- The linearised operator `h ↦ u(1-u)(μ/2)D∇ℛ_W(u)[h]`, acting on functions. -/
noncomputable def linFun (u : BddMeas) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => ∑ v, ∑ z₀ : Nbr H v, ∑ i : Nbr H v,
    kernelFun (Measure.pi fun _ : V => unitμ) (fun ξ => ξ (i : V))
      (linKernel H W μ u v z₀ i) f y

omit [DecidableEq V] in
/-- A coordinate of the product measure is uniform. -/
theorem measurePreserving_coord (i : V) :
    MeasurePreserving (fun ξ : V → ℝ => ξ i) (Measure.pi fun _ : V => unitμ) unitμ :=
  measurePreserving_eval (μ := fun _ : V => unitμ) i

/-- The linearised operator depends only on the almost everywhere class. -/
theorem linFun_congr (u : BddMeas) {f g : ℝ → ℝ} (hfg : f =ᵐ[unitμ] g) :
    linFun H W μ u f = linFun H W μ u g := by
  funext y
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z₀ _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [kernelFun_congr (measurePreserving_coord (i : V)) _ hfg]

/-- The linearised operator produces measurable functions. -/
theorem measurable_linFun (u : BddMeas) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (linFun H W μ u f) := by
  refine Finset.measurable_sum _ fun v _ => Finset.measurable_sum _ fun z₀ _ =>
    Finset.measurable_sum _ fun i _ => ?_
  exact measurable_kernelFun (measurable_pi_apply (i : V)) (measurable_linKernel u v z₀ i) hf

/-- The linearised operator is bounded in terms of the `L¹` norm. -/
theorem abs_linFun_le {u : BddMeas} (hu : UnitValued u) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f unitμ) (y : ℝ) :
    |linFun H W μ u f y| ≤ ∑ v : V, ∑ _z₀ : Nbr H v, ∑ _i : Nbr H v,
      |μ| / 2 * ∫ t, |f t| ∂unitμ := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z₀ _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact abs_kernelFun_le (measurePreserving_coord (i : V)) (measurable_linKernel u v z₀ i)
    (abs_linKernel_le hu v z₀ i) hfm hf y

/-- The linearised operator on functions agrees with `gradDeriv` on `BddMeas`. -/
theorem linFun_coe {u : BddMeas} (_hu : UnitValued u) (h : BddMeas) :
    linFun H W μ u ⇑h = ⇑(weight u * ((μ / 2) • gradDeriv H W u h)) := by
  classical
  funext y
  rw [BddMeas.mul_apply, BddMeas.smul_apply, gradDeriv_apply, BddMeas.sum_apply, Finset.mul_sum,
    Finset.mul_sum, linFun]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [BddMeas.sum_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z₀ _ => ?_
  rw [BddMeas.sum_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = z₀
  · subst hi
    have h0 : gradForm H W v i (Function.update (Function.update (fun _ => u) i 1) i
        (if (i : Nbr H v) = i then (0 : BddMeas) else h)) = 0 := by
      rw [if_pos rfl]
      exact (gradForm H W v i).map_update_zero _ _
    rw [h0, BddMeas.zero_apply, kernelFun]
    have hzero : ∀ ξ : V → ℝ, h (ξ (i : V)) * linKernel H W μ u v i i (ξ, y) = 0 := by
      intro ξ
      unfold linKernel
      rw [if_pos rfl, mul_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
    simp
  · rw [if_neg hi, kernelFun, gradForm_apply]
    have hpt : ∀ ξ : V → ℝ, h (ξ (i : V)) * linKernel H W μ u v z₀ i (ξ, y)
        = weight u y * (μ / 2 * formIntegrand H W v
            (Function.update (Function.update (fun _ => u) z₀ 1) i h)
            (Function.update ξ (z₀ : V) y)) := by
      intro ξ
      have hiz : (Function.update ξ (z₀ : V) y) (i : V) = ξ (i : V) :=
        Function.update_of_ne (fun hc => hi (Subtype.ext hc)) _ _
      have hker : linKernel H W μ u v z₀ i (ξ, y)
          = weight u y * (μ / 2) * ((∏ j ∈ Finset.univ.erase i,
              (Function.update (fun _ => u) z₀ (1 : BddMeas)) j (Function.update ξ (z₀ : V) y j))
            * avoidingProduct H W v (Function.update ξ (z₀ : V) y)) := by
        unfold linKernel
        rw [if_neg hi]
      rw [hker, formIntegrand_update, hiz]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_const_mul]


/-! ### The `L²` realisation -/

/-- A bounded measurable function lies in `L²`. -/
theorem memLp_bddMeas (b : BddMeas) : MemLp (⇑b) 2 unitμ :=
  MemLp.of_bound b.measurable.aestronglyMeasurable ‖b‖
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact b.abs_apply_le_norm y)

/-- A bounded measurable function as an element of `L²`. -/
noncomputable def toL2 (b : BddMeas) : Lp ℝ 2 unitμ := (memLp_bddMeas b).toLp ⇑b

/-- The `L²` class of a bounded measurable function is represented by it. -/
theorem coeFn_toL2 (b : BddMeas) : ⇑(toL2 b) =ᵐ[unitμ] ⇑b := (memLp_bddMeas b).coeFn_toLp

/-- The integral as a continuous linear functional on `L²`. -/
noncomputable def integL2 : Lp ℝ 2 unitμ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ y, f y ∂unitμ
      map_add' := fun f g => by
        have h1 : ∫ y, (f + g) y ∂unitμ = ∫ y, (f y + g y) ∂unitμ :=
          integral_congr_ae ((Lp.coeFn_add f g).mono fun y hy => by rw [hy]; rfl)
        rw [h1, integral_add ((Lp.memLp f).integrable (by norm_num))
          ((Lp.memLp g).integrable (by norm_num))]
      map_smul' := fun c f => by
        have h1 : ∫ y, (c • f) y ∂unitμ = ∫ y, c * f y ∂unitμ :=
          integral_congr_ae ((Lp.coeFn_smul c f).mono fun y hy => by rw [hy]; rfl)
        rw [h1, integral_const_mul]
        rfl } 1
    (fun f => by
      show ‖∫ y, f y ∂unitμ‖ ≤ 1 * ‖f‖
      rw [Real.norm_eq_abs, one_mul]
      exact (abs_integral_le_integral_abs).trans (integral_abs_le_norm f))

/-- The value of the integral functional on `L²`. -/
theorem integL2_apply (f : Lp ℝ 2 unitμ) : integL2 f = ∫ y, f y ∂unitμ := rfl

/-- The integral of a bounded measurable function, computed in `L²`. -/
theorem integL2_toL2 (b : BddMeas) : integL2 (toL2 b) = BddMeas.integ b := by
  rw [integL2_apply, BddMeas.integ_apply]
  exact integral_congr_ae (coeFn_toL2 b)

/-- A finite sum of compact operators is compact. -/
theorem isCompactOperator_finsetSum {ι : Type*} (s : Finset ι)
    (T : ι → (Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ)) (h : ∀ i ∈ s, IsCompactOperator (T i)) :
    IsCompactOperator (⇑(∑ i ∈ s, T i) : Lp ℝ 2 unitμ → Lp ℝ 2 unitμ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isCompactOperator_zero (M₁ := Lp ℝ 2 unitμ) (M₂ := Lp ℝ 2 unitμ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hco : ⇑(T a + ∑ x ∈ s, T x)
        = (⇑(T a) : Lp ℝ 2 unitμ → Lp ℝ 2 unitμ) + ⇑(∑ x ∈ s, T x) := rfl
    rw [hco]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The value of a finite sum of operators, computed pointwise. -/
theorem coeFn_sum_apply {ι : Type*} [Fintype ι] (T : ι → (Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ))
    (f : Lp ℝ 2 unitμ) (g : ι → ℝ → ℝ) (h : ∀ i, ⇑(T i f) =ᵐ[unitμ] g i) :
    ⇑((∑ i, T i) f) =ᵐ[unitμ] fun y => ∑ i, g i y := by
  have h1 : (∑ i, T i) f = ∑ i, T i f := by rw [_root_.sum_apply]
  rw [h1]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h2 : ∀ᵐ y ∂unitμ, ∀ i, (T i f) y = g i y := by
    rw [ae_all_iff]; exact h
  filter_upwards [h2] with y hy
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hy i

variable (H W μ) in
/-- The linearised operator on `L²`. -/
noncomputable def linOpL2 (u : BddMeas) (hu : UnitValued u) :
    Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ :=
  ∑ v : V, ∑ z₀ : Nbr H v, ∑ i : Nbr H v,
    kernelOp (measurePreserving_coord (i : V))
      (measurable_linKernel (H := H) (W := W) (μ := μ) u v z₀ i)
      (by positivity : (0:ℝ) ≤ |μ| / 2) (abs_linKernel_le (H := H) (W := W) (μ := μ) hu v z₀ i)

/-- The linearised operator is compact on `L²`. -/
theorem isCompactOperator_linOpL2 (u : BddMeas) (hu : UnitValued u) :
    IsCompactOperator (linOpL2 H W μ u hu) := by
  rw [linOpL2]
  refine isCompactOperator_finsetSum _ _ fun v _ => ?_
  refine isCompactOperator_finsetSum _ _ fun z₀ _ => ?_
  refine isCompactOperator_finsetSum _ _ fun i _ => ?_
  exact isCompactOperator_kernelOp _ _ _ _

/-- The `L²` linearised operator is computed by `linFun`. -/
theorem coeFn_linOpL2 (u : BddMeas) (hu : UnitValued u) (f : Lp ℝ 2 unitμ) :
    ⇑(linOpL2 H W μ u hu f) =ᵐ[unitμ] linFun H W μ u ⇑f := by
  rw [linOpL2]
  refine coeFn_sum_apply _ f
    (fun v : V => fun y : ℝ => ∑ z₀ : Nbr H v, ∑ j : Nbr H v,
      kernelFun (Measure.pi fun _ : V => unitμ) (fun ξ : V → ℝ => ξ (j : V))
        (linKernel H W μ u v z₀ j) (⇑f) y) fun v => ?_
  refine coeFn_sum_apply _ f
    (fun z₀ : Nbr H v => fun y : ℝ => ∑ j : Nbr H v,
      kernelFun (Measure.pi fun _ : V => unitμ) (fun ξ : V → ℝ => ξ (j : V))
        (linKernel H W μ u v z₀ j) (⇑f) y) fun z₀ => ?_
  refine coeFn_sum_apply _ f
    (fun j : Nbr H v => fun y : ℝ =>
      kernelFun (Measure.pi fun _ : V => unitμ) (fun ξ : V → ℝ => ξ (j : V))
        (linKernel H W μ u v z₀ j) (⇑f) y) fun j => ?_
  exact coeFn_kernelOp _ _ _ _ f


end SingleGraph

/-! ### The bordered operator of a family -/

section Family

variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {W : Graphon} {q α : ℝ} {μ : ι → ℝ}

variable (Hs W μ) in
/-- The bordered linearisation `(h, λ) ↦ (h - u(1-u)((1/2)D∇𝒫_W(u)[h] + λ/2), ∫h)`. -/
noncomputable def borderedOp (u : BddMeas) : (BddMeas × ℝ) →L[ℝ] (BddMeas × ℝ) :=
  ((ContinuousLinearMap.fst ℝ BddMeas ℝ)
      - (BddMeas.mulLeftCLM (weight u)).comp
          (((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u).comp
              (ContinuousLinearMap.fst ℝ BddMeas ℝ)
            + (ContinuousLinearMap.snd ℝ BddMeas ℝ).smulRight ((1 / 2 : ℝ) • (1 : BddMeas)))).prod
    (BddMeas.integ.comp (ContinuousLinearMap.fst ℝ BddMeas ℝ))

/-- The value of the bordered operator. -/
theorem borderedOp_apply (u : BddMeas) (h : BddMeas) (lam : ℝ) :
    borderedOp Hs W μ u (h, lam)
      = (h - weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u h + (lam / 2) • (1 : BddMeas)),
        BddMeas.integ h) := by
  rw [borderedOp]
  simp only [ContinuousLinearMap.prod_apply, _root_.sub_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply, BddMeas.mulLeftCLM_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
    Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  have hsm : lam • ((1 / 2 : ℝ) • (1 : BddMeas)) = (lam / 2) • (1 : BddMeas) := by
    rw [smul_smul]
    congr 1
    ring
  rw [hsm]

/-- The pointwise Euler–Lagrange form of a bordered kernel element. -/
theorem el_of_borderedOp_eq_zero {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) {h : BddMeas} {lam : ℝ}
    (hker : borderedOp Hs W μ u (h, lam) = 0) (y : ℝ) :
    2 * Jp'' (u y) * h y - combinedGradDeriv Hs W μ u h y = lam := by
  have h1 : h - weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u h
      + (lam / 2) • (1 : BddMeas)) = 0 := by
    have := congrArg Prod.fst hker
    rw [borderedOp_apply] at this
    exact this
  have h2 := congrArg (fun f : BddMeas => f y) h1
  simp only [BddMeas.sub_apply, BddMeas.mul_apply, BddMeas.add_apply, BddMeas.smul_apply,
    BddMeas.one_apply, BddMeas.zero_apply] at h2
  have hs := weight_mul_Jpp hc hd hu y
  have hspos := weight_pos hc hd hu y
  have hval : h y
      = weight u y * (1 / 2 * combinedGradDeriv Hs W μ u h y + lam / 2 * 1) := by linarith
  rw [hval]
  have : 2 * Jp'' (u y) * (weight u y * (1 / 2 * combinedGradDeriv Hs W μ u h y + lam / 2 * 1))
      = (weight u y * Jp'' (u y)) * (combinedGradDeriv Hs W μ u h y + lam) := by ring
  rw [this, hs]
  ring

/-! ### The linearised operator of a family -/

variable (Hs W μ) in
/-- The linearised operator `h ↦ u(1-u)(1/2)D∇𝒫_W(u)[h]`, acting on functions. -/
noncomputable def combinedLinFun (u : BddMeas) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => ∑ j, linFun (Hs j) W (μ j) u f y

/-- The linearised operator depends only on the almost everywhere class. -/
theorem combinedLinFun_congr (u : BddMeas) {f g : ℝ → ℝ} (hfg : f =ᵐ[unitμ] g) :
    combinedLinFun Hs W μ u f = combinedLinFun Hs W μ u g := by
  funext y
  exact Finset.sum_congr rfl fun _j _ => congrFun (linFun_congr u hfg) y

/-- The linearised operator produces measurable functions. -/
theorem measurable_combinedLinFun (u : BddMeas) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (combinedLinFun Hs W μ u f) :=
  Finset.measurable_sum _ fun _j _ => measurable_linFun u hf

/-- The linearised operator is bounded in terms of the `L¹` norm. -/
theorem abs_combinedLinFun_le {u : BddMeas} (hu : UnitValued u) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : Integrable f unitμ) (y : ℝ) :
    |combinedLinFun Hs W μ u f y|
      ≤ ∑ j, ∑ _v : V, ∑ _z₀ : Nbr (Hs j) _v, ∑ _i : Nbr (Hs j) _v,
          |μ j| / 2 * ∫ t, |f t| ∂unitμ :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun _j _ => abs_linFun_le hu hfm hf y)

/-- The linearised operator on functions agrees with `combinedGradDeriv` on `BddMeas`. -/
theorem combinedLinFun_coe {u : BddMeas} (hu : UnitValued u) (h : BddMeas) :
    combinedLinFun Hs W μ u ⇑h
      = ⇑(weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u h)) := by
  funext y
  have hj : ∀ j : ι, linFun (Hs j) W (μ j) u ⇑h y
      = weight u y * (μ j / 2 * gradDeriv (Hs j) W u h y) := by
    intro j
    have hc := congrFun (linFun_coe hu h (H := Hs j) (W := W) (μ := μ j)) y
    rw [hc]
    show (weight u * ((μ j / 2) • gradDeriv (Hs j) W u h)) y = _
    rw [BddMeas.mul_apply, BddMeas.smul_apply]
  show ∑ j, linFun (Hs j) W (μ j) u ⇑h y = _
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hj j, BddMeas.mul_apply,
    BddMeas.smul_apply, combinedGradDeriv, _root_.sum_apply, BddMeas.sum_apply, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.smul_apply, BddMeas.smul_apply]
  ring

variable (Hs W μ) in
/-- The linearised operator of the family on `L²`, a finite sum of compact operators. -/
noncomputable def combinedLinOpL2 (u : BddMeas) (hu : UnitValued u) :
    Lp ℝ 2 unitμ →L[ℝ] Lp ℝ 2 unitμ :=
  ∑ j, linOpL2 (Hs j) W (μ j) u hu

/-- The linearised operator of the family is compact on `L²`. -/
theorem isCompactOperator_combinedLinOpL2 (u : BddMeas) (hu : UnitValued u) :
    IsCompactOperator (combinedLinOpL2 Hs W μ u hu) := by
  rw [combinedLinOpL2]
  exact isCompactOperator_finsetSum _ _ fun j _ => isCompactOperator_linOpL2 u hu

/-- The `L²` linearised operator of the family is computed by `combinedLinFun`. -/
theorem coeFn_combinedLinOpL2 (u : BddMeas) (hu : UnitValued u) (f : Lp ℝ 2 unitμ) :
    ⇑(combinedLinOpL2 Hs W μ u hu f) =ᵐ[unitμ] combinedLinFun Hs W μ u ⇑f := by
  rw [combinedLinOpL2]
  exact coeFn_sum_apply _ f (fun j => linFun (Hs j) W (μ j) u ⇑f)
    fun j => coeFn_linOpL2 u hu f

/-! ### Bijectivity -/

variable (Hs W μ) in
/-- The compact part of the bordered operator, on `L² × ℝ`. -/
noncomputable def compactPart (u : BddMeas) (hu : UnitValued u) :
    (Lp ℝ 2 unitμ × ℝ) →L[ℝ] (Lp ℝ 2 unitμ × ℝ) :=
  (((combinedLinOpL2 Hs W μ u hu).comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ))
      + (ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ).smulRight
          (toL2 ((1 / 2 : ℝ) • weight u))).prod
    (ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ
      - integL2.comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ))

/-- The value of the compact part of the bordered operator. -/
theorem compactPart_apply (u : BddMeas) (hu : UnitValued u) (f : Lp ℝ 2 unitμ) (lam : ℝ) :
    compactPart Hs W μ u hu (f, lam)
      = (combinedLinOpL2 Hs W μ u hu f + lam • toL2 ((1 / 2 : ℝ) • weight u), lam - integL2 f) := rfl

/-- The bordered operator on `L²` as `1` minus a compact operator. -/
theorem id_sub_compactPart_apply (u : BddMeas) (hu : UnitValued u) (f : Lp ℝ 2 unitμ)
    (lam : ℝ) :
    ((1 : (Lp ℝ 2 unitμ × ℝ) →L[ℝ] (Lp ℝ 2 unitμ × ℝ)) - compactPart Hs W μ u hu) (f, lam)
      = (f - combinedLinOpL2 Hs W μ u hu f - lam • toL2 ((1 / 2 : ℝ) • weight u), integL2 f) := by
  rw [_root_.sub_apply, compactPart_apply, one_apply_eq_self, Prod.mk_sub_mk]
  refine Prod.ext ?_ ?_
  · simp only
    abel
  · simp only
    abel

/-- The compact part of the bordered operator is compact. -/
theorem isCompactOperator_compactPart (u : BddMeas) (hu : UnitValued u) :
    IsCompactOperator (compactPart Hs W μ u hu) := by
  have h1 : IsCompactOperator
      (⇑((combinedLinOpL2 Hs W μ u hu).comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ))) :=
    (isCompactOperator_combinedLinOpL2 u hu).comp_clm _
  have hsnd : IsCompactOperator (⇑(ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have h2 : IsCompactOperator
      (⇑((ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ).smulRight
        (toL2 ((1 / 2 : ℝ) • weight u)))) := by
    have := hsnd.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (toL2 ((1 / 2 : ℝ) • weight u)))
    exact this
  have h3 : IsCompactOperator
      (⇑(ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ
        - integL2.comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ))) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have hA : IsCompactOperator (⇑((combinedLinOpL2 Hs W μ u hu).comp
      (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ)
      + (ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ).smulRight
        (toL2 ((1 / 2 : ℝ) • weight u)))) := h1.add h2
  have hfun : ⇑(compactPart Hs W μ u hu)
      = fun x => ContinuousLinearMap.inl ℝ (Lp ℝ 2 unitμ) ℝ
          (((combinedLinOpL2 Hs W μ u hu).comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ)
            + (ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ).smulRight
              (toL2 ((1 / 2 : ℝ) • weight u))) x)
        + ContinuousLinearMap.inr ℝ (Lp ℝ 2 unitμ) ℝ
          ((ContinuousLinearMap.snd ℝ (Lp ℝ 2 unitμ) ℝ
            - integL2.comp (ContinuousLinearMap.fst ℝ (Lp ℝ 2 unitμ) ℝ)) x) := by
    funext x
    refine Prod.ext ?_ ?_ <;> simp [compactPart]
  rw [hfun]
  exact (hA.clm_comp _).add (h3.clm_comp _)

/-- From a solution of the bordered equation in `L²` one obtains a bounded solution. -/
theorem exists_bdd_solution {u : BddMeas} (hu : UnitValued u) (g : BddMeas)
    (f : Lp ℝ 2 unitμ) (lam : ℝ)
    (hf : f - combinedLinOpL2 Hs W μ u hu f - lam • toL2 ((1 / 2 : ℝ) • weight u) = toL2 g) :
    ∃ b : BddMeas, ⇑f =ᵐ[unitμ] ⇑b ∧ borderedOp Hs W μ u (b, lam) = (g, integL2 f) := by
  classical
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hfi : Integrable (⇑f) unitμ := (Lp.memLp f).integrable (by norm_num)
  -- the bounded representative
  set M : ℝ := ∑ j, ∑ _v : V, ∑ _z₀ : Nbr (Hs j) _v, ∑ _i : Nbr (Hs j) _v,
    |μ j| / 2 * ∫ t, |f t| ∂unitμ with hM
  set F : ℝ → ℝ := fun y => g y + combinedLinFun Hs W μ u ⇑f y + lam / 2 * weight u y with hF
  have hFm : Measurable F := by
    refine (g.measurable.add (measurable_combinedLinFun (Hs := Hs) (W := W) (μ := μ) u hfm)).add ?_
    exact ((weight u).measurable.const_mul _)
  have hFb : ∀ y, |F y| ≤ ‖g‖ + M + |lam| / 2 * ‖weight u‖ := by
    intro y
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (g.abs_apply_le_norm y)
        (abs_combinedLinFun_le (Hs := Hs) (W := W) (μ := μ) hu hfm hfi y))) ?_)
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left ((weight u).abs_apply_le_norm y) (by positivity)
  set b : BddMeas := BddMeas.mk F hFm _ hFb with hb
  have hbval : ∀ y, b y = g y + combinedLinFun Hs W μ u ⇑f y + lam / 2 * weight u y := fun y => rfl
  -- `f` and `b` agree almost everywhere
  have hfeq : f = combinedLinOpL2 Hs W μ u hu f + lam • toL2 ((1 / 2 : ℝ) • weight u) + toL2 g := by
    rw [← hf]; abel
  have hfb : ⇑f =ᵐ[unitμ] ⇑b := by
    conv_lhs => rw [hfeq]
    have h1 := Lp.coeFn_add (combinedLinOpL2 Hs W μ u hu f + lam • toL2 ((1 / 2 : ℝ) • weight u)) (toL2 g)
    have h2 := Lp.coeFn_add (combinedLinOpL2 Hs W μ u hu f) (lam • toL2 ((1 / 2 : ℝ) • weight u))
    have h3 := coeFn_combinedLinOpL2 (Hs := Hs) (W := W) (μ := μ) u hu f
    have h4 := Lp.coeFn_smul lam (toL2 ((1 / 2 : ℝ) • weight u))
    have h5 := coeFn_toL2 ((1 / 2 : ℝ) • weight u)
    have h6 := coeFn_toL2 g
    filter_upwards [h1, h2, h3, h4, h5, h6] with y hy1 hy2 hy3 hy4 hy5 hy6
    rw [hy1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy2 hy4 ⊢
    rw [hy2, hy3, hy4, hy5, hy6, hbval]
    simp only [BddMeas.smul_apply]
    ring
  refine ⟨b, hfb, ?_⟩
  -- the bordered equation
  have hlin : combinedLinFun Hs W μ u ⇑f = ⇑(weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b)) := by
    rw [combinedLinFun_congr (Hs := Hs) (W := W) (μ := μ) u hfb]
    exact combinedLinFun_coe hu b
  have hfirst : b - weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b + (lam / 2) • (1 : BddMeas)) = g := by
    ext y
    have hy := hbval y
    have hy2 : combinedLinFun Hs W μ u ⇑f y = (weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b)) y := by
      rw [hlin]
    simp only [BddMeas.sub_apply, BddMeas.mul_apply, BddMeas.add_apply, BddMeas.smul_apply,
      BddMeas.one_apply]
    rw [hy, hy2, BddMeas.mul_apply, BddMeas.smul_apply]
    ring
  have hsecond : BddMeas.integ b = integL2 f := by
    rw [BddMeas.integ_apply, integL2_apply]
    exact (integral_congr_ae hfb).symm
  rw [borderedOp_apply, hfirst, hsecond]


/-- **Injectivity of the bordered operator**: a kernel element is a mean-zero solution of the
linearised Euler–Lagrange equation, which vanishes by `secondVariation_pos`. -/
theorem borderedOp_injective {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    Function.Injective (borderedOp Hs W μ u) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨h, lam⟩ hker
  have hUV : UnitValued u := fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩
  have hELh := el_of_borderedOp_eq_zero hc hd hu hker
  have hmean : BddMeas.integ h = 0 := by
    have h2 := congrArg Prod.snd hker
    rw [borderedOp_apply] at h2
    exact h2
  -- the second variation vanishes
  have hA : Integrable (fun y => Jp'' (u y) * h y ^ 2) unitμ := integrable_Jpp_mul_sq hc hd hu h
  have hB : Integrable (fun y => (combinedGradDeriv Hs W μ u h) y * h y) unitμ :=
    (combinedGradDeriv Hs W μ u h * h).integrable
  have hQ : secondVariation Hs W μ u h = lam * BddMeas.integ h := by
    rw [secondVariation]
    have e0 : ∀ y, 2 * (Jp'' (u y) * h y ^ 2) - (combinedGradDeriv Hs W μ u h) y * h y
        = lam * h y := by
      intro y
      linear_combination (h y) * hELh y
    have hcoe : BddMeas.integ (combinedGradDeriv Hs W μ u h * h)
        = ∫ y, (combinedGradDeriv Hs W μ u h) y * h y ∂unitμ := rfl
    rw [hcoe]
    have hsplit : ∫ y, (2 * (Jp'' (u y) * h y ^ 2)
          - (combinedGradDeriv Hs W μ u h) y * h y) ∂unitμ
        = 2 * (∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ)
          - ∫ y, (combinedGradDeriv Hs W μ u h) y * h y ∂unitμ := by
      rw [integral_sub (hA.const_mul 2) hB, integral_const_mul]
    have hlam : ∫ y, (2 * (Jp'' (u y) * h y ^ 2)
          - (combinedGradDeriv Hs W μ u h) y * h y) ∂unitμ
        = lam * BddMeas.integ h := by
      rw [integral_congr_ae (Filter.Eventually.of_forall e0), BddMeas.integ_apply,
        integral_const_mul]
    rw [← hsplit, hlam]
  -- hence `h` vanishes almost everywhere
  have hzero : ⇑h =ᵐ[unitμ] 0 := by
    by_contra hne
    have hpos := secondVariation_pos hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL hmean hne
    rw [hQ, hmean, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  have hint0 : ∫ t, |h t| ∂unitμ = 0 := by
    rw [← integral_zero ℝ ℝ (μ := unitμ)]
    refine integral_congr_ae ?_
    filter_upwards [hzero] with t ht
    simp only [Pi.zero_apply] at ht
    simp [ht]
  have hgrad : ∀ y, combinedGradDeriv Hs W μ u h y = 0 := by
    intro y
    have h1 := abs_combinedGradDeriv_apply_le (Hs := Hs) (W := W) hμ hUV h y
    rw [hint0, mul_zero] at h1
    exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
  have hy : ∀ y, 2 * Jp'' (u y) * h y = lam := by
    intro y
    have := hELh y
    rw [hgrad y, sub_zero] at this
    exact this
  have hlam0 : lam = 0 := by
    have hint : ∫ y, (2 * Jp'' (u y) * h y) ∂unitμ = ∫ _y : ℝ, lam ∂unitμ :=
      integral_congr_ae (Filter.Eventually.of_forall hy)
    have hzero2 : ∫ y, (2 * Jp'' (u y) * h y) ∂unitμ = 0 := by
      rw [← integral_zero ℝ ℝ (μ := unitμ)]
      refine integral_congr_ae ?_
      filter_upwards [hzero] with y hy'
      simp only [Pi.zero_apply] at hy'
      simp [hy']
    rw [hzero2, integral_const] at hint
    simpa using hint.symm
  have hh : h = 0 := by
    ext y
    have h1 := hy y
    have hJ := (Jp''_mem_of_mem_Icc hc hd (hu y)).1
    rw [hlam0] at h1
    rw [BddMeas.zero_apply]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (by positivity)
    · exact h2
  rw [Prod.mk_eq_zero]
  exact ⟨hh, hlam0⟩

/-- **Surjectivity of the bordered operator**, from the Fredholm alternative on `L²`. -/
theorem borderedOp_surjective {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    Function.Surjective (borderedOp Hs W μ u) := by
  have hUV : UnitValued u := fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩
  have hinj := borderedOp_injective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL
  -- the `L²` operator `1 - compactPart` is injective
  have hinjL2 : Function.Injective
      ((1 : (Lp ℝ 2 unitμ × ℝ) →L[ℝ] (Lp ℝ 2 unitμ × ℝ)) - compactPart Hs W μ u hUV) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨f, lam⟩ hf
    rw [id_sub_compactPart_apply] at hf
    have hf1 : f - combinedLinOpL2 Hs W μ u hUV f - lam • toL2 ((1 / 2 : ℝ) • weight u) = toL2 0 := by
      have := congrArg Prod.fst hf
      simp only at this
      rw [this]
      refine (Lp.ext ?_).symm
      filter_upwards [coeFn_toL2 (0 : BddMeas)] with y hy
      rw [hy]
      simp
    have hf2 : integL2 f = 0 := by
      have := congrArg Prod.snd hf
      simpa using this
    obtain ⟨b, hb1, hb2⟩ := exists_bdd_solution hUV 0 f lam hf1
    rw [hf2] at hb2
    have hb0 : (b, lam) = 0 := hinj (by rw [hb2, map_zero]; exact Prod.mk_zero_zero)
    have hb : b = 0 := (Prod.mk_eq_zero.mp hb0).1
    have hlam : lam = 0 := (Prod.mk_eq_zero.mp hb0).2
    have hfz : f = 0 := by
      refine Lp.ext ?_
      filter_upwards [hb1, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := unitμ)] with y hy hy0
      rw [hy, hy0, hb]
      rfl
    rw [Prod.mk_eq_zero]
    exact ⟨hfz, hlam⟩
  -- the Fredholm alternative
  have hcompact := isCompactOperator_compactPart (Hs := Hs) (W := W) (μ := μ) u hUV
  have hfred := hcompact.hasEigenvalue_or_mem_resolventSet (μ := (1:ℝ)) one_ne_zero
  have hunit : IsUnit ((1 : (Lp ℝ 2 unitμ × ℝ) →L[ℝ] (Lp ℝ 2 unitμ × ℝ))
      - compactPart Hs W μ u hUV) := by
    rcases hfred with heig | hres
    · exfalso
      obtain ⟨x, hx⟩ := heig.exists_hasEigenvector
      have hx0 : x ≠ 0 := hx.2
      have hxe : compactPart Hs W μ u hUV x = x := by
        have := Module.End.mem_eigenspace_iff.mp hx.1
        simpa using this
      have hx1 : ((1 : (Lp ℝ 2 unitμ × ℝ) →L[ℝ] (Lp ℝ 2 unitμ × ℝ))
          - compactPart Hs W μ u hUV) x = 0 := by
        rw [_root_.sub_apply, one_apply_eq_self, hxe, sub_self]
      exact hx0 (hinjL2 (by rw [hx1, map_zero]))
    · rw [spectrum.mem_resolventSet_iff] at hres
      simpa using hres
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  rintro ⟨g, β⟩
  obtain ⟨⟨f, lam⟩, hflam⟩ := hbij.2 (toL2 g, β)
  rw [id_sub_compactPart_apply] at hflam
  have hf1 : f - combinedLinOpL2 Hs W μ u hUV f - lam • toL2 ((1 / 2 : ℝ) • weight u) = toL2 g :=
    congrArg Prod.fst hflam
  have hf2 : integL2 f = β := congrArg Prod.snd hflam
  obtain ⟨b, -, hb2⟩ := exists_bdd_solution hUV g f lam hf1
  exact ⟨(b, lam), by rw [hb2, hf2]⟩

variable (Hs W μ) in
/-- **`lem:bordered`**: the bordered second variation is a bounded isomorphism of
`BddMeas × ℝ`. -/
noncomputable def borderedEquiv {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    (BddMeas × ℝ) ≃L[ℝ] (BddMeas × ℝ) :=
  ContinuousLinearEquiv.ofBijective (borderedOp Hs W μ u)
    (LinearMap.ker_eq_bot.mpr (borderedOp_injective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin
      hEL))
    (LinearMap.range_eq_top.mpr (borderedOp_surjective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin
      hEL))

/-- The bordered isomorphism is the bordered operator. -/
theorem coe_borderedEquiv {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    ((borderedEquiv Hs W μ hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL :
      (BddMeas × ℝ) →L[ℝ] (BddMeas × ℝ))) = borderedOp Hs W μ u := rfl


end Family

end UpperTailMultipodality
