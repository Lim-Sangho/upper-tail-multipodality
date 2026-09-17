import UpperTailMultipodality.Preliminaries.Calculus.Resampling

/-!
# Integrals of products of affine families

For bounded measurable functions `g`, `k_e` and `u_{e,i}` on a finite measure space, the map

`s ↦ ∫ g ∏_{e ∈ A} (k_e + ∑ᵢ sᵢ u_{e,i})`

is a polynomial in `s ∈ ℝⁿ`.  This file proves that it is analytic
(`analyticOnNhd_integral_mul_prod_affine`) and computes its derivative at `s = 0`
(`hasFDerivAt_integral_mul_prod_affine`):

`∑ᵢ (∑_{e ∈ A} ∫ g u_{e,i} ∏_{e' ∈ A ∖ {e}} k_{e'}) • projᵢ`.

Both follow by induction on `A` from the one-step expansion
`integral_mul_prod_insert_affine`, generalizing over the weight `g`.  Applied to the edge
factors of kernels, these give the analyticity and the first variation of `t(H,·)`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {ι : Type*} [DecidableEq ι] {n : ℕ} {k : ι → α → ℝ} {u : ι → Fin n → α → ℝ}

omit [DecidableEq ι] in
/-- The product `∏_{e ∈ A} (k_e + ∑ᵢ sᵢ u_{e,i})` is bounded and measurable for each `s`. -/
theorem isBddMeas_prod_affine (hk : ∀ e, IsBddMeas (k e)) (hu : ∀ e i, IsBddMeas (u e i))
    (A : Finset ι) (s : Fin n → ℝ) :
    IsBddMeas fun x => ∏ e ∈ A, (k e x + ∑ i, s i * u e i x) :=
  IsBddMeas.finset_prod A fun e _ =>
    (hk e).add (IsBddMeas.finset_sum _ fun i _ => (hu e i).const_mul (s i))

/-- **One step of the expansion.**  Splitting off the factor of `e ∉ A`:
`∫ g ∏_{insert e A} = ∫ (g k_e) ∏_A + ∑ᵢ sᵢ ∫ (g u_{e,i}) ∏_A`. -/
theorem integral_mul_prod_insert_affine (hk : ∀ e, IsBddMeas (k e))
    (hu : ∀ e i, IsBddMeas (u e i)) {g : α → ℝ} (hg : IsBddMeas g) {A : Finset ι} {e : ι}
    (he : e ∉ A) (s : Fin n → ℝ) :
    ∫ x, g x * ∏ e' ∈ insert e A, (k e' x + ∑ i, s i * u e' i x) ∂μ
      = ∫ x, (g x * k e x) * ∏ e' ∈ A, (k e' x + ∑ i, s i * u e' i x) ∂μ
        + ∑ i, s i * ∫ x, (g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x) ∂μ := by
  have hP := isBddMeas_prod_affine hk hu A s
  have hpt : ∀ x, g x * ∏ e' ∈ insert e A, (k e' x + ∑ i, s i * u e' i x)
      = (g x * k e x) * ∏ e' ∈ A, (k e' x + ∑ i, s i * u e' i x)
        + ∑ i, s i * ((g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x)) := by
    intro x
    rw [Finset.prod_insert he, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  have hint0 : Integrable (fun x => (g x * k e x) * ∏ e' ∈ A, (k e' x + ∑ i, s i * u e' i x)) μ :=
    ((hg.mul (hk e)).mul hP).integrable
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => s i * ((g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x))) μ :=
    fun i _ => (((hg.mul (hu e i)).mul hP).const_mul (s i)).integrable
  rw [integral_add hint0 (integrable_finsetSum _ hint), integral_finsetSum _ hint]
  simp_rw [integral_const_mul]

/-- **Analyticity.**  `s ↦ ∫ g ∏_{e ∈ A} (k_e + ∑ᵢ sᵢ u_{e,i})` is analytic on `ℝⁿ`. -/
theorem analyticOnNhd_integral_mul_prod_affine (hk : ∀ e, IsBddMeas (k e))
    (hu : ∀ e i, IsBddMeas (u e i)) (A : Finset ι) :
    ∀ g : α → ℝ, IsBddMeas g → AnalyticOnNhd ℝ
      (fun s : Fin n → ℝ => ∫ x, g x * ∏ e ∈ A, (k e x + ∑ i, s i * u e i x) ∂μ) Set.univ := by
  induction A using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.prod_empty, mul_one]
    exact analyticOnNhd_const
  | insert e A he ih =>
    intro g hg
    have hfun : (fun s : Fin n → ℝ => ∫ x, g x * ∏ e' ∈ insert e A,
          (k e' x + ∑ i, s i * u e' i x) ∂μ)
        = (fun s => ∫ x, (g x * k e x) * ∏ e' ∈ A, (k e' x + ∑ i, s i * u e' i x) ∂μ)
          + ∑ i, fun s => s i
            * ∫ x, (g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x) ∂μ := by
      funext s
      rw [integral_mul_prod_insert_affine hk hu hg he s, Pi.add_apply, Finset.sum_apply]
    rw [hfun]
    refine (ih _ (hg.mul (hk e))).add (Finset.analyticOnNhd_sum _ fun i _ => ?_)
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticOnNhd
      Set.univ).mul (ih _ (hg.mul (hu e i)))

/-- **The derivative at `0`.**  `s ↦ ∫ g ∏_{e ∈ A} (k_e + ∑ᵢ sᵢ u_{e,i})` has Fréchet derivative
`∑ᵢ (∑_{e ∈ A} ∫ g u_{e,i} ∏_{e' ∈ A ∖ {e}} k_{e'}) • projᵢ` at `s = 0`. -/
theorem hasFDerivAt_integral_mul_prod_affine (hk : ∀ e, IsBddMeas (k e))
    (hu : ∀ e i, IsBddMeas (u e i)) (A : Finset ι) :
    ∀ g : α → ℝ, IsBddMeas g → HasFDerivAt
      (fun s : Fin n → ℝ => ∫ x, g x * ∏ e ∈ A, (k e x + ∑ i, s i * u e i x) ∂μ)
      (∑ i, (∑ e ∈ A, ∫ x, g x * u e i x * ∏ e' ∈ A.erase e, k e' x ∂μ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) 0 := by
  induction A using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.prod_empty, mul_one, Finset.sum_empty, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const _ _
  | insert e A he ih =>
    intro g hg
    have hfun : (fun s : Fin n → ℝ => ∫ x, g x * ∏ e' ∈ insert e A,
          (k e' x + ∑ i, s i * u e' i x) ∂μ)
        = fun s => ∫ x, (g x * k e x) * ∏ e' ∈ A, (k e' x + ∑ i, s i * u e' i x) ∂μ
          + ∑ i, s i
            * ∫ x, (g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x) ∂μ := by
      funext s
      exact integral_mul_prod_insert_affine hk hu hg he s
    rw [hfun]
    have h0 := ih _ (hg.mul (hk e))
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt
        (fun s : Fin n → ℝ => s i
          * ∫ x, (g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, s j * u e' j x) ∂μ)
        ((0 : Fin n → ℝ) i • (∑ j, (∑ e' ∈ A, ∫ x, (g x * u e i x) * u e' j x
            * ∏ e'' ∈ A.erase e', k e'' x ∂μ) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
          + (∫ x, (g x * u e i x) * ∏ e' ∈ A, (k e' x + ∑ j, (0 : Fin n → ℝ) j * u e' j x) ∂μ)
            • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) 0 :=
      fun i _ => (hasFDerivAt_apply i (0 : Fin n → ℝ)).mul (ih _ (hg.mul (hu e i)))
    refine (h0.fun_add (HasFDerivAt.fun_sum hi)).congr_fderiv ?_
    -- identify the coefficients
    have hcoef : ∀ i, (∑ e' ∈ A, ∫ x, (g x * k e x) * u e' i x * ∏ e'' ∈ A.erase e', k e'' x ∂μ)
        + ∫ x, (g x * u e i x) * ∏ e' ∈ A, k e' x ∂μ
        = ∑ e' ∈ insert e A, ∫ x, g x * u e' i x * ∏ e'' ∈ (insert e A).erase e', k e'' x ∂μ := by
      intro i
      rw [Finset.sum_insert he, Finset.erase_insert he, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun e' he' => ?_
        have hne : e' ≠ e := fun h => he (h ▸ he')
        have hnotin : e ∉ A.erase e' := fun h => he (Finset.mem_of_mem_erase h)
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert hnotin]
        ring
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.zero_apply, zero_mul, zero_add, Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcoef i]
    ring

end UpperTailMultipodality
