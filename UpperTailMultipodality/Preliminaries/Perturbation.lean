import UpperTailMultipodality.Preliminaries.RootedDensity

/-!
# Perturbations of graphons in bounded symmetric directions

The paper differentiates `t(H,·)` and `I_p` in the Banach space `L^∞_sym([0,1]²)`.  The Lean
development only needs these derivatives along finitely many bounded directions, which this file
provides:

* `Kernel.lincomb K U s = K + ∑ᵢ sᵢ Uᵢ`;
* `analyticOnNhd_tDensity_lincomb` — `s ↦ t(H, K + ∑ᵢ sᵢUᵢ)` is a polynomial, hence analytic;
* `hasFDerivAt_tDensity_lincomb` — its derivative at `s = 0` for a graphon `K = W` is
  `s ↦ ∑ᵢ sᵢ ∫∫ 𝒟_W Uᵢ` (`eq:first-variation`);
* `Kernel.Ip`, `Kernel.edgeDensity` and `hasDerivAt_Ip_line` — the first variation of `I_p` at a
  graphon with values in a compact subinterval of `(0,1)`;
* `Kernel.toGraphon` and `Graphon.clamp` — kernels with values in `[0,1]` are graphons, and a
  graphon with almost everywhere bounds has a representative with pointwise bounds.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Kernel

/-- The kernel `K + ∑ᵢ sᵢ Uᵢ`. -/
noncomputable def lincomb {n : ℕ} (K : Kernel) (U : Fin n → Kernel) (s : Fin n → ℝ) : Kernel where
  toFun x y := K.toFun x y + ∑ i, s i * (U i).toFun x y
  symm' x y := by simp only [K.symm' x y, fun i => (U i).symm' x y]
  meas' := K.meas'.add (Finset.measurable_sum _ fun i _ => (U i).meas'.const_mul (s i))
  bdd' := by
    obtain ⟨C, hC⟩ := K.bdd'
    choose D hD using fun i => (U i).bdd'
    refine ⟨C + ∑ i, |s i| * D i, fun x y => ?_⟩
    calc |K.toFun x y + ∑ i, s i * (U i).toFun x y|
        ≤ |K.toFun x y| + ∑ i, |s i * (U i).toFun x y| :=
          (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ C + ∑ i, |s i| * D i := by
          refine add_le_add (hC x y) (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD i x y) (abs_nonneg _)

@[simp] theorem lincomb_apply {n : ℕ} (K : Kernel) (U : Fin n → Kernel) (s : Fin n → ℝ)
    (x y : ℝ) : (K.lincomb U s).toFun x y = K.toFun x y + ∑ i, s i * (U i).toFun x y := rfl

/-- The edge density `∫∫ K` of a kernel. -/
noncomputable def edgeDensity (K : Kernel) : ℝ := ∫ z, K.toFun z.1 z.2 ∂gμ

/-- The relative entropy `∫∫ J_p(K)` of a kernel. -/
noncomputable def Ip (K : Kernel) (p : ℝ) : ℝ := ∫ z, Jp p (K.toFun z.1 z.2) ∂gμ

/-- A kernel with values in `[0,1]`, regarded as a graphon. -/
def toGraphon (K : Kernel) (h0 : ∀ x y, 0 ≤ K.toFun x y) (h1 : ∀ x y, K.toFun x y ≤ 1) :
    Graphon where
  toFun := K.toFun
  symm' := K.symm'
  meas' := K.meas'
  nonneg' := h0
  le_one' := h1

/-- The edge factor of `K + ∑ᵢ sᵢUᵢ` is `K_e + ∑ᵢ sᵢ (Uᵢ)_e`. -/
theorem edgeVal_lincomb {V : Type*} {n : ℕ} (K : Kernel) (U : Fin n → Kernel) (s : Fin n → ℝ)
    (x : V → ℝ) (e : Sym2 V) :
    edgeVal (K.lincomb U s).toFun (K.lincomb U s).symm' x e
      = edgeVal K.toFun K.symm' x e + ∑ i, s i * edgeVal (U i).toFun (U i).symm' x e := by
  induction e using Sym2.ind with
  | _ a b => rfl

/-- `t(H, K + ∑ᵢ sᵢUᵢ)` as the integral of a product of affine functions of `s`. -/
theorem tDensity_lincomb_eq (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ} (K : Kernel)
    (U : Fin n → Kernel) (s : Fin n → ℝ) :
    (K.lincomb U s).tDensity H
      = ∫ x, (fun _ => (1:ℝ)) x * ∏ e ∈ H.edgeFinset,
          (edgeVal K.toFun K.symm' x e + ∑ i, s i * edgeVal (U i).toFun (U i).symm' x e)
          ∂(Measure.pi fun _ => unitμ) := by
  unfold tDensity
  simp only [one_mul]
  exact integral_congr_ae (ae_of_all _ fun x =>
    Finset.prod_congr rfl fun e _ => edgeVal_lincomb K U s x e)

end Kernel

/-- **`t(H, K + ∑ᵢ sᵢUᵢ)` is a polynomial in `s`.** -/
theorem analyticOnNhd_tDensity_lincomb (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ}
    (K : Kernel) (U : Fin n → Kernel) :
    AnalyticOnNhd ℝ (fun s : Fin n → ℝ => (K.lincomb U s).tDensity H) Set.univ := by
  rw [funext (Kernel.tDensity_lincomb_eq H K U)]
  exact analyticOnNhd_integral_mul_prod_affine (fun e => isBddMeas_edgeVal K e)
    (fun e i => isBddMeas_edgeVal (U i) e) H.edgeFinset _ (IsBddMeas.const 1)

/-- **The first variation of `t(H,·)` at a graphon along finitely many directions.** -/
theorem hasFDerivAt_tDensity_lincomb (H : SimpleGraph V) [DecidableRel H.Adj] {n : ℕ}
    (W : Graphon) (U : Fin n → Kernel) :
    HasFDerivAt (fun s : Fin n → ℝ => ((Kernel.ofGraphon W).lincomb U s).tDensity H)
      (∑ i, (∫ z, derivKernel H W z.1 z.2 * (U i).toFun z.1 z.2 ∂gμ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) 0 := by
  rw [funext (Kernel.tDensity_lincomb_eq H (Kernel.ofGraphon W) U)]
  refine (hasFDerivAt_integral_mul_prod_affine (fun e => isBddMeas_edgeVal _ e)
    (fun e i => isBddMeas_edgeVal (U i) e) H.edgeFinset _ (IsBddMeas.const 1)).congr_fderiv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_derivKernel_mul]
  simp only [one_mul]
  rfl

/-- **The first variation of `I_p`.**  If `a ≤ W ≤ b` almost everywhere with `0 < a` and
`b < 1`, then `ξ ↦ I_p(W + ξU)` has derivative `∫∫ J_p'(W) U` at `ξ = 0`. -/
theorem hasDerivAt_Ip_line (W : Graphon) (U : Kernel) {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : b < 1) (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b) :
    HasDerivAt (fun ξ : ℝ => (Kernel.ofGraphon W + ξ • U).Ip p)
      (∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ) 0 := by
  obtain ⟨C, hC⟩ := U.bdd'
  obtain ⟨D, hD, hDpos⟩ : ∃ D : ℝ, D = |C| + 1 ∧ 0 < D := ⟨_, rfl, by positivity⟩
  have hUD : ∀ x y, |U.toFun x y| ≤ D := fun x y => by
    rw [hD]; linarith [hC x y, le_abs_self C]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min a (1 - b) / (2 * D) := ⟨_, rfl⟩
  have hmin : 0 < min a (1 - b) := lt_min ha (by linarith)
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- the window `[a/2, (1+b)/2]` and a bound for `J_p'` on it
  have hwin : ∀ z : ℝ × ℝ, W.toFun z.1 z.2 ∈ Set.Icc a b → ∀ ξ ∈ Metric.ball (0:ℝ) δ,
      W.toFun z.1 z.2 + ξ * U.toFun z.1 z.2 ∈ Set.Icc (a / 2) ((1 + b) / 2) := by
    intro z hz ξ hξ
    have hξ' : |ξ| < δ := by simpa [Real.dist_eq] using hξ
    have hprod : |ξ * U.toFun z.1 z.2| ≤ min a (1 - b) / 2 := by
      rw [abs_mul]
      calc |ξ| * |U.toFun z.1 z.2| ≤ δ * D :=
            mul_le_mul hξ'.le (hUD _ _) (abs_nonneg _) hδpos.le
        _ = min a (1 - b) / 2 := by rw [hδ]; field_simp
    have h1 := min_le_left a (1 - b)
    have h2 := min_le_right a (1 - b)
    have h3 := abs_le.mp hprod
    constructor <;> linarith [hz.1, hz.2, h3.1, h3.2]
  have hwin01 : ∀ w ∈ Set.Icc (a / 2) ((1 + b) / 2), 0 < w ∧ w < 1 := fun w hw =>
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hcont : ContinuousOn (Jp' p) (Set.Icc (a / 2) ((1 + b) / 2)) := fun w hw =>
    (hasDerivAt_Jp' hp0 hp1 (hwin01 w hw).1 (hwin01 w hw).2).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmeasJp' : Measurable (Jp' p) := by
    unfold Jp'
    fun_prop
  have hWU : ∀ ξ : ℝ, Measurable fun z : ℝ × ℝ => W.toFun z.1 z.2 + ξ * U.toFun z.1 z.2 :=
    fun ξ => W.measurable_uncurry.add (U.meas'.const_mul ξ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gμ)
    (F := fun ξ (z : ℝ × ℝ) => Jp p (W.toFun z.1 z.2 + ξ * U.toFun z.1 z.2))
    (F' := fun ξ (z : ℝ × ℝ) => Jp' p (W.toFun z.1 z.2 + ξ * U.toFun z.1 z.2) * U.toFun z.1 z.2)
    (x₀ := 0) (bound := fun _ => M * D) (Metric.ball_mem_nhds 0 hδpos)
    (Filter.Eventually.of_forall fun ξ => ((measurable_Jp p).comp (hWU ξ)).aestronglyMeasurable)
    (by
      simp only [zero_mul, add_zero]
      exact W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1))
    ((hmeasJp'.comp (hWU 0)).mul U.meas').aestronglyMeasurable
    (by
      filter_upwards [hW] with z hz ξ hξ
      rw [Real.norm_eq_abs, abs_mul]
      have hM' := hM _ (hwin z hz ξ hξ)
      rw [Real.norm_eq_abs] at hM'
      exact mul_le_mul hM' (hUD _ _) (abs_nonneg _) ((abs_nonneg _).trans hM'))
    (integrable_const _)
    (by
      filter_upwards [hW] with z hz ξ hξ
      have hw := hwin01 _ (hwin z hz ξ hξ)
      have hlin : HasDerivAt (fun ξ : ℝ => W.toFun z.1 z.2 + ξ * U.toFun z.1 z.2)
          (U.toFun z.1 z.2) ξ := by
        simpa using ((hasDerivAt_id ξ).mul_const (U.toFun z.1 z.2)).const_add (W.toFun z.1 z.2)
      exact (hasDerivAt_Jp hp0 hp1 hw.1 hw.2).comp ξ hlin)
  have h2 := key.2
  simp only [zero_mul, add_zero] at h2
  exact h2

/-- **Clamping.**  A graphon with `a ≤ W ≤ b` almost everywhere agrees almost everywhere with
a graphon whose values lie in `[a,b]` everywhere. -/
theorem Graphon.exists_clamp (W : Graphon) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b) :
    ∃ W' : Graphon, (∀ x y, W'.toFun x y ∈ Set.Icc a b) ∧
      ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun z.1 z.2 := by
  refine ⟨{ toFun := fun x y => max a (min b (W.toFun x y))
            symm' := fun x y => by rw [W.symm']
            meas' := measurable_const.max (measurable_const.min W.meas')
            nonneg' := fun x y => le_max_of_le_left ha
            le_one' := fun x y => max_le (hab.trans hb) ((min_le_left _ _).trans hb) },
    fun x y => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
  filter_upwards [hW] with z hz
  show max a (min b (W.toFun z.1 z.2)) = W.toFun z.1 z.2
  rw [min_eq_right hz.2, max_eq_right hz.1]

end UpperTailMultipodality
