import UpperTailMultipodality.Preliminaries.Graphons.Basic

/-!
# The Banach algebra of bounded measurable functions

The proof of `lem:row-finite` applies an implicit function theorem in a Banach space of bounded
functions on `[0,1]`.  We use the space `BddMeas` of bounded measurable functions `ℝ → ℝ` with
the supremum norm, realised as the subalgebra of measurable elements of `ℓ^∞(ℝ)`.  Evaluation
at a point is a continuous algebra homomorphism, so pointwise identities pass to limits and to
power series; in particular the logistic function `σ(t) = 1/(1+e^{-t})` acts on `BddMeas`
pointwise and analytically (`BddMeas.sigma`).

Almost everywhere questions are handled separately: the integral `BddMeas.integ` against `unitμ`
is a continuous linear functional.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The measurable elements of `ℓ^∞(ℝ)`. -/
noncomputable def measurableSubalgebra : Subalgebra ℝ (lp (fun _ : ℝ => ℝ) ∞) where
  carrier := {f | Measurable (f : ℝ → ℝ)}
  mul_mem' := by
    intro a b ha hb
    change Measurable (⇑(a * b) : ℝ → ℝ)
    rw [lp.infty_coeFn_mul]
    exact Measurable.mul ha hb
  add_mem' := by
    intro a b ha hb
    change Measurable (⇑(a + b) : ℝ → ℝ)
    rw [lp.coeFn_add]
    exact Measurable.add ha hb
  algebraMap_mem' := by
    intro r
    change Measurable (⇑(algebraMap ℝ (lp (fun _ : ℝ => ℝ) ∞) r) : ℝ → ℝ)
    rw [Algebra.algebraMap_eq_smul_one, lp.coeFn_smul, lp.infty_coeFn_one]
    exact measurable_one.const_smul r

/-- **Bounded measurable functions** `ℝ → ℝ` with the supremum norm. -/
def BddMeas : Type := ↥measurableSubalgebra

namespace BddMeas

noncomputable instance : NormedCommRing BddMeas :=
  inferInstanceAs (NormedCommRing ↥measurableSubalgebra)

noncomputable instance : NormedAlgebra ℝ BddMeas :=
  inferInstanceAs (NormedAlgebra ℝ ↥measurableSubalgebra)

/-- The underlying element of `ℓ^∞(ℝ)`. -/
def val (u : BddMeas) : lp (fun _ : ℝ => ℝ) ∞ := Subtype.val (p := (· ∈ measurableSubalgebra)) u

/-- The underlying `ℓ^∞` element determines the function. -/
theorem val_injective : Function.Injective val := fun _ _ h => Subtype.ext h

instance : FunLike BddMeas ℝ ℝ where
  coe u := ⇑(val u)
  coe_injective _ _ h := val_injective (lp.ext h)

/-- The coercion to a function goes through the underlying `ℓ^∞` element. -/
theorem coe_def (u : BddMeas) : ⇑u = ⇑(val u) := rfl

@[ext] theorem ext {u v : BddMeas} (h : ∀ y, u y = v y) : u = v :=
  DFunLike.ext u v h

/-- Elements of `BddMeas` are measurable. -/
theorem measurable (u : BddMeas) : Measurable u := (show ↥measurableSubalgebra from u).2

@[simp] theorem coe_add (u v : BddMeas) : ⇑(u + v) = ⇑u + ⇑v := rfl
@[simp] theorem coe_sub (u v : BddMeas) : ⇑(u - v) = ⇑u - ⇑v := rfl
@[simp] theorem coe_neg (u : BddMeas) : ⇑(-u) = -⇑u := rfl
@[simp] theorem coe_zero : ⇑(0 : BddMeas) = 0 := rfl
@[simp] theorem coe_mul (u v : BddMeas) : ⇑(u * v) = ⇑u * ⇑v := rfl
@[simp] theorem coe_smul (c : ℝ) (u : BddMeas) : ⇑(c • u) = c • ⇑u := rfl
@[simp] theorem coe_one : ⇑(1 : BddMeas) = 1 := rfl

/-- Addition is pointwise. -/
theorem add_apply (u v : BddMeas) (y : ℝ) : (u + v) y = u y + v y := rfl
/-- Subtraction is pointwise. -/
theorem sub_apply (u v : BddMeas) (y : ℝ) : (u - v) y = u y - v y := rfl
/-- Negation is pointwise. -/
theorem neg_apply (u : BddMeas) (y : ℝ) : (-u) y = -u y := rfl
/-- The zero element is the zero function. -/
theorem zero_apply (y : ℝ) : (0 : BddMeas) y = 0 := rfl
/-- Multiplication is pointwise. -/
theorem mul_apply (u v : BddMeas) (y : ℝ) : (u * v) y = u y * v y := rfl
/-- Scalar multiplication is pointwise. -/
theorem smul_apply (c : ℝ) (u : BddMeas) (y : ℝ) : (c • u) y = c * u y := rfl
/-- The unit is the constant function `1`. -/
theorem one_apply (y : ℝ) : (1 : BddMeas) y = 1 := rfl

@[simp] theorem coe_algebraMap (c : ℝ) : ⇑(algebraMap ℝ BddMeas c) = fun _ => c := by
  rw [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one]
  funext y; simp

/-- A finite sum is computed pointwise. -/
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → BddMeas) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coe_add, ih]

/-- The value of a finite sum at a point. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → BddMeas) (y : ℝ) :
    (∑ i ∈ s, f i) y = ∑ i ∈ s, f i y := by
  rw [coe_sum, Finset.sum_apply]

/-- The norm is the supremum norm of the underlying `ℓ^∞` element. -/
theorem norm_def (u : BddMeas) : ‖u‖ = ‖val u‖ := rfl

/-- Pointwise values are bounded by the norm. -/
theorem abs_apply_le_norm (u : BddMeas) (y : ℝ) : |u y| ≤ ‖u‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero (val u) y
  rw [Real.norm_eq_abs] at this
  exact this

/-- A pointwise bound bounds the norm. -/
theorem norm_le_of_forall {u : BddMeas} {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, |u y| ≤ C) : ‖u‖ ≤ C := by
  rw [norm_def]
  exact lp.norm_le_of_forall_le hC fun y => by rw [Real.norm_eq_abs]; exact h y

/-- Pointwise differences are bounded by the distance. -/
theorem abs_apply_sub_le_dist (u v : BddMeas) (y : ℝ) : |u y - v y| ≤ ‖u - v‖ := by
  simpa using abs_apply_le_norm (u - v) y

/-- Build an element of `BddMeas` from a bounded measurable function. -/
noncomputable def mk (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) : BddMeas :=
  ⟨⟨f, memℓp_infty ⟨C, by
    rintro _ ⟨y, rfl⟩
    simpa [Real.norm_eq_abs] using hC y⟩⟩, hf⟩

@[simp] theorem coe_mk (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    ⇑(mk f hf C hC) = f := rfl

/-- The value of `BddMeas.mk` at a point. -/
theorem mk_apply (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) (y : ℝ) :
    mk f hf C hC y = f y := rfl

/-- Every element is bounded. -/
theorem exists_bound (u : BddMeas) : ∃ C, ∀ y, |u y| ≤ C := ⟨‖u‖, abs_apply_le_norm u⟩

/-- The measurable elements form a closed subset of `ℓ^∞(ℝ)`. -/
theorem isClosed_measurableSubalgebra :
    IsClosed (measurableSubalgebra : Set (lp (fun _ : ℝ => ℝ) ∞)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨g, hg, hgf⟩ := mem_closure_iff_seq_limit.mp hf
  change Measurable (f : ℝ → ℝ)
  refine measurable_of_tendsto_metrizable (f := fun n => ((g n : lp (fun _ : ℝ => ℝ) ∞) : ℝ → ℝ))
    (fun n => hg n) ?_
  rw [tendsto_pi_nhds]
  intro y
  have hev : Continuous fun F : lp (fun _ : ℝ => ℝ) ∞ => F y := by
    refine continuous_iff_continuousAt.mpr fun F => ?_
    refine Metric.continuousAt_iff.mpr fun ε hε => ⟨ε, hε, fun {G} hG => ?_⟩
    have h1 := lp.norm_apply_le_norm ENNReal.top_ne_zero (G - F) y
    rw [dist_eq_norm] at hG ⊢
    exact lt_of_le_of_lt (by simpa using h1) hG
  exact (hev.tendsto f).comp hgf

instance : CompleteSpace BddMeas :=
  haveI := isClosed_measurableSubalgebra.completeSpace_coe
  inferInstanceAs (CompleteSpace ↥measurableSubalgebra)

/-- Evaluation at a point, as a ring homomorphism. -/
noncomputable def evalRingHom (y : ℝ) : BddMeas →+* ℝ where
  toFun u := u y
  map_one' := one_apply y
  map_mul' u v := mul_apply u v y
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evalRingHom_apply (y : ℝ) (u : BddMeas) : evalRingHom y u = u y := rfl

/-- Evaluation at a point is continuous. -/
theorem continuous_eval (y : ℝ) : Continuous fun u : BddMeas => u y := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  refine Metric.continuousAt_iff.mpr fun ε hε => ⟨ε, hε, fun {v} hv => ?_⟩
  rw [dist_eq_norm] at hv
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_apply_sub_le_dist v u y) hv

/-- Evaluation at a point, as a continuous linear functional. -/
noncomputable def evalCLM (y : ℝ) : BddMeas →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => u y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun u => by
      show ‖u y‖ ≤ 1 * ‖u‖
      rw [Real.norm_eq_abs, one_mul]; exact abs_apply_le_norm u y)

@[simp] theorem evalCLM_apply (y : ℝ) (u : BddMeas) : evalCLM y u = u y := rfl

/-- Elements of `BddMeas` are integrable against `unitμ`. -/
theorem integrable (u : BddMeas) : Integrable u unitμ :=
  integrable_of_abs_le u.measurable ‖u‖ (abs_apply_le_norm u)

/-- The integral against `unitμ`, as a continuous linear functional of norm at most one. -/
noncomputable def integ : BddMeas →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ y, u y ∂unitμ
      map_add' := fun u v => integral_add u.integrable v.integrable
      map_smul' := fun c u => integral_const_mul c _ } 1
    (fun u => by
      show ‖∫ y, u y ∂unitμ‖ ≤ 1 * ‖u‖
      rw [Real.norm_eq_abs, one_mul]
      calc |∫ y, u y ∂unitμ| ≤ ∫ y, |u y| ∂unitμ := abs_integral_le_integral_abs
        _ ≤ ∫ _y, ‖u‖ ∂unitμ :=
            integral_mono u.integrable.abs (integrable_const _) (abs_apply_le_norm u)
        _ = ‖u‖ := by simp)

/-- The value of the integral functional. -/
theorem integ_apply (u : BddMeas) : integ u = ∫ y, u y ∂unitμ := rfl

/-- A measurable function bounded by one in absolute value, e.g. a row. -/
noncomputable def ofRow {u : ℝ → ℝ} (hm : Measurable u) (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) :
    BddMeas :=
  mk u hm 1 fun y => by
    rw [abs_le]; exact ⟨by linarith [(hu y).1], (hu y).2⟩

@[simp] theorem coe_ofRow {u : ℝ → ℝ} (hm : Measurable u) (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) :
    ⇑(ofRow hm hu) = u := rfl

/-- Composition with a measurable function that is bounded on the range. -/
noncomputable def comp (g : ℝ → ℝ) (hg : Measurable g) (u : BddMeas) (C : ℝ)
    (hC : ∀ y, |g (u y)| ≤ C) : BddMeas :=
  mk (fun y => g (u y)) (hg.comp u.measurable) C hC

@[simp] theorem coe_comp (g : ℝ → ℝ) (hg : Measurable g) (u : BddMeas) (C : ℝ)
    (hC : ∀ y, |g (u y)| ≤ C) : ⇑(comp g hg u C hC) = fun y => g (u y) := rfl

/-- The positive part. -/
noncomputable def posPart (u : BddMeas) : BddMeas :=
  mk (fun y => max (u y) 0) (u.measurable.max measurable_const) ‖u‖ fun y => by
    have h := abs_apply_le_norm u y
    rw [abs_le] at h ⊢
    constructor <;> [linarith [le_max_right (u y) 0]; exact max_le h.2 (by linarith [h.1])]

/-- The negative part. -/
noncomputable def negPart (u : BddMeas) : BddMeas := posPart (-u)

/-- The value of the positive part at a point. -/
theorem posPart_apply (u : BddMeas) (y : ℝ) : posPart u y = max (u y) 0 := rfl

/-- The value of the negative part at a point. -/
theorem negPart_apply (u : BddMeas) (y : ℝ) : negPart u y = max (-u y) 0 := rfl

/-- A function is the difference of its positive and negative parts. -/
theorem posPart_sub_negPart (u : BddMeas) : posPart u - negPart u = u := by
  ext y
  rw [sub_apply, posPart_apply, negPart_apply]
  rcases le_total (u y) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- The positive and negative parts have disjoint supports. -/
theorem posPart_mul_negPart (u : BddMeas) : posPart u * negPart u = 0 := by
  ext y
  rw [mul_apply, posPart_apply, negPart_apply, zero_apply]
  rcases le_total (u y) 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_right (by linarith : -u y ≤ 0)]; ring

/-- The positive part is nonnegative. -/
theorem posPart_nonneg (u : BddMeas) (y : ℝ) : 0 ≤ posPart u y := le_max_right _ _

/-- The negative part is nonnegative. -/
theorem negPart_nonneg (u : BddMeas) (y : ℝ) : 0 ≤ negPart u y := le_max_right _ _

/-! ### The logistic function acting on `BddMeas` -/

/-- `1 + exp(-w)` is invertible in `BddMeas`. -/
theorem isUnit_one_add_exp_neg (w : BddMeas) : IsUnit (1 + NormedSpace.exp (-w)) := by
  -- the pointwise inverse
  have hexp : ∀ y, (1 + NormedSpace.exp (-w)) y = 1 + Real.exp (-w y) := by
    intro y
    have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (evalRingHom y) (continuous_eval y) (-w)
      ((NormedSpace.expSeries_radius_eq_top ℝ BddMeas).symm ▸ edist_lt_top _ _)
    rw [add_apply, one_apply]
    congr 1
    simpa [Real.exp_eq_exp_ℝ] using h
  let g : ℝ → ℝ := fun y => 1 / (1 + Real.exp (-w y))
  have hgm : Measurable g := by
    have := w.measurable
    fun_prop
  have hgb : ∀ y, |g y| ≤ 1 := by
    intro y
    have hpos : 0 < 1 + Real.exp (-w y) := by positivity
    rw [abs_of_pos (by positivity), div_le_one hpos]
    linarith [Real.exp_pos (-w y)]
  refine IsUnit.of_mul_eq_one (mk g hgm 1 hgb) ?_
  ext y
  rw [mul_apply, hexp, mk_apply, one_apply]
  have hpos : 0 < 1 + Real.exp (-w y) := by positivity
  simp only [g]
  field_simp

/-- The value of `exp` in `BddMeas` is computed pointwise. -/
theorem exp_apply (w : BddMeas) (y : ℝ) : NormedSpace.exp w y = Real.exp (w y) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (evalRingHom y) (continuous_eval y) w
    ((NormedSpace.expSeries_radius_eq_top ℝ BddMeas).symm ▸ edist_lt_top _ _)
  simpa [Real.exp_eq_exp_ℝ] using h

/-- The logistic function `σ(t) = 1/(1+e^{-t})`. -/
noncomputable def logistic (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

/-- **The logistic function acting pointwise on `BddMeas`**, `σ(w) = (1 + exp(-w))⁻¹`. -/
noncomputable def sigma (w : BddMeas) : BddMeas := Ring.inverse (1 + NormedSpace.exp (-w))

/-- The logistic function acts pointwise. -/
theorem sigma_apply (w : BddMeas) (y : ℝ) : sigma w y = logistic (w y) := by
  obtain ⟨U, hU⟩ := isUnit_one_add_exp_neg w
  have hmul : sigma w * (1 + NormedSpace.exp (-w)) = 1 := by
    rw [sigma, ← hU, Ring.inverse_unit]; exact U.inv_mul
  have h := congrArg (fun f : BddMeas => f y) hmul
  simp only [mul_apply, add_apply, one_apply, exp_apply, neg_apply] at h
  rw [logistic]
  have hpos : 0 < 1 + Real.exp (-w y) := by positivity
  field_simp
  linarith

/-- The logistic function is analytic on `BddMeas`. -/
theorem analyticAt_sigma (w : BddMeas) : AnalyticAt ℝ sigma w := by
  obtain ⟨U, hU⟩ := isUnit_one_add_exp_neg w
  have h1 : AnalyticAt ℝ (fun w : BddMeas => 1 + NormedSpace.exp (-w)) w :=
    analyticAt_const.add ((NormedSpace.exp_analytic (𝕂 := ℝ) (-w)).comp analyticAt_id.neg)
  have h2 : AnalyticAt ℝ Ring.inverse (1 + NormedSpace.exp (-w)) := by
    rw [← hU]; exact analyticAt_inverse U
  exact AnalyticAt.comp (g := Ring.inverse) (f := fun w : BddMeas => 1 + NormedSpace.exp (-w))
    h2 h1

/-- Left multiplication by a fixed element, as a continuous linear map. -/
noncomputable def mulLeftCLM (a : BddMeas) : BddMeas →L[ℝ] BddMeas :=
  ContinuousLinearMap.mul ℝ BddMeas a

@[simp] theorem mulLeftCLM_apply (a u : BddMeas) : mulLeftCLM a u = a * u := rfl

/-- The logistic function is positive. -/
theorem logistic_pos (t : ℝ) : 0 < logistic t := by
  rw [logistic]; positivity

/-- The logistic function is less than one. -/
theorem logistic_lt_one (t : ℝ) : logistic t < 1 := by
  rw [logistic, div_lt_one (by positivity)]
  linarith [Real.exp_pos (-t)]

/-- The derivative of the logistic function acting on `BddMeas`: multiplication by
`σ(w)(1-σ(w))`. -/
theorem hasFDerivAt_sigma (w : BddMeas) :
    HasFDerivAt sigma (mulLeftCLM (sigma w * (1 - sigma w))) w := by
  obtain ⟨U, hU⟩ := isUnit_one_add_exp_neg w
  have h1 : HasFDerivAt (fun w : BddMeas => 1 + NormedSpace.exp (-w))
      ((NormedSpace.exp (-w) • (1 : BddMeas →L[ℝ] BddMeas)).comp
        (-(ContinuousLinearMap.id ℝ BddMeas))) w := by
    have hneg : HasFDerivAt (fun w : BddMeas => -w) (-(ContinuousLinearMap.id ℝ BddMeas)) w :=
      (hasFDerivAt_id w).neg
    exact (hasFDerivAt_exp (𝕂 := ℝ)).comp w hneg |>.const_add 1
  have h2 := hasFDerivAt_ringInverse (𝕜 := ℝ) U
  rw [hU] at h2
  have h := h2.comp w h1
  refine h.congr_fderiv ?_
  have hinvσ : ((U⁻¹ : BddMeasˣ) : BddMeas) = sigma w := by
    rw [sigma, ← hU, Ring.inverse_unit]
  ext u y
  have e1 : ((-(ContinuousLinearMap.mulLeftRight ℝ BddMeas ↑U⁻¹) ↑U⁻¹).comp
      ((NormedSpace.exp (-w) • (1 : BddMeas →L[ℝ] BddMeas)).comp
        (-(ContinuousLinearMap.id ℝ BddMeas)))) u
      = sigma w * sigma w * NormedSpace.exp (-w) * u := by
    simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply, _root_.smul_apply,
      one_apply_eq_self, ContinuousLinearMap.id_apply, ContinuousLinearMap.mulLeftRight_apply,
      hinvσ, smul_eq_mul]
    ring
  rw [e1, mulLeftCLM_apply]
  simp only [mul_apply, sub_apply, one_apply, exp_apply, sigma_apply, neg_apply]
  rw [logistic]
  have hpos : 0 < 1 + Real.exp (-w y) := by positivity
  have hne : Real.exp (-w y) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

end BddMeas

end UpperTailMultipodality
