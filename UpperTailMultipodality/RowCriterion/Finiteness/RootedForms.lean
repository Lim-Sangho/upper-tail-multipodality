import UpperTailMultipodality.RowCriterion.Finiteness.BoundedMeasurable
import UpperTailMultipodality.RowCriterion.Finiteness.Coordinates

/-!
# Rooted densities as multilinear forms

For a vertex `v` of `H`, the rooted density `ℛ_{v,W}` is the restriction to the diagonal of the
multilinear form

`M_v(φ) = ∫ ∏_{z ∈ N_H(v)} φ_z(ξ_z) · ∏_{ab ∈ E(H), a,b ≠ v} W(ξ_a,ξ_b) dξ`,

one slot per neighbour of `v`.  Fixing a neighbour `z₀` and pinning `ξ_{z₀} = y` gives a
multilinear map with values in bounded measurable functions of `y`,

`G_{v,z₀}(φ)(y) = ∫ ∏_{z ∈ N_H(v)} φ_z((ξ[z₀ ↦ y])_z) · ∏_{ab} W(...) dξ`,

whose value at `φ = u, …, u, 1 (slot z₀), u, …, u` is the gradient term `G_{v,z₀}(u)`,
`eq:rooted-gradient-kernel`.  This file constructs both maps on `BddMeas` (`rootedForm`, `gradForm`)
and proves the pairing identity `∫ G_{v,z₀}(φ) b = M_v(φ with φ_{z₀} b in slot z₀)`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbours of `v`, as a type indexing the slots of the rooted forms. -/
abbrev Nbr (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Type _ := ↥(H.neighborFinset v)

section Pointwise

/-- If every edge factor is at least `ω ∈ (0,1]`, the avoiding product is at least `ω^m`. -/
theorem avoidingProduct_ge (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) {ξ : V → ℝ}
    (hξ : ∀ a b : V, a ≠ b → ω ≤ W.toFun (ξ a) (ξ b)) :
    ω ^ H.edgeFinset.card ≤ avoidingProduct H W v ξ := by
  unfold avoidingProduct
  have hedge : ∀ e ∈ H.edgeFinset.filter (fun e => v ∉ e),
      ω ≤ edgeVal W.toFun W.symm' ξ e := by
    intro e he
    have he' := (Finset.mem_filter.mp he).1
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      exact hξ a b hadj.ne
  calc ω ^ H.edgeFinset.card
      ≤ ω ^ (H.edgeFinset.filter (fun e => v ∉ e)).card :=
        pow_le_pow_of_le_one hω0 hω1 (Finset.card_filter_le _ _)
    _ = ∏ _e ∈ H.edgeFinset.filter (fun e => v ∉ e), ω := by rw [Finset.prod_const]
    _ ≤ ∏ e ∈ H.edgeFinset.filter (fun e => v ∉ e), edgeVal W.toFun W.symm' ξ e :=
        Finset.prod_le_prod (fun _ _ => hω0) hedge

/-- The value of a product over slots after updating one slot. -/
theorem prod_apply_update {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → BddMeas) (i : ι)
    (g : BddMeas) (ζ : ι → ℝ) :
    ∏ j, (Function.update φ i g j) (ζ j) = g (ζ i) * ∏ j ∈ Finset.univ.erase i, φ j (ζ j) := by
  have h : ∀ j, (Function.update φ i g j) (ζ j)
      = Function.update (fun j => φ j (ζ j)) i (g (ζ i)) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [h]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

/-- A product of values is bounded by the product of the norms. -/
theorem abs_prod_apply_le {ι : Type*} [Fintype ι] (φ : ι → BddMeas) (ζ : ι → ℝ) :
    |∏ j, φ j (ζ j)| ≤ ∏ j, ‖φ j‖ := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => BddMeas.abs_apply_le_norm _ _

end Pointwise

variable (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)

/-- The integrand `∏_{z ∈ N(v)} φ_z(ξ_z) · ∏_{ab, a,b ≠ v} W(ξ_a,ξ_b)` of the rooted form. -/
noncomputable def formIntegrand (v : V) (φ : Nbr H v → BddMeas) (ξ : V → ℝ) : ℝ :=
  (∏ i, φ i (ξ i)) * avoidingProduct H W v ξ

variable {H W}

/-- The integrand of the rooted form is measurable. -/
theorem measurable_formIntegrand (v : V) (φ : Nbr H v → BddMeas) :
    Measurable (formIntegrand H W v φ) := by
  unfold formIntegrand
  refine Measurable.mul ?_ (measurable_avoidingProduct H W v)
  exact Finset.measurable_prod _ fun i _ => (φ i).measurable.comp (measurable_pi_apply _)

/-- The integrand of the rooted form is bounded by the product of the norms. -/
theorem abs_formIntegrand_le (v : V) (φ : Nbr H v → BddMeas) (ξ : V → ℝ) :
    |formIntegrand H W v φ ξ| ≤ ∏ i, ‖φ i‖ := by
  unfold formIntegrand
  rw [abs_mul, abs_of_nonneg (avoidingProduct_mem_Icc H W v ξ).1]
  calc |∏ i, φ i (ξ i)| * avoidingProduct H W v ξ ≤ (∏ i, ‖φ i‖) * 1 :=
        mul_le_mul (abs_prod_apply_le φ fun i => ξ i) (avoidingProduct_mem_Icc H W v ξ).2
          (avoidingProduct_mem_Icc H W v ξ).1 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ∏ i, ‖φ i‖ := mul_one _

/-- The integrand of the rooted form is integrable. -/
theorem integrable_formIntegrand (v : V) (φ : Nbr H v → BddMeas) :
    Integrable (formIntegrand H W v φ) (Measure.pi fun _ : V => unitμ) :=
  integrable_of_abs_le (measurable_formIntegrand v φ) _ (abs_formIntegrand_le v φ)

/-- The integrand after updating one slot. -/
theorem formIntegrand_update (v : V) [DecidableEq (Nbr H v)] (φ : Nbr H v → BddMeas)
    (i : Nbr H v) (g : BddMeas) (ξ : V → ℝ) :
    formIntegrand H W v (Function.update φ i g) ξ
      = g (ξ i) * ((∏ j ∈ Finset.univ.erase i, φ j (ξ j)) * avoidingProduct H W v ξ) := by
  unfold formIntegrand
  rw [prod_apply_update φ i g (fun j => ξ j), mul_assoc]

/-- The integrand is additive in each slot. -/
theorem formIntegrand_update_add (v : V) [DecidableEq (Nbr H v)] (φ : Nbr H v → BddMeas)
    (i : Nbr H v) (x y : BddMeas) (ξ : V → ℝ) :
    formIntegrand H W v (Function.update φ i (x + y)) ξ
      = formIntegrand H W v (Function.update φ i x) ξ
        + formIntegrand H W v (Function.update φ i y) ξ := by
  rw [formIntegrand_update, formIntegrand_update, formIntegrand_update, BddMeas.add_apply]
  ring

/-- The integrand is homogeneous in each slot. -/
theorem formIntegrand_update_smul (v : V) [DecidableEq (Nbr H v)] (φ : Nbr H v → BddMeas)
    (i : Nbr H v) (c : ℝ) (x : BddMeas) (ξ : V → ℝ) :
    formIntegrand H W v (Function.update φ i (c • x)) ξ
      = c * formIntegrand H W v (Function.update φ i x) ξ := by
  rw [formIntegrand_update, formIntegrand_update, BddMeas.smul_apply]
  ring

/-- The pinned integrand is integrable. -/
theorem integrable_formIntegrand_update (v z₀ : V) (φ : Nbr H v → BddMeas) (y : ℝ) :
    Integrable (fun ξ => formIntegrand H W v φ (Function.update ξ z₀ y))
      (Measure.pi fun _ : V => unitμ) := by
  classical
  refine integrable_of_abs_le ((measurable_formIntegrand v φ).comp ?_) _
    (fun ξ => abs_formIntegrand_le v φ _)
  exact (measurable_update_pair z₀).comp (measurable_id.prodMk measurable_const)

variable (H W)

/-- **The rooted form `M_v`**, a continuous multilinear form on `BddMeas` with one slot per
neighbour of `v`. -/
noncomputable def rootedForm (v : V) : ContinuousMultilinearMap ℝ (fun _ : Nbr H v => BddMeas) ℝ :=
  MultilinearMap.mkContinuous
    { toFun := fun φ => ∫ ξ, formIntegrand H W v φ ξ ∂(Measure.pi fun _ : V => unitμ)
      map_update_add' := by
        intro _ φ i x y
        simp_rw [formIntegrand_update_add]
        exact integral_add (integrable_formIntegrand v _) (integrable_formIntegrand v _)
      map_update_smul' := by
        intro _ φ i c x
        simp_rw [formIntegrand_update_smul]
        exact integral_const_mul c _ } 1
    (fun φ => by
      show ‖∫ ξ, formIntegrand H W v φ ξ ∂(Measure.pi fun _ : V => unitμ)‖ ≤ 1 * ∏ i, ‖φ i‖
      rw [one_mul, Real.norm_eq_abs]
      calc |∫ ξ, formIntegrand H W v φ ξ ∂(Measure.pi fun _ : V => unitμ)|
          ≤ ∫ ξ, |formIntegrand H W v φ ξ| ∂(Measure.pi fun _ : V => unitμ) :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _ξ, ∏ i, ‖φ i‖ ∂(Measure.pi fun _ : V => unitμ) :=
            integral_mono (integrable_formIntegrand v φ).abs (integrable_const _)
              (abs_formIntegrand_le v φ)
        _ = ∏ i, ‖φ i‖ := by simp)

/-- The value of the rooted form as an integral. -/
theorem rootedForm_apply (v : V) (φ : Nbr H v → BddMeas) :
    rootedForm H W v φ = ∫ ξ, formIntegrand H W v φ ξ ∂(Measure.pi fun _ : V => unitμ) := rfl

/-- The pinned rooted form is measurable in the pinned variable. -/
theorem measurable_gradFormFun (v : V) (z₀ : V) (φ : Nbr H v → BddMeas) :
    Measurable fun y => ∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y)
      ∂(Measure.pi fun _ : V => unitμ) := by
  classical
  exact measurable_integral_left (F := fun p : (V → ℝ) × ℝ =>
    formIntegrand H W v φ (Function.update p.1 z₀ p.2))
    ((measurable_formIntegrand v φ).comp (measurable_update_pair z₀))

/-- **The pinned rooted form `G_{v,z₀}`**, a continuous multilinear map from `BddMeas` (one slot
per neighbour of `v`) to `BddMeas`. -/
noncomputable def gradForm (v : V) (z₀ : V) :
    ContinuousMultilinearMap ℝ (fun _ : Nbr H v => BddMeas) BddMeas :=
  MultilinearMap.mkContinuous
    { toFun := fun φ => BddMeas.mk
        (fun y => ∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y)
          ∂(Measure.pi fun _ : V => unitμ))
        (measurable_gradFormFun H W v z₀ φ) (∏ i, ‖φ i‖) (fun y => by
          calc |∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y)
                ∂(Measure.pi fun _ : V => unitμ)|
              ≤ ∫ ξ, |formIntegrand H W v φ (Function.update ξ z₀ y)|
                  ∂(Measure.pi fun _ : V => unitμ) := abs_integral_le_integral_abs
            _ ≤ ∫ _ξ, ∏ i, ‖φ i‖ ∂(Measure.pi fun _ : V => unitμ) := by
                refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
                  (integrable_const _) (Filter.Eventually.of_forall fun ξ => ?_)
                exact abs_formIntegrand_le v φ _
            _ = ∏ i, ‖φ i‖ := by simp)
      map_update_add' := by
        intro _ φ i x y
        ext t
        simp only [BddMeas.add_apply, BddMeas.mk_apply]
        simp_rw [formIntegrand_update_add]
        exact integral_add (integrable_formIntegrand_update v z₀ _ t)
          (integrable_formIntegrand_update v z₀ _ t)
      map_update_smul' := by
        intro _ φ i c x
        ext t
        simp only [BddMeas.smul_apply, BddMeas.mk_apply]
        simp_rw [formIntegrand_update_smul]
        exact integral_const_mul c _ } 1
    (fun φ => by
      rw [one_mul]
      exact BddMeas.norm_le_of_forall (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (fun y => by
          show |∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y)
            ∂(Measure.pi fun _ : V => unitμ)| ≤ _
          calc |∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y)
                ∂(Measure.pi fun _ : V => unitμ)|
              ≤ ∫ ξ, |formIntegrand H W v φ (Function.update ξ z₀ y)|
                  ∂(Measure.pi fun _ : V => unitμ) := abs_integral_le_integral_abs
            _ ≤ ∫ _ξ, ∏ i, ‖φ i‖ ∂(Measure.pi fun _ : V => unitμ) := by
                refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
                  (integrable_const _) (Filter.Eventually.of_forall fun ξ => ?_)
                exact abs_formIntegrand_le v φ _
            _ = ∏ i, ‖φ i‖ := by simp))

/-- The value of the pinned rooted form as an integral. -/
theorem gradForm_apply (v z₀ : V) (φ : Nbr H v → BddMeas) (y : ℝ) :
    gradForm H W v z₀ φ y
      = ∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y) ∂(Measure.pi fun _ : V => unitμ) :=
  rfl

variable {H W}

/-- **The rooted form on the diagonal is the rooted density.** -/
theorem rootedForm_diag (v : V) (u : BddMeas) :
    rootedForm H W v (fun _ => u) = rootedDensity H W v u := by
  rw [rootedForm_apply, rootedDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [formIntegrand]
  rw [Finset.prod_coe_sort (H.neighborFinset v) (fun z => u (ξ z))]

/-- A product over the neighbours of `v` other than `z₀`. -/
theorem prod_univ_erase_nbr (v : V) (z₀ : Nbr H v) (f : V → ℝ) :
    ∏ j ∈ (Finset.univ : Finset (Nbr H v)).erase z₀, f j
      = ∏ z ∈ (H.neighborFinset v).erase z₀, f z := by
  rw [← Finset.attach_eq_univ]
  exact Finset.prod_erase_attach f z₀

/-- **The pinned rooted form with `1` in the pinned slot is the gradient term**
`G_{v,z₀}(u)`, `eq:rooted-gradient-kernel`. -/
theorem gradForm_update_one (v : V) (z₀ : Nbr H v) (u : BddMeas) (y : ℝ) :
    gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) y
      = rootedGradientTerm H W v z₀ u y := by
  rw [gradForm_apply, rootedGradientTerm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [formIntegrand_update, BddMeas.one_apply, one_mul,
    prod_univ_erase_nbr v z₀ (fun z => u (Function.update ξ z₀ y z))]

/-- **The pairing identity**: `∫ G_{v,z₀}(φ) b = M_v(φ with φ_{z₀} b in slot z₀)`. -/
theorem integ_gradForm_mul (v : V) (z₀ : Nbr H v) (φ : Nbr H v → BddMeas) (b : BddMeas) :
    BddMeas.integ (gradForm H W v z₀ φ * b)
      = rootedForm H W v (Function.update φ z₀ (φ z₀ * b)) := by
  rw [BddMeas.integ_apply, rootedForm_apply]
  have hpt : ∀ y ξ, formIntegrand H W v φ (Function.update ξ z₀ y) * b y
      = formIntegrand H W v (Function.update φ z₀ (φ z₀ * b)) (Function.update ξ z₀ y) := by
    intro y ξ
    have hφ : φ = Function.update φ z₀ (φ z₀) := (Function.update_eq_self z₀ φ).symm
    conv_lhs => rw [hφ]
    rw [formIntegrand_update, formIntegrand_update, BddMeas.mul_apply, Function.update_self]
    ring
  calc ∫ y, (gradForm H W v z₀ φ * b) y ∂unitμ
      = ∫ y, (∫ ξ, formIntegrand H W v (Function.update φ z₀ (φ z₀ * b))
          (Function.update ξ z₀ y) ∂(Measure.pi fun _ : V => unitμ)) ∂unitμ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [BddMeas.mul_apply, gradForm_apply]
        rw [← integral_mul_const]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => hpt y ξ)
    _ = ∫ ξ, formIntegrand H W v (Function.update φ z₀ (φ z₀ * b)) ξ
          ∂(Measure.pi fun _ : V => unitμ) :=
        integral_integral_update (z₀ : V) (measurable_formIntegrand v _)
          (abs_formIntegrand_le v _)

/-- The rooted form of nonnegative functions is nonnegative. -/
theorem rootedForm_nonneg (v : V) {φ : Nbr H v → BddMeas} (hφ : ∀ i y, 0 ≤ φ i y) :
    0 ≤ rootedForm H W v φ := by
  rw [rootedForm_apply]
  refine integral_nonneg fun ξ => ?_
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hφ i _) (avoidingProduct_mem_Icc H W v ξ).1

/-- The integrand takes values in `[0,1]` for arguments with values in `[0,1]`. -/
theorem formIntegrand_mem_Icc (v : V) {φ : Nbr H v → BddMeas}
    (hφ : ∀ i y, φ i y ∈ Set.Icc (0:ℝ) 1) (ξ : V → ℝ) :
    formIntegrand H W v φ ξ ∈ Set.Icc (0:ℝ) 1 := by
  unfold formIntegrand
  have hP := avoidingProduct_mem_Icc H W v ξ
  refine ⟨mul_nonneg (Finset.prod_nonneg fun i _ => (hφ i _).1) hP.1, ?_⟩
  calc (∏ i, φ i (ξ i)) * avoidingProduct H W v ξ ≤ 1 * 1 :=
        mul_le_mul (Finset.prod_le_one (fun i _ => (hφ i _).1) fun i _ => (hφ i _).2) hP.2 hP.1
          zero_le_one
    _ = 1 := one_mul 1

/-- The pinned rooted form of functions with values in `[0,1]` has values in `[0,1]`. -/
theorem gradForm_mem_Icc (v z₀ : V) {φ : Nbr H v → BddMeas}
    (hφ : ∀ i y, φ i y ∈ Set.Icc (0:ℝ) 1) (y : ℝ) :
    gradForm H W v z₀ φ y ∈ Set.Icc (0:ℝ) 1 := by
  rw [gradForm_apply]
  constructor
  · exact integral_nonneg fun ξ => (formIntegrand_mem_Icc v hφ _).1
  · calc ∫ ξ, formIntegrand H W v φ (Function.update ξ z₀ y) ∂(Measure.pi fun _ : V => unitμ)
        ≤ ∫ _ξ, (1:ℝ) ∂(Measure.pi fun _ : V => unitμ) :=
          integral_mono (integrable_formIntegrand_update v z₀ φ y) (integrable_const _)
            fun ξ => (formIntegrand_mem_Icc v hφ _).2
      _ = 1 := by simp

end UpperTailMultipodality
