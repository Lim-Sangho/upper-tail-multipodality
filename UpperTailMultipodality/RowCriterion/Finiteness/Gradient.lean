import UpperTailMultipodality.RowCriterion.Finiteness.RootedForms

/-!
# The rooted density and its gradient on bounded measurable functions

On `BddMeas`, the total rooted density `ℛ_W = ∑_v ℛ_{v,W}` is a polynomial (`rootedE`) and its
gradient `∇ℛ_W` (`gradE`) is a polynomial map `BddMeas → BddMeas`.  This file proves:

* `hasFDerivAt_rootedE` — the first variation `Dℛ_W(u)[k] = ∫ ∇ℛ_W(u) k`;
* `hasFDerivAt_gradE`, `analyticAt_gradE` — `∇ℛ_W` is analytic, with derivative `gradDeriv`;
* `integ_gradDeriv_mul` — the second variation `∫ D∇ℛ_W(u)[a] b` as a sum of rooted forms, and
  its positivity (`integ_gradDeriv_mul_nonneg`, `integ_gradDeriv_mul_ge`), the source of the
  strict inequalities of `lem:strict-supermodular` and `lem:coercive`;
* `abs_gradE_sub_le` — the Lipschitz bound `‖∇ℛ_W(u) - ∇ℛ_W(u')‖_∞ ≤ C_H ‖u-u'‖₁`,
  `eq:gradient-lipschitz`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The continuous linear map `k ↦ (k, …, k, 0 (slot z₀), k, …, k)`. -/
noncomputable def slotCLM {ι : Type*} [DecidableEq ι] (z₀ : ι) : BddMeas →L[ℝ] (ι → BddMeas) :=
  ContinuousLinearMap.pi fun i => if i = z₀ then 0 else ContinuousLinearMap.id ℝ BddMeas

/-- The value of the slot map. -/
theorem slotCLM_apply {ι : Type*} [DecidableEq ι] (z₀ : ι) (k : BddMeas) (i : ι) :
    slotCLM z₀ k i = if i = z₀ then 0 else k := by
  unfold slotCLM
  split_ifs <;> simp [*]

/-- The pinned diagonal as an affine map. -/
theorem update_const_eq_slot {ι : Type*} [DecidableEq ι] (z₀ : ι) (u : BddMeas) :
    Function.update (fun _ : ι => u) z₀ 1
      = slotCLM z₀ u + Function.update (0 : ι → BddMeas) z₀ 1 := by
  funext i
  rw [Pi.add_apply, slotCLM_apply]
  by_cases h : i = z₀
  · subst h; simp
  · simp [h]

/-- The derivative of the pinned diagonal. -/
theorem hasFDerivAt_update_const {ι : Type*} [Fintype ι] [DecidableEq ι] (z₀ : ι) (u : BddMeas) :
    HasFDerivAt (fun u : BddMeas => Function.update (fun _ : ι => u) z₀ 1) (slotCLM z₀) u := by
  have h : (fun u : BddMeas => Function.update (fun _ : ι => u) z₀ 1)
      = fun u => slotCLM z₀ u + Function.update (0 : ι → BddMeas) z₀ 1 :=
    funext (update_const_eq_slot z₀)
  rw [h]
  exact (hasFDerivAt_add_const_iff _).mpr (slotCLM z₀).hasFDerivAt

/-- The diagonal map `u ↦ (u, …, u)`. -/
noncomputable def diagCLM (ι : Type*) : BddMeas →L[ℝ] (ι → BddMeas) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ BddMeas

@[simp] theorem diagCLM_apply (ι : Type*) (u : BddMeas) : diagCLM ι u = fun _ => u := rfl

variable (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)

/-- **The total rooted density `ℛ_W` on `BddMeas`.** -/
noncomputable def rootedE (u : BddMeas) : ℝ := ∑ v, rootedForm H W v (fun _ => u)

/-- **The gradient `∇ℛ_W` on `BddMeas`.** -/
noncomputable def gradE (u : BddMeas) : BddMeas :=
  ∑ v, ∑ z₀ : Nbr H v, gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1)

/-- **The derivative of `∇ℛ_W` at `u`.** -/
noncomputable def gradDeriv (u : BddMeas) : BddMeas →L[ℝ] BddMeas :=
  ∑ v, ∑ z₀ : Nbr H v,
    ((gradForm H W v z₀).linearDeriv (Function.update (fun _ => u) z₀ 1)).comp (slotCLM z₀)

variable {H W}

/-- `rootedE` is the total rooted density `ℛ_W`. -/
theorem rootedE_eq (u : BddMeas) : rootedE H W u = totalRootedDensity H W u := by
  simp only [rootedE, totalRootedDensity, rootedForm_diag]

/-- `gradE` is the gradient `∇ℛ_W`, `eq:rooted-gradient`. -/
theorem gradE_apply (u : BddMeas) (y : ℝ) : gradE H W u y = rootedGradient H W u y := by
  simp only [gradE, rootedGradient, BddMeas.sum_apply, gradForm_update_one]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact Finset.sum_coe_sort (H.neighborFinset v) (fun z => rootedGradientTerm H W v z u y)

/-- The derivative of `∇ℛ_W` as a sum of pinned rooted forms. -/
theorem gradDeriv_apply (u k : BddMeas) :
    gradDeriv H W u k = ∑ v, ∑ z₀ : Nbr H v, ∑ i : Nbr H v,
      gradForm H W v z₀ (Function.update (Function.update (fun _ => u) z₀ 1) i
        (if i = z₀ then 0 else k)) := by
  simp only [gradDeriv, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, slotCLM_apply]

/-- **The first variation of `ℛ_W`**: `Dℛ_W(u)[k] = ∫ ∇ℛ_W(u) k`. -/
theorem hasFDerivAt_rootedE (u : BddMeas) :
    HasFDerivAt (rootedE H W) (BddMeas.integ.comp (BddMeas.mulLeftCLM (gradE H W u))) u := by
  have h : HasFDerivAt (rootedE H W)
      (∑ v, ((rootedForm H W v).linearDeriv (fun _ => u)).comp (diagCLM (Nbr H v))) u := by
    have : rootedE H W = fun u => ∑ v, rootedForm H W v (diagCLM (Nbr H v) u) := rfl
    rw [this]
    refine HasFDerivAt.fun_sum fun v _ => ?_
    exact ((rootedForm H W v).hasFDerivAt (diagCLM (Nbr H v) u)).comp u
      (diagCLM (Nbr H v)).hasFDerivAt
  refine h.congr_fderiv ?_
  ext k
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, diagCLM_apply, BddMeas.mulLeftCLM_apply, gradE,
    Finset.sum_mul, map_sum, integ_gradForm_mul]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z₀ _ => ?_
  rw [Function.update_self, one_mul, Function.update_idem]

/-- `∇ℛ_W` is differentiable with derivative `gradDeriv`. -/
theorem hasFDerivAt_gradE (u : BddMeas) : HasFDerivAt (gradE H W) (gradDeriv H W u) u := by
  have : gradE H W = fun u => ∑ v, ∑ z₀ : Nbr H v,
      gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) := rfl
  rw [this, gradDeriv]
  refine HasFDerivAt.fun_sum fun v _ => HasFDerivAt.fun_sum fun z₀ _ => ?_
  exact ((gradForm H W v z₀).hasFDerivAt _).comp u (hasFDerivAt_update_const z₀ u)

/-- `∇ℛ_W` is analytic, being a polynomial map. -/
theorem analyticAt_gradE (u : BddMeas) : AnalyticAt ℝ (gradE H W) u := by
  have : gradE H W = fun u => ∑ v, ∑ z₀ : Nbr H v,
      gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) := rfl
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun v _ => Finset.analyticAt_fun_sum _ fun z₀ _ => ?_
  have haff : AnalyticAt ℝ (fun u : BddMeas => Function.update (fun _ : Nbr H v => u) z₀ 1) u := by
    have h : (fun u : BddMeas => Function.update (fun _ : Nbr H v => u) z₀ 1)
        = fun u => slotCLM z₀ u + Function.update (0 : Nbr H v → BddMeas) z₀ 1 :=
      funext (update_const_eq_slot z₀)
    rw [h]
    exact (slotCLM z₀).analyticAt u |>.add analyticAt_const
  exact (gradForm H W v z₀).analyticAt.comp haff

/-- **The second variation as a sum of rooted forms**:
`∫ D∇ℛ_W(u)[a] b = ∑_v ∑_{z₀ ≠ i} M_v(u, …, b (slot z₀), …, a (slot i), …, u)`. -/
theorem integ_gradDeriv_mul (u a b : BddMeas) :
    BddMeas.integ (gradDeriv H W u a * b) = ∑ v, ∑ z₀ : Nbr H v, ∑ i : Nbr H v,
      if i = z₀ then 0 else
        rootedForm H W v (Function.update (Function.update (fun _ => u) z₀ b) i a) := by
  rw [gradDeriv_apply]
  simp only [Finset.sum_mul, map_sum, integ_gradForm_mul]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z₀ _ =>
    Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = z₀
  · subst hi
    simp only [if_true, Function.update_self, zero_mul, Function.update_idem]
    exact (rootedForm H W v).map_update_zero _ _
  · simp only [hi, if_false]
    rw [Function.update_of_ne (Ne.symm hi), Function.update_self, one_mul,
      Function.update_comm hi, Function.update_idem]

/-- The second variation is nonnegative on nonnegative functions. -/
theorem integ_gradDeriv_mul_nonneg {u a b : BddMeas} (hu : ∀ y, 0 ≤ u y) (ha : ∀ y, 0 ≤ a y)
    (hb : ∀ y, 0 ≤ b y) : 0 ≤ BddMeas.integ (gradDeriv H W u a * b) := by
  rw [integ_gradDeriv_mul]
  refine Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun z₀ _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact le_refl 0
  · refine rootedForm_nonneg v fun j y => ?_
    by_cases hj : j = i
    · subst hj; simp [ha]
    · rw [Function.update_of_ne hj]
      by_cases hj' : j = z₀
      · subst hj'; simp [hb]
      · rw [Function.update_of_ne hj']; exact hu y

/-- **Quantitative positivity of the mixed second variation.**  If `Δ(H) ≥ 2`, `W ≥ ω` almost
everywhere, and `c ≤ u ≤ 1`, then `∫ D∇ℛ_W(u)[a] b ≥ c^N ω^m ∫a ∫b` for `a, b ≥ 0`. -/
theorem integ_gradDeriv_mul_ge (hΔ : ∃ v, 2 ≤ H.degree v) {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {u a b : BddMeas}
    (hu : ∀ y, c ≤ u y) (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) :
    c ^ Fintype.card V * ω ^ H.edgeFinset.card * BddMeas.integ a * BddMeas.integ b
      ≤ BddMeas.integ (gradDeriv H W u a * b) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hΔ
  have hcard : 1 < (H.neighborFinset v₀).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hne⟩ := Finset.one_lt_card.mp hcard
  let Z₀ : Nbr H v₀ := ⟨z₀, hz₀⟩
  let Z₁ : Nbr H v₀ := ⟨z₁, hz₁⟩
  have hZ : Z₁ ≠ Z₀ := fun h => hne (congrArg Subtype.val h).symm
  have hu0 : ∀ y, 0 ≤ u y := fun y => hc0.trans (hu y)
  -- all terms are nonnegative; keep the term `(v₀, Z₀, Z₁)`
  have hterm_nonneg : ∀ v (z i : Nbr H v), 0 ≤ (if i = z then 0 else
      rootedForm H W v (Function.update (Function.update (fun _ => u) z b) i a)) := by
    intro v z i
    split_ifs
    · exact le_refl 0
    · refine rootedForm_nonneg v fun j y => ?_
      by_cases hj : j = i
      · subst hj; simp [ha]
      · rw [Function.update_of_ne hj]
        by_cases hj' : j = z
        · subst hj'; simp [hb]
        · rw [Function.update_of_ne hj']; exact hu0 y
  have hkeep : rootedForm H W v₀ (Function.update (Function.update (fun _ => u) Z₀ b) Z₁ a)
      ≤ BddMeas.integ (gradDeriv H W u a * b) := by
    rw [integ_gradDeriv_mul]
    have h1 : (if Z₁ = Z₀ then 0 else
        rootedForm H W v₀ (Function.update (Function.update (fun _ => u) Z₀ b) Z₁ a))
        ≤ ∑ i : Nbr H v₀, (if i = Z₀ then 0 else
          rootedForm H W v₀ (Function.update (Function.update (fun _ => u) Z₀ b) i a)) :=
      Finset.single_le_sum (f := fun i => if i = Z₀ then 0 else
          rootedForm H W v₀ (Function.update (Function.update (fun _ => u) Z₀ b) i a))
        (fun i _ => hterm_nonneg v₀ Z₀ i) (Finset.mem_univ Z₁)
    rw [if_neg hZ] at h1
    refine h1.trans ?_
    refine (Finset.single_le_sum (f := fun z => ∑ i : Nbr H v₀, (if i = z then 0 else
          rootedForm H W v₀ (Function.update (Function.update (fun _ => u) z b) i a)))
        (fun z _ => Finset.sum_nonneg fun i _ => hterm_nonneg v₀ z i) (Finset.mem_univ Z₀)).trans ?_
    exact Finset.single_le_sum (f := fun v => ∑ z : Nbr H v, ∑ i : Nbr H v, (if i = z then 0 else
          rootedForm H W v (Function.update (Function.update (fun _ => u) z b) i a)))
        (fun v _ => Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ => hterm_nonneg v z i)
        (Finset.mem_univ v₀)
  refine le_trans ?_ hkeep
  -- lower bound for the kept term
  rw [rootedForm_apply]
  have hlow : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ),
      c ^ Fintype.card V * ω ^ H.edgeFinset.card * (a (ξ z₁) * b (ξ z₀))
        ≤ formIntegrand H W v₀ (Function.update (Function.update (fun _ => u) Z₀ b) Z₁ a) ξ := by
    filter_upwards [ae_forall_edge_ge (V := V) W hWω] with ξ hξ
    rw [formIntegrand_update, ← Finset.mul_prod_erase (Finset.univ.erase Z₁) _
      (Finset.mem_erase.mpr ⟨hZ.symm, Finset.mem_univ Z₀⟩)]
    rw [Function.update_self]
    have hrest : ∀ j ∈ (Finset.univ.erase Z₁).erase Z₀,
        (Function.update (fun _ => u) Z₀ b j) (ξ j) = u (ξ j) := by
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [Finset.prod_congr rfl hrest]
    have hprod : c ^ Fintype.card V ≤ ∏ j ∈ (Finset.univ.erase Z₁).erase Z₀, u (ξ j) := by
      calc c ^ Fintype.card V ≤ c ^ ((Finset.univ.erase Z₁).erase Z₀).card := by
            refine pow_le_pow_of_le_one hc0 hc1 ?_
            calc ((Finset.univ.erase Z₁).erase Z₀).card ≤ (Finset.univ : Finset (Nbr H v₀)).card :=
                  (Finset.card_erase_le).trans Finset.card_erase_le
              _ = (H.neighborFinset v₀).card := Finset.card_univ.trans (Fintype.card_coe _)
              _ ≤ Fintype.card V := Finset.card_le_univ _
        _ = ∏ _j ∈ (Finset.univ.erase Z₁).erase Z₀, c := by rw [Finset.prod_const]
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc0) fun j _ => hu _
    have hP := avoidingProduct_ge H W v₀ hω0 hω1 hξ
    have ha' := ha (ξ z₁)
    have hb' := hb (ξ z₀)
    have hcpow : 0 ≤ c ^ Fintype.card V := pow_nonneg hc0 _
    have hωpow : 0 ≤ ω ^ H.edgeFinset.card := pow_nonneg hω0 _
    calc c ^ Fintype.card V * ω ^ H.edgeFinset.card * (a (ξ z₁) * b (ξ z₀))
        = a (ξ z₁) * (b (ξ z₀) * (c ^ Fintype.card V * ω ^ H.edgeFinset.card)) := by ring
      _ ≤ a (ξ z₁) * (b (ξ z₀) * ((∏ j ∈ (Finset.univ.erase Z₁).erase Z₀, u (ξ j))
            * avoidingProduct H W v₀ ξ)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hb') ha'
          exact mul_le_mul hprod hP hωpow (hcpow.trans hprod)
      _ = _ := by ring
  have hint : Integrable (fun ξ : V → ℝ => a (ξ z₁) * b (ξ z₀)) (Measure.pi fun _ : V => unitμ) :=
    integrable_of_abs_le ((a.measurable.comp (measurable_pi_apply z₁)).mul
      (b.measurable.comp (measurable_pi_apply z₀))) (‖a‖ * ‖b‖) fun ξ => by
        rw [abs_mul]
        exact mul_le_mul (a.abs_apply_le_norm _) (b.abs_apply_le_norm _) (abs_nonneg _)
          (norm_nonneg _)
  calc c ^ Fintype.card V * ω ^ H.edgeFinset.card * BddMeas.integ a * BddMeas.integ b
      = ∫ ξ, c ^ Fintype.card V * ω ^ H.edgeFinset.card * (a (ξ z₁) * b (ξ z₀))
          ∂(Measure.pi fun _ : V => unitμ) := by
        rw [integral_const_mul,
          integral_eval_mul_eval (Ne.symm hne) a.measurable.aestronglyMeasurable
          b.measurable.aestronglyMeasurable, BddMeas.integ_apply, BddMeas.integ_apply]
        ring
    _ ≤ _ := integral_mono_ae (hint.const_mul _) (integrable_formIntegrand v₀ _) hlow

/-! ### Bounds -/

/-- `|∏ f - ∏ g| ≤ ∑ |f - g|` for factors in `[0,1]`. -/
private theorem abs_prod_sub_prod_le_sum' {ι : Type*} [DecidableEq ι] (T : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1) (hg : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1) :
    |∏ i ∈ T, f i - ∏ i ∈ T, g i| ≤ ∑ i ∈ T, |f i - g i| := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hfT : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgT : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga := hg a (Finset.mem_insert_self a T)
    have hP : ∏ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hfT i hi).1,
        Finset.prod_le_one (fun i hi => (hfT i hi).1) fun i hi => (hfT i hi).2⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hsplit : f a * ∏ i ∈ T, f i - g a * ∏ i ∈ T, g i
        = (f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i) := by ring
    rw [hsplit]
    calc |(f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)|
        ≤ |(f a - g a) * ∏ i ∈ T, f i| + |g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)| := abs_add_le _ _
      _ = |f a - g a| * ∏ i ∈ T, f i + g a * |∏ i ∈ T, f i - ∏ i ∈ T, g i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hP.1, abs_of_nonneg hga.1]
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ T, |f i - g i| :=
          add_le_add (mul_le_mul_of_nonneg_left hP.2 (abs_nonneg _))
            (mul_le_mul hga.2 (ih hfT hgT) (abs_nonneg _) zero_le_one)
      _ = |f a - g a| + ∑ i ∈ T, |f i - g i| := by ring

variable (H) in
/-- The constant `C_H = ∑_v deg(v)²` of the Lipschitz bounds. -/
noncomputable def lipConst : ℝ := ∑ v, (Fintype.card (Nbr H v) : ℝ) ^ 2

omit [DecidableEq V] in
/-- The Lipschitz constant is nonnegative. -/
theorem lipConst_nonneg : 0 ≤ lipConst H := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A function with values in `[0,1]`. -/
def UnitValued (u : BddMeas) : Prop := ∀ y, u y ∈ Set.Icc (0:ℝ) 1

/-- Pinning the value `1` preserves values in `[0,1]`. -/
theorem unitValued_update_one {ι : Type*} [DecidableEq ι] {u : BddMeas} (hu : UnitValued u)
    (z₀ : ι) : ∀ i y, (Function.update (fun _ : ι => u) z₀ 1) i y ∈ Set.Icc (0:ℝ) 1 := by
  intro i y
  by_cases h : i = z₀
  · subst h; simp [BddMeas.one_apply]
  · rw [Function.update_of_ne h]; exact hu y

/-- The absolute difference of two bounded measurable functions is integrable. -/
theorem abs_sub_integrable (u u' : BddMeas) : Integrable (fun y => |u y - u' y|) unitμ :=
  (u.integrable.sub u'.integrable).abs

/-- The gradient of a function with values in `[0,1]` is bounded by `C_H`. -/
theorem gradE_mem_Icc {u : BddMeas} (hu : UnitValued u) (y : ℝ) :
    gradE H W u y ∈ Set.Icc (0:ℝ) (lipConst H) := by
  simp only [gradE, BddMeas.sum_apply]
  constructor
  · exact Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun z₀ _ =>
      (gradForm_mem_Icc v z₀ (unitValued_update_one hu z₀) y).1
  · refine Finset.sum_le_sum fun v _ => ?_
    calc ∑ z₀ : Nbr H v, gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) y
        ≤ ∑ _z₀ : Nbr H v, (1:ℝ) := Finset.sum_le_sum fun z₀ _ =>
          (gradForm_mem_Icc v z₀ (unitValued_update_one hu z₀) y).2
      _ = (Fintype.card (Nbr H v) : ℝ) := by simp
      _ ≤ (Fintype.card (Nbr H v) : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos (Fintype.card (Nbr H v)) with h | h
          · simp [h]
          · have : (1:ℝ) ≤ Fintype.card (Nbr H v) := by exact_mod_cast h
            nlinarith

/-- **`eq:gradient-lipschitz`**: `|∇ℛ_W(u)(y) - ∇ℛ_W(u')(y)| ≤ C_H ‖u - u'‖₁` for functions with
values in `[0,1]`. -/
theorem abs_gradE_sub_le {u u' : BddMeas} (hu : UnitValued u) (hu' : UnitValued u') (y : ℝ) :
    |gradE H W u y - gradE H W u' y| ≤ lipConst H * ∫ t, |u t - u' t| ∂unitμ := by
  simp only [gradE, BddMeas.sum_apply]
  rw [← Finset.sum_sub_distrib, lipConst, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ z₀ : Nbr H v,
      |gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) y
        - gradForm H W v z₀ (Function.update (fun _ => u') z₀ 1) y|
        ≤ (Fintype.card (Nbr H v) : ℝ) * ∫ t, |u t - u' t| ∂unitμ := by
    intro z₀
    rw [gradForm_apply, gradForm_apply, ← integral_sub (integrable_formIntegrand_update v z₀ _ y)
      (integrable_formIntegrand_update v z₀ _ y)]
    refine (abs_integral_le_integral_abs).trans ?_
    have hpt : ∀ ξ : V → ℝ,
        |formIntegrand H W v (Function.update (fun _ => u) z₀ 1) (Function.update ξ z₀ y)
          - formIntegrand H W v (Function.update (fun _ => u') z₀ 1) (Function.update ξ z₀ y)|
          ≤ ∑ j : Nbr H v, |u (ξ j) - u' (ξ j)| := by
      intro ξ
      simp only [formIntegrand]
      rw [← sub_mul, abs_mul]
      have hP := avoidingProduct_mem_Icc H W v (Function.update ξ z₀ y)
      rw [abs_of_nonneg hP.1]
      refine (mul_le_of_le_one_right (abs_nonneg _) hP.2).trans ?_
      refine (abs_prod_sub_prod_le_sum' Finset.univ _ _
        (fun j _ => unitValued_update_one hu z₀ j _)
        (fun j _ => unitValued_update_one hu' z₀ j _)).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j = z₀
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj,
          Function.update_of_ne (fun h => hj (Subtype.ext h))]
    have hint : ∀ j : Nbr H v, Integrable (fun ξ : V → ℝ => |u (ξ j) - u' (ξ j)|)
        (Measure.pi fun _ : V => unitμ) := fun j =>
      integrable_of_abs_le (((u.measurable.comp (measurable_pi_apply _)).sub
        (u'.measurable.comp (measurable_pi_apply _))).abs) (‖u‖ + ‖u'‖) fun ξ => by
          rw [abs_abs]
          exact (abs_sub _ _).trans (add_le_add (u.abs_apply_le_norm _) (u'.abs_apply_le_norm _))
    calc ∫ ξ, |formIntegrand H W v (Function.update (fun _ => u) z₀ 1) (Function.update ξ z₀ y)
          - formIntegrand H W v (Function.update (fun _ => u') z₀ 1) (Function.update ξ z₀ y)|
          ∂(Measure.pi fun _ : V => unitμ)
        ≤ ∫ ξ, ∑ j : Nbr H v, |u (ξ j) - u' (ξ j)| ∂(Measure.pi fun _ : V => unitμ) :=
          integral_mono ((integrable_formIntegrand_update v z₀ _ y).sub
            (integrable_formIntegrand_update v z₀ _ y)).abs
            (integrable_finsetSum _ fun j _ => hint j) hpt
      _ = ∑ j : Nbr H v, ∫ t, |u t - u' t| ∂unitμ := by
          rw [integral_finsetSum _ fun j _ => hint j]
          refine Finset.sum_congr rfl fun j _ => ?_
          exact integral_comp_eval (j : V) (f := fun t => |u t - u' t|)
            (abs_sub_integrable u u').aestronglyMeasurable
      _ = (Fintype.card (Nbr H v) : ℝ) * ∫ t, |u t - u' t| ∂unitμ := by simp
  calc ∑ z₀ : Nbr H v, |gradForm H W v z₀ (Function.update (fun _ => u) z₀ 1) y
        - gradForm H W v z₀ (Function.update (fun _ => u') z₀ 1) y|
      ≤ ∑ _z₀ : Nbr H v, (Fintype.card (Nbr H v) : ℝ) * ∫ t, |u t - u' t| ∂unitμ :=
        Finset.sum_le_sum fun z₀ _ => hterm z₀
    _ = (Fintype.card (Nbr H v) : ℝ) ^ 2 * ∫ t, |u t - u' t| ∂unitμ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The derivative of the gradient is bounded from `L¹` to pointwise values:
`|D∇ℛ_W(u)[a](y)| ≤ C_H ‖a‖₁` for `u` with values in `[0,1]`. -/
theorem abs_gradDeriv_apply_le {u : BddMeas} (hu : UnitValued u) (a : BddMeas) (y : ℝ) :
    |gradDeriv H W u a y| ≤ lipConst H * ∫ t, |a t| ∂unitμ := by
  rw [gradDeriv_apply]
  simp only [BddMeas.sum_apply]
  rw [lipConst, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ z₀ i : Nbr H v,
      |gradForm H W v z₀ (Function.update (Function.update (fun _ => u) z₀ 1) i
        (if i = z₀ then 0 else a)) y| ≤ ∫ t, |a t| ∂unitμ := by
    intro z₀ i
    by_cases hi : i = z₀
    · subst hi
      have h0 : gradForm H W v i (Function.update (Function.update (fun _ => u) i 1) i 0) = 0 :=
        (gradForm H W v i).map_update_zero _ _
      rw [if_pos rfl, h0, BddMeas.zero_apply, abs_zero]
      exact integral_nonneg fun _ => abs_nonneg _
    · simp only [hi, if_false]
      rw [gradForm_apply]
      refine (abs_integral_le_integral_abs).trans ?_
      have hpt : ∀ ξ : V → ℝ, |formIntegrand H W v (Function.update (Function.update
          (fun _ => u) z₀ 1) i a) (Function.update ξ z₀ y)| ≤ |a (ξ i)| := by
        intro ξ
        rw [formIntegrand_update, abs_mul,
          Function.update_of_ne (fun h => hi (Subtype.ext h))]
        refine mul_le_of_le_one_right (abs_nonneg _) ?_
        have hP := avoidingProduct_mem_Icc H W v (Function.update ξ z₀ y)
        have hprod : ∏ j ∈ Finset.univ.erase i, (Function.update (fun _ => u) z₀ 1 j)
            ((Function.update ξ z₀ y) j) ∈ Set.Icc (0:ℝ) 1 :=
          ⟨Finset.prod_nonneg fun j _ => (unitValued_update_one hu z₀ j _).1,
            Finset.prod_le_one (fun j _ => (unitValued_update_one hu z₀ j _).1)
              fun j _ => (unitValued_update_one hu z₀ j _).2⟩
        rw [abs_of_nonneg (mul_nonneg hprod.1 hP.1)]
        calc _ ≤ (1:ℝ) * 1 := mul_le_mul hprod.2 hP.2 hP.1 zero_le_one
          _ = 1 := one_mul 1
      have hint : Integrable (fun ξ : V → ℝ => |a (ξ i)|) (Measure.pi fun _ : V => unitμ) :=
        integrable_of_abs_le (a.measurable.comp (measurable_pi_apply _)).abs ‖a‖ fun ξ => by
          rw [abs_abs]; exact a.abs_apply_le_norm _
      calc ∫ ξ, |formIntegrand H W v (Function.update (Function.update (fun _ => u) z₀ 1) i a)
            (Function.update ξ z₀ y)| ∂(Measure.pi fun _ : V => unitμ)
          ≤ ∫ ξ, |a (ξ i)| ∂(Measure.pi fun _ : V => unitμ) :=
            integral_mono (integrable_formIntegrand_update v z₀ _ y).abs hint hpt
        _ = ∫ t, |a t| ∂unitμ :=
            integral_comp_eval (i : V) (f := fun t => |a t|) a.integrable.abs.aestronglyMeasurable
  calc ∑ z₀ : Nbr H v, |∑ i : Nbr H v, gradForm H W v z₀ (Function.update (Function.update
        (fun _ => u) z₀ 1) i (if i = z₀ then 0 else a)) y|
      ≤ ∑ z₀ : Nbr H v, ∑ i : Nbr H v, |gradForm H W v z₀ (Function.update (Function.update
        (fun _ => u) z₀ 1) i (if i = z₀ then 0 else a)) y| :=
        Finset.sum_le_sum fun z₀ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z₀ : Nbr H v, ∑ _i : Nbr H v, ∫ t, |a t| ∂unitμ :=
        Finset.sum_le_sum fun z₀ _ => Finset.sum_le_sum fun i _ => hterm z₀ i
    _ = (Fintype.card (Nbr H v) : ℝ) ^ 2 * ∫ t, |a t| ∂unitμ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end UpperTailMultipodality
