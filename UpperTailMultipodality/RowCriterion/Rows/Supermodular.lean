import UpperTailMultipodality.RowCriterion.Rows.Resampling

/-!
# Supermodularity of rooted densities

The pointwise input to `lem:strict-supermodular`.  For nonnegative `a, b` indexed by a finite
set `S`, the product is supermodular,

`∏ a + ∏ b ≤ ∏ (a ⊓ b) + ∏ (a ⊔ b)`,

and the defect is at least `(a_i - b_i)₊ (b_j - a_j)₊ ∏_{k ≠ i,j} (a_k ⊓ b_k)` for distinct
`i, j ∈ S` (`prod_cross_le`).  Integrating against the product over the edges avoiding `v`
gives the corresponding statements for `ℛ_{v,W}` (`rootedDensity_add_le_inf_add_sup` and
`rootedDensity_cross_le`).
-/

namespace UpperTailMultipodality.Rows

open MeasureTheory Filter

/-! ## Pointwise inequalities -/

/-- The two-coordinate estimate behind `prod_cross_le`: with `P_m ≤ P_a, P_b ≤ P_M` and
`P_a + P_b ≤ P_m + P_M`, the defect of the two-coordinate products is at least
`(a₁ - b₁)₊ (b₂ - a₂)₊ P_m`. -/
theorem two_coordinate_cross_le {a₁ b₁ a₂ b₂ Pm Pa Pb PM : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) (hm0 : 0 ≤ Pm) (hma : Pm ≤ Pa) (hmb : Pm ≤ Pb)
    (haM : Pa ≤ PM) (hbM : Pb ≤ PM) (hsum : Pa + Pb ≤ Pm + PM) :
    max (a₁ - b₁) 0 * max (b₂ - a₂) 0 * Pm
      ≤ (a₁ ⊓ b₁) * ((a₂ ⊓ b₂) * Pm) + (a₁ ⊔ b₁) * ((a₂ ⊔ b₂) * PM)
        - a₁ * (a₂ * Pa) - b₁ * (b₂ * Pb) := by
  have hD : 0 ≤ PM - Pa - Pb + Pm := by linarith
  rcases le_total b₁ a₁ with h1 | h1 <;> rcases le_total a₂ b₂ with h2 | h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), inf_eq_right.mpr h1,
      sup_eq_left.mpr h1, inf_eq_left.mpr h2, sup_eq_right.mpr h2]
    nlinarith [mul_nonneg (mul_nonneg ha₁ hb₂) hD,
      mul_nonneg (mul_nonneg ha₁ (sub_nonneg.2 h2)) (sub_nonneg.2 hma),
      mul_nonneg (mul_nonneg hb₂ (sub_nonneg.2 h1)) (sub_nonneg.2 hmb)]
  · rw [max_eq_right (by linarith : b₂ - a₂ ≤ 0), mul_zero, zero_mul, inf_eq_right.mpr h1,
      sup_eq_left.mpr h1, inf_eq_right.mpr h2, sup_eq_left.mpr h2]
    nlinarith [mul_nonneg (mul_nonneg ha₁ (sub_nonneg.2 h2)) (sub_nonneg.2 haM),
      mul_nonneg (mul_nonneg hb₂ (sub_nonneg.2 h1)) (sub_nonneg.2 haM),
      mul_nonneg (mul_nonneg hb₁ hb₂) hD]
  · rw [max_eq_right (by linarith : a₁ - b₁ ≤ 0), zero_mul, zero_mul, inf_eq_left.mpr h1,
      sup_eq_right.mpr h1, inf_eq_left.mpr h2, sup_eq_right.mpr h2]
    nlinarith [mul_nonneg (mul_nonneg hb₁ (sub_nonneg.2 h2)) (sub_nonneg.2 hbM),
      mul_nonneg (mul_nonneg ha₂ (sub_nonneg.2 h1)) (sub_nonneg.2 hbM),
      mul_nonneg (mul_nonneg ha₁ ha₂) hD]
  · rw [max_eq_right (by linarith : a₁ - b₁ ≤ 0), zero_mul, zero_mul, inf_eq_left.mpr h1,
      sup_eq_right.mpr h1, inf_eq_right.mpr h2, sup_eq_left.mpr h2]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) hm0,
      mul_nonneg (mul_nonneg hb₁ (sub_nonneg.2 h2)) (sub_nonneg.2 hmb),
      mul_nonneg (mul_nonneg ha₂ (sub_nonneg.2 h1)) (sub_nonneg.2 hma),
      mul_nonneg (mul_nonneg hb₁ ha₂) hD]

section Finite

variable {ι : Type*} [DecidableEq ι]

/-- **Supermodularity of the product.**  For nonnegative `a, b`,
`∏ a + ∏ b ≤ ∏ (a ⊓ b) + ∏ (a ⊔ b)`. -/
theorem prod_add_prod_le_prod_inf_add_prod_sup (S : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) :
    ∏ i ∈ S, a i + ∏ i ∈ S, b i ≤ ∏ i ∈ S, (a i ⊓ b i) + ∏ i ∈ S, (a i ⊔ b i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert z T hz ih =>
    have ha' : ∀ i ∈ T, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ T, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hIH := ih ha' hb'
    have haz := ha z (Finset.mem_insert_self z T)
    have hbz := hb z (Finset.mem_insert_self z T)
    have haM : ∏ i ∈ T, a i ≤ ∏ i ∈ T, (a i ⊔ b i) :=
      Finset.prod_le_prod ha' fun i _ => le_sup_left
    have hbM : ∏ i ∈ T, b i ≤ ∏ i ∈ T, (a i ⊔ b i) :=
      Finset.prod_le_prod hb' fun i _ => le_sup_right
    have hma : ∏ i ∈ T, (a i ⊓ b i) ≤ ∏ i ∈ T, a i :=
      Finset.prod_le_prod (fun i hi => le_inf (ha' i hi) (hb' i hi)) fun i _ => inf_le_left
    have hmb : ∏ i ∈ T, (a i ⊓ b i) ≤ ∏ i ∈ T, b i :=
      Finset.prod_le_prod (fun i hi => le_inf (ha' i hi) (hb' i hi)) fun i _ => inf_le_right
    rw [Finset.prod_insert hz, Finset.prod_insert hz, Finset.prod_insert hz,
      Finset.prod_insert hz]
    rcases le_total (b z) (a z) with h | h
    · rw [inf_eq_right.mpr h, sup_eq_left.mpr h]
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 haM),
        mul_nonneg hbz (by linarith : (0:ℝ) ≤ ∏ i ∈ T, (a i ⊓ b i) + ∏ i ∈ T, (a i ⊔ b i)
          - ∏ i ∈ T, a i - ∏ i ∈ T, b i)]
    · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hbM),
        mul_nonneg haz (by linarith : (0:ℝ) ≤ ∏ i ∈ T, (a i ⊓ b i) + ∏ i ∈ T, (a i ⊔ b i)
          - ∏ i ∈ T, a i - ∏ i ∈ T, b i)]

/-- **The cross term of the supermodularity defect.**  For nonnegative `a, b` and distinct
`i, j ∈ S`, the defect `∏ (a ⊓ b) + ∏ (a ⊔ b) - ∏ a - ∏ b` is at least
`(a_i - b_i)₊ (b_j - a_j)₊ ∏_{k ∈ S ∖ {i,j}} (a_k ⊓ b_k)`. -/
theorem prod_cross_le (S : Finset ι) (a b : ι → ℝ) (ha : ∀ k ∈ S, 0 ≤ a k)
    (hb : ∀ k ∈ S, 0 ≤ b k) {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    max (a i - b i) 0 * max (b j - a j) 0 * ∏ k ∈ (S.erase i).erase j, (a k ⊓ b k)
      ≤ ∏ k ∈ S, (a k ⊓ b k) + ∏ k ∈ S, (a k ⊔ b k) - ∏ k ∈ S, a k - ∏ k ∈ S, b k := by
  obtain ⟨T, hT⟩ : ∃ T, T = (S.erase i).erase j := ⟨_, rfl⟩
  have hj' : j ∈ S.erase i := Finset.mem_erase.2 ⟨hij.symm, hj⟩
  have hTS : ∀ k ∈ T, k ∈ S := fun k hk => by
    rw [hT] at hk
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)
  have key : ∀ f : ι → ℝ, ∏ k ∈ S, f k = f i * (f j * ∏ k ∈ T, f k) := fun f => by
    rw [hT, Finset.mul_prod_erase _ _ hj', Finset.mul_prod_erase _ _ hi]
  rw [key (fun k => a k ⊓ b k), key (fun k => a k ⊔ b k), key a, key b, ← hT]
  have ha' : ∀ k ∈ T, 0 ≤ a k := fun k hk => ha k (hTS k hk)
  have hb' : ∀ k ∈ T, 0 ≤ b k := fun k hk => hb k (hTS k hk)
  exact two_coordinate_cross_le (ha i hi) (hb i hi) (ha j hj) (hb j hj)
    (Finset.prod_nonneg fun k hk => le_inf (ha' k hk) (hb' k hk))
    (Finset.prod_le_prod (fun k hk => le_inf (ha' k hk) (hb' k hk)) fun k _ => inf_le_left)
    (Finset.prod_le_prod (fun k hk => le_inf (ha' k hk) (hb' k hk)) fun k _ => inf_le_right)
    (Finset.prod_le_prod ha' fun k _ => le_sup_left)
    (Finset.prod_le_prod hb' fun k _ => le_sup_right)
    (prod_add_prod_le_prod_inf_add_prod_sup T a b ha' hb')

end Finite

/-! ## Rows -/

/-- The pointwise minimum of two rows is a row. -/
theorem isRow_inf {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) : IsRow (u₁ ⊓ u₂) :=
  ⟨hu₁.1.inf hu₂.1, fun y => ⟨le_inf (hu₁.2 y).1 (hu₂.2 y).1, inf_le_left.trans (hu₁.2 y).2⟩⟩

/-- The pointwise maximum of two rows is a row. -/
theorem isRow_sup {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) : IsRow (u₁ ⊔ u₂) :=
  ⟨hu₁.1.sup hu₂.1, fun y => ⟨(hu₁.2 y).1.trans le_sup_left, sup_le (hu₁.2 y).2 (hu₂.2 y).2⟩⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The supermodularity defect of `ℛ_{v,W}` as a single integral. -/
theorem rootedDensity_defect_eq (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) :
    rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
        - rootedDensity H W v u₁ - rootedDensity H W v u₂
      = ∫ ξ, (∏ z ∈ H.neighborFinset v, (u₁ (ξ z) ⊓ u₂ (ξ z))
          + ∏ z ∈ H.neighborFinset v, (u₁ (ξ z) ⊔ u₂ (ξ z))
          - ∏ z ∈ H.neighborFinset v, u₁ (ξ z) - ∏ z ∈ H.neighborFinset v, u₂ (ξ z))
          * avoidingProduct H W v ξ ∂(Measure.pi fun _ : V => unitμ) := by
  have i₁ := integrable_rootedIntegrand H W v hu₁ (H.neighborFinset v)
  have i₂ := integrable_rootedIntegrand H W v hu₂ (H.neighborFinset v)
  have i₃ := integrable_rootedIntegrand H W v (isRow_inf hu₁ hu₂) (H.neighborFinset v)
  have i₄ := integrable_rootedIntegrand H W v (isRow_sup hu₁ hu₂) (H.neighborFinset v)
  have e : ∀ f₁ f₂ f₃ f₄ : (V → ℝ) → ℝ, Integrable f₁ (Measure.pi fun _ : V => unitμ) →
      Integrable f₂ (Measure.pi fun _ : V => unitμ) →
      Integrable f₃ (Measure.pi fun _ : V => unitμ) →
      Integrable f₄ (Measure.pi fun _ : V => unitμ) →
      (∫ ξ, f₃ ξ ∂(Measure.pi fun _ : V => unitμ)) + (∫ ξ, f₄ ξ ∂(Measure.pi fun _ : V => unitμ))
          - (∫ ξ, f₁ ξ ∂(Measure.pi fun _ : V => unitμ))
          - (∫ ξ, f₂ ξ ∂(Measure.pi fun _ : V => unitμ))
        = ∫ ξ, f₃ ξ + f₄ ξ - f₁ ξ - f₂ ξ ∂(Measure.pi fun _ : V => unitμ) := by
    intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄
    rw [integral_sub (by exact (h₃.add h₄).sub h₁) h₂, integral_sub (by exact h₃.add h₄) h₁,
      integral_add h₃ h₄]
  unfold rootedDensity
  rw [e _ _ _ _ i₁ i₂ i₃ i₄]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.inf_apply, Pi.sup_apply]
  ring

/-- **Supermodularity of `ℛ_{v,W}`.** -/
theorem rootedDensity_add_le_inf_add_sup (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) :
    rootedDensity H W v u₁ + rootedDensity H W v u₂
      ≤ rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂) := by
  have h := rootedDensity_defect_eq H W v hu₁ hu₂
  have hnn : 0 ≤ rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
      - rootedDensity H W v u₁ - rootedDensity H W v u₂ := by
    rw [h]
    refine integral_nonneg fun ξ => mul_nonneg ?_ (avoidingProduct_mem_Icc H W v ξ).1
    have := prod_add_prod_le_prod_inf_add_prod_sup (H.neighborFinset v) (fun z => u₁ (ξ z))
      (fun z => u₂ (ξ z)) (fun z _ => (hu₁.2 _).1) (fun z _ => (hu₂.2 _).1)
    linarith
  linarith

/-- **The quantitative supermodularity of `ℛ_{v,W}`.**  If `z₁ ≠ z₂` are neighbours of `v`,
`δ ≤ u₁ ⊓ u₂` almost everywhere and `W ≥ ω` almost everywhere, then the defect of `ℛ_{v,W}`
is at least `δ^{d-2} ω^k ∫(u₁ - u₂)₊ ∫(u₂ - u₁)₊`, where `d` is the degree of `v` and `k` the
number of edges avoiding `v`. -/
theorem rootedDensity_cross_le (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) {δ ω : ℝ} (hδ : 0 ≤ δ) (hω : 0 ≤ ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) (hinf : ∀ᵐ y ∂unitμ, δ ≤ u₁ y ⊓ u₂ y)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ H.neighborFinset v) (hz₂ : z₂ ∈ H.neighborFinset v)
    (hz : z₁ ≠ z₂) :
    δ ^ ((H.neighborFinset v).erase z₁ |>.erase z₂).card
        * ω ^ (H.edgeFinset.filter (fun e => v ∉ e)).card
        * ((∫ y, max (u₁ y - u₂ y) 0 ∂unitμ) * ∫ y, max (u₂ y - u₁ y) 0 ∂unitμ)
      ≤ rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
        - rootedDensity H W v u₁ - rootedDensity H W v u₂ := by
  obtain ⟨T, hT⟩ : ∃ T, T = ((H.neighborFinset v).erase z₁).erase z₂ := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = (H.edgeFinset.filter (fun e => v ∉ e)).card := ⟨_, rfl⟩
  rw [← hT, ← hk]
  have hm₁ : Measurable fun y => max (u₁ y - u₂ y) 0 := (hu₁.1.sub hu₂.1).max measurable_const
  have hm₂ : Measurable fun y => max (u₂ y - u₁ y) 0 := (hu₂.1.sub hu₁.1).max measurable_const
  have hpair := integral_eval_mul_eval (V := V) hz hm₁ hm₂
  rw [rootedDensity_defect_eq H W v hu₁ hu₂, ← hpair, ← integral_const_mul]
  have hTmem : ∀ z ∈ T, z ∈ H.neighborFinset v := fun z hz => by
    rw [hT] at hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hbd₁ : ∀ y, |max (u₁ y - u₂ y) 0| ≤ 1 := fun y => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(hu₁.2 y).2, (hu₂.2 y).1]) zero_le_one
  have hbd₂ : ∀ y, |max (u₂ y - u₁ y) 0| ≤ 1 := fun y => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(hu₂.2 y).2, (hu₁.2 y).1]) zero_le_one
  refine integral_mono_ae ?_ ?_ ?_
  · refine (integrable_pi_of_abs_le ((hm₁.comp (measurable_pi_apply z₁)).mul
      (hm₂.comp (measurable_pi_apply z₂))) 1 fun ξ => ?_).const_mul _
    show |max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0 * max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0| ≤ 1
    rw [abs_mul]
    calc |max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0| * |max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0| ≤ 1 * 1 :=
          mul_le_mul (hbd₁ _) (hbd₂ _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have i₁ := integrable_rootedIntegrand H W v hu₁ (H.neighborFinset v)
    have i₂ := integrable_rootedIntegrand H W v hu₂ (H.neighborFinset v)
    have i₃ := integrable_rootedIntegrand H W v (isRow_inf hu₁ hu₂) (H.neighborFinset v)
    have i₄ := integrable_rootedIntegrand H W v (isRow_sup hu₁ hu₂) (H.neighborFinset v)
    refine (((i₃.add i₄).sub i₁).sub i₂).congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.inf_apply, Pi.sup_apply, Pi.add_apply, Pi.sub_apply]
    ring
  · have hT' : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ∀ z ∈ T, δ ≤ u₁ (ξ z) ⊓ u₂ (ξ z) :=
      (eventually_all_finset _).mpr fun z _ => ae_eval (p := fun y => δ ≤ u₁ y ⊓ u₂ y) hinf z
    filter_upwards [hT', avoidingProduct_ge H W v hω hWω] with ξ hξ hA
    rw [← hk] at hA
    have hcross := prod_cross_le (H.neighborFinset v) (fun z => u₁ (ξ z)) (fun z => u₂ (ξ z))
      (fun z _ => (hu₁.2 _).1) (fun z _ => (hu₂.2 _).1) hz₁ hz₂ hz
    rw [← hT] at hcross
    have hP : δ ^ T.card ≤ ∏ z ∈ T, (u₁ (ξ z) ⊓ u₂ (ξ z)) := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => hδ) hξ
    have hc₁ : 0 ≤ max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0 * max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0 :=
      mul_nonneg (le_max_right _ _) (le_max_right _ _)
    have hA0 : 0 ≤ avoidingProduct H W v ξ := (avoidingProduct_mem_Icc H W v ξ).1
    calc δ ^ T.card * ω ^ k
          * (max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0 * max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0)
        = (max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0 * max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0 * δ ^ T.card)
            * ω ^ k := by ring
      _ ≤ (max (u₁ (ξ z₁) - u₂ (ξ z₁)) 0 * max (u₂ (ξ z₂) - u₁ (ξ z₂)) 0
            * ∏ z ∈ T, (u₁ (ξ z) ⊓ u₂ (ξ z))) * avoidingProduct H W v ξ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hP hc₁) hA (pow_nonneg hω _)
            (mul_nonneg hc₁ (Finset.prod_nonneg fun z hz => le_inf (hu₁.2 _).1 (hu₂.2 _).1))
      _ ≤ _ := mul_le_mul_of_nonneg_right hcross hA0

end UpperTailMultipodality.Rows
