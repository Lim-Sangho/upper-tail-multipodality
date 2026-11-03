import UpperTailMultipodality.Insertion.Split

/-!
# Splitting `[0,1]` into an inserted block with several rows and the old vertices

`lem:insertion-first-order` inserts `k` new blocks of measures `θc_i` with rows `u_i`.  It is
convenient to describe them by a single new block of measure `θ` carrying a *row kernel*
`U : ℝ → ℝ → ℝ`: the new vertex with label `t` has row `U t`.  Taking `U` constant on the
intervals of a partition of `[0,1]` of lengths `c_i/c` recovers `k` blocks of measures `θc_i`.

This file relabels the points of `[0,1]` accordingly:

* `insertMapRows θ` maps `[0,θ)` affinely onto the label space `[-1,0)` of the new block, and
  `[θ,1]` affinely onto `[0,1]`;
* `map_insertMapRows` — the push-forward of `unitμ` is `θ labelμ + (1-θ) unitμ`, where
  `labelμ` is `unitμ` translated onto `[-1,0]`;
* `integral_gμ_insertMapRows` — the resulting four-term expansion of a double integral;
* `integral_pi_insertMapRows` — the expansion of an integral over `[0,1]^V` as a sum over the
  set `S ⊆ V` of coordinates in the new block, with weights `θ^{|S|}(1-θ)^{N-|S|}`; the
  coordinates in `S` are translated by `-1` (`pinNewRows`).
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

/-- The label of a new vertex: the label space of the new block is `[0,1]` translated
onto `[-1,0]`, so that labels are negative. -/
def newLabel (t : ℝ) : ℝ := t - 1

/-- `newLabel` is measurable. -/
theorem measurable_newLabel : Measurable newLabel := by unfold newLabel; fun_prop

/-- The label measure of the new block: `unitμ` translated onto `[-1,0]`. -/
noncomputable def labelμ : Measure ℝ := unitμ.map newLabel

instance : IsProbabilityMeasure labelμ := by
  constructor
  rw [labelμ, Measure.map_apply measurable_newLabel MeasurableSet.univ, Set.preimage_univ,
    measure_univ]

/-- Almost every point of `[0,1]` lies in `[0,1)`. -/
theorem ae_mem_Ico_unitμ : ∀ᵐ y ∂unitμ, 0 ≤ y ∧ y < 1 := by
  have h1 : unitμ {(1:ℝ)} = 0 := by
    rw [unitμ, Measure.restrict_apply (measurableSet_singleton 1)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  have h2 : ∀ᵐ y ∂unitμ, y ≠ 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) h1
    simp only [Set.mem_ofPred_eq, not_not] at hy
    exact hy
  filter_upwards [ae_restrict_mem measurableSet_Icc, h2] with y hy hy1
  exact ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

/-- Almost every point of `[0,1]^V` has coordinates in `[0,1)`. -/
theorem ae_mem_Ico_pi {V : Type*} [Fintype V] :
    ∀ᵐ y ∂(Measure.pi fun _ : V => unitμ), ∀ v, 0 ≤ y v ∧ y v < 1 := by
  rw [ae_all_iff]
  intro v
  exact (measurePreserving_eval (μ := fun _ : V => unitμ) v).quasiMeasurePreserving.ae
    ae_mem_Ico_unitμ

/-- Almost every point of `[0,1]²` has coordinates in `[0,1)`. -/
theorem ae_mem_Ico_gμ : ∀ᵐ z ∂gμ, (0 ≤ z.1 ∧ z.1 < 1) ∧ (0 ≤ z.2 ∧ z.2 < 1) :=
  Filter.Eventually.and (Measure.quasiMeasurePreserving_fst.ae ae_mem_Ico_unitμ)
    (Measure.quasiMeasurePreserving_snd.ae ae_mem_Ico_unitμ)

/-- The relabelling of the insertion of a block with several rows: `x < θ` (the new block) is
mapped affinely onto `[-1,0)`, and `x ≥ θ` onto `[0,1]`. -/
noncomputable def insertMapRows (θ : ℝ) (x : ℝ) : ℝ :=
  if x < θ then x / θ - 1 else (x - θ) / (1 - θ)

/-- `insertMapRows θ` is measurable. -/
theorem measurable_insertMapRows (θ : ℝ) : Measurable (insertMapRows θ) :=
  Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)

/-- The scaling `x ↦ x/θ` scales Lebesgue measure of preimages by `θ`. -/
theorem volume_preimage_div {θ : ℝ} (hθ0 : 0 < θ) (s : Set ℝ) :
    volume ((fun x : ℝ => x / θ) ⁻¹' s) = ENNReal.ofReal θ * volume s := by
  have hfun : (fun x : ℝ => x / θ) = fun x => θ⁻¹ * x := by
    funext x; rw [div_eq_inv_mul]
  have habs : |θ⁻¹⁻¹| = θ := by rw [inv_inv, abs_of_pos hθ0]
  rw [hfun, Real.volume_preimage_mul_left (inv_ne_zero hθ0.ne'), habs]

/-- The push-forward of `unitμ` under `insertMapRows θ`, evaluated on a measurable set. -/
theorem map_insertMapRows_apply {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    unitμ.map (insertMapRows θ) s
      = ENNReal.ofReal θ * labelμ s + ENNReal.ofReal (1 - θ) * unitμ s := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  rw [Measure.map_apply (measurable_insertMapRows θ) hs, unitμ,
    Measure.restrict_apply (measurable_insertMapRows θ hs), Measure.restrict_apply hs, labelμ,
    Measure.map_apply measurable_newLabel hs, unitμ,
    Measure.restrict_apply (measurable_newLabel hs)]
  have hdecomp : insertMapRows θ ⁻¹' s ∩ Set.Icc 0 1
      = ((fun x : ℝ => x / θ) ⁻¹' (newLabel ⁻¹' s ∩ Set.Ico 0 1))
        ∪ ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_union, Set.mem_Ico,
      insertMapRows]
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      by_cases hxθ : x < θ
      · rw [if_pos hxθ] at hx
        refine Or.inl ⟨hx, div_nonneg hx0 hθ0.le, (div_lt_one hθ0).2 hxθ⟩
      · rw [if_neg hxθ] at hx
        refine Or.inr ⟨hx, div_nonneg (by linarith [not_lt.1 hxθ]) h1.le,
          (div_le_one h1).2 (by linarith)⟩
    · rintro (⟨hx, hx0, hx1⟩ | ⟨hx, hx0, hx1⟩)
      · have hxθ : x < θ := by
          rw [div_lt_one hθ0] at hx1; exact hx1
        have hx0' : 0 ≤ x := by
          rcases div_nonneg_iff.mp hx0 with h | h
          · exact h.1
          · linarith [h.2]
        rw [if_pos hxθ]
        exact ⟨hx, hx0', by linarith⟩
      · have hxθ : θ ≤ x := by
          rcases div_nonneg_iff.mp hx0 with h | h
          · linarith [h.1]
          · linarith [h.2]
        have hx1' : x ≤ 1 := by
          have := (div_le_one h1).1 hx1; linarith
        rw [if_neg (not_lt.2 hxθ)]
        exact ⟨hx, by linarith, hx1'⟩
  have hdisj : Disjoint ((fun x : ℝ => x / θ) ⁻¹' (newLabel ⁻¹' s ∩ Set.Ico 0 1))
      ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, -, hx1⟩ ⟨-, hx0, -⟩
    rw [div_lt_one hθ0] at hx1
    have : (x - θ) / (1 - θ) < 0 := div_neg_of_neg_of_pos (by linarith) h1
    linarith
  have hmeas : MeasurableSet ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1)) :=
    (by fun_prop : Measurable fun x : ℝ => (x - θ) / (1 - θ)) (hs.inter measurableSet_Icc)
  have hnull : volume (newLabel ⁻¹' s ∩ Set.Ico 0 1)
      = volume (newLabel ⁻¹' s ∩ Set.Icc 0 1) :=
    measure_congr ((ae_eq_refl (newLabel ⁻¹' s)).inter Ico_ae_eq_Icc)
  rw [hdecomp, measure_union hdisj hmeas, volume_preimage_affine hθ1, volume_preimage_div hθ0,
    hnull]

/-- **The push-forward of `unitμ` under `insertMapRows θ` is `θ labelμ + (1-θ) unitμ`.** -/
theorem map_insertMapRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unitμ.map (insertMapRows θ)
      = θ.toNNReal • labelμ + (1 - θ).toNNReal • unitμ := by
  ext s hs
  rw [map_insertMapRows_apply hθ0 hθ1 hs, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def]
  rfl

/-- **The four-term expansion of a double integral under the insertion relabelling.** -/
theorem integral_gμ_insertMapRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : ℝ × ℝ → ℝ}
    (hG : Measurable G) {C : ℝ} (hGb : ∀ z, |G z| ≤ C) :
    ∫ z, G (insertMapRows θ z.1, insertMapRows θ z.2) ∂gμ
      = θ ^ 2 * ∫ z, G (newLabel z.1, newLabel z.2) ∂gμ
        + θ * (1 - θ) * ∫ z, G (newLabel z.1, z.2) ∂gμ
        + θ * (1 - θ) * ∫ z, G (z.1, newLabel z.2) ∂gμ
        + (1 - θ) ^ 2 * ∫ z, G z ∂gμ := by
  have hφ := measurable_insertMapRows θ
  have hmap : gμ.map (Prod.map (insertMapRows θ) (insertMapRows θ))
      = (unitμ.map (insertMapRows θ)).prod (unitμ.map (insertMapRows θ)) := by
    rw [gμ, Measure.map_prod_map _ _ hφ hφ]
  have h1 : ∫ z, G (insertMapRows θ z.1, insertMapRows θ z.2) ∂gμ
      = ∫ z, G z ∂((unitμ.map (insertMapRows θ)).prod (unitμ.map (insertMapRows θ))) := by
    rw [← hmap, integral_map (hφ.prodMap hφ).aemeasurable hG.aestronglyMeasurable]
    rfl
  have hint : ∀ (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ], Integrable G μ :=
    fun μ _ => integrable_of_abs_le hG C hGb
  have hadd : ∀ (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∫ z, G z ∂(μ + ν) = ∫ z, G z ∂μ + ∫ z, G z ∂ν :=
    fun μ ν _ _ => integral_add_measure (hint μ) (hint ν)
  -- the four product measures, rewritten as push-forwards of `gμ`
  have e11 : ∫ z, G z ∂(labelμ.prod labelμ) = ∫ z, G (newLabel z.1, newLabel z.2) ∂gμ := by
    have hm : gμ.map (Prod.map newLabel newLabel) = labelμ.prod labelμ := by
      rw [labelμ, Measure.map_prod_map _ _ measurable_newLabel measurable_newLabel, gμ]
    rw [← hm, integral_map (measurable_newLabel.prodMap measurable_newLabel).aemeasurable
      hG.aestronglyMeasurable]
    rfl
  have e12 : ∫ z, G z ∂(labelμ.prod unitμ) = ∫ z, G (newLabel z.1, z.2) ∂gμ := by
    have hm : gμ.map (Prod.map newLabel id) = labelμ.prod unitμ := by
      have hid : labelμ.prod unitμ = (unitμ.map newLabel).prod (unitμ.map id) := by
        rw [Measure.map_id, labelμ]
      rw [hid, Measure.map_prod_map _ _ measurable_newLabel measurable_id, gμ]
    rw [← hm, integral_map (measurable_newLabel.prodMap measurable_id).aemeasurable
      hG.aestronglyMeasurable]
    rfl
  have e21 : ∫ z, G z ∂(unitμ.prod labelμ) = ∫ z, G (z.1, newLabel z.2) ∂gμ := by
    have hm : gμ.map (Prod.map id newLabel) = unitμ.prod labelμ := by
      have hid : unitμ.prod labelμ = (unitμ.map id).prod (unitμ.map newLabel) := by
        rw [Measure.map_id, labelμ]
      rw [hid, Measure.map_prod_map _ _ measurable_id measurable_newLabel, gμ]
    rw [← hm, integral_map (measurable_id.prodMap measurable_newLabel).aemeasurable
      hG.aestronglyMeasurable]
    rfl
  rw [h1, map_insertMapRows hθ0 hθ1]
  simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_add, smul_smul]
  rw [hadd, hadd, hadd]
  simp only [integral_smul_nnreal_measure]
  rw [e11, e12, e21]
  simp only [NNReal.smul_def, NNReal.coe_mul, Real.coe_toNNReal _ hθ0.le,
    Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - θ), smul_eq_mul, gμ]
  ring

/-- **The expansion of a one-dimensional integral under the insertion relabelling.** -/
theorem integral_comp_insertMapRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) {C : ℝ} (hb : ∀ x, |Ψ x| ≤ C) :
    ∫ t, Ψ (insertMapRows θ t) ∂unitμ
      = θ * ∫ s, Ψ (newLabel s) ∂unitμ + (1 - θ) * ∫ s, Ψ s ∂unitμ := by
  have hφ := measurable_insertMapRows θ
  have h1 : ∫ t, Ψ (insertMapRows θ t) ∂unitμ = ∫ x, Ψ x ∂(unitμ.map (insertMapRows θ)) :=
    (integral_map hφ.aemeasurable hΨ.aestronglyMeasurable).symm
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m], Integrable Ψ m :=
    fun m _ => integrable_of_abs_le hΨ C hb
  have hlab : ∫ x, Ψ x ∂labelμ = ∫ s, Ψ (newLabel s) ∂unitμ := by
    rw [labelμ, integral_map measurable_newLabel.aemeasurable hΨ.aestronglyMeasurable]
  rw [h1, map_insertMapRows hθ0 hθ1, integral_add_measure (hint _) (hint _),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, hlab]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hθ0.le,
    Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - θ)]

section Pi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The assignment `y` with the coordinates in `S` moved to the label space of the new block. -/
def pinNewRows (S : Finset V) (y : V → ℝ) : V → ℝ := fun v => if v ∈ S then newLabel (y v) else y v

omit [Fintype V] in
/-- `pinNewRows S` is measurable. -/
theorem measurable_pinNewRows (S : Finset V) : Measurable (pinNewRows S) := by
  refine measurable_pi_lambda _ fun v => ?_
  by_cases h : v ∈ S
  · simp only [pinNewRows, h, if_true]
    exact measurable_newLabel.comp (measurable_pi_apply v)
  · simp only [pinNewRows, h, if_false]; exact measurable_pi_apply v

/-- The push-forward of the product measure under `pinNewRows S` puts `labelμ` on the
coordinates in `S`. -/
theorem map_pinNewRows (S : Finset V) :
    (Measure.pi fun _ : V => unitμ).map (pinNewRows S)
      = Measure.pi fun v => if v ∈ S then labelμ else unitμ := by
  have hf : ∀ v : V, AEMeasurable (fun t : ℝ => if v ∈ S then newLabel t else t) unitμ := by
    intro v
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact measurable_newLabel.aemeasurable
    · simp only [h, if_false]; exact aemeasurable_id
  have key := Measure.pi_map_pi (μ := fun _ : V => unitμ) hf
  have hfun : (fun (x : V → ℝ) (i : V) => if i ∈ S then newLabel (x i) else x i)
      = pinNewRows S := rfl
  rw [hfun] at key
  rw [key]
  congr 1
  funext v
  by_cases h : v ∈ S
  · simp only [h, if_true, labelμ]
  · simp only [h, if_false, Measure.map_id']

/-- **The product of `θ labelμ + (1-θ) unitμ` over `V`**, expanded as a sum over subsets
`S ⊆ V`. -/
theorem pi_map_insertMapRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Measure.pi (fun _ : V => unitμ.map (insertMapRows θ))
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          ((∏ _v ∈ S, θ.toNNReal) * ∏ _v ∈ Sᶜ, (1 - θ).toNNReal) •
            (Measure.pi fun _ : V => unitμ).map (pinNewRows S) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [map_insertMapRows hθ0 hθ1, Measure.add_apply, Measure.smul_apply, map_pinNewRows,
    Measure.pi_pi]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, ENNReal.coe_mul,
    ENNReal.ofNNReal_finsetProd]
  have hsplit : ∏ i, (if i ∈ S then labelμ else unitμ) (s i)
      = (∏ x ∈ S, labelμ (s x)) * ∏ x ∈ Finset.univ \ S, unitμ (s x) := by
    rw [← Finset.prod_mul_prod_compl S, Finset.compl_eq_univ_sdiff]
    congr 1
    · exact Finset.prod_congr rfl fun x hx => by rw [if_pos hx]
    · exact Finset.prod_congr rfl fun x hx => by
        rw [if_neg (Finset.mem_sdiff.1 hx).2]
  rw [hsplit, Finset.compl_eq_univ_sdiff]
  ring

/-- **The expansion of an integral over `[0,1]^V` under the insertion relabelling**: a sum over
the set `S` of coordinates that fall into the new block. -/
theorem integral_pi_insertMapRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : (V → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hGb : ∀ x, |G x| ≤ C) :
    ∫ x, G (fun v => insertMapRows θ (x v)) ∂(Measure.pi fun _ : V => unitμ)
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          θ ^ S.card * (1 - θ) ^ Sᶜ.card
            * ∫ y, G (pinNewRows S y) ∂(Measure.pi fun _ : V => unitμ) := by
  have hφ := measurable_insertMapRows θ
  have hmap : (Measure.pi fun _ : V => unitμ).map (fun x v => insertMapRows θ (x v))
      = Measure.pi (fun _ : V => unitμ.map (insertMapRows θ)) :=
    Measure.pi_map_pi (fun _ => hφ.aemeasurable)
  have hmeasφ : Measurable (fun (x : V → ℝ) v => insertMapRows θ (x v)) :=
    measurable_pi_lambda _ fun v => hφ.comp (measurable_pi_apply v)
  rw [← integral_map hmeasφ.aemeasurable hG.aestronglyMeasurable, hmap,
    pi_map_insertMapRows hθ0 hθ1,
    integral_finsetSum_measure
      (fun S _ => (integrable_of_abs_le hG C hGb).smul_measure_nnreal)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_smul_nnreal_measure,
    integral_map (measurable_pinNewRows S).aemeasurable hG.aestronglyMeasurable]
  simp only [NNReal.smul_def, NNReal.coe_mul, Finset.prod_const, smul_eq_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ hθ0.le, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - θ)]

end Pi

end UpperTailMultipodality.Insertion
