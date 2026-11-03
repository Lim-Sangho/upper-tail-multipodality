import UpperTailMultipodality.RowCriterion.Defs

/-!
# Splitting `[0,1]` into an inserted block and the old vertices

The insertion of `eq:vertex-insertion` and `lem:fixed-insertion` gives the new vertices the
interval `[0,θ)` and rescales the old vertices affinely from `[θ,1]` onto `[0,1]`.  Instead of
rescaling the graphon, this file relabels the points of `[0,1]`:

* `insertMap θ` sends `[0,θ)` to the single point `-1` (a label for the new block) and `[θ,1]`
  affinely onto `[0,1]`;
* `map_insertMap` — the push-forward of `unitμ` under `insertMap θ` is
  `θ δ_{-1} + (1-θ) unitμ`;
* `integral_gμ_insertMap` — the resulting four-term expansion of a double integral;
* `integral_pi_insertMap` — the expansion of an integral over `[0,1]^V` as a sum over the set
  `S ⊆ V` of coordinates in the new block, with weights `θ^{|S|}(1-θ)^{N-|S|}`; the coordinates in
  `S` are replaced by `-1` (`pinNew S`).
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

/-- The relabelling of the insertion: `x < θ` (the new block) goes to `-1`, and `x ≥ θ` goes to
`(x-θ)/(1-θ)`, which maps `[θ,1]` onto `[0,1]`. -/
noncomputable def insertMap (θ : ℝ) (x : ℝ) : ℝ := if x < θ then -1 else (x - θ) / (1 - θ)

/-- `insertMap θ` is measurable. -/
theorem measurable_insertMap (θ : ℝ) : Measurable (insertMap θ) :=
  Measurable.ite measurableSet_Iio measurable_const (by fun_prop)

/-- The affine map `x ↦ (x-θ)/(1-θ)` scales Lebesgue measure of preimages by `1-θ`. -/
theorem volume_preimage_affine {θ : ℝ} (hθ1 : θ < 1) (s : Set ℝ) :
    volume ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' s) = ENNReal.ofReal (1 - θ) * volume s := by
  have h1 : (1 - θ) ≠ 0 := by linarith
  have hfun : (fun x : ℝ => (x - θ) / (1 - θ))
      = (fun x => (1 - θ)⁻¹ * x) ∘ (fun x => x + (-θ)) := by
    funext x; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [hfun, Set.preimage_comp, measure_preimage_add_right,
    Real.volume_preimage_mul_left (inv_ne_zero h1), inv_inv, abs_of_pos (by linarith)]

/-- The push-forward of `unitμ` under `insertMap θ`, evaluated on a measurable set. -/
theorem map_insertMap_apply {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    unitμ.map (insertMap θ) s
      = ENNReal.ofReal θ * Measure.dirac (-1 : ℝ) s + ENNReal.ofReal (1 - θ) * unitμ s := by
  rw [Measure.map_apply (measurable_insertMap θ) hs, unitμ,
    Measure.restrict_apply (measurable_insertMap θ hs), Measure.restrict_apply hs,
    Measure.dirac_apply' _ hs]
  have hdecomp : insertMap θ ⁻¹' s ∩ Set.Icc 0 1
      = ({x | (-1 : ℝ) ∈ s} ∩ Set.Ico 0 θ)
        ∪ (fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_Ico, insertMap]
    have h1 : (0:ℝ) < 1 - θ := by linarith
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      by_cases hxθ : x < θ
      · rw [if_pos hxθ] at hx; exact Or.inl ⟨hx, hx0, hxθ⟩
      · rw [if_neg hxθ] at hx
        refine Or.inr ⟨hx, div_nonneg (by linarith) h1.le, (div_le_one h1).2 (by linarith)⟩
    · rintro (⟨hx, hx0, hxθ⟩ | ⟨hx, hx0, hx1⟩)
      · rw [if_pos hxθ]; exact ⟨hx, hx0, by linarith⟩
      · have hxθ : θ ≤ x := by
          have := (div_nonneg_iff.mp hx0); rcases this with h | h
          · linarith [h.1]
          · linarith [h.2]
        have hx1' : x ≤ 1 := by
          have := (div_le_one h1).1 hx1; linarith
        rw [if_neg (not_lt.2 hxθ)]; exact ⟨hx, by linarith, hx1'⟩
  have hdisj : Disjoint ({x | (-1 : ℝ) ∈ s} ∩ Set.Ico 0 θ)
      ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, -, hxθ⟩ ⟨-, hx0, -⟩
    have h1 : (0:ℝ) < 1 - θ := by linarith
    have : (x - θ) / (1 - θ) < 0 := div_neg_of_neg_of_pos (by linarith) h1
    linarith
  have hmeas : MeasurableSet ((fun x : ℝ => (x - θ) / (1 - θ)) ⁻¹' (s ∩ Set.Icc 0 1)) :=
    (by fun_prop : Measurable fun x : ℝ => (x - θ) / (1 - θ)) (hs.inter measurableSet_Icc)
  rw [hdecomp, measure_union hdisj hmeas, volume_preimage_affine hθ1]
  by_cases h : (-1 : ℝ) ∈ s
  · simp [h, Real.volume_Ico]
  · simp [h]

/-- **The push-forward of `unitμ` under `insertMap θ` is `θ δ_{-1} + (1-θ) unitμ`.** -/
theorem map_insertMap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unitμ.map (insertMap θ)
      = θ.toNNReal • Measure.dirac (-1 : ℝ) + (1 - θ).toNNReal • unitμ := by
  ext s hs
  rw [map_insertMap_apply hθ0 hθ1 hs, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    ENNReal.smul_def, ENNReal.smul_def]
  rfl

/-- **The four-term expansion of a double integral under the insertion relabelling.** -/
theorem integral_gμ_insertMap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : ℝ × ℝ → ℝ}
    (hG : Measurable G) {C : ℝ} (hGb : ∀ z, |G z| ≤ C) :
    ∫ z, G (insertMap θ z.1, insertMap θ z.2) ∂gμ
      = θ ^ 2 * G (-1, -1) + θ * (1 - θ) * ∫ y, G (-1, y) ∂unitμ
        + θ * (1 - θ) * ∫ x, G (x, -1) ∂unitμ + (1 - θ) ^ 2 * ∫ z, G z ∂gμ := by
  have hφ := measurable_insertMap θ
  have hmap : gμ.map (Prod.map (insertMap θ) (insertMap θ))
      = (unitμ.map (insertMap θ)).prod (unitμ.map (insertMap θ)) := by
    rw [gμ, Measure.map_prod_map _ _ hφ hφ]
  have h1 : ∫ z, G (insertMap θ z.1, insertMap θ z.2) ∂gμ
      = ∫ z, G z ∂((unitμ.map (insertMap θ)).prod (unitμ.map (insertMap θ))) := by
    rw [← hmap, integral_map (hφ.prodMap hφ).aemeasurable hG.aestronglyMeasurable]
    rfl
  have hint : ∀ (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ], Integrable G μ :=
    fun μ _ => integrable_of_abs_le hG C hGb
  rw [h1, map_insertMap hθ0 hθ1]
  have hadd : ∀ (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∫ z, G z ∂(μ + ν) = ∫ z, G z ∂μ + ∫ z, G z ∂ν :=
    fun μ ν _ _ => integral_add_measure (hint μ) (hint ν)
  simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_add, smul_smul]
  rw [hadd, hadd, hadd]
  simp only [integral_smul_nnreal_measure, Measure.dirac_prod_dirac]
  simp only [integral_dirac, Measure.dirac_prod, Measure.prod_dirac]
  rw [integral_map (by fun_prop) hG.aestronglyMeasurable,
    integral_map (by fun_prop) hG.aestronglyMeasurable]
  simp only [NNReal.smul_def, NNReal.coe_mul, Real.coe_toNNReal _ hθ0.le,
    Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - θ), smul_eq_mul, gμ]
  ring

section Pi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The assignment `y` with the coordinates in `S` moved to the label `-1` of the new block. -/
def pinNew (S : Finset V) (y : V → ℝ) : V → ℝ := fun v => if v ∈ S then -1 else y v

omit [Fintype V] in
/-- `pinNew S` is measurable. -/
theorem measurable_pinNew (S : Finset V) : Measurable (pinNew S) := by
  refine measurable_pi_lambda _ fun v => ?_
  by_cases h : v ∈ S
  · simp only [pinNew, h, if_true]; exact measurable_const
  · simp only [pinNew, h, if_false]; exact measurable_pi_apply v

/-- The push-forward of the product measure under `pinNew S` puts `δ_{-1}` on the coordinates in
`S`. -/
theorem map_pinNew (S : Finset V) :
    (Measure.pi fun _ : V => unitμ).map (pinNew S)
      = Measure.pi fun v => if v ∈ S then Measure.dirac (-1 : ℝ) else unitμ := by
  have hf : ∀ v : V, AEMeasurable (fun t : ℝ => if v ∈ S then (-1 : ℝ) else t) unitμ := by
    intro v
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact aemeasurable_const
    · simp only [h, if_false]; exact aemeasurable_id
  have key := Measure.pi_map_pi (μ := fun _ : V => unitμ) hf
  have hfun : (fun (x : V → ℝ) (i : V) => if i ∈ S then (-1 : ℝ) else x i) = pinNew S := rfl
  rw [hfun] at key
  rw [key]
  congr 1
  funext v
  by_cases h : v ∈ S
  · simp only [h, if_true, Measure.map_const, measure_univ, one_smul]
  · simp only [h, if_false, Measure.map_id']

/-- **The product of `θ δ_{-1} + (1-θ) unitμ` over `V`**, expanded as a sum over subsets `S ⊆ V`. -/
theorem pi_map_insertMap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Measure.pi (fun _ : V => unitμ.map (insertMap θ))
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          ((∏ _v ∈ S, θ.toNNReal) * ∏ _v ∈ Sᶜ, (1 - θ).toNNReal) •
            (Measure.pi fun _ : V => unitμ).map (pinNew S) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [map_insertMap hθ0 hθ1, Measure.add_apply, Measure.smul_apply, map_pinNew,
    Measure.pi_pi]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib, ENNReal.coe_mul,
    ENNReal.ofNNReal_finsetProd]
  have hsplit : ∏ i, (if i ∈ S then Measure.dirac (-1 : ℝ) else unitμ) (s i)
      = (∏ x ∈ S, Measure.dirac (-1 : ℝ) (s x)) * ∏ x ∈ Finset.univ \ S, unitμ (s x) := by
    rw [← Finset.prod_mul_prod_compl S, Finset.compl_eq_univ_sdiff]
    congr 1
    · exact Finset.prod_congr rfl fun x hx => by rw [if_pos hx]
    · exact Finset.prod_congr rfl fun x hx => by
        rw [if_neg (Finset.mem_sdiff.1 hx).2]
  rw [hsplit, Finset.compl_eq_univ_sdiff]
  ring

/-- **The expansion of an integral over `[0,1]^V` under the insertion relabelling**: a sum over
the set `S` of coordinates that fall into the new block. -/
theorem integral_pi_insertMap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : (V → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hGb : ∀ x, |G x| ≤ C) :
    ∫ x, G (fun v => insertMap θ (x v)) ∂(Measure.pi fun _ : V => unitμ)
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          θ ^ S.card * (1 - θ) ^ Sᶜ.card
            * ∫ y, G (pinNew S y) ∂(Measure.pi fun _ : V => unitμ) := by
  have hφ := measurable_insertMap θ
  have hmap : (Measure.pi fun _ : V => unitμ).map (fun x v => insertMap θ (x v))
      = Measure.pi (fun _ : V => unitμ.map (insertMap θ)) :=
    Measure.pi_map_pi (fun _ => hφ.aemeasurable)
  have hmeasφ : Measurable (fun (x : V → ℝ) v => insertMap θ (x v)) :=
    measurable_pi_lambda _ fun v => hφ.comp (measurable_pi_apply v)
  rw [← integral_map hmeasφ.aemeasurable hG.aestronglyMeasurable, hmap, pi_map_insertMap hθ0 hθ1,
    integral_finsetSum_measure
      (fun S _ => (integrable_of_abs_le hG C hGb).smul_measure_nnreal)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_smul_nnreal_measure,
    integral_map (measurable_pinNew S).aemeasurable hG.aestronglyMeasurable]
  simp only [NNReal.smul_def, NNReal.coe_mul, Finset.prod_const, smul_eq_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ hθ0.le, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - θ)]

end Pi

end UpperTailMultipodality.Insertion
