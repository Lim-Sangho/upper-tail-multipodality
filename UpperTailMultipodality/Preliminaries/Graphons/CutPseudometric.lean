import UpperTailMultipodality.Preliminaries.Graphons.CutContinuity

/-!
# The cut distance is a pseudometric, and the graphon space is compact

`sec:graphons` states that the cut distance
`δ_□(U,W) = inf_σ ‖U - W^σ‖_□` induces a metric on the quotient `W̃₀` of the graphons by weak
isomorphism (`δ_□ = 0`), that the resulting metric space is compact, and that "unique up to
relabelling" means unique in `W̃₀`.  This file proves:

* `cutDist_self`, `cutDist_nonneg`, `cutDist_comm`, `cutDist_triangle` — `cutDist` is a
  pseudometric, recorded as `cutPseudoMetricSpace`;
* `cutDist_eq_zero_of_relabel` — graphons that agree a.e. after a relabelling are at cut
  distance `0`, so a statement "`W'` is `W` up to relabelling" gives equality in `W̃₀`;
* `GraphonSpace` — the quotient `W̃₀`, a metric space, and `GraphonSpace.compactSpace`, its
  compactness, from the sequential-compactness axiom `cut_seqCompact`.

The pseudometric axioms rest on three properties of the cut norm of a bounded measurable
kernel, proved first: it is invariant under relabelling (`cutNorm_comp_relabel`), under
negation (`cutNorm_neg`), and subadditive (`cutNorm_add_le`).
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

/-! ### The cut norm of a bounded measurable kernel -/

/-- A set integral against `unitμ` of a function bounded by `C` is bounded by `C`. -/
theorem abs_setIntegral_le_of_abs_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (S : Set ℝ) :
    |∫ x in S, f x ∂unitμ| ≤ C := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := unitμ) (s := S) (f := f)
    (measure_lt_top unitμ S) fun x _ => by simpa [Real.norm_eq_abs] using hC x
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right ((abs_nonneg _).trans (hC 0)) measureReal_le_one)

/-- An iterated integral of a bounded kernel over `S × T` is bounded by the bound. -/
theorem abs_iter_integral_le {U : ℝ → ℝ → ℝ} {C : ℝ} (hC : ∀ x y, |U x y| ≤ C) (S T : Set ℝ) :
    |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ| ≤ C :=
  abs_setIntegral_le_of_abs_le (fun x => abs_setIntegral_le_of_abs_le (hC x) T) S

/-- The set of values whose supremum is `cutNorm U` is nonempty. -/
theorem cutNorm_set_nonempty (U : ℝ → ℝ → ℝ) :
    {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
      v = |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ|}.Nonempty :=
  ⟨_, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, rfl⟩

/-- For a bounded kernel, the set of values whose supremum is `cutNorm U` is bounded above. -/
theorem cutNorm_set_bddAbove {U : ℝ → ℝ → ℝ} {C : ℝ} (hC : ∀ x y, |U x y| ≤ C) :
    BddAbove {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
      v = |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ|} := by
  refine ⟨C, ?_⟩
  rintro v ⟨S, T, -, -, rfl⟩
  exact abs_iter_integral_le hC S T

/-- The cut norm is nonnegative. -/
theorem cutNorm_nonneg (U : ℝ → ℝ → ℝ) : 0 ≤ cutNorm U := by
  refine Real.sSup_nonneg fun v hv => ?_
  obtain ⟨S, T, -, -, rfl⟩ := hv
  exact abs_nonneg _

/-- For a bounded kernel, every `|∫_S ∫_T U|` is at most `cutNorm U`. -/
theorem abs_iter_integral_le_cutNorm {U : ℝ → ℝ → ℝ} {C : ℝ} (hC : ∀ x y, |U x y| ≤ C)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ| ≤ cutNorm U :=
  le_csSup (cutNorm_set_bddAbove hC) ⟨S, T, hS, hT, rfl⟩

/-- The cut norm of the zero kernel is `0`. -/
theorem cutNorm_zero : cutNorm (fun _ _ => 0) = 0 := by
  refine le_antisymm (csSup_le (cutNorm_set_nonempty _) ?_) (cutNorm_nonneg _)
  rintro v ⟨S, T, -, -, rfl⟩
  simp

/-- The cut norm is invariant under negation of the kernel. -/
theorem cutNorm_neg (U : ℝ → ℝ → ℝ) : cutNorm (fun x y => -U x y) = cutNorm U := by
  unfold cutNorm
  simp only [integral_neg, abs_neg]

/-- **Change of variables in the iterated integral.**  For a measure-preserving `σ`, the
iterated integral of `U ∘ (σ × σ)` over `σ⁻¹ S × σ⁻¹ T` is that of `U` over `S × T`. -/
theorem iter_integral_comp_preimage {σ : ℝ → ℝ} (hσ : MeasurePreserving σ unitμ unitμ)
    {U : ℝ → ℝ → ℝ} (hU : Measurable (Function.uncurry U)) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ x in σ ⁻¹' S, ∫ y in σ ⁻¹' T, U (σ x) (σ y) ∂unitμ ∂unitμ)
      = ∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ := by
  have hinner : ∀ x, (∫ y in σ ⁻¹' T, U x (σ y) ∂unitμ) = ∫ y in T, U x y ∂unitμ := by
    intro x
    have hm : Measurable (U x) := hU.comp measurable_prodMk_left
    have h := setIntegral_map (μ := unitμ) hT hm.aestronglyMeasurable hσ.measurable.aemeasurable
    rw [hσ.map_eq] at h
    exact h.symm
  have hg : StronglyMeasurable fun x => ∫ y in T, U x y ∂unitμ :=
    hU.stronglyMeasurable.integral_prod_right
  have h := setIntegral_map (μ := unitμ) hS hg.aestronglyMeasurable hσ.measurable.aemeasurable
  rw [hσ.map_eq] at h
  rw [h]
  exact setIntegral_congr_fun (hσ.measurable hS) fun x _ => hinner (σ x)

/-- Pulling a kernel back along a measure-preserving map does not decrease its cut norm. -/
theorem cutNorm_le_comp {σ : ℝ → ℝ} (hσ : MeasurePreserving σ unitμ unitμ)
    {U : ℝ → ℝ → ℝ} (hU : Measurable (Function.uncurry U)) {C : ℝ} (hC : ∀ x y, |U x y| ≤ C) :
    cutNorm U ≤ cutNorm fun x y => U (σ x) (σ y) := by
  refine csSup_le (cutNorm_set_nonempty _) ?_
  rintro v ⟨S, T, hS, hT, rfl⟩
  rw [← iter_integral_comp_preimage hσ hU hS hT]
  exact abs_iter_integral_le_cutNorm (U := fun x y => U (σ x) (σ y)) (fun x y => hC _ _)
    (hσ.measurable hS) (hσ.measurable hT)

/-- **The cut norm is relabelling invariant**: `‖U^σ‖_□ = ‖U‖_□` for a bounded measurable
kernel `U` and a relabelling `σ`. -/
theorem cutNorm_comp_relabel {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    {U : ℝ → ℝ → ℝ} (hU : Measurable (Function.uncurry U)) {C : ℝ} (hC : ∀ x y, |U x y| ≤ C) :
    (cutNorm fun x y => U (σ x) (σ y)) = cutNorm U := by
  obtain ⟨τ, hτ, -, hστ⟩ := hσ.exists_symm
  refine le_antisymm ?_ (cutNorm_le_comp hσ.measurePreserving hU hC)
  have hUσ : Measurable (Function.uncurry fun x y => U (σ x) (σ y)) :=
    hU.comp (hσ.measurable.prodMap hσ.measurable)
  refine (cutNorm_le_comp hτ.measurePreserving hUσ (fun x y => hC _ _)).trans (le_of_eq ?_)
  refine cutNorm_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hστ,
    Measure.quasiMeasurePreserving_snd.ae hστ] with z h1 h2
  simp only [h1, h2]

/-- **The cut norm is subadditive** on bounded measurable kernels. -/
theorem cutNorm_add_le {U V : ℝ → ℝ → ℝ} (hU : Measurable (Function.uncurry U))
    (hV : Measurable (Function.uncurry V)) {C D : ℝ} (hC : ∀ x y, |U x y| ≤ C)
    (hD : ∀ x y, |V x y| ≤ D) :
    (cutNorm fun x y => U x y + V x y) ≤ cutNorm U + cutNorm V := by
  refine csSup_le (cutNorm_set_nonempty _) ?_
  rintro v ⟨S, T, hS, hT, rfl⟩
  have hinner : ∀ x, (∫ y in T, (U x y + V x y) ∂unitμ)
      = (∫ y in T, U x y ∂unitμ) + ∫ y in T, V x y ∂unitμ := fun x =>
    integral_add (integrable_of_abs_le (hU.comp measurable_prodMk_left) C (hC x))
      (integrable_of_abs_le (hV.comp measurable_prodMk_left) D (hD x))
  have hgU : Integrable (fun x => ∫ y in T, U x y ∂unitμ) (unitμ.restrict S) :=
    integrable_of_abs_le (hU.stronglyMeasurable.integral_prod_right).measurable C
      fun x => abs_setIntegral_le_of_abs_le (hC x) T
  have hgV : Integrable (fun x => ∫ y in T, V x y ∂unitμ) (unitμ.restrict S) :=
    integrable_of_abs_le (hV.stronglyMeasurable.integral_prod_right).measurable D
      fun x => abs_setIntegral_le_of_abs_le (hD x) T
  simp only [hinner]
  rw [integral_add hgU hgV]
  exact (abs_add_le _ _).trans (add_le_add (abs_iter_integral_le_cutNorm hC hS hT)
    (abs_iter_integral_le_cutNorm hD hS hT))

/-! ### The kernels `W - W'^σ` -/

/-- The difference of two graphon values has absolute value at most `1`. -/
theorem abs_graphon_sub_le_one (W W' : Graphon) (a b c d : ℝ) :
    |W.toFun a b - W'.toFun c d| ≤ 1 :=
  abs_sub_le_iff.2 ⟨by linarith [W.le_one' a b, W'.nonneg' c d],
    by linarith [W.nonneg' a b, W'.le_one' c d]⟩

/-- A graphon pulled back along a relabelling is measurable. -/
theorem measurable_graphon_comp (W : Graphon) {σ : ℝ → ℝ} (hσ : IsRelabelling σ) :
    Measurable (Function.uncurry fun x y => W.toFun (σ x) (σ y)) :=
  W.meas'.comp (hσ.measurable.prodMap hσ.measurable)

/-- The kernel `W - W'^σ` is measurable. -/
theorem measurable_graphon_sub_comp (W W' : Graphon) {σ : ℝ → ℝ} (hσ : IsRelabelling σ) :
    Measurable (Function.uncurry fun x y => W.toFun x y - W'.toFun (σ x) (σ y)) :=
  W.meas'.sub (measurable_graphon_comp W' hσ)

/-- The set of values whose infimum is `cutDist W W'` is nonempty (take `σ = id`). -/
theorem cutDist_set_nonempty (W W' : Graphon) :
    {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
      v = cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y))}.Nonempty :=
  ⟨_, id, isRelabelling_id, rfl⟩

/-- The set of values whose infimum is `cutDist W W'` is bounded below by `0`. -/
theorem cutDist_set_bddBelow (W W' : Graphon) :
    BddBelow {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
      v = cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y))} := by
  refine ⟨0, ?_⟩
  rintro v ⟨σ, -, rfl⟩
  exact cutNorm_nonneg _

/-- `δ_□(W,W') ≤ ‖W - W'^σ‖_□` for every relabelling `σ`. -/
theorem cutDist_le_cutNorm (W W' : Graphon) {σ : ℝ → ℝ} (hσ : IsRelabelling σ) :
    cutDist W W' ≤ cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y)) :=
  csInf_le (cutDist_set_bddBelow W W') ⟨σ, hσ, rfl⟩

/-- An `ε`-approximate minimiser for the infimum defining `cutDist W W'`. -/
theorem exists_cutNorm_lt_cutDist_add (W W' : Graphon) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
      cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y)) < cutDist W W' + ε := by
  obtain ⟨v, ⟨σ, hσ, rfl⟩, hv⟩ :=
    exists_lt_of_csInf_lt (cutDist_set_nonempty W W') (lt_add_of_pos_right (cutDist W W') hε)
  exact ⟨σ, hσ, hv⟩

/-! ### The pseudometric axioms -/

theorem cutDist_self (W : Graphon) : cutDist W W = 0 := by
  refine le_antisymm ((cutDist_le_cutNorm W W isRelabelling_id).trans (le_of_eq ?_))
    (Real.sInf_nonneg ?_)
  · simpa using cutNorm_zero
  · rintro v ⟨σ, -, rfl⟩
    exact cutNorm_nonneg _

theorem cutDist_nonneg (W W' : Graphon) : 0 ≤ cutDist W W' := by
  refine Real.sInf_nonneg ?_
  rintro v ⟨σ, -, rfl⟩
  exact cutNorm_nonneg _

/-- One half of `cutDist_comm`: `‖W - W'^σ‖_□ = ‖W' - W^τ‖_□` for the a.e. inverse `τ`. -/
theorem cutDist_comm_le (W W' : Graphon) : cutDist W' W ≤ cutDist W W' := by
  refine le_csInf (cutDist_set_nonempty W W') ?_
  rintro v ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, -, hστ⟩ := hσ.exists_symm
  refine (cutDist_le_cutNorm W' W hτ).trans (le_of_eq ?_)
  rw [← cutNorm_neg, ← cutNorm_comp_relabel hτ (measurable_graphon_sub_comp W W' hσ)
    (fun x y => abs_graphon_sub_le_one W W' _ _ _ _)]
  refine cutNorm_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hστ,
    Measure.quasiMeasurePreserving_snd.ae hστ] with z h1 h2
  simp only [h1, h2, neg_sub]

theorem cutDist_comm (W W' : Graphon) : cutDist W W' = cutDist W' W :=
  le_antisymm (cutDist_comm_le W' W) (cutDist_comm_le W W')

theorem cutDist_triangle (W₁ W₂ W₃ : Graphon) : cutDist W₁ W₃ ≤ cutDist W₁ W₂ + cutDist W₂ W₃ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨σ₁, hσ₁, h₁⟩ := exists_cutNorm_lt_cutDist_add W₁ W₂ (half_pos hε)
  obtain ⟨σ₂, hσ₂, h₂⟩ := exists_cutNorm_lt_cutDist_add W₂ W₃ (half_pos hε)
  have hsplit : (fun x y => W₁.toFun x y - W₃.toFun (σ₂ (σ₁ x)) (σ₂ (σ₁ y)))
      = fun x y => (W₁.toFun x y - W₂.toFun (σ₁ x) (σ₁ y))
        + (W₂.toFun (σ₁ x) (σ₁ y) - W₃.toFun (σ₂ (σ₁ x)) (σ₂ (σ₁ y))) := by
    funext x y; ring
  have hrel : (cutNorm fun x y =>
        W₂.toFun (σ₁ x) (σ₁ y) - W₃.toFun (σ₂ (σ₁ x)) (σ₂ (σ₁ y)))
      = cutNorm fun x y => W₂.toFun x y - W₃.toFun (σ₂ x) (σ₂ y) :=
    cutNorm_comp_relabel (U := fun x y => W₂.toFun x y - W₃.toFun (σ₂ x) (σ₂ y)) hσ₁
      (measurable_graphon_sub_comp W₂ W₃ hσ₂) (fun x y => abs_graphon_sub_le_one W₂ W₃ _ _ _ _)
  have hadd := cutNorm_add_le
    (U := fun x y => W₁.toFun x y - W₂.toFun (σ₁ x) (σ₁ y))
    (V := fun x y => W₂.toFun (σ₁ x) (σ₁ y) - W₃.toFun (σ₂ (σ₁ x)) (σ₂ (σ₁ y)))
    (measurable_graphon_sub_comp W₁ W₂ hσ₁)
    ((measurable_graphon_comp W₂ hσ₁).sub (measurable_graphon_comp W₃ (hσ₂.comp hσ₁)))
    (fun x y => abs_graphon_sub_le_one W₁ W₂ _ _ _ _)
    (fun x y => abs_graphon_sub_le_one W₂ W₃ _ _ _ _)
  rw [← hsplit, hrel] at hadd
  calc cutDist W₁ W₃
      ≤ cutNorm fun x y => W₁.toFun x y - W₃.toFun (σ₂ (σ₁ x)) (σ₂ (σ₁ y)) :=
        cutDist_le_cutNorm W₁ W₃ (hσ₂.comp hσ₁)
    _ ≤ _ := hadd
    _ < (cutDist W₁ W₂ + ε / 2) + (cutDist W₂ W₃ + ε / 2) := add_lt_add h₁ h₂
    _ = cutDist W₁ W₂ + cutDist W₂ W₃ + ε := by ring

/-- Graphons that agree almost everywhere after a relabelling are at cut distance `0`. -/
theorem cutDist_eq_zero_of_relabel {W W' : Graphon} {σ : ℝ → ℝ} (hσ : IsRelabelling σ)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) : cutDist W' W = 0 := by
  refine le_antisymm ((cutDist_le_cutNorm W' W hσ).trans (le_of_eq ?_)) (cutDist_nonneg W' W)
  rw [← cutNorm_zero]
  refine cutNorm_congr_ae ?_
  filter_upwards [h] with z hz
  simp only [hz, sub_self]

/-- The cut distance as a pseudometric on graphons. -/
@[instance_reducible]
noncomputable def cutPseudoMetricSpace : PseudoMetricSpace Graphon where
  dist := cutDist
  dist_self := cutDist_self
  dist_comm := cutDist_comm
  dist_triangle := cutDist_triangle

/-- **The graphon space `W̃₀`**: graphons modulo weak isomorphism `δ_□ = 0`, with the cut metric. -/
def GraphonSpace : Type := @SeparationQuotient Graphon cutPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable instance : MetricSpace GraphonSpace :=
  @SeparationQuotient.instMetricSpace Graphon cutPseudoMetricSpace

/-- **`(W̃₀, δ_□)` is compact.** -/
theorem GraphonSpace.compactSpace : CompactSpace GraphonSpace := by
  let := cutPseudoMetricSpace
  have hseq : SeqCompactSpace Graphon := by
    refine ⟨fun x _ => ?_⟩
    obtain ⟨φ, Wlim, hφ, hlim⟩ := cut_seqCompact x
    exact ⟨Wlim, Set.mem_univ _, φ, hφ, tendsto_iff_dist_tendsto_zero.2 hlim⟩
  have : CompactSpace Graphon := compactSpace_iff_seqCompactSpace.2 hseq
  exact SeparationQuotient.surjective_mk.compactSpace SeparationQuotient.continuous_mk

end UpperTailMultipodality
