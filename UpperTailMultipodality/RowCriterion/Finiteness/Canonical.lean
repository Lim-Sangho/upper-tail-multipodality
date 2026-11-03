import UpperTailMultipodality.RowCriterion.Finiteness.Branch
import UpperTailMultipodality.RowCriterion.Basic

/-!
# Canonical representatives of row minimizers

Every `u ∈ 𝓜_W` satisfies the Euler–Lagrange equation `eq:row-euler` almost everywhere, hence
agrees almost everywhere with the *canonical representative*
`σ(ℓ(q) + α + (1/2)∇𝒫_W(u))`, which satisfies it everywhere and takes values in a fixed compact
subinterval of `(0,1)`.  Canonical representatives are Lipschitz in the mean
(`dist_canonical_le`), because two minimizers are ordered (`prop:row-ordering`), so that their
`L¹`-distance is the difference of their means, and `eq:gradient-lipschitz` applies.

The file also contains the topological endgame of `lem:row-finite`: a bounded closed subset of
`ℝ` all of whose accumulation points are interior is finite.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {W : Graphon} {q α : ℝ} {μ : ι → ℝ}

/-- **The topological endgame of `lem:row-finite`.**  A bounded closed subset of `ℝ` each of
whose accumulation points has a neighbourhood inside the set is finite. -/
theorem finite_of_accPt_interior {A : Set ℝ} (hbdd : A ⊆ Set.Icc 0 1) (hclosed : IsClosed A)
    (hnbhd : ∀ a ∈ A, AccPt a (𝓟 A) → ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A) : A.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hcompact : IsCompact A := isCompact_Icc.of_isClosed_subset hclosed hbdd
  have hA'ne : (derivedSet A).Nonempty := by
    obtain ⟨x, -, hx⟩ := hinf.exists_accPt_of_subset_isCompact hcompact (subset_refl A)
    exact ⟨x, hx⟩
  have hA'sub : derivedSet A ⊆ A := (isClosed_iff_derivedSet_subset A).mp hclosed
  have hA'closed : IsClosed (derivedSet A) := isClosed_derivedSet A
  have hA'bdd : BddAbove (derivedSet A) :=
    (bddAbove_Icc (a := (0:ℝ)) (b := 1)).mono (hA'sub.trans hbdd)
  set s := sSup (derivedSet A) with hs
  have hsA' : s ∈ derivedSet A := hA'closed.csSup_mem hA'ne hA'bdd
  obtain ⟨ε, hε, hsub⟩ := hnbhd s (hA'sub hsA') hsA'
  have hNbhd : Set.Ioo (s - ε) (s + ε) ∈ 𝓝 (s + ε / 2) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hacc2 : AccPt (s + ε / 2) (𝓟 A) := by
    have hle : 𝓝[≠] (s + ε / 2) ≤ 𝓟 A :=
      le_principal_iff.mpr (mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset hNbhd hsub))
    have : 𝓝[≠] (s + ε / 2) ⊓ 𝓟 A = 𝓝[≠] (s + ε / 2) := inf_eq_left.mpr hle
    rw [AccPt, this]
    infer_instance
  have hle2 : s + ε / 2 ≤ s := le_csSup hA'bdd hacc2
  linarith

/-- The row functional depends only on the almost everywhere class. -/
theorem rowFunctional_congr_ae (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) (q α : ℝ) (μ : ι → ℝ) {u v : ℝ → ℝ} (hu : IsRow u) (hv : IsRow v)
    (huv : u =ᵐ[unitμ] v) :
    combinedRowFunctional Hs W q α μ u = combinedRowFunctional Hs W q α μ v := by
  have h1 : ∫ y, Jp q (u y) ∂unitμ = ∫ y, Jp q (v y) ∂unitμ :=
    integral_congr_ae (huv.mono fun y hy => by
      show Jp q (u y) = Jp q (v y)
      rw [hy])
  have h2 : ∫ y, u y ∂unitμ = ∫ y, v y ∂unitμ := integral_congr_ae huv
  have hz : ∫ y, |u y - v y| ∂unitμ = 0 := by
    rw [← integral_zero ℝ ℝ (μ := unitμ)]
    refine integral_congr_ae (huv.mono fun y hy => ?_)
    show |u y - v y| = 0
    rw [hy, sub_self, abs_zero]
  have h3 : combinedRooted Hs W μ u = combinedRooted Hs W μ v := by
    unfold combinedRooted
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlip := rooted_lipschitz (Hs j) W hu hv
    rw [hz, mul_zero] at hlip
    have habs := abs_nonneg (totalRootedDensity (Hs j) W u - totalRootedDensity (Hs j) W v)
    have heq : |totalRootedDensity (Hs j) W u - totalRootedDensity (Hs j) W v| = 0 :=
      le_antisymm hlip habs
    have := abs_eq_zero.mp heq
    have : totalRootedDensity (Hs j) W u = totalRootedDensity (Hs j) W v := by linarith
    rw [this]
  rw [combinedRowFunctional, combinedRowFunctional, h1, h2, h3]

/-- A row as an element of `BddMeas`. -/
noncomputable def rowToBdd {u : ℝ → ℝ} (hu : IsRow u) : BddMeas :=
  BddMeas.ofRow hu.1 hu.2

@[simp] theorem coe_rowToBdd {u : ℝ → ℝ} (hu : IsRow u) : ⇑(rowToBdd hu) = u := rfl

/-- A row has values in `[0,1]`. -/
theorem unitValued_rowToBdd {u : ℝ → ℝ} (hu : IsRow u) : UnitValued (rowToBdd hu) := hu.2

variable (Hs W q α μ) in
/-- **The canonical representative** `σ(ℓ(q) + α + (1/2)∇𝒫_W(u))` of a row. -/
noncomputable def canonical (u : BddMeas) : BddMeas :=
  BddMeas.sigma (elArg Hs W q α μ (u, 0))

/-- The value of the canonical representative at a point. -/
theorem canonical_apply (u : BddMeas) (y : ℝ) :
    canonical Hs W q α μ u y
      = BddMeas.logistic (α + logit q + 1 / 2 * combinedGradE Hs W μ u y) := by
  rw [canonical, BddMeas.sigma_apply, elArg_apply]
  simp only
  ring_nf

/-- The canonical representative takes values in a fixed compact subinterval of `(0,1)`. -/
theorem canonical_mem_Icc (hμ : ∀ j, 0 ≤ μ j) {u : BddMeas} (hu : UnitValued u) (y : ℝ) :
    canonical Hs W q α μ u y ∈ Set.Icc (BddMeas.logistic (α + logit q))
      (BddMeas.logistic (α + logit q + 1 / 2 * combinedLipConst Hs μ)) := by
  rw [canonical_apply]
  have hg := combinedGradE_mem_Icc (Hs := Hs) (W := W) hμ hu y
  constructor
  · refine logistic_monotone ?_
    have := hg.1
    linarith
  · refine logistic_monotone ?_
    have := hg.2
    linarith

/-- The canonical representative of a minimizer agrees with it almost everywhere. -/
theorem canonical_ae_eq (hq0 : 0 < q) (hq1 : q < 1) {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1 / 2)
    {u : ℝ → ℝ} (hu : IsRow u) (hbounds : ∀ᵐ y ∂unitμ, δ ≤ u y ∧ u y ≤ 1 - δ)
    (hEL : ∀ᵐ y ∂unitμ, 2 * Jp' q (u y) - 2 * α = combinedRootedGradient Hs W μ u y) :
    ⇑(canonical Hs W q α μ (rowToBdd hu)) =ᵐ[unitμ] u := by
  filter_upwards [hbounds, hEL] with y hy hELy
  rw [canonical_apply]
  have hu0 : 0 < u y := lt_of_lt_of_le hδ0 hy.1
  have hu1 : u y < 1 := lt_of_le_of_lt hy.2 (by linarith)
  have hgrad : combinedGradE Hs W μ (rowToBdd hu) y = combinedRootedGradient Hs W μ u y :=
    combinedGradE_apply _ y
  rw [hgrad]
  have hJ : Jp' q (u y) = α + 1 / 2 * combinedRootedGradient Hs W μ u y := by linarith
  have := logistic_Jp' hq0 hq1 hu0 hu1
  rw [hJ] at this
  rw [show α + logit q + 1 / 2 * combinedRootedGradient Hs W μ u y
      = α + 1 / 2 * combinedRootedGradient Hs W μ u y + logit q by ring]
  exact this

/-- The canonical representative is a fixed point of the Euler–Lagrange map. -/
theorem canonical_fix (hμ : ∀ j, 0 ≤ μ j) (hq0 : 0 < q) (hq1 : q < 1) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {u : ℝ → ℝ} (hu : IsRow u)
    (hbounds : ∀ᵐ y ∂unitμ, δ ≤ u y ∧ u y ≤ 1 - δ)
    (hEL : ∀ᵐ y ∂unitμ, 2 * Jp' q (u y) - 2 * α = combinedRootedGradient Hs W μ u y) :
    canonical Hs W q α μ (rowToBdd hu)
      = BddMeas.sigma (elArg Hs W q α μ (canonical Hs W q α μ (rowToBdd hu), 0)) := by
  have hae := canonical_ae_eq (Hs := Hs) (W := W) (μ := μ) hq0 hq1 hδ0 hδ1 hu hbounds hEL
  have hgrad : combinedGradE Hs W μ (canonical Hs W q α μ (rowToBdd hu))
      = combinedGradE Hs W μ (rowToBdd hu) := by
    have hUV1 : UnitValued (canonical Hs W q α μ (rowToBdd hu)) := by
      intro y
      rw [canonical_apply]
      exact ⟨(BddMeas.logistic_pos _).le, (BddMeas.logistic_lt_one _).le⟩
    have hUV2 : UnitValued (rowToBdd hu) := unitValued_rowToBdd hu
    have hzero : ∫ t, |canonical Hs W q α μ (rowToBdd hu) t - (rowToBdd hu) t| ∂unitμ = 0 := by
      rw [← integral_zero ℝ ℝ (μ := unitμ)]
      refine integral_congr_ae ?_
      filter_upwards [hae] with t ht
      show |canonical Hs W q α μ (rowToBdd hu) t - (rowToBdd hu) t| = 0
      have hru : (rowToBdd hu) t = u t := rfl
      rw [hru, ht, sub_self, abs_zero]
    refine BddMeas.ext fun y => ?_
    have hb := abs_combinedGradE_sub_le (Hs := Hs) (W := W) hμ hUV1 hUV2 y
    rw [hzero, mul_zero] at hb
    have := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    linarith
  have key : ∀ x y : BddMeas, combinedGradE Hs W μ x = combinedGradE Hs W μ y →
      canonical Hs W q α μ x = canonical Hs W q α μ y := by
    intro x y hxy
    unfold canonical elArg
    simp only
    rw [hxy]
  show canonical Hs W q α μ (rowToBdd hu)
      = canonical Hs W q α μ (canonical Hs W q α μ (rowToBdd hu))
  exact key _ _ hgrad.symm

/-- For ordered rows, the `L¹` distance is the difference of the means. -/
theorem integral_abs_sub_eq {u v : ℝ → ℝ} (hu : IsRow u) (hv : IsRow v) (hord : u ≤ᵐ[unitμ] v) :
    ∫ y, |u y - v y| ∂unitμ = |(∫ y, u y ∂unitμ) - ∫ y, v y ∂unitμ| := by
  have hiu : Integrable u unitμ := integrable_of_abs_le hu.1 1 fun y => by
    rw [abs_le]; exact ⟨by linarith [(hu.2 y).1], (hu.2 y).2⟩
  have hiv : Integrable v unitμ := integrable_of_abs_le hv.1 1 fun y => by
    rw [abs_le]; exact ⟨by linarith [(hv.2 y).1], (hv.2 y).2⟩
  have h1 : ∫ y, |u y - v y| ∂unitμ = ∫ y, (v y - u y) ∂unitμ := by
    refine integral_congr_ae ?_
    filter_upwards [hord] with y hy
    show |u y - v y| = v y - u y
    rw [abs_of_nonpos (by linarith)]
    ring
  have h2 : ∫ y, (v y - u y) ∂unitμ = (∫ y, v y ∂unitμ) - ∫ y, u y ∂unitμ :=
    integral_sub hiv hiu
  have h3 : (0:ℝ) ≤ (∫ y, v y ∂unitμ) - ∫ y, u y ∂unitμ := by
    have := integral_mono_ae hiu hiv hord
    linarith
  rw [h1, h2, abs_of_nonpos (by linarith)]
  ring

/-- **Canonical representatives are Lipschitz in the mean.** -/
theorem dist_canonical_le (hμ : ∀ j, 0 ≤ μ j) {u v : ℝ → ℝ} (hu : IsRow u) (hv : IsRow v)
    (hord : u ≤ᵐ[unitμ] v ∨ v ≤ᵐ[unitμ] u) :
    ‖canonical Hs W q α μ (rowToBdd hu) - canonical Hs W q α μ (rowToBdd hv)‖
      ≤ 1 / 8 * combinedLipConst Hs μ * |(∫ y, u y ∂unitμ) - ∫ y, v y ∂unitμ| := by
  have hL1 : ∫ y, |u y - v y| ∂unitμ = |(∫ y, u y ∂unitμ) - ∫ y, v y ∂unitμ| := by
    rcases hord with h | h
    · exact integral_abs_sub_eq hu hv h
    · have := integral_abs_sub_eq hv hu h
      rw [show ∫ y, |v y - u y| ∂unitμ = ∫ y, |u y - v y| ∂unitμ from
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          show |v y - u y| = |u y - v y|
          rw [abs_sub_comm])] at this
      rw [this, abs_sub_comm]
  refine BddMeas.norm_le_of_forall
    (mul_nonneg (mul_nonneg (by norm_num) (combinedLipConst_nonneg hμ)) (abs_nonneg _))
    fun y => ?_
  have hgrad := abs_combinedGradE_sub_le (Hs := Hs) (W := W) hμ (unitValued_rowToBdd hu)
    (unitValued_rowToBdd hv) y
  have hcoe : ∫ t, |(rowToBdd hu) t - (rowToBdd hv) t| ∂unitμ = ∫ t, |u t - v t| ∂unitμ := rfl
  rw [hcoe, hL1] at hgrad
  have hlogis :=
    abs_logistic_sub_le (α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hu) y)
      (α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hv) y)
  have harg : |(α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hu) y)
      - (α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hv) y)|
      = 1 / 2 * |combinedGradE Hs W μ (rowToBdd hu) y
        - combinedGradE Hs W μ (rowToBdd hv) y| := by
    rw [show (α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hu) y)
        - (α + logit q + 1 / 2 * combinedGradE Hs W μ (rowToBdd hv) y)
        = (1 / 2 : ℝ) * (combinedGradE Hs W μ (rowToBdd hu) y
          - combinedGradE Hs W μ (rowToBdd hv) y) by ring, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  rw [harg] at hlogis
  rw [BddMeas.sub_apply, canonical_apply, canonical_apply]
  refine hlogis.trans ?_
  have hLip0 : 0 ≤ combinedLipConst Hs μ := combinedLipConst_nonneg hμ
  have habs : 0 ≤ |(∫ y, u y ∂unitμ) - ∫ y, v y ∂unitμ| := abs_nonneg _
  nlinarith [abs_nonneg (combinedGradE Hs W μ (rowToBdd hu) y
    - combinedGradE Hs W μ (rowToBdd hv) y)]

/-- **The row functional is Lipschitz** on functions with values in a compact subinterval of
`(0,1)`. -/
theorem exists_lipschitz_rowFunctionalE (hq0 : 0 < q) (hq1 : q < 1) {lo hi : ℝ} (hlo : 0 < lo)
    (hhi : hi < 1) (hμ : ∀ j, 0 ≤ μ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b b' : BddMeas, (∀ y, b y ∈ Set.Icc lo hi) →
      (∀ y, b' y ∈ Set.Icc lo hi) →
      |rowFunctionalE Hs W q α μ b - rowFunctionalE Hs W q α μ b'| ≤ C * ‖b - b'‖ := by
  classical
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    (f := Jp' q) (fun z hz => (hasDerivAt_Jp' hq0 hq1 (hlo.trans_le hz.1)
      (hz.2.trans_lt hhi)).continuousAt.continuousWithinAt)
  set K : ℝ := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ z ∈ Set.Icc lo hi, |Jp' q z| ≤ K := by
    intro z hz
    have := hK₀ z hz
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hJlip : ∀ x ∈ Set.Icc lo hi, ∀ x' ∈ Set.Icc lo hi, |Jp q x - Jp q x'| ≤ K * |x - x'| := by
    intro x hx x' hx'
    have hderiv : ∀ z ∈ Set.Icc lo hi, HasDerivWithinAt (Jp q) (Jp' q z) (Set.Icc lo hi) z :=
      fun z hz => (hasDerivAt_Jp hq0 hq1 (hlo.trans_le hz.1)
        (hz.2.trans_lt hhi)).hasDerivWithinAt
    have hbound : ∀ z ∈ Set.Icc lo hi, ‖Jp' q z‖ ≤ K := fun z hz => by
      rw [Real.norm_eq_abs]; exact hK z hz
    have := (convex_Icc lo hi).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hx' hx
    simpa [Real.norm_eq_abs] using this
  have hM0 : (0:ℝ) ≤ combinedEdgeCard Hs μ := combinedEdgeCard_nonneg hμ
  refine ⟨2 * K + 2 * |α| + 2 * combinedEdgeCard Hs μ, by positivity, ?_⟩
  intro b b' hb hb'
  have hrow : ∀ (w : BddMeas), (∀ y, w y ∈ Set.Icc lo hi) → IsRow (⇑w) := by
    intro w hw
    refine ⟨w.measurable, fun y => ⟨?_, ?_⟩⟩
    · exact hlo.le.trans (hw y).1
    · exact (hw y).2.trans hhi.le
  have hnorm : ∀ y, |b y - b' y| ≤ ‖b - b'‖ := fun y => BddMeas.abs_apply_sub_le_dist b b' y
  have hL1 : ∫ y, |b y - b' y| ∂unitμ ≤ ‖b - b'‖ := by
    calc ∫ y, |b y - b' y| ∂unitμ ≤ ∫ _y, ‖b - b'‖ ∂unitμ :=
          integral_mono ((b - b').integrable.abs) (integrable_const _) hnorm
      _ = ‖b - b'‖ := by simp
  -- the entropy term
  have hJint : |(∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ| ≤ K * ‖b - b'‖ := by
    have hsub : (∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ
        = ∫ y, (Jp q (b y) - Jp q (b' y)) ∂unitμ :=
      (integral_sub (integrable_Jp_comp hq0 hq1 b) (integrable_Jp_comp hq0 hq1 b')).symm
    rw [hsub]
    calc |∫ y, (Jp q (b y) - Jp q (b' y)) ∂unitμ|
        ≤ ∫ y, |Jp q (b y) - Jp q (b' y)| ∂unitμ := abs_integral_le_integral_abs
      _ ≤ ∫ y, K * |b y - b' y| ∂unitμ := by
          refine integral_mono ((integrable_Jp_comp hq0 hq1 b).sub
            (integrable_Jp_comp hq0 hq1 b')).abs (((b - b').integrable.abs).const_mul K)
            fun y => ?_
          exact hJlip _ (hb y) _ (hb' y)
      _ = K * ∫ y, |b y - b' y| ∂unitμ := integral_const_mul _ _
      _ ≤ K * ‖b - b'‖ := mul_le_mul_of_nonneg_left hL1 hK0
  -- the mean term
  have hmint : |(∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ| ≤ ‖b - b'‖ := by
    have hsub : (∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ = ∫ y, (b y - b' y) ∂unitμ :=
      (integral_sub b.integrable b'.integrable).symm
    rw [hsub]
    exact (abs_integral_le_integral_abs).trans hL1
  -- the rooted density term
  have hrint : |combinedRooted Hs W μ ⇑b - combinedRooted Hs W μ ⇑b'|
      ≤ 2 * combinedEdgeCard Hs μ * ‖b - b'‖ := by
    refine (combined_lipschitz Hs W hμ (hrow b hb) (hrow b' hb')).trans ?_
    exact mul_le_mul_of_nonneg_left hL1 (by positivity)
  rw [rowFunctionalE, rowFunctionalE, combinedRowFunctional, combinedRowFunctional]
  have hexp : (2 * ∫ y, Jp q (b y) ∂unitμ - 2 * α * ∫ y, b y ∂unitμ
        - combinedRooted Hs W μ ⇑b)
      - (2 * ∫ y, Jp q (b' y) ∂unitμ - 2 * α * ∫ y, b' y ∂unitμ
        - combinedRooted Hs W μ ⇑b')
      = 2 * ((∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ)
        - 2 * α * ((∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ)
        - (combinedRooted Hs W μ ⇑b - combinedRooted Hs W μ ⇑b') := by ring
  rw [hexp]
  have h1 : |2 * ((∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ)| ≤ 2 * (K * ‖b - b'‖) := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hJint (by norm_num)
  have h2 : |2 * α * ((∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ)| ≤ 2 * |α| * ‖b - b'‖ := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hmint (by positivity)
  have h3 : |combinedRooted Hs W μ ⇑b - combinedRooted Hs W μ ⇑b'|
      ≤ 2 * combinedEdgeCard Hs μ * ‖b - b'‖ := hrint
  calc |2 * ((∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ)
        - 2 * α * ((∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ)
        - (combinedRooted Hs W μ ⇑b - combinedRooted Hs W μ ⇑b')|
      ≤ |2 * ((∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ)|
        + |2 * α * ((∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ)|
        + |combinedRooted Hs W μ ⇑b - combinedRooted Hs W μ ⇑b'| := by
        refine (abs_sub _ _).trans ?_
        have := abs_sub (2 * ((∫ y, Jp q (b y) ∂unitμ) - ∫ y, Jp q (b' y) ∂unitμ))
          (2 * α * ((∫ y, b y ∂unitμ) - ∫ y, b' y ∂unitμ))
        linarith
    _ ≤ (2 * K + 2 * |α| + 2 * combinedEdgeCard Hs μ) * ‖b - b'‖ := by
        have := h1
        have := h2
        have := h3
        nlinarith [norm_nonneg (b - b')]


/-- **The set of means of minimizers is closed**, because the canonical representatives are
Lipschitz in the mean and the row functional is continuous. -/
theorem isClosed_of_lipschitz_rep (hq0 : 0 < q) (hq1 : q < 1) (hμ0 : ∀ j, 0 ≤ μ j)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    {cval : ℝ} {A : Set ℝ} {rep : ℝ → BddMeas}
    (hmem : ∀ a ∈ A, ∀ y, rep a y ∈ Set.Icc lo hi)
    (hval : ∀ a ∈ A, rowFunctionalE Hs W q α μ (rep a) = cval)
    (hmeanA : ∀ a ∈ A, BddMeas.integ (rep a) = a)
    {L : ℝ} (hL0 : 0 ≤ L) (hlip : ∀ a ∈ A, ∀ a' ∈ A, ‖rep a - rep a'‖ ≤ L * |a - a'|)
    (hext : ∀ b : BddMeas, (∀ y, b y ∈ Set.Icc lo hi) → rowFunctionalE Hs W q α μ b = cval →
      BddMeas.integ b ∈ A) :
    IsClosed A := by
  obtain ⟨C, hC0, hCf⟩ := exists_lipschitz_rowFunctionalE (Hs := Hs) (W := W) (α := α) (μ := μ)
    hq0 hq1 hlo hhi hμ0
  rw [← closure_subset_iff_isClosed]
  intro a ha
  obtain ⟨seq, hseq, htend⟩ := mem_closure_iff_seq_limit.mp ha
  -- the canonical representatives form a Cauchy sequence
  have hcauchy : CauchySeq (fun n => rep (seq n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp htend.cauchySeq (ε / (L + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := hN m hm n hn
    rw [Real.dist_eq] at hd
    have h1 : ‖rep (seq m) - rep (seq n)‖ ≤ L * |seq m - seq n| :=
      hlip _ (hseq m) _ (hseq n)
    rw [dist_eq_norm]
    have hpos : (0:ℝ) < L + 1 := by linarith
    have h2 : L * |seq m - seq n| < ε := by
      calc L * |seq m - seq n| ≤ (L + 1) * |seq m - seq n| := by
            nlinarith [abs_nonneg (seq m - seq n)]
        _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hd hpos
        _ = ε := by field_simp
    exact lt_of_le_of_lt h1 h2
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hnormtend : Filter.Tendsto (fun n => ‖rep (seq n) - b‖) Filter.atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hb
  -- pointwise convergence
  have hpt : ∀ y, Filter.Tendsto (fun n => rep (seq n) y) Filter.atTop (𝓝 (b y)) := by
    intro y
    have h1 : Filter.Tendsto (fun n => rep (seq n) y - b y) Filter.atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by
        rw [Real.norm_eq_abs]
        exact BddMeas.abs_apply_sub_le_dist _ _ y) hnormtend
    have := h1.add (tendsto_const_nhds (x := b y) (f := Filter.atTop (α := ℕ)))
    simpa using this
  -- the limit has values in the interval
  have hbmem : ∀ y, b y ∈ Set.Icc lo hi := by
    intro y
    constructor
    · exact ge_of_tendsto (hpt y) (Filter.Eventually.of_forall fun n => (hmem _ (hseq n) y).1)
    · exact le_of_tendsto (hpt y) (Filter.Eventually.of_forall fun n => (hmem _ (hseq n) y).2)
  -- the value of the functional
  have hbval : rowFunctionalE Hs W q α μ b = cval := by
    have hFtend : Filter.Tendsto (fun n => rowFunctionalE Hs W q α μ (rep (seq n))) Filter.atTop
        (𝓝 (rowFunctionalE Hs W q α μ b)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (?_ : Filter.Tendsto
        (fun n => C * ‖rep (seq n) - b‖) Filter.atTop (𝓝 0))
      · rw [Real.dist_eq]
        exact hCf _ _ (hmem _ (hseq n)) hbmem
      · have := hnormtend.const_mul C
        simpa using this
    have hconst : Filter.Tendsto (fun n => rowFunctionalE Hs W q α μ (rep (seq n))) Filter.atTop
        (𝓝 cval) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      exact (hval _ (hseq n)).symm
    exact tendsto_nhds_unique hFtend hconst
  -- the mean of the limit
  have hbmean : BddMeas.integ b = a := by
    have h1 : Filter.Tendsto (fun n => BddMeas.integ (rep (seq n))) Filter.atTop
        (𝓝 (BddMeas.integ b)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hnormtend
      rw [Real.dist_eq, ← map_sub, BddMeas.integ_apply]
      calc |∫ y, (rep (seq n) - b) y ∂unitμ| ≤ ∫ y, |(rep (seq n) - b) y| ∂unitμ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _y, ‖rep (seq n) - b‖ ∂unitμ :=
            integral_mono ((rep (seq n) - b).integrable.abs) (integrable_const _)
              (fun y => BddMeas.abs_apply_le_norm _ y)
        _ = ‖rep (seq n) - b‖ := by simp
    have h2 : Filter.Tendsto (fun n => BddMeas.integ (rep (seq n))) Filter.atTop (𝓝 a) := by
      refine Filter.Tendsto.congr' ?_ htend
      filter_upwards with n
      exact (hmeanA _ (hseq n)).symm
    exact tendsto_nhds_unique h1 h2
  rw [← hbmean]
  exact hext b hbmem hbval


/-- A bounded measurable row is its own `BddMeas` element. -/
theorem rowToBdd_coe (w : BddMeas) (hw : IsRow (⇑w)) : rowToBdd hw = w := BddMeas.ext fun _ => rfl

/-- Two ordered rows with the same mean agree almost everywhere. -/
theorem ae_eq_of_mean_eq {u v : ℝ → ℝ} (hu : IsRow u) (hv : IsRow v)
    (hord : u ≤ᵐ[unitμ] v ∨ v ≤ᵐ[unitμ] u)
    (hmean : ∫ y, u y ∂unitμ = ∫ y, v y ∂unitμ) : u =ᵐ[unitμ] v := by
  have key : ∀ {f g : ℝ → ℝ}, IsRow f → IsRow g → f ≤ᵐ[unitμ] g →
      (∫ y, f y ∂unitμ) = ∫ y, g y ∂unitμ → f =ᵐ[unitμ] g := by
    intro f g hf hg hfg hmn
    have hif : Integrable f unitμ := integrable_of_abs_le hf.1 1 fun y => by
      rw [abs_le]; exact ⟨by linarith [(hf.2 y).1], (hf.2 y).2⟩
    have hig : Integrable g unitμ := integrable_of_abs_le hg.1 1 fun y => by
      rw [abs_le]; exact ⟨by linarith [(hg.2 y).1], (hg.2 y).2⟩
    have hnn : 0 ≤ᵐ[unitμ] fun y => g y - f y := by
      filter_upwards [hfg] with y hy
      simp only [Pi.zero_apply]
      linarith
    have hzero : ∫ y, (g y - f y) ∂unitμ = 0 := by
      rw [integral_sub hig hif, hmn, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hig.sub hif)).mp hzero
    filter_upwards [this] with y hy
    simp only [Pi.zero_apply] at hy
    linarith
  rcases hord with h | h
  · exact key hu hv h hmean
  · exact (key hv hu h hmean.symm).symm


end UpperTailMultipodality
