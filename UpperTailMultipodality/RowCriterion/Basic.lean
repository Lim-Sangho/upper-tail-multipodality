import UpperTailMultipodality.RowCriterion.Rows.Interior
import UpperTailMultipodality.RowCriterion.Rows.Supermodular

/-!
# Interiority, supermodularity and total order of row minimizers (`sec:row-criterion`)

`lem:row-interior` and `prop:row-ordering`, for the combined term
`𝒫_W = ∑_j μ_j ℛ_{j,W}` of `eq:row-functional`, assuming some `H_j` with `μ_j > 0` has a vertex
of degree at least two.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Supermodularity of a single total rooted density -/

/-- **Supermodularity of `ℛ_W`**, the sum over `v` of the inclusion–exclusion step in
`prop:row-ordering`. -/
theorem totalRootedDensity_add_le_inf_add_sup (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂) :
    totalRootedDensity H W u₁ + totalRootedDensity H W u₂
      ≤ totalRootedDensity H W (u₁ ⊓ u₂) + totalRootedDensity H W (u₁ ⊔ u₂) := by
  have hdef : totalRootedDensity H W (u₁ ⊓ u₂) + totalRootedDensity H W (u₁ ⊔ u₂)
      - totalRootedDensity H W u₁ - totalRootedDensity H W u₂
      = ∑ v, (rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
        - rootedDensity H W v u₁ - rootedDensity H W v u₂) := by
    unfold totalRootedDensity
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hnn : ∀ v, 0 ≤ rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
      - rootedDensity H W v u₁ - rootedDensity H W v u₂ := fun v => by
    have := Rows.rootedDensity_add_le_inf_add_sup H W v hu₁ hu₂
    linarith
  have := Finset.sum_nonneg fun v (_ : v ∈ Finset.univ) => hnn v
  linarith

/-- **Strict supermodularity of `ℛ_W`** at a graph with a vertex of degree at least two
(`prop:row-ordering`).  If `W ≥ ω > 0` and `u₁ ⊓ u₂ ≥ δ > 0` almost everywhere and `u₁`
and `u₂` cross, the supermodularity defect of `ℛ_W` is positive. -/
theorem totalRootedDensity_lt_inf_add_sup (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) (W : Graphon) {ω δ : ℝ} (hδ0 : 0 < δ) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂)
    (hinf : ∀ᵐ y ∂unitμ, δ ≤ u₁ y ⊓ u₂ y) (h₁ : 0 < unitμ {y | u₂ y < u₁ y})
    (h₂ : 0 < unitμ {y | u₁ y < u₂ y}) :
    totalRootedDensity H W u₁ + totalRootedDensity H W u₂
      < totalRootedDensity H W (u₁ ⊓ u₂) + totalRootedDensity H W (u₁ ⊔ u₂) := by
  have hdef : totalRootedDensity H W (u₁ ⊓ u₂) + totalRootedDensity H W (u₁ ⊔ u₂)
      - totalRootedDensity H W u₁ - totalRootedDensity H W u₂
      = ∑ v, (rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
        - rootedDensity H W v u₁ - rootedDensity H W v u₂) := by
    unfold totalRootedDensity
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hnn : ∀ v, 0 ≤ rootedDensity H W v (u₁ ⊓ u₂) + rootedDensity H W v (u₁ ⊔ u₂)
      - rootedDensity H W v u₁ - rootedDensity H W v u₂ := fun v => by
    have := Rows.rootedDensity_add_le_inf_add_sup H W v hu₁ hu₂
    linarith
  obtain ⟨v₀, hv₀⟩ := hΔ
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hv₀
  obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (H.neighborFinset v₀).card)
  have hcross :=
    Rows.rootedDensity_cross_le H W v₀ hu₁ hu₂ hδ0.le hω.le hWω hinf hz₁ hz₂ hz
  have hint : ∀ {a b : ℝ → ℝ}, IsRow a → IsRow b →
      Integrable (fun y => max (a y - b y) 0) unitμ := fun ha hb =>
    integrable_of_abs_le ((ha.1.sub hb.1).max measurable_const) 1 fun y => by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [(ha.2 y).2, (hb.2 y).1]) zero_le_one
  have hI₁ : 0 < ∫ y, max (u₁ y - u₂ y) 0 ∂unitμ := by
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (u₁ y - u₂ y) 0)
      (fun y => le_max_right _ _) (hint hu₁ hu₂)]
    refine h₁.trans_le (measure_mono fun y hy => ?_)
    exact Function.mem_support.mpr (lt_max_of_lt_left (sub_pos.mpr hy)).ne'
  have hI₂ : 0 < ∫ y, max (u₂ y - u₁ y) 0 ∂unitμ := by
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (u₂ y - u₁ y) 0)
      (fun y => le_max_right _ _) (hint hu₂ hu₁)]
    refine h₂.trans_le (measure_mono fun y hy => ?_)
    exact Function.mem_support.mpr (lt_max_of_lt_left (sub_pos.mpr hy)).ne'
  have hpos : 0 < rootedDensity H W v₀ (u₁ ⊓ u₂) + rootedDensity H W v₀ (u₁ ⊔ u₂)
      - rootedDensity H W v₀ u₁ - rootedDensity H W v₀ u₂ :=
    lt_of_lt_of_le (by positivity) hcross
  have := Finset.sum_pos' (s := Finset.univ) (fun v _ => hnn v) ⟨v₀, Finset.mem_univ _, hpos⟩
  linarith

/-! ### The row functional of a family -/

variable {ι : Type*} [Fintype ι]

/-- **`lem:row-interior`.**  There is `δ ∈ (0,1/2)` such that every `u ∈ 𝓜_W` satisfies
`δ ≤ u ≤ 1 - δ` almost everywhere, together with the Euler–Lagrange equation `eq:row-euler`,
`2J_q'(u) - 2α = ∇𝒫_W(u)` almost everywhere. -/
theorem row_interior (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] (W : Graphon)
    {q α c : ℝ} {μ : ι → ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ u ∈ combinedRowMinimizers Hs W q α μ c,
      (∀ᵐ y ∂unitμ, δ ≤ u y ∧ u y ≤ 1 - δ) ∧
      ∀ᵐ y ∂unitμ, 2 * Jp' q (u y) - 2 * α = combinedRootedGradient Hs W μ u y := by
  obtain ⟨δ, hδ0, hδ1, hJlo, hJhi⟩ :=
    Rows.exists_Jp'_margin hq0 hq1 α (combinedEdgeCard Hs μ)
  refine ⟨δ, hδ0, hδ1, fun u hu => ?_⟩
  obtain ⟨hrow, hval⟩ := hu
  -- `u ≥ δ` almost everywhere: otherwise `max(u, δ)` has a smaller value of `ℱ_W`
  have hlo : ∀ᵐ y ∂unitμ, δ ≤ u y := by
    by_contra hne
    have hpos : 0 < unitμ {y | u y < δ} := by
      rw [ae_iff] at hne
      simpa only [not_le, pos_iff_ne_zero] using hne
    have hv : IsRow (fun y => max (u y) δ) :=
      ⟨hrow.1.max measurable_const, fun y =>
        ⟨le_max_of_le_right hδ0.le, max_le (hrow.2 y).2 (by linarith)⟩⟩
    have hlt : ∀ y, u y < δ → 2 * (Jp q (max (u y) δ) - Jp q (u y))
        - 2 * α * (max (u y) δ - u y)
        + 2 * combinedEdgeCard Hs μ * |max (u y) δ - u y| < 0 := by
      intro y hy
      rw [max_eq_right hy.le, abs_of_pos (sub_pos.mpr hy)]
      have hmvt := Rows.Jp_sub_lt_of_deriv_lt hq0 hq1 (hrow.2 y).1 hy (by linarith)
        (fun z hz1 hz2 => hJlo z (lt_of_le_of_lt (hrow.2 y).1 hz1) hz2)
      nlinarith
    have hF := Rows.rowFunctional_lt_of_pointwise Hs W hq0 hq1 hμ hrow hv hpos
      (fun y => by
        rcases lt_or_ge (u y) δ with hy | hy
        · exact (hlt y hy).le
        · rw [max_eq_left hy]; simp)
      (fun y hy => hlt y hy)
    have := hlow _ hv
    linarith
  -- `u ≤ 1 - δ` almost everywhere: otherwise `min(u, 1 - δ)` has a smaller value of `ℱ_W`
  have hhi : ∀ᵐ y ∂unitμ, u y ≤ 1 - δ := by
    by_contra hne
    have hpos : 0 < unitμ {y | 1 - δ < u y} := by
      rw [ae_iff] at hne
      simpa only [not_le, pos_iff_ne_zero] using hne
    have hv : IsRow (fun y => min (u y) (1 - δ)) :=
      ⟨hrow.1.min measurable_const, fun y =>
        ⟨le_min (hrow.2 y).1 (by linarith), min_le_of_right_le (by linarith)⟩⟩
    have hlt : ∀ y, 1 - δ < u y → 2 * (Jp q (min (u y) (1 - δ)) - Jp q (u y))
        - 2 * α * (min (u y) (1 - δ) - u y)
        + 2 * combinedEdgeCard Hs μ * |min (u y) (1 - δ) - u y| < 0 := by
      intro y hy
      rw [min_eq_right hy.le, abs_of_neg (sub_neg.mpr hy)]
      have hmvt := Rows.lt_Jp_sub_of_lt_deriv (a := 1 - δ) (b := u y) hq0 hq1 (by linarith) hy
        (hrow.2 y).2 (fun z hz1 hz2 => hJhi z hz1 (lt_of_lt_of_le hz2 (hrow.2 y).2))
      nlinarith
    have hF := Rows.rowFunctional_lt_of_pointwise Hs W hq0 hq1 hμ hrow hv hpos
      (fun y => by
        rcases lt_or_ge (1 - δ) (u y) with hy | hy
        · exact (hlt y hy).le
        · rw [min_eq_left hy]; simp)
      (fun y hy => hlt y hy)
    have := hlow _ hv
    linarith
  have hbounds : ∀ᵐ y ∂unitμ, δ ≤ u y ∧ u y ≤ 1 - δ := hlo.and hhi
  refine ⟨hbounds, ?_⟩
  -- the Euler–Lagrange equation: vary `u` in the direction `h = sign(g)` on `{δ ≤ u ≤ 1-δ}`
  obtain ⟨CJ, hCJ0, hCJ⟩ :=
    Rows.exists_abs_Jp'_le (a := δ) (b := 1 - δ) hq0 hq1 hδ0 (by linarith)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun y => 2 * Jp' q (u y) - 2 * α - combinedRootedGradient Hs W μ u y := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact ((((measurable_Jp' q).comp hrow.1).const_mul 2).sub measurable_const).sub
      (Rows.measurable_combinedRootedGradient Hs W μ hrow.1)
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ,
      h = fun y => if δ ≤ u y ∧ u y ≤ 1 - δ then (if 0 ≤ g y then 1 else -1) else 0 :=
    ⟨_, rfl⟩
  have hSm : MeasurableSet {y | δ ≤ u y ∧ u y ≤ 1 - δ} :=
    (measurableSet_le measurable_const hrow.1).inter (measurableSet_le hrow.1 measurable_const)
  have hhm : Measurable h := by
    rw [hh]
    exact Measurable.ite hSm (Measurable.ite (measurableSet_le measurable_const hgm)
      measurable_const measurable_const) measurable_const
  have hhb : ∀ y, |h y| ≤ 1 := by
    intro y
    rw [hh]
    dsimp only
    split_ifs <;> simp
  have hsupp : ∀ y, h y ≠ 0 → δ ≤ u y ∧ u y ≤ 1 - δ := by
    intro y hy
    by_contra hS
    apply hy
    rw [hh]
    exact if_neg hS
  -- `u + t h` is a row for `|t| < δ`, so `t = 0` is a local minimum
  have hmin : IsLocalMin
      (fun t : ℝ => combinedRowFunctional Hs W q α μ (fun y => u y + t * h y)) 0 := by
    have h0 : (fun y => u y + (0:ℝ) * h y) = u := funext fun y => by simp
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ0] with t ht
    have ht' : |t| < δ := by simpa using ht
    show combinedRowFunctional Hs W q α μ (fun y => u y + 0 * h y)
      ≤ combinedRowFunctional Hs W q α μ (fun y => u y + t * h y)
    rw [h0, hval]
    refine hlow _ ⟨hrow.1.add (hhm.const_mul t), fun y => ?_⟩
    show u y + t * h y ∈ Set.Icc 0 1
    by_cases hy : h y = 0
    · rw [hy, mul_zero, add_zero]; exact hrow.2 y
    · obtain ⟨h1, h2⟩ := hsupp y hy
      have hth : |t * h y| ≤ δ := by
        rw [abs_mul]
        calc |t| * |h y| ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hhb y) (abs_nonneg t)
          _ ≤ δ := by linarith
      have := abs_le.mp hth
      constructor <;> linarith [this.1, this.2]
  have hzero := hmin.hasDerivAt_eq_zero
    (Rows.hasDerivAt_rowFunctional_line Hs W (α := α) (μ := μ) hq0 hq1 hδ0 hrow hhm hhb hsupp)
  -- the derivative is `∫ g h = ∫ |g|` over `{δ ≤ u ≤ 1-δ}`
  have iJh : Integrable (fun y => Jp' q (u y) * h y) unitμ := by
    refine integrable_of_abs_le (((measurable_Jp' q).comp hrow.1).mul hhm) CJ
      fun y => ?_
    rw [abs_mul]
    by_cases hy : h y = 0
    · rw [hy]; simpa using hCJ0
    · calc |Jp' q (u y)| * |h y| ≤ CJ * 1 :=
            mul_le_mul (hCJ _ (hsupp y hy)) (hhb y) (abs_nonneg _) hCJ0
        _ = CJ := mul_one _
  have ih : Integrable h unitμ := integrable_of_abs_le hhm 1 hhb
  have iRj : ∀ j : ι, Integrable (fun y => rootedGradient (Hs j) W u y * h y) unitμ := by
    intro j
    refine integrable_of_abs_le ((Rows.measurable_rootedGradient (Hs j) W hrow.1).mul hhm)
      (∑ v, (((Hs j).neighborFinset v).card : ℝ)) fun y => ?_
    have hG := Rows.rootedGradient_mem_Icc (Hs j) W hrow.2 y
    rw [abs_mul, abs_of_nonneg hG.1]
    calc rootedGradient (Hs j) W u y * |h y|
        ≤ (∑ v, (((Hs j).neighborFinset v).card : ℝ)) * 1 :=
          mul_le_mul hG.2 (hhb y) (abs_nonneg _) (hG.1.trans hG.2)
      _ = _ := mul_one _
  have hpt : (fun y => g y * h y) = fun y => 2 * (Jp' q (u y) * h y) - 2 * α * h y
      - ∑ j, μ j * (rootedGradient (Hs j) W u y * h y) := by
    funext y
    have hexp : combinedRootedGradient Hs W μ u y * h y
        = ∑ j, μ j * (rootedGradient (Hs j) W u y * h y) := by
      rw [combinedRootedGradient, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hg]
    rw [sub_mul, sub_mul, hexp]
    ring
  have i₁ : Integrable (fun y => 2 * (Jp' q (u y) * h y)) unitμ := iJh.const_mul 2
  have i₂ : Integrable (fun y => 2 * α * h y) unitμ := ih.const_mul _
  have i₃ : Integrable (fun y => ∑ j, μ j * (rootedGradient (Hs j) W u y * h y)) unitμ :=
    integrable_finsetSum _ fun j _ => (iRj j).const_mul _
  have i₁₂ : Integrable (fun y => 2 * (Jp' q (u y) * h y) - 2 * α * h y) unitμ := i₁.sub i₂
  have iGh : Integrable (fun y => g y * h y) unitμ := by
    rw [hpt]; exact i₁₂.sub i₃
  have hsum : ∫ y, (∑ j, μ j * (rootedGradient (Hs j) W u y * h y)) ∂unitμ
      = ∑ j, μ j * ∫ y, rootedGradient (Hs j) W u y * h y ∂unitμ := by
    rw [integral_finsetSum _ fun j _ => (iRj j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hgh : ∫ y, g y * h y ∂unitμ = 0 := by
    rw [hpt, integral_sub i₁₂ i₃, integral_sub i₁ i₂, integral_const_mul, integral_const_mul,
      hsum]
    exact hzero
  have hghnn : ∀ y, 0 ≤ g y * h y := by
    intro y
    rw [hh]
    dsimp only
    split_ifs with h1 h2
    · simpa using h2
    · nlinarith
    · simp
  have hae := (integral_eq_zero_iff_of_nonneg hghnn iGh).mp hgh
  filter_upwards [hae, hbounds] with y hy hb
  have hhy : h y = if 0 ≤ g y then 1 else -1 := by
    rw [hh]; exact if_pos hb
  have hgy : g y = 0 := by
    simp only [Pi.zero_apply] at hy
    rw [hhy] at hy
    split_ifs at hy <;> simpa using hy
  simp only [hg] at hgy
  linarith

/-- **The lattice inequality of `prop:row-ordering`.**  For `u₁, u₂ ∈ 𝓜_W`,
`𝒫_W(u₁ ⊓ u₂) + 𝒫_W(u₁ ⊔ u₂) ≥ 𝒫_W(u₁) + 𝒫_W(u₂)`, strictly if `u₁` and `u₂` cross.  The
strict inequality uses an index `j₀` with `μ_{j₀} > 0` and `Δ(H_{j₀}) ≥ 2`. -/
theorem strict_supermodular (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀) (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u)
    {u₁ u₂ : ℝ → ℝ} (hu₁ : u₁ ∈ combinedRowMinimizers Hs W q α μ c)
    (hu₂ : u₂ ∈ combinedRowMinimizers Hs W q α μ c) :
    combinedRooted Hs W μ u₁ + combinedRooted Hs W μ u₂
        ≤ combinedRooted Hs W μ (u₁ ⊓ u₂) + combinedRooted Hs W μ (u₁ ⊔ u₂) ∧
      (0 < unitμ {y | u₂ y < u₁ y} → 0 < unitμ {y | u₁ y < u₂ y} →
        combinedRooted Hs W μ u₁ + combinedRooted Hs W μ u₂
          < combinedRooted Hs W μ (u₁ ⊓ u₂) + combinedRooted Hs W μ (u₁ ⊔ u₂)) := by
  have hdef : combinedRooted Hs W μ (u₁ ⊓ u₂) + combinedRooted Hs W μ (u₁ ⊔ u₂)
      - combinedRooted Hs W μ u₁ - combinedRooted Hs W μ u₂
      = ∑ j, μ j * (totalRootedDensity (Hs j) W (u₁ ⊓ u₂)
        + totalRootedDensity (Hs j) W (u₁ ⊔ u₂) - totalRootedDensity (Hs j) W u₁
        - totalRootedDensity (Hs j) W u₂) := by
    unfold combinedRooted
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnn : ∀ j : ι, 0 ≤ μ j * (totalRootedDensity (Hs j) W (u₁ ⊓ u₂)
      + totalRootedDensity (Hs j) W (u₁ ⊔ u₂) - totalRootedDensity (Hs j) W u₁
      - totalRootedDensity (Hs j) W u₂) := fun j => by
    have h := totalRootedDensity_add_le_inf_add_sup (Hs j) W hu₁.1 hu₂.1
    exact mul_nonneg (hμ j) (by linarith)
  refine ⟨?_, fun h₁ h₂ => ?_⟩
  · have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hnn j
    linarith
  · obtain ⟨δ, hδ0, -, hδ⟩ := row_interior Hs W hq0 hq1 hμ hlow
    have hinf : ∀ᵐ y ∂unitμ, δ ≤ u₁ y ⊓ u₂ y := by
      filter_upwards [(hδ u₁ hu₁).1, (hδ u₂ hu₂).1] with y h1 h2
      exact le_inf h1.1 h2.1
    have hstrict := totalRootedDensity_lt_inf_add_sup (Hs j₀) hΔ W hδ0 hω hWω hu₁.1 hu₂.1
      hinf h₁ h₂
    have hpos : 0 < μ j₀ * (totalRootedDensity (Hs j₀) W (u₁ ⊓ u₂)
        + totalRootedDensity (Hs j₀) W (u₁ ⊔ u₂) - totalRootedDensity (Hs j₀) W u₁
        - totalRootedDensity (Hs j₀) W u₂) := mul_pos hμ₀ (by linarith)
    have := Finset.sum_pos' (s := Finset.univ) (fun j _ => hnn j)
      ⟨j₀, Finset.mem_univ _, hpos⟩
    linarith

/-- **`prop:row-ordering`.**  Any two elements of `𝓜_W` are ordered almost everywhere. -/
theorem row_chain (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀) (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u)
    {u₁ u₂ : ℝ → ℝ} (hu₁ : u₁ ∈ combinedRowMinimizers Hs W q α μ c)
    (hu₂ : u₂ ∈ combinedRowMinimizers Hs W q α μ c) :
    u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h12, h21⟩ := hne
  have hpos₁ : 0 < unitμ {y | u₂ y < u₁ y} := by
    rw [Filter.EventuallyLE, ae_iff] at h12
    simpa only [not_le, pos_iff_ne_zero] using h12
  have hpos₂ : 0 < unitμ {y | u₁ y < u₂ y} := by
    rw [Filter.EventuallyLE, ae_iff] at h21
    simpa only [not_le, pos_iff_ne_zero] using h21
  have hstrict :=
    (strict_supermodular Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow hu₁ hu₂).2 hpos₁ hpos₂
  obtain ⟨hr₁, hv₁⟩ := hu₁
  obtain ⟨hr₂, hv₂⟩ := hu₂
  -- the entropy and linear terms of `ℱ_W` are modular
  have hJ : ∫ y, Jp q ((u₁ ⊓ u₂) y) ∂unitμ + ∫ y, Jp q ((u₁ ⊔ u₂) y) ∂unitμ
      = ∫ y, Jp q (u₁ y) ∂unitμ + ∫ y, Jp q (u₂ y) ∂unitμ := by
    rw [← integral_add (Rows.integrable_Jp_row hq0 hq1 (Rows.isRow_inf hr₁ hr₂))
        (Rows.integrable_Jp_row hq0 hq1 (Rows.isRow_sup hr₁ hr₂)),
      ← integral_add (Rows.integrable_Jp_row hq0 hq1 hr₁) (Rows.integrable_Jp_row hq0 hq1 hr₂)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.inf_apply, Pi.sup_apply]
    rcases le_total (u₁ y) (u₂ y) with h | h
    · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
    · rw [inf_eq_right.mpr h, sup_eq_left.mpr h, add_comm]
  have hlin : ∫ y, (u₁ ⊓ u₂) y ∂unitμ + ∫ y, (u₁ ⊔ u₂) y ∂unitμ
      = ∫ y, u₁ y ∂unitμ + ∫ y, u₂ y ∂unitμ := by
    rw [← integral_add (Rows.integrable_of_isRow (Rows.isRow_inf hr₁ hr₂))
        (Rows.integrable_of_isRow (Rows.isRow_sup hr₁ hr₂)),
      ← integral_add (Rows.integrable_of_isRow hr₁) (Rows.integrable_of_isRow hr₂)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.inf_apply, Pi.sup_apply]
    rcases le_total (u₁ y) (u₂ y) with h | h
    · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
    · rw [inf_eq_right.mpr h, sup_eq_left.mpr h, add_comm]
  have hαlin : 2 * α * ∫ y, (u₁ ⊓ u₂) y ∂unitμ + 2 * α * ∫ y, (u₁ ⊔ u₂) y ∂unitμ
      = 2 * α * ∫ y, u₁ y ∂unitμ + 2 * α * ∫ y, u₂ y ∂unitμ := by
    rw [← mul_add, ← mul_add, hlin]
  have h₁ := hlow _ (Rows.isRow_inf hr₁ hr₂)
  have h₂ := hlow _ (Rows.isRow_sup hr₁ hr₂)
  unfold combinedRowFunctional at h₁ h₂ hv₁ hv₂
  linarith

end UpperTailMultipodality
