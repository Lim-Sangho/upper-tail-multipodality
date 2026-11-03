import UpperTailMultipodality.Insertion.Construction

/-!
# Rows attain the lower bound almost everywhere

The last step of `lem:global-row-minimality` and `lem:fixed-insertion`: by Fubini's theorem and
`eq:rooted-average`, `∫₀¹ ℱ_W(W_x) dx = 2I_q(W) - 2α e(W) - μN t(H,W)`.  Hence, if `ℱ_W` is
bounded below on all rows by this value, almost every row of `W` attains it.
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rows of a graphon are rows. -/
theorem isRow_row (W : Graphon) (x : ℝ) : IsRow (W.row x) :=
  ⟨W.meas'.comp measurable_prodMk_left, fun y => W.mem_Icc x y⟩

/-- `ℛ_{v,W}(u) ∈ [0,1]` for a row `u`. -/
theorem rootedDensity_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    {u : ℝ → ℝ} (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) :
    rootedDensity H W v u ∈ Set.Icc (0:ℝ) 1 := by
  have hpt : ∀ ξ : V → ℝ,
      (∏ z ∈ H.neighborFinset v, u (ξ z)) * avoidingProduct H W v ξ ∈ Set.Icc (0:ℝ) 1 := by
    intro ξ
    have h1 : ∏ z ∈ H.neighborFinset v, u (ξ z) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun z _ => (hu _).1,
        Finset.prod_le_one (fun z _ => (hu _).1) fun z _ => (hu _).2⟩
    have h2 : avoidingProduct H W v ξ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun e _ => (edgeVal_mem_Icc W.symm' W.mem_Icc ξ e).1,
        Finset.prod_le_one (fun e _ => (edgeVal_mem_Icc W.symm' W.mem_Icc ξ e).1)
          fun e _ => (edgeVal_mem_Icc W.symm' W.mem_Icc ξ e).2⟩
    exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩
  refine ⟨integral_nonneg fun ξ => (hpt ξ).1, ?_⟩
  have h := integral_mono_of_nonneg (ae_of_all _ fun ξ => (hpt ξ).1)
    (integrable_const (μ := Measure.pi fun _ : V => unitμ) (1:ℝ))
    (ae_of_all _ fun ξ => (hpt ξ).2)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

/-- `x ↦ ℛ_{v,W}(W_x)` is measurable. -/
theorem measurable_rootedDensity_row (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) : Measurable fun x => rootedDensity H W v (W.row x) := by
  have hjoint : Measurable fun p : ℝ × (V → ℝ) =>
      (∏ z ∈ H.neighborFinset v, W.toFun p.1 (p.2 z)) * avoidingProduct H W v p.2 := by
    refine (Finset.measurable_prod _ fun z _ => ?_).mul ?_
    · have hp : Measurable fun p : ℝ × (V → ℝ) => (p.1, p.2 z) :=
        measurable_fst.prodMk ((measurable_pi_apply z).comp measurable_snd)
      exact W.measurable_uncurry.comp hp
    · exact (Finset.measurable_prod _ fun e _ =>
        measurable_edgeVal W.symm' W.measurable_uncurry e).comp measurable_snd
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- `x ↦ ℛ_W(W_x)` is integrable. -/
theorem integrable_totalRootedDensity_row (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) : Integrable (fun x => totalRootedDensity H W (W.row x)) unitμ := by
  refine integrable_of_abs_le (Finset.measurable_sum _ fun v _ =>
    measurable_rootedDensity_row H W v) (Fintype.card V) fun x => ?_
  unfold totalRootedDensity
  have h0 : 0 ≤ ∑ v, rootedDensity H W v (W.row x) :=
    Finset.sum_nonneg fun v _ => (rootedDensity_mem_Icc H W v (isRow_row W x).2).1
  rw [abs_of_nonneg h0]
  calc ∑ v, rootedDensity H W v (W.row x) ≤ ∑ _v : V, (1:ℝ) :=
        Finset.sum_le_sum fun v _ => (rootedDensity_mem_Icc H W v (isRow_row W x).2).2
    _ = Fintype.card V := by simp

/-- **`∫₀¹ ℱ_W(W_x) dx = 2I_q(W) - 2α e(W) - μN t(H,W)`**, and the integrand is integrable. -/
theorem integral_rowFunctional_row (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (α μ : ℝ) :
    Integrable (fun x => rowFunctional H W q α μ (W.row x)) unitμ ∧
      ∫ x, rowFunctional H W q α μ (W.row x) ∂unitμ
        = 2 * W.Ip q - 2 * α * W.edgeDensity - μ * Fintype.card V * W.tDensity H := by
  have hJint : Integrable (fun z : ℝ × ℝ => Jp q (W.toFun z.1 z.2)) (unitμ.prod unitμ) :=
    W.integrable_comp (measurable_Jp q) (continuousOn_Jp_Icc hq0 hq1)
  have hWint : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) (unitμ.prod unitμ) :=
    W.integrable_self
  have h1 : Integrable (fun x => ∫ y, Jp q (W.row x y) ∂unitμ) unitμ :=
    hJint.integral_prod_left
  have h2 : Integrable (fun x => ∫ y, W.row x y ∂unitμ) unitμ := hWint.integral_prod_left
  have h3 := integrable_totalRootedDensity_row H W
  have hint : Integrable (fun x => rowFunctional H W q α μ (W.row x)) unitμ :=
    ((h1.const_mul 2).sub (h2.const_mul (2 * α))).sub (h3.const_mul μ)
  refine ⟨hint, ?_⟩
  have e1 : ∫ x, ∫ y, Jp q (W.row x y) ∂unitμ ∂unitμ = W.Ip q :=
    (integral_prod _ hJint).symm
  have e2 : ∫ x, ∫ y, W.row x y ∂unitμ ∂unitμ = W.edgeDensity :=
    (integral_prod _ hWint).symm
  have hA : Integrable (fun x => 2 * ∫ y, Jp q (W.row x y) ∂unitμ
      - 2 * α * ∫ y, W.row x y ∂unitμ) unitμ := (h1.const_mul 2).sub (h2.const_mul (2 * α))
  have hB : Integrable (fun x => μ * totalRootedDensity H W (W.row x)) unitμ := h3.const_mul μ
  have hA1 : Integrable (fun x => 2 * ∫ y, Jp q (W.row x y) ∂unitμ) unitμ := h1.const_mul 2
  have hA2 : Integrable (fun x => 2 * α * ∫ y, W.row x y ∂unitμ) unitμ := h2.const_mul (2 * α)
  unfold rowFunctional
  rw [integral_sub hA hB, integral_sub hA1 hA2, integral_const_mul,
    integral_const_mul, integral_const_mul, e1, e2, rooted_average]
  ring

/-- **Almost every row attains the lower bound.**  If `c ≤ ℱ_W(u)` for every row `u` and
`c = 2I_q(W) - 2α e(W) - μN t(H,W)`, then `ℱ_W(W_x) = c` for almost every `x`. -/
theorem ae_rowFunctional_row_eq (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {α μ c : ℝ}
    (hle : ∀ u, IsRow u → c ≤ rowFunctional H W q α μ u)
    (hc : 2 * W.Ip q - 2 * α * W.edgeDensity - μ * Fintype.card V * W.tDensity H = c) :
    ∀ᵐ x ∂unitμ, rowFunctional H W q α μ (W.row x) = c := by
  obtain ⟨hint, hval⟩ := integral_rowFunctional_row H W hq0 hq1 α μ
  have hnn : 0 ≤ᵐ[unitμ] fun x => rowFunctional H W q α μ (W.row x) - c :=
    ae_of_all _ fun x => sub_nonneg.2 (hle _ (isRow_row W x))
  have hzero : ∫ x, (rowFunctional H W q α μ (W.row x) - c) ∂unitμ = 0 := by
    rw [integral_sub hint (integrable_const c), hval, hc]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub (integrable_const c))).1 hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 hx

/-! ### A finite family of graphs -/

section Family

variable {ι : Type*} [Fintype ι]

/-- `x ↦ 𝒫_W(W_x)` is integrable. -/
theorem integrable_combinedRooted_row (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (μ : ι → ℝ) :
    Integrable (fun x => combinedRooted Hs W μ (W.row x)) unitμ := by
  unfold combinedRooted
  exact integrable_finsetSum _ fun j _ =>
    (integrable_totalRootedDensity_row (Hs j) W).const_mul _

/-- **`∫₀¹ ℱ_W(W_x) dx = 2I_q(W) - 2α e(W) - ∑_j μ_j N t(H_j,W)`**, and the integrand is
integrable. -/
theorem integral_combinedRowFunctional_row (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (α : ℝ) (μ : ι → ℝ) :
    Integrable (fun x => combinedRowFunctional Hs W q α μ (W.row x)) unitμ ∧
      ∫ x, combinedRowFunctional Hs W q α μ (W.row x) ∂unitμ
        = 2 * W.Ip q - 2 * α * W.edgeDensity
          - ∑ j, μ j * (Fintype.card V * W.tDensity (Hs j)) := by
  have hJint : Integrable (fun z : ℝ × ℝ => Jp q (W.toFun z.1 z.2)) (unitμ.prod unitμ) :=
    W.integrable_comp (measurable_Jp q) (continuousOn_Jp_Icc hq0 hq1)
  have hWint : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) (unitμ.prod unitμ) :=
    W.integrable_self
  have h1 : Integrable (fun x => ∫ y, Jp q (W.row x y) ∂unitμ) unitμ :=
    hJint.integral_prod_left
  have h2 : Integrable (fun x => ∫ y, W.row x y ∂unitμ) unitμ := hWint.integral_prod_left
  have h3 := integrable_combinedRooted_row Hs W μ
  have hint : Integrable (fun x => combinedRowFunctional Hs W q α μ (W.row x)) unitμ :=
    ((h1.const_mul 2).sub (h2.const_mul (2 * α))).sub h3
  refine ⟨hint, ?_⟩
  have e1 : ∫ x, ∫ y, Jp q (W.row x y) ∂unitμ ∂unitμ = W.Ip q :=
    (integral_prod _ hJint).symm
  have e2 : ∫ x, ∫ y, W.row x y ∂unitμ ∂unitμ = W.edgeDensity :=
    (integral_prod _ hWint).symm
  have hA : Integrable (fun x => 2 * ∫ y, Jp q (W.row x y) ∂unitμ
      - 2 * α * ∫ y, W.row x y ∂unitμ) unitμ := (h1.const_mul 2).sub (h2.const_mul (2 * α))
  have hA1 : Integrable (fun x => 2 * ∫ y, Jp q (W.row x y) ∂unitμ) unitμ := h1.const_mul 2
  have hA2 : Integrable (fun x => 2 * α * ∫ y, W.row x y ∂unitμ) unitμ := h2.const_mul (2 * α)
  unfold combinedRowFunctional
  rw [integral_sub hA h3, integral_sub hA1 hA2, integral_const_mul, integral_const_mul, e1, e2,
    combined_average Hs W μ]

/-- **Almost every row attains the lower bound.**  If `c ≤ ℱ_W(u)` for every row `u` and
`c = 2I_q(W) - 2α e(W) - ∑_j μ_j N t(H_j,W)`, then `ℱ_W(W_x) = c` for almost every `x`. -/
theorem ae_combinedRowFunctional_row_eq (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {α c : ℝ} {μ : ι → ℝ} (hle : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u)
    (hc : 2 * W.Ip q - 2 * α * W.edgeDensity
      - ∑ j, μ j * (Fintype.card V * W.tDensity (Hs j)) = c) :
    ∀ᵐ x ∂unitμ, combinedRowFunctional Hs W q α μ (W.row x) = c := by
  obtain ⟨hint, hval⟩ := integral_combinedRowFunctional_row Hs W hq0 hq1 α μ
  have hnn : 0 ≤ᵐ[unitμ] fun x => combinedRowFunctional Hs W q α μ (W.row x) - c :=
    ae_of_all _ fun x => sub_nonneg.2 (hle _ (isRow_row W x))
  have hzero : ∫ x, (combinedRowFunctional Hs W q α μ (W.row x) - c) ∂unitμ = 0 := by
    rw [integral_sub hint (integrable_const c), hval, hc]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub (integrable_const c))).1 hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.1 hx

end Family

end UpperTailMultipodality.Insertion
