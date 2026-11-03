import UpperTailMultipodality.Insertion.FirstOrder
import UpperTailMultipodality.Insertion.Rows
import UpperTailMultipodality.RowCriterion.Rows.Derivative
import UpperTailMultipodality.Insertion.ConstructionRows

/-!
# First-order expansion of the insertion of a block with several rows (`lem:insertion-first-order`)

The old vertices of the inserted graphon carry `W + g(θ) Z` for a bounded symmetric direction
`Z` supported where `η < W < 1 - η`, and a reparametrization `g` with `g(0) = 0`.  This file
computes the one-sided derivatives at `θ = 0` of `lem:insertion-first-order`:

* `hasDerivAt_insertionPolyRows` — the polynomial expansion `Q(θ)` of `t(H, W_θ)` has derivative
  `g'(0) ∫∫ 𝒟_W Z + ∫₀¹ ℛ_W(U t) dt - N t(H,W)`;
* `eventually_exists_insertGraphonRows` — one graphon realizing, for *every* graph of a finite
  family at once, the polynomial `Q(θ)`, with the exact value of `I_p`.

`hasDerivAt_insertion_Ip` of `Insertion/FirstOrder.lean` already gives the derivative of `I_p`,
since it does not refer to the rows.
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

section Block

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `s ↦ T_S(W + sZ)` is continuous at `0` (dominated convergence). -/
theorem continuousAt_blockDensityRows (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η) (S : Finset V)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) :
    ContinuousAt (fun s : ℝ => blockDensityRows H S q U (Kernel.ofGraphon W + s • Z)) 0 := by
  obtain ⟨δ, hδ, hK⟩ := exists_add_smul_mem_Icc W Z hη hZ
  unfold blockDensityRows
  refine continuousAt_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · refine Eventually.of_forall fun s => ?_
    exact (Finset.measurable_prod _ fun e _ => (measurable_edgeVal
      (blockKernelRows_symm q U (Kernel.ofGraphon W + s • Z).symm')
      (measurable_blockKernelRows q hU.1 (Kernel.ofGraphon W + s • Z).meas') e).comp
        (measurable_pinNewRows S)).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) hδ] with s hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
    refine Eventually.of_forall fun y => ?_
    have h := prod_edgeVal_mem_Icc H
      (blockKernelRows_symm q U (Kernel.ofGraphon W + s • Z).symm')
      (blockKernelRows_mem_Icc hq hU.2 (hK s hs)) (pinNewRows S y)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  · refine Eventually.of_forall fun y => (continuous_finsetProd _ fun e _ => ?_).continuousAt
    induction e using Sym2.ind with
    | _ a b =>
      show Continuous fun s : ℝ => blockKernelRows q U (Kernel.ofGraphon W + s • Z).toFun
        (pinNewRows S y a) (pinNewRows S y b)
      simp only [blockKernelRows, Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply]
      split_ifs <;> fun_prop

/-- The polynomial expansion `Q(θ) = ∑_S θ^{|S|}(1-θ)^{N-|S|} T_S(W + g(θ)Z)` of the
`H`-density of the inserted graphon. -/
noncomputable def insertionPolyRows (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ)
    (U : ℝ → ℝ → ℝ) (W : Graphon) (Z : Kernel) (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset V).powerset,
    θ ^ S.card * (1 - θ) ^ Sᶜ.card * blockDensityRows H S q U (Kernel.ofGraphon W + g θ • Z)

/-- `Q(0) = t(H,W)`. -/
theorem insertionPolyRows_zero (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ)
    (U : ℝ → ℝ → ℝ) (W : Graphon) (Z : Kernel) {g : ℝ → ℝ} (hg0 : g 0 = 0) :
    insertionPolyRows H q U W Z g 0 = W.tDensity H := by
  unfold insertionPolyRows
  rw [Finset.sum_eq_single ∅]
  · simp [hg0, ofGraphon_add_zero_smul, blockDensityRows_empty, Kernel.tDensity_ofGraphon]
  · intro S _ hS
    have hpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS)
    simp [zero_pow hpos.ne']
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

/-- **`Q'(0) = g'(0) ∫∫ 𝒟_W Z + ∑_v T_{v} - N t(H,W)`.** -/
theorem hasDerivAt_insertionPolyRows (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) :
    HasDerivAt (insertionPolyRows H q U W Z g)
      (g' * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        + (∑ v, blockDensityRows H {v} q U (Kernel.ofGraphon W))
        - Fintype.card V * W.tDensity H) 0 := by
  have hterm : ∀ S ∈ (Finset.univ : Finset V).powerset,
      HasDerivAt (fun θ => θ ^ S.card * (1 - θ) ^ Sᶜ.card
          * blockDensityRows H S q U (Kernel.ofGraphon W + g θ • Z))
        ((if S = ∅ then g' * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
            - Fintype.card V * W.tDensity H else 0)
          + (if S.card = 1 then blockDensityRows H S q U (Kernel.ofGraphon W) else 0)) 0 := by
    intro S _
    by_cases hS : S = ∅
    · subst hS
      have h1 := ((hasDerivAt_id' (0:ℝ)).const_sub 1).fun_pow (Fintype.card V)
      have h2 : HasDerivAt (fun θ => (Kernel.ofGraphon W + g θ • Z).tDensity H)
          ((∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ) * g') 0 := by
        have hf := first_variation H W Z
        rw [← hg0] at hf
        exact hf.comp 0 hg
      refine hasDerivAt_of_eq (h1.fun_mul h2) (fun θ => ?_) ?_
      · simp [blockDensityRows_empty, Finset.compl_empty, Finset.card_univ]
      · simp [hg0, ofGraphon_add_zero_smul, Kernel.tDensity_ofGraphon]
        ring
    · have hpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS)
      have hc : ContinuousAt (fun θ : ℝ => θ ^ (S.card - 1) * (1 - θ) ^ Sᶜ.card
          * blockDensityRows H S q U (Kernel.ofGraphon W + g θ • Z)) 0 := by
        refine ((continuous_pow _).continuousAt.mul
          ((continuous_const.sub continuous_id).pow _).continuousAt).mul ?_
        exact (continuousAt_blockDensityRows H W Z hη hZ S hq hU).comp_of_eq hg.continuousAt hg0
      refine hasDerivAt_of_eq (hasDerivAt_mul_of_continuousAt hc) (fun θ => ?_) ?_
      · rw [← mul_assoc, ← mul_assoc, ← pow_succ']
        congr 3
        omega
      · rw [if_neg hS, zero_add]
        by_cases h1 : S.card = 1
        · rw [if_pos h1, h1]
          simp [hg0, ofGraphon_add_zero_smul]
        · rw [if_neg h1]
          have h1' : S.card - 1 ≠ 0 := by omega
          simp [zero_pow h1']
  have hsum := HasDerivAt.fun_sum hterm
  rw [sum_powerset_ite] at hsum
  refine hasDerivAt_of_eq hsum (fun θ => rfl) ?_
  ring

/-- `∑_v T_{v} = ∫₀¹ ℛ_W(U t) dt`. -/
theorem sum_blockDensityRows_singleton (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ)
    {U : ℝ → ℝ → ℝ} (hU : IsRows U) (W : Graphon) :
    (∑ v, blockDensityRows H {v} q U (Kernel.ofGraphon W))
      = ∫ t, totalRootedDensity H W (U t) ∂unitμ := by
  have hrow : ∀ t, IsRow (U t) := fun t =>
    ⟨by
      have hp : Measurable fun y : ℝ => ((t, y) : ℝ × ℝ) := measurable_const.prodMk measurable_id
      have h := hU.1.comp hp
      exact h, fun y => hU.2 t y⟩
  have hmeas : ∀ v : V, Measurable fun t => rootedDensity H W v (U t) := by
    intro v
    have hjoint : Measurable fun p : ℝ × (V → ℝ) =>
        (∏ z ∈ H.neighborFinset v, U p.1 (p.2 z)) * avoidingProduct H W v p.2 := by
      refine (Finset.measurable_prod _ fun z _ => ?_).mul ?_
      · have hp : Measurable fun p : ℝ × (V → ℝ) => ((p.1, p.2 z) : ℝ × ℝ) :=
          measurable_fst.prodMk ((measurable_pi_apply z).comp measurable_snd)
        have h := hU.1.comp hp
        exact h
      · exact (measurable_avoidingProduct H W v).comp measurable_snd
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have hint : ∀ v : V, Integrable (fun t => rootedDensity H W v (U t)) unitμ := by
    intro v
    refine integrable_of_abs_le (hmeas v) 1 fun t => ?_
    have h := rootedDensity_mem_Icc H W v (hrow t).2
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  rw [show (fun t => totalRootedDensity H W (U t))
      = fun t => ∑ v, rootedDensity H W v (U t) from rfl,
    integral_finsetSum _ fun v _ => hint v]
  exact Finset.sum_congr rfl fun v _ => blockDensityRows_singleton H v q hU W

end Block

/-! ### Measurability and bounds of the row functionals -/

/-- Each row of a row kernel is a row. -/
theorem isRow_rows {U : ℝ → ℝ → ℝ} (hU : IsRows U) (t : ℝ) : IsRow (U t) := by
  refine ⟨?_, fun y => hU.2 t y⟩
  have hp : Measurable fun y : ℝ => ((t, y) : ℝ × ℝ) := measurable_const.prodMk measurable_id
  have h := hU.1.comp hp
  exact h

/-- `t ↦ ∫ J_q(U t)` is measurable. -/
theorem measurable_integral_Jp_rows (q : ℝ) {U : ℝ → ℝ → ℝ} (hU : IsRows U) :
    Measurable fun t => ∫ y, Jp q (U t y) ∂unitμ := by
  have hjoint : Measurable fun z : ℝ × ℝ => Jp q (U z.1 z.2) := (measurable_Jp q).comp hU.1
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- `∫∫ J_q(U) = ∫ (∫ J_q(U t)) dt` for a row kernel `U`. -/
theorem integral_gμ_Jp_rows {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {U : ℝ → ℝ → ℝ}
    (hU : IsRows U) :
    ∫ z, Jp q (U z.1 z.2) ∂gμ = ∫ t, (∫ y, Jp q (U t y) ∂unitμ) ∂unitμ := by
  obtain ⟨C, hC⟩ := Rows.exists_abs_Jp_le hq0 hq1
  have hjoint : Measurable fun z : ℝ × ℝ => Jp q (U z.1 z.2) := (measurable_Jp q).comp hU.1
  have hint : Integrable (fun z : ℝ × ℝ => Jp q (U z.1 z.2)) gμ :=
    integrable_of_abs_le hjoint C fun z => hC _ (hU.2 _ _)
  rw [gμ] at hint ⊢
  exact integral_prod _ hint

/-- `t ↦ ℛ_W(U t)` is measurable. -/
theorem measurable_totalRootedDensity_rows {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {U : ℝ → ℝ → ℝ} (hU : IsRows U) :
    Measurable fun t => totalRootedDensity H W (U t) := by
  refine Finset.measurable_sum _ fun v _ => ?_
  have hjoint : Measurable fun p : ℝ × (V → ℝ) =>
      (∏ z ∈ H.neighborFinset v, U p.1 (p.2 z)) * avoidingProduct H W v p.2 := by
    refine (Finset.measurable_prod _ fun z _ => ?_).mul ?_
    · have hp : Measurable fun p : ℝ × (V → ℝ) => ((p.1, p.2 z) : ℝ × ℝ) :=
        measurable_fst.prodMk ((measurable_pi_apply z).comp measurable_snd)
      have h := hU.1.comp hp
      exact h
    · exact (measurable_avoidingProduct H W v).comp measurable_snd
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-- `|ℛ_W(u)| ≤ N` for a row `u`. -/
theorem abs_totalRootedDensity_le {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (W : Graphon) {u : ℝ → ℝ} (hu : IsRow u) :
    |totalRootedDensity H W u| ≤ Fintype.card V := by
  unfold totalRootedDensity
  have h0 : 0 ≤ ∑ v, rootedDensity H W v u :=
    Finset.sum_nonneg fun v _ => (rootedDensity_mem_Icc H W v hu.2).1
  rw [abs_of_nonneg h0]
  calc ∑ v, rootedDensity H W v u ≤ ∑ _v : V, (1:ℝ) :=
        Finset.sum_le_sum fun v _ => (rootedDensity_mem_Icc H W v hu.2).2
    _ = Fintype.card V := by simp

/-! ### The inserted graphon, for a finite family of graphs -/

section Family

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For small `θ > 0` the insertion is a graphon whose `H_j`-density is `Q_j(θ)` **for every `j`
at once**, with the exact expression of its relative entropy. -/
theorem eventually_exists_insertGraphonRows {ι : Type*} (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) {g : ℝ → ℝ}
    (hgc : ContinuousAt g 0) (hg0 : g 0 = 0) :
    ∀ᶠ θ in 𝓝[>] 0, ∃ W' : Graphon,
      (∀ j, W'.tDensity (Hs j) = insertionPolyRows (Hs j) q U W Z g θ) ∧
      ∀ p, 0 < p → p < 1 →
        W'.Ip p = θ ^ 2 * Jp p q + 2 * θ * (1 - θ) * ∫ z, Jp p (U z.1 z.2) ∂gμ
          + (1 - θ) ^ 2 * (Kernel.ofGraphon W + g θ • Z).Ip p := by
  obtain ⟨δ, hδ, hK⟩ := exists_add_smul_mem_Icc W Z hη hZ
  have hgδ : ∀ᶠ θ in 𝓝 (0:ℝ), |g θ| ≤ δ := by
    have hmem := hgc.preimage_mem_nhds (by rw [hg0]; exact Metric.closedBall_mem_nhds (0:ℝ) hδ)
    filter_upwards [hmem] with θ hθ
    simpa [Metric.mem_closedBall, Real.dist_eq] using hθ
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds one_pos),
    nhdsWithin_le_nhds hgδ] with θ hθ0 hθ1 hgθ
  have hθ0' : 0 < θ := hθ0
  have hθ1' : θ < 1 := hθ1
  have hKmem := hK (g θ) hgθ
  have hcl : (Kernel.ofGraphon (clampKernel (Kernel.ofGraphon W + g θ • Z))).toFun
      = (Kernel.ofGraphon W + g θ • Z).toFun :=
    funext fun x => funext fun y => clampKernel_apply_of_mem hKmem x y
  refine ⟨insertGraphonRows θ q hq U hU (clampKernel (Kernel.ofGraphon W + g θ • Z)),
    fun j => ?_, fun p hp0 hp1 => ?_⟩
  · rw [tDensity_insertGraphonRows (Hs j) hθ0' hθ1' hq hU]
    unfold insertionPolyRows
    exact Finset.sum_congr rfl fun S _ => by rw [blockDensityRows_congr (Hs j) S q U hcl]
  · rw [Ip_insertGraphonRows hθ0' hθ1' hq hU _ hp0 hp1]
    have hI : (clampKernel (Kernel.ofGraphon W + g θ • Z)).Ip p
        = (Kernel.ofGraphon W + g θ • Z).Ip p :=
      integral_congr_ae (ae_of_all _ fun z => by
        simp only [clampKernel_apply_of_mem hKmem z.1 z.2])
    rw [hI]

end Family

end UpperTailMultipodality.Insertion
