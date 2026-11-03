import UpperTailMultipodality.Insertion.Construction
import UpperTailMultipodality.Preliminaries.Perturbation

/-!
# First-order expansion of the insertion at `θ = 0`

The old vertices of the inserted graphon carry `W + g(θ) Z` for a bounded symmetric direction
`Z` supported where `η < W < 1 - η`, and a reparametrization `g` with `g(0) = 0`.  This file
computes the one-sided derivatives at `θ = 0` used in `lem:insertion-first-order` and
`lem:fixed-insertion`:

* `hasDerivAt_insertionPoly` — the polynomial expansion `Q(θ)` of `t(H, W_θ)` has derivative
  `g'(0) ∫∫ 𝒟_W Z + ℛ_W(u) - N t(H,W)`;
* `hasDerivAt_insertion_Ip` — the exact expression of `I_p(W_θ)` has derivative
  `2 ∫ J_p(u) - 2 I_p(W) + g'(0) ∫∫ J_p'(W) Z`;
* `euler_lagrange_integral` — `∫∫ J_p'(W) Z = α ∫∫ Z + μ ∫∫ 𝒟_W Z` under `J_p'(W) = α + μ𝒟_W`;
* `insertion_derivative_nonneg` — if the insertion increases `t(H,·)` to first order and `W`
  minimizes `I_p` among the graphons with larger `H`-density and the edge density of the
  insertion, then the derivative of `I_p` above is nonnegative.
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

/-! ### One-sided slopes at `0` -/

/-- If `h` is continuous at `0`, then `θ ↦ θ h(θ)` has derivative `h(0)` at `0`. -/
theorem hasDerivAt_mul_of_continuousAt {h : ℝ → ℝ} (hh : ContinuousAt h 0) :
    HasDerivAt (fun θ => θ * h θ) (h 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim : Tendsto h (𝓝[≠] 0) (𝓝 (h 0)) := hh.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  field_simp [show t ≠ 0 from ht]

/-- Transport `HasDerivAt` along equal functions and equal derivatives. -/
theorem hasDerivAt_of_eq {f g : ℝ → ℝ} {f' g' x : ℝ} (h : HasDerivAt f f' x)
    (hfg : ∀ θ, g θ = f θ) (h' : f' = g') : HasDerivAt g g' x := by
  have : g = f := funext hfg
  subst this h'
  exact h

/-- A positive derivative at `0` gives `Q(0) < Q(θ)` for small `θ > 0`. -/
theorem eventually_lt_of_hasDerivAt_pos {Q : ℝ → ℝ} {Q' : ℝ} (hQ : HasDerivAt Q Q' 0)
    (hpos : 0 < Q') : ∀ᶠ θ in 𝓝[>] 0, Q 0 < Q θ := by
  have h := hQ.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)
  filter_upwards [h, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, smul_eq_mul] at ht
  have htpos' : 0 < t := htpos
  have : 0 < Q t - Q 0 := by
    by_contra hcon
    push Not at hcon
    have : t⁻¹ * (Q t - Q 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htpos'.le) hcon
    linarith
  linarith

/-- If `F(0) ≤ F(θ)` for small `θ > 0`, then `F'(0) ≥ 0`. -/
theorem nonneg_of_hasDerivAt_of_eventually_le {F : ℝ → ℝ} {F' : ℝ} (hF : HasDerivAt F F' 0)
    (h : ∀ᶠ θ in 𝓝[>] 0, F 0 ≤ F θ) : 0 ≤ F' := by
  refine ge_of_tendsto hF.tendsto_slope_zero_right ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, smul_eq_mul]
  have htpos' : 0 < t := htpos
  exact mul_nonneg (inv_nonneg.2 htpos'.le) (by linarith)

/-! ### Kernels near a graphon -/

/-- Two kernels with the same values are equal. -/
theorem kernel_ext_toFun {K K' : Kernel} (h : K.toFun = K'.toFun) : K = K' := by
  obtain ⟨f, _, _, _⟩ := K
  obtain ⟨f', _, _, _⟩ := K'
  cases h
  rfl

/-- `W + 0 • Z = W`. -/
theorem ofGraphon_add_zero_smul (W : Graphon) (Z : Kernel) :
    Kernel.ofGraphon W + (0 : ℝ) • Z = Kernel.ofGraphon W :=
  kernel_ext_toFun (funext fun x => funext fun y => by simp)

/-- A bounded measurable kernel is integrable. -/
theorem integrable_kernel (Z : Kernel) : Integrable (fun z : ℝ × ℝ => Z.toFun z.1 z.2) gμ := by
  obtain ⟨C, hC⟩ := Z.bdd'
  exact integrable_of_abs_le Z.meas' C fun z => hC z.1 z.2

/-- If `Z` is supported where `η < W < 1 - η`, then `W + sZ` takes values in `[0,1]` for all
small `s`. -/
theorem exists_add_smul_mem_Icc (W : Graphon) (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| ≤ δ → ∀ x y,
      (Kernel.ofGraphon W + s • Z).toFun x y ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨C, hC⟩ := Z.bdd'
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  refine ⟨η / (C + 1), by positivity, fun s hs x y => ?_⟩
  simp only [Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply]
  by_cases hz : Z.toFun x y = 0
  · simpa [hz] using W.mem_Icc x y
  · obtain ⟨h1, h2⟩ := hZ x y hz
    have hsZ : |s * Z.toFun x y| ≤ η := by
      rw [abs_mul]
      calc |s| * |Z.toFun x y| ≤ η / (C + 1) * C :=
            mul_le_mul hs (hC x y) (abs_nonneg _) (by positivity)
        _ ≤ η := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
    rw [abs_le] at hsZ
    constructor <;> linarith [hsZ.1, hsZ.2]

section Block

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `s ↦ T_S(W + sZ)` is continuous at `0` (dominated convergence). -/
theorem continuousAt_blockDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η) (S : Finset V)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) :
    ContinuousAt (fun s : ℝ => blockDensity H S q u (Kernel.ofGraphon W + s • Z)) 0 := by
  obtain ⟨δ, hδ, hK⟩ := exists_add_smul_mem_Icc W Z hη hZ
  unfold blockDensity
  refine continuousAt_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · refine Eventually.of_forall fun s => ?_
    exact (Finset.measurable_prod _ fun e _ => (measurable_edgeVal
      (blockKernel_symm q u (Kernel.ofGraphon W + s • Z).symm')
      (measurable_blockKernel q hu.1 (Kernel.ofGraphon W + s • Z).meas') e).comp
        (measurable_pinNew S)).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) hδ] with s hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
    refine Eventually.of_forall fun y => ?_
    have h := prod_edgeVal_mem_Icc H (blockKernel_symm q u (Kernel.ofGraphon W + s • Z).symm')
      (blockKernel_mem_Icc hq hu.2 (hK s hs)) (pinNew S y)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  · refine Eventually.of_forall fun y => (continuous_finsetProd _ fun e _ => ?_).continuousAt
    induction e using Sym2.ind with
    | _ a b =>
      show Continuous fun s : ℝ =>
        blockKernel q u (Kernel.ofGraphon W + s • Z).toFun (pinNew S y a) (pinNew S y b)
      simp only [blockKernel, Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply]
      split_ifs <;> fun_prop

/-- The polynomial expansion `Q(θ) = ∑_S θ^{|S|}(1-θ)^{N-|S|} T_S(W + g(θ)Z)` of the
`H`-density of the inserted graphon. -/
noncomputable def insertionPoly (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ) (u : ℝ → ℝ)
    (W : Graphon) (Z : Kernel) (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset V).powerset,
    θ ^ S.card * (1 - θ) ^ Sᶜ.card * blockDensity H S q u (Kernel.ofGraphon W + g θ • Z)

/-- `Q(0) = t(H,W)`. -/
theorem insertionPoly_zero (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ) (u : ℝ → ℝ)
    (W : Graphon) (Z : Kernel) {g : ℝ → ℝ} (hg0 : g 0 = 0) :
    insertionPoly H q u W Z g 0 = W.tDensity H := by
  unfold insertionPoly
  rw [Finset.sum_eq_single ∅]
  · simp [hg0, ofGraphon_add_zero_smul, blockDensity_empty, Kernel.tDensity_ofGraphon]
  · intro S _ hS
    have hpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS)
    simp [zero_pow hpos.ne']
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

/-- Collapse a sum over subsets to the empty set and the singletons. -/
theorem sum_powerset_ite (f : Finset V → ℝ) (A : ℝ) :
    ∑ S ∈ (Finset.univ : Finset V).powerset,
        ((if S = ∅ then A else 0) + (if S.card = 1 then f S else 0))
      = A + ∑ v, f {v} := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ ∅ (fun _ => A),
    if_pos (Finset.empty_mem_powerset _), ← Finset.sum_filter, ← Finset.powersetCard_eq_filter,
    Finset.powersetCard_one, Finset.sum_map]
  rfl

/-- **`Q'(0) = g'(0) ∫∫ 𝒟_W Z + ℛ_W(u) - N t(H,W)`.** -/
theorem hasDerivAt_insertionPoly (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) :
    HasDerivAt (insertionPoly H q u W Z g)
      (g' * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ) + totalRootedDensity H W u
        - Fintype.card V * W.tDensity H) 0 := by
  have hterm : ∀ S ∈ (Finset.univ : Finset V).powerset,
      HasDerivAt (fun θ => θ ^ S.card * (1 - θ) ^ Sᶜ.card
          * blockDensity H S q u (Kernel.ofGraphon W + g θ • Z))
        ((if S = ∅ then g' * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
            - Fintype.card V * W.tDensity H else 0)
          + (if S.card = 1 then blockDensity H S q u (Kernel.ofGraphon W) else 0)) 0 := by
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
      · simp [blockDensity_empty, Finset.compl_empty, Finset.card_univ]
      · simp [hg0, ofGraphon_add_zero_smul, Kernel.tDensity_ofGraphon]
        ring
    · have hpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS)
      have hc : ContinuousAt (fun θ : ℝ => θ ^ (S.card - 1) * (1 - θ) ^ Sᶜ.card
          * blockDensity H S q u (Kernel.ofGraphon W + g θ • Z)) 0 := by
        refine ((continuous_pow _).continuousAt.mul
          ((continuous_const.sub continuous_id).pow _).continuousAt).mul ?_
        exact (continuousAt_blockDensity H W Z hη hZ S hq hu).comp_of_eq hg.continuousAt hg0
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
  simp only [blockDensity_singleton, totalRootedDensity]
  ring

/-- For small `θ > 0` the insertion is a graphon whose `H`-density is `Q(θ)`, with the exact
expressions of its edge density and its relative entropy. -/
theorem eventually_exists_insertGraphon (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) {g : ℝ → ℝ}
    (hgc : ContinuousAt g 0) (hg0 : g 0 = 0) :
    ∀ᶠ θ in 𝓝[>] 0, ∃ W' : Graphon,
      W'.tDensity H = insertionPoly H q u W Z g θ ∧
      W'.edgeDensity = θ ^ 2 * q + 2 * θ * (1 - θ) * ∫ y, u y ∂unitμ
        + (1 - θ) ^ 2 * (W.edgeDensity + g θ * ∫ z, Z.toFun z.1 z.2 ∂gμ) ∧
      ∀ p, 0 < p → p < 1 →
        W'.Ip p = θ ^ 2 * Jp p q + 2 * θ * (1 - θ) * ∫ y, Jp p (u y) ∂unitμ
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
  refine ⟨insertGraphon θ q hq u hu (clampKernel (Kernel.ofGraphon W + g θ • Z)), ?_, ?_,
    fun p hp0 hp1 => ?_⟩
  · rw [tDensity_insertGraphon H hθ0' hθ1' hq hu]
    unfold insertionPoly
    exact Finset.sum_congr rfl fun S _ => by rw [blockDensity_congr H S q u hcl]
  · rw [edgeDensity_insertGraphon hθ0' hθ1' hq hu]
    have he : (clampKernel (Kernel.ofGraphon W + g θ • Z)).edgeDensity
        = ∫ z, (W.toFun z.1 z.2 + g θ * Z.toFun z.1 z.2) ∂gμ :=
      integral_congr_ae (ae_of_all _ fun z => clampKernel_apply_of_mem hKmem z.1 z.2)
    rw [he, integral_add W.integrable_self ((integrable_kernel Z).const_mul _), integral_const_mul]
    rfl
  · rw [Ip_insertGraphon hθ0' hθ1' hq hu _ hp0 hp1]
    have hI : (clampKernel (Kernel.ofGraphon W + g θ • Z)).Ip p
        = (Kernel.ofGraphon W + g θ • Z).Ip p :=
      integral_congr_ae (ae_of_all _ fun z => by
        simp only [clampKernel_apply_of_mem hKmem z.1 z.2])
    rw [hI]

end Block

/-- **The derivative of `θ²J_p(q) + 2θ(1-θ)∫J_p(u) + (1-θ)² I_p(W + g(θ)Z)` at `0`.** -/
theorem hasDerivAt_insertion_Ip (W : Graphon) (Z : Kernel) {p a b : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (ha : 0 < a) (hb : b < 1) (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b)
    {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) (A B : ℝ) :
    HasDerivAt (fun θ => θ ^ 2 * B + 2 * θ * (1 - θ) * A
        + (1 - θ) ^ 2 * (Kernel.ofGraphon W + g θ • Z).Ip p)
      (2 * A - 2 * W.Ip p + g' * ∫ z, Jp' p (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ) 0 := by
  have hI : HasDerivAt (fun θ => (Kernel.ofGraphon W + g θ • Z).Ip p)
      ((∫ z, Jp' p (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ) * g') 0 := by
    have hf := hasDerivAt_Ip_line W Z hp0 hp1 ha hb hW
    rw [← hg0] at hf
    exact hf.comp 0 hg
  have h1 := ((hasDerivAt_id' (0:ℝ)).fun_pow 2).mul_const B
  have h2 := (((hasDerivAt_id' (0:ℝ)).const_mul 2).fun_mul
    ((hasDerivAt_id' (0:ℝ)).const_sub 1)).mul_const A
  have h3 := (((hasDerivAt_id' (0:ℝ)).const_sub 1).fun_pow 2).fun_mul hI
  refine hasDerivAt_of_eq ((h1.add h2).add h3) (fun θ => rfl) ?_
  simp only [hg0, ofGraphon_add_zero_smul]
  have hW0 : (Kernel.ofGraphon W).Ip p = W.Ip p := rfl
  rw [hW0]
  ring

/-! ### The Euler–Lagrange equation and the sign of the derivative -/

section EulerLagrange

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Integrating the Euler–Lagrange equation against a direction.**  If
`J_p'(W) = α + μ𝒟_W` almost everywhere with `μ ≠ 0`, then `𝒟_W Z` is integrable and
`∫∫ J_p'(W) Z = α ∫∫ Z + μ ∫∫ 𝒟_W Z`. -/
theorem euler_lagrange_integral (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {p a b α μ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : b < 1)
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b) (hμ : μ ≠ 0)
    (hEL : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = α + μ * derivKernel H W z.1 z.2) :
    Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2 * Z.toFun z.1 z.2) gμ ∧
      ∫ z, Jp' p (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ
        = α * ∫ z, Z.toFun z.1 z.2 ∂gμ
          + μ * ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := by
  have hJZ := integrable_Jp'_mul W Z hp0 hp1 ha hb hW
  have hDZ : Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2 * Z.toFun z.1 z.2) gμ := by
    refine ((hJZ.sub ((integrable_kernel Z).const_mul α)).div_const μ).congr ?_
    filter_upwards [hEL] with z hz
    simp only [Pi.sub_apply, hz]
    field_simp
    ring
  refine ⟨hDZ, ?_⟩
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_kernel Z).const_mul α) (hDZ.const_mul μ)]
  refine integral_congr_ae ?_
  filter_upwards [hEL] with z hz
  simp only [hz]
  ring

/-- **The first-order insertion inequality.**  Insert a block with value `q` and row `u`, and move
the old values along `W + g(θ)Z`.  If this increases `t(H,·)` to first order, and `W` minimizes
`I_p` among the graphons with larger `H`-density and the edge density of the insertion, then the
derivative of `I_p` along the insertion at `θ = 0⁺` is nonnegative. -/
theorem insertion_derivative_nonneg (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) {η : ℝ} (hη : 0 < η)
    (hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η)
    {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' 0) (hg0 : g 0 = 0) {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hb : b < 1) (hWab : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc a b)
    (hpos : 0 < g' * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
      + totalRootedDensity H W u - Fintype.card V * W.tDensity H)
    (hmin : ∀ᶠ θ in 𝓝[>] 0, ∀ W' : Graphon, W.tDensity H < W'.tDensity H →
      W'.edgeDensity = θ ^ 2 * q + 2 * θ * (1 - θ) * ∫ y, u y ∂unitμ
        + (1 - θ) ^ 2 * (W.edgeDensity + g θ * ∫ z, Z.toFun z.1 z.2 ∂gμ) →
      W.Ip p ≤ W'.Ip p) :
    0 ≤ 2 * ∫ y, Jp p (u y) ∂unitμ - 2 * W.Ip p
      + g' * ∫ z, Jp' p (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ := by
  have hlt := eventually_lt_of_hasDerivAt_pos
    (hasDerivAt_insertionPoly H W Z hη hZ hq hu hg hg0) hpos
  have hex := eventually_exists_insertGraphon H W Z hη hZ hq hu hg.continuousAt hg0
  have hF := hasDerivAt_insertion_Ip W Z hp0 hp1 ha hb hWab hg hg0
    (∫ y, Jp p (u y) ∂unitμ) (Jp p q)
  refine nonneg_of_hasDerivAt_of_eventually_le hF ?_
  filter_upwards [hlt, hex, hmin] with θ hθlt hθex hθmin
  obtain ⟨W', ht, he, hI⟩ := hθex
  rw [insertionPoly_zero H q u W Z hg0, ← ht] at hθlt
  have hle := hθmin W' hθlt he
  rw [hI p hp0 hp1] at hle
  simp only [hg0, ofGraphon_add_zero_smul]
  have hW0 : (Kernel.ofGraphon W).Ip p = W.Ip p := rfl
  rw [hW0]
  simpa using hle

end EulerLagrange

end UpperTailMultipodality.Insertion
