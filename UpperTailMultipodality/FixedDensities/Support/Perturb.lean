import UpperTailMultipodality.FixedDensities.Support.Correction
import UpperTailMultipodality.FixedDensities.Support.Existence

/-!
# First-order perturbation estimates

* `eventually_abs_sub_le_of_hasDerivAt` — the little-o form of a derivative at `0`;
* `eq_zero_of_forall_eventually`, `nonneg_of_forall_eventually` — first-order optimality in one
  real variable, in the form used with error terms;
* `integrable_mul_of_ae_bdd` — products of almost everywhere bounded measurable functions;
* `Ip_sub_le_taylor` — the first-order Taylor bound for `I_ε` at a graphon with values in
  `[γ, 1-γ]`, for a kernel perturbation of size at most `γ/2`.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `J_p'` is measurable. -/
theorem measurable_Jp' (p : ℝ) : Measurable (Jp' p) := by
  unfold Jp'
  fun_prop

/-- The little-o form of `HasDerivAt f v 0`. -/
theorem eventually_abs_sub_le_of_hasDerivAt {f : ℝ → ℝ} {v : ℝ} (h : HasDerivAt f v 0)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ θ in 𝓝 0, |f θ - f 0 - θ * v| ≤ δ * |θ| := by
  have := (hasDerivAt_iff_isLittleO_nhds_zero.mp h).def hδ
  filter_upwards [this] with θ hθ
  simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using hθ

/-- If `0 ≤ θ r + δ|θ|` near `0` for every `δ > 0`, then `r = 0`. -/
theorem eq_zero_of_forall_eventually {r : ℝ}
    (h : ∀ δ > 0, ∀ᶠ θ in 𝓝 (0:ℝ), 0 ≤ θ * r + δ * |θ|) : r = 0 := by
  by_contra hr
  have hr' : 0 < |r| := abs_pos.mpr hr
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (h (|r| / 2) (by positivity))
  have hθ : dist (-(SignType.sign r : ℝ) * (ρ / 2)) 0 < ρ := by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_neg]
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · rw [sign_neg hneg]; simp only [SignType.coe_neg, SignType.coe_one, abs_neg, abs_one,
        one_mul, abs_of_pos (half_pos hρ)]; linarith
    · rw [sign_pos hpos]; simp only [SignType.coe_one, abs_one, one_mul,
        abs_of_pos (half_pos hρ)]; linarith
  have key := hball hθ
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · rw [sign_neg hneg] at key
    simp only [SignType.coe_neg, SignType.coe_one, neg_neg, one_mul,
      abs_of_pos (half_pos hρ), abs_of_neg hneg] at key
    nlinarith
  · rw [sign_pos hpos] at key
    simp only [SignType.coe_one, neg_mul, one_mul, abs_neg,
      abs_of_pos (half_pos hρ), abs_of_pos hpos] at key
    nlinarith

/-- If `0 ≤ θ r + δθ` for all small `θ > 0` and every `δ > 0`, then `0 ≤ r`. -/
theorem nonneg_of_forall_eventually {r : ℝ}
    (h : ∀ δ > 0, ∀ᶠ θ in 𝓝[>] (0:ℝ), 0 ≤ θ * r + δ * θ) : 0 ≤ r := by
  by_contra hr
  replace hr := not_le.mp hr
  obtain ⟨θ, hθ, hθ0⟩ := ((h (-r / 2) (by linarith)).and self_mem_nhdsWithin).exists
  have : 0 < θ := hθ0
  nlinarith

/-- Products of almost everywhere bounded measurable functions are integrable. -/
theorem integrable_mul_of_ae_bdd {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {L C : ℝ} (hfL : ∀ᵐ z ∂gμ, |f z| ≤ L) (hgC : ∀ᵐ z ∂gμ, |g z| ≤ C) :
    Integrable (fun z => f z * g z) gμ :=
  Integrable.of_bound (hf.mul hg).aestronglyMeasurable (L * C) (by
    filter_upwards [hfL, hgC] with z h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))

/-- `J_ε'(W)` is almost everywhere bounded when `W ∈ [γ, 1-γ]` almost everywhere. -/
theorem ae_abs_Jp'_le (W : Graphon) {ε γ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hγ : 0 < γ)
    (hW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᵐ z ∂gμ, |Jp' ε (W.toFun z.1 z.2)| ≤ L := by
  obtain ⟨L, hL0, hL⟩ := Jp'_bdd_box hγ hε0 hε1
  exact ⟨L, hL0, hW.mono fun z hz => hL _ ⟨hz.1, hz.2⟩⟩

/-- `J_ε'(W) · K` is integrable for a bounded kernel `K` when `W ∈ [γ, 1-γ]` a.e. -/
theorem integrable_Jp'_mul (W : Graphon) {ε γ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hγ : 0 < γ)
    (hW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ) (K : Kernel) :
    Integrable (fun z : ℝ × ℝ => Jp' ε (W.toFun z.1 z.2) * K.toFun z.1 z.2) gμ := by
  obtain ⟨L, -, hL⟩ := ae_abs_Jp'_le W hε0 hε1 hγ hW
  obtain ⟨C, -, hC⟩ := kernel_bound K
  exact integrable_mul_of_ae_bdd ((measurable_Jp' ε).comp W.meas') K.meas' hL
    (ae_of_all _ fun z => hC z.1 z.2)

/-- **First-order Taylor bound for `I_ε`.**  If `γ ≤ W ≤ 1-γ` almost everywhere and the kernel
`K` satisfies `|K - W| ≤ q ≤ γ/2` everywhere, then `K` agrees almost everywhere with a graphon
`G` with the same edge and `H`-densities, and
`I_ε(G) - I_ε(W) ≤ ∫∫ J_ε'(W)(K - W) + M q²` with `M = 1/((γ/2)(1-γ/2))`. -/
theorem Ip_sub_le_taylor (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε γ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ : 0 < γ)
    (hW : ∀ᵐ z ∂gμ, γ ≤ W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 ≤ 1 - γ) (K : Kernel) {q : ℝ}
    (hq : q ≤ γ / 2) (hK : ∀ x y, |K.toFun x y - W.toFun x y| ≤ q) :
    ∃ G : Graphon, G.edgeDensity = K.edgeDensity ∧ G.tDensity H = K.tDensity H ∧
      G.Ip ε - W.Ip ε
        ≤ (∫ z, Jp' ε (W.toFun z.1 z.2) * (K.toFun z.1 z.2 - W.toFun z.1 z.2) ∂gμ)
          + (1 / ((γ / 2) * (1 - γ / 2))) * q ^ 2 := by
  have hbox : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc (γ / 2) (1 - γ / 2) ∧
      K.toFun z.1 z.2 ∈ Icc (γ / 2) (1 - γ / 2) := by
    filter_upwards [hW] with z hz
    have h := abs_le.mp (hK z.1 z.2)
    exact ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  obtain ⟨G, hGae, hGe, hGt, hGI⟩ := exists_graphon_of_ae_mem H K ε
    (hbox.mono fun z hz => ⟨by linarith [hz.2.1, hz.1.1, hγ], by linarith [hz.2.2, hγ]⟩)
  refine ⟨G, hGe, hGt, ?_⟩
  have hIG := G.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hIW := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hγ1 : γ / 2 < 1 := by
    obtain ⟨z, hz⟩ := hW.exists
    linarith [hz.1, hz.2]
  -- the linear term is integrable
  obtain ⟨L, -, hL⟩ := ae_abs_Jp'_le W hε0 hε1 hγ hW
  have hlin : Integrable
      (fun z : ℝ × ℝ => Jp' ε (W.toFun z.1 z.2) * (K.toFun z.1 z.2 - W.toFun z.1 z.2)) gμ :=
    integrable_mul_of_ae_bdd ((measurable_Jp' ε).comp W.meas') (K.meas'.sub W.meas') hL
      (ae_of_all _ fun z => hK z.1 z.2)
  set M := 1 / ((γ / 2) * (1 - γ / 2)) with hM
  have hpt : ∀ᵐ z ∂gμ, Jp ε (G.toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)
      ≤ Jp' ε (W.toFun z.1 z.2) * (K.toFun z.1 z.2 - W.toFun z.1 z.2) + M * q ^ 2 := by
    filter_upwards [hbox, hGae] with z hz hzG
    rw [hzG]
    have ht := Jp_taylor_box (half_pos hγ) hε0 hε1 hz.2 hz.1
    have hsq : (K.toFun z.1 z.2 - W.toFun z.1 z.2) ^ 2 ≤ q ^ 2 := by
      have h1 := hK z.1 z.2
      have h0 : 0 ≤ q := (abs_nonneg _).trans h1
      calc (K.toFun z.1 z.2 - W.toFun z.1 z.2) ^ 2 = |K.toFun z.1 z.2 - W.toFun z.1 z.2| ^ 2 :=
            (sq_abs _).symm
        _ ≤ q ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hM0 : 0 ≤ M := by
      rw [hM]; have : 0 < γ / 2 * (1 - γ / 2) := mul_pos (half_pos hγ) (by linarith)
      positivity
    have := (abs_le.mp ht).2
    nlinarith [mul_le_mul_of_nonneg_left hsq hM0]
  have hint : ∫ z, (Jp ε (G.toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)) ∂gμ
      ≤ ∫ z, (Jp' ε (W.toFun z.1 z.2) * (K.toFun z.1 z.2 - W.toFun z.1 z.2) + M * q ^ 2) ∂gμ :=
    integral_mono_ae (hIG.sub hIW) (hlin.add (integrable_const (M * q ^ 2))) hpt
  rw [integral_sub hIG hIW, integral_add hlin (integrable_const _), integral_const] at hint
  simpa [Graphon.Ip] using hint

end FixedDensities

end UpperTailMultipodality
