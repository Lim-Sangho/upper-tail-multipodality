import UpperTailMultipodality.UpperTail.Support.UpperBound

/-!
# The Lagrange multiplier of `lem:upper-tail-multiplier`

Let `W` be a minimizer with `p ≤ W ≤ b < 1` almost everywhere and an active constraint.  The proof
avoids the Banach-space Lagrange rule:

* `first_order_condition` — for every bounded symmetric `U` with `∫∫ 𝒟_W U > 0`, the graphons
  `W + θU` are feasible for small `θ > 0`, so `∫∫ J_p'(W) U ≥ 0`;
* applying this to `cU + t·1` for all real `c, t` gives `∫∫ J_p'(W) U = μ ∫∫ 𝒟_W U` with
  `μ = ∫∫ J_p'(W) / ∫∫ 𝒟_W` (`integral_Jp'_mul_eq`);
* taking `U = J_p'(W) - μ𝒟_W` (with a pointwise bounded representative) gives
  `∫∫ U² = 0`, hence `lem:upper-tail-multiplier`(i) (`multiplier_of_bounds`).
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory Filter Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On `[p,b] ⊆ (0,1)`, `|J_p'| ≤ J_p'(b)`. -/
theorem abs_Jp'_le {p b w : ℝ} (hp0 : 0 < p) (hb1 : b < 1) (hw : w ∈ Icc p b) :
    |Jp' p w| ≤ Jp' p b := by
  have hp1 : p < 1 := lt_of_le_of_lt (hw.1.trans hw.2) hb1
  have hmono := (Jp'_strictMonoOn hp0 hp1).monotoneOn
  have h0 : 0 ≤ Jp' p w := by
    rw [← Jp'_self hp0 hp1]
    exact hmono ⟨hp0, hp1⟩ ⟨by linarith [hw.1], by linarith [hw.2]⟩ hw.1
  rw [abs_of_nonneg h0]
  exact hmono ⟨by linarith [hw.1], by linarith [hw.2]⟩ ⟨by linarith [hw.1, hw.2], hb1⟩ hw.2

/-- The constant kernel `1`. -/
noncomputable def oneKernel : Kernel := Kernel.ofGraphon (constGraphon 1 ⟨zero_le_one, le_rfl⟩)

/-- The constant kernel `1` takes the value `1`. -/
theorem oneKernel_apply (x y : ℝ) : oneKernel.toFun x y = 1 := rfl

/-- `𝒟_W U` is integrable. -/
theorem integrable_derivKernel_mul (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (U : Kernel) :
    Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2 * U.toFun z.1 z.2) gμ := by
  obtain ⟨C, hC⟩ := U.bdd'
  refine integrable_of_abs_le ((measurable_derivKernel H W).mul U.meas') (H.edgeFinset.card * C)
    fun z => ?_
  have hD := derivKernel_mem_Icc H W z.1 z.2
  rw [abs_mul, abs_of_nonneg hD.1]
  exact mul_le_mul hD.2 (hC z.1 z.2) (abs_nonneg _) (by positivity)

/-- **First-order condition.**  If `∫∫ 𝒟_W U > 0`, then `∫∫ J_p'(W) U ≥ 0`. -/
theorem first_order_condition (H : SimpleGraph V) [DecidableRel H.Adj] {p r b : ℝ}
    (hp0 : 0 < p) (hpb : p ≤ b) (hb1 : b < 1) {W : Graphon} (hmin : W.Ip p = phiVar H p r)
    (hact : W.tDensity H = r ^ H.edgeFinset.card) (hmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc p b)
    (U : Kernel) (hU : 0 < ∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ) :
    0 ≤ ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ := by
  have hp1 : p < 1 := lt_of_le_of_lt hpb hb1
  obtain ⟨ε, hε, hεf⟩ := exists_pos_lt_of_hasDerivAt_pos (first_variation H W U) hU
  obtain ⟨W', hW'mem, hW'ae⟩ := W.exists_clamp hp0.le hpb hb1.le hmem
  obtain ⟨C, hC⟩ := U.bdd'
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min p (1 - b) / (C + 1) := ⟨_, rfl⟩
  have hmin0 : 0 < min p (1 - b) := lt_min hp0 (by linarith)
  have hη : 0 < η := hη_def ▸ div_pos hmin0 (by linarith)
  refine nonneg_of_hasDerivAt_of_le (hasDerivAt_Ip_line W U hp0 hp1 hp0 hb1 hmem)
    (lt_min hε hη) fun θ hθ0 hθ => ?_
  have hθε : θ < ε := hθ.trans_le (min_le_left _ _)
  have hθη : θ < η := hθ.trans_le (min_le_right _ _)
  have hθC : θ * C ≤ min p (1 - b) := by
    have h1 : θ * (C + 1) ≤ min p (1 - b) := by
      rw [hη_def, lt_div_iff₀ (by linarith)] at hθη
      exact hθη.le
    nlinarith
  have hvals : ∀ x y, (Kernel.ofGraphon W' + θ • U).toFun x y ∈ Icc (0:ℝ) 1 := by
    intro x y
    have h1 := hW'mem x y
    have h3 : |θ * U.toFun x y| ≤ θ * C := by
      rw [abs_mul, abs_of_pos hθ0]; exact mul_le_mul_of_nonneg_left (hC x y) hθ0.le
    have h4 := abs_le.mp h3
    have h5 := min_le_left p (1 - b)
    have h6 := min_le_right p (1 - b)
    show W'.toFun x y + θ * U.toFun x y ∈ Icc (0:ℝ) 1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  let Vθ : Graphon := (Kernel.ofGraphon W' + θ • U).toGraphon (fun x y => (hvals x y).1)
    (fun x y => (hvals x y).2)
  have hae : ∀ᵐ z ∂gμ, (Kernel.ofGraphon W' + θ • U).toFun z.1 z.2
      = (Kernel.ofGraphon W + θ • U).toFun z.1 z.2 := by
    filter_upwards [hW'ae] with z hz
    show W'.toFun z.1 z.2 + θ * U.toFun z.1 z.2 = W.toFun z.1 z.2 + θ * U.toFun z.1 z.2
    rw [hz]
  have htV : Vθ.tDensity H = (Kernel.ofGraphon W + θ • U).tDensity H :=
    kernel_tDensity_congr_ae H hae
  have hf0 : (Kernel.ofGraphon W + (0:ℝ) • U).tDensity H = W.tDensity H :=
    kernel_tDensity_congr_ae H (L := Kernel.ofGraphon W) (ae_of_all _ fun z => by simp)
  have hfeas : Feasible H r Vθ := by
    have h := hεf θ hθ0 hθε
    rw [hf0, hact] at h
    show r ^ H.edgeFinset.card ≤ Vθ.tDensity H
    rw [htV]; exact h.le
  have hIV : Vθ.Ip p = (Kernel.ofGraphon W + θ • U).Ip p :=
    integral_congr_ae (hae.mono fun z hz => by
      show Jp p ((Kernel.ofGraphon W' + θ • U).toFun z.1 z.2) = _
      rw [hz])
  have h0 : (Kernel.ofGraphon W + (0:ℝ) • U).Ip p = W.Ip p :=
    integral_congr_ae (ae_of_all _ fun z => by simp)
  show (Kernel.ofGraphon W + (0:ℝ) • U).Ip p ≤ (Kernel.ofGraphon W + θ • U).Ip p
  rw [h0, ← hIV, hmin]
  exact phiVar_le_of_feasible H hp0 hp1 hfeas

/-- The first-order condition along `cU + t·1`. -/
theorem first_order_affine (H : SimpleGraph V) [DecidableRel H.Adj] {p r b : ℝ}
    (hp0 : 0 < p) (hpb : p ≤ b) (hb1 : b < 1) {W : Graphon} (hmin : W.Ip p = phiVar H p r)
    (hact : W.tDensity H = r ^ H.edgeFinset.card) (hmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc p b)
    (U : Kernel) (c t : ℝ)
    (h : 0 < c * (∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ)
      + t * ∫ z, derivKernel H W z.1 z.2 ∂gμ) :
    0 ≤ c * (∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ)
      + t * ∫ z, Jp' p (W.toFun z.1 z.2) ∂gμ := by
  have hD1 : Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2) gμ := by
    have h := integrable_derivKernel_mul H W oneKernel
    simp only [oneKernel_apply, mul_one] at h
    exact h
  have hJ1 : Integrable (fun z : ℝ × ℝ => Jp' p (W.toFun z.1 z.2)) gμ := by
    have h := integrable_Jp'_mul W oneKernel hp0 (hpb.trans_lt hb1) hp0 hb1 hmem
    simp only [oneKernel_apply, mul_one] at h
    exact h
  have hkey := first_order_condition H hp0 hpb hb1 hmin hact hmem (c • U + t • oneKernel)
  have e1 : ∀ (g : ℝ × ℝ → ℝ), (fun z : ℝ × ℝ => g z * (c • U + t • oneKernel).toFun z.1 z.2)
      = fun z => c * (g z * U.toFun z.1 z.2) + t * g z := by
    intro g; funext z
    show g z * (c * U.toFun z.1 z.2 + t * 1) = _
    ring
  rw [e1, integral_add ((integrable_derivKernel_mul H W U).const_mul c) (hD1.const_mul t),
    integral_const_mul, integral_const_mul] at hkey
  have hkey' := hkey h
  rw [e1 (fun z => Jp' p (W.toFun z.1 z.2)),
    integral_add ((integrable_Jp'_mul W U hp0 (hpb.trans_lt hb1) hp0 hb1 hmem).const_mul c)
      (hJ1.const_mul t),
    integral_const_mul, integral_const_mul] at hkey'
  exact hkey'

/-- **The multiplier identity.**  `∫∫ J_p'(W) U = μ ∫∫ 𝒟_W U` for every bounded symmetric `U`,
with `μ = ∫∫ J_p'(W) / ∫∫ 𝒟_W ≥ 0`. -/
theorem integral_Jp'_mul_eq (H : SimpleGraph V) [DecidableRel H.Adj] {p r b : ℝ}
    (hp0 : 0 < p) (hpb : p ≤ b) (hb1 : b < 1) {W : Graphon} (hmin : W.Ip p = phiVar H p r)
    (hact : W.tDensity H = r ^ H.edgeFinset.card) (hmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc p b)
    (hA : 0 < ∫ z, derivKernel H W z.1 z.2 ∂gμ) :
    0 ≤ (∫ z, Jp' p (W.toFun z.1 z.2) ∂gμ) / ∫ z, derivKernel H W z.1 z.2 ∂gμ ∧
      ∀ U : Kernel, ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ
        = ((∫ z, Jp' p (W.toFun z.1 z.2) ∂gμ) / ∫ z, derivKernel H W z.1 z.2 ∂gμ)
          * ∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := by
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = ∫ z, derivKernel H W z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ∫ z, Jp' p (W.toFun z.1 z.2) ∂gμ := ⟨_, rfl⟩
  rw [← hA_def] at hA ⊢
  rw [← hB_def]
  have hstep := first_order_affine H hp0 hpb hb1 hmin hact hmem
  have hB : 0 ≤ B := by
    have h := hstep oneKernel 0 1 (by rw [← hA_def]; linarith)
    rw [← hB_def] at h
    linarith
  refine ⟨div_nonneg hB hA.le, fun U => ?_⟩
  obtain ⟨L₁, hL₁⟩ : ∃ x : ℝ, x = ∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ :=
    ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ x : ℝ, x = ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ :=
    ⟨_, rfl⟩
  rw [← hL₁, ← hL₂]
  -- `c L₂ ≥ (B/A) c L₁` for `c = ±1`
  have hside : ∀ c : ℝ, (B / A) * (c * L₁) ≤ c * L₂ := by
    intro c
    by_contra hlt
    push Not at hlt
    obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = (B / A) * (c * L₁) - c * L₂ := ⟨_, rfl⟩
    have hd : 0 < d := by rw [hd_def]; linarith
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = d / (B + 1) := ⟨_, rfl⟩
    have hs : 0 < s := hs_def ▸ div_pos hd (by linarith)
    have h := hstep U c (-(c * L₁) / A + s) (by
      rw [← hL₁, ← hA_def]
      have : (-(c * L₁) / A + s) * A = -(c * L₁) + s * A := by field_simp
      nlinarith [mul_pos hs hA])
    rw [← hL₂, ← hB_def] at h
    have e : c * L₂ + (-(c * L₁) / A + s) * B = -d + s * B := by
      rw [hd_def]; field_simp; ring
    have e2 : s * B < d := by
      rw [hs_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have h1 := hside 1
  have h2 := hside (-1)
  simp only [one_mul, neg_one_mul, mul_neg] at h1 h2
  linarith

/-- The product of two kernels is integrable. -/
theorem integrable_kernel_mul (U U' : Kernel) :
    Integrable (fun z : ℝ × ℝ => U.toFun z.1 z.2 * U'.toFun z.1 z.2) gμ := by
  obtain ⟨C, hC⟩ := U.bdd'
  obtain ⟨C', hC'⟩ := U'.bdd'
  refine integrable_of_abs_le (U.meas'.mul U'.meas') (C * C') fun z => ?_
  rw [abs_mul]
  exact mul_le_mul (hC z.1 z.2) (hC' z.1 z.2) (abs_nonneg _) ((abs_nonneg _).trans (hC 0 0))

/-- **The multiplier of `lem:upper-tail-multiplier` from the bounds of
`lem:upper-tail-basic`.** -/
theorem multiplier_of_bounds (H : SimpleGraph V) [DecidableRel H.Adj]
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    {W : Graphon} (hmin : W.Ip p = phiVar H p r)
    (hlow : ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2) (hact : W.tDensity H = r ^ H.edgeFinset.card)
    {γ : ℝ} (hγ : 0 < γ) (hup : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - γ) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = μ * derivKernel H W z.1 z.2) ∧
      ∃ a b : ℝ, p < a ∧ a ≤ b ∧ b < 1 ∧ ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc a b := by
  have hp1 : p < 1 := lt_trans hpr hr1
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = max (1 - γ) p := ⟨_, rfl⟩
  have hpb : p ≤ b := hb_def ▸ le_max_right _ _
  have hb1 : b < 1 := hb_def ▸ max_lt (by linarith) hp1
  have hmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc p b := by
    filter_upwards [hlow, hup] with z h1 h2
    exact ⟨h1, h2.trans (hb_def ▸ le_max_left _ _)⟩
  -- `∫∫ 𝒟_W > 0`
  obtain ⟨c₀, hc₀_def⟩ : ∃ c₀ : ℝ, c₀ = (H.edgeFinset.card : ℝ) * p ^ (H.edgeFinset.card - 1) :=
    ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by
    have hmR : (0:ℝ) < H.edgeFinset.card := by exact_mod_cast (by omega : 0 < H.edgeFinset.card)
    rw [hc₀_def]; positivity
  have hD_ge : ∀ᵐ z ∂gμ, c₀ ≤ derivKernel H W z.1 z.2 := by
    rw [hc₀_def]; exact derivKernel_ge H W hp0.le hlow
  have hD1 : Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2) gμ := by
    have h := integrable_derivKernel_mul H W oneKernel
    simp only [oneKernel_apply, mul_one] at h
    exact h
  have hA : 0 < ∫ z, derivKernel H W z.1 z.2 ∂gμ := by
    have h := integral_mono_ae (integrable_const c₀) hD1 hD_ge
    rw [integral_const, probReal_univ, one_smul] at h
    linarith
  obtain ⟨hμ0, hlin⟩ := integral_Jp'_mul_eq H hp0 hpb hb1 hmin hact hmem hA
  obtain ⟨μ, hμ_def⟩ : ∃ μ : ℝ,
      μ = (∫ z, Jp' p (W.toFun z.1 z.2) ∂gμ) / ∫ z, derivKernel H W z.1 z.2 ∂gμ := ⟨_, rfl⟩
  rw [← hμ_def] at hμ0 hlin
  -- the kernel `G = J_p'(W') - μ𝒟_W`, with `W'` a pointwise bounded representative of `W`
  obtain ⟨W', hW'mem, hW'ae⟩ := W.exists_clamp hp0.le hpb hb1.le hmem
  let G : Kernel :=
    { toFun := fun x y => Jp' p (W'.toFun x y) - μ * derivKernel H W x y
      symm' := fun x y => by
        show Jp' p (W'.toFun x y) - μ * derivKernel H W x y
          = Jp' p (W'.toFun y x) - μ * derivKernel H W y x
        rw [W'.symm' x y, derivKernel_symm H W x y]
      meas' := ((measurable_Jp' p).comp W'.measurable_uncurry).sub
        ((measurable_derivKernel H W).const_mul μ)
      bdd' := ⟨Jp' p b + |μ| * H.edgeFinset.card, fun x y => by
        have hD := derivKernel_mem_Icc H W x y
        have h1 := abs_Jp'_le hp0 hb1 (hW'mem x y)
        have h2 : |μ * derivKernel H W x y| ≤ |μ| * H.edgeFinset.card := by
          rw [abs_mul, abs_of_nonneg hD.1]
          exact mul_le_mul_of_nonneg_left hD.2 (abs_nonneg μ)
        exact (abs_sub _ _).trans (add_le_add h1 h2)⟩ }
  have hGapply : ∀ z : ℝ × ℝ, G.toFun z.1 z.2
      = Jp' p (W'.toFun z.1 z.2) - μ * derivKernel H W z.1 z.2 := fun z => rfl
  have hGG : ∫ z, G.toFun z.1 z.2 * G.toFun z.1 z.2 ∂gμ = 0 := by
    have hcongr : ∫ z, G.toFun z.1 z.2 * G.toFun z.1 z.2 ∂gμ
        = ∫ z, (Jp' p (W.toFun z.1 z.2) * G.toFun z.1 z.2
          - μ * (derivKernel H W z.1 z.2 * G.toFun z.1 z.2)) ∂gμ := by
      refine integral_congr_ae ?_
      filter_upwards [hW'ae] with z hz
      rw [hGapply z, hz]
      ring
    rw [hcongr, integral_sub (integrable_Jp'_mul W G hp0 (hpb.trans_lt hb1) hp0 hb1 hmem)
      ((integrable_derivKernel_mul H W G).const_mul μ), integral_const_mul, hlin G, sub_self]
  have hG0 : ∀ᵐ z ∂gμ, G.toFun z.1 z.2 * G.toFun z.1 z.2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg _)
      (integrable_kernel_mul G G)).mp hGG
  have hEL : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = μ * derivKernel H W z.1 z.2 := by
    filter_upwards [hG0, hW'ae] with z h1 h2
    have h3 : G.toFun z.1 z.2 = 0 := mul_self_eq_zero.mp h1
    rw [hGapply z, h2] at h3
    linarith
  -- `μ > 0`
  have hmono := Jp'_strictMonoOn hp0 hp1
  have hWmem01 : ∀ w ∈ Icc p b, w ∈ Ioo (0:ℝ) 1 := fun w hw =>
    ⟨lt_of_lt_of_le hp0 hw.1, lt_of_le_of_lt hw.2 hb1⟩
  have hμ : 0 < μ := by
    rcases hμ0.lt_or_eq with h | h
    · exact h
    exfalso
    have hWp : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = p := by
      filter_upwards [hEL, hmem] with z h1 h2
      rw [← h, zero_mul, ← Jp'_self hp0 hp1] at h1
      exact hmono.injOn (hWmem01 _ h2) ⟨hp0, hp1⟩ h1
    have ht := tDensity_ae_const W H hWp
    rw [hact] at ht
    have hlt : p ^ H.edgeFinset.card < r ^ H.edgeFinset.card :=
      pow_lt_pow_left₀ hpr hp0.le (by omega)
    linarith
  -- the compact subinterval
  obtain ⟨a, ha0, ha1, haeq, hpa⟩ := exists_Jp'_eq hp0 hp1 (μ * c₀)
  refine ⟨μ, hμ, hEL, a, max b a, hpa (mul_pos hμ hc₀), le_max_right _ _, max_lt hb1 ha1, ?_⟩
  filter_upwards [hEL, hmem, hD_ge] with z h1 h2 h3
  refine ⟨?_, h2.2.trans (le_max_left _ _)⟩
  by_contra hlt
  push Not at hlt
  have h4 : Jp' p (W.toFun z.1 z.2) < Jp' p a := hmono (hWmem01 _ h2) ⟨ha0, ha1⟩ hlt
  have h5 : μ * c₀ ≤ μ * derivKernel H W z.1 z.2 := mul_le_mul_of_nonneg_left h3 hμ.le
  linarith

end UpperTailSupport

end UpperTailMultipodality
