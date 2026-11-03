import UpperTailMultipodality.UpperTail.Support.UpperBound
import UpperTailMultipodality.RowCriterion.Defs

/-!
# Basic properties of joint upper-tail minimizers (`lem:upper-tail-basic`)

Fix `p ∈ (0,1)`, graphs `H_1, …, H_s` and targets `τ_1, …, τ_s`, and let `W` be a minimizer of
`eq:joint-variational-problem`, that is, a feasible graphon (`JointFeasible`) with `I_p(W) ≤ I_p(V')` for
every feasible `V'`.  Assuming that the constant graphon `W ≡ p` is *not* feasible, this file
proves the three parts of `lem:upper-tail-basic`:

* `joint_ae_ge` — `W ≥ p` almost everywhere;
* `joint_exists_active` — the active set `𝒜` is nonempty;
* `joint_exists_ae_le_one_sub` — `W ≤ 1 - γ` almost everywhere for some `γ > 0`.

As in the one-constraint case (`UpperTail/Support/UpperBound.lean`), the upper bound avoids the
implicit function theorem: the constraints are inequalities, so it is enough to perturb along
`Z_Λ = -1_E + κ1_A` with `κ = 2 max_j (∫_E 𝒟_{j,W})/(∫_A 𝒟_{j,W})`, which makes the first
variation of *every* `t(H_j,·)` at least `∫_E 𝒟_{j,W} > 0`.  This is the paper's `ĉ_Λ` doubled;
with the strict first-order increase the paper's extra correction `θ²K1_A` is not needed.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Set Topology UpperTailSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Feasibility for the joint problem `eq:joint-variational-problem`**: `t(H_j,W) ≥ τ_j` for every `j`. -/
def JointFeasible {ι : Type*} (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (τ : ι → ℝ) (W : Graphon) : Prop :=
  ∀ j, τ j ≤ W.tDensity (Hs j)

section Family

variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {τ : ι → ℝ} {p : ℝ} {W : Graphon}

omit [Fintype ι] in
/-- **Lower bound of `lem:upper-tail-basic`.**  A minimizer satisfies `W ≥ p` almost
everywhere, because replacing `W` by `max(W,p)` keeps every constraint satisfied and does not
increase `I_p`. -/
theorem joint_ae_ge (hp0 : 0 < p) (hp1 : p < 1) (hfeas : JointFeasible Hs τ W)
    (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p) :
    ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2 := by
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  set Wp := maxGraphon W p hpI with hWp
  have hfeas' : JointFeasible Hs τ Wp := fun j =>
    (hfeas j).trans (tDensity_le_of_le (Hs j) fun x y => le_max_left (W.toFun x y) p)
  have hle : W.Ip p ≤ Wp.Ip p := hmin Wp hfeas'
  have hpt : ∀ z : ℝ × ℝ, 0 ≤ Jp p (W.toFun z.1 z.2) - Jp p (Wp.toFun z.1 z.2) := by
    intro z
    show 0 ≤ Jp p (W.toFun z.1 z.2) - Jp p (max (W.toFun z.1 z.2) p)
    by_cases h : p ≤ W.toFun z.1 z.2
    · rw [max_eq_left h, sub_self]
    · rw [max_eq_right (le_of_not_ge h), Jp_self hp0 hp1, sub_zero]
      exact Jp_nonneg_of_mem hp0 hp1 (W.nonneg' _ _) (W.le_one' _ _)
  have hiW := W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hiWp := Wp.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hint0 : ∫ z, (Jp p (W.toFun z.1 z.2) - Jp p (Wp.toFun z.1 z.2)) ∂gμ = 0 := by
    rw [integral_sub hiW hiWp]
    have h1 : 0 ≤ ∫ z, (Jp p (W.toFun z.1 z.2) - Jp p (Wp.toFun z.1 z.2)) ∂gμ :=
      integral_nonneg hpt
    rw [integral_sub hiW hiWp] at h1
    exact le_antisymm (by unfold Graphon.Ip at hle; linarith) h1
  have hae := (integral_eq_zero_iff_of_nonneg hpt (hiW.sub hiWp)).mp hint0
  filter_upwards [hae] with z hz
  by_contra hlt
  push Not at hlt
  have hz' : Jp p (W.toFun z.1 z.2) - Jp p (max (W.toFun z.1 z.2) p) = 0 := hz
  rw [max_eq_right hlt.le, Jp_self hp0 hp1, sub_zero] at hz'
  exact hlt.ne (Jp_eq_zero_imp hp0 hp1 (W.nonneg' _ _) (W.le_one' _ _) hz')

/-- **Active constraint of `lem:upper-tail-basic`.**  If `W ≡ p` is not feasible, then some
constraint of a minimizer is active.  Otherwise the graphons `W_λ = p + λ(W - p)` would be
feasible for `λ < 1` close to `1`, with `I_p(W_λ) ≤ λ I_p(W) < I_p(W)`. -/
theorem joint_exists_active (hp0 : 0 < p) (hp1 : p < 1) (hfeas : JointFeasible Hs τ W)
    (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p)
    (hnf : ¬ ∀ j, τ j ≤ p ^ (Hs j).edgeFinset.card) :
    ∃ j, W.tDensity (Hs j) = τ j := by
  have hp_mem : p ∈ Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ j, τ j < W.tDensity (Hs j) := fun j =>
    lt_of_le_of_ne (hfeas j) (fun h => hcon j h.symm)
  -- `I_p(W) > 0`, since `W ≡ p` is not feasible
  have hIpos : 0 < W.Ip p := by
    rcases (Ip_nonneg W hp0 hp1).lt_or_eq with h | h
    · exact h
    · exfalso
      refine hnf fun j => ?_
      have hae := ae_eq_of_Ip_eq_zero hp0 hp1 h.symm
      rw [← tDensity_ae_const W (Hs j) hae]
      exact hfeas j
  -- a mixing parameter `θ < 1` keeping all constraints strict
  have hcont : ∀ j, ContinuousWithinAt (mixTDensity W p (Hs j)) (Icc 0 1) 1 := fun j =>
    mixTDensity_continuousOn W p hp_mem (Hs j) 1 ⟨zero_le_one, le_rfl⟩
  have hev : ∀ j, ∀ᶠ θ in 𝓝[Icc (0:ℝ) 1] 1, τ j < mixTDensity W p (Hs j) θ := by
    intro j
    have h1 : τ j < mixTDensity W p (Hs j) 1 := by
      rw [mixTDensity_one]; exact hstrict j
    exact hcont j (Ioi_mem_nhds h1)
  have hall : ∀ᶠ θ in 𝓝[Icc (0:ℝ) 1] 1, ∀ j, τ j < mixTDensity W p (Hs j) θ :=
    Filter.eventually_all.mpr hev
  have hNeBot : (𝓝[Ico (0:ℝ) 1] 1).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨θ, hθall, hθmem⟩ :=
    ((hall.filter_mono (nhdsWithin_mono _ Ico_subset_Icc_self)).and self_mem_nhdsWithin).exists
  have hθ_mem : θ ∈ Icc (0:ℝ) 1 := ⟨hθmem.1, hθmem.2.le⟩
  -- the mixed graphon is feasible
  have hfeas_mix : JointFeasible Hs τ (Wmix W p hp_mem θ hθ_mem) := by
    intro j
    rw [← mixTDensity_eq_tDensity W hp_mem (Hs j) hθ_mem]
    exact (hθall j).le
  -- convexity: `I_p(W_θ) ≤ θ I_p(W)`
  have hconv : (Wmix W p hp_mem θ hθ_mem).Ip p ≤ θ * W.Ip p := by
    have hptwise : ∀ z : ℝ × ℝ, Jp p ((Wmix W p hp_mem θ hθ_mem).toFun z.1 z.2)
        ≤ θ * Jp p (W.toFun z.1 z.2) := by
      intro z
      have hcv := (convexOn_Jp hp0 hp1).2 hp_mem (W.mem_Icc z.1 z.2)
        (by linarith [hθ_mem.2] : (0:ℝ) ≤ 1 - θ) hθ_mem.1 (by ring : (1 - θ) + θ = 1)
      simp only [smul_eq_mul, Jp_self hp0 hp1, mul_zero, zero_add] at hcv
      rw [Wmix_apply]; exact hcv
    have int1 := (Wmix W p hp_mem θ hθ_mem).integrable_comp (measurable_Jp p)
      (continuousOn_Jp_Icc hp0 hp1)
    have int2 := (W.integrable_comp (measurable_Jp p)
      (continuousOn_Jp_Icc hp0 hp1)).const_mul θ
    have h1 := integral_mono int1 int2 hptwise
    rwa [integral_const_mul] at h1
  have hge := hmin _ hfeas_mix
  nlinarith [hθmem.2]

/-! ### The upper bound -/

/-- The final arithmetic of the upper bound. -/
private theorem joint_upper_bound_arith {θ κ C mA mE Kap cδ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hmE : 0 < mE) (hκmA : κ * mA ≤ Kap * mE) (hcδ : Kap * C + 1 ≤ cδ) :
    θ * κ * C * mA - θ * cδ * mE < 0 := by
  have h1 : θ * κ * C * mA ≤ θ * C * (Kap * mE) := by
    calc θ * κ * C * mA = θ * C * (κ * mA) := by ring
      _ ≤ θ * C * (Kap * mE) := by
          exact mul_le_mul_of_nonneg_left hκmA (by positivity)
  have h2 : θ * (Kap * C + 1) * mE ≤ θ * cδ * mE := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcδ hθ.le) hmE.le
  nlinarith [mul_pos hθ hmE]

/-- **Upper bound of `lem:upper-tail-basic`.**  A minimizer with `W ≥ p` almost everywhere and
some `t(H_{j₀},W) < 1` satisfies `W ≤ 1 - γ` almost everywhere for some `γ > 0`. -/
theorem joint_exists_ae_le_one_sub (hm : ∀ j, 1 ≤ (Hs j).edgeFinset.card) (hp0 : 0 < p)
    (hp1 : p < 1) (hfeas : JointFeasible Hs τ W)
    (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p)
    (hlow : ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2) {j₀ : ι} (ht1 : W.tDensity (Hs j₀) < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - γ := by
  classical
  obtain ⟨γ₀, hγ₀, hγ₀1, hA0⟩ := exists_measure_le_one_sub_ne_zero (Hs j₀) ht1
  by_contra hcon
  have hEpos : ∀ δ : ℝ, 0 < δ → gμ (nearOneSet W δ) ≠ 0 := by
    intro δ hδ hzero
    refine hcon ⟨δ, hδ, ae_iff.mpr ?_⟩
    have hset : {a : ℝ × ℝ | ¬W.toFun a.1 a.2 ≤ 1 - δ} = nearOneSet W δ := by
      ext z; simp only [nearOneSet, mem_ofPred_eq, not_le]
    rw [hset]; exact hzero
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
  -- the lower and upper bounds for the derivative kernels
  set c₀ : ι → ℝ := fun j => ((Hs j).edgeFinset.card : ℝ) * p ^ ((Hs j).edgeFinset.card - 1)
    with hc₀def
  have hmR : ∀ j, (0:ℝ) < (Hs j).edgeFinset.card := fun j => by
    exact_mod_cast (by have := hm j; omega : 0 < (Hs j).edgeFinset.card)
  have hc₀ : ∀ j, 0 < c₀ j := fun j => by
    rw [hc₀def]
    exact mul_pos (hmR j) (pow_pos hp0 _)
  have hD_ge : ∀ j, ∀ᵐ z ∂gμ, c₀ j ≤ derivKernel (Hs j) W z.1 z.2 := fun j => by
    rw [hc₀def]; exact derivKernel_ge (Hs j) W hp0.le hlow
  have hD_mem : ∀ j, ∀ x y, derivKernel (Hs j) W x y ∈ Icc (0:ℝ) (Hs j).edgeFinset.card :=
    fun j => derivKernel_mem_Icc (Hs j) W
  -- the constants
  set C₁ : ℝ := max (Jp' p (1 - γ₀ / 2)) 0 with hC₁def
  have hC₁0 : 0 ≤ C₁ := hC₁def ▸ le_max_right _ _
  have hC₁ : Jp' p (1 - γ₀ / 2) ≤ C₁ := hC₁def ▸ le_max_left _ _
  set Kap : ℝ := 2 * Finset.univ.sup' hne (fun j => ((Hs j).edgeFinset.card : ℝ) / c₀ j)
    with hKapdef
  have hKap0 : 0 ≤ Kap := by
    rw [hKapdef]
    have h := Finset.le_sup' (f := fun j => ((Hs j).edgeFinset.card : ℝ) / c₀ j)
      (Finset.mem_univ j₀)
    have h0 : (0:ℝ) ≤ ((Hs j₀).edgeFinset.card : ℝ) / c₀ j₀ :=
      div_nonneg (hmR j₀).le (hc₀ j₀).le
    linarith
  set Kc : ℝ := Kap * C₁ with hKcdef
  obtain ⟨t₀, ht₀0, ht₀1, ht₀eq, -⟩ := exists_Jp'_eq hp0 hp1 (Kc + 1)
  set δ : ℝ := min (γ₀ / 2) ((1 - t₀) / 2) with hδdef
  have hδ0 : 0 < δ := hδdef ▸ lt_min (by linarith) (by linarith)
  have hδγ : δ ≤ γ₀ / 2 := hδdef ▸ min_le_left _ _
  have hδt : δ ≤ (1 - t₀) / 2 := hδdef ▸ min_le_right _ _
  have hδγ' : δ < γ₀ := by linarith
  have hδ1 : 2 * δ < 1 := by linarith
  have hcδ : Kc + 1 ≤ Jp' p (1 - 2 * δ) := by
    rw [← ht₀eq]
    exact (Jp'_strictMonoOn hp0 hp1).monotoneOn ⟨ht₀0, ht₀1⟩ ⟨by linarith, by linarith⟩
      (by linarith)
  -- integrals over `E = {W > 1 - δ}` and `A = {W ≤ 1 - γ₀}`
  have hEm := measurableSet_nearOneSet W δ
  have hAm := measurableSet_belowSet W γ₀
  have hind_int : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      Integrable (S.indicator (1 : ℝ × ℝ → ℝ)) gμ := fun S hS =>
    integrable_of_abs_le (measurable_one.indicator hS) 1 fun z => by
      rw [abs_of_nonneg (indicator_one_mem_Icc S z).1]; exact (indicator_one_mem_Icc S z).2
  have hDind_int : ∀ (j : ι) (S : Set (ℝ × ℝ)), MeasurableSet S →
      Integrable (fun z : ℝ × ℝ => derivKernel (Hs j) W z.1 z.2 * S.indicator 1 z) gμ :=
    fun j S hS => integrable_of_abs_le ((measurable_derivKernel (Hs j) W).mul
      (measurable_one.indicator hS)) (Hs j).edgeFinset.card fun z => by
        rw [abs_mul, abs_of_nonneg (hD_mem j z.1 z.2).1,
          abs_of_nonneg (indicator_one_mem_Icc S z).1]
        calc derivKernel (Hs j) W z.1 z.2 * S.indicator 1 z
            ≤ (Hs j).edgeFinset.card * 1 :=
              mul_le_mul (hD_mem j z.1 z.2).2 (indicator_one_mem_Icc S z).2
                (indicator_one_mem_Icc S z).1 (hmR j).le
          _ = _ := mul_one _
  have hmeas_pos : ∀ S : Set (ℝ × ℝ), MeasurableSet S → gμ S ≠ 0 →
      0 < ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ := by
    intro S hS hSne
    rw [integral_indicator_one hS, measureReal_def]
    exact ENNReal.toReal_pos hSne (measure_ne_top _ _)
  have hD_lower : ∀ (j : ι) (S : Set (ℝ × ℝ)), MeasurableSet S →
      c₀ j * ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ
        ≤ ∫ z, derivKernel (Hs j) W z.1 z.2 * S.indicator 1 z ∂gμ := by
    intro j S hS
    rw [← integral_const_mul]
    refine integral_mono_ae ((hind_int S hS).const_mul (c₀ j)) (hDind_int j S hS) ?_
    filter_upwards [hD_ge j] with z hz
    exact mul_le_mul_of_nonneg_right hz (indicator_one_mem_Icc S z).1
  have hD_upper : ∀ (j : ι) (S : Set (ℝ × ℝ)), MeasurableSet S →
      ∫ z, derivKernel (Hs j) W z.1 z.2 * S.indicator 1 z ∂gμ
        ≤ (Hs j).edgeFinset.card * ∫ z, S.indicator (1 : ℝ × ℝ → ℝ) z ∂gμ := by
    intro j S hS
    rw [← integral_const_mul]
    refine integral_mono (hDind_int j S hS) ((hind_int S hS).const_mul _) fun z => ?_
    exact mul_le_mul_of_nonneg_right (hD_mem j z.1 z.2).2 (indicator_one_mem_Icc S z).1
  set mE : ℝ := ∫ z, (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z ∂gμ with hmEdef
  set mA : ℝ := ∫ z, (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z ∂gμ with hmAdef
  set DE : ι → ℝ := fun j =>
    ∫ z, derivKernel (Hs j) W z.1 z.2 * (nearOneSet W δ).indicator 1 z ∂gμ with hDEdef
  set DA : ι → ℝ := fun j =>
    ∫ z, derivKernel (Hs j) W z.1 z.2 * (belowSet W γ₀).indicator 1 z ∂gμ with hDAdef
  have hmE : 0 < mE := hmEdef ▸ hmeas_pos _ hEm (hEpos δ hδ0)
  have hmA : 0 < mA := hmAdef ▸ hmeas_pos _ hAm hA0
  have hDE_ge : ∀ j, c₀ j * mE ≤ DE j := fun j => hD_lower j _ hEm
  have hDA_ge : ∀ j, c₀ j * mA ≤ DA j := fun j => hD_lower j _ hAm
  have hDE_le : ∀ j, DE j ≤ (Hs j).edgeFinset.card * mE := fun j => hD_upper j _ hEm
  have hDE_pos : ∀ j, 0 < DE j := fun j => lt_of_lt_of_le (mul_pos (hc₀ j) hmE) (hDE_ge j)
  have hDA_pos : ∀ j, 0 < DA j := fun j => lt_of_lt_of_le (mul_pos (hc₀ j) hmA) (hDA_ge j)
  -- the coefficient `κ = 2 ĉ_Λ`
  set κ : ℝ := 2 * Finset.univ.sup' hne (fun j => DE j / DA j) with hκdef
  have hκ_ge : ∀ j, 2 * (DE j / DA j) ≤ κ := fun j => by
    rw [hκdef]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (f := fun j => DE j / DA j) (Finset.mem_univ j)) (by norm_num)
  have hκ : 0 < κ := lt_of_lt_of_le
    (by have := div_pos (hDE_pos j₀) (hDA_pos j₀); linarith) (hκ_ge j₀)
  have hvar : ∀ j, DE j ≤ -DE j + κ * DA j := by
    intro j
    have h : 2 * DE j / DA j ≤ κ := by
      rw [mul_div_assoc]; exact hκ_ge j
    rw [div_le_iff₀ (hDA_pos j)] at h
    linarith
  have hκmA : κ * mA ≤ Kap * mE := by
    obtain ⟨j₁, -, hj₁⟩ := Finset.exists_mem_eq_sup' hne (fun j => DE j / DA j)
    have hκ1 : κ = 2 * (DE j₁ / DA j₁) := by rw [hκdef, hj₁]
    have hcne : c₀ j₁ ≠ 0 := (hc₀ j₁).ne'
    have hq : (0:ℝ) ≤ ((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE :=
      mul_nonneg (div_nonneg (hmR j₁).le (hc₀ j₁).le) hmE.le
    have hc : (((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE) * (c₀ j₁ * mA)
        = ((Hs j₁).edgeFinset.card : ℝ) * mE * mA := by
      field_simp
    have hmul : DE j₁ * mA ≤ (((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE) * DA j₁ := by
      have ha : DE j₁ * mA ≤ ((Hs j₁).edgeFinset.card : ℝ) * mE * mA :=
        mul_le_mul_of_nonneg_right (hDE_le j₁) hmA.le
      have hb : (((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE) * (c₀ j₁ * mA)
          ≤ (((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE) * DA j₁ :=
        mul_le_mul_of_nonneg_left (hDA_ge j₁) hq
      rw [hc] at hb
      linarith
    have h1 : DE j₁ / DA j₁ * mA ≤ ((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (hDA_pos j₁)]
      exact hmul
    have hsup : ((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁
        ≤ Finset.univ.sup' hne (fun j => ((Hs j).edgeFinset.card : ℝ) / c₀ j) :=
      Finset.le_sup' (f := fun j => ((Hs j).edgeFinset.card : ℝ) / c₀ j) (Finset.mem_univ j₁)
    have h2 := mul_le_mul_of_nonneg_right hsup hmE.le
    calc κ * mA = 2 * (DE j₁ / DA j₁ * mA) := by rw [hκ1]; ring
      _ ≤ 2 * (((Hs j₁).edgeFinset.card : ℝ) / c₀ j₁ * mE) := by linarith
      _ ≤ 2 * (Finset.univ.sup' hne (fun j => ((Hs j).edgeFinset.card : ℝ) / c₀ j) * mE) := by
          linarith
      _ = Kap * mE := by rw [hKapdef]; ring
  -- the first variation along `Z_Λ` is positive for every constraint
  have hDU : ∀ j, ∫ z, derivKernel (Hs j) W z.1 z.2 * (shiftKernel W δ γ₀ κ).toFun z.1 z.2 ∂gμ
      = -DE j + κ * DA j := by
    intro j
    have h1 : ∀ z : ℝ × ℝ,
        derivKernel (Hs j) W z.1 z.2 * (shiftKernel W δ γ₀ κ).toFun z.1 z.2
        = -(derivKernel (Hs j) W z.1 z.2 * (nearOneSet W δ).indicator 1 z)
          + κ * (derivKernel (Hs j) W z.1 z.2 * (belowSet W γ₀).indicator 1 z) := fun z => by
      rw [shiftKernel_apply]; ring
    simp_rw [h1]
    rw [integral_add (hDind_int j _ hEm).fun_neg ((hDind_int j _ hAm).const_mul κ), integral_neg,
      integral_const_mul]
  have hDUpos : ∀ j,
      0 < ∫ z, derivKernel (Hs j) W z.1 z.2 * (shiftKernel W δ γ₀ κ).toFun z.1 z.2 ∂gμ := by
    intro j
    rw [hDU j]
    have := hvar j
    have := hDE_pos j
    linarith
  have hexε := fun j : ι => exists_pos_lt_of_hasDerivAt_pos
    (first_variation (Hs j) W (shiftKernel W δ γ₀ κ)) (hDUpos j)
  choose εf hεf0 hεf using hexε
  set ε : ℝ := Finset.univ.inf' hne εf with hεdef
  have hε : 0 < ε := (Finset.lt_inf'_iff hne).mpr fun j _ => hεf0 j
  have hεle : ∀ j, ε ≤ εf j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hf0 : ∀ j, (Kernel.ofGraphon W + (0:ℝ) • shiftKernel W δ γ₀ κ).tDensity (Hs j)
      = W.tDensity (Hs j) := fun j =>
    kernel_tDensity_congr_ae (Hs j) (L := Kernel.ofGraphon W) (ae_of_all _ fun z => by simp)
  -- the step size
  set θ : ℝ := min (ε / 2) (min δ (γ₀ / (2 * κ))) with hθdef
  have hθ0 : 0 < θ := hθdef ▸ lt_min (by linarith) (lt_min hδ0 (by positivity))
  have hθε : θ < ε := hθdef ▸ (min_le_left _ _).trans_lt (by linarith)
  have hθδ : θ ≤ δ := hθdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hθκ : κ * θ ≤ γ₀ / 2 := by
    have h : θ ≤ γ₀ / (2 * κ) := hθdef ▸ (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hκθ0 : 0 < κ * θ := mul_pos hκ hθ0
  have hmemI := shift_mem_Icc (W := W) (κ := κ) hδγ' hθ0.le hθδ hδ1.le hκθ0.le (by linarith)
  set Vθ : Graphon := (Kernel.ofGraphon W + θ • shiftKernel W δ γ₀ κ).toGraphon
    (fun x y => (hmemI x y).1) (fun x y => (hmemI x y).2) with hVθdef
  -- `Vθ` is feasible, hence `I_p(W) ≤ I_p(Vθ)`
  have hfeasV : JointFeasible Hs τ Vθ := by
    intro j
    have h := hεf j θ hθ0 (hθε.trans_le (hεle j))
    rw [hf0 j] at h
    exact (hfeas j).trans h.le
  have hge : W.Ip p ≤ Vθ.Ip p := hmin Vθ hfeasV
  -- integrate the pointwise comparison of `J_p`
  have hpt : ∀ z : ℝ × ℝ, Jp p (Vθ.toFun z.1 z.2)
      ≤ Jp p (W.toFun z.1 z.2) + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z
        - θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z :=
    Jp_shift_le hp0 hp1 hδγ' hγ₀1 hθ0 hθδ hδ1 hκθ0 hθκ hC₁
  have hiW := W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hiV := Vθ.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hIV : Vθ.Ip p ≤ W.Ip p + θ * κ * C₁ * mA - θ * Jp' p (1 - 2 * δ) * mE := by
    have hi1 : Integrable (fun z : ℝ × ℝ => Jp p (W.toFun z.1 z.2)
        + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z) gμ :=
      hiW.add ((hind_int _ hAm).const_mul (θ * κ * C₁))
    have hi2 : Integrable (fun z : ℝ × ℝ =>
        θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z) gμ :=
      (hind_int _ hEm).const_mul (θ * Jp' p (1 - 2 * δ))
    have h : ∫ z, Jp p (Vθ.toFun z.1 z.2) ∂gμ ≤ ∫ z, (Jp p (W.toFun z.1 z.2)
        + θ * κ * C₁ * (belowSet W γ₀).indicator (1 : ℝ × ℝ → ℝ) z
        - θ * Jp' p (1 - 2 * δ) * (nearOneSet W δ).indicator (1 : ℝ × ℝ → ℝ) z) ∂gμ :=
      integral_mono hiV (hi1.sub hi2) hpt
    rw [integral_sub hi1 hi2, integral_add hiW ((hind_int _ hAm).const_mul _),
      integral_const_mul, integral_const_mul, ← hmAdef, ← hmEdef] at h
    exact h
  have hfinal := joint_upper_bound_arith hθ0 hC₁0 hmE hκmA hcδ
  linarith

/-! ### The value of the joint problem -/

/-- **The joint upper-tail value of `eq:joint-variational-problem`**,
`inf { I_p(W) : t(H_j,W) ≥ τ_j for every j }`. -/
noncomputable def jointVar (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] (p : ℝ)
    (τ : ι → ℝ) : ℝ :=
  sInf {y | ∃ W : Graphon, JointFeasible Hs τ W ∧ W.Ip p = y}

omit [Fintype ι] in
/-- A graphon attaining `jointVar` has the least `I_p` among the feasible graphons. -/
theorem Ip_le_of_jointVar (hp0 : 0 < p) (hp1 : p < 1) (hmin : W.Ip p = jointVar Hs p τ) :
    ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p := by
  intro V' hV'
  rw [hmin]
  refine csInf_le ⟨0, ?_⟩ ⟨V', hV', rfl⟩
  rintro y ⟨W'', -, rfl⟩
  exact Ip_nonneg W'' hp0 hp1

end Family

end UpperTailMultipodality
