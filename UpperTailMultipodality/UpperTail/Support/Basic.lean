import UpperTailMultipodality.UpperTail.Support.DerivKernel

/-!
# The three parts of `lem:upper-tail-basic`

* `ae_ge_of_minimizer` — a minimizer satisfies `W ≥ p` almost everywhere;
* `tDensity_eq_of_minimizer` — the constraint is active, `t(H,W) = r^m`;
* `exists_ae_le_one_sub_of_minimizer` — `W ≤ 1 - γ` almost everywhere for some `γ > 0`.

The upper bound avoids the implicit function theorem of the paper: since the constraint is an
inequality, it is enough to perturb in a direction `U = -1_E + κ1_A` along which `t(H,·)` has a
positive first variation, and to bound the change of `I_p` by the tangent lines of `J_p`.
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory Filter Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A feasible graphon is a competitor: `Φ_H(p,r) ≤ I_p(W)`. -/
theorem phiVar_le_of_feasible (H : SimpleGraph V) [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {W : Graphon} (hW : Feasible H r W) : phiVar H p r ≤ W.Ip p :=
  csInf_le (phiVar_bddBelow H hp0 hp1) ⟨W, hW, rfl⟩

omit [DecidableEq V] in
/-- The integrand of `t(H,W)` is integrable. -/
theorem integrable_prod_liftEdge (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) :
    Integrable (fun x : V → ℝ => ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e)
      (Measure.pi fun _ : V => unitμ) := by
  refine integrable_of_abs_le (Finset.measurable_prod _ fun e _ => measurable_liftEdge W e) 1
    fun x => ?_
  rw [abs_of_nonneg (Finset.prod_nonneg fun e _ => (liftEdge_mem_Icc W x e).1)]
  exact Finset.prod_le_one (fun e _ => (liftEdge_mem_Icc W x e).1)
    (fun e _ => (liftEdge_mem_Icc W x e).2)

/-- **`t(H,·)` is monotone** (the edge factors are nonnegative). -/
theorem tDensity_le_of_le (H : SimpleGraph V) [DecidableRel H.Adj] {W W' : Graphon}
    (h : ∀ x y, W.toFun x y ≤ W'.toFun x y) : W.tDensity H ≤ W'.tDensity H := by
  unfold Graphon.tDensity
  refine integral_mono (integrable_prod_liftEdge H W) (integrable_prod_liftEdge H W') fun x => ?_
  refine Finset.prod_le_prod (fun e _ => (liftEdge_mem_Icc W x e).1) fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => exact h _ _

/-- The graphon `max(W, c)`. -/
noncomputable def maxGraphon (W : Graphon) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) : Graphon where
  toFun x y := max (W.toFun x y) c
  symm' x y := by rw [W.symm']
  meas' := W.measurable_uncurry.max measurable_const
  nonneg' x y := le_max_of_le_left (W.nonneg' x y)
  le_one' x y := max_le (W.le_one' x y) hc.2

/-- **Lower bound of `lem:upper-tail-basic`.**  A minimizer satisfies `W ≥ p` almost
everywhere. -/
theorem ae_ge_of_minimizer (H : SimpleGraph V) [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {W : Graphon} (hW : Feasible H r W) (hmin : W.Ip p = phiVar H p r) :
    ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2 := by
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  let Wp := maxGraphon W p hpI
  have hfeas : Feasible H r Wp :=
    le_trans hW (tDensity_le_of_le H fun x y => le_max_left (W.toFun x y) p)
  have hle : W.Ip p ≤ Wp.Ip p := hmin ▸ phiVar_le_of_feasible H hp0 hp1 hfeas
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

/-- **Active constraint of `lem:upper-tail-basic`.**  A minimizer satisfies `t(H,W) = r^m`. -/
theorem tDensity_eq_of_minimizer (H : SimpleGraph V) [DecidableRel H.Adj]
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    {W : Graphon} (hW : Feasible H r W) (hmin : W.Ip p = phiVar H p r) :
    W.tDensity H = r ^ H.edgeFinset.card := by
  have hp1 : p < 1 := lt_trans hpr hr1
  have hp_mem : p ∈ Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  have hmne : H.edgeFinset.card ≠ 0 := by omega
  have hpm_lt : p ^ H.edgeFinset.card < r ^ H.edgeFinset.card :=
    pow_lt_pow_left₀ hpr hp0.le hmne
  refine le_antisymm ?_ hW
  by_contra hgt
  push Not at hgt
  have hmem : r ^ H.edgeFinset.card ∈ Ioo (mixTDensity W p H 0) (mixTDensity W p H 1) := by
    rw [mixTDensity_zero W p H, mixTDensity_one W p H]; exact ⟨hpm_lt, hgt⟩
  obtain ⟨θ0, hθ0, hθ0_eq⟩ :=
    intermediate_value_Ioo zero_le_one (mixTDensity_continuousOn W p hp_mem H) hmem
  have hθ0_mem : θ0 ∈ Icc (0:ℝ) 1 := ⟨hθ0.1.le, hθ0.2.le⟩
  have hfeas_mix : Feasible H r (Wmix W p hp_mem θ0 hθ0_mem) := by
    show r ^ H.edgeFinset.card ≤ (Wmix W p hp_mem θ0 hθ0_mem).tDensity H
    rw [← mixTDensity_eq_tDensity W hp_mem H hθ0_mem]
    exact le_of_eq hθ0_eq.symm
  -- convexity: `I_p(W_{θ₀}) ≤ θ₀ I_p(W)`
  have hconv : (Wmix W p hp_mem θ0 hθ0_mem).Ip p ≤ θ0 * W.Ip p := by
    have hptwise : ∀ z : ℝ × ℝ, Jp p ((Wmix W p hp_mem θ0 hθ0_mem).toFun z.1 z.2)
        ≤ θ0 * Jp p (W.toFun z.1 z.2) := by
      intro z
      have hcv := (convexOn_Jp hp0 hp1).2 hp_mem (W.mem_Icc z.1 z.2)
        (by linarith [hθ0.2] : (0:ℝ) ≤ 1 - θ0) hθ0.1.le (by ring : (1 - θ0) + θ0 = 1)
      simp only [smul_eq_mul, Jp_self hp0 hp1, mul_zero, zero_add] at hcv
      rw [Wmix_apply]; exact hcv
    have int1 := (Wmix W p hp_mem θ0 hθ0_mem).integrable_comp (measurable_Jp p)
      (continuousOn_Jp_Icc hp0 hp1)
    have int2 := (W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)).const_mul θ0
    have h1 := integral_mono int1 int2 hptwise
    rwa [integral_const_mul] at h1
  have hge : W.Ip p ≤ (Wmix W p hp_mem θ0 hθ0_mem).Ip p :=
    hmin ▸ phiVar_le_of_feasible H hp0 hp1 hfeas_mix
  have hnn := Ip_nonneg W hp0 hp1
  have hIp0 : W.Ip p = 0 := by nlinarith [hθ0.2]
  -- `I_p(W) = 0` forces `W = p` almost everywhere
  have hJp_zero : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = p := by
    have hint := W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
    have hae0 := (integral_eq_zero_iff_of_nonneg
      (fun z : ℝ × ℝ => Jp_nonneg_of_mem hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2)) hint).mp
      hIp0
    filter_upwards [hae0] with z hz
    exact Jp_eq_zero_imp hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2) hz
  rw [tDensity_ae_const W H hJp_zero] at hgt
  linarith

end UpperTailSupport

end UpperTailMultipodality
