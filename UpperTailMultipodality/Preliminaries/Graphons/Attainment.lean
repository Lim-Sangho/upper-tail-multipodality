import UpperTailMultipodality.Preliminaries.Graphons.CutContinuity
import UpperTailMultipodality.Preliminaries.Graphons.HomDensity

/-!
# Attainment of the upper-tail infimum (the direct method)

The infimum `Φ_H(p,r) = inf { I_p(W) : t(H,W) ≥ r^m }` of `eq:joint-variational-problem` with
`s = 1` is
attained.  This is the classical direct method, derived from three of the graph-limit facts
assumed in `Preliminaries/Graphons/CutContinuity.lean`:

* sequential cut-compactness `cut_seqCompact`,
* cut-continuity of the homomorphism density `tDensity_cutContinuous` (so the feasible set
  is cut-closed),
* lower semicontinuity of `I_p` `Ip_cut_lowerSemicontinuous`.

A minimizing sequence has a cut-convergent subsequence; its limit is feasible and has
`I_p ≤ Φ` by lower semicontinuity, hence attains `Φ`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

/-- `Φ_H(p,r)` is bounded below (by `0`), since `I_p ≥ 0`. -/
theorem phiVar_bddBelow {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    BddBelow {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y} := by
  refine ⟨0, ?_⟩
  rintro y ⟨W', _, rfl⟩
  exact Ip_nonneg W' hp0 hp1

/-- **`Φ_H(p,r)` is the infimum** of `eq:joint-variational-problem` with `s = 1`: for `0 < p < 1` and
`r ∈ [0,1]` the feasible set is nonempty (it contains `W ≡ r`), and the real `sInf` defining
`phiVar` is the greatest lower bound of the feasible costs. -/
theorem phiVar_isGLB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : r ∈ Set.Icc (0:ℝ) 1) :
    (∃ W : Graphon, Feasible H r W) ∧
      IsGLB {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y} (phiVar H p r) := by
  have hfeas : Feasible H r (constGraphon r hr) := le_of_eq (tDensity_constGraphon hr H).symm
  exact ⟨⟨_, hfeas⟩, isGLB_csInf ⟨_, constGraphon r hr, hfeas, rfl⟩ (phiVar_bddBelow H hp0 hp1)⟩

/-- **Attainment of the upper-tail infimum.**  Derived (no longer assumed) from sequential
cut-compactness, cut-continuity of `t(H,·)`, and lower semicontinuity of `I_p`. -/
theorem feasible_attains {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ W : Graphon, Feasible H r W ∧ W.Ip p = phiVar H p r := by
  have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr0.le, hr1.le⟩
  have hbdd : BddBelow {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y} :=
    phiVar_bddBelow H hp0 hp1
  -- the variational set is nonempty (the constant graphon `r` is feasible)
  have hcfeas : Feasible H r (constGraphon r hr_mem) :=
    le_of_eq (tDensity_constGraphon hr_mem H).symm
  have hcIp : (constGraphon r hr_mem).Ip p = Jp p r := by
    unfold Graphon.Ip; simp only [constGraphon_apply]; rw [integral_const]; simp
  have hne : {y | ∃ W : Graphon, Feasible H r W ∧ W.Ip p = y}.Nonempty :=
    ⟨Jp p r, constGraphon r hr_mem, hcfeas, hcIp⟩
  -- a minimizing sequence `W n` with `Φ ≤ I_p(W n) < Φ + 1/(n+1)`
  have hex : ∀ n : ℕ, ∃ W : Graphon, Feasible H r W ∧
      phiVar H p r ≤ W.Ip p ∧ W.Ip p < phiVar H p r + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hyS, hylt⟩ :=
      exists_lt_of_csInf_lt hne (show phiVar H p r < phiVar H p r + 1 / ((n : ℝ) + 1) by linarith)
    have hyge : phiVar H p r ≤ y := csInf_le hbdd hyS
    obtain ⟨W, hWfeas, hWeq⟩ := hyS
    refine ⟨W, hWfeas, ?_, ?_⟩
    · rw [hWeq]; exact hyge
    · rw [hWeq]; exact hylt
  choose W hWfeas hWlb hWub using hex
  -- `I_p(W n) → Φ` by the squeeze `Φ ≤ I_p(W n) < Φ + 1/(n+1)`
  have hWtendsto : Tendsto (fun n => (W n).Ip p) atTop (𝓝 (phiVar H p r)) := by
    have hupper : Tendsto (fun n : ℕ => phiVar H p r + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (phiVar H p r)) := by
      have h : Tendsto (fun n : ℕ => phiVar H p r + 1 / ((n : ℝ) + 1)) atTop
          (𝓝 (phiVar H p r + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => hWlb n) (fun n => (hWub n).le)
  -- a cut-convergent subsequence; its limit is feasible and attains `Φ`
  obtain ⟨φ, Wlim, hφ, hcut⟩ := cut_seqCompact W
  have hfeas_lim : Feasible H r Wlim :=
    ge_of_tendsto' (tDensity_cutContinuous H hcut) (fun k => hWfeas (φ k))
  refine ⟨Wlim, hfeas_lim, le_antisymm ?_ (csInf_le hbdd ⟨Wlim, hfeas_lim, rfl⟩)⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hsub : Tendsto (fun k => (W (φ k)).Ip p) atTop (𝓝 (phiVar H p r)) :=
    hWtendsto.comp hφ.tendsto_atTop
  have hev : ∀ᶠ k in atTop, (W (φ k)).Ip p ≤ phiVar H p r + ε := by
    have hlt := hsub.eventually
      (eventually_lt_nhds (show phiVar H p r < phiVar H p r + ε by linarith))
    filter_upwards [hlt] with k hk; exact hk.le
  exact Ip_cut_lowerSemicontinuous hp0 hp1 hcut hev

end UpperTailMultipodality
