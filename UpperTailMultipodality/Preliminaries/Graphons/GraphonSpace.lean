import UpperTailMultipodality.Preliminaries.Graphons.CutPseudometric

/-!
# Homomorphism densities and relative entropy on the graphon space

`sec:graphons` works in the quotient `W̃₀` of graphons by weak isomorphism, a compact metric space
(`GraphonSpace`, `GraphonSpace.compactSpace`), and uses that every homomorphism density
`t(H,·)` is `δ_□`-continuous and that `I_p` is lower semicontinuous in the cut metric.  This file
states these two facts on `GraphonSpace`:

* `GraphonSpace.mk`, `GraphonSpace.dist_mk`, `GraphonSpace.mk_eq_mk` — the quotient map, whose
  metric is the cut distance and whose fibres are the weak-isomorphism classes;
* `GraphonSpace.tDensity`, `GraphonSpace.continuous_tDensity` — `t(H,·)` descends to `W̃₀` and is
  continuous;
* `GraphonSpace.Ip`, `GraphonSpace.lowerSemicontinuous_Ip` — for `0 < p < 1`, `I_p` descends to
  `W̃₀` and is lower semicontinuous.

Both follow from the sequential axioms `tDensity_cutContinuous` and `Ip_cut_lowerSemicontinuous`,
because `W̃₀` is a metric space.
-/

namespace UpperTailMultipodality

open Filter Topology

namespace GraphonSpace

/-- The class `[W] ∈ W̃₀` of a graphon. -/
noncomputable def mk (W : Graphon) : GraphonSpace :=
  @SeparationQuotient.mk Graphon cutPseudoMetricSpace.toUniformSpace.toTopologicalSpace W

theorem mk_surjective : Function.Surjective mk :=
  @SeparationQuotient.surjective_mk Graphon cutPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The metric of `W̃₀` is the cut distance. -/
theorem dist_mk (W W' : Graphon) : dist (mk W) (mk W') = cutDist W W' :=
  @SeparationQuotient.dist_mk Graphon cutPseudoMetricSpace W W'

/-- Two graphons have the same class exactly when they are weakly isomorphic. -/
theorem mk_eq_mk {W W' : Graphon} : mk W = mk W' ↔ cutDist W W' = 0 := by
  let := cutPseudoMetricSpace
  exact SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

/-- Cut convergence is convergence of the classes in `W̃₀`. -/
theorem cutTendsto_iff {W : ℕ → Graphon} {Wlim : Graphon} :
    CutTendsto W Wlim ↔ Tendsto (fun n => mk (W n)) atTop (𝓝 (mk Wlim)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_mk]
  rfl

private theorem cutTendsto_const {W W' : Graphon} (h : cutDist W W' = 0) :
    CutTendsto (fun _ => W) W' := by
  show Tendsto (fun _ => cutDist W W') atTop (𝓝 0)
  rw [h]
  exact tendsto_const_nhds

/-- Every sequence in `W̃₀` is the sequence of classes of some graphons. -/
private theorem exists_rep (x : ℕ → GraphonSpace) :
    ∃ W : ℕ → Graphon, x = fun n => mk (W n) := by
  choose W hW using fun n => mk_surjective (x n)
  exact ⟨W, funext fun n => (hW n).symm⟩

/-- Weakly isomorphic graphons have the same homomorphism densities. -/
theorem tDensity_eq_of_cutDist_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {W W' : Graphon} (h : cutDist W W' = 0) :
    W.tDensity H = W'.tDensity H :=
  tendsto_nhds_unique tendsto_const_nhds (tDensity_cutContinuous H (cutTendsto_const h))

/-- The homomorphism density `t(H,·)` on `W̃₀`. -/
noncomputable def tDensity {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : GraphonSpace → ℝ :=
  @SeparationQuotient.lift Graphon ℝ cutPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun W => W.tDensity H) fun _ _ h =>
      tDensity_eq_of_cutDist_eq_zero H
        ((@Metric.inseparable_iff Graphon cutPseudoMetricSpace _ _).mp h)

theorem tDensity_mk {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (W : Graphon) : tDensity H (mk W) = W.tDensity H :=
  rfl

/-- **`t(H,·)` is `δ_□`-continuous** on `W̃₀`. -/
theorem continuous_tDensity {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : Continuous (tDensity H) := by
  refine continuous_iff_seqContinuous.mpr fun x xlim hx => ?_
  obtain ⟨W, rfl⟩ := exists_rep x
  obtain ⟨Wlim, rfl⟩ := mk_surjective xlim
  exact tDensity_cutContinuous H (cutTendsto_iff.mpr hx)

/-- Weakly isomorphic graphons have the same relative entropy, for `0 < p < 1`. -/
theorem Ip_eq_of_cutDist_eq_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {W W' : Graphon}
    (h : cutDist W W' = 0) : W.Ip p = W'.Ip p :=
  le_antisymm
    (Ip_cut_lowerSemicontinuous hp0 hp1 (cutTendsto_const ((cutDist_comm W' W).trans h))
      (Eventually.of_forall fun _ => le_rfl))
    (Ip_cut_lowerSemicontinuous hp0 hp1 (cutTendsto_const h)
      (Eventually.of_forall fun _ => le_rfl))

/-- The relative entropy `I_p` on `W̃₀`, for `0 < p < 1`. -/
noncomputable def Ip {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : GraphonSpace → ℝ :=
  @SeparationQuotient.lift Graphon ℝ cutPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun W => W.Ip p) fun _ _ h =>
      Ip_eq_of_cutDist_eq_zero hp0 hp1
        ((@Metric.inseparable_iff Graphon cutPseudoMetricSpace _ _).mp h)

theorem Ip_mk {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W : Graphon) : Ip hp0 hp1 (mk W) = W.Ip p :=
  rfl

/-- **`I_p` is lower semicontinuous in the cut metric** on `W̃₀`, for `0 < p < 1`. -/
theorem lowerSemicontinuous_Ip {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    LowerSemicontinuous (Ip hp0 hp1) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun y => IsSeqClosed.isClosed ?_
  intro x xlim hx hlim
  obtain ⟨W, rfl⟩ := exists_rep x
  obtain ⟨Wlim, rfl⟩ := mk_surjective xlim
  exact Ip_cut_lowerSemicontinuous hp0 hp1 (cutTendsto_iff.mpr hlim) (Eventually.of_forall hx)

end GraphonSpace

end UpperTailMultipodality
