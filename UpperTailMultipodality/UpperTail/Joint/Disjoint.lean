import UpperTailMultipodality.UpperTail.Joint.Cone

/-!
# The cone of first-order changes avoids the improving directions

This is the first half of the proof of `lem:upper-tail-multiplier`.  Suppose a vector of the cone
`insertionCone` of `lem:upper-tail-multiplier` decreases `I_p` and increases every active
density to first
order.  Realizing it by the insertion of `lem:insertion-first-order` — a block of measure `θc`
with rows given by the row kernel `U`, together with the perturbation `θZ` of the old values —
produces feasible graphons with strictly smaller `I_p`, contradicting the minimality of `W`.

The `c = 0` case, where nothing is inserted, is reduced to the case `c > 0` by making the
inserted block small: the two conditions are strict, so they survive a small perturbation of
`c`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Set Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The case `c > 0` of `insertionCone_disjoint`. -/
private theorem not_improving_of_pos {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {τ : ι → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {W : Graphon} (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p)
    {η : ℝ} (hη : 0 < η) (hηW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc η (1 - η))
    {A : Finset ι} (hA : ∀ j ∈ A, W.tDensity (Hs j) = τ j)
    (hnA : ∀ j ∉ A, τ j < W.tDensity (Hs j)) {c : ℝ} (hc : 0 < c) {U : ℝ → ℝ → ℝ}
    (hU : IsRows U) {Z : Kernel} (hZ : AdmissibleDir W η Z)
    (h1 : c * insertionEntropy p W U + variationIp p W Z < 0)
    (h2 : ∀ j ∈ A, 0 < c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z) :
    False := by
  classical
  have hq : p ∈ Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  have hZ' : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η := hZ
  have hcne : c ≠ 0 := hc.ne'
  -- the reparametrization `g(s) = s/c`, so that the block of measure `s` carries the weight `c`
  set g : ℝ → ℝ := fun s => c⁻¹ * s with hgdef
  have hg : HasDerivAt g c⁻¹ 0 := by
    have h := (hasDerivAt_id' (0:ℝ)).const_mul c⁻¹
    rw [hgdef]
    simpa using h
  have hg0 : g 0 = 0 := by rw [hgdef]; exact mul_zero _
  -- the first-order behaviour of the densities
  have hQ : ∀ j, HasDerivAt (insertionPolyRows (Hs j) p U W Z g)
      (c⁻¹ * (c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z)) 0 := by
    intro j
    have h := hasDerivAt_insertionPolyRows (Hs j) W Z hη hZ' hq hU hg hg0
    rw [sum_blockDensityRows_singleton (Hs j) p hU W] at h
    refine h.congr_deriv ?_
    unfold insertionDensity variationDensity
    field_simp
    ring
  have hQ0 : ∀ j, insertionPolyRows (Hs j) p U W Z g 0 = W.tDensity (Hs j) := fun j =>
    insertionPolyRows_zero (Hs j) p U W Z hg0
  have hev : ∀ j, ∀ᶠ s in 𝓝[>] (0:ℝ), τ j < insertionPolyRows (Hs j) p U W Z g s := by
    intro j
    by_cases hj : j ∈ A
    · have hpos : 0 < c⁻¹ * (c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z) :=
        mul_pos (inv_pos.mpr hc) (h2 j hj)
      have h := eventually_lt_of_hasDerivAt_pos (hQ j) hpos
      filter_upwards [h] with s hs
      rw [hQ0 j, hA j hj] at hs
      exact hs
    · have hgt : τ j < insertionPolyRows (Hs j) p U W Z g 0 := by
        rw [hQ0 j]; exact hnA j hj
      have hcont := (hQ j).continuousAt
      have h : ∀ᶠ s in 𝓝 (0:ℝ), τ j < insertionPolyRows (Hs j) p U W Z g s :=
        hcont (Ioi_mem_nhds hgt)
      exact h.filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ j, τ j < insertionPolyRows (Hs j) p U W Z g s :=
    Filter.eventually_all.mpr hev
  -- the first-order behaviour of the entropy
  have hFd : HasDerivAt (fun s : ℝ => s ^ 2 * Jp p p
        + 2 * s * (1 - s) * (∫ z, Jp p (U z.1 z.2) ∂gμ)
        + (1 - s) ^ 2 * (Kernel.ofGraphon W + g s • Z).Ip p)
      (c⁻¹ * (c * insertionEntropy p W U + variationIp p W Z)) 0 := by
    have h := hasDerivAt_insertion_Ip W Z hp0 hp1 hη (by linarith : (1:ℝ) - η < 1) hηW hg hg0
      (∫ z, Jp p (U z.1 z.2) ∂gμ) (Jp p p)
    refine h.congr_deriv ?_
    rw [integral_gμ_Jp_rows hp0 hp1 hU]
    unfold insertionEntropy variationIp
    field_simp
  have hFneg := hFd.neg
  have hdecpos : 0 < -(c⁻¹ * (c * insertionEntropy p W U + variationIp p W Z)) := by
    have := mul_pos (inv_pos.mpr hc) (neg_pos.mpr h1)
    rw [mul_neg] at this
    exact this
  have hF0 : ((0:ℝ) ^ 2 * Jp p p + 2 * 0 * (1 - 0) * (∫ z, Jp p (U z.1 z.2) ∂gμ)
      + (1 - 0) ^ 2 * (Kernel.ofGraphon W + g 0 • Z).Ip p) = W.Ip p := by
    rw [hg0, ofGraphon_add_zero_smul]
    have hW0 : (Kernel.ofGraphon W).Ip p = W.Ip p := rfl
    rw [hW0]
    ring
  have hdec : ∀ᶠ s in 𝓝[>] (0:ℝ), (s ^ 2 * Jp p p
      + 2 * s * (1 - s) * (∫ z, Jp p (U z.1 z.2) ∂gμ)
      + (1 - s) ^ 2 * (Kernel.ofGraphon W + g s • Z).Ip p) < W.Ip p := by
    have h := eventually_lt_of_hasDerivAt_pos hFneg hdecpos
    filter_upwards [h] with s hs
    have hs' : -((0:ℝ) ^ 2 * Jp p p + 2 * 0 * (1 - 0) * (∫ z, Jp p (U z.1 z.2) ∂gμ)
        + (1 - 0) ^ 2 * (Kernel.ofGraphon W + g 0 • Z).Ip p)
        < -(s ^ 2 * Jp p p + 2 * s * (1 - s) * (∫ z, Jp p (U z.1 z.2) ∂gμ)
          + (1 - s) ^ 2 * (Kernel.ofGraphon W + g s • Z).Ip p) := hs
    rw [hF0] at hs'
    linarith
  -- the insertion realizes all the densities at once
  have hex := eventually_exists_insertGraphonRows Hs W Z hη hZ' hq hU hg.continuousAt hg0
  obtain ⟨s, ⟨hsall, hsex⟩, hsdec⟩ := ((hall.and hex).and hdec).exists
  obtain ⟨W', hW't, hW'I⟩ := hsex
  have hfeasW' : JointFeasible Hs τ W' := by
    intro j
    rw [hW't j]
    exact (hsall j).le
  have hle := hmin W' hfeasW'
  rw [hW'I p hp0 hp1] at hle
  linarith

/-- **The cone `𝒞` avoids the improving directions.**  If `W` minimizes `I_p` among
the feasible graphons, no first-order change produced by an insertion decreases `I_p` while
increasing every active density. -/
theorem insertionCone_disjoint {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {τ : ι → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {W : Graphon} (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p)
    {η : ℝ} (hη : 0 < η) (hηW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc η (1 - η))
    {A : Finset ι} (hA : ∀ j ∈ A, W.tDensity (Hs j) = τ j)
    (hnA : ∀ j ∉ A, τ j < W.tDensity (Hs j)) :
    ∀ w ∈ insertionCone Hs p W η, ¬ (w.1 < 0 ∧ ∀ j ∈ A, 0 < w.2 j) := by
  classical
  rintro w ⟨c, U, Z, hc, hU, hZ, rfl⟩ ⟨hw1, hw2⟩
  have hw1' : c * insertionEntropy p W U + variationIp p W Z < 0 := hw1
  have hw2' : ∀ j ∈ A, 0 < c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z := hw2
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- nothing is inserted: shrink the block instead of removing it
    rw [← hc0] at hw1' hw2'
    have hev1 : ∀ᶠ ε in 𝓝 (0:ℝ),
        ε * insertionEntropy p W U + variationIp p W Z < 0 := by
      have hcont : ContinuousAt
          (fun ε : ℝ => ε * insertionEntropy p W U + variationIp p W Z) 0 := by fun_prop
      exact hcont (Iio_mem_nhds hw1')
    have hev2 : ∀ j ∈ A, ∀ᶠ ε in 𝓝 (0:ℝ),
        0 < ε * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z := by
      intro j hj
      have hcont : ContinuousAt
          (fun ε : ℝ => ε * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z) 0 := by
        fun_prop
      exact hcont (Ioi_mem_nhds (hw2' j hj))
    have hallA : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ j ∈ A,
        0 < ε * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z :=
      (eventually_all_finset A).mpr hev2
    obtain ⟨ε, ⟨hε1, hε2⟩, hεpos⟩ :=
      (((hev1.and hallA).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0))).exists
    exact not_improving_of_pos Hs hp0 hp1 hmin hη hηW hA hnA hεpos hU hZ hε1 hε2
  · exact not_improving_of_pos Hs hp0 hp1 hmin hη hηW hA hnA hcpos hU hZ hw1' hw2'

end UpperTailMultipodality
