import UpperTailMultipodality.RowCriterion.Finiteness.MeanParam

/-!
# Compactness of the set of row minimizers (`lem:row-compact`)

`𝓜_W` is compact in the sup norm.  The paper proves this by writing each term `G_{v,z₀}(u)` of
`eq:rooted-gradient-kernel` as `T_K(u^{⊗k})` for a Hilbert–Schmidt operator `T_K` on
`L²([0,1]^k)`, so that the weighted gradients of rows form a relatively compact family in
`L²([0,1])`; a subsequence of gradients converges, the fixed-point form of `eq:row-euler`
transfers the convergence to the rows, and `eq:gradient-lipschitz` bootstraps it from `L¹` to
`L^∞`.

Here the same conclusion comes from the mean parametrization of `Finiteness/MeanParam.lean`.
By `prop:row-ordering` the mean is injective on `𝓜_W`, the set `A` of means is a closed subset of
`[0,1]`, hence compact, and the canonical representatives are Lipschitz in the mean — which is
where `eq:gradient-lipschitz` enters, exactly as in the paper's last step.  So `𝓜_W` is the
image of a compact subset of `ℝ` under a continuous map, hence compact.  This avoids the
Hilbert–Schmidt operator between the spaces `L²([0,1]^k)` and `L²([0,1])`; the Hilbert–Schmidt
compactness that the project does prove, `isCompactOperator_kernelOp`, is on `L²([0,1])` and is
used for `lem:bordered`.

The argument does not use `lem:row-finite`, so `lem:row-compact` stays available at the place the
paper uses it, before finiteness.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:row-compact`.**  `𝓜_W` is compact in the sup norm: there is a compact set `K` of
bounded measurable functions, each of which is itself an element of `𝓜_W`, such that every
element of `𝓜_W` agrees almost everywhere with a member of `K`. -/
theorem row_compact {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    ∃ K : Set BddMeas, IsCompact K ∧
      (∀ w ∈ K, ⇑w ∈ combinedRowMinimizers Hs W q α μ c) ∧
      ∀ u ∈ combinedRowMinimizers Hs W q α μ c, ∃ w ∈ K, u =ᵐ[unitμ] ⇑w := by
  obtain ⟨P⟩ := exists_meanParam (Hs := Hs) (W := W) (q := q) (α := α) (μ := μ) (j₀ := j₀)
    hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  refine ⟨P.rep '' P.A, P.A_isCompact.image_of_continuousOn P.rep_continuousOn, ?_, ?_⟩
  · rintro w ⟨a, ha, rfl⟩
    exact P.rep_mem_rowMinimizers a ha
  · intro u hu
    exact ⟨P.rep (∫ y, u y ∂unitμ), ⟨∫ y, u y ∂unitμ, (P.mem_iff _).mpr ⟨u, hu, rfl⟩, rfl⟩,
      P.rep_ae u hu⟩

/-- **The sequential form of `lem:row-compact`**, which is how the paper states and uses it:
every sequence in `𝓜_W` has a subsequence whose canonical representatives converge in the sup
norm to an element of `𝓜_W`. -/
theorem row_compact_seq {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u)
    (u : ℕ → ℝ → ℝ) (hu : ∀ i, u i ∈ combinedRowMinimizers Hs W q α μ c) :
    ∃ (w : ℕ → BddMeas) (wlim : BddMeas) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, u i =ᵐ[unitμ] ⇑(w i)) ∧
      ⇑wlim ∈ combinedRowMinimizers Hs W q α μ c ∧
      Tendsto (w ∘ φ) atTop (nhds wlim) := by
  obtain ⟨P⟩ := exists_meanParam (Hs := Hs) (W := W) (q := q) (α := α) (μ := μ) (j₀ := j₀)
    hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  set K : Set BddMeas := P.rep '' P.A with hK
  have hKcompact : IsCompact K := P.A_isCompact.image_of_continuousOn P.rep_continuousOn
  set w : ℕ → BddMeas := fun i => P.rep (∫ y, u i y ∂unitμ) with hw
  have hwmem : ∀ i, w i ∈ K := fun i =>
    ⟨∫ y, u i y ∂unitμ, (P.mem_iff _).mpr ⟨u i, hu i, rfl⟩, rfl⟩
  obtain ⟨wlim, hwlim, φ, hφ, htend⟩ := hKcompact.tendsto_subseq hwmem
  obtain ⟨a, ha, hrep⟩ := hwlim
  refine ⟨w, wlim, φ, hφ, fun i => P.rep_ae (u i) (hu i), ?_, htend⟩
  rw [← hrep]
  exact P.rep_mem_rowMinimizers a ha

end UpperTailMultipodality
