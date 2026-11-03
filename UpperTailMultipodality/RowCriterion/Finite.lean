import UpperTailMultipodality.RowCriterion.Basic
import UpperTailMultipodality.RowCriterion.Finiteness.MeanParam

/-!
# Finiteness of the set of row minimizers (`lem:row-finite`)

The set `𝓜_W` is finite up to null sets.  The mean parametrization `MeanParam`
(`Finiteness/MeanParam.lean`) supplies the set `A` of means as a closed bounded subset of `ℝ` in
bijection with `𝓜_W`, together with the canonical representatives
`σ(ℓ(q) + α + (1/2)∇𝒫_W(u))`, which are Lipschitz in the mean; the same data gives
`lem:row-compact` in `Finiteness/Compact.lean`.  Around an
accumulation point of `A` the analytic implicit function theorem produces an analytic branch of
solutions of `eq:row-euler` whose multiplier vanishes identically (identity theorem) and along
which `ℱ_W` is constant, so a whole interval of means lies in `A`
(`Finiteness/Branch.lean`).  A bounded closed subset of `ℝ` all of whose accumulation points are
interior is finite, and the finiteness of `𝓜_W` follows.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:row-finite`.**  `𝓜_W` is finite up to null sets: there are finitely many rows such
that every element of `𝓜_W` agrees almost everywhere with one of them. -/
theorem row_finite {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    ∃ g : Finset (ℝ → ℝ), ∀ u ∈ combinedRowMinimizers Hs W q α μ c,
      ∃ g' ∈ g, u =ᵐ[unitμ] g' := by
  classical
  have hω1 : ω ≤ 1 := le_one_of_ae_le hWω
  -- the mean parametrization: `A` closed in `[0,1]`, representatives Lipschitz in the mean
  obtain ⟨P⟩ := exists_meanParam (Hs := Hs) (W := W) (q := q) (α := α) (μ := μ) (j₀ := j₀)
    hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  have hlowE : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) → c ≤ rowFunctionalE Hs W q α μ v :=
    fun v hv => hlow _ ⟨v.measurable, hv⟩
  -- accumulation points of `A` are interior, by the analytic branch argument
  have hnbhd : ∀ a ∈ P.A, AccPt a (𝓟 P.A) → ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ P.A := by
    intro a₀ ha₀ hacc
    obtain ⟨ε, hε, hbranch⟩ := exists_interval_of_accPt (Hs := Hs) (W := W) (α := α) hμ hμ₀ hΔ
      hq0 hq1 hω hω1 hWω hlowE P.lo_pos P.hi_lt_one P.lo_le_one P.rep_mem P.rep_val P.rep_fix
      P.rep_mean P.L_nonneg P.rep_lipschitz ha₀ hacc
    refine ⟨ε, hε, fun a ha => ?_⟩
    obtain ⟨v, hvmem, hvval, hvmean⟩ := hbranch a ha
    exact (P.mem_iff a).mpr ⟨⇑v, ⟨⟨v.measurable, hvmem⟩, hvval⟩, hvmean⟩
  have hAfin : P.A.Finite := finite_of_accPt_interior P.A_subset P.A_closed hnbhd
  -- the finite set of canonical representatives
  refine ⟨hAfin.toFinset.image (fun a => ⇑(P.rep a)), fun u hu => ?_⟩
  refine ⟨⇑(P.rep (∫ y, u y ∂unitμ)), ?_, P.rep_ae u hu⟩
  exact Finset.mem_image.mpr ⟨∫ y, u y ∂unitμ,
    (Set.Finite.mem_toFinset hAfin).mpr ((P.mem_iff _).mpr ⟨u, hu, rfl⟩), rfl⟩

end UpperTailMultipodality
