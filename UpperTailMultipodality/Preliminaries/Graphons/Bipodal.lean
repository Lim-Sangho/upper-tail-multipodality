import UpperTailMultipodality.Preliminaries.Graphons.Basic

/-!
# Bipodal graphons (`sec:graphons`)

A graphon is *bipodal* if there are a measurable set `A ⊆ [0,1]` and three values
`q₁₁, q₁₂, q₂₂ ∈ [0,1]` with `W = q₁₁` on `A×A`, `q₁₂` on `(A×Aᶜ) ∪ (Aᶜ×A)`, and `q₂₂` on
`Aᶜ×Aᶜ`, almost everywhere.

The definition uses an arbitrary measurable `A : Set ℝ`; only its intersection with `[0,1]`
affects equality under `gμ`. Positive block measures are not required, so constant graphons also
satisfy `IsBipodal`.
-/

namespace UpperTailMultipodality

open MeasureTheory
open scoped Classical

/-- The almost-everywhere two-block value associated with a set `A` and three
levels `q₁₁, q₁₂, q₂₂`. -/
noncomputable def bipodalValue (A : Set ℝ) (q11 q12 q22 : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ A then (if z.2 ∈ A then q11 else q12)
  else (if z.2 ∈ A then q12 else q22)

/-- A graphon agrees almost everywhere with a two-block kernel on a measurable partition.
Degenerate blocks and coincident edge probabilities are allowed. -/
def IsBipodal (W : Graphon) : Prop :=
  ∃ (A : Set ℝ) (q11 q12 q22 : ℝ),
    MeasurableSet A ∧
    q11 ∈ Set.Icc (0:ℝ) 1 ∧ q12 ∈ Set.Icc (0:ℝ) 1 ∧ q22 ∈ Set.Icc (0:ℝ) 1 ∧
    (∀ᵐ z ∂gμ, W.toFun z.1 z.2 = bipodalValue A q11 q12 q22 z)

/-- **Bipodality is invariant under measure-preserving relabelling.**  If `W'` is `W`
relabelled by a measure-preserving `σ` of `[0,1]` (i.e. `W'(x,y) = W(σx, σy)` a.e.) and `W` is
bipodal, then `W'` is bipodal (with vertex class `σ⁻¹` of `W`'s). -/
theorem isBipodal_of_relabel {W W' : Graphon} {σ : ℝ → ℝ}
    (hσ : IsRelabelling σ) (hW : IsBipodal W)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) : IsBipodal W' := by
  obtain ⟨A, q11, q12, q22, hA, hq11, hq12, hq22, hWae⟩ := hW
  refine ⟨σ ⁻¹' A, q11, q12, q22, hσ.measurable hA, hq11, hq12, hq22, ?_⟩
  have hmp : MeasurePreserving (Prod.map σ σ) gμ gμ :=
    hσ.measurePreserving.prod hσ.measurePreserving
  have hpull : (fun z : ℝ × ℝ => W.toFun (σ z.1) (σ z.2)) =ᵐ[gμ]
      fun z => bipodalValue A q11 q12 q22 (σ z.1, σ z.2) :=
    hmp.quasiMeasurePreserving.ae_eq hWae
  filter_upwards [h, hpull] with z hz hpz
  rw [hz, hpz]
  simp only [bipodalValue, Set.mem_preimage]

end UpperTailMultipodality
