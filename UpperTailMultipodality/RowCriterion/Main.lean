import UpperTailMultipodality.RowCriterion.Finite
import UpperTailMultipodality.RowCriterion.Rows.Blocks

/-!
# A criterion for finitely many row types (`thm:row-criterion`)

Fix graphs `H_1, …, H_s`, weights `μ_j ≥ 0` with `μ_{j₀} > 0` and `Δ(H_{j₀}) ≥ 2` for some
`j₀`, a graphon `W` with `W ≥ ω > 0` almost everywhere (as in `lem:upper-tail-basic`), and
`q ∈ (0,1)`, `α ∈ ℝ`.  If the row functional `ℱ_W` of `eq:row-functional`, built from the
combined term `𝒫_W` of `eq:row-functional`, satisfies `ℱ_W ≥ c_W` on all rows, then the set
`𝓜_W` of rows attaining `c_W` is finite and totally ordered up to null sets.  If almost every
row of `W` lies in `𝓜_W`, then `W` is multipodal with ordered blocks.  Both hypotheses on `ℱ_W`
come from `lem:global-row-minimality`.

`row_criterion` is the case of a single term, which is what `thm:joint-upper-tail` with `s = 1`
and `prop:nondegenerate-multipodality` use.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:row-criterion`.**  Given `W ≥ ω > 0`, an index `j₀` with `μ_{j₀} > 0` and
`Δ(H_{j₀}) ≥ 2`, and the lower bound `ℱ_W ≥ c_W` of `lem:global-row-minimality`, the set `𝓜_W`
is finite up to null sets and totally ordered; if almost every row of `W` lies in `𝓜_W`, then
`W` is multipodal with ordered blocks. -/
theorem row_criterion_family {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι} (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    (∃ g : Finset (ℝ → ℝ), ∀ u ∈ combinedRowMinimizers Hs W q α μ c,
        ∃ g' ∈ g, u =ᵐ[unitμ] g') ∧
      (∀ u₁ ∈ combinedRowMinimizers Hs W q α μ c, ∀ u₂ ∈ combinedRowMinimizers Hs W q α μ c,
        u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁) ∧
      ((∀ᵐ x ∂unitμ, W.row x ∈ combinedRowMinimizers Hs W q α μ c) →
        IsOrderedMultipodal W) := by
  have hfin := row_finite Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  have hchain : ∀ u₁ ∈ combinedRowMinimizers Hs W q α μ c,
      ∀ u₂ ∈ combinedRowMinimizers Hs W q α μ c, u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁ :=
    fun u₁ hu₁ u₂ hu₂ =>
      row_chain Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow hu₁ hu₂
  exact ⟨hfin, hchain, fun hrows =>
    Rows.isOrderedMultipodal_of_rows W (fun u hu => hu.1) hfin hchain hrows⟩

/-- **`thm:row-criterion` with a single rooted-density term.**  Given `W ≥ ω > 0`, `Δ(H) ≥ 2`
and the lower bound `ℱ_W ≥ c_W` of `lem:global-row-minimality`, the set `𝓜_W` is finite up to
null sets and totally ordered; if almost every row of `W` lies in `𝓜_W`, then `W` is multipodal
with ordered blocks. -/
theorem row_criterion (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) (W : Graphon) {q α μ ω c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hμ : 0 < μ) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ rowFunctional H W q α μ u) :
    (∃ g : Finset (ℝ → ℝ), ∀ u ∈ rowMinimizers H W q α μ c, ∃ g' ∈ g, u =ᵐ[unitμ] g') ∧
      (∀ u₁ ∈ rowMinimizers H W q α μ c, ∀ u₂ ∈ rowMinimizers H W q α μ c,
        u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁) ∧
      ((∀ᵐ x ∂unitμ, W.row x ∈ rowMinimizers H W q α μ c) → IsOrderedMultipodal W) := by
  have h := row_criterion_family (fun _ : Fin 1 => H) (j₀ := 0) W hq0 hq1
    (fun _ => hμ.le) hμ hΔ hω hWω (by simpa using hlow)
  simpa using h

end UpperTailMultipodality
