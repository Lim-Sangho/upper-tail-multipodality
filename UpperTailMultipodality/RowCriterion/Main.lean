import UpperTailMultipodality.RowCriterion.Finite
import UpperTailMultipodality.RowCriterion.Rows.Blocks

/-!
# A criterion for finitely many row types (`thm:row-criterion`)

Fix a graph `H` with `Δ(H) ≥ 2`, a graphon `W` with `W ≥ ω > 0` almost everywhere
(`eq:positive-base`), and `q ∈ (0,1)`, `α ∈ ℝ`, `μ > 0`.  If `ℱ_W ≥ c_W` on all rows
(`eq:row-lower-bound`), then the set `𝓜_W` of rows attaining `c_W` is finite and totally
ordered up to null sets.  If almost every row of `W` lies in `𝓜_W` (`eq:rows-attain`), then `W`
is multipodal with ordered blocks.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:row-criterion`.**  Under `eq:positive-base` and `eq:row-lower-bound`, the set `𝓜_W`
is finite up to null sets and totally ordered; if almost every row of `W` lies in `𝓜_W`, then
`W` is multipodal with ordered blocks. -/
theorem row_criterion (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) (W : Graphon) {q α μ ω c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hμ : 0 < μ) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ rowFunctional H W q α μ u) :
    (∃ g : Finset (ℝ → ℝ), ∀ u ∈ rowMinimizers H W q α μ c, ∃ g' ∈ g, u =ᵐ[unitμ] g') ∧
      (∀ u₁ ∈ rowMinimizers H W q α μ c, ∀ u₂ ∈ rowMinimizers H W q α μ c,
        u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁) ∧
      ((∀ᵐ x ∂unitμ, W.row x ∈ rowMinimizers H W q α μ c) → IsOrderedMultipodal W) := by
  have hfin := row_finite H hΔ W hq0 hq1 hμ hω hWω hlow
  have hchain : ∀ u₁ ∈ rowMinimizers H W q α μ c, ∀ u₂ ∈ rowMinimizers H W q α μ c,
      u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁ := fun u₁ hu₁ u₂ hu₂ =>
    row_chain H hΔ W hq0 hq1 hμ hω hWω hlow hu₁ hu₂
  exact ⟨hfin, hchain, fun hrows =>
    Rows.isOrderedMultipodal_of_rows W (fun u hu => hu.1) hfin hchain hrows⟩

end UpperTailMultipodality
