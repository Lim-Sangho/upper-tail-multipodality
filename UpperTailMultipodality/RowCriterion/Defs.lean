import UpperTailMultipodality.Preliminaries.RootedDensity

/-!
# The row functional (`sec:row-criterion`)

For `q ∈ (0,1)`, `α ∈ ℝ` and `μ > 0`, the row functional, `eq:row-functional`, is

`ℱ_W(u) = 2∫₀¹ J_q(u(y)) dy - 2α ∫₀¹ u(y) dy - μ ℛ_W(u)`.

`rowMinimizers H W q α μ c` is the set `𝓜_W` of rows attaining the value `c`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The row functional `ℱ_W`, `eq:row-functional`.** -/
noncomputable def rowFunctional (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (q α μ : ℝ) (u : ℝ → ℝ) : ℝ :=
  2 * ∫ y, Jp q (u y) ∂unitμ - 2 * α * ∫ y, u y ∂unitμ - μ * totalRootedDensity H W u

/-- **The set `𝓜_W` of rows at which `ℱ_W` takes the value `c`.** -/
def rowMinimizers (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (q α μ c : ℝ) :
    Set (ℝ → ℝ) :=
  {u | IsRow u ∧ rowFunctional H W q α μ u = c}

end UpperTailMultipodality
