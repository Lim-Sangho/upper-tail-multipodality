import UpperTailMultipodality.Preliminaries.Kernel

/-!
# The entropy identity (`eq:entropy-identity`)

With `S_0(z) = -½(z log z + (1-z) log(1-z))`, every graphon with `e(W) = ε` satisfies
`I_ε(W) = 2S_0(ε) - 2s(W)`.  Hence, among graphons with a fixed edge density, minimizing
`I_ε` is equivalent to maximizing the entropy `s`.
-/

namespace UpperTailMultipodality

open MeasureTheory Real

/-- The entropy density `S_0(z) = -½(z log z + (1-z) log(1-z))`. -/
noncomputable def S0 (z : ℝ) : ℝ := -(1 / 2) * entIntegrand z

/-- **`eq:entropy-identity`.**  If `e(W) = ε ∈ (0,1)`, then `I_ε(W) = 2S_0(ε) - 2s(W)`. -/
theorem entropy_identity (W : Graphon) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (he : W.edgeDensity = ε) :
    W.Ip ε = 2 * S0 ε - 2 * W.entropy := by
  rw [W.Ip_eq_entropy hε0 hε1, he, S0, entIntegrand,
    Real.log_div (ne_of_gt (by linarith : (0:ℝ) < 1 - ε)) (ne_of_gt hε0)]
  ring

end UpperTailMultipodality
