import UpperTailMultipodality.Preliminaries.Graphons.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The Shannon entropy `H`

`Preliminaries/Graphons/Basic.lean` carries the *entropy integrand*
`entIntegrand t = t log t + (1-t) log(1-t)`, because `Graphon.entropy` is defined as
`-½∫ entIntegrand ∘ W`.  This file provides the entropy itself,

`H(t) = -t log t - (1-t) log(1-t) = -entIntegrand t`,

its expanded form, its identification with Mathlib's `Real.binEntropy`, and the sign relation to
`entIntegrand`.
-/

namespace UpperTailMultipodality

open Real

/-- The Shannon entropy `H(s) = -s log s - (1-s) log(1-s)`; equals `-entIntegrand s`. -/
noncomputable def shannonH (s : ℝ) : ℝ := -entIntegrand s

/-- `H` written out. -/
theorem shannonH_eq (s : ℝ) :
    shannonH s = -(s * Real.log s) - (1 - s) * Real.log (1 - s) := by
  unfold shannonH entIntegrand; ring

/-- `entIntegrand t = -H(t)` (the entropy integrand is minus the Shannon entropy). -/
theorem entIntegrand_eq_neg_shannonH (t : ℝ) : entIntegrand t = -shannonH t := by
  unfold shannonH; ring

/-- `shannonH` coincides with Mathlib's binary entropy `Real.binEntropy`. -/
theorem shannonH_eq_binEntropy (s : ℝ) : shannonH s = Real.binEntropy s := by
  rw [shannonH_eq, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog; ring

end UpperTailMultipodality
