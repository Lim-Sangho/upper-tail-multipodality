import UpperTailMultipodality.Preliminaries.Graphons.Variational

/-!
# Cut norm and cut distance

* `cutNorm`, `cutDist` — the cut norm and the cut distance `δ_□` of `sec:graphons`.

The file declares no axiom.  The graph-limit facts assumed by the formalization are in
`Preliminaries/Graphons/CutContinuity.lean`; attainment of the infimum is the theorem
`feasible_attains` in `Preliminaries/Graphons/Attainment.lean`.  The Chatterjee–Varadhan large
deviation principle is outside the formalization.
-/

namespace UpperTailMultipodality

open MeasureTheory Real
open scoped Classical

/-- The cut norm `‖U‖_□ = sup_{S,T} |∫_{S×T} U|` of an integrable kernel on
`[0,1]²`. -/
noncomputable def cutNorm (U : ℝ → ℝ → ℝ) : ℝ :=
  sSup {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
    v = |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ|}

/-- The cut distance `δ_□(W,W') = inf_σ ‖W - (W')^σ‖_□`, the infimum over
relabellings `σ` of `[0,1]`. -/
noncomputable def cutDist (W W' : Graphon) : ℝ :=
  sInf {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
    v = cutNorm (fun x y => W.toFun x y - W'.toFun (σ x) (σ y))}

/-! ### The Chatterjee–Varadhan large deviation principle

The large deviation principle of Chatterjee and Varadhan is not formalized, and no result of the
formalization uses it.  Stating it requires a formal model of `G(n,p)` and of its empirical
graphon, whereas every result formalized here is a statement about deterministic graphon
variational problems. -/

end UpperTailMultipodality
