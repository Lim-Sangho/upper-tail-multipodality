import UpperTailMultipodality.RowCriterion.Main
import UpperTailMultipodality.Preliminaries.Perturbation

/-!
# Fixed edge and subgraph densities: definitions (`sec:fixed-densities`)

* `tauMax H ε` — `τ_max(ε) = max { t(H,W) : e(W) = ε }`;
* `IsEntropyMaximizer H ε τ W` — `W` maximizes `s` subject to `e(W) = ε` and `t(H,W) = τ`,
  `eq:entropy-maximization`;
* `fixedValue H ε τ` — `Ψ_ε(τ) = min { I_ε(W) : e(W) = ε, t(H,W) = τ }`, `eq:fixed-problem`;
* `ConstraintQualification H W` — `def:constraint-qualification`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `τ_max(ε) = sup { t(H,W) : e(W) = ε }`; the supremum is attained. -/
noncomputable def tauMax (H : SimpleGraph V) [DecidableRel H.Adj] (ε : ℝ) : ℝ :=
  sSup {τ | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ}

/-- **`eq:entropy-maximization`.**  `W` maximizes the entropy among graphons with `e(W) = ε`
and `t(H,W) = τ`. -/
def IsEntropyMaximizer (H : SimpleGraph V) [DecidableRel H.Adj] (ε τ : ℝ) (W : Graphon) : Prop :=
  W.edgeDensity = ε ∧ W.tDensity H = τ ∧
    ∀ W' : Graphon, W'.edgeDensity = ε → W'.tDensity H = τ → W'.entropy ≤ W.entropy

/-- **`eq:fixed-problem`.**  `Ψ_ε(τ) = inf { I_ε(W) : e(W) = ε, t(H,W) = τ }`. -/
noncomputable def fixedValue (H : SimpleGraph V) [DecidableRel H.Adj] (ε τ : ℝ) : ℝ :=
  sInf {y | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.Ip ε = y}

/-- `W` attains `Ψ_ε(τ)`: a minimizer of `eq:fixed-problem`. -/
def IsFixedMinimizer (H : SimpleGraph V) [DecidableRel H.Adj] (ε τ : ℝ) (W : Graphon) : Prop :=
  W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.Ip ε = fixedValue H ε τ

/-- By `eq:entropy-identity`, the maximizers of `eq:entropy-maximization` are exactly the
minimizers of `eq:fixed-problem`. -/
theorem isEntropyMaximizer_iff (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (W : Graphon) :
    IsEntropyMaximizer H ε τ W ↔ IsFixedMinimizer H ε τ W := by
  have hbdd : BddBelow {y | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ ∧ W.Ip ε = y} :=
    ⟨0, by rintro y ⟨W', -, -, rfl⟩; exact Ip_nonneg W' hε0 hε1⟩
  constructor
  · rintro ⟨he, ht, hmax⟩
    refine ⟨he, ht, le_antisymm ?_ (csInf_le hbdd ⟨W, he, ht, rfl⟩)⟩
    refine le_csInf ⟨_, W, he, ht, rfl⟩ ?_
    rintro y ⟨W', he', ht', rfl⟩
    rw [entropy_identity W hε0 hε1 he, entropy_identity W' hε0 hε1 he']
    linarith [hmax W' he' ht']
  · rintro ⟨he, ht, hmin⟩
    refine ⟨he, ht, fun W' he' ht' => ?_⟩
    have h1 : W.Ip ε ≤ W'.Ip ε := hmin ▸ csInf_le hbdd ⟨W', he', ht', rfl⟩
    rw [entropy_identity W hε0 hε1 he, entropy_identity W' hε0 hε1 he'] at h1
    linarith

/-- The determinant of the matrix `Γ_W(U₁,U₂)` of `def:constraint-qualification`. -/
noncomputable def cqDet (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (U₁ U₂ : Kernel) :
    ℝ :=
  (∫ z, U₁.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)
    - (∫ z, U₂.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ)

/-- `U` is supported in `Ω_η(W) = {η < W < 1 - η}`. -/
def SupportedIn (W : Graphon) (η : ℝ) (U : Kernel) : Prop :=
  ∀ x y, U.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η

/-- **`def:constraint-qualification`.**  There are `η > 0` and bounded symmetric kernels
`U₁, U₂` supported in `Ω_η(W)` for which the matrix `Γ_W(U₁,U₂)` of
`def:constraint-qualification` is invertible. -/
def ConstraintQualification (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ U₁ U₂ : Kernel, SupportedIn W η U₁ ∧ SupportedIn W η U₂ ∧
    cqDet H W U₁ U₂ ≠ 0

end UpperTailMultipodality
