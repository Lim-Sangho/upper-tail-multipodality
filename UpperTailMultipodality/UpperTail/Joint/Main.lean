import UpperTailMultipodality.RowCriterion.Main
import UpperTailMultipodality.UpperTail.Joint.Multiplier
import UpperTailMultipodality.UpperTail.Support.Matching

/-!
# The joint upper-tail problem (`thm:joint-upper-tail`)

For `p ∈ (0,1)` and densities `τ_j < 1`, the minimizers of `eq:joint-variational-problem` are the
feasible graphons attaining `jointVar`.  This file proves `thm:joint-upper-tail`: each of them is
multipodal with ordered blocks.

The proof follows `sec:row-criterion`.  If the constant graphon `p` is feasible it is the unique
minimizer, so `W ≡ p` has one block.  Otherwise some constraint is active, `W` takes values in a
compact subinterval of `(0,1)` (`joint_ae_ge`, `joint_exists_ae_le_one_sub`), and
`joint_multiplier` produces weights `μ_j ≥ 0`, not all zero, for which almost every row of `W`
minimizes the row functional `eq:row-functional` with `q = p` and `α = 0`.  If some `H_j` with
`μ_j > 0` has a vertex of degree at least two, `row_criterion_family` applies.  Otherwise every such `H_j` has maximum degree at most one, so
its derivative kernel is constant (`derivKernel_const_of_degree_le_one`); then
`eq:separated-el` makes `J_p'(W)` constant, and `W` is again constant because `J_p'` is
injective on `(0,1)`.
-/

namespace UpperTailMultipodality

open MeasureTheory UpperTailSupport Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`thm:joint-upper-tail`.**  Let each `H_j` have at least one edge, let `0 < p < 1` and
`τ_j < 1`.  Every minimizer of `eq:joint-variational-problem` is multipodal with ordered
blocks. -/
theorem joint_upper_tail {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (hm : ∀ j, 1 ≤ (Hs j).edgeFinset.card) {p : ℝ} {τ : ι → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hτ1 : ∀ j, τ j < 1) {W : Graphon}
    (hfeas : JointFeasible Hs τ W) (hmin : W.Ip p = jointVar Hs p τ) :
    IsOrderedMultipodal W := by
  classical
  have hpI : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp0.le, hp1.le⟩
  have hle := Ip_le_of_jointVar hp0 hp1 hmin
  by_cases hnf : ∀ j, τ j ≤ p ^ (Hs j).edgeFinset.card
  · -- the constant graphon `p` is feasible, so `I_p(W) = 0` and `W ≡ p`
    have hcfeas : JointFeasible Hs τ (constGraphon p hpI) := by
      intro j
      rw [tDensity_constGraphon hpI (Hs j)]
      exact hnf j
    have hcIp : (constGraphon p hpI).Ip p = 0 := by
      unfold Graphon.Ip
      simp only [constGraphon_apply]
      rw [integral_const, Jp_self hp0 hp1]
      simp
    have h0 : W.Ip p = 0 :=
      le_antisymm (by rw [← hcIp]; exact hle _ hcfeas) (Ip_nonneg W hp0 hp1)
    exact isOrderedMultipodal_of_ae_const hpI (ae_eq_of_Ip_eq_zero hp0 hp1 h0)
  · -- some constraint is active, and `W` avoids `0` and `1`
    obtain ⟨j₁, hact⟩ := joint_exists_active hp0 hp1 hfeas hle hnf
    have hlow := joint_ae_ge hp0 hp1 hfeas hle
    have ht1 : W.tDensity (Hs j₁) < 1 := by rw [hact]; exact hτ1 j₁
    obtain ⟨γ, hγ, hup⟩ := joint_exists_ae_le_one_sub hm hp0 hp1 hfeas hle hlow ht1
    obtain ⟨μ, hμ0, -, hEL, hrow⟩ :=
      joint_multiplier Hs hm hp0 hp1 hfeas hle hnf hlow hγ hup
    by_cases hΔ : ∃ j, 0 < μ j ∧ ∃ v, 2 ≤ (Hs j).degree v
    · -- some `H_j` with `μ_j > 0` is not a matching: the row criterion applies
      obtain ⟨j₂, hμj₂, hdeg⟩ := hΔ
      refine (row_criterion_family Hs (j₀ := j₂) W hp0 hp1 hμ0 hμj₂ hdeg hp0 hlow hrow).2.2 ?_
      filter_upwards [ae_combinedRowFunctional_row_eq Hs W hp0 hp1 hrow (by ring)] with x hx
      exact ⟨isRow_row W x, hx⟩
    · -- every `H_j` with `μ_j > 0` is a matching, so `J_p'(W)` is constant
      have hmatch : ∀ j, 0 < μ j → ∀ v, (Hs j).degree v ≤ 1 := by
        intro j hj v
        by_contra hv
        exact hΔ ⟨j, hj, v, by omega⟩
      obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ∑ j, μ j * derivKernel (Hs j) W 0 0 := ⟨_, rfl⟩
      have hconst : ∀ x y : ℝ, ∑ j, μ j * derivKernel (Hs j) W x y = c := by
        intro x y
        rw [hcdef]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases (hμ0 j).lt_or_eq with hj | hj
        · rw [derivKernel_const_of_degree_le_one (Hs j) (hmatch j hj) W x y 0 0]
        · rw [← hj, zero_mul, zero_mul]
      have hWio : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Ioo (0:ℝ) 1 := by
        filter_upwards [hlow, hup] with z h1 h2
        exact ⟨lt_of_lt_of_le hp0 h1, by linarith⟩
      obtain ⟨z₀, hz₀EL, hz₀in⟩ := (hEL.and hWio).exists
      refine isOrderedMultipodal_of_ae_const ⟨hz₀in.1.le, hz₀in.2.le⟩ ?_
      filter_upwards [hEL, hWio] with z h1 h2
      refine (Jp'_strictMonoOn hp0 hp1).injOn h2 hz₀in ?_
      rw [h1, hz₀EL, hconst z.1 z.2, hconst z₀.1 z₀.2]

end UpperTailMultipodality
