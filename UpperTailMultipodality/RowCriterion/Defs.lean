import UpperTailMultipodality.Preliminaries.RootedDensity

/-!
# The row functional (`sec:row-criterion`)

For a finite family of graphs `H_j`, weights `μ_j ≥ 0`, `q ∈ (0,1)` and `α ∈ ℝ`, the combined
rooted density `𝒫_W` and the row functional of `eq:row-functional` are

`𝒫_W(u) = ∑_j μ_j ℛ_{H_j,W}(u)`,
`ℱ_W(u) = 2∫₀¹ J_q(u(y)) dy - 2α ∫₀¹ u(y) dy - 𝒫_W(u)`.

`combinedRowMinimizers Hs W q α μ c` is the set `𝓜_W` of rows at which `ℱ_W` takes the value
`c`.  The single-term versions `rowFunctional` and `rowMinimizers` are the case of one graph,
used by `thm:joint-upper-tail` with `s = 1` and by `prop:nondegenerate-multipodality`.

The file also records the family form of the bounds `eq:rooted-lipschitz`, that is
`eq:combined-lipschitz`, with `M_* = ∑_j μ_j m_j` (`combinedEdgeCard`).
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### A single graph -/

/-- **The row functional `ℱ_W`, `eq:row-functional`, with a single rooted-density term.** -/
noncomputable def rowFunctional (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (q α μ : ℝ) (u : ℝ → ℝ) : ℝ :=
  2 * ∫ y, Jp q (u y) ∂unitμ - 2 * α * ∫ y, u y ∂unitμ - μ * totalRootedDensity H W u

/-- **The set `𝓜_W` of rows at which `ℱ_W` takes the value `c`**, for a single graph. -/
def rowMinimizers (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (q α μ c : ℝ) :
    Set (ℝ → ℝ) :=
  {u | IsRow u ∧ rowFunctional H W q α μ u = c}

/-! ### A finite family of graphs -/

variable {ι : Type*} [Fintype ι]

/-- **The combined rooted density `𝒫_W = ∑_j μ_j ℛ_{j,W}` of `eq:row-functional`.** -/
noncomputable def combinedRooted (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) (μ : ι → ℝ) (u : ℝ → ℝ) : ℝ :=
  ∑ j, μ j * totalRootedDensity (Hs j) W u

/-- **The gradient `∇𝒫_W` of the combined rooted density.** -/
noncomputable def combinedRootedGradient (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (μ : ι → ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ j, μ j * rootedGradient (Hs j) W u y

/-- **The weighted number of edges `M_* = ∑_j μ_j m_j` of `eq:combined-lipschitz`.** -/
noncomputable def combinedEdgeCard (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (μ : ι → ℝ) : ℝ :=
  ∑ j, μ j * (Hs j).edgeFinset.card

/-- **The row functional `ℱ_W`, `eq:row-functional`.** -/
noncomputable def combinedRowFunctional (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (q α : ℝ) (μ : ι → ℝ) (u : ℝ → ℝ) : ℝ :=
  2 * ∫ y, Jp q (u y) ∂unitμ - 2 * α * ∫ y, u y ∂unitμ - combinedRooted Hs W μ u

/-- **The set `𝓜_W` of rows at which `ℱ_W` takes the value `c`.** -/
def combinedRowMinimizers (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) (q α : ℝ) (μ : ι → ℝ) (c : ℝ) : Set (ℝ → ℝ) :=
  {u | IsRow u ∧ combinedRowFunctional Hs W q α μ u = c}

omit [DecidableEq V] in
/-- `M_* ≥ 0` for nonnegative weights. -/
theorem combinedEdgeCard_nonneg {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
    {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j) : 0 ≤ combinedEdgeCard Hs μ :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hμ j) (Nat.cast_nonneg _)

/-- **`eq:combined-lipschitz`.**  `|𝒫_W(u) - 𝒫_W(u')| ≤ 2M_* ‖u - u'‖₁` for rows `u, u'`. -/
theorem combined_lipschitz (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j) {u u' : ℝ → ℝ} (hu : IsRow u)
    (hu' : IsRow u') :
    |combinedRooted Hs W μ u - combinedRooted Hs W μ u'|
      ≤ 2 * combinedEdgeCard Hs μ * ∫ y, |u y - u' y| ∂unitμ := by
  unfold combinedRooted
  rw [← Finset.sum_sub_distrib]
  calc |∑ j, (μ j * totalRootedDensity (Hs j) W u - μ j * totalRootedDensity (Hs j) W u')|
      ≤ ∑ j, |μ j * totalRootedDensity (Hs j) W u - μ j * totalRootedDensity (Hs j) W u'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, μ j * (2 * (Hs j).edgeFinset.card * ∫ y, |u y - u' y| ∂unitμ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hμ j)]
        exact mul_le_mul_of_nonneg_left (rooted_lipschitz (Hs j) W hu hu') (hμ j)
    _ = 2 * combinedEdgeCard Hs μ * ∫ y, |u y - u' y| ∂unitμ := by
        rw [combinedEdgeCard, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **`ℱ_W` only depends on the almost everywhere class of a row.**  This is what lets
`sec:row-criterion` read `𝓜_W` as a subset of `L^∞([0,1])`, as the paper does; see
`rowMinimizersLinfty` in `RowCriterion/Linfty.lean`.  No sign condition on the weights is needed,
because `eq:rooted-lipschitz` applies to each term separately. -/
theorem combinedRowFunctional_congr_ae (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (q α : ℝ) (μ : ι → ℝ) {u u' : ℝ → ℝ}
    (hu : IsRow u) (hu' : IsRow u') (h : u =ᵐ[unitμ] u') :
    combinedRowFunctional Hs W q α μ u = combinedRowFunctional Hs W q α μ u' := by
  have hL1 : ∫ y, |u y - u' y| ∂unitμ = 0 := by
    have hae : (fun y => |u y - u' y|) =ᵐ[unitμ] fun _ => (0:ℝ) :=
      h.mono fun y hy => by show |u y - u' y| = (0:ℝ); rw [hy]; simp
    rw [integral_congr_ae hae, integral_zero]
  have hP : combinedRooted Hs W μ u = combinedRooted Hs W μ u' := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlip := rooted_lipschitz (Hs j) W hu hu'
    rw [hL1, mul_zero] at hlip
    have h0 : totalRootedDensity (Hs j) W u - totalRootedDensity (Hs j) W u' = 0 :=
      abs_eq_zero.mp (le_antisymm hlip (abs_nonneg _))
    rw [show totalRootedDensity (Hs j) W u = totalRootedDensity (Hs j) W u' by linarith]
  have hJ : ∫ y, Jp q (u y) ∂unitμ = ∫ y, Jp q (u' y) ∂unitμ :=
    integral_congr_ae (h.mono fun y hy => by show Jp q (u y) = Jp q (u' y); rw [hy])
  have hm : ∫ y, u y ∂unitμ = ∫ y, u' y ∂unitμ := integral_congr_ae h
  simp only [combinedRowFunctional, hJ, hm, hP]

/-- **`eq:rooted-average` for the family.**
`∫₀¹ 𝒫_W(W_x) dx = ∑_j μ_j N t(H_j,W)`. -/
theorem combined_average (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] (W : Graphon)
    (μ : ι → ℝ) :
    ∫ x, combinedRooted Hs W μ (W.row x) ∂unitμ
      = ∑ j, μ j * (Fintype.card V * W.tDensity (Hs j)) := by
  unfold combinedRooted
  have hint : ∀ j ∈ (Finset.univ : Finset ι),
      Integrable (fun x => μ j * totalRootedDensity (Hs j) W (W.row x)) unitμ := by
    intro j _
    refine Integrable.const_mul ?_ _
    have hF := isBddMeas_prod_edgeVal W (Hs j).edgeFinset
    refine integrable_finsetSum _ fun v _ => ?_
    simp_rw [rootedDensity_row]
    exact integrable_integral_update_pi v hF
  rw [integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, rooted_average (Hs j) W]

/-! ### The single-term family -/

/-- The combined rooted density of the one-term family is the single rooted density. -/
@[simp] theorem combinedRooted_one (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (μ : ℝ) (u : ℝ → ℝ) :
    combinedRooted (fun _ : Fin 1 => H) W (fun _ => μ) u = μ * totalRootedDensity H W u := by
  rw [combinedRooted, Fin.sum_univ_one]

/-- The combined gradient of the one-term family is the single gradient. -/
@[simp] theorem combinedRootedGradient_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) (μ : ℝ) (u : ℝ → ℝ) (y : ℝ) :
    combinedRootedGradient (fun _ : Fin 1 => H) W (fun _ => μ) u y
      = μ * rootedGradient H W u y := by
  rw [combinedRootedGradient, Fin.sum_univ_one]

omit [DecidableEq V] in
/-- `M_*` for the one-term family. -/
@[simp] theorem combinedEdgeCard_one (H : SimpleGraph V) [DecidableRel H.Adj] (μ : ℝ) :
    combinedEdgeCard (fun _ : Fin 1 => H) (fun _ => μ) = μ * H.edgeFinset.card := by
  rw [combinedEdgeCard, Fin.sum_univ_one]

/-- The row functional of the one-term family is the single-term row functional. -/
@[simp] theorem combinedRowFunctional_one (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (q α μ : ℝ) (u : ℝ → ℝ) :
    combinedRowFunctional (fun _ : Fin 1 => H) W q α (fun _ => μ) u
      = rowFunctional H W q α μ u := by
  rw [combinedRowFunctional, rowFunctional, combinedRooted_one]

/-- The minimizers of the one-term family are the single-term minimizers. -/
@[simp] theorem combinedRowMinimizers_one (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (q α μ c : ℝ) :
    combinedRowMinimizers (fun _ : Fin 1 => H) W q α (fun _ => μ) c
      = rowMinimizers H W q α μ c := by
  unfold combinedRowMinimizers rowMinimizers
  simp only [combinedRowFunctional_one]

end UpperTailMultipodality
