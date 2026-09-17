import UpperTailMultipodality.RowCriterion.Finiteness.Functional

/-!
# Strict positivity of the second variation on mean-zero functions

This is the qualitative half of `lem:coercive`: at a global minimizer `u` of `ℱ_W` the second
variation `Q_u` is nonnegative (`secondVariation_nonneg`), and it is *strictly* positive at every
nonzero mean-zero direction.  Writing `h = h₊ - h₋` with disjoint supports,

`Q_u(h) = Q_u(h₊) + Q_u(h₋) + μ(D²ℛ_W(u)[h₊,h₋] + D²ℛ_W(u)[h₋,h₊])`,

and the mixed terms are bounded below by `c^N ω^m ‖h₊‖₁‖h₋‖₁ > 0` by
`integ_gradDeriv_mul_ge`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj] {W : Graphon} {q α μ : ℝ}

/-- The integrand of the entropy part of the second variation is integrable. -/
theorem integrable_Jpp_mul_sq {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (k : BddMeas) :
    Integrable (fun y => Jp'' (u y) * k y ^ 2) unitμ := by
  have hmeasJ'' : Measurable Jp'' := by unfold Jp''; fun_prop
  refine integrable_of_abs_le ((hmeasJ''.comp u.measurable).mul (k.measurable.pow_const 2))
    (1 / (c * (1 - d)) * ‖k‖ ^ 2) fun y => ?_
  rw [abs_mul, abs_pow]
  have hJ := Jp''_mem_of_mem_Icc hc hd (hu y)
  rw [abs_of_pos hJ.1]
  exact mul_le_mul hJ.2 (pow_le_pow_left₀ (abs_nonneg _) (k.abs_apply_le_norm y) 2)
    (by positivity) (hJ.1.le.trans hJ.2)

/-- The splitting of the second variation along the positive and negative parts. -/
theorem secondVariation_split {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    secondVariation H W μ u h
      = secondVariation H W μ u (BddMeas.posPart h) + secondVariation H W μ u (BddMeas.negPart h)
        + μ * (BddMeas.integ (gradDeriv H W u (BddMeas.posPart h) * BddMeas.negPart h)
          + BddMeas.integ (gradDeriv H W u (BddMeas.negPart h) * BddMeas.posPart h)) := by
  set a := BddMeas.posPart h with ha
  set b := BddMeas.negPart h with hb
  have hab : a * b = 0 := BddMeas.posPart_mul_negPart h
  have hh : h = a - b := (BddMeas.posPart_sub_negPart h).symm
  -- the entropy part splits pointwise
  have hsq : ∀ y, h y ^ 2 = a y ^ 2 + b y ^ 2 := by
    intro y
    have h0 : a y * b y = 0 := by
      have := congrArg (fun f : BddMeas => f y) hab
      simpa [BddMeas.mul_apply] using this
    have : h y = a y - b y := by rw [hh]; rfl
    rw [this]; nlinarith [h0]
  have hentropy : ∫ y, Jp'' (u y) * h y ^ 2 ∂unitμ
      = (∫ y, Jp'' (u y) * a y ^ 2 ∂unitμ) + ∫ y, Jp'' (u y) * b y ^ 2 ∂unitμ := by
    rw [← integral_add (integrable_Jpp_mul_sq hc hd hu a) (integrable_Jpp_mul_sq hc hd hu b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Jp'' (u y) * h y ^ 2 = Jp'' (u y) * a y ^ 2 + Jp'' (u y) * b y ^ 2
    rw [hsq y]; ring
  -- the gradient part splits by bilinearity
  have hgrad : gradDeriv H W u h * h
      = gradDeriv H W u a * a + gradDeriv H W u b * b
        - (gradDeriv H W u a * b + gradDeriv H W u b * a) := by
    rw [hh, map_sub]
    ring
  rw [secondVariation, secondVariation, secondVariation, hentropy, hgrad, map_sub, map_add,
    map_add]
  ring

/-- **Strict positivity of the second variation on mean-zero directions** (`lem:coercive`).  If
`u` is a global minimizer of `ℱ_W` over rows with values in `[c,d] ⊆ (0,1)` satisfying
`eq:row-euler`, then `Q_u(h) > 0` for every `h` of mean zero that does not vanish almost
everywhere. -/
theorem secondVariation_pos (hΔ : ∃ v, 2 ≤ H.degree v) (hq0 : 0 < q) (hq1 : q < 1) (hμ : 0 < μ)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {c d : ℝ} (hc : 0 < c) (hd : d < 1) (hc1 : c ≤ 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE H W q α μ u ≤ rowFunctionalE H W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = μ * gradE H W u y)
    {h : BddMeas} (hmean : BddMeas.integ h = 0) (hne : ¬ (⇑h =ᵐ[unitμ] 0)) :
    0 < secondVariation H W μ u h := by
  set a := BddMeas.posPart h with ha
  set b := BddMeas.negPart h with hb
  have hane : ∀ y, 0 ≤ a y := BddMeas.posPart_nonneg h
  have hbne : ∀ y, 0 ≤ b y := BddMeas.negPart_nonneg h
  -- the means of the two parts agree and are positive
  have hsub : BddMeas.integ a - BddMeas.integ b = 0 := by
    rw [← map_sub, BddMeas.posPart_sub_negPart h, hmean]
  have habs : BddMeas.integ a + BddMeas.integ b = ∫ y, |h y| ∂unitμ := by
    rw [← map_add, BddMeas.integ_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (a + b) y = |h y|
    rw [BddMeas.add_apply, ha, hb, BddMeas.posPart_apply, BddMeas.negPart_apply]
    rcases le_total (h y) 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (by linarith : (0:ℝ) ≤ -h y), abs_of_nonpos hy]
      ring
    · rw [max_eq_left hy, max_eq_right (by linarith : -h y ≤ 0), abs_of_nonneg hy]
      ring
  have habspos : 0 < ∫ y, |h y| ∂unitμ := by
    rcases lt_or_eq_of_le (integral_nonneg (f := fun y => |h y|)
      (fun y => abs_nonneg (h y))) with hpos | hzero
    · exact hpos
    · exfalso
      apply hne
      have hz := (integral_eq_zero_iff_of_nonneg (f := fun y => |h y|)
        (fun y => abs_nonneg (h y)) h.integrable.abs).mp hzero.symm
      filter_upwards [hz] with y hy
      simpa [abs_eq_zero] using hy
  have hapos : 0 < BddMeas.integ a := by
    have := habs
    have h2 : BddMeas.integ a = BddMeas.integ b := by linarith
    linarith
  have hbpos : 0 < BddMeas.integ b := by
    have h2 : BddMeas.integ a = BddMeas.integ b := by linarith
    linarith
  -- the diagonal terms are nonnegative
  have hQa := secondVariation_nonneg (H := H) (W := W) (α := α) (μ := μ) hq0 hq1 hc hd hu hmin
    hEL a
  have hQb := secondVariation_nonneg (H := H) (W := W) (α := α) (μ := μ) hq0 hq1 hc hd hu hmin
    hEL b
  -- the mixed terms are positive
  have hcross : ∀ x y : BddMeas, (∀ t, 0 ≤ x t) → (∀ t, 0 ≤ y t) →
      c ^ Fintype.card V * ω ^ H.edgeFinset.card * BddMeas.integ x * BddMeas.integ y
        ≤ BddMeas.integ (gradDeriv H W u x * y) := by
    intro x y hx hy
    exact integ_gradDeriv_mul_ge hΔ hω0.le hω1 hWω hc.le hc1 (fun t => (hu t).1) hx hy
  have h1 := hcross a b hane hbne
  have h2 := hcross b a hbne hane
  have hconst : 0 < c ^ Fintype.card V * ω ^ H.edgeFinset.card := by positivity
  have hpos1 : 0 < c ^ Fintype.card V * ω ^ H.edgeFinset.card * BddMeas.integ a
      * BddMeas.integ b := by positivity
  have hpos2 : 0 < c ^ Fintype.card V * ω ^ H.edgeFinset.card * BddMeas.integ b
      * BddMeas.integ a := by positivity
  rw [secondVariation_split hc hd hu h]
  have := mul_pos hμ (by linarith : (0:ℝ) < BddMeas.integ (gradDeriv H W u a * b)
    + BddMeas.integ (gradDeriv H W u b * a))
  linarith

end UpperTailMultipodality
