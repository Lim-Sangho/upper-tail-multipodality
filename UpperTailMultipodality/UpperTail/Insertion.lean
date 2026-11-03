import UpperTailMultipodality.UpperTail.Basic
import UpperTailMultipodality.Insertion.FirstOrder
import UpperTailMultipodality.Insertion.Rows

/-!
# Global row minimality for the upper-tail problem (`lem:global-row-minimality`)
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:global-row-minimality`, for a single constraint.**  With `μ` as in
`upper_tail_multiplier`, the row
functional with `q = p` and `α = 0` satisfies `ℱ_W ≥ c_W := 2I_p(W) - μN t(H,W)` on all rows, and
almost every row of `W` attains `c_W`. -/
theorem upper_tail_insertion (H : SimpleGraph V) [DecidableRel H.Adj]
    (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p) (hpr : p < r) (hr1 : r < 1)
    {W : Graphon} (hW : Feasible H r W) (hmin : W.Ip p = phiVar H p r) {μ : ℝ} (hμ : 0 < μ)
    (hEL : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = μ * derivKernel H W z.1 z.2) :
    (∀ u, IsRow u → 2 * W.Ip p - μ * Fintype.card V * W.tDensity H
        ≤ rowFunctional H W p 0 μ u) ∧
      ∀ᵐ x ∂unitμ, rowFunctional H W p 0 μ (W.row x)
        = 2 * W.Ip p - μ * Fintype.card V * W.tDensity H := by
  /- Proof.  Insert a block of measure `θ` with row `u` and value `p`, and shift the old values
  by `κθ` (along the constant direction, cut off outside `{η < W < 1-η}`, which is a null set).
  If `ℱ_W(u) < c_W`, then for a suitable `κ` the `H`-density increases to first order, so the
  insertion is feasible for small `θ > 0`, while `I_p` decreases to first order; this contradicts
  minimality (`insertion_derivative_nonneg`).  No implicit function is needed, because the
  constraint `t(H,·) ≥ r^m` is an inequality.  The statement about rows is
  `ae_rowFunctional_row_eq`. -/
  obtain ⟨hWp, -, γ, hγ, hWγ⟩ := upper_tail_basic H hm hp0 hpr hr1 hW hmin
  have hp1 : p < 1 := hpr.trans hr1
  have hb : 1 - γ < 1 := by linarith
  have hWab : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc p (1 - γ) := by
    filter_upwards [hWp, hWγ] with z h1 h2 using ⟨h1, h2⟩
  have hEL' : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = 0 + μ * derivKernel H W z.1 z.2 := by
    filter_upwards [hEL] with z hz
    rw [hz, zero_add]
  -- The constant direction `1`, cut off where `W` is close to `0` or `1`.
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min p γ / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact half_pos (lt_min hp0 hγ)
  have hηp : η < p := by
    rw [hηdef]; linarith [min_le_left p γ, half_lt_self (lt_min hp0 hγ)]
  have hηγ : η < γ := by
    rw [hηdef]; linarith [min_le_right p γ, half_lt_self (lt_min hp0 hγ)]
  obtain ⟨Z, hZdef⟩ : ∃ Z : Kernel, ∀ x y,
      Z.toFun x y = if η < W.toFun x y ∧ W.toFun x y < 1 - η then 1 else 0 := by
    refine ⟨{ toFun := fun x y => if η < W.toFun x y ∧ W.toFun x y < 1 - η then 1 else 0
              symm' := fun x y => by rw [W.symm' x y]
              meas' := ?_
              bdd' := ⟨1, fun x y => by split_ifs <;> simp⟩ }, fun _ _ => rfl⟩
    show Measurable fun z : ℝ × ℝ =>
      if η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η then (1:ℝ) else 0
    exact Measurable.ite ((measurableSet_lt measurable_const W.measurable_uncurry).inter
      (measurableSet_lt W.measurable_uncurry measurable_const)) measurable_const measurable_const
  have hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η := by
    intro x y h
    by_contra hc
    exact h (by rw [hZdef, if_neg hc])
  have hZ1 : ∀ᵐ z ∂gμ, Z.toFun z.1 z.2 = 1 := by
    filter_upwards [hWab] with z hz
    rw [hZdef, if_pos ⟨by linarith [hz.1], by linarith [hz.2]⟩]
  obtain ⟨hDZint, hJZ⟩ := euler_lagrange_integral H W Z hp0 hp1 hp0 hb hWab hμ.ne' hEL'
  -- `D₁ = ∫∫ 𝒟_W > 0`.
  obtain ⟨D₁, hD₁⟩ : ∃ D₁, D₁ = ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  have hD₁pos : 0 < D₁ := by
    have hc : 0 < (H.edgeFinset.card : ℝ) * p ^ (H.edgeFinset.card - 1) :=
      mul_pos (by exact_mod_cast hm) (pow_pos hp0 _)
    have hle : ∀ᵐ z ∂gμ, (H.edgeFinset.card : ℝ) * p ^ (H.edgeFinset.card - 1)
        ≤ derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 := by
      filter_upwards [derivKernel_ge H W hp0.le hWp, hZ1] with z h1 h2
      rw [h2, mul_one]; exact h1
    have h := integral_mono_ae (integrable_const _) hDZint hle
    rw [integral_const, probReal_univ, one_smul] at h
    rw [hD₁]; linarith
  have hrow : ∀ u, IsRow u → 2 * W.Ip p - μ * Fintype.card V * W.tDensity H
      ≤ rowFunctional H W p 0 μ u := by
    intro u hu
    by_contra hlt
    push Not at hlt
    obtain ⟨R, hR⟩ : ∃ R, R = totalRootedDensity H W u - Fintype.card V * W.tDensity H :=
      ⟨_, rfl⟩
    obtain ⟨gap, hgap⟩ : ∃ gap,
        gap = 2 * W.Ip p - μ * Fintype.card V * W.tDensity H - rowFunctional H W p 0 μ u :=
      ⟨_, rfl⟩
    have hgap0 : 0 < gap := by rw [hgap]; linarith
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = -R / D₁ + gap / (2 * μ * D₁) := ⟨_, rfl⟩
    have hκD : κ * D₁ = -R + gap / (2 * μ) := by
      rw [hκ]; field_simp
    have hg : HasDerivAt (fun θ : ℝ => κ * θ) κ 0 :=
      hasDerivAt_of_eq ((hasDerivAt_id' (0:ℝ)).const_mul κ) (fun _ => rfl) (mul_one κ)
    have hpos : 0 < κ * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        + totalRootedDensity H W u - Fintype.card V * W.tDensity H := by
      rw [← hD₁, hκD]
      have : 0 < gap / (2 * μ) := by positivity
      linarith
    have hmin' : ∀ᶠ θ in 𝓝[>] (0:ℝ), ∀ W' : Graphon, W.tDensity H < W'.tDensity H →
        W'.edgeDensity = θ ^ 2 * p + 2 * θ * (1 - θ) * ∫ y, u y ∂unitμ
          + (1 - θ) ^ 2 * (W.edgeDensity + κ * θ * ∫ z, Z.toFun z.1 z.2 ∂gμ) →
        W.Ip p ≤ W'.Ip p := by
      refine Eventually.of_forall fun θ W' ht _ => ?_
      rw [hmin]
      refine csInf_le ⟨0, ?_⟩ ⟨W', hW.trans ht.le, rfl⟩
      rintro y ⟨W'', -, rfl⟩
      exact Ip_nonneg W'' hp0 hp1
    have hnn := insertion_derivative_nonneg H W Z hη hZ ⟨hp0.le, hp1.le⟩ hu hg (by simp)
      hp0 hp1 hp0 hb hWab hpos hmin'
    rw [hJZ, ← hD₁] at hnn
    have hF : rowFunctional H W p 0 μ u
        = 2 * ∫ y, Jp p (u y) ∂unitμ - μ * totalRootedDensity H W u := by
      unfold rowFunctional; ring
    have hkey : κ * (0 * ∫ z, Z.toFun z.1 z.2 ∂gμ + μ * D₁) = μ * (κ * D₁) := by ring
    rw [hkey, hκD] at hnn
    have hμgap : μ * (-R + gap / (2 * μ)) = -μ * R + gap / 2 := by
      field_simp
    rw [hμgap] at hnn
    rw [hF] at hgap
    rw [hR] at hnn
    linarith
  exact ⟨hrow, ae_rowFunctional_row_eq H W hp0 hp1 hrow (by ring)⟩

end UpperTailMultipodality
