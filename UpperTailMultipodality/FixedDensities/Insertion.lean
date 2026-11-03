import UpperTailMultipodality.FixedDensities.Interior
import UpperTailMultipodality.Insertion.FirstOrder
import UpperTailMultipodality.Insertion.Rows

/-!
# The insertion inequality for fixed densities (`lem:fixed-insertion`)
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:fixed-insertion`.**  With `α, μ` as in `lem:fixed-multiplier`, the row functional with
`q = ε` satisfies `ℱ_W ≥ c_W := 2I_ε(W) - 2αε - μNτ` on all rows, and almost every row of `W`
attains `c_W`. -/
theorem fixed_insertion (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsFixedMinimizer H ε τ W)
    (hcq : ConstraintQualification H W) {α μ : ℝ} (hμ : 0 < μ)
    (hEL : ∀ᵐ z ∂gμ, Jp' ε (W.toFun z.1 z.2) = α + μ * derivKernel H W z.1 z.2) :
    (∀ u, IsRow u → 2 * W.Ip ε - 2 * α * ε - μ * Fintype.card V * τ
        ≤ rowFunctional H W ε α μ u) ∧
      ∀ᵐ x ∂unitμ, rowFunctional H W ε α μ (W.row x)
        = 2 * W.Ip ε - 2 * α * ε - μ * Fintype.card V * τ := by
  /- Proof.  Insert a block of measure `θ` with row `u` and value `ε`, and move the old values
  along `W + θ/(1-θ) Z` with `Z = v₁U₁ + v₂U₂`.  Since `e` is affine along this path, the choice
  `∫∫ Z = -2(∫u - ε)` keeps `e = ε` exactly, and the invertibility of `Γ_W(U₁,U₂)` lets us also
  prescribe `∫∫ 𝒟_W Z`.  If `ℱ_W(u) < c_W`, a suitable choice makes `t(H,·)` increase to first
  order, so `lem:fixed-monotonicity` applies for small `θ > 0`, while `I_ε` decreases to first order
  (`insertion_derivative_nonneg`), a contradiction.  The statement about rows is
  `ae_rowFunctional_row_eq`. -/
  obtain ⟨γ, hγ, hWγ⟩ := fixed_interior H hΔ hε0 hε1 hτ0 hτ1 hW hcq
  obtain ⟨he, ht, hI⟩ := hW
  obtain ⟨η, hη, U₁, U₂, hU₁, hU₂, hdet⟩ := hcq
  have hb : 1 - γ < 1 := by linarith
  have hWab : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc γ (1 - γ) :=
    hWγ.mono fun z hz => ⟨hz.1, hz.2⟩
  obtain ⟨hDU₁, -⟩ := euler_lagrange_integral H W U₁ hε0 hε1 hγ hb hWab hμ.ne' hEL
  obtain ⟨hDU₂, -⟩ := euler_lagrange_integral H W U₂ hε0 hε1 hγ hb hWab hμ.ne' hEL
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = ∫ z, U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = ∫ z, U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨d₁, hd₁⟩ : ∃ d, d = ∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d, d = ∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  have hΔ' : a₁ * d₂ - a₂ * d₁ ≠ 0 := by
    rw [ha₁, ha₂, hd₁, hd₂]; exact hdet
  have hrow : ∀ u, IsRow u → 2 * W.Ip ε - 2 * α * ε - μ * Fintype.card V * τ
      ≤ rowFunctional H W ε α μ u := by
    intro u hu
    by_contra hlt
    push Not at hlt
    obtain ⟨E, hE⟩ : ∃ E, E = (∫ y, u y ∂unitμ) - ε := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = totalRootedDensity H W u - Fintype.card V * τ := ⟨_, rfl⟩
    obtain ⟨gap, hgap⟩ : ∃ gap,
        gap = 2 * W.Ip ε - 2 * α * ε - μ * Fintype.card V * τ - rowFunctional H W ε α μ u :=
      ⟨_, rfl⟩
    have hgap0 : 0 < gap := by rw [hgap]; linarith
    -- Solve `a·v = -2E`, `d·v = -R + gap/(2μ)` by Cramer's rule.
    obtain ⟨s, hs⟩ : ∃ s, s = -R + gap / (2 * μ) := ⟨_, rfl⟩
    obtain ⟨v₁, hv₁⟩ : ∃ v, v = ((-2 * E) * d₂ - a₂ * s) / (a₁ * d₂ - a₂ * d₁) := ⟨_, rfl⟩
    obtain ⟨v₂, hv₂⟩ : ∃ v, v = (a₁ * s - d₁ * (-2 * E)) / (a₁ * d₂ - a₂ * d₁) := ⟨_, rfl⟩
    have hav : a₁ * v₁ + a₂ * v₂ = -2 * E := by
      have h : a₁ * v₁ + a₂ * v₂
          = (-2 * E) * ((a₁ * d₂ - a₂ * d₁) / (a₁ * d₂ - a₂ * d₁)) := by
        rw [hv₁, hv₂]; ring
      rw [h, div_self hΔ', mul_one]
    have hdv : d₁ * v₁ + d₂ * v₂ = s := by
      have h : d₁ * v₁ + d₂ * v₂ = s * ((a₁ * d₂ - a₂ * d₁) / (a₁ * d₂ - a₂ * d₁)) := by
        rw [hv₁, hv₂]; ring
      rw [h, div_self hΔ', mul_one]
    obtain ⟨Z, hZdef⟩ : ∃ Z : Kernel, Z = v₁ • U₁ + v₂ • U₂ := ⟨_, rfl⟩
    have hZapp : ∀ x y, Z.toFun x y = v₁ * U₁.toFun x y + v₂ * U₂.toFun x y := by
      intro x y; rw [hZdef]; rfl
    have hZ : ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η := by
      intro x y h
      by_cases h1 : U₁.toFun x y = 0
      · by_cases h2 : U₂.toFun x y = 0
        · exact absurd (by rw [hZapp, h1, h2]; ring) h
        · exact hU₂ x y h2
      · exact hU₁ x y h1
    have hintZ : ∫ z, Z.toFun z.1 z.2 ∂gμ = -2 * E := by
      rw [← hav, ha₁, ha₂, ← integral_mul_const, ← integral_mul_const,
        ← integral_add ((integrable_kernel U₁).mul_const _)
          ((integrable_kernel U₂).mul_const _)]
      exact integral_congr_ae (ae_of_all _ fun z => by beta_reduce; rw [hZapp]; ring)
    have hintDZ : ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ = s := by
      rw [← hdv, hd₁, hd₂, ← integral_mul_const, ← integral_mul_const,
        ← integral_add (hDU₁.mul_const _) (hDU₂.mul_const _)]
      exact integral_congr_ae (ae_of_all _ fun z => by beta_reduce; rw [hZapp]; ring)
    obtain ⟨-, hJZ⟩ := euler_lagrange_integral H W Z hε0 hε1 hγ hb hWab hμ.ne' hEL
    -- The reparametrization `ξ(θ) = θ/(1-θ)` keeps the edge density exact.
    have hg : HasDerivAt (fun θ : ℝ => θ / (1 - θ)) 1 0 := by
      have h := (hasDerivAt_id' (0:ℝ)).div ((hasDerivAt_id' (0:ℝ)).const_sub 1) (by norm_num)
      exact hasDerivAt_of_eq h (fun _ => rfl) (by norm_num)
    have hpos : 0 < 1 * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        + totalRootedDensity H W u - Fintype.card V * W.tDensity H := by
      rw [hintDZ, ht, hs]
      have : 0 < gap / (2 * μ) := by positivity
      linarith
    have hmin' : ∀ᶠ θ in 𝓝[>] (0:ℝ), ∀ W' : Graphon, W.tDensity H < W'.tDensity H →
        W'.edgeDensity = θ ^ 2 * ε + 2 * θ * (1 - θ) * ∫ y, u y ∂unitμ
          + (1 - θ) ^ 2 * (W.edgeDensity + θ / (1 - θ) * ∫ z, Z.toFun z.1 z.2 ∂gμ) →
        W.Ip ε ≤ W'.Ip ε := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with θ hθ1 W' ht' he'
      have hθ1' : (1:ℝ) - θ ≠ 0 := by have : θ < 1 := hθ1; linarith
      have he'' : W'.edgeDensity = ε := by
        rw [he', he, hintZ, hE]
        field_simp
        ring
      exact (fixed_monotone H hΔ hε0 hε1).2 τ ⟨hτ0, hτ1⟩ W he ht hI W' he'' (ht ▸ ht'.le)
    have hnn := insertion_derivative_nonneg H W Z hη hZ ⟨hε0.le, hε1.le⟩ hu hg (by simp)
      hε0 hε1 hγ hb hWab hpos hmin'
    rw [hJZ, hintZ, hintDZ, hs] at hnn
    have hF : rowFunctional H W ε α μ u
        = 2 * ∫ y, Jp ε (u y) ∂unitμ - 2 * α * ∫ y, u y ∂unitμ
          - μ * totalRootedDensity H W u := rfl
    have hμgap : μ * (-R + gap / (2 * μ)) = -μ * R + gap / 2 := by
      field_simp
    rw [one_mul, hμgap, hR, hE] at hnn
    rw [hF] at hgap
    linarith
  exact ⟨hrow, ae_rowFunctional_row_eq H W hε0 hε1 hrow (by rw [he, ht])⟩

end UpperTailMultipodality
