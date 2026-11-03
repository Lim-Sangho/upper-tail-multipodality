import UpperTailMultipodality.FixedDensities.Defs

/-!
# Kernels, graphons and the derivative kernel: measure-theoretic facts

Helpers for `sec:fixed-densities` and `sec:degenerate-optimizers`:

* integrability of bounded kernels;
* a kernel with values in `[0,1]` almost everywhere agrees almost everywhere with a graphon;
* the indicator kernel of a symmetric measurable set.

The measurability, symmetry and almost-everywhere invariance of `𝒟_W` and `t(H,·)` are in
`Preliminaries/DerivativeKernel.lean`.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A bounded symmetric kernel has a nonnegative uniform bound. -/
theorem kernel_bound (K : Kernel) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |K.toFun x y| ≤ C := by
  obtain ⟨C, hC⟩ := K.bdd'
  exact ⟨max C 0, le_max_right _ _, fun x y => (hC x y).trans (le_max_left _ _)⟩

/-- A bounded kernel is integrable on `[0,1]²`. -/
theorem kernel_integrable (K : Kernel) : Integrable (fun z : ℝ × ℝ => K.toFun z.1 z.2) gμ := by
  obtain ⟨C, hC⟩ := K.bdd'
  exact integrable_of_abs_le K.meas' C (fun z => hC z.1 z.2)

/-- `t(H,·)` of two kernels with the same values. -/
theorem kernel_tDensity_congr (H : SimpleGraph V) [DecidableRel H.Adj] {K L : Kernel}
    (h : ∀ x y, K.toFun x y = L.toFun x y) : K.tDensity H = L.tDensity H :=
  kernel_tDensity_congr_ae H (ae_of_all _ fun z => h z.1 z.2)

/-- The pointwise clamp of a kernel to `[0,1]`, as a graphon. -/
noncomputable def clampGraphon (K : Kernel) : Graphon where
  toFun x y := max 0 (min 1 (K.toFun x y))
  symm' x y := by rw [K.symm']
  meas' := by
    have h : Measurable fun z : ℝ × ℝ => max 0 (min 1 (K.toFun z.1 z.2)) :=
      measurable_const.max (measurable_const.min K.meas')
    exact h
  nonneg' _ _ := le_max_left _ _
  le_one' _ _ := max_le zero_le_one (min_le_left _ _)

/-- The value of the clamped graphon. -/
theorem clampGraphon_apply (K : Kernel) (x y : ℝ) :
    (clampGraphon K).toFun x y = max 0 (min 1 (K.toFun x y)) := rfl

/-- **A kernel with values in `[0,1]` almost everywhere is almost everywhere a graphon**, with
the same edge density, homomorphism densities and relative entropy. -/
theorem exists_graphon_of_ae_mem (H : SimpleGraph V) [DecidableRel H.Adj] (K : Kernel) (p : ℝ)
    (h : ∀ᵐ z ∂gμ, K.toFun z.1 z.2 ∈ Set.Icc (0:ℝ) 1) :
    ∃ G : Graphon, (∀ᵐ z ∂gμ, G.toFun z.1 z.2 = K.toFun z.1 z.2) ∧
      G.edgeDensity = K.edgeDensity ∧ G.tDensity H = K.tDensity H ∧ G.Ip p = K.Ip p := by
  have hae : ∀ᵐ z ∂gμ, (clampGraphon K).toFun z.1 z.2 = K.toFun z.1 z.2 := by
    filter_upwards [h] with z hz
    rw [clampGraphon_apply, min_eq_right hz.2, max_eq_right hz.1]
  refine ⟨clampGraphon K, hae, ?_, ?_, ?_⟩
  · exact integral_congr_ae hae
  · exact kernel_tDensity_congr_ae H (K := Kernel.ofGraphon (clampGraphon K)) hae
  · exact integral_congr_ae (hae.mono fun z hz => by simp only [hz])

/-- A kernel with values in `[0,1]` everywhere is a graphon. -/
theorem exists_graphon_of_mem (K : Kernel) (h : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1) :
    ∃ G : Graphon, ∀ x y, G.toFun x y = K.toFun x y :=
  ⟨K.toGraphon (fun x y => (h x y).1) (fun x y => (h x y).2), fun _ _ => rfl⟩

/-- The kernel `σ 1_E` of a measurable symmetric set `E ⊆ ℝ²`. -/
noncomputable def indicatorKernel (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) (σ : ℝ) : Kernel where
  toFun x y := E.indicator (fun _ => σ) (x, y)
  symm' x y := by
    by_cases h : (x, y) ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hsymm x y h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hsymm y x h'))]
  meas' := measurable_const.indicator hE
  bdd' := ⟨|σ|, fun x y => by by_cases h : (x, y) ∈ E <;> simp [h]⟩

/-- The value of the kernel `σ 1_E`. -/
theorem indicatorKernel_apply (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) (σ x y : ℝ) :
    (indicatorKernel E hE hsymm σ).toFun x y = E.indicator (fun _ => σ) (x, y) := rfl

/-- `∫∫ σ 1_E = σ |E|`. -/
theorem integral_indicatorKernel (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) (σ : ℝ) :
    ∫ z, (indicatorKernel E hE hsymm σ).toFun z.1 z.2 ∂gμ = σ * gμ.real E := by
  simp only [indicatorKernel_apply, Prod.mk.eta]
  rw [integral_indicator_const σ hE, smul_eq_mul, mul_comm]

/-! ### The derivative kernel -/

/-- `|𝒟_W| ≤ m`. -/
theorem abs_derivKernel_le (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (x y : ℝ) :
    |derivKernel H W x y| ≤ H.edgeFinset.card := by
  have h := derivKernel_mem_Icc H W x y
  rw [abs_of_nonneg h.1]; exact h.2

end FixedDensities

end UpperTailMultipodality
