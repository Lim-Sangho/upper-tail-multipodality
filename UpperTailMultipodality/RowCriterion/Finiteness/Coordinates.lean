import UpperTailMultipodality.RowCriterion.Defs

/-!
# Coordinates of the product measure

Lemmas about the product measure `Measure.pi (fun _ : V => unitμ)` used for rooted densities:
resampling one coordinate (`measurePreserving_update`, `integral_integral_update`), the
one-coordinate and two-coordinate marginals, and almost everywhere statements transported
along coordinates.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- `(ξ, y) ↦ ξ[w ↦ y]` is measurable. -/
theorem measurable_update_pair (w : V) :
    Measurable (fun p : (V → ℝ) × ℝ => Function.update p.1 w p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i = w
  · subst h
    have he : (fun p : (V → ℝ) × ℝ => Function.update p.1 i p.2 i) = fun p => p.2 := by
      funext p; simp
    rw [he]; exact measurable_snd
  · have he : (fun p : (V → ℝ) × ℝ => Function.update p.1 w p.2 i) = fun p => p.1 i := by
      funext p; simp [Function.update_of_ne h]
    rw [he]; exact (measurable_pi_apply i).comp measurable_fst

/-- **Resampling one coordinate preserves the product measure**: `(ξ, y) ↦ ξ[w ↦ y]` pushes
`π ⊗ unitμ` forward to `π`. -/
theorem measurePreserving_update (w : V) :
    MeasurePreserving (fun p : (V → ℝ) × ℝ => Function.update p.1 w p.2)
      ((Measure.pi fun _ : V => unitμ).prod unitμ) (Measure.pi fun _ : V => unitμ) := by
  refine ⟨measurable_update_pair w, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (V → ℝ) × ℝ => Function.update p.1 w p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s w Set.univ)) ×ˢ s w := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = w
        · subst hi; rw [Function.update_self]; exact Set.mem_univ _
        · rw [Function.update_of_ne hi]
          have hpi := hp i
          rwa [Function.update_of_ne hi] at hpi
      · have hpw := hp w
        rwa [Function.update_self] at hpw
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = w
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        have h1i := h1 i
        rwa [Function.update_of_ne hi] at h1i
  have hrest : (∏ i ∈ Finset.univ.erase w, unitμ (Function.update s w Set.univ i))
      = ∏ i ∈ Finset.univ.erase w, unitμ (s i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [Measure.map_apply (measurable_update_pair w) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun i => unitμ (s i)) (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => unitμ (Function.update s w Set.univ i)) (Finset.mem_univ w),
    Function.update_self, measure_univ, hrest]
  ring

/-- **The resampling identity**: `∫ (∫ G(ξ[w ↦ y]) dξ) dy = ∫ G`. -/
theorem integral_integral_update (w : V) {G : (V → ℝ) → ℝ} (hG : Measurable G) {C : ℝ}
    (hb : ∀ ξ, |G ξ| ≤ C) :
    ∫ y, (∫ ξ, G (Function.update ξ w y) ∂(Measure.pi fun _ : V => unitμ)) ∂unitμ
      = ∫ ξ, G ξ ∂(Measure.pi fun _ : V => unitμ) := by
  have hmp := measurePreserving_update (V := V) w
  have hint : Integrable (fun p : (V → ℝ) × ℝ => G (Function.update p.1 w p.2))
      ((Measure.pi fun _ : V => unitμ).prod unitμ) :=
    integrable_of_abs_le (hG.comp (measurable_update_pair w)) C fun p => hb _
  have step1 : ∫ ξ, G ξ ∂(Measure.pi fun _ : V => unitμ)
      = ∫ p, G (Function.update p.1 w p.2)
          ∂((Measure.pi fun _ : V => unitμ).prod unitμ) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map (measurable_update_pair w).aemeasurable hG.aestronglyMeasurable
  rw [step1, integral_prod_symm _ hint]

omit [DecidableEq V] in
/-- The partial integral `y ↦ ∫ F(ξ, y) dξ` of a jointly measurable function is measurable. -/
theorem measurable_integral_left {F : (V → ℝ) × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun y => ∫ ξ, F (ξ, y) ∂(Measure.pi fun _ : V => unitμ)) :=
  (hF.stronglyMeasurable.integral_prod_left' (μ := Measure.pi fun _ : V => unitμ)).measurable

omit [DecidableEq V] in
/-- **The one-coordinate marginal.** -/
theorem integral_comp_eval (w : V) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f unitμ) :
    ∫ ξ, f (ξ w) ∂(Measure.pi fun _ : V => unitμ) = ∫ y, f y ∂unitμ := by
  have hmp := measurePreserving_eval (μ := fun _ : V => unitμ) w
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ) (φ := Function.eval w)
    (measurable_pi_apply w).aemeasurable (f := f) (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

omit [DecidableEq V] in
/-- Almost everywhere statements transport along a coordinate. -/
theorem ae_comp_eval (w : V) {p : ℝ → Prop} (h : ∀ᵐ y ∂unitμ, p y) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), p (ξ w) :=
  (measurePreserving_eval (μ := fun _ : V => unitμ) w).quasiMeasurePreserving.ae h

/-- **The two-coordinate marginal**: distinct coordinates are independent. -/
theorem integral_eval_mul_eval {a b : V} (hab : a ≠ b) {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f unitμ) (hg : AEStronglyMeasurable g unitμ) :
    ∫ ξ, f (ξ a) * g (ξ b) ∂(Measure.pi fun _ : V => unitμ)
      = (∫ y, f y ∂unitμ) * ∫ y, g y ∂unitμ := by
  have hmp := measurePreserving_pair (V := V) hab
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1 * g z.2) (unitμ.prod unitμ) :=
    (hf.comp_fst).mul hg.comp_snd
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun ξ : V → ℝ => (ξ a, ξ b)) hmp.measurable.aemeasurable
    (f := fun z : ℝ × ℝ => f z.1 * g z.2) (by rw [hmp.map_eq]; exact hm)
  rw [hmp.map_eq] at h
  rw [← integral_prod_mul]
  exact h.symm

/-- A lower bound `ω ≤ W` almost everywhere holds on every edge, for almost every vertex
assignment. -/
theorem ae_forall_edge_ge (W : Graphon) {ω : ℝ} (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ∀ a b : V, a ≠ b → ω ≤ W.toFun (ξ a) (ξ b) := by
  have h : ∀ a b : V, ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), a ≠ b → ω ≤ W.toFun (ξ a) (ξ b) := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h => absurd hab h
    · have hpe := (measurePreserving_pair (V := V) hab).quasiMeasurePreserving.ae hWω
      filter_upwards [hpe] with ξ hξ _
      exact hξ
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro b
  exact h a b

end UpperTailMultipodality
