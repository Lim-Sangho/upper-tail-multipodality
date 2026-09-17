import UpperTailMultipodality.FixedDensities.Defs

/-!
# Kernels, graphons and the derivative kernel: measure-theoretic facts

Helpers for `sec:fixed-densities`:

* integrability of bounded kernels and of their products with the derivative kernel;
* `t(H,·)`, `e` and `I_p` of kernels depend only on the almost-everywhere class;
* a kernel with values in `[0,1]` almost everywhere agrees almost everywhere with a graphon;
* the derivative kernel `𝒟_W` is measurable and symmetric.
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

/-- **`t(H,·)` on kernels depends only on the almost-everywhere class.** -/
theorem kernel_tDensity_congr_ae (H : SimpleGraph V) [DecidableRel H.Adj] {K L : Kernel}
    (hae : ∀ᵐ z ∂gμ, K.toFun z.1 z.2 = L.toFun z.1 z.2) :
    K.tDensity H = L.tDensity H := by
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      edgeVal K.toFun K.symm' x e = edgeVal L.toFun L.symm' x e := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hpe := (measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae_eq hae
    filter_upwards [hpe] with x hx
    exact hx
  have hall := (Filter.eventually_all_finset _).mpr hedge
  unfold Kernel.tDensity
  exact integral_congr_ae (hall.mono fun x hx => Finset.prod_congr rfl fun e he => hx e he)

/-- `t(H,·)` of two kernels with the same values. -/
theorem kernel_tDensity_congr (H : SimpleGraph V) [DecidableRel H.Adj] {K L : Kernel}
    (h : ∀ x y, K.toFun x y = L.toFun x y) : K.tDensity H = L.tDensity H :=
  kernel_tDensity_congr_ae H (ae_of_all _ fun z => h z.1 z.2)

/-- `t(H,·)` of graphons depends only on the almost-everywhere class. -/
theorem graphon_tDensity_congr_ae (H : SimpleGraph V) [DecidableRel H.Adj] {W W' : Graphon}
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) : W.tDensity H = W'.tDensity H :=
  kernel_tDensity_congr_ae H (K := Kernel.ofGraphon W) (L := Kernel.ofGraphon W') hae

/-- `I_p` of graphons depends only on the almost-everywhere class. -/
theorem graphon_Ip_congr_ae {W W' : Graphon} (p : ℝ)
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) : W.Ip p = W'.Ip p := by
  unfold Graphon.Ip
  exact integral_congr_ae (hae.mono fun z hz => by simp only [hz])

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

/-- The derivative kernel is jointly measurable. -/
theorem measurable_derivKernel (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) :
    Measurable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2) := by
  have hpin : ∀ a b v : V,
      Measurable (fun p : (ℝ × ℝ) × (V → ℝ) => pin p.2 a b p.1.1 p.1.2 v) := by
    intro a b v
    by_cases hvb : v = b
    · subst hvb; simp only [pin, Function.update_self]; fun_prop
    · by_cases hva : v = a
      · subst hva; simp only [pin, Function.update_of_ne hvb, Function.update_self]; fun_prop
      · simp only [pin, Function.update_of_ne hvb, Function.update_of_ne hva]; fun_prop
  have hK : ∀ a b : V, Measurable (fun z : ℝ × ℝ => edgeRemovedDensity H W a b z.1 z.2) := by
    intro a b
    have hF : Measurable (fun p : (ℝ × ℝ) × (V → ℝ) =>
        ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin p.2 a b p.1.1 p.1.2) e) := by
      refine Finset.measurable_prod _ (fun e _ => ?_)
      induction e using Sym2.ind with
      | _ c d =>
        show Measurable (fun p : (ℝ × ℝ) × (V → ℝ) =>
          W.toFun (pin p.2 a b p.1.1 p.1.2 c) (pin p.2 a b p.1.1 p.1.2 d))
        exact W.measurable_uncurry.comp ((hpin a b c).prodMk (hpin a b d))
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := Measure.pi fun _ => unitμ)).measurable
  unfold derivKernel
  refine Measurable.const_mul (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun b _ => ?_) _
  by_cases h : H.Adj a b
  · simp only [if_pos h]; exact hK a b
  · simp only [if_neg h]; exact measurable_const

/-- `K_{ab,W}(y,x) = K_{ba,W}(x,y)`. -/
theorem edgeRemovedDensity_swap (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {a b : V}
    (hab : a ≠ b) (x y : ℝ) :
    edgeRemovedDensity H W a b y x = edgeRemovedDensity H W b a x y := by
  unfold edgeRemovedDensity pin
  rw [Sym2.eq_swap]
  congr 1
  funext ξ
  rw [Function.update_comm hab]

/-- The derivative kernel is symmetric. -/
theorem derivKernel_symm (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (x y : ℝ) :
    derivKernel H W x y = derivKernel H W y x := by
  unfold derivKernel
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : H.Adj b a
  · rw [if_pos h, if_pos h.symm, edgeRemovedDensity_swap H W h.symm.ne]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- `|𝒟_W| ≤ m`. -/
theorem abs_derivKernel_le (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (x y : ℝ) :
    |derivKernel H W x y| ≤ H.edgeFinset.card := by
  have h := derivKernel_mem_Icc H W x y
  rw [abs_of_nonneg h.1]; exact h.2

/-- The product of the derivative kernel with a bounded kernel is integrable. -/
theorem integrable_derivKernel_mul (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (K : Kernel) :
    Integrable (fun z : ℝ × ℝ => derivKernel H W z.1 z.2 * K.toFun z.1 z.2) gμ := by
  obtain ⟨C, hC0, hC⟩ := kernel_bound K
  refine integrable_of_abs_le ((measurable_derivKernel H W).mul K.meas')
    (H.edgeFinset.card * C) fun z => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_derivKernel_le H W _ _) (hC _ _) (abs_nonneg _) (by positivity)

end FixedDensities

end UpperTailMultipodality
