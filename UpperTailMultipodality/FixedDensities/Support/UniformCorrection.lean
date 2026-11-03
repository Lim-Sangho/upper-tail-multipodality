import UpperTailMultipodality.FixedDensities.Support.Degenerate
import UpperTailMultipodality.FixedDensities.Support.InteriorAux

/-!
# A uniformly bounded upward correction along a sequence of minimizers (`lem:uniform-density-restoration`)

The proof of `thm:fixed-densities` by contradiction bounds the left difference quotients of
`Ψ_ε` at an interior `τ`, contradicting the infinite left slope of `lem:degenerate-slope`.
This file supplies that bound, which is `lem:uniform-density-restoration` together with the use made of
it in the proof of `thm:fixed-densities`: given minimizers `W_n` of `eq:fixed-problem` at
densities `τ_n ↑ τ` which converge in `L¹` to a graphon `W_*` satisfying
`def:constraint-qualification`, the values `Ψ_ε(τ)` and `Ψ_ε(τ_n)` differ by at most
`C(τ - τ_n)` for a constant `C` independent of `n`.

The argument replaces the two-variable Newton iteration of the paper by a
one-variable intermediate value argument.  A single direction `V₀`, supported in the window
`Ω_η(W_*)` of `def:constraint-qualification` and with vanishing mean, is cut down to the
window of `W_n` and recentred; moving `W_n` along the resulting direction `d_n` preserves the
edge density exactly, raises `t(H,·)` at a rate bounded below uniformly in `n`, and costs a
bounded multiple of the step length because the moving values stay inside a fixed compact
subinterval of `(0,1)`.

Contents:

* `abs_prod_sub_prod_le` — `|∏x - ∏y| ≤ ∑|xᵢ - yᵢ|` for factors bounded by `1`;
* `windowSet`, `restrictKernel` — the window `Ω_δ(W) = {δ < W < 1-δ}` and the restriction of a
  kernel to a symmetric measurable set;
* `abs_integral_derivKernel_mul_sub_le` — `K ↦ 𝒟_K` is Lipschitz in `L¹`, with a constant
  depending only on the number of edges of `H`;
* `exists_Jp_lipschitz_window` — `J_ε` is Lipschitz on a window, which bounds the entropy cost
  of the correction;
* `exists_uniform_direction` — the directions `d_n` (Steps 1–3 of the argument);
* `fixedValue_le_of_direction` — one intermediate value step (Steps 4–6);
* `exists_uniform_upward_correction` — the bound itself.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Elementary estimates -/

/-- `|∫ f| ≤ C` on a probability space, from a pointwise bound on `|f|`. -/
theorem abs_integral_le_of_forall_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {C : ℝ} (h : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  calc |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂μ := integral_mono hf.abs (integrable_const C) h
    _ = C := by simp

/-- **Products of factors bounded by `1` differ by at most the sum of the differences.** -/
theorem abs_prod_sub_prod_le {ι : Type*} (x y : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, |x i| ≤ 1) → (∀ i ∈ s, |y i| ≤ 1) →
      |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.cons_induction with
  | empty => intro _ _; simp
  | cons a s ha ih =>
    intro hx hy
    have hxa : |x a| ≤ 1 := hx a (by simp)
    have hya : |y a| ≤ 1 := hy a (by simp)
    have hxs : ∀ i ∈ s, |x i| ≤ 1 := fun i hi => hx i (by simp [hi])
    have hys : ∀ i ∈ s, |y i| ≤ 1 := fun i hi => hy i (by simp [hi])
    have hPx : |∏ i ∈ s, x i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) hxs
    rw [Finset.prod_cons, Finset.prod_cons, Finset.sum_cons,
      show x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i
        = (x a - y a) * (∏ i ∈ s, x i) + y a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i) by ring]
    calc |(x a - y a) * (∏ i ∈ s, x i) + y a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i)|
        ≤ |(x a - y a) * (∏ i ∈ s, x i)| + |y a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i)| :=
          abs_add_le _ _
      _ = |x a - y a| * |∏ i ∈ s, x i| + |y a| * |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| := by
          rw [abs_mul, abs_mul]
      _ ≤ |x a - y a| * 1 + 1 * ∑ i ∈ s, |x i - y i| :=
          add_le_add (mul_le_mul_of_nonneg_left hPx (abs_nonneg _))
            (mul_le_mul hya (ih hxs hys) (abs_nonneg _) zero_le_one)
      _ = |x a - y a| + ∑ i ∈ s, |x i - y i| := by ring

/-! ### Kernel integrals -/

/-- `∫∫ (K + L) = ∫∫ K + ∫∫ L`. -/
theorem integral_kernel_add (K L : Kernel) :
    ∫ z, (K + L).toFun z.1 z.2 ∂gμ
      = (∫ z, K.toFun z.1 z.2 ∂gμ) + ∫ z, L.toFun z.1 z.2 ∂gμ := by
  simp only [Kernel.add_apply]
  exact integral_add (kernel_integrable K) (kernel_integrable L)

/-- `∫∫ (rK) = r ∫∫ K`. -/
theorem integral_kernel_smul (r : ℝ) (K : Kernel) :
    ∫ z, (r • K).toFun z.1 z.2 ∂gμ = r * ∫ z, K.toFun z.1 z.2 ∂gμ := by
  simp only [Kernel.smul_apply]
  exact integral_const_mul r _

/-- `∫∫ 𝒟_W (K + L) = ∫∫ 𝒟_W K + ∫∫ 𝒟_W L`. -/
theorem integral_derivKernel_mul_add (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (K L : Kernel) :
    ∫ z, derivKernel H W z.1 z.2 * (K + L).toFun z.1 z.2 ∂gμ
      = (∫ z, derivKernel H W z.1 z.2 * K.toFun z.1 z.2 ∂gμ)
        + ∫ z, derivKernel H W z.1 z.2 * L.toFun z.1 z.2 ∂gμ := by
  simp only [Kernel.add_apply, mul_add]
  exact integral_add (integrable_derivKernel_mul H W K) (integrable_derivKernel_mul H W L)

/-- `∫∫ 𝒟_W (rK) = r ∫∫ 𝒟_W K`. -/
theorem integral_derivKernel_mul_smul (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (r : ℝ) (K : Kernel) :
    ∫ z, derivKernel H W z.1 z.2 * (r • K).toFun z.1 z.2 ∂gμ
      = r * ∫ z, derivKernel H W z.1 z.2 * K.toFun z.1 z.2 ∂gμ := by
  simp only [Kernel.smul_apply,
    show ∀ z : ℝ × ℝ, derivKernel H W z.1 z.2 * (r * K.toFun z.1 z.2)
      = r * (derivKernel H W z.1 z.2 * K.toFun z.1 z.2) from fun z => by ring]
  exact integral_const_mul r _

/-- **Integrals over an edge pair.**  For distinct coordinates `a ≠ b`, integrating a bounded
measurable function of `(ξ_a, ξ_b)` over the product measure is integrating it over `gμ`. -/
theorem integral_pair_eq {a b : V} (hab : a ≠ b) {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    ∫ ξ : V → ℝ, g (ξ a, ξ b) ∂(Measure.pi fun _ : V => unitμ) = ∫ z, g z ∂gμ := by
  have hmp := measurePreserving_pair (V := V) hab
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun ξ : V → ℝ => (ξ a, ξ b)) hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

/-! ### The derivative kernel is Lipschitz -/

/-- The absolute difference of two bounded kernels is integrable. -/
private theorem integrable_abs_sub (K L : Kernel) :
    Integrable (fun z : ℝ × ℝ => |K.toFun z.1 z.2 - L.toFun z.1 z.2|) gμ :=
  ((kernel_integrable K).sub (kernel_integrable L)).abs

/-- **`𝒟_W` is Lipschitz in the direction.**  `|∫∫ 𝒟_W K - ∫∫ 𝒟_W L| ≤ m ‖K - L‖₁`. -/
theorem abs_integral_derivKernel_mul_sub_kernel_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) (K L : Kernel) :
    |(∫ z, derivKernel H W z.1 z.2 * K.toFun z.1 z.2 ∂gμ)
        - ∫ z, derivKernel H W z.1 z.2 * L.toFun z.1 z.2 ∂gμ|
      ≤ (H.edgeFinset.card : ℝ) * ∫ z, |K.toFun z.1 z.2 - L.toFun z.1 z.2| ∂gμ := by
  rw [← integral_sub (integrable_derivKernel_mul H W K) (integrable_derivKernel_mul H W L)]
  calc |∫ z, (derivKernel H W z.1 z.2 * K.toFun z.1 z.2
              - derivKernel H W z.1 z.2 * L.toFun z.1 z.2) ∂gμ|
      ≤ ∫ z, |derivKernel H W z.1 z.2 * K.toFun z.1 z.2
              - derivKernel H W z.1 z.2 * L.toFun z.1 z.2| ∂gμ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (H.edgeFinset.card : ℝ) * |K.toFun z.1 z.2 - L.toFun z.1 z.2| ∂gμ := by
        refine integral_mono
          ((integrable_derivKernel_mul H W K).sub (integrable_derivKernel_mul H W L)).abs
          ((integrable_abs_sub K L).const_mul _) fun z => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_derivKernel_le H W _ _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- **`W ↦ 𝒟_W` is Lipschitz in `L¹`.**  For a kernel `U` bounded by `B`,
`|∫∫ 𝒟_W U - ∫∫ 𝒟_{W'} U| ≤ m² B ‖W - W'‖₁`. -/
theorem abs_integral_derivKernel_mul_sub_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (W W' : Graphon) (U : Kernel) {B : ℝ} (hB : ∀ x y, |U.toFun x y| ≤ B) :
    |(∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ)
        - ∫ z, derivKernel H W' z.1 z.2 * U.toFun z.1 z.2 ∂gμ|
      ≤ (H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * B
          * ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = ∫ z, |W.toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ integral_nonneg fun z => abs_nonneg _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  -- the `L¹` distance of two edge factors is `d`
  have hedge : ∀ e ∈ H.edgeFinset,
      ∫ ξ : V → ℝ, |edgeVal W.toFun W.symm' ξ e - edgeVal W'.toFun W'.symm' ξ e|
        ∂(Measure.pi fun _ : V => unitμ) = d := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rw [hd]
    exact integral_pair_eq hadj.ne
      ((W.measurable_uncurry.sub W'.measurable_uncurry).abs)
  -- the per-edge estimate
  have hterm : ∀ e ∈ H.edgeFinset,
      |(∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ))
          - ∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W'.toFun W'.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ)|
        ≤ B * ((H.edgeFinset.card : ℝ) * d) := by
    intro e he
    have hi1 := ((isBddMeas_edgeVal U e).mul (isBddMeas_prod_edgeVal W
      (H.edgeFinset.erase e))).integrable (μ := Measure.pi fun _ : V => unitμ)
    have hi2 := ((isBddMeas_edgeVal U e).mul (isBddMeas_prod_edgeVal W'
      (H.edgeFinset.erase e))).integrable (μ := Measure.pi fun _ : V => unitμ)
    have habs : ∀ e' : Sym2 V, Integrable
        (fun ξ : V → ℝ => |edgeVal W.toFun W.symm' ξ e' - edgeVal W'.toFun W'.symm' ξ e'|)
        (Measure.pi fun _ : V => unitμ) := fun e' =>
      (((IsBddMeas.of_mem_Icc (measurable_edgeVal W.symm' W.meas' e')
          fun x => edgeVal_mem_Icc W x e').sub
        (IsBddMeas.of_mem_Icc (measurable_edgeVal W'.symm' W'.meas' e')
          fun x => edgeVal_mem_Icc W' x e')).abs).integrable
    rw [← integral_sub hi1 hi2]
    calc |∫ ξ, (edgeVal U.toFun U.symm' ξ e
              * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
            - edgeVal U.toFun U.symm' ξ e
              * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W'.toFun W'.symm' ξ e')
            ∂(Measure.pi fun _ : V => unitμ)|
        ≤ ∫ ξ, |edgeVal U.toFun U.symm' ξ e
                * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
              - edgeVal U.toFun U.symm' ξ e
                * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W'.toFun W'.symm' ξ e'|
              ∂(Measure.pi fun _ : V => unitμ) := abs_integral_le_integral_abs
      _ ≤ ∫ ξ, B * ∑ e' ∈ H.edgeFinset.erase e,
              |edgeVal W.toFun W.symm' ξ e' - edgeVal W'.toFun W'.symm' ξ e'|
              ∂(Measure.pi fun _ : V => unitμ) := by
          refine integral_mono (hi1.sub hi2).abs
            ((integrable_finsetSum _ fun e' _ => habs e').const_mul B) fun ξ => ?_
          rw [← mul_sub, abs_mul]
          refine mul_le_mul (by
            induction e using Sym2.ind with
            | _ a b => exact hB (ξ a) (ξ b)) ?_ (abs_nonneg _) hB0
          exact abs_prod_sub_prod_le _ _ _
            (fun e' _ => by
              rw [abs_of_nonneg (edgeVal_mem_Icc W ξ e').1]; exact (edgeVal_mem_Icc W ξ e').2)
            (fun e' _ => by
              rw [abs_of_nonneg (edgeVal_mem_Icc W' ξ e').1]; exact (edgeVal_mem_Icc W' ξ e').2)
      _ = B * ∑ e' ∈ H.edgeFinset.erase e, d := by
          rw [integral_const_mul, integral_finsetSum _ fun e' _ => habs e']
          refine congrArg _ (Finset.sum_congr rfl fun e' he' => ?_)
          exact hedge e' (Finset.mem_of_mem_erase he')
      _ ≤ B * ((H.edgeFinset.card : ℝ) * d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hd0) hB0
          exact Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset _ _))
  rw [integral_derivKernel_mul, integral_derivKernel_mul, ← Finset.sum_sub_distrib, ← hd]
  calc |∑ e ∈ H.edgeFinset, ((∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ))
          - ∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W'.toFun W'.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ))|
      ≤ ∑ e ∈ H.edgeFinset, |(∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ))
          - ∫ ξ, edgeVal U.toFun U.symm' ξ e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W'.toFun W'.symm' ξ e'
            ∂(Measure.pi fun _ : V => unitμ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.edgeFinset, B * ((H.edgeFinset.card : ℝ) * d) := Finset.sum_le_sum hterm
    _ = (H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * B * d := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### Windows and restricted kernels -/

/-- The window `Ω_δ(W) = {δ < W < 1 - δ}`, as a subset of `ℝ²`. -/
def windowSet (W : Graphon) (δ : ℝ) : Set (ℝ × ℝ) :=
  {z | δ < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - δ}

/-- Membership in the window. -/
theorem mem_windowSet {W : Graphon} {δ : ℝ} {z : ℝ × ℝ} :
    z ∈ windowSet W δ ↔ δ < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - δ := Iff.rfl

/-- The window is measurable. -/
theorem measurableSet_windowSet (W : Graphon) (δ : ℝ) : MeasurableSet (windowSet W δ) :=
  (measurableSet_lt measurable_const W.measurable_uncurry).inter
    (measurableSet_lt W.measurable_uncurry measurable_const)

/-- The window is symmetric. -/
theorem windowSet_symm (W : Graphon) (δ : ℝ) {x y : ℝ} (h : (x, y) ∈ windowSet W δ) :
    (y, x) ∈ windowSet W δ := by
  rw [mem_windowSet] at h ⊢
  rwa [W.symm' y x]

/-- The restriction `U · 1_E` of a kernel to a symmetric measurable set. -/
noncomputable def restrictKernel (U : Kernel) (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) : Kernel where
  toFun x y := E.indicator (fun z => U.toFun z.1 z.2) (x, y)
  symm' x y := by
    by_cases h : (x, y) ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hsymm x y h)]
      exact U.symm' x y
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hsymm y x h'))]
  meas' := U.meas'.indicator hE
  bdd' := by
    obtain ⟨C, hC0, hC⟩ := kernel_bound U
    refine ⟨C, fun x y => ?_⟩
    by_cases h : (x, y) ∈ E
    · rw [Set.indicator_of_mem h]; exact hC x y
    · rw [Set.indicator_of_notMem h, abs_zero]; exact hC0

/-- The value of the restricted kernel. -/
theorem restrictKernel_apply (U : Kernel) (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) (x y : ℝ) :
    (restrictKernel U E hE hsymm).toFun x y = E.indicator (fun z => U.toFun z.1 z.2) (x, y) := rfl

/-- The restricted kernel agrees with `U` on `E`. -/
theorem restrictKernel_of_mem {U : Kernel} {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) {x y : ℝ} (h : (x, y) ∈ E) :
    (restrictKernel U E hE hsymm).toFun x y = U.toFun x y := by
  rw [restrictKernel_apply, Set.indicator_of_mem h]

/-- The restricted kernel vanishes off `E`. -/
theorem restrictKernel_of_notMem {U : Kernel} {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (hsymm : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) {x y : ℝ} (h : (x, y) ∉ E) :
    (restrictKernel U E hE hsymm).toFun x y = 0 := by
  rw [restrictKernel_apply, Set.indicator_of_notMem h]

/-! ### The cost of a small move inside a window -/

/-- **`J_ε` is Lipschitz on the window `[η/4, 1-η/4]`.**  Moving a value in `Ω_{η/2}` by at most
`η/4` costs at most `Λ` times the size of the move; this is the entropy cost estimate used in
`thm:fixed-densities`. -/
theorem exists_Jp_lipschitz_window {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ w ∈ Ioo (η / 2) (1 - η / 2), ∀ h : ℝ, |h| ≤ η / 4 →
      Jp ε (w + h) - Jp ε w ≤ Λ * |h| := by
  obtain ⟨L, hL0, hL⟩ := Jp'_bdd_box (show (0:ℝ) < η / 4 by linarith) hε0 hε1
  obtain ⟨M, hM⟩ : ∃ M, M = 1 / (η / 2 / 2 * (1 - η / 2 / 2)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact one_div_nonneg.mpr (mul_pos (by linarith : (0:ℝ) < η / 2 / 2)
      (by linarith : (0:ℝ) < 1 - η / 2 / 2)).le
  refine ⟨L + M * (η / 4), add_nonneg hL0 (mul_nonneg hM0 (by linarith)),
    fun w hw h hh => ?_⟩
  have hLbox : ∀ u ∈ Icc (η / 2 / 2) (1 - η / 2 / 2), |Jp' ε u| ≤ L := fun u hu =>
    hL u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hkey := (Jp_sub_le_of_mem_Ioo hε0 hε1 (show (0:ℝ) < η / 2 by linarith) hLbox hw
    (le_refl |h|) (show |h| ≤ η / 2 / 2 by linarith)).2
  rw [← hM] at hkey
  have hsq : M * |h| ^ 2 ≤ M * (η / 4) * |h| := by
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hM0) (abs_nonneg _)
  calc Jp ε (w + h) - Jp ε w ≤ L * |h| + M * |h| ^ 2 := hkey
    _ ≤ L * |h| + M * (η / 4) * |h| := by linarith
    _ = (L + M * (η / 4)) * |h| := by ring

/-! ### The uniformly good directions -/

/-- `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := congrArg abs (sub_eq_add_neg a b)
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- **Steps 1–3 of the correction.**  If the graphons `W_n` converge in `L¹` to a graphon `W_*`
satisfying `def:constraint-qualification` at level `η`, then there are directions `d_n`,
supported in the window `Ω_{η/2}(W_n)`, uniformly bounded, of vanishing mean, and along which
`t(H,·)` increases at a rate bounded below uniformly in `n`.

The direction is obtained from the two kernels `U₁, U₂` of `def:constraint-qualification` by
eliminating the edge-density constraint, cutting the result down to the window of `W_n` and
recentring it by a multiple of the indicator of that window. -/
theorem exists_uniform_direction (H : SimpleGraph V) [DecidableRel H.Adj]
    (Wn : ℕ → Graphon) (Wstar : Graphon)
    (hL1 : Tendsto (fun n => ∫ z, |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2| ∂gμ)
      atTop (𝓝 0))
    (hcq : ConstraintQualification H Wstar) :
    ∃ η B c : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 < B ∧ 0 < c ∧ ∃ D : ℕ → Kernel, ∀ᶠ n in atTop,
      (∀ x y, (D n).toFun x y ≠ 0 →
          η / 2 < (Wn n).toFun x y ∧ (Wn n).toFun x y < 1 - η / 2) ∧
      (∀ x y, |(D n).toFun x y| ≤ B) ∧
      (∫ z, (D n).toFun z.1 z.2 ∂gμ) = 0 ∧
      c ≤ ∫ z, derivKernel H (Wn n) z.1 z.2 * (D n).toFun z.1 z.2 ∂gμ := by
  classical
  obtain ⟨η₀, hη₀, U₁, U₂, hU₁, hU₂, hdet⟩ := hcq
  obtain ⟨η, hηdef⟩ : ∃ η, η = min η₀ (1 / 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hη₀ (by norm_num)
  have hη1 : η ≤ 1 / 2 := hηdef ▸ min_le_right _ _
  have hηη₀ : η ≤ η₀ := hηdef ▸ min_le_left _ _
  have hshrink : ∀ U : Kernel, SupportedIn Wstar η₀ U → SupportedIn Wstar η U := by
    intro U hU x y hxy
    obtain ⟨h1, h2⟩ := hU x y hxy
    exact ⟨lt_of_le_of_lt hηη₀ h1, lt_of_lt_of_le h2 (by linarith)⟩
  -- Step 1: a single direction with vanishing mean and positive first variation
  obtain ⟨V₀, hV₀int, hV₀supp, hV₀c⟩ :
      ∃ V₀ : Kernel, (∫ z, V₀.toFun z.1 z.2 ∂gμ) = 0 ∧ SupportedIn Wstar η V₀ ∧
        0 < ∫ z, derivKernel H Wstar z.1 z.2 * V₀.toFun z.1 z.2 ∂gμ := by
    obtain ⟨a₁, ha₁⟩ : ∃ a, a = ∫ z, U₁.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
    obtain ⟨a₂, ha₂⟩ : ∃ a, a = ∫ z, U₂.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
    obtain ⟨b₁, hb₁⟩ : ∃ b, b = ∫ z, derivKernel H Wstar z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ :=
      ⟨_, rfl⟩
    obtain ⟨b₂, hb₂⟩ : ∃ b, b = ∫ z, derivKernel H Wstar z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ :=
      ⟨_, rfl⟩
    obtain ⟨Vc, hVc⟩ : ∃ Vc : Kernel, Vc = a₂ • U₁ + (-a₁) • U₂ := ⟨_, rfl⟩
    have hdetv : cqDet H Wstar U₁ U₂ = a₁ * b₂ - a₂ * b₁ := by
      simp only [cqDet, ← ha₁, ← ha₂, ← hb₁, ← hb₂]
    have hVcsupp : SupportedIn Wstar η Vc := by
      intro x y hxy
      rw [hVc] at hxy
      simp only [Kernel.add_apply, Kernel.smul_apply] at hxy
      by_cases h1 : U₁.toFun x y = 0
      · by_cases h2 : U₂.toFun x y = 0
        · exact absurd (by rw [h1, h2]; ring) hxy
        · exact hshrink U₂ hU₂ x y h2
      · exact hshrink U₁ hU₁ x y h1
    have hVcint : ∫ z, Vc.toFun z.1 z.2 ∂gμ = 0 := by
      rw [hVc, integral_kernel_add, integral_kernel_smul, integral_kernel_smul, ← ha₁, ← ha₂]
      ring
    have hVcd : ∫ z, derivKernel H Wstar z.1 z.2 * Vc.toFun z.1 z.2 ∂gμ = a₂ * b₁ - a₁ * b₂ := by
      rw [hVc, integral_derivKernel_mul_add, integral_derivKernel_mul_smul,
        integral_derivKernel_mul_smul, ← hb₁, ← hb₂]
      ring
    rw [hdetv] at hdet
    rcases lt_or_gt_of_ne hdet with hlt | hgt
    · exact ⟨Vc, hVcint, hVcsupp, by rw [hVcd]; linarith⟩
    · refine ⟨(-1 : ℝ) • Vc, ?_, ?_, ?_⟩
      · rw [integral_kernel_smul, hVcint]; ring
      · intro x y hxy
        refine hVcsupp x y fun h => hxy ?_
        simp only [Kernel.smul_apply, h]
        ring
      · rw [integral_derivKernel_mul_smul, hVcd]; linarith
  obtain ⟨Cv, hCv0, hCv⟩ := kernel_bound V₀
  obtain ⟨c₀, hc₀⟩ : ∃ c, c = ∫ z, derivKernel H Wstar z.1 z.2 * V₀.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := hc₀ ▸ hV₀c
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (H.edgeFinset.card : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  -- Step 2: the bad sets and the windows
  obtain ⟨L1, hL1def⟩ : ∃ L1 : ℕ → ℝ,
      L1 = fun n => ∫ z, |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2| ∂gμ := ⟨_, rfl⟩
  have hL1tend : Tendsto L1 atTop (𝓝 0) := hL1def ▸ hL1
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (ℝ × ℝ), A = fun n =>
      {z : ℝ × ℝ | η / 2 ≤ |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2|} := ⟨_, rfl⟩
  have hAm : ∀ n, MeasurableSet (A n) := by
    intro n
    rw [hA]
    exact measurableSet_le measurable_const
      (((Wn n).measurable_uncurry.sub Wstar.measurable_uncurry).abs)
  have hAtend : Tendsto (fun n => gμ.real (A n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
      (by simpa using hL1tend.const_mul (2 / η))
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (μ := gμ) (f := fun z : ℝ × ℝ => |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2|)
      (ae_of_all _ fun z => abs_nonneg _)
      (integrable_abs_sub (Kernel.ofGraphon (Wn n)) (Kernel.ofGraphon Wstar)) (η / 2)
    rw [hA, hL1def]
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    nlinarith [hmk]
  obtain ⟨win, hwin⟩ : ∃ win : ℕ → Set (ℝ × ℝ), win = fun n => windowSet (Wn n) (η / 2) :=
    ⟨_, rfl⟩
  have hwinm : ∀ n, MeasurableSet (win n) := fun n => by
    rw [hwin]; exact measurableSet_windowSet _ _
  have hwinsymm : ∀ n, ∀ x y : ℝ, (x, y) ∈ win n → (y, x) ∈ win n := fun n x y h => by
    rw [hwin] at h ⊢; exact windowSet_symm _ _ h
  obtain ⟨S, hS⟩ : ∃ S, S = windowSet Wstar η := ⟨_, rfl⟩
  have hincl : ∀ n, ∀ z : ℝ × ℝ, z ∈ S → z ∉ A n → z ∈ win n := by
    intro n z hzS hzA
    rw [hS, mem_windowSet] at hzS
    rw [hA] at hzA
    have hlt : |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2| < η / 2 := not_le.mp hzA
    have := abs_lt.mp hlt
    rw [hwin, mem_windowSet]
    constructor <;> linarith [hzS.1, hzS.2, this.1, this.2]
  have hVS : ∀ z : ℝ × ℝ, V₀.toFun z.1 z.2 ≠ 0 → z ∈ S := by
    intro z hz
    rw [hS, mem_windowSet]
    exact hV₀supp z.1 z.2 hz
  -- the window of `W_*` has positive measure
  have hSne : gμ S ≠ 0 := by
    intro h0
    have hae : ∀ᵐ z ∂gμ, V₀.toFun z.1 z.2 = 0 := by
      rw [ae_iff]
      exact measure_mono_null (fun z hz => hVS z hz) h0
    have hzero : ∫ z, derivKernel H Wstar z.1 z.2 * V₀.toFun z.1 z.2 ∂gμ = 0 := by
      rw [integral_congr_ae (hae.mono fun z hz => by rw [hz, mul_zero])]
      simp
    rw [hzero] at hV₀c
    exact lt_irrefl _ hV₀c
  have hSpos : 0 < gμ.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hSne (measure_ne_top _ _)
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ = gμ.real S / 2 := ⟨_, rfl⟩
  have hq₀0 : 0 < q₀ := by rw [hq₀]; linarith
  have hwinge : ∀ n, gμ.real S - gμ.real (A n) ≤ gμ.real (win n) := by
    intro n
    have h1 : gμ.real (S \ A n) ≤ gμ.real (win n) :=
      measureReal_mono (fun z hz => hincl n z hz.1 hz.2) (measure_ne_top _ _)
    have h2 : gμ.real S ≤ gμ.real (S \ A n) + gμ.real (A n) := by
      calc gμ.real S ≤ gμ.real ((S \ A n) ∪ A n) := by
            refine measureReal_mono (fun z hz => ?_) (measure_ne_top _ _)
            by_cases h : z ∈ A n
            · exact Or.inr h
            · exact Or.inl ⟨hz, h⟩
        _ ≤ gμ.real (S \ A n) + gμ.real (A n) := measureReal_union_le _ _
    linarith
  -- the cut and indicator kernels
  obtain ⟨Dcut, hDcut⟩ : ∃ Dcut : ℕ → Kernel,
      Dcut = fun n => restrictKernel V₀ (win n) (hwinm n) (hwinsymm n) := ⟨_, rfl⟩
  obtain ⟨Ind, hInd⟩ : ∃ Ind : ℕ → Kernel,
      Ind = fun n => indicatorKernel (win n) (hwinm n) (hwinsymm n) 1 := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, p = fun n => ∫ z, (Dcut n).toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, q = fun n => gμ.real (win n) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Kernel, D = fun n => Dcut n + (-(p n / q n)) • Ind n := ⟨_, rfl⟩
  have hDcutbd : ∀ n, ∀ x y, |(Dcut n).toFun x y| ≤ Cv := by
    intro n x y
    rw [hDcut]
    by_cases h : (x, y) ∈ win n
    · rw [restrictKernel_of_mem]; exacts [hCv x y, h]
    · rw [restrictKernel_of_notMem (h := h), abs_zero]; exact hCv0
  have hDcutsupp : ∀ n, ∀ x y, (Dcut n).toFun x y ≠ 0 → (x, y) ∈ win n := by
    intro n x y hxy
    by_contra h
    rw [hDcut, restrictKernel_of_notMem (h := h)] at hxy
    exact hxy rfl
  have hIndbd : ∀ n, ∀ x y, |(Ind n).toFun x y| ≤ 1 := by
    intro n x y
    rw [hInd, indicatorKernel_apply]
    by_cases h : (x, y) ∈ win n <;> simp [h]
  have hIndsupp : ∀ n, ∀ x y, (Ind n).toFun x y ≠ 0 → (x, y) ∈ win n := by
    intro n x y hxy
    by_contra h
    rw [hInd, indicatorKernel_apply, Set.indicator_of_notMem h] at hxy
    exact hxy rfl
  have hIndint : ∀ n, ∫ z, (Ind n).toFun z.1 z.2 ∂gμ = q n := by
    intro n
    rw [hInd, integral_indicatorKernel, one_mul, hq]
  -- the cut direction is close to `V₀` in `L¹`
  have hcutdiff : ∀ n, ∫ z, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2| ∂gμ
      ≤ 2 * Cv * gμ.real (A n) := by
    intro n
    have hpt : ∀ z : ℝ × ℝ, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2|
        ≤ (A n).indicator (fun _ => 2 * Cv) z := by
      intro z
      by_cases hz : z ∈ A n
      · rw [Set.indicator_of_mem hz]
        calc |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2|
            ≤ |(Dcut n).toFun z.1 z.2| + |V₀.toFun z.1 z.2| := abs_sub_le_add _ _
          _ ≤ Cv + Cv := add_le_add (hDcutbd n _ _) (hCv _ _)
          _ = 2 * Cv := by ring
      · rw [Set.indicator_of_notMem hz]
        have heq : (Dcut n).toFun z.1 z.2 = V₀.toFun z.1 z.2 := by
          by_cases hw : z ∈ win n
          · rw [hDcut]; exact restrictKernel_of_mem _ _ hw
          · have hv : V₀.toFun z.1 z.2 = 0 := by
              by_contra hne
              exact hw (hincl n z (hVS z hne) hz)
            rw [hDcut, restrictKernel_of_notMem (h := hw), hv]
        rw [heq, sub_self, abs_zero]
    calc ∫ z, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2| ∂gμ
        ≤ ∫ z, (A n).indicator (fun _ => 2 * Cv) z ∂gμ :=
          integral_mono (integrable_abs_sub _ _)
            ((integrable_const _).indicator (hAm n)) hpt
      _ = 2 * Cv * gμ.real (A n) := by
          rw [integral_indicator_const _ (hAm n), smul_eq_mul, mul_comm]
  -- `p n → 0`
  have hpabs : ∀ n, |p n| ≤ ∫ z, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2| ∂gμ := by
    intro n
    have h1 : ∫ z, ((Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2) ∂gμ = p n := by
      rw [integral_sub (kernel_integrable _) (kernel_integrable _), hV₀int, sub_zero, hp]
    rw [← h1]
    exact abs_integral_le_integral_abs
  have hptend : Tendsto p atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hAtend.const_mul (2 * Cv))
    rw [Real.norm_eq_abs]
    exact (hpabs n).trans (hcutdiff n)
  -- the eventual bounds
  have habs : Tendsto (fun n => |p n|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.mp hptend
  have e1 : ∀ᶠ n in atTop, gμ.real (A n) < q₀ := hAtend.eventually_lt_const hq₀0
  have e2 : ∀ᶠ n in atTop, |p n| < q₀ := habs.eventually_lt_const hq₀0
  have e3 : ∀ᶠ n in atTop, m * (2 * Cv * gμ.real (A n)) < c₀ / 6 := by
    have ht : Tendsto (fun n => m * (2 * Cv * gμ.real (A n))) atTop (𝓝 0) := by
      simpa using (hAtend.const_mul (2 * Cv)).const_mul m
    exact ht.eventually_lt_const (by linarith)
  have e4 : ∀ᶠ n in atTop, m * m * Cv * L1 n < c₀ / 6 := by
    have ht : Tendsto (fun n => m * m * Cv * L1 n) atTop (𝓝 0) := by
      simpa using hL1tend.const_mul (m * m * Cv)
    exact ht.eventually_lt_const (by linarith)
  have e5 : ∀ᶠ n in atTop, |p n| * (m / q₀) < c₀ / 6 := by
    have ht : Tendsto (fun n => |p n| * (m / q₀)) atTop (𝓝 0) := by
      simpa using habs.mul_const (m / q₀)
    exact ht.eventually_lt_const (by linarith)
  refine ⟨η, Cv + 1, c₀ / 2, hη, hη1, by linarith, by linarith, D, ?_⟩
  filter_upwards [e1, e2, e3, e4, e5] with n h1 h2 h3 h4 h5
  -- the window of `W_n` is large
  have hqn : q₀ ≤ q n := by
    rw [hq]
    have := hwinge n
    rw [hq₀] at h1 ⊢
    linarith
  have hqn0 : 0 < q n := lt_of_lt_of_le hq₀0 hqn
  have hqne : q n ≠ 0 := ne_of_gt hqn0
  have hpn : p n = ∫ z, (Dcut n).toFun z.1 z.2 ∂gμ := by rw [hp]
  have hr : |p n / q n| ≤ |p n| / q₀ := by
    rw [abs_div, abs_of_pos hqn0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hq₀0 hqn
  have hr1 : |p n / q n| ≤ 1 := by
    have h' : |p n| / q₀ ≤ 1 := by
      rw [div_le_one hq₀0]; linarith
    linarith [hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- support
    intro x y hxy
    rw [hD] at hxy
    simp only [Kernel.add_apply, Kernel.smul_apply] at hxy
    have hmem : (x, y) ∈ win n := by
      by_cases hc : (Dcut n).toFun x y = 0
      · by_cases hi : (Ind n).toFun x y = 0
        · exact absurd (by rw [hc, hi]; ring) hxy
        · exact hIndsupp n x y hi
      · exact hDcutsupp n x y hc
    rw [hwin, mem_windowSet] at hmem
    exact hmem
  · -- uniform bound
    intro x y
    rw [hD]
    simp only [Kernel.add_apply, Kernel.smul_apply]
    calc |(Dcut n).toFun x y + -(p n / q n) * (Ind n).toFun x y|
        ≤ |(Dcut n).toFun x y| + |-(p n / q n) * (Ind n).toFun x y| := abs_add_le _ _
      _ ≤ Cv + 1 * 1 := by
          refine add_le_add (hDcutbd n x y) ?_
          rw [abs_mul, abs_neg]
          exact mul_le_mul hr1 (hIndbd n x y) (abs_nonneg _) zero_le_one
      _ = Cv + 1 := by ring
  · -- vanishing mean
    rw [hD, integral_kernel_add, integral_kernel_smul, hIndint, ← hpn]
    field_simp
    ring
  · -- the lower bound on the first variation
    obtain ⟨X, hX⟩ : ∃ X, X = ∫ z, derivKernel H (Wn n) z.1 z.2 * (Dcut n).toFun z.1 z.2 ∂gμ :=
      ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ z, derivKernel H (Wn n) z.1 z.2 * V₀.toFun z.1 z.2 ∂gμ :=
      ⟨_, rfl⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = ∫ z, derivKernel H (Wn n) z.1 z.2 * (Ind n).toFun z.1 z.2 ∂gμ :=
      ⟨_, rfl⟩
    have hsum : ∫ z, derivKernel H (Wn n) z.1 z.2 * (D n).toFun z.1 z.2 ∂gμ
        = X + -(p n / q n) * Y := by
      rw [hX, hYdef, hD, integral_derivKernel_mul_add, integral_derivKernel_mul_smul]
    have hXZ : |X - Z| ≤ m * ∫ z, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2| ∂gμ := by
      rw [hX, hZ, hm]
      exact abs_integral_derivKernel_mul_sub_kernel_le H (Wn n) (Dcut n) V₀
    have hcut : m * (∫ z, |(Dcut n).toFun z.1 z.2 - V₀.toFun z.1 z.2| ∂gμ)
        ≤ m * (2 * Cv * gμ.real (A n)) := mul_le_mul_of_nonneg_left (hcutdiff n) hm0
    have hZc : |Z - c₀| ≤ m * m * Cv * L1 n := by
      rw [hZ, hc₀, hm, hL1def]
      exact abs_integral_derivKernel_mul_sub_le H (Wn n) Wstar V₀ hCv
    have hYbd : |Y| ≤ m := by
      rw [hYdef]
      refine abs_integral_le_of_forall_abs_le (integrable_derivKernel_mul H (Wn n) (Ind n))
        fun z => ?_
      rw [abs_mul, hm]
      calc |derivKernel H (Wn n) z.1 z.2| * |(Ind n).toFun z.1 z.2|
          ≤ (H.edgeFinset.card : ℝ) * 1 :=
            mul_le_mul (abs_derivKernel_le H (Wn n) _ _) (hIndbd n _ _) (abs_nonneg _)
              (by positivity)
        _ = (H.edgeFinset.card : ℝ) := mul_one _
    have hlast : |-(p n / q n) * Y| ≤ |p n| * (m / q₀) := by
      rw [abs_mul, abs_neg]
      calc |p n / q n| * |Y| ≤ (|p n| / q₀) * m :=
            mul_le_mul hr hYbd (abs_nonneg _) (div_nonneg (abs_nonneg _) hq₀0.le)
        _ = |p n| * (m / q₀) := by rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [hsum]
    have h6 := abs_le.mp hXZ
    have h7 := abs_le.mp hZc
    have h8 := abs_le.mp hlast
    linarith [h6.1, h7.1, h8.1]


/-! ### One intermediate value step -/

/-- **Steps 4–6 of the correction.**  Along a direction `D` supported in the window
`Ω_{η/2}(W)`, of vanishing mean and with first variation of `t(H,·)` at least `c > 0`, the
graphons `W + θD` have edge density `e(W)` for every `θ`, and `t(H, W + θD)` grows at rate at
least `c/2` for `θ` in a range controlled by `η`, `B` and `c`.  The intermediate value theorem
therefore reaches the target density `τ` at some `θ ≤ 2(τ - t)/c`, at an entropy cost at most
`Λ B` per unit of `θ` because the moving values stay in `[η/4, 1-η/4]`. -/
theorem fixedValue_le_of_direction (H : SimpleGraph V) [DecidableRel H.Adj] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {η B c Λ : ℝ} (hη : 0 < η) (hB : 0 < B) (hc : 0 < c)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ w ∈ Ioo (η / 2) (1 - η / 2), ∀ h : ℝ, |h| ≤ η / 4 →
      Jp ε (w + h) - Jp ε w ≤ Λ * |h|)
    {W : Graphon} {t τ : ℝ} (hWe : W.edgeDensity = ε) (hWt : W.tDensity H = t)
    {D : Kernel}
    (hsupp : ∀ x y, D.toFun x y ≠ 0 → η / 2 < W.toFun x y ∧ W.toFun x y < 1 - η / 2)
    (hDB : ∀ x y, |D.toFun x y| ≤ B)
    (hD0 : ∫ z, D.toFun z.1 z.2 ∂gμ = 0)
    (hDc : c ≤ ∫ z, derivKernel H W z.1 z.2 * D.toFun z.1 z.2 ∂gμ)
    (hτ : t < τ)
    (hstep : 2 * (τ - t) / c ≤ min (η / (4 * B))
      (c / (2 * ((H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * B * B + 1)))) :
    fixedValue H ε τ ≤ W.Ip ε + 2 * Λ * B / c * (τ - t) := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hcne : c ≠ 0 := ne_of_gt hc
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (H.edgeFinset.card : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hmmB : 0 ≤ m * m * B := mul_nonneg (mul_nonneg hm0 hm0) hB.le
  obtain ⟨K, hK⟩ : ∃ K, K = m * m * B * B + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    rw [hK]; linarith [mul_nonneg hmmB hB.le]
  rw [← hm, ← hK] at hstep
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = min (η / (4 * B)) (c / (2 * K)) := ⟨_, rfl⟩
  have hθ₀0 : 0 < θ₀ := by
    rw [hθ₀]
    exact lt_min (div_pos hη (by linarith)) (div_pos hc (by linarith))
  obtain ⟨s, hsdef⟩ : ∃ s, s = 2 * (τ - t) / c := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos (by linarith) hc
  have hsθ : s ≤ θ₀ := by rw [hsdef, hθ₀]; exact hstep
  -- the one-parameter family
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun θ => (Kernel.ofGraphon W + θ • D).tDensity H :=
    ⟨_, rfl⟩
  have hFcont : Continuous F := by rw [hFdef]; exact continuous_tDensity_line H W D
  have hF0 : F 0 = t := by
    rw [hFdef]
    simp only
    rw [← hWt, ← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  -- for `|θ| ≤ θ₀` the moved values stay in `[η/4, 1-η/4]`
  have hsmall : ∀ θ : ℝ, |θ| ≤ θ₀ → ∀ x y, |θ * D.toFun x y| ≤ η / 4 := by
    intro θ hθ x y
    rw [abs_mul]
    have h1 : |θ| ≤ η / (4 * B) := hθ.trans (hθ₀ ▸ min_le_left _ _)
    calc |θ| * |D.toFun x y| ≤ η / (4 * B) * B :=
          mul_le_mul h1 (hDB x y) (abs_nonneg _) (by positivity)
      _ = η / 4 := by field_simp
  have hgraphon : ∀ θ : ℝ, |θ| ≤ θ₀ →
      ∃ G : Graphon, ∀ x y, G.toFun x y = W.toFun x y + θ * D.toFun x y := by
    intro θ hθ
    obtain ⟨G, hG⟩ := exists_graphon_of_mem (Kernel.ofGraphon W + θ • D) (by
      intro x y
      obtain ⟨hlo, hhi⟩ := abs_le.mp (hsmall θ hθ x y)
      simp only [Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply]
      by_cases hd : D.toFun x y = 0
      · rw [hd, mul_zero, add_zero]; exact W.mem_Icc x y
      · obtain ⟨h1, h2⟩ := hsupp x y hd
        exact ⟨by linarith, by linarith⟩)
    exact ⟨G, fun x y => by rw [hG]; simp⟩
  -- the derivative of `F` is at least `c/2` on the relevant range
  have hkey : ∀ θ : ℝ, |θ| ≤ θ₀ → ∃ v : ℝ, HasDerivAt F v θ ∧ c / 2 ≤ v := by
    intro θ hθ
    obtain ⟨G, hG⟩ := hgraphon θ hθ
    refine ⟨∫ z, derivKernel H G z.1 z.2 * D.toFun z.1 z.2 ∂gμ, ?_, ?_⟩
    · have hsub : HasDerivAt (fun u : ℝ => u - θ) 1 θ := (hasDerivAt_id θ).sub_const θ
      have hfv' : HasDerivAt (fun σ : ℝ => (Kernel.ofGraphon G + σ • D).tDensity H)
          (∫ z, derivKernel H G z.1 z.2 * D.toFun z.1 z.2 ∂gμ) (θ - θ) := by
        simpa using first_variation H G D
      have hcomp := hfv'.comp_sub_const θ θ
      have hFeq : F = fun u : ℝ => (Kernel.ofGraphon G + (u - θ) • D).tDensity H := by
        funext u
        rw [hFdef]
        simp only
        refine kernel_tDensity_congr H fun x y => ?_
        simp only [Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply, hG x y]
        ring
      rw [hFeq]
      exact hcomp
    · have hGW : ∫ z, |G.toFun z.1 z.2 - W.toFun z.1 z.2| ∂gμ ≤ |θ| * B := by
        have hpt : ∀ z : ℝ × ℝ, |G.toFun z.1 z.2 - W.toFun z.1 z.2| ≤ |θ| * B := by
          intro z
          rw [hG z.1 z.2, add_sub_cancel_left, abs_mul]
          exact mul_le_mul_of_nonneg_left (hDB _ _) (abs_nonneg _)
        calc ∫ z, |G.toFun z.1 z.2 - W.toFun z.1 z.2| ∂gμ ≤ ∫ _z : ℝ × ℝ, |θ| * B ∂gμ :=
              integral_mono (integrable_abs_sub (Kernel.ofGraphon G) (Kernel.ofGraphon W))
                (integrable_const _) hpt
          _ = |θ| * B := by simp
      have h1 : |(∫ z, derivKernel H G z.1 z.2 * D.toFun z.1 z.2 ∂gμ)
          - ∫ z, derivKernel H W z.1 z.2 * D.toFun z.1 z.2 ∂gμ| ≤ m * m * B * (|θ| * B) := by
        have hlip := abs_integral_derivKernel_mul_sub_le H G W D hDB
        rw [← hm] at hlip
        exact hlip.trans (mul_le_mul_of_nonneg_left hGW hmmB)
      have h2 : m * m * B * (|θ| * B) ≤ c / 2 := by
        have hθK : |θ| ≤ c / (2 * K) := hθ.trans (hθ₀ ▸ min_le_right _ _)
        calc m * m * B * (|θ| * B) = m * m * B * B * |θ| := by ring
          _ ≤ K * |θ| := mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (abs_nonneg _)
          _ ≤ K * (c / (2 * K)) := mul_le_mul_of_nonneg_left hθK hK0.le
          _ = c / 2 := by field_simp
      linarith [(abs_le.mp h1).1]
  -- the mean value theorem: `F s ≥ τ`
  have hFs : τ ≤ F s := by
    obtain ⟨θc, hθc, heq⟩ := exists_hasDerivAt_eq_slope F (deriv F) hs0 hFcont.continuousOn
      (fun x hx => by
        obtain ⟨v, hv, -⟩ := hkey x (by rw [abs_of_pos hx.1]; linarith [hx.2, hsθ])
        rw [hv.deriv]; exact hv)
    have hd2 : c / 2 ≤ deriv F θc := by
      obtain ⟨v, hv, hcv⟩ := hkey θc (by rw [abs_of_pos hθc.1]; linarith [hθc.2, hsθ])
      rw [hv.deriv]; exact hcv
    rw [hF0, sub_zero] at heq
    rw [heq, le_div_iff₀ hs0] at hd2
    have hst : c / 2 * s = τ - t := by rw [hsdef]; field_simp
    linarith
  -- the intermediate value theorem: `F θ = τ` for some `θ ∈ [0, s]`
  obtain ⟨θ, hθmem, hθeq⟩ : ∃ θ ∈ Icc (0:ℝ) s, F θ = τ :=
    intermediate_value_Icc hs0.le hFcont.continuousOn ⟨by rw [hF0]; linarith, hFs⟩
  have hθabs : |θ| ≤ θ₀ := by
    rw [abs_of_nonneg hθmem.1]; exact hθmem.2.trans hsθ
  obtain ⟨G, hG⟩ := hgraphon θ hθabs
  -- the corrected graphon is feasible
  have hGe : G.edgeDensity = ε := by
    have h1 : G.edgeDensity = ∫ z, (W.toFun z.1 z.2 + θ * D.toFun z.1 z.2) ∂gμ :=
      integral_congr_ae (ae_of_all _ fun z => hG z.1 z.2)
    rw [h1, integral_add W.integrable_self ((kernel_integrable D).const_mul θ),
      integral_const_mul, hD0, mul_zero, add_zero]
    exact hWe
  have hGt : G.tDensity H = τ := by
    rw [← hθeq, hFdef]
    simp only
    rw [← Kernel.tDensity_ofGraphon]
    refine kernel_tDensity_congr H fun x y => ?_
    simp only [Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply, hG x y]
  -- the entropy cost
  have hIG := G.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hIW := W.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
  have hpt : ∀ z : ℝ × ℝ,
      Jp ε (G.toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2) ≤ Λ * (|θ| * B) := by
    intro z
    rw [hG z.1 z.2]
    by_cases hd : D.toFun z.1 z.2 = 0
    · rw [hd, mul_zero, add_zero, sub_self]
      exact mul_nonneg hΛ (mul_nonneg (abs_nonneg _) hB.le)
    · obtain ⟨h1, h2⟩ := hsupp z.1 z.2 hd
      refine (hLip (W.toFun z.1 z.2) ⟨h1, h2⟩ (θ * D.toFun z.1 z.2)
        (hsmall θ hθabs z.1 z.2)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hDB _ _) (abs_nonneg _)
  have hcost : G.Ip ε ≤ W.Ip ε + Λ * (|θ| * B) := by
    have h : (∫ z, (Jp ε (G.toFun z.1 z.2) - Jp ε (W.toFun z.1 z.2)) ∂gμ)
        ≤ ∫ _z : ℝ × ℝ, Λ * (|θ| * B) ∂gμ :=
      integral_mono (hIG.sub hIW) (integrable_const _) hpt
    have hconst : ∫ _z : ℝ × ℝ, Λ * (|θ| * B) ∂gμ = Λ * (|θ| * B) := by simp
    rw [integral_sub hIG hIW, hconst] at h
    show (∫ z, Jp ε (G.toFun z.1 z.2) ∂gμ) ≤ (∫ z, Jp ε (W.toFun z.1 z.2) ∂gμ) + _
    linarith
  -- the step length is at most `s`
  have hfinal : Λ * (|θ| * B) ≤ 2 * Λ * B / c * (τ - t) := by
    have hΛB : 0 ≤ Λ * B := mul_nonneg hΛ hB.le
    have hθs : |θ| ≤ s := by rw [abs_of_nonneg hθmem.1]; exact hθmem.2
    calc Λ * (|θ| * B) = Λ * B * |θ| := by ring
      _ ≤ Λ * B * s := mul_le_mul_of_nonneg_left hθs hΛB
      _ = 2 * Λ * B / c * (τ - t) := by rw [hsdef]; field_simp
  linarith [fixedValue_le H hε0 hε1 hGe hGt]


/-! ### The uniform bound -/

/-- **`lem:uniform-density-restoration`, in the form used by `thm:fixed-densities`.**  Let `W_n` attain
`Ψ_ε(τ_n)` for densities `τ_n ↑ τ`, and suppose the `W_n` converge in `L¹` to a graphon `W_*`
satisfying `def:constraint-qualification`.  Then

`Ψ_ε(τ) ≤ Ψ_ε(τ_n) + C(τ - τ_n)`

for all large `n`, with `C` independent of `n`.  Combined with `lem:degenerate-slope`, which
forces the left difference quotients of `Ψ_ε` at `τ` to tend to `+∞`, this is the contradiction
that proves `thm:fixed-densities`. -/
theorem exists_uniform_upward_correction (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (Wn : ℕ → Graphon) (tn : ℕ → ℝ)
    (hfeas : ∀ n, (Wn n).edgeDensity = ε ∧ (Wn n).tDensity H = tn n)
    (hopt : ∀ n, (Wn n).Ip ε = fixedValue H ε (tn n))
    (hlt : ∀ n, tn n < τ) (htend : Filter.Tendsto tn Filter.atTop (nhds τ))
    (Wstar : Graphon)
    (hL1 : Filter.Tendsto (fun n => ∫ z, |(Wn n).toFun z.1 z.2 - Wstar.toFun z.1 z.2| ∂gμ)
      Filter.atTop (nhds 0))
    (hcq : ConstraintQualification H Wstar) :
    ∃ C : ℝ, ∀ᶠ n in Filter.atTop,
      fixedValue H ε τ ≤ fixedValue H ε (tn n) + C * (τ - tn n) := by
  obtain ⟨η, B, c, hη, hη1, hB, hc, D, hev⟩ := exists_uniform_direction H Wn Wstar hL1 hcq
  obtain ⟨Λ, hΛ0, hLip⟩ := exists_Jp_lipschitz_window hε0 hε1 hη hη1
  refine ⟨2 * Λ * B / c, ?_⟩
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = min (η / (4 * B))
      (c / (2 * ((H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * B * B + 1))) := ⟨_, rfl⟩
  have hθ₀0 : 0 < θ₀ := by
    have hmm : (0:ℝ) ≤ (H.edgeFinset.card : ℝ) * (H.edgeFinset.card : ℝ) * B * B :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hB.le) hB.le
    rw [hθ₀]
    exact lt_min (div_pos hη (by linarith)) (div_pos hc (by linarith))
  have hstep : ∀ᶠ n in Filter.atTop, 2 * (τ - tn n) / c ≤ θ₀ := by
    have htd : Filter.Tendsto (fun n => 2 * (τ - tn n) / c) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun n => τ - tn n) Filter.atTop (nhds (τ - τ)) :=
        tendsto_const_nhds.sub htend
      rw [sub_self] at h0
      simpa using (h0.const_mul 2).div_const c
    exact (htd.eventually_lt_const hθ₀0).mono fun n h => h.le
  filter_upwards [hev, hstep] with n hn hsn
  obtain ⟨hsupp, hDB, hD0, hDc⟩ := hn
  have hres := fixedValue_le_of_direction H hε0 hε1 hη hB hc hΛ0 hLip
    (hfeas n).1 (hfeas n).2 hsupp hDB hD0 hDc (hlt n) (hθ₀ ▸ hsn)
  rwa [hopt n] at hres

end FixedDensities

end UpperTailMultipodality
