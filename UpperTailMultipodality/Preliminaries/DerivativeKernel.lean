import UpperTailMultipodality.Preliminaries.EntropyIdentity
import UpperTailMultipodality.Preliminaries.Calculus.EdgeProducts
import UpperTailMultipodality.Preliminaries.Calculus.PolynomialIntegral

/-!
# The first variation of homomorphism densities (`sec:derivatives`)

For an edge `ab` of `H`, oriented from `a` to `b`, `K_{ab,W}(x,y)` integrates the product of `W`
over the edges of `H` other than `ab`, with `x_a = x` and `x_b = y`.  The derivative kernel,
`eq:derivative-kernel`, is

`𝒟_W(x,y) = ½ ∑_{ab ∈ E(H)} (K_{ab,W}(x,y) + K_{ab,W}(y,x))`,

written here as `½` times the sum over ordered adjacent pairs `(a,b)`, since
`K_{ba,W}(x,y) = K_{ab,W}(y,x)`.  It represents the first variation of `t(H,·)`,
`eq:first-variation`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The assignment `ξ` with the coordinates `a` and `b` replaced by `x` and `y`. -/
def pin (ξ : V → ℝ) (a b : V) (x y : ℝ) : V → ℝ :=
  Function.update (Function.update ξ a x) b y

/-- `K_{ab,W}(x,y)`: the integral of `∏_{e ∈ E(H) ∖ {ab}} W` with `x_a = x`, `x_b = y`. -/
noncomputable def edgeRemovedDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (a b : V) (x y : ℝ) : ℝ :=
  ∫ ξ : V → ℝ, ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin ξ a b x y) e
    ∂(Measure.pi fun _ => unitμ)

/-- **The derivative kernel `𝒟_W`, `eq:derivative-kernel`.** -/
noncomputable def derivKernel (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (x y : ℝ) : ℝ :=
  (1 / 2) * ∑ a, ∑ b, if H.Adj a b then edgeRemovedDensity H W a b x y else 0

/-! ### Pinned coordinates and the kernels `K_{ab,W}` -/

section Pinned

omit [Fintype V] in
/-- The pinned value at `a`. -/
@[simp] theorem pin_apply_left (ξ : V → ℝ) {a b : V} (hab : a ≠ b) (x y : ℝ) :
    pin ξ a b x y a = x := by
  simp [pin, Function.update_of_ne hab]

omit [Fintype V] in
/-- The pinned value at `b`. -/
@[simp] theorem pin_apply_right (ξ : V → ℝ) (a b : V) (x y : ℝ) : pin ξ a b x y b = y := by
  simp [pin]

omit [Fintype V] in
/-- Coordinates other than `a` and `b` are unchanged. -/
theorem pin_apply_of_ne (ξ : V → ℝ) {a b i : V} (hia : i ≠ a) (hib : i ≠ b) (x y : ℝ) :
    pin ξ a b x y i = ξ i := by
  simp [pin, Function.update_of_ne hia, Function.update_of_ne hib]

omit [Fintype V] in
/-- `ξ ↦ pin ξ a b x y` is measurable. -/
theorem measurable_pin (a b : V) (x y : ℝ) : Measurable fun ξ : V → ℝ => pin ξ a b x y :=
  measurable_update_left.comp measurable_update_left

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `K_{ab,W}` takes values in `[0,1]`. -/
theorem edgeRemovedDensity_mem_Icc (W : Graphon) (a b : V) (x y : ℝ) :
    edgeRemovedDensity H W a b x y ∈ Set.Icc (0:ℝ) 1 := by
  have hint : Integrable (fun ξ : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin ξ a b x y) e)
      (Measure.pi fun _ : V => unitμ) :=
    ((isBddMeas_prod_edgeVal W _).comp (measurable_pin a b x y)).integrable
  refine ⟨integral_nonneg fun ξ => (prod_edgeVal_mem_Icc W _ _).1, ?_⟩
  calc edgeRemovedDensity H W a b x y ≤ ∫ _ξ : V → ℝ, (1:ℝ) ∂(Measure.pi fun _ : V => unitμ) :=
        integral_mono hint (integrable_const 1) fun ξ => (prod_edgeVal_mem_Icc W _ _).2
    _ = 1 := by simp

/-- `(x,y) ↦ K_{ab,W}(x,y)` is measurable. -/
theorem measurable_edgeRemovedDensity (W : Graphon) (a b : V) :
    Measurable fun z : ℝ × ℝ => edgeRemovedDensity H W a b z.1 z.2 :=
  measurable_integral_update₂_pi a b (isBddMeas_prod_edgeVal W (H.edgeFinset.erase s(a, b))).1

/-- The derivative kernel as a sum over neighbourhoods. -/
theorem derivKernel_eq_sum (W : Graphon) (x y : ℝ) :
    derivKernel H W x y
      = (1 / 2) * ∑ a, ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H W a b x y := by
  rw [derivKernel, sum_ite_adj_eq_sum_neighborFinset]

/-- **Resampling the pinned coordinates.**  For an ordered pair `a ≠ b` and a bounded kernel `U`,
`∫∫ K_{ab,W} U = ∫ U(ξ_a, ξ_b) ∏_{e ≠ ab} W_e dξ`. -/
theorem integral_edgeRemovedDensity_mul (W : Graphon) (U : Kernel) {a b : V} (hab : a ≠ b) :
    ∫ z, edgeRemovedDensity H W a b z.1 z.2 * U.toFun z.1 z.2 ∂gμ
      = ∫ ξ, U.toFun (ξ a) (ξ b) * ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' ξ e
          ∂(Measure.pi fun _ : V => unitμ) := by
  have hF : IsBddMeas fun ξ : V → ℝ =>
      U.toFun (ξ a) (ξ b) * ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' ξ e :=
    (isBddMeas_edgeVal U s(a, b)).mul (isBddMeas_prod_edgeVal W _)
  rw [← integral_integral_update₂_pi a b hF]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have hpin : ∀ ξ : V → ℝ, Function.update (Function.update ξ a z.1) b z.2 = pin ξ a b z.1 z.2 :=
    fun _ => rfl
  simp only [hpin, pin_apply_left _ hab, pin_apply_right]
  rw [integral_const_mul, mul_comm]
  rfl

/-- **The first variation as a sum over edges.**  For a bounded kernel `U`,
`∫∫ 𝒟_W U = ∑_{e ∈ E(H)} ∫ U_e ∏_{e' ≠ e} W_{e'}`. -/
theorem integral_derivKernel_mul (W : Graphon) (U : Kernel) :
    ∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ
      = ∑ e ∈ H.edgeFinset, ∫ ξ, edgeVal U.toFun U.symm' ξ e
          * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
          ∂(Measure.pi fun _ : V => unitμ) := by
  have hint : ∀ a b, Integrable
      (fun z : ℝ × ℝ => edgeRemovedDensity H W a b z.1 z.2 * U.toFun z.1 z.2) gμ := fun a b =>
    ((IsBddMeas.of_mem_Icc (measurable_edgeRemovedDensity H W a b)
      fun z => edgeRemovedDensity_mem_Icc H W a b z.1 z.2).mul
        ⟨U.meas', U.bdd'.imp fun C hC z => hC z.1 z.2⟩).integrable
  have hpt : ∀ z : ℝ × ℝ, derivKernel H W z.1 z.2 * U.toFun z.1 z.2
      = (1 / 2) * ∑ a, ∑ b ∈ H.neighborFinset a,
          edgeRemovedDensity H W a b z.1 z.2 * U.toFun z.1 z.2 := by
    intro z
    rw [derivKernel_eq_sum, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  simp_rw [hpt]
  rw [integral_const_mul,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  simp_rw [integral_finsetSum _ fun b _ => hint _ b]
  obtain ⟨T, hT⟩ : ∃ T : Sym2 V → ℝ, T = fun e => ∫ ξ, edgeVal U.toFun U.symm' ξ e
      * ∏ e' ∈ H.edgeFinset.erase e, edgeVal W.toFun W.symm' ξ e'
        ∂(Measure.pi fun _ : V => unitμ) := ⟨_, rfl⟩
  have hterm : ∀ a, ∀ b ∈ H.neighborFinset a,
      ∫ z, edgeRemovedDensity H W a b z.1 z.2 * U.toFun z.1 z.2 ∂gμ = T s(a, b) := fun a b hb => by
    rw [hT]
    exact integral_edgeRemovedDensity_mul H W U (H.ne_of_adj ((H.mem_neighborFinset a b).mp hb))
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl (hterm a), sum_neighborFinset_sym2 H T,
    hT]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- For an edge `ij ≠ ab` and pinned values `x`, `y` whose rows are `≥ ω` almost everywhere,
the factor `W(x_i, x_j)` of `K_{ab,W}(x,y)` is `≥ ω` for almost every `ξ`. -/
theorem ae_le_pin_edge (W : Graphon) {ω : ℝ} (hW : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {a b i j : V} (hab : a ≠ b) (hij : i ≠ j) (hne : s(i, j) ≠ s(a, b)) {x y : ℝ}
    (hx : ∀ᵐ t ∂unitμ, ω ≤ W.toFun x t) (hy : ∀ᵐ t ∂unitμ, ω ≤ W.toFun y t) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ω ≤ W.toFun (pin ξ a b x y i) (pin ξ a b x y j) := by
  have hfree : ∀ c : ℝ, (∀ᵐ t ∂unitμ, ω ≤ W.toFun c t) →
      ∀ k : V, ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ω ≤ W.toFun c (ξ k) := fun c hc k =>
    (measurePreserving_eval (μ := fun _ : V => unitμ) k).quasiMeasurePreserving.ae hc
  by_cases hia : i = a
  · rw [hia] at hij hne ⊢
    have hjb : j ≠ b := fun h => hne (by rw [h])
    filter_upwards [hfree x hx j] with ξ hξ
    rwa [pin_apply_left _ hab, pin_apply_of_ne _ hij.symm hjb]
  by_cases hib : i = b
  · rw [hib] at hij hne ⊢
    have hja : j ≠ a := fun h => hne (by rw [h, Sym2.eq_swap])
    filter_upwards [hfree y hy j] with ξ hξ
    rwa [pin_apply_right, pin_apply_of_ne _ hja hij.symm]
  by_cases hja : j = a
  · rw [hja]
    filter_upwards [hfree x hx i] with ξ hξ
    rwa [pin_apply_left _ hab, pin_apply_of_ne _ hia hib, W.symm']
  by_cases hjb : j = b
  · rw [hjb]
    filter_upwards [hfree y hy i] with ξ hξ
    rwa [pin_apply_right, pin_apply_of_ne _ hia hib, W.symm']
  filter_upwards [(measurePreserving_pair (V := V) hij).quasiMeasurePreserving.ae hW] with ξ hξ
  rwa [pin_apply_of_ne _ hia hib, pin_apply_of_ne _ hja hjb]

/-- If `W ≥ ω ≥ 0` almost everywhere and the rows at `x` and `y` are `≥ ω` almost everywhere, then
`K_{ab,W}(x,y) ≥ ω^{m-1}` for every edge `ab`. -/
theorem edgeRemovedDensity_ge (W : Graphon) {ω : ℝ} (hω : 0 ≤ ω)
    (hW : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {a b : V} (hab : H.Adj a b) {x y : ℝ}
    (hx : ∀ᵐ t ∂unitμ, ω ≤ W.toFun x t) (hy : ∀ᵐ t ∂unitμ, ω ≤ W.toFun y t) :
    ω ^ (H.edgeFinset.card - 1) ≤ edgeRemovedDensity H W a b x y := by
  have hmem : s(a, b) ∈ H.edgeFinset := H.mem_edgeFinset.mpr hab
  have hae : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ∀ e ∈ H.edgeFinset.erase s(a, b),
      ω ≤ edgeVal W.toFun W.symm' (pin ξ a b x y) e := by
    refine (Filter.eventually_all_finset _).mpr fun e he => ?_
    induction e using Sym2.ind with
    | _ i j =>
      have hij : H.Adj i j := H.mem_edgeFinset.mp (Finset.mem_of_mem_erase he)
      exact ae_le_pin_edge W hW hab.ne hij.ne (Finset.ne_of_mem_erase he) hx hy
  have hprod : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ω ^ (H.edgeFinset.card - 1)
      ≤ ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin ξ a b x y) e := by
    filter_upwards [hae] with ξ hξ
    rw [← Finset.card_erase_of_mem hmem, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hω) hξ
  have hint : Integrable (fun ξ : V → ℝ =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin ξ a b x y) e)
      (Measure.pi fun _ : V => unitμ) :=
    ((isBddMeas_prod_edgeVal W _).comp (measurable_pin a b x y)).integrable
  calc ω ^ (H.edgeFinset.card - 1)
      = ∫ _ξ : V → ℝ, ω ^ (H.edgeFinset.card - 1) ∂(Measure.pi fun _ : V => unitμ) := by simp
    _ ≤ edgeRemovedDensity H W a b x y := integral_mono_ae (integrable_const _) hint hprod

end Pinned

/-- **`eq:first-variation`.**  For every bounded symmetric kernel `U`,
`d/dξ t(H, W + ξU)|_{ξ=0} = ∫∫ 𝒟_W U`. -/
theorem first_variation (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (U : Kernel) :
    HasDerivAt (fun ξ : ℝ => (Kernel.ofGraphon W + ξ • U).tDensity H)
      (∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ) 0 := by
  have hF := hasFDerivAt_integral_mul_prod_affine (μ := Measure.pi fun _ : V => unitμ)
    (k := fun e ξ => edgeVal W.toFun W.symm' ξ e)
    (u := fun e (_ : Fin 1) ξ => edgeVal U.toFun U.symm' ξ e)
    (fun e => isBddMeas_edgeVal (Kernel.ofGraphon W) e) (fun e _ => isBddMeas_edgeVal U e)
    H.edgeFinset (fun _ => 1) (IsBddMeas.const 1)
  have hline : HasDerivAt (fun ξ : ℝ => fun _ : Fin 1 => ξ) (fun _ => (1:ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have hcomp := hF.comp_hasDerivAt (0:ℝ) hline
  have hfun : (fun ξ : ℝ => (Kernel.ofGraphon W + ξ • U).tDensity H)
      = (fun s : Fin 1 → ℝ => ∫ ξ, (fun _ => (1:ℝ)) ξ * ∏ e ∈ H.edgeFinset,
          (edgeVal W.toFun W.symm' ξ e + ∑ i, s i * edgeVal U.toFun U.symm' ξ e)
            ∂(Measure.pi fun _ : V => unitμ)) ∘ (fun ξ : ℝ => fun _ : Fin 1 => ξ) := by
    funext t
    simp only [Function.comp_apply, Fin.sum_univ_one, one_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => Finset.prod_congr rfl fun e _ => ?_)
    induction e using Sym2.ind with
    | _ a b => rfl
  rw [hfun, integral_derivKernel_mul]
  refine hcomp.congr_deriv ?_
  simp

/-- `0 ≤ 𝒟_W ≤ m`. -/
theorem derivKernel_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (x y : ℝ) :
    derivKernel H W x y ∈ Set.Icc (0:ℝ) H.edgeFinset.card := by
  rw [derivKernel_eq_sum]
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      (edgeRemovedDensity_mem_Icc H W a b x y).1)
  · calc (1 / 2) * ∑ a, ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H W a b x y
        ≤ (1 / 2) * ∑ a, ∑ _b ∈ H.neighborFinset a, (1:ℝ) := by
          gcongr with a _ b _
          exact (edgeRemovedDensity_mem_Icc H W a b x y).2
      _ = H.edgeFinset.card := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [sum_card_neighborFinset]
          ring

/-- If `W ≥ ω` almost everywhere, then `𝒟_W ≥ m ω^{m-1}` almost everywhere. -/
theorem derivKernel_ge (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ω : ℝ}
    (hω : 0 ≤ ω) (hW : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) :
    ∀ᵐ z ∂gμ, (H.edgeFinset.card : ℝ) * ω ^ (H.edgeFinset.card - 1)
      ≤ derivKernel H W z.1 z.2 := by
  have hrow : ∀ᵐ x ∂unitμ, ∀ᵐ t ∂unitμ, ω ≤ W.toFun x t :=
    Measure.ae_ae_of_ae_prod (μ := unitμ) (ν := unitμ) (p := fun z => ω ≤ W.toFun z.1 z.2) hW
  have hpair : ∀ᵐ z ∂gμ, (∀ᵐ t ∂unitμ, ω ≤ W.toFun z.1 t) ∧ (∀ᵐ t ∂unitμ, ω ≤ W.toFun z.2 t) :=
    (Measure.quasiMeasurePreserving_fst.ae hrow).and (Measure.quasiMeasurePreserving_snd.ae hrow)
  filter_upwards [hpair] with z hz
  rw [derivKernel_eq_sum]
  calc (H.edgeFinset.card : ℝ) * ω ^ (H.edgeFinset.card - 1)
      = (1 / 2) * ∑ a, ∑ _b ∈ H.neighborFinset a, ω ^ (H.edgeFinset.card - 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, sum_card_neighborFinset]
        ring
    _ ≤ (1 / 2) * ∑ a, ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H W a b z.1 z.2 := by
        gcongr with a _ b hb
        exact edgeRemovedDensity_ge H W hω hW ((H.mem_neighborFinset a b).mp hb) hz.1 hz.2


end UpperTailMultipodality
