import UpperTailMultipodality.UpperTail.Support.Analysis

/-!
# Measurability and symmetry of the derivative kernel; a.e. invariance of `t(H,·)`

* `measurable_derivKernel` — `(x,y) ↦ 𝒟_W(x,y)` is measurable (a parametric integral of a jointly
  measurable integrand);
* `derivKernel_symm` — `𝒟_W(x,y) = 𝒟_W(y,x)`;
* `kernel_tDensity_congr_ae`, `graphon_tDensity_congr_ae` — `t(H,·)` depends only on the
  almost-everywhere class of the kernel.
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Each coordinate of `pin ξ a b x y` is jointly measurable in `((x,y), ξ)`. -/
theorem measurable_pin_apply (a b c : V) :
    Measurable fun q : (ℝ × ℝ) × (V → ℝ) => pin q.2 a b q.1.1 q.1.2 c := by
  unfold pin
  simp only [Function.update_apply]
  by_cases hcb : c = b
  · simp only [if_pos hcb]; fun_prop
  · by_cases hca : c = a
    · simp only [if_neg hcb, if_pos hca]; fun_prop
    · simp only [if_neg hcb, if_neg hca]
      exact (measurable_pi_apply c).comp measurable_snd

/-- `(x,y) ↦ K_{ab,W}(x,y)` is measurable. -/
theorem measurable_edgeRemovedDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (a b : V) : Measurable fun z : ℝ × ℝ => edgeRemovedDensity H W a b z.1 z.2 := by
  have hF : StronglyMeasurable fun q : (ℝ × ℝ) × (V → ℝ) =>
      ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal W.toFun W.symm' (pin q.2 a b q.1.1 q.1.2) e := by
    refine Measurable.stronglyMeasurable (Finset.measurable_prod _ fun e _ => ?_)
    induction e using Sym2.ind with
    | _ c d =>
      show Measurable fun q : (ℝ × ℝ) × (V → ℝ) =>
        W.toFun (pin q.2 a b q.1.1 q.1.2 c) (pin q.2 a b q.1.1 q.1.2 d)
      exact W.measurable_uncurry.comp ((measurable_pin_apply a b c).prodMk
        (measurable_pin_apply a b d))
  exact hF.integral_prod_right'.measurable

/-- **`𝒟_W` is measurable.** -/
theorem measurable_derivKernel (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) :
    Measurable fun z : ℝ × ℝ => derivKernel H W z.1 z.2 := by
  unfold derivKernel
  refine Measurable.const_mul (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun b _ => ?_) _
  by_cases hab : H.Adj a b
  · simp only [hab, if_true]; exact measurable_edgeRemovedDensity H W a b
  · simp only [hab, if_false]; exact measurable_const

/-- Swapping the roles of the two pinned endpoints. -/
theorem edgeRemovedDensity_swap (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {a b : V} (hab : a ≠ b) (x y : ℝ) :
    edgeRemovedDensity H W a b x y = edgeRemovedDensity H W b a y x := by
  unfold edgeRemovedDensity pin
  rw [Sym2.eq_swap]
  congr 1
  funext ξ
  rw [Function.update_comm hab]

/-- **`𝒟_W` is symmetric.** -/
theorem derivKernel_symm (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (x y : ℝ) :
    derivKernel H W x y = derivKernel H W y x := by
  unfold derivKernel
  congr 1
  have h1 : ∀ a b : V, (if H.Adj a b then edgeRemovedDensity H W a b x y else 0)
      = if H.Adj b a then edgeRemovedDensity H W b a y x else 0 := by
    intro a b
    by_cases hab : H.Adj a b
    · rw [if_pos hab, if_pos hab.symm, edgeRemovedDensity_swap H W hab.ne]
    · rw [if_neg hab, if_neg fun h => hab h.symm]
  simp_rw [h1]
  exact Finset.sum_comm

/-- **`t(H,·)` of a kernel depends only on its a.e. class.** -/
theorem kernel_tDensity_congr_ae {K L : Kernel} (H : SimpleGraph V) [DecidableRel H.Adj]
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
  have hall := (eventually_all_finset _).mpr hedge
  unfold Kernel.tDensity
  exact integral_congr_ae (hall.mono fun x hx => Finset.prod_congr rfl fun e he => hx e he)

/-- **`t(H,·)` of a graphon depends only on its a.e. class.** -/
theorem graphon_tDensity_congr_ae {W W' : Graphon} (H : SimpleGraph V) [DecidableRel H.Adj]
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) :
    W.tDensity H = W'.tDensity H :=
  kernel_tDensity_congr_ae (K := Kernel.ofGraphon W) (L := Kernel.ofGraphon W') H hae

/-- `I_p` of a graphon depends only on its a.e. class. -/
theorem graphon_Ip_congr_ae {W W' : Graphon} (p : ℝ)
    (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) : W.Ip p = W'.Ip p :=
  integral_congr_ae (hae.mono fun z hz => by simp only [hz])

end UpperTailSupport

end UpperTailMultipodality
