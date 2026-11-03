import UpperTailMultipodality.Preliminaries.DerivativeKernel

/-!
# Rooted densities (`sec:rooted-densities`)

For a measurable `u : [0,1] → [0,1]`, regarded as the row of a new vertex, the rooted density of
`H` at `v`, `eq:rooted-density`, is

`ℛ_{v,W}(u) = ∫ ∏_{z ∈ N_H(v)} u(x_z) ∏_{ab ∈ E(H), a,b ≠ v} W(x_a,x_b) ∏_{z ≠ v} dx_z`,

and `ℛ_W = ∑_v ℛ_{v,W}`, `eq:total-rooted-density`.  The integral is taken over all coordinates;
the coordinate `x_v` does not occur in the integrand.  The gradient `∇ℛ_W(u)` is the sum over
ordered pairs `(v, z₀)` with `z₀ ∈ N_H(v)` of `G_{v,z₀}(u)`, `eq:rooted-gradient-kernel`.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A *row*: a measurable function with values in `[0,1]`. -/
def IsRow (u : ℝ → ℝ) : Prop := Measurable u ∧ ∀ y, u y ∈ Set.Icc (0:ℝ) 1

/-- The product of `W` over the edges of `H` that avoid the vertex `v`. -/
noncomputable def avoidingProduct (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) (ξ : V → ℝ) : ℝ :=
  ∏ e ∈ H.edgeFinset.filter (fun e => v ∉ e), edgeVal W.toFun W.symm' ξ e

/-- `avoidingProduct` lies in `[0,1]`. -/
theorem avoidingProduct_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    (ξ : V → ℝ) : avoidingProduct H W v ξ ∈ Set.Icc (0:ℝ) 1 :=
  prod_edgeVal_mem_Icc W _ ξ

/-- `avoidingProduct` is bounded and measurable. -/
theorem isBddMeas_avoidingProduct (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) : IsBddMeas fun ξ : V → ℝ => avoidingProduct H W v ξ :=
  isBddMeas_prod_edgeVal W _

/-- `avoidingProduct` is measurable. -/
theorem measurable_avoidingProduct (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) : Measurable (avoidingProduct H W v) :=
  (isBddMeas_avoidingProduct H W v).1

/-- **The rooted density `ℛ_{v,W}(u)`, `eq:rooted-density`.** -/
noncomputable def rootedDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    (u : ℝ → ℝ) : ℝ :=
  ∫ ξ : V → ℝ, (∏ z ∈ H.neighborFinset v, u (ξ z)) * avoidingProduct H W v ξ
    ∂(Measure.pi fun _ => unitμ)

/-- **The total rooted density `ℛ_W(u)`, `eq:total-rooted-density`.** -/
noncomputable def totalRootedDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (u : ℝ → ℝ) : ℝ :=
  ∑ v, rootedDensity H W v u

/-- `G_{v,z₀}(u)(y)`, `eq:rooted-gradient-kernel`. -/
noncomputable def rootedGradientTerm (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v z₀ : V) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ ξ : V → ℝ, (∏ z ∈ (H.neighborFinset v).erase z₀, u (Function.update ξ z₀ y z))
      * avoidingProduct H W v (Function.update ξ z₀ y)
    ∂(Measure.pi fun _ => unitμ)

/-- **The gradient `∇ℛ_W(u)`.** -/
noncomputable def rootedGradient (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ v, ∑ z₀ ∈ H.neighborFinset v, rootedGradientTerm H W v z₀ u y

/-! ### Rows substituted into the rooted densities -/

section Rows

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The product over the edges avoiding `v` does not see the coordinate `v`. -/
theorem avoidingProduct_update (W : Graphon) (v : V) (ξ : V → ℝ) (x : ℝ) :
    avoidingProduct H W v (Function.update ξ v x) = avoidingProduct H W v ξ := by
  unfold avoidingProduct
  refine Finset.prod_congr rfl fun e he => ?_
  have hv : v ∉ e := (Finset.mem_filter.mp he).2
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ v := fun h => hv (h ▸ Sym2.mem_mk_left a b)
    have hb : b ≠ v := fun h => hv (h ▸ Sym2.mem_mk_right a b)
    show W.toFun (Function.update ξ v x a) (Function.update ξ v x b) = W.toFun (ξ a) (ξ b)
    rw [Function.update_of_ne ha, Function.update_of_ne hb]

/-- **Substituting the root.**  Setting `x_v = x` in `∏_{e ∈ E(H)} W` gives the integrand of
`ℛ_{v,W}(W_x)`. -/
theorem prod_edgeVal_update_eq (W : Graphon) (v : V) (ξ : V → ℝ) (x : ℝ) :
    ∏ e ∈ H.edgeFinset, edgeVal W.toFun W.symm' (Function.update ξ v x) e
      = (∏ z ∈ H.neighborFinset v, W.row x (ξ z)) * avoidingProduct H W v ξ := by
  rw [prod_edgeFinset_eq_star H _ v]
  show (∏ z ∈ H.neighborFinset v, edgeVal W.toFun W.symm' (Function.update ξ v x) s(v, z))
      * avoidingProduct H W v (Function.update ξ v x) = _
  rw [avoidingProduct_update]
  congr 1
  refine Finset.prod_congr rfl fun z hz => ?_
  have hzv : z ≠ v := (H.ne_of_adj ((H.mem_neighborFinset v z).mp hz)).symm
  show W.toFun (Function.update ξ v x v) (Function.update ξ v x z) = W.toFun x (ξ z)
  rw [Function.update_self, Function.update_of_ne hzv]

/-- **Substituting the root, with one edge removed.** -/
theorem prod_edgeVal_erase_update_eq (W : Graphon) (v z₀ : V) (ξ : V → ℝ) (x : ℝ) :
    ∏ e ∈ H.edgeFinset.erase s(v, z₀), edgeVal W.toFun W.symm' (Function.update ξ v x) e
      = (∏ z ∈ (H.neighborFinset v).erase z₀, W.row x (ξ z)) * avoidingProduct H W v ξ := by
  rw [prod_edgeFinset_erase_eq_star H _ v z₀]
  show (∏ z ∈ (H.neighborFinset v).erase z₀,
        edgeVal W.toFun W.symm' (Function.update ξ v x) s(v, z))
      * avoidingProduct H W v (Function.update ξ v x) = _
  rw [avoidingProduct_update]
  congr 1
  refine Finset.prod_congr rfl fun z hz => ?_
  have hzv : z ≠ v :=
    (H.ne_of_adj ((H.mem_neighborFinset v z).mp (Finset.mem_of_mem_erase hz))).symm
  show W.toFun (Function.update ξ v x v) (Function.update ξ v x z) = W.toFun x (ξ z)
  rw [Function.update_self, Function.update_of_ne hzv]

/-- `ℛ_{v,W}(W_x)` is the homomorphism density of `H` with the vertex `v` fixed at `x`. -/
theorem rootedDensity_row (W : Graphon) (v : V) (x : ℝ) :
    rootedDensity H W v (W.row x)
      = ∫ ξ, ∏ e ∈ H.edgeFinset, edgeVal W.toFun W.symm' (Function.update ξ v x) e
          ∂(Measure.pi fun _ => unitμ) := by
  unfold rootedDensity
  simp_rw [prod_edgeVal_update_eq]

/-- `ℛ_{v,W}(u)` is Lipschitz in `u`: `|ℛ_{v,W}(u) - ℛ_{v,W}(u')| ≤ deg(v) ‖u - u'‖₁`. -/
theorem abs_rootedDensity_sub_le (W : Graphon) (v : V) {u u' : ℝ → ℝ} (hu : IsRow u)
    (hu' : IsRow u') :
    |rootedDensity H W v u - rootedDensity H W v u'|
      ≤ (H.neighborFinset v).card * ∫ y, |u y - u' y| ∂unitμ := by
  have hA := isBddMeas_prod_edgeVal W (H.edgeFinset.filter fun e => v ∉ e)
  have hP : ∀ w : ℝ → ℝ, IsRow w →
      IsBddMeas fun ξ : V → ℝ => ∏ z ∈ H.neighborFinset v, w (ξ z) := fun w hw =>
    IsBddMeas.finset_prod _ fun z _ =>
      (IsBddMeas.of_mem_Icc hw.1 hw.2).comp (measurable_pi_apply z)
  have hint : ∀ w : ℝ → ℝ, IsRow w → Integrable (fun ξ : V → ℝ =>
      (∏ z ∈ H.neighborFinset v, w (ξ z)) * avoidingProduct H W v ξ)
      (Measure.pi fun _ => unitμ) := fun w hw => ((hP w hw).mul hA).integrable
  have hdiff : ∀ z : V, Integrable (fun ξ : V → ℝ => |u (ξ z) - u' (ξ z)|)
      (Measure.pi fun _ => unitμ) := fun z =>
    ((((IsBddMeas.of_mem_Icc hu.1 hu.2).sub (IsBddMeas.of_mem_Icc hu'.1 hu'.2)).abs).comp
      (measurable_pi_apply z)).integrable
  have hpt : ∀ ξ : V → ℝ,
      |(∏ z ∈ H.neighborFinset v, u (ξ z)) * avoidingProduct H W v ξ
        - (∏ z ∈ H.neighborFinset v, u' (ξ z)) * avoidingProduct H W v ξ|
      ≤ ∑ z ∈ H.neighborFinset v, |u (ξ z) - u' (ξ z)| := by
    intro ξ
    have hAξ : avoidingProduct H W v ξ ∈ Set.Icc (0:ℝ) 1 := prod_edgeVal_mem_Icc W _ ξ
    rw [← sub_mul, abs_mul, abs_of_nonneg hAξ.1]
    calc |(∏ z ∈ H.neighborFinset v, u (ξ z)) - ∏ z ∈ H.neighborFinset v, u' (ξ z)|
          * avoidingProduct H W v ξ
        ≤ |(∏ z ∈ H.neighborFinset v, u (ξ z)) - ∏ z ∈ H.neighborFinset v, u' (ξ z)| * 1 :=
          mul_le_mul_of_nonneg_left hAξ.2 (abs_nonneg _)
      _ ≤ ∑ z ∈ H.neighborFinset v, |u (ξ z) - u' (ξ z)| := by
          rw [mul_one]
          exact abs_prod_sub_prod_le_sum _ _ _ (fun z _ => hu.2 _) (fun z _ => hu'.2 _)
  unfold rootedDensity
  rw [← integral_sub (hint u hu) (hint u' hu')]
  calc |∫ ξ, ((∏ z ∈ H.neighborFinset v, u (ξ z)) * avoidingProduct H W v ξ
        - (∏ z ∈ H.neighborFinset v, u' (ξ z)) * avoidingProduct H W v ξ)
          ∂(Measure.pi fun _ => unitμ)|
      ≤ ∫ ξ, |(∏ z ∈ H.neighborFinset v, u (ξ z)) * avoidingProduct H W v ξ
        - (∏ z ∈ H.neighborFinset v, u' (ξ z)) * avoidingProduct H W v ξ|
          ∂(Measure.pi fun _ => unitμ) := abs_integral_le_integral_abs
    _ ≤ ∫ ξ, ∑ z ∈ H.neighborFinset v, |u (ξ z) - u' (ξ z)| ∂(Measure.pi fun _ => unitμ) :=
        integral_mono ((hint u hu).sub (hint u' hu')).abs
          (integrable_finsetSum _ fun z _ => hdiff z) hpt
    _ = ∑ z ∈ H.neighborFinset v, ∫ ξ, |u (ξ z) - u' (ξ z)| ∂(Measure.pi fun _ => unitμ) :=
        integral_finsetSum _ fun z _ => hdiff z
    _ = ∑ _z ∈ H.neighborFinset v, ∫ y, |u y - u' y| ∂unitμ :=
        Finset.sum_congr rfl fun z _ => integral_comp_eval_pi z (hu.1.sub hu'.1).abs
    _ = (H.neighborFinset v).card * ∫ y, |u y - u' y| ∂unitμ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `G_{v,z₀}(W_x)(y) = K_{vz₀,W}(x,y)`: substituting the row `W_x` into the gradient term
recovers the kernel with the edge `vz₀` removed. -/
theorem rootedGradientTerm_row (W : Graphon) {v z₀ : V} (h : z₀ ∈ H.neighborFinset v)
    (x y : ℝ) :
    rootedGradientTerm H W v z₀ (W.row x) y = edgeRemovedDensity H W v z₀ x y := by
  have hne : v ≠ z₀ := H.ne_of_adj ((H.mem_neighborFinset v z₀).mp h)
  unfold rootedGradientTerm edgeRemovedDensity
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  have hpin : pin ξ v z₀ x y = Function.update (Function.update ξ z₀ y) v x := by
    unfold pin
    exact Function.update_comm hne x y ξ
  simp only
  rw [hpin, prod_edgeVal_erase_update_eq]

end Rows

/-- **`eq:rooted-average`.**  `∫₀¹ ℛ_W(W_x) dx = N t(H,W)`. -/
theorem rooted_average (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) :
    ∫ x, totalRootedDensity H W (W.row x) ∂unitμ = Fintype.card V * W.tDensity H := by
  have hF := isBddMeas_prod_edgeVal W H.edgeFinset
  have hint : ∀ v ∈ (Finset.univ : Finset V),
      Integrable (fun x => rootedDensity H W v (W.row x)) unitμ := fun v _ => by
    simp_rw [rootedDensity_row]
    exact integrable_integral_update_pi v hF
  have hv : ∀ v : V, ∫ x, rootedDensity H W v (W.row x) ∂unitμ = W.tDensity H := fun v => by
    simp_rw [rootedDensity_row]
    exact integral_integral_update_pi v hF
  unfold totalRootedDensity
  rw [integral_finsetSum _ hint, Finset.sum_congr rfl fun v _ => hv v, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- **`eq:rooted-lipschitz`.**  `|ℛ_W(u) - ℛ_W(u')| ≤ 2m ‖u - u'‖₁` for rows `u, u'`. -/
theorem rooted_lipschitz (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {u u' : ℝ → ℝ} (hu : IsRow u) (hu' : IsRow u') :
    |totalRootedDensity H W u - totalRootedDensity H W u'|
      ≤ 2 * H.edgeFinset.card * ∫ y, |u y - u' y| ∂unitμ := by
  unfold totalRootedDensity
  rw [← Finset.sum_sub_distrib]
  calc |∑ v, (rootedDensity H W v u - rootedDensity H W v u')|
      ≤ ∑ v, |rootedDensity H W v u - rootedDensity H W v u'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, ((H.neighborFinset v).card : ℝ) * ∫ y, |u y - u' y| ∂unitμ :=
        Finset.sum_le_sum fun v _ => abs_rootedDensity_sub_le H W v hu hu'
    _ = 2 * H.edgeFinset.card * ∫ y, |u y - u' y| ∂unitμ := by
        rw [← Finset.sum_mul, sum_card_neighborFinset]

/-- **The gradient at a row of `W`.**  `∇ℛ_W(W_x)(y) = 2𝒟_W(x,y)` for almost every `(x,y)`;
this identifies `eq:rooted-gradient-kernel` at `u = W_x` with `eq:derivative-kernel`. -/
theorem rootedGradient_row (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) :
    ∀ᵐ z ∂gμ, rootedGradient H W (W.row z.1) z.2 = 2 * derivKernel H W z.1 z.2 := by
  refine ae_of_all _ fun z => ?_
  rw [rootedGradient, derivKernel_eq_sum, ← mul_assoc, show (2:ℝ) * (1 / 2) = 1 by norm_num,
    one_mul]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun z₀ hz₀ =>
    rootedGradientTerm_row H W hz₀ z.1 z.2

end UpperTailMultipodality
