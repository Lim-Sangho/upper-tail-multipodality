import UpperTailMultipodality.RowCriterion.Defs

/-!
# Resampling one coordinate of a product measure, and the rooted-density integrands

Measure-theoretic tools for `sec:row-criterion`:

* `measurePreserving_update` — `(ξ, y) ↦ Function.update ξ w y` pushes `π ⊗ unitμ` forward to
  `π = Measure.pi fun _ => unitμ`;
* `integral_mul_update` — the resampling identity
  `∫ (∫ F(update ξ w y) dξ) h(y) dy = ∫ h(ξ_w) F(ξ) dξ`;
* `integral_eval_mul_eval` — `∫ f(ξ_a) g(ξ_b) dξ = ∫ f ∫ g` for `a ≠ b`;
* measurability and bounds for the integrands of `rootedDensity` and `rootedGradientTerm`.
-/

namespace UpperTailMultipodality.Rows

open MeasureTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Resampling one coordinate -/

omit [Fintype V] in
/-- `(ξ, y) ↦ Function.update ξ w y` is measurable. -/
theorem measurable_update_pair (w : V) :
    Measurable (fun p : (V → ℝ) × ℝ => Function.update p.1 w p.2) :=
  measurable_update'

/-- **Resampling one coordinate preserves the product measure**: the map
`(ξ, y) ↦ Function.update ξ w y` pushes `π ⊗ unitμ` forward to `π`. -/
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

/-- The partially integrated function `y ↦ ∫ F(update ξ w y) dξ` is measurable. -/
theorem measurable_integral_update (w : V) {F : (V → ℝ) → ℝ} (hF : Measurable F) :
    Measurable (fun y : ℝ => ∫ ξ, F (Function.update ξ w y) ∂(Measure.pi fun _ : V => unitμ)) := by
  have h : StronglyMeasurable (fun p : (V → ℝ) × ℝ => F (Function.update p.1 w p.2)) :=
    (hF.comp (measurable_update_pair w)).stronglyMeasurable
  exact h.integral_prod_left'.measurable

/-- A bound on `F` bounds the partially integrated function `y ↦ ∫ F(update ξ w y) dξ`. -/
theorem abs_integral_update_le (w : V) {F : (V → ℝ) → ℝ} {C : ℝ} (hb : ∀ ξ, |F ξ| ≤ C)
    (y : ℝ) :
    |∫ ξ, F (Function.update ξ w y) ∂(Measure.pi fun _ : V => unitμ)| ≤ C := by
  have hnorm : ‖∫ ξ, F (Function.update ξ w y) ∂(Measure.pi fun _ : V => unitμ)‖
      ≤ C * (Measure.pi fun _ : V => unitμ).real Set.univ :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun ξ => by simpa [Real.norm_eq_abs] using hb _)
  have huniv : C * (Measure.pi fun _ : V => unitμ).real Set.univ = C := by
    simp [measureReal_def]
  rw [huniv] at hnorm
  simpa [Real.norm_eq_abs] using hnorm

/-- **The resampling identity.**  For bounded measurable `F` and `h`,
`∫ (∫ F(update ξ w y) dξ) h(y) dy = ∫ h(ξ_w) F(ξ) dξ`. -/
theorem integral_mul_update (w : V) {F : (V → ℝ) → ℝ} {h : ℝ → ℝ} (hF : Measurable F)
    (hh : Measurable h) {C D : ℝ} (hbF : ∀ ξ, |F ξ| ≤ C) (hbh : ∀ y, |h y| ≤ D) :
    ∫ y, (∫ ξ, F (Function.update ξ w y) ∂(Measure.pi fun _ : V => unitμ)) * h y ∂unitμ
      = ∫ ξ, h (ξ w) * F ξ ∂(Measure.pi fun _ : V => unitμ) := by
  have hmp := measurePreserving_update (V := V) w
  have hG : Measurable fun ξ : V → ℝ => h (ξ w) * F ξ :=
    (hh.comp (measurable_pi_apply w)).mul hF
  have hint : Integrable (fun p : (V → ℝ) × ℝ => h p.2 * F (Function.update p.1 w p.2))
      ((Measure.pi fun _ : V => unitμ).prod unitμ) := by
    refine integrable_of_abs_le ((hh.comp measurable_snd).mul
      (hF.comp (measurable_update_pair w))) (D * C) fun p => ?_
    rw [abs_mul]
    exact mul_le_mul (hbh _) (hbF _) (abs_nonneg _) ((abs_nonneg _).trans (hbh p.2))
  have step1 : ∫ ξ, h (ξ w) * F ξ ∂(Measure.pi fun _ : V => unitμ)
      = ∫ p, h p.2 * F (Function.update p.1 w p.2)
          ∂((Measure.pi fun _ : V => unitμ).prod unitμ) := by
    conv_lhs => rw [← hmp.map_eq]
    rw [integral_map (measurable_update_pair w).aemeasurable hG.aestronglyMeasurable]
    simp
  rw [step1, integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_const_mul, mul_comm]

/-! ## Two coordinates and one coordinate -/

/-- **Independence of two coordinates.**  For `a ≠ b` and bounded measurable `f`, `g`,
`∫ f(ξ_a) g(ξ_b) dξ = ∫ f · ∫ g`. -/
theorem integral_eval_mul_eval {a b : V} (hab : a ≠ b) {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) :
    ∫ ξ, f (ξ a) * g (ξ b) ∂(Measure.pi fun _ : V => unitμ)
      = (∫ y, f y ∂unitμ) * ∫ y, g y ∂unitμ := by
  have hmp := measurePreserving_pair (V := V) hab
  have hm : Measurable fun z : ℝ × ℝ => f z.1 * g z.2 :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun ξ : V → ℝ => (ξ a, ξ b)) hmp.measurable.aemeasurable
    (f := fun z : ℝ × ℝ => f z.1 * g z.2) (by rw [hmp.map_eq]; exact hm.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  rw [← h]
  exact integral_prod_mul f g

omit [DecidableEq V] in
/-- An almost-everywhere statement about one coordinate transfers to `π`. -/
theorem ae_eval {p : ℝ → Prop} (h : ∀ᵐ y ∂unitμ, p y) (a : V) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), p (ξ a) :=
  (measurePreserving_eval (μ := fun _ : V => unitμ) a).quasiMeasurePreserving.ae h

/-- An almost-everywhere statement about a pair of coordinates transfers to `π`. -/
theorem ae_eval_pair {p : ℝ → ℝ → Prop} (h : ∀ᵐ z ∂gμ, p z.1 z.2) {a b : V} (hab : a ≠ b) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), p (ξ a) (ξ b) :=
  (measurePreserving_pair (V := V) hab).quasiMeasurePreserving.ae h

/-! ## The integrands of rooted densities -/

omit [Fintype V] [DecidableEq V] in
/-- An edge factor of a graphon is measurable in the vertex assignment. -/
theorem measurable_edgeVal (W : Graphon) (e : Sym2 V) :
    Measurable (fun ξ : V → ℝ => edgeVal W.toFun W.symm' ξ e) :=
  measurable_liftEdge W e

omit [Fintype V] [DecidableEq V] in
/-- An edge factor of a graphon lies in `[0,1]`. -/
theorem edgeVal_mem_Icc (W : Graphon) (ξ : V → ℝ) (e : Sym2 V) :
    edgeVal W.toFun W.symm' ξ e ∈ Set.Icc (0:ℝ) 1 :=
  liftEdge_mem_Icc W ξ e

/-- If `W ≥ ω` almost everywhere, then `avoidingProduct ≥ ω^k` almost everywhere, where `k` is
the number of edges avoiding `v`. -/
theorem avoidingProduct_ge (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) {ω : ℝ} (hω : 0 ≤ ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) :
    ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ),
      ω ^ (H.edgeFinset.filter (fun e => v ∉ e)).card ≤ avoidingProduct H W v ξ := by
  have hedge : ∀ e ∈ H.edgeFinset.filter (fun e => v ∉ e),
      ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), ω ≤ edgeVal W.toFun W.symm' ξ e := by
    intro e he
    have he' : e ∈ H.edgeFinset := (Finset.mem_filter.mp he).1
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
      exact ae_eval_pair (p := fun x y => ω ≤ W.toFun x y) hWω hadj.ne
  filter_upwards [(eventually_all_finset _).mpr hedge] with ξ hξ
  rw [avoidingProduct, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => hω) hξ

omit [DecidableEq V] in
/-- A bounded measurable function is integrable for `π`. -/
theorem integrable_pi_of_abs_le {F : (V → ℝ) → ℝ} (hF : Measurable F) (C : ℝ)
    (hb : ∀ ξ, |F ξ| ≤ C) : Integrable F (Measure.pi fun _ : V => unitμ) :=
  integrable_of_abs_le hF C hb

/-- A row is bounded measurable, hence integrable. -/
theorem integrable_of_isRow {u : ℝ → ℝ} (hu : IsRow u) : Integrable u unitμ :=
  integrable_of_abs_le hu.1 1 fun y => by
    rw [abs_of_nonneg (hu.2 y).1]; exact (hu.2 y).2

/-- The rooted-density integrand of a row lies in `[0,1]`. -/
theorem rootedIntegrand_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) (v : V)
    {u : ℝ → ℝ} (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) (S : Finset V) (ξ ξ' : V → ℝ) :
    (∏ z ∈ S, u (ξ z)) * avoidingProduct H W v ξ' ∈ Set.Icc (0:ℝ) 1 := by
  have hP : (∏ z ∈ S, u (ξ z)) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Finset.prod_nonneg fun z _ => (hu _).1,
      Finset.prod_le_one (fun z _ => (hu _).1) (fun z _ => (hu _).2)⟩
  have hA := avoidingProduct_mem_Icc H W v ξ'
  exact ⟨mul_nonneg hP.1 hA.1, mul_le_one₀ hP.2 hA.1 hA.2⟩

/-- The rooted-density integrand of a measurable function is measurable. -/
theorem measurable_rootedIntegrand (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) {u : ℝ → ℝ} (hu : Measurable u) (S : Finset V) :
    Measurable (fun ξ : V → ℝ => (∏ z ∈ S, u (ξ z)) * avoidingProduct H W v ξ) :=
  (Finset.measurable_prod _ fun z _ => hu.comp (measurable_pi_apply z)).mul
    (measurable_avoidingProduct H W v)

/-- The rooted-density integrand of a row is integrable. -/
theorem integrable_rootedIntegrand (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v : V) {u : ℝ → ℝ} (hu : IsRow u) (S : Finset V) :
    Integrable (fun ξ : V → ℝ => (∏ z ∈ S, u (ξ z)) * avoidingProduct H W v ξ)
      (Measure.pi fun _ : V => unitμ) :=
  integrable_pi_of_abs_le (measurable_rootedIntegrand H W v hu.1 S) 1 fun ξ => by
    have h := rootedIntegrand_mem_Icc H W v hu.2 S ξ ξ
    rw [abs_of_nonneg h.1]; exact h.2

/-- `G_{v,z₀}(u)` is measurable for measurable `u`. -/
theorem measurable_rootedGradientTerm (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v z₀ : V) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (rootedGradientTerm H W v z₀ u) :=
  measurable_integral_update z₀
    (F := fun ξ => (∏ z ∈ (H.neighborFinset v).erase z₀, u (ξ z)) * avoidingProduct H W v ξ)
    (measurable_rootedIntegrand H W v hu _)

/-- `0 ≤ G_{v,z₀}(u) ≤ 1` for a row `u`. -/
theorem rootedGradientTerm_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (v z₀ : V) {u : ℝ → ℝ} (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) (y : ℝ) :
    rootedGradientTerm H W v z₀ u y ∈ Set.Icc (0:ℝ) 1 := by
  have hb := fun ξ : V → ℝ => rootedIntegrand_mem_Icc H W v hu
    ((H.neighborFinset v).erase z₀) (Function.update ξ z₀ y) (Function.update ξ z₀ y)
  refine ⟨integral_nonneg fun ξ => (hb ξ).1, ?_⟩
  have h := abs_integral_update_le (V := V) z₀
    (F := fun ξ => (∏ z ∈ (H.neighborFinset v).erase z₀, u (ξ z)) * avoidingProduct H W v ξ)
    (C := 1) (fun ξ => by
      have h := rootedIntegrand_mem_Icc H W v hu ((H.neighborFinset v).erase z₀) ξ ξ
      rw [abs_of_nonneg h.1]; exact h.2) y
  exact (le_abs_self _).trans h

/-- `∇ℛ_W(u)` is measurable for measurable `u`. -/
theorem measurable_rootedGradient (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {u : ℝ → ℝ} (hu : Measurable u) : Measurable (rootedGradient H W u) := by
  unfold rootedGradient
  exact Finset.measurable_sum _ fun v _ => Finset.measurable_sum _ fun z₀ _ =>
    measurable_rootedGradientTerm H W v z₀ hu

/-- `0 ≤ ∇ℛ_W(u) ≤ ∑_v deg(v)` for a row `u`. -/
theorem rootedGradient_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {u : ℝ → ℝ} (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) (y : ℝ) :
    rootedGradient H W u y ∈ Set.Icc (0:ℝ) (∑ v, ((H.neighborFinset v).card : ℝ)) := by
  unfold rootedGradient
  refine ⟨Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun z₀ _ =>
    (rootedGradientTerm_mem_Icc H W v z₀ hu y).1, Finset.sum_le_sum fun v _ => ?_⟩
  calc ∑ z₀ ∈ H.neighborFinset v, rootedGradientTerm H W v z₀ u y
      ≤ ∑ _z₀ ∈ H.neighborFinset v, (1:ℝ) :=
        Finset.sum_le_sum fun z₀ _ => (rootedGradientTerm_mem_Icc H W v z₀ hu y).2
    _ = (H.neighborFinset v).card := by simp

/-! ## The combined gradient -/

section Combined

variable {ι : Type*} [Fintype ι]

/-- `∇𝒫_W(u)` is measurable for measurable `u`. -/
theorem measurable_combinedRootedGradient (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) (μ : ι → ℝ) {u : ℝ → ℝ}
    (hu : Measurable u) : Measurable (combinedRootedGradient Hs W μ u) := by
  unfold combinedRootedGradient
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_rootedGradient (Hs j) W hu).const_mul _

/-- **`eq:combined-lipschitz`**: `0 ≤ ∇𝒫_W(u) ≤ 2M_*` for a row `u` and weights `μ ≥ 0`. -/
theorem combinedRootedGradient_mem_Icc (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (W : Graphon) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    {u : ℝ → ℝ} (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) (y : ℝ) :
    combinedRootedGradient Hs W μ u y ∈ Set.Icc (0:ℝ) (2 * combinedEdgeCard Hs μ) := by
  unfold combinedRootedGradient
  refine ⟨Finset.sum_nonneg fun j _ =>
    mul_nonneg (hμ j) (rootedGradient_mem_Icc (Hs j) W hu y).1, ?_⟩
  rw [combinedEdgeCard, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := (rootedGradient_mem_Icc (Hs j) W hu y).2
  rw [sum_card_neighborFinset] at h
  calc μ j * rootedGradient (Hs j) W u y
      ≤ μ j * (2 * (Hs j).edgeFinset.card) := mul_le_mul_of_nonneg_left h (hμ j)
    _ = 2 * (μ j * (Hs j).edgeFinset.card) := by ring

end Combined

end UpperTailMultipodality.Rows
