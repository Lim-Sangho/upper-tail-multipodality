import UpperTailMultipodality.FixedDensities.Support.OrderedWindow

/-!
# Ordered minimizers are nondegenerate (`lem:ordered-nondegenerate`)

A minimizer of `eq:fixed-problem` at an interior value of `τ` that has a representative
nondecreasing in each variable satisfies the constraint qualification.

Suppose not.  By `lem:degenerate-forms` there is a constant `a` with `𝒟_W = a` almost everywhere
on `Ω = {0 < W < 1}`, and `lem:degenerate-insertion` then says that almost every row `u = W_x`
maximizes `𝒢_W(u) = ℛ_W(u) - 2a∫u` over all rows.  Since `𝒢_W` differs from `ℛ_W` by a linear
term, the even second difference

`ℛ_W(u + h) + ℛ_W(u - h) - 2ℛ_W(u) ≤ 0`

for every admissible direction `h`.  Taking `h := min(u, 1-u)`, which keeps `u ± h` in `[0,1]`
without any uniform bound on `u`, `rooted_two_sided` bounds the left-hand side below by the
contribution of one vertex `v₀` of degree at least `2` and one ordered pair of distinct
neighbours of `v₀`; that contribution is an integral of a nonnegative function, hence vanishes
almost everywhere.

Monotonicity provides the window on which the integrand is positive: if `f` is a monotone
representative of `W`, the set `{(x,y) : x ≤ y, 0 < f(x,y) < 1}` has positive measure, so some
row index `x` has a positive-measure set `B` of `y ≥ x` with `0 < W(x,y) < 1`, and then
`f(y,y') ≥ f(x,y') > 0` for `y, y' ∈ B`.  On `B^{V(H)}` the integrand is therefore positive, a
contradiction.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:ordered-nondegenerate`.**  A maximizer of `eq:entropy-maximization` at an interior
value of `τ` that has ordered rows — `def:ordered-structure` with the relabelling already
applied — satisfies the constraint qualification `def:constraint-qualification`. -/
theorem ordered_nondegenerate (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hord : HasOrderedRows W) :
    ConstraintQualification H W := by
  by_contra hdeg
  obtain ⟨he, ht, hI⟩ := (isEntropyMaximizer_iff H hε0 hε1 W).mp hW
  obtain ⟨v₀, hv₀⟩ := id hΔ
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ :
      ∃ p ∈ H.neighborFinset v₀, ∃ q ∈ H.neighborFinset v₀, p ≠ q := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hv₀
    exact Finset.one_lt_card.mp (by omega)
  -- the constant of `lem:degenerate-forms` and the insertion inequality
  obtain ⟨η₀, hη₀0, hη₀pos⟩ := exists_interior_window H hε0 hε1 hτ0.le hτ1 ⟨he, ht, hI⟩
  obtain ⟨a, ha⟩ := exists_deriv_const_on_interior H W hdeg hη₀0 hη₀pos
  obtain ⟨hBle, hBrow⟩ := degenerate_insertion H hΔ hε0 hε1 hτ0 hτ1 hW hdeg ha
  have hmax : ∀ᵐ x ∂unitμ, ∀ u' : ℝ → ℝ, IsRow u' →
      totalRootedDensity H W u' - 2 * a * (∫ y, u' y ∂unitμ)
        ≤ totalRootedDensity H W (W.row x) - 2 * a * (∫ y, W.row x y ∂unitμ) := by
    filter_upwards [hBrow] with x hx u' hu'
    have h1 := hBle u' hu'
    linarith
  -- the monotone representative and the interior window on the upper triangle
  obtain ⟨f, hWf⟩ := hord
  have hfmeas : Measurable fun z : ℝ × ℝ => f.toFun z.1 z.2 := f.meas'
  have hΩW : gμ {z : ℝ × ℝ | 0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1} ≠ 0 := by
    intro hz
    refine hη₀pos (measure_mono_null (fun z hz' => ?_) hz)
    have h : η₀ < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η₀ := hz'
    exact ⟨lt_trans hη₀0 h.1, by linarith [h.2]⟩
  have hΩ'pos : gμ {z : ℝ × ℝ | 0 < f.toFun z.1 z.2 ∧ f.toFun z.1 z.2 < 1} ≠ 0 := by
    intro hz
    refine hΩW (measure_mono_null (fun z hz' => ?_) (measure_union_null hz (ae_iff.mp hWf)))
    by_cases hfz : W.toFun z.1 z.2 = f.toFun z.1 z.2
    · refine Or.inl ?_
      show 0 < f.toFun z.1 z.2 ∧ f.toFun z.1 z.2 < 1
      rw [← hfz]
      exact hz'
    · exact Or.inr hfz
  obtain ⟨Ωle, hΩledef⟩ : ∃ S : Set (ℝ × ℝ), S =
      {z : ℝ × ℝ | (0 < f.toFun z.1 z.2 ∧ f.toFun z.1 z.2 < 1) ∧ z.1 ≤ z.2} := ⟨_, rfl⟩
  have hΩlem : MeasurableSet Ωle := by
    rw [hΩledef]
    exact ((measurableSet_lt measurable_const hfmeas).inter
        (measurableSet_lt hfmeas measurable_const)).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hswap : gμ (Prod.swap ⁻¹' Ωle) = gμ Ωle :=
    (MeasureTheory.Measure.measurePreserving_swap).measure_preimage hΩlem.nullMeasurableSet
  have hΩlepos : gμ Ωle ≠ 0 := by
    intro hz
    refine hΩ'pos (measure_mono_null (fun z hz' => ?_)
      (measure_union_null hz (by rw [hswap]; exact hz)))
    have hz'' : 0 < f.toFun z.1 z.2 ∧ f.toFun z.1 z.2 < 1 := hz'
    rcases le_total z.1 z.2 with hle | hle
    · exact Or.inl (by rw [hΩledef]; exact ⟨hz'', hle⟩)
    · refine Or.inr ?_
      rw [Set.mem_preimage, hΩledef]
      refine ⟨?_, hle⟩
      show 0 < f.toFun z.2 z.1 ∧ f.toFun z.2 z.1 < 1
      rw [f.symm' z.2 z.1]
      exact hz''
  -- a positive-measure set of row indices with a positive-measure window above the diagonal
  have hX : unitμ {x : ℝ | unitμ (Prod.mk x ⁻¹' Ωle) ≠ 0} ≠ 0 := by
    intro hz
    have hae : ∀ᵐ x ∂unitμ, unitμ (Prod.mk x ⁻¹' Ωle) = 0 := by rw [ae_iff]; exact hz
    refine hΩlepos ?_
    calc gμ Ωle = ∫⁻ x, unitμ (Prod.mk x ⁻¹' Ωle) ∂unitμ := Measure.prod_apply hΩlem
      _ = ∫⁻ _x : ℝ, (0 : ENNReal) ∂unitμ := lintegral_congr_ae (hae.mono fun x hx => hx)
      _ = 0 := by simp
  have hgood : ∀ᵐ x ∂unitμ, (∀ u' : ℝ → ℝ, IsRow u' →
        totalRootedDensity H W u' - 2 * a * (∫ y, u' y ∂unitμ)
          ≤ totalRootedDensity H W (W.row x) - 2 * a * (∫ y, W.row x y ∂unitμ))
      ∧ (∀ᵐ y ∂unitμ, W.toFun x y = f.toFun x y) := by
    filter_upwards [hmax, Measure.ae_ae_of_ae_prod hWf] with x h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨x, hxX, hxmax, hxf⟩ := exists_mem_of_measure_ne_zero' hX hgood
  obtain ⟨u, hudef⟩ : ∃ w : ℝ → ℝ, w = W.row x := ⟨_, rfl⟩
  have hu : IsRow u := hudef ▸ isRow_row W x
  -- the window `B` of columns
  obtain ⟨B, hBdef⟩ : ∃ S : Set ℝ,
      S = (Prod.mk x ⁻¹' Ωle) ∩ {y | W.toFun x y = f.toFun x y} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact (measurable_prodMk_left hΩlem).inter
      (measurableSet_eq_fun (W.meas'.comp measurable_prodMk_left)
        (f.meas'.comp measurable_prodMk_left))
  have hB0 : unitμ B ≠ 0 := by
    intro hz
    refine hxX (measure_mono_null (fun y hy => ?_) (measure_union_null hz (ae_iff.mp hxf)))
    by_cases hfy : W.toFun x y = f.toFun x y
    · exact Or.inl (by rw [hBdef]; exact ⟨hy, hfy⟩)
    · exact Or.inr hfy
  have hBprop : ∀ y ∈ B, (0 < u y ∧ u y < 1) ∧ x ≤ y := by
    intro y hy
    rw [hBdef] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Set.mem_preimage, hΩledef] at hy1
    have hy1' : (0 < f.toFun x y ∧ f.toFun x y < 1) ∧ x ≤ y := hy1
    refine ⟨?_, hy1'.2⟩
    rw [hudef]
    show 0 < W.toFun x y ∧ W.toFun x y < 1
    rw [hy2]
    exact hy1'.1
  have hfpos : ∀ y ∈ B, 0 < f.toFun x y := by
    intro y hy
    rw [hBdef] at hy
    have h := hy.1
    rw [Set.mem_preimage, hΩledef] at h
    have h' : (0 < f.toFun x y ∧ f.toFun x y < 1) ∧ x ≤ y := h
    exact h'.1.1
  have hWpos : ∀ᵐ z ∂gμ, z.1 ∈ B → z.2 ∈ B → 0 < W.toFun z.1 z.2 := by
    filter_upwards [hWf] with z hz h1 h2
    rw [hz]
    calc (0:ℝ) < f.toFun x z.2 := hfpos z.2 h2
      _ ≤ f.toFun z.1 z.2 := f.mono' z.2 (hBprop z.1 h1).2
  -- the admissible direction `min(u, 1-u)`
  obtain ⟨d, hddef⟩ : ∃ w : ℝ → ℝ, w = fun y => min (u y) (1 - u y) := ⟨_, rfl⟩
  have hdval : ∀ y, d y = min (u y) (1 - u y) := by intro y; rw [hddef]
  have hdmin0 : ∀ y, 0 ≤ min (u y) (1 - u y) := fun y =>
    le_min (hu.2 y).1 (by linarith [(hu.2 y).2])
  have hd : IsRow d := by
    refine ⟨?_, fun y => ?_⟩
    · rw [hddef]; exact hu.1.min (measurable_const.sub hu.1)
    · rw [hdval y]
      exact ⟨hdmin0 y, le_trans (min_le_left _ _) (hu.2 y).2⟩
  have hdpos : ∀ y ∈ B, 0 < d y := by
    intro y hy
    rw [hdval y]
    obtain ⟨⟨h1, h2⟩, -⟩ := hBprop y hy
    exact lt_min h1 (by linarith)
  obtain ⟨ut, hutdef⟩ : ∃ w : ℝ → ℝ, w = fun y => u y + (1:ℝ) * d y := ⟨_, rfl⟩
  obtain ⟨um, humdef⟩ : ∃ w : ℝ → ℝ, w = fun y => u y + (-1:ℝ) * d y := ⟨_, rfl⟩
  have hutv : ∀ y, ut y = u y + (1:ℝ) * d y := by intro y; rw [hutdef]
  have humv : ∀ y, um y = u y + (-1:ℝ) * d y := by intro y; rw [humdef]
  have hut : IsRow ut := by
    refine ⟨?_, fun y => ?_⟩
    · rw [hutdef]; exact hu.1.add (hd.1.const_mul 1)
    · rw [hutv y, hdval y]
      have h1 := hu.2 y
      have hmin1 : min (u y) (1 - u y) ≤ 1 - u y := min_le_right _ _
      exact ⟨by linarith [hdmin0 y, h1.1], by linarith⟩
  have hum : IsRow um := by
    refine ⟨?_, fun y => ?_⟩
    · rw [humdef]; exact hu.1.add (hd.1.const_mul (-1))
    · rw [humv y, hdval y]
      have h1 := hu.2 y
      have hmin2 : min (u y) (1 - u y) ≤ u y := min_le_left _ _
      exact ⟨by linarith, by linarith [hdmin0 y, h1.2]⟩
  -- the second difference is nonpositive
  have hintsum : (∫ y, ut y ∂unitμ) + ∫ y, um y ∂unitμ = 2 * ∫ y, u y ∂unitμ := by
    have hiut : Integrable ut unitμ := integrable_of_abs_le hut.1 1 fun y => by
      rw [abs_of_nonneg (hut.2 y).1]; exact (hut.2 y).2
    have hium : Integrable um unitμ := integrable_of_abs_le hum.1 1 fun y => by
      rw [abs_of_nonneg (hum.2 y).1]; exact (hum.2 y).2
    rw [← integral_add hiut hium]
    have hpt : ∀ y, ut y + um y = 2 * u y := fun y => by rw [hutv y, humv y]; ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  have hΔ0 : totalRootedDensity H W ut + totalRootedDensity H W um
      - 2 * totalRootedDensity H W u ≤ 0 := by
    have h1 := hxmax ut hut
    have h2 := hxmax um hum
    rw [← hudef] at h1 h2
    have h3 : 2 * a * ((∫ y, ut y ∂unitμ) + ∫ y, um y ∂unitμ)
        = 2 * a * (2 * ∫ y, u y ∂unitμ) := by rw [hintsum]
    linarith
  -- the quadratic contribution of `v₀` vanishes
  obtain ⟨G, hGval⟩ : ∃ G : (V → ℝ) → ℝ, ∀ ξ : V → ℝ, G ξ =
      2 * (1:ℝ) ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), d (ξ z))
          * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z))
        * avoidingProduct H W v₀ ξ := ⟨_, fun _ => rfl⟩
  have hGle : ∫ ξ, G ξ ∂(Measure.pi fun _ : V => unitμ)
      ≤ totalRootedDensity H W ut + totalRootedDensity H W um
        - 2 * totalRootedDensity H W u := by
    rw [integral_congr_ae (ae_of_all _ hGval)]
    exact rooted_two_sided H W hu hd hut hum hutv humv v₀ hz₁ hz₂ hne
  have hGnn : ∀ ξ : V → ℝ, 0 ≤ G ξ := by
    intro ξ
    rw [hGval ξ]
    have h1 : 0 ≤ ∏ z ∈ ({z₁, z₂} : Finset V), d (ξ z) :=
      Finset.prod_nonneg fun z _ => (hd.2 (ξ z)).1
    have h2 : 0 ≤ ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z) :=
      Finset.prod_nonneg fun z _ => (hu.2 (ξ z)).1
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg h1 h2))
      (avoidingProduct_mem_Icc H W v₀ ξ).1
  have hGint : Integrable G (Measure.pi fun _ : V => unitμ) := by
    have hb : IsBddMeas fun ξ : V → ℝ =>
        2 * (1:ℝ) ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), d (ξ z))
            * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z))
          * avoidingProduct H W v₀ ξ :=
      ((IsBddMeas.const (2 * (1:ℝ) ^ 2)).mul
        ((IsBddMeas.finset_prod _ fun z _ =>
            (IsBddMeas.of_mem_Icc hd.1 hd.2).comp (measurable_pi_apply z)).mul
          (IsBddMeas.finset_prod _ fun z _ =>
            (IsBddMeas.of_mem_Icc hu.1 hu.2).comp (measurable_pi_apply z)))).mul
        (isBddMeas_avoidingProduct H W v₀)
    exact hb.integrable.congr (Eventually.of_forall fun ξ => (hGval ξ).symm)
  have hGzero : ∫ ξ, G ξ ∂(Measure.pi fun _ : V => unitμ) = 0 :=
    le_antisymm (le_trans hGle hΔ0) (integral_nonneg hGnn)
  have hGae : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ), G ξ = 0 :=
    (integral_eq_zero_iff_of_nonneg hGnn hGint).mp hGzero
  -- but the integrand is positive on `B^{V(H)}`
  have hGpos : ∀ ξ : V → ℝ, (∀ z, ξ z ∈ B) →
      (∀ e ∈ H.edgeFinset.filter (fun e => v₀ ∉ e), 0 < edgeVal W.toFun W.symm' ξ e) →
      0 < G ξ := by
    intro ξ hall hedgepos
    rw [hGval ξ]
    have h1 : 0 < ∏ z ∈ ({z₁, z₂} : Finset V), d (ξ z) :=
      Finset.prod_pos fun z _ => hdpos (ξ z) (hall z)
    have h2 : 0 < ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z) :=
      Finset.prod_pos fun z _ => (hBprop (ξ z) (hall z)).1.1
    have h3 : 0 < avoidingProduct H W v₀ ξ := by
      unfold avoidingProduct
      exact Finset.prod_pos hedgepos
    exact mul_pos (mul_pos (by norm_num) (mul_pos h1 h2)) h3
  have hedge : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ),
      (∀ z, ξ z ∈ B) →
        ∀ e ∈ H.edgeFinset.filter (fun e => v₀ ∉ e), 0 < edgeVal W.toFun W.symm' ξ e := by
    have hall : ∀ᵐ ξ ∂(Measure.pi fun _ : V => unitμ),
        ∀ e ∈ H.edgeFinset.filter (fun e => v₀ ∉ e),
          (∀ z, ξ z ∈ B) → 0 < edgeVal W.toFun W.symm' ξ e := by
      refine (Filter.eventually_all_finset _).mpr ?_
      intro e
      induction e using Sym2.ind with
      | _ p q =>
        intro hemem
        have hadj : H.Adj p q := H.mem_edgeFinset.mp (Finset.mem_filter.mp hemem).1
        filter_upwards [(measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae hWpos]
          with ξ hξ hallz
        exact hξ (hallz p) (hallz q)
    filter_upwards [hall] with ξ hξ hallz e hemem
    exact hξ e hemem hallz
  have hEnull : (Measure.pi fun _ : V => unitμ) {ξ : V → ℝ | ∀ z, ξ z ∈ B} = 0 := by
    have h1 : (Measure.pi fun _ : V => unitμ) {ξ : V → ℝ | ¬ G ξ = 0} = 0 := by
      rw [← ae_iff]; exact hGae
    have h2 : (Measure.pi fun _ : V => unitμ)
        {ξ : V → ℝ | ¬ ((∀ z, ξ z ∈ B) →
          ∀ e ∈ H.edgeFinset.filter (fun e => v₀ ∉ e),
            0 < edgeVal W.toFun W.symm' ξ e)} = 0 := by
      rw [← ae_iff]; exact hedge
    refine measure_mono_null (fun ξ hξ => ?_) (measure_union_null h1 h2)
    by_cases hg : G ξ = 0
    · by_cases hep : (∀ z, ξ z ∈ B) →
          ∀ e ∈ H.edgeFinset.filter (fun e => v₀ ∉ e), 0 < edgeVal W.toFun W.symm' ξ e
      · exact absurd hg (hGpos ξ hξ (hep hξ)).ne'
      · exact Or.inr hep
    · exact Or.inl hg
  have hEpos : (Measure.pi fun _ : V => unitμ) {ξ : V → ℝ | ∀ z, ξ z ∈ B} ≠ 0 := by
    have hpi : {ξ : V → ℝ | ∀ z, ξ z ∈ B} = Set.univ.pi fun _ : V => B := by ext ξ; simp
    rw [hpi, Measure.pi_pi, Finset.prod_const, Finset.card_univ]
    exact pow_ne_zero _ hB0
  exact hEpos hEnull

/-- **`lem:degenerate-forms`, in the paper's form.**  For a degenerate minimizer `W` of
`eq:fixed-problem`, the set `Ω = {0 < W < 1}` has positive measure, and there is a constant `a`
with `𝒟_{H,W} = a` almost everywhere on `Ω`.  The two halves are `exists_interior_window` and
`exists_deriv_const_on_interior`; `degenerate_forms` below is the dichotomy that
`lem:degenerate-smoothing` consumes. -/
theorem degenerate_interior_const (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card ≤ τ) (hτ1 : τ < tauMax H ε)
    {W : Graphon} (hW : IsFixedMinimizer H ε τ W) (hdeg : ¬ ConstraintQualification H W) :
    0 < gμ {z : ℝ × ℝ | 0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1} ∧
      ∃ a : ℝ, ∀ᵐ z ∂gμ, 0 < W.toFun z.1 z.2 → W.toFun z.1 z.2 < 1 →
        derivKernel H W z.1 z.2 = a := by
  obtain ⟨η, hη, hpos⟩ := exists_interior_window H hε0 hε1 hτ0 hτ1 hW
  refine ⟨lt_of_lt_of_le (zero_lt_iff.mpr hpos) (measure_mono fun z hz => ?_),
    exists_deriv_const_on_interior H W hdeg hη hpos⟩
  exact ⟨hη.trans hz.1, hz.2.trans (by linarith)⟩

end UpperTailMultipodality
