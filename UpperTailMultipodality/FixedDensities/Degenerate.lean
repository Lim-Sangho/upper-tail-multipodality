import UpperTailMultipodality.FixedDensities.Monotone
import UpperTailMultipodality.FixedDensities.Support.Degenerate
import UpperTailMultipodality.FixedDensities.Support.InteriorWindow

/-!
# Degenerate maximizers occur only for a null set of values

`lem:degenerate-forms`, the smoothing estimate of `lem:degenerate-smoothing` and
`lem:degenerate-slope`.

Two notational conventions, kept throughout `FixedDensities/`.  The constant of
`lem:degenerate-forms`, which the paper calls `κ`, is written `a` or `c` here.  The smoothing
parameter of `W_θ = (1-θ)W + θε` is written `θ`, where the paper writes `s`, and the measure of
an inserted block is written `s`, where the paper writes `θ`: the two letters are exchanged.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology FixedDensities

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:degenerate-forms`.**  A degenerate minimizer either takes the values `0` or `1` on a
set of positive measure, or satisfies `0 < W < 1` almost everywhere and has an almost everywhere
constant derivative kernel. -/
theorem degenerate_forms (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hdeg : ¬ ConstraintQualification H W) :
    0 < gμ {z | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1} ∨
      ((∀ᵐ z ∂gμ, 0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1) ∧
        ∃ c : ℝ, ∀ᵐ z ∂gμ, derivKernel H W z.1 z.2 = c) := by
  -- only degeneracy enters: the normal forms hold for any graphon violating `def:constraint-qualification`
  obtain ⟨-, -⟩ := hΔ
  have _ := hτ0.trans hτ1
  have _ := hε0.trans hε1
  have _ := hW.1
  by_cases hB : 0 < gμ {z : ℝ × ℝ | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1}
  · exact Or.inl hB
  refine Or.inr ⟨?_, ?_⟩
  · rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (nonpos_iff_eq_zero.mp (not_lt.mp hB))
    have hz' : ¬ (0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1) := hz
    rcases not_and_or.mp hz' with h | h
    · exact Or.inl (le_antisymm (not_lt.mp h) (W.nonneg' _ _))
    · exact Or.inr (le_antisymm (W.le_one' _ _) (not_lt.mp h))
  -- the increasing exhaustion `Ω_{1/(n+2)}(W)` of `{0 < W < 1}`
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (ℝ × ℝ), ∀ n : ℕ, A n =
      {z : ℝ × ℝ | 1 / ((n : ℝ) + 2) < W.toFun z.1 z.2 ∧
        W.toFun z.1 z.2 < 1 - 1 / ((n : ℝ) + 2)} := ⟨_, fun n => rfl⟩
  have hηpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hmono : ∀ m n : ℕ, m ≤ n → A m ⊆ A n := by
    intro m n hmn z hz
    rw [hA m] at hz
    rw [hA n]
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have h : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact ⟨lt_of_le_of_lt h hz.1, lt_of_lt_of_le hz.2 (by linarith)⟩
  have hcover : ∀ᵐ z ∂gμ, ∃ n : ℕ, z ∈ A n := by
    have hint : ∀ᵐ z ∂gμ, 0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 := by
      rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) (nonpos_iff_eq_zero.mp (not_lt.mp hB))
      have hz' : ¬ (0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1) := hz
      rcases not_and_or.mp hz' with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (W.nonneg' _ _))
      · exact Or.inr (le_antisymm (W.le_one' _ _) (not_lt.mp h))
    filter_upwards [hint] with z hz
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (show 0 < min (W.toFun z.1 z.2) (1 - W.toFun z.1 z.2) by
        exact lt_min hz.1 (by linarith [hz.2]))
    refine ⟨n, ?_⟩
    have hle : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    rw [hA n]
    exact ⟨lt_of_le_of_lt hle (lt_of_lt_of_le hn (min_le_left _ _)),
      by linarith [lt_of_le_of_lt hle (lt_of_lt_of_le hn (min_le_right _ _))]⟩
  -- some `Ω_{1/(n+2)}(W)` has positive measure
  have hex : ∃ n : ℕ, gμ (A n) ≠ 0 := by
    by_contra hc
    have hall : ∀ n : ℕ, gμ (A n) = 0 := by
      intro n
      by_contra h
      exact hc ⟨n, h⟩
    have h1 : gμ (⋃ n, A n) = 0 := measure_iUnion_null hall
    have h2 : gμ (⋃ n, A n)ᶜ = 0 := by
      rw [← ae_iff.mp (hcover.mono fun z hz => Set.mem_iUnion.mpr hz)]
      rfl
    have := measure_union_null h1 h2
    rw [Set.union_compl_self] at this
    simp only [measure_univ] at this
    exact one_ne_zero this
  obtain ⟨n₀, hn₀⟩ := hex
  obtain ⟨c, hc⟩ := ae_const_on_of_not_cq H W hdeg (hηpos n₀) (by rw [← hA n₀]; exact hn₀)
  have hcA : ∀ᵐ z ∂gμ, z ∈ A n₀ → derivKernel H W z.1 z.2 = c := by
    filter_upwards [hc] with z hz hzA
    rw [hA n₀] at hzA
    exact hz hzA.1 hzA.2
  -- the constant does not depend on `n`
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂gμ, z ∈ A n → derivKernel H W z.1 z.2 = c := by
    intro n
    by_cases hAn : gμ (A n) = 0
    · have : ∀ᵐ z ∂gμ, z ∉ A n := by simpa [ae_iff] using hAn
      filter_upwards [this] with z hz hzA
      exact absurd hzA hz
    · have hmax : gμ (A n₀) ≠ 0 := hn₀
      have hsub : A n₀ ⊆ A (max n n₀) := hmono _ _ (le_max_right n n₀)
      have hposm : gμ (A (max n n₀)) ≠ 0 := fun h =>
        hmax (nonpos_iff_eq_zero.mp (h ▸ measure_mono hsub))
      obtain ⟨c', hc'⟩ := ae_const_on_of_not_cq H W hdeg (hηpos (max n n₀))
        (by rw [← hA (max n n₀)]; exact hposm)
      have hc'A : ∀ᵐ z ∂gμ, z ∈ A (max n n₀) → derivKernel H W z.1 z.2 = c' := by
        filter_upwards [hc'] with z hz hzA
        rw [hA (max n n₀)] at hzA
        exact hz hzA.1 hzA.2
      have hboth : ∀ᵐ z ∂gμ, z ∈ A n₀ →
          derivKernel H W z.1 z.2 = c ∧ derivKernel H W z.1 z.2 = c' := by
        filter_upwards [hcA, hc'A] with z h1 h2 hzA
        exact ⟨h1 hzA, h2 (hsub hzA)⟩
      have hcc' : c = c' := by
        obtain ⟨z, -, hz⟩ := exists_mem_of_measure_ne_zero hmax hboth
        rw [← hz.1, hz.2]
      filter_upwards [hc'A] with z hz hzA
      rw [hz (hmono _ _ (le_max_left n n₀) hzA), hcc']
  refine ⟨c, ?_⟩
  filter_upwards [(ae_all_iff.mpr hstep), hcover] with z h1 h2
  obtain ⟨n, hn⟩ := h2
  exact h1 n hn

/-- **The gain of the smoothing beats the deficit, `lem:degenerate-smoothing`.**  For every
constant `C` and all small `θ > 0`, the mixed graphon `W_θ = (1-θ)W + θε` satisfies
`t(H,W_θ) < τ` and `C (τ - t(H,W_θ)) < I_ε(W) - I_ε(W_θ)`. -/
theorem degenerate_gain (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hdeg : ¬ ConstraintQualification H W) (C : ℝ) :
    ∀ᶠ θ in 𝓝[>] (0:ℝ), ∀ Y : Graphon,
      (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) →
        0 < τ - Y.tDensity H ∧ C * (τ - Y.tDensity H) < W.Ip ε - Y.Ip ε := by
  obtain ⟨he, ht, hI⟩ := (isEntropyMaximizer_iff H hε0 hε1 W).mp hW
  have hIpos : 0 < W.Ip ε :=
    Ip_pos_of_tDensity_ne H W hε0 hε1 (by rw [ht]; exact hτ0.ne')
  obtain ⟨U, hU⟩ : ∃ U : Kernel, U = constSubKernel W ε := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, ∀ θ : ℝ, f θ = (Kernel.ofGraphon W + θ • U).tDensity H :=
    ⟨_, fun _ => rfl⟩
  have hf0 : f 0 = τ := by
    rw [hfdef, ← ht, ← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  -- every graphon with the mixing values has the same `H`-density and at most the mixing cost
  have hYt : ∀ θ : ℝ, ∀ Y : Graphon,
      (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) → Y.tDensity H = f θ := by
    intro θ Y hY
    rw [hfdef, ← Kernel.tDensity_ofGraphon]
    refine kernel_tDensity_congr H fun x y => ?_
    rw [hU]
    show Y.toFun x y = W.toFun x y + θ * (ε - W.toFun x y)
    rw [hY x y]; ring
  have hYI : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ Y : Graphon,
      (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) → Y.Ip ε ≤ (1 - θ) * W.Ip ε := by
    intro θ h0 h1 Y hY
    obtain ⟨Y', hY'1, -, -, hY'4⟩ := exists_mix H W hε0 hε1 h0 h1 he
    have hsame : Y.Ip ε = Y'.Ip ε :=
      integral_congr_ae (ae_of_all _ fun z => by
        show Jp ε (Y.toFun z.1 z.2) = Jp ε (Y'.toFun z.1 z.2)
        rw [hY z.1 z.2, hY'1 z.1 z.2])
    rw [hsame]; exact hY'4
  have hlt : ∀ θ : ℝ, 0 < θ → θ < 1 → f θ < τ := by
    intro θ h0 h1
    obtain ⟨Y, hY1, hY2, -, -⟩ := exists_mix H W hε0 hε1 h0.le h1.le he
    by_contra hc
    have hge : τ ≤ Y.tDensity H := by rw [hYt θ Y hY1]; exact not_lt.mp hc
    have hmin := (fixed_monotone H hΔ hε0 hε1).2 τ ⟨hτ0, hτ1⟩ W he ht hI Y hY2 hge
    have hcost := hYI θ h0.le h1.le Y hY1
    nlinarith
  -- the Lipschitz bound `|t(H,W_θ) - τ| ≤ m θ`
  have hLip : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ Y : Graphon,
      (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) →
        |Y.tDensity H - τ| ≤ (H.edgeFinset.card : ℝ) * θ := by
    intro θ h0 h1 Y hY
    have h := abs_kernel_tDensity_sub_le H (K := Kernel.ofGraphon Y) (L := Kernel.ofGraphon W)
      (fun x y => Y.mem_Icc x y) (fun x y => W.mem_Icc x y) (c := θ) (fun x y => by
        show |Y.toFun x y - W.toFun x y| ≤ θ
        rw [hY x y]
        have h2 : (1 - θ) * W.toFun x y + θ * ε - W.toFun x y = θ * (ε - W.toFun x y) := by ring
        rw [h2, abs_mul, abs_of_nonneg h0]
        have h3 : |ε - W.toFun x y| ≤ 1 := by
          rw [abs_le]
          constructor <;> [linarith [W.le_one' x y, hε0]; linarith [W.nonneg' x y, hε1]]
        nlinarith)
    rw [Kernel.tDensity_ofGraphon, Kernel.tDensity_ofGraphon, ht] at h
    exact h
  -- the comparison used in both cases
  obtain ⟨C₀, hC₀def⟩ : ∃ c : ℝ, c = |C| + 1 := ⟨_, rfl⟩
  have hC₀0 : 0 < C₀ := by rw [hC₀def]; positivity
  have hCC₀ : C ≤ C₀ := by rw [hC₀def]; linarith [le_abs_self C]
  have key : ∀ d g db nb : ℝ, 0 < d → d ≤ db → nb ≤ g → C₀ * db < nb → C * d < g := by
    intro d g db nb hd hdb hnb hC
    have h1 : C * d ≤ C₀ * d := mul_le_mul_of_nonneg_right hCC₀ hd.le
    have h2 : C₀ * d ≤ C₀ * db := mul_le_mul_of_nonneg_left hdb hC₀0.le
    linarith
  rcases degenerate_forms H hΔ hε0 hε1 hτ0 hτ1 hW hdeg with hB | ⟨-, c₀, hc₀⟩
  · -- a positive measure of endpoint values: the `θ log(1/θ)` gain
    obtain ⟨β, hβ⟩ : ∃ β, β = gμ.real {z : ℝ × ℝ | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1} :=
      ⟨_, rfl⟩
    have hβ0 : 0 < β := by
      rw [hβ, measureReal_def]
      exact ENNReal.toReal_pos hB.ne' (measure_ne_top _ _)
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = min ε (1 - ε) := ⟨_, rfl⟩
    have hκ0 : 0 < κ := by rw [hκ]; exact lt_min hε0 (by linarith)
    obtain ⟨K, hK⟩ : ∃ K, K = (H.edgeFinset.card : ℝ) + 1 := ⟨_, rfl⟩
    have hK0 : 0 < K := by rw [hK]; positivity
    obtain ⟨t, htdef⟩ : ∃ t, t = (C₀ * K + 1) / (β * κ) := ⟨_, rfl⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num),
      Ioc_mem_nhdsGT (Real.exp_pos (-t))] with θ hθ hexp Y hY
    have hlog : t ≤ Real.log (1 / θ) := by
      have h1 : Real.log θ ≤ -t := by
        have h2 := Real.log_le_log hθ.1 hexp.2
        rwa [Real.log_exp] at h2
      rw [one_div, Real.log_inv]
      linarith
    have hlog0 : 0 ≤ Real.log (1 / θ) := by
      rw [one_div]
      exact Real.log_nonneg (by rw [le_inv_comm₀ one_pos hθ.1]; linarith [hθ.2])
    have hYtv : Y.tDensity H = f θ := hYt θ Y hY
    have hd0 : 0 < τ - Y.tDensity H := by rw [hYtv]; linarith [hlt θ hθ.1 hθ.2]
    refine ⟨hd0, ?_⟩
    have hdenb : τ - Y.tDensity H ≤ K * θ := by
      have h := hLip θ hθ.1.le hθ.2.le Y hY
      rw [abs_le] at h
      nlinarith [h.1, hθ.1]
    have hnum : β * (κ * (θ * Real.log (1 / θ))) ≤ W.Ip ε - Y.Ip ε := by
      have h := Ip_mix_gain W hε0 hε1 hθ.1 hθ.2 hY
      rw [← hβ, ← hκ] at h
      exact h
    have hbig : C₀ * (K * θ) < β * (κ * (θ * Real.log (1 / θ))) := by
      have h5 : C₀ * K + 1 ≤ β * κ * Real.log (1 / θ) := by
        have hβκ : 0 < β * κ := mul_pos hβ0 hκ0
        rw [htdef, div_le_iff₀ hβκ] at hlog
        nlinarith
      calc C₀ * (K * θ) = C₀ * K * θ := by ring
        _ < (β * κ * Real.log (1 / θ)) * θ := by nlinarith [hθ.1]
        _ = β * (κ * (θ * Real.log (1 / θ))) := by ring
    exact key _ _ _ _ hd0 hdenb hnum hbig
  · -- an almost everywhere constant derivative kernel: the quadratic bound
    have hv0 : (∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ) = 0 := by
      have hUint : ∫ z, U.toFun z.1 z.2 ∂gμ = 0 := by
        rw [hU]
        show ∫ z, (ε - W.toFun z.1 z.2) ∂gμ = 0
        rw [integral_sub (integrable_const ε) W.integrable_self, integral_const]
        simp only [smul_eq_mul, probReal_univ]
        rw [← Graphon.edgeDensity, he]
        ring
      rw [integral_congr_ae (hc₀.mono fun z hz => by rw [hz]), integral_const_mul, hUint,
        mul_zero]
    obtain ⟨K, hK0, hKev⟩ := tDensity_line_isBigO_sq H W U hv0
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = W.Ip ε / (C₀ * K + 1) := ⟨_, rfl⟩
    have hθ₀0 : 0 < θ₀ := by
      rw [hθ₀]
      have : 0 < C₀ * K + 1 := by positivity
      positivity
    filter_upwards [hKev.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num), Ioo_mem_nhdsGT hθ₀0] with θ hKθ hθ hθsmall Y hY
    have hYtv : Y.tDensity H = f θ := hYt θ Y hY
    have hd0 : 0 < τ - Y.tDensity H := by rw [hYtv]; linarith [hlt θ hθ.1 hθ.2]
    refine ⟨hd0, ?_⟩
    have hdenb : τ - Y.tDensity H ≤ K * θ ^ 2 := by
      rw [hYtv, hfdef θ, ← ht]
      rw [abs_le] at hKθ
      linarith [hKθ.1]
    have hnum : θ * W.Ip ε ≤ W.Ip ε - Y.Ip ε := by
      have h := hYI θ hθ.1.le hθ.2.le Y hY
      nlinarith
    have hbig : C₀ * (K * θ ^ 2) < θ * W.Ip ε := by
      have h1 : θ < W.Ip ε / (C₀ * K + 1) := hθ₀ ▸ hθsmall.2
      rw [lt_div_iff₀ (by positivity)] at h1
      calc C₀ * (K * θ ^ 2) = (C₀ * K) * θ * θ := by ring
        _ < θ * W.Ip ε := by nlinarith [hθ.1]
    exact key _ _ _ _ hd0 hdenb hnum hbig

/-- **`lem:degenerate-slope`.**  If `eq:fixed-problem` has a degenerate minimizer at `τ`, then the
left difference quotients of `Ψ_ε` at `τ` tend to infinity, so `Ψ_ε` has an infinite left
derivative there.  The bound is first proved along the smoothing path `θ ↦ t(H, (1-θ)W + θε)`,
and the intermediate value theorem then reaches every value slightly below `τ`. -/
theorem degenerate_slope (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hdeg : ¬ ConstraintQualification H W) :
    Tendsto (fun τ' => (fixedValue H ε τ - fixedValue H ε τ') / (τ - τ')) (𝓝[<] τ) atTop := by
  obtain ⟨he, ht, hI⟩ := (isEntropyMaximizer_iff H hε0 hε1 W).mp hW
  have hIpos : 0 < W.Ip ε :=
    Ip_pos_of_tDensity_ne H W hε0 hε1 (by rw [ht]; exact hτ0.ne')
  obtain ⟨U, hU⟩ : ∃ U : Kernel, U = constSubKernel W ε := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, ∀ θ : ℝ, f θ = (Kernel.ofGraphon W + θ • U).tDensity H :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = ∫ z, derivKernel H W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  have hfd : HasDerivAt f v 0 := by
    have h := first_variation H W U
    rw [← hv] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with θ
    rw [hfdef]
  have hf0 : f 0 = τ := by
    rw [hfdef, ← ht, ← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  -- the mixing path
  have hmix : ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ V : Graphon,
      (∀ x y, V.toFun x y = (1 - θ) * W.toFun x y + θ * ε) ∧ V.edgeDensity = ε ∧
        V.tDensity H = f θ ∧ V.Ip ε ≤ (1 - θ) * W.Ip ε := by
    intro θ h0 h1
    obtain ⟨V, hV1, hV2, hV3, hV4⟩ := exists_mix H W hε0 hε1 h0.le h1.le he
    exact ⟨V, hV1, hV2, by rw [hV3, hfdef, hU], hV4⟩
  have hlt : ∀ θ : ℝ, 0 < θ → θ < 1 → f θ < τ := by
    intro θ h0 h1
    obtain ⟨V, -, hV2, hV3, hV4⟩ := hmix θ h0 h1
    by_contra hc
    have hge : τ ≤ V.tDensity H := by rw [hV3]; exact not_lt.mp hc
    have := (fixed_monotone H hΔ hε0 hε1).2 τ ⟨hτ0, hτ1⟩ W he ht hI V hV2 hge
    nlinarith
  -- the difference-quotient bound from a lower bound on the cost gain
  have hfinal : ∀ C : ℝ, ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ V : Graphon, V.edgeDensity = ε →
      V.tDensity H = f θ → ∀ nb db : ℝ, 0 ≤ nb → nb ≤ W.Ip ε - V.Ip ε → 0 < db →
      τ - f θ ≤ db → C * db < nb →
      C < (fixedValue H ε τ - fixedValue H ε (f θ)) / (τ - f θ) := by
    intro C θ h0 h1 V hV2 hV3 nb db hnb0 hnb hdb0 hdb hC
    have hden : 0 < τ - f θ := by linarith [hlt θ h0 h1]
    have hle : fixedValue H ε (f θ) ≤ V.Ip ε := fixedValue_le H hε0 hε1 hV2 hV3
    have hnum : nb ≤ fixedValue H ε τ - fixedValue H ε (f θ) := by rw [← hI]; linarith
    calc C < nb / db := by rw [lt_div_iff₀ hdb0]; exact hC
      _ ≤ (fixedValue H ε τ - fixedValue H ε (f θ)) / (τ - f θ) :=
          div_le_div₀ (by linarith) hnum hden hdb
  rw [tendsto_atTop]
  intro C
  -- the bound along the smoothing path `θ ↦ f θ`
  have hev : ∀ᶠ θ in 𝓝[>] (0:ℝ),
      C < (fixedValue H ε τ - fixedValue H ε (f θ)) / (τ - f θ) := by
    filter_upwards [degenerate_gain H hΔ hε0 hε1 hτ0 hτ1 hW hdeg |C|,
      Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with θ hgain hθ
    obtain ⟨V, hV1, hV2, hV3, -⟩ := hmix θ hθ.1 hθ.2
    obtain ⟨hpos, hgt⟩ := hgain V hV1
    rw [hV3] at hpos hgt
    have hnn : 0 ≤ |C| * (τ - f θ) := mul_nonneg (abs_nonneg C) hpos.le
    have hCle : C * (τ - f θ) ≤ |C| * (τ - f θ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
    exact hfinal C θ hθ.1 hθ.2 V hV2 hV3 _ _ (by linarith) le_rfl hpos le_rfl (by linarith)
  -- `f` is continuous with `f 0 = τ`, so it attains every value slightly below `τ`
  have hcontf : Continuous f := by
    refine (continuous_tDensity_line H W U).congr fun θ => ?_
    rw [hfdef θ]
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0 : (0:ℝ) < u := hu
  obtain ⟨θ₂, hθ₂def⟩ : ∃ θ₂, θ₂ = min (u / 2) (1 / 2) := ⟨_, rfl⟩
  have hθ₂0 : 0 < θ₂ := by rw [hθ₂def]; exact lt_min (by linarith) (by norm_num)
  have hθ₂u : θ₂ < u := lt_of_le_of_lt (hθ₂def ▸ min_le_left _ _) (by linarith)
  have hθ₂1 : θ₂ < 1 := lt_of_le_of_lt (hθ₂def ▸ min_le_right _ _) (by norm_num)
  filter_upwards [Ioo_mem_nhdsLT (hlt θ₂ hθ₂0 hθ₂1)] with τ' hτ'
  have hsurj := intermediate_value_Ioo' hθ₂0.le hcontf.continuousOn
  rw [hf0] at hsurj
  obtain ⟨θ, hθmem, hθeq⟩ := hsurj hτ'
  have hbound : C < (fixedValue H ε τ - fixedValue H ε (f θ)) / (τ - f θ) :=
    hsub ⟨hθmem.1, hθmem.2.trans hθ₂u⟩
  rw [hθeq] at hbound
  exact hbound.le

/-- The form of `lem:degenerate-slope` used by `cor:almost-every-tau`: the left difference
quotients are unbounded. -/
theorem degenerate_slope_frequently (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ0 : ε ^ H.edgeFinset.card < τ) (hτ1 : τ < tauMax H ε) {W : Graphon}
    (hW : IsEntropyMaximizer H ε τ W) (hdeg : ¬ ConstraintQualification H W) :
    ∀ C : ℝ, ∃ᶠ τ' in 𝓝[<] τ,
      C < (fixedValue H ε τ - fixedValue H ε τ') / (τ - τ') := by
  intro C
  have h := degenerate_slope H hΔ hε0 hε1 hτ0 hτ1 hW hdeg
  rw [tendsto_atTop] at h
  exact ((h (C + 1)).mono fun τ' hτ' => by linarith).frequently

/-- **The first two assertions of `lem:degenerate-smoothing`.**  Along `W_θ = (1-θ)W + θε` the
cost saving `g_θ = I_ε(W) - I_ε(W_θ)` and the density loss `d_θ = τ - t(H,W_θ)` are positive for
every `0 < θ < 1`.  Degeneracy is not needed: convexity of `J_ε` with `J_ε(ε) = 0` gives
`I_ε(W_θ) ≤ (1-θ)I_ε(W) < I_ε(W)`, and `lem:fixed-monotonicity` then forces
`t(H,W_θ) < τ`, since otherwise `W_θ` would be a strictly better competitor. -/
theorem smoothing_pos (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hτ : τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) {W : Graphon}
    (hW : IsFixedMinimizer H ε τ W) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (Y : Graphon)
    (hY : ∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) :
    0 < W.Ip ε - Y.Ip ε ∧ 0 < τ - Y.tDensity H := by
  have hsmem : (1 - θ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  -- `Y` is the mixed graphon at parameter `1 - θ`
  have hYeq : Y = Wmix W ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) (1 - θ) hsmem := by
    refine Graphon.ext fun x y => ?_
    rw [hY, Wmix_apply]; ring
  have hIpos : 0 < W.Ip ε :=
    Ip_pos_of_tDensity_ne H W hε0 hε1 (by rw [hW.2.1]; exact hτ.1.ne')
  -- the cost strictly drops
  have hgain : 0 < W.Ip ε - Y.Ip ε := by
    have hle : Y.Ip ε ≤ (1 - θ) * W.Ip ε := by
      rw [hYeq]; exact Ip_Wmix_le W hε0 hε1 hsmem
    nlinarith
  refine ⟨hgain, ?_⟩
  -- so the density must have dropped as well
  by_contra hcon
  push Not at hcon
  have hYe : Y.edgeDensity = ε := by
    rw [hYeq, edgeDensity_Wmix, hW.1]; ring
  have := (fixed_inequality_minimality H hε0 hε1 hτ hW.2.2 hYe (by linarith)).1
  linarith

/-- `t(H, W_s)` along the mixing path is the density of a one-parameter linear family of
kernels, with base the constant graphon `ε` and direction `W - ε`. -/
theorem mixTDensity_eq_lincomb (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) 1) (s : ℝ) :
    mixTDensity W ε H s = ((Kernel.ofGraphon (constGraphon ε hε)).lincomb
        (fun _ : Fin 1 => Kernel.ofGraphon W + (-1 : ℝ) • Kernel.ofGraphon (constGraphon ε hε))
        (fun _ => s)).tDensity H := by
  rw [Kernel.tDensity_lincomb_eq, mixTDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = (1:ℝ) * _
  rw [one_mul]
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    show (1 - s) * ε + s * (Sym2.lift ⟨fun a b => W.toFun (x a) (x b), _⟩ s(a, b)) = _
    show _ = ε + ∑ _i : Fin 1, s * (W.toFun (x a) (x b) + (-1) * ε)
    simp
    ring

/-- **`t(H, W_s)` is analytic in the mixing parameter**, being a polynomial in it. -/
theorem analyticAt_mixTDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) 1) (s₀ : ℝ) : AnalyticAt ℝ (mixTDensity W ε H) s₀ := by
  rw [funext (mixTDensity_eq_lincomb H W hε)]
  have hana := analyticOnNhd_tDensity_lincomb H (Kernel.ofGraphon (constGraphon ε hε))
    (fun _ : Fin 1 => Kernel.ofGraphon W + (-1 : ℝ) • Kernel.ofGraphon (constGraphon ε hε))
  have hlin : AnalyticAt ℝ (fun s : ℝ => (fun _ : Fin 1 => s)) s₀ :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ).analyticAt s₀
  exact (hana _ (Set.mem_univ _)).comp hlin

/-- **The polynomial order of the density loss, the last assertion of
`lem:degenerate-smoothing`.**  Along `W_θ = (1-θ)W + θε` the loss `d_θ = τ - t(H,W_θ)` is a
polynomial in `θ` that vanishes at `θ = 0` and is positive on `(0,1)`.  Hence
`d_θ = a_kθ^k + O(θ^{k+1})` for some `k ≥ 1` and `a_k > 0`, stated here as
`d_θ/θ^k → a_k > 0` as `θ ↓ 0`.  Degeneracy is not needed. -/
theorem exists_smoothing_deficit_order (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ : τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε))
    {W : Graphon} (hW : IsFixedMinimizer H ε τ W) :
    ∃ (k : ℕ) (a : ℝ), 1 ≤ k ∧ 0 < a ∧
      Tendsto (fun θ => (τ - mixTDensity W ε H (1 - θ)) / θ ^ k) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have hεI : ε ∈ Set.Icc (0:ℝ) 1 := ⟨hε0.le, hε1.le⟩
  set d : ℝ → ℝ := fun θ => τ - mixTDensity W ε H (1 - θ) with hddef
  -- `d` is analytic at `0`, being a polynomial
  have hda : AnalyticAt ℝ d 0 := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => 1 - θ) 0 := (analyticAt_const).sub analyticAt_id
    exact analyticAt_const.sub ((analyticAt_mixTDensity H W hεI (1 - 0)).comp h1)
  -- `d` vanishes at `0` and is positive on `(0,1)`
  have hd0 : d 0 = 0 := by
    rw [hddef]
    show τ - mixTDensity W ε H (1 - 0) = 0
    rw [sub_zero, mixTDensity_one, hW.2.1, sub_self]
  have hdpos : ∀ θ ∈ Set.Ioo (0:ℝ) 1, 0 < d θ := by
    intro θ hθ
    have hsmem : (1 - θ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hY : ∀ x y, (Wmix W ε hεI (1 - θ) hsmem).toFun x y
        = (1 - θ) * W.toFun x y + θ * ε := by
      intro x y; rw [Wmix_apply]; ring
    have hpos := (smoothing_pos H hε0 hε1 hτ hW hθ.1 hθ.2 _ hY).2
    rw [hddef]
    show 0 < τ - mixTDensity W ε H (1 - θ)
    rwa [mixTDensity_eq_tDensity W hεI H hsmem]
  -- so `d` is not identically zero near `0`
  have hne : ¬ (∀ᶠ θ in 𝓝 (0:ℝ), d θ = 0) := by
    intro hcon
    obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp hcon
    set θ : ℝ := min (δ / 2) (1 / 2) with hθdef
    have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
    have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hθδ : dist θ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθ0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact absurd (hsub hθδ) (hdpos θ ⟨hθ0, hθ1⟩).ne'
  -- the analytic factorization `d θ = θ^k g θ` with `g 0 ≠ 0`
  obtain ⟨k, g, hga, hg0, heq⟩ := hda.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have heq' : ∀ᶠ θ in 𝓝 (0:ℝ), d θ = θ ^ k * g θ := by
    filter_upwards [heq] with θ hθ
    simpa [sub_zero] using hθ
  -- `k ≥ 1`, since `d 0 = 0` while `g 0 ≠ 0`
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      have h0 := heq'.self_of_nhds
      rw [hk, pow_zero, one_mul, hd0] at h0
      exact hg0 h0.symm
    · exact hk
  -- `g` is continuous at `0` and nonnegative on `(0,1)` near `0`, so `g 0 > 0`
  have hgcont : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
    hga.continuousAt.continuousWithinAt.tendsto
  have hgpos : ∀ᶠ θ in 𝓝[>] (0:ℝ), 0 ≤ g θ := by
    filter_upwards [nhdsWithin_le_nhds heq',
      Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with θ hθeq hθmem
    have hdθ := hdpos θ hθmem
    rw [hθeq] at hdθ
    have hpow : 0 < θ ^ k := pow_pos hθmem.1 k
    exact ((mul_pos_iff_of_pos_left hpow).mp hdθ).le
  have hgzero : 0 < g 0 :=
    lt_of_le_of_ne (ge_of_tendsto hgcont hgpos) (Ne.symm hg0)
  -- the ratio converges to `g 0`
  refine ⟨k, g 0, hk1, hgzero, ?_⟩
  refine Tendsto.congr' ?_ hgcont
  filter_upwards [nhdsWithin_le_nhds heq', self_mem_nhdsWithin] with θ hθeq hθpos
  have hval : τ - mixTDensity W ε H (1 - θ) = θ ^ k * g θ := hθeq
  show g θ = (τ - mixTDensity W ε H (1 - θ)) / θ ^ k
  rw [hval, mul_comm, mul_div_assoc, div_self (pow_ne_zero k (ne_of_gt hθpos)), mul_one]

/-- **`lem:degenerate-smoothing`.**  For a degenerate minimizer `W`, the smoothing
`W_θ = (1-θ)W + θε` has positive cost saving and positive density loss on `0 < θ < 1`, and the
ratio `g_θ/d_θ` exceeds any prescribed bound for all small `θ > 0` — the form in which
`lem:degenerate-slope` and `lem:degenerate-insertion` use it.  The polynomial expansion
`d_θ = a_kθ^k + O(θ^{k+1})` that the paper also records is `exists_smoothing_deficit_order`. -/
theorem degenerate_smoothing (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ : τ ∈ Set.Ioo (ε ^ H.edgeFinset.card) (tauMax H ε)) {W : Graphon}
    (hW : IsEntropyMaximizer H ε τ W) (hdeg : ¬ ConstraintQualification H W) :
    (∀ θ ∈ Set.Ioo (0:ℝ) 1, ∀ Y : Graphon,
        (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) →
          0 < W.Ip ε - Y.Ip ε ∧ 0 < τ - Y.tDensity H) ∧
      ∀ C : ℝ, ∀ᶠ θ in 𝓝[>] (0:ℝ), ∀ Y : Graphon,
        (∀ x y, Y.toFun x y = (1 - θ) * W.toFun x y + θ * ε) →
          0 < τ - Y.tDensity H ∧ C * (τ - Y.tDensity H) < W.Ip ε - Y.Ip ε :=
  ⟨fun _ hθ Y hY => smoothing_pos H hε0 hε1 hτ
      ((isEntropyMaximizer_iff H hε0 hε1 W).mp hW) hθ.1 hθ.2 Y hY,
    fun C => degenerate_gain H hΔ hε0 hε1 hτ.1 hτ.2 hW hdeg C⟩

end UpperTailMultipodality
