import UpperTailMultipodality.FixedDensities.Monotone
import UpperTailMultipodality.FixedDensities.Support.Degenerate

/-!
# Degenerate maximizers occur only for a null set of values

`lem:degenerate-forms` and `lem:degenerate-slope`.
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
  -- only degeneracy enters: the normal forms hold for any graphon violating `eq:cq-matrix`
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

/-- **`lem:degenerate-slope`.**  If `eq:fixed-problem` has a degenerate minimizer at `τ`, then the
left difference quotients of `Ψ_ε` at `τ` are unbounded. -/
theorem degenerate_slope (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : ∃ v, 2 ≤ H.degree v)
    {ε τ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card < τ)
    (hτ1 : τ < tauMax H ε) {W : Graphon} (hW : IsEntropyMaximizer H ε τ W)
    (hdeg : ¬ ConstraintQualification H W) :
    ∀ C : ℝ, ∃ᶠ τ' in 𝓝[<] τ,
      C < (fixedValue H ε τ - fixedValue H ε τ') / (τ - τ') := by
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
  intro C
  have htend : Tendsto f (𝓝[>] 0) (𝓝[<] τ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto f (𝓝 0) (𝓝 τ) := by rw [← hf0]; exact hfd.continuousAt.tendsto
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with θ hθ
      exact hlt θ hθ.1 hθ.2
  refine htend.frequently (Filter.Eventually.frequently ?_)
  rcases degenerate_forms H hΔ hε0 hε1 hτ0 hτ1 hW hdeg with hB | ⟨-, c₀, hc₀⟩
  · -- a positive measure of endpoint values: the `θ log(1/θ)` gain
    obtain ⟨β, hβ⟩ : ∃ β, β = gμ.real {z : ℝ × ℝ | W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1} :=
      ⟨_, rfl⟩
    have hβ0 : 0 < β := by
      rw [hβ, measureReal_def]
      exact ENNReal.toReal_pos hB.ne' (measure_ne_top _ _)
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = min ε (1 - ε) := ⟨_, rfl⟩
    have hκ0 : 0 < κ := by rw [hκ]; exact lt_min hε0 (by linarith)
    obtain ⟨K, hK⟩ : ∃ K, K = |v| + 1 := ⟨_, rfl⟩
    have hK0 : 0 < K := by rw [hK]; positivity
    obtain ⟨t, htdef⟩ : ∃ t, t = (|C| * K + 1) / (β * κ) := ⟨_, rfl⟩
    have hderiv := eventually_abs_sub_le_of_hasDerivAt hfd one_pos
    rw [hf0] at hderiv
    filter_upwards [hderiv.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num),
      Ioc_mem_nhdsGT (Real.exp_pos (-t))] with θ hd hθ hexp
    obtain ⟨V, hV1, hV2, hV3, -⟩ := hmix θ hθ.1 hθ.2
    have hlog : t ≤ Real.log (1 / θ) := by
      have h1 : Real.log θ ≤ -t := by
        have := Real.log_le_log hθ.1 hexp.2
        rwa [Real.log_exp] at this
      rw [one_div, Real.log_inv]
      linarith
    have hlog0 : 0 ≤ Real.log (1 / θ) := by
      rw [one_div]
      exact Real.log_nonneg (by rw [le_inv_comm₀ one_pos hθ.1]; linarith [hθ.2])
    have hnum : β * (κ * (θ * Real.log (1 / θ))) ≤ W.Ip ε - V.Ip ε := by
      have := Ip_mix_gain W hε0 hε1 hθ.1 hθ.2 hV1
      rw [← hβ, ← hκ] at this
      calc β * (κ * (θ * Real.log (1 / θ))) = β * (κ * (θ * Real.log (1 / θ))) := rfl
        _ ≤ W.Ip ε - V.Ip ε := this
    have hdenb : τ - f θ ≤ K * θ := by
      rw [abs_le] at hd
      have h1 : |θ * v| ≤ θ * |v| := by rw [abs_mul, abs_of_pos hθ.1]
      have h2 : -(θ * |v|) ≤ θ * v := by
        have := neg_abs_le (θ * v); linarith [abs_mul θ v, abs_of_pos hθ.1]
      rw [hK]
      have h3 := hd.1
      have := abs_of_pos hθ.1
      nlinarith [hd.1, h2]
    have hbig : C * (K * θ) < β * (κ * (θ * Real.log (1 / θ))) := by
      have h5 : |C| * K + 1 ≤ β * κ * Real.log (1 / θ) := by
        have hβκ : 0 < β * κ := mul_pos hβ0 hκ0
        rw [htdef, div_le_iff₀ hβκ] at hlog
        nlinarith
      have h6 : C * K ≤ |C| * K := mul_le_mul_of_nonneg_right (le_abs_self C) hK0.le
      calc C * (K * θ) = C * K * θ := by ring
        _ < (β * κ * Real.log (1 / θ)) * θ := by nlinarith [hθ.1]
        _ = β * (κ * (θ * Real.log (1 / θ))) := by ring
    exact hfinal C θ hθ.1 hθ.2 V hV2 hV3 _ _
      (mul_nonneg hβ0.le (mul_nonneg hκ0.le (mul_nonneg hθ.1.le hlog0))) hnum
      (mul_pos hK0 hθ.1) hdenb hbig
  · -- an almost everywhere constant derivative kernel: the quadratic bound
    have hv0 : v = 0 := by
      have hUint : ∫ z, U.toFun z.1 z.2 ∂gμ = 0 := by
        rw [hU]
        show ∫ z, (ε - W.toFun z.1 z.2) ∂gμ = 0
        rw [integral_sub (integrable_const ε) W.integrable_self, integral_const]
        simp only [smul_eq_mul, probReal_univ]
        rw [← Graphon.edgeDensity, he]
        ring
      rw [hv, integral_congr_ae (hc₀.mono fun z hz => by rw [hz]), integral_const_mul, hUint,
        mul_zero]
    obtain ⟨K, hK0, hKev⟩ := tDensity_line_isBigO_sq H W U (by rw [← hv, hv0])
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = W.Ip ε / (|C| * K + 1) := ⟨_, rfl⟩
    have hθ₀0 : 0 < θ₀ := by rw [hθ₀]; positivity
    filter_upwards [hKev.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num), Ioo_mem_nhdsGT hθ₀0] with θ hK hθ hθsmall
    obtain ⟨V, -, hV2, hV3, hV4⟩ := hmix θ hθ.1 hθ.2
    have hnum : θ * W.Ip ε ≤ W.Ip ε - V.Ip ε := by nlinarith
    have hdenb : τ - f θ ≤ K * θ ^ 2 := by
      rw [hfdef θ, ← ht]
      rw [abs_le] at hK
      linarith [hK.1]
    have hbig : C * (K * θ ^ 2) < θ * W.Ip ε := by
      have h1 : θ < W.Ip ε / (|C| * K + 1) := hθ₀ ▸ hθsmall.2
      rw [lt_div_iff₀ (by positivity)] at h1
      have h2 : C * K ≤ |C| * K := mul_le_mul_of_nonneg_right (le_abs_self C) hK0.le
      calc C * (K * θ ^ 2) = (C * K) * θ * θ := by ring
        _ ≤ (|C| * K) * θ * θ := by nlinarith [hθ.1]
        _ < θ * W.Ip ε := by nlinarith [hθ.1]
    exact hfinal C θ hθ.1 hθ.2 V hV2 hV3 _ _ (mul_nonneg hθ.1.le hIpos.le) hnum
      (mul_pos hK0 (pow_pos hθ.1 2)) hdenb hbig

end UpperTailMultipodality
