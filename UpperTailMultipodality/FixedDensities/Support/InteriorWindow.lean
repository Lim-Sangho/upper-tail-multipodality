import UpperTailMultipodality.FixedDensities.Support.Existence
import UpperTailMultipodality.FixedDensities.Support.InsertionEstimates

/-!
# The interior window at a minimizer

`exists_interior_window`: every minimizer of `eq:fixed-problem` at an interior value of `τ` has
`|Ω_η(W)| > 0` for some `η > 0`.  This is the first assertion `|Ω| > 0` of
`lem:degenerate-forms`: a minimizer cannot take only the values `0` and `1`, because a
competitor with values in a compact subinterval of `(0,1)` has strictly smaller cost, by strict
convexity of `J_ε`.  `Jp_lt_chord` is the strict convexity bound it uses.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### An interior window -/

/-- Strict convexity of `J_p` compared with the chord through the endpoints. -/
theorem Jp_lt_chord {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Jp p t < Jp p 0 + (Jp p 1 - Jp p 0) * t := by
  have h := (strictConvexOn_Jp hp0 hp1).2 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) (by norm_num)
    (show (0:ℝ) < 1 - t by linarith) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h
  linarith

/-- **`|Ω_η(W)| > 0` for some `η > 0`.**  The first assertion of `lem:degenerate-forms`: a
minimizer of `eq:fixed-problem` at an interior value of `τ` is interior on a set of positive
measure. -/
theorem exists_interior_window (H : SimpleGraph V) [DecidableRel H.Adj] {ε τ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hτ0 : ε ^ H.edgeFinset.card ≤ τ) (hτ1 : τ < tauMax H ε) {W : Graphon}
    (hW : IsFixedMinimizer H ε τ W) :
    ∃ η : ℝ, 0 < η ∧ gμ {z : ℝ × ℝ | η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η} ≠ 0 := by
  obtain ⟨he, ht, hI⟩ := hW
  -- a feasible competitor with values in a compact subinterval of `(0,1)`
  have hne : {τ | ∃ W : Graphon, W.edgeDensity = ε ∧ W.tDensity H = τ}.Nonempty :=
    ⟨_, constGraphon ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩),
      edgeDensity_ae_const _ (ae_of_all _ fun _ => rfl), rfl⟩
  obtain ⟨τ', ⟨W₂, he₂, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hτ1
  obtain ⟨θ, hθ, hθeq⟩ := exists_mix_tDensity_eq H W₂ hε0 hε1 hτ0 hlt.le
  have hθ1 : θ < 1 := by
    refine lt_of_le_of_ne hθ.2 fun hh => ?_
    subst hh
    have hone : (Wmix W₂ ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) 1 hθ).tDensity H
        = W₂.tDensity H := by
      rw [← mixTDensity_eq_tDensity W₂ _ H hθ, mixTDensity_one]
    rw [hone] at hθeq
    linarith
  obtain ⟨Z, hZdef⟩ : ∃ Z : Graphon, Z = Wmix W₂ ε (Set.mem_Icc.mpr ⟨hε0.le, hε1.le⟩) θ hθ :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = min ((1 - θ) * ε) ((1 - θ) * (1 - ε)) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by
    rw [hγdef]
    exact lt_min (by nlinarith) (by nlinarith)
  have hγhalf : γ ≤ 1 - γ := by
    have h1 : γ ≤ (1 - θ) * ε := hγdef ▸ min_le_left _ _
    have h2 : γ ≤ (1 - θ) * (1 - ε) := hγdef ▸ min_le_right _ _
    nlinarith [hθ.1]
  have hZmem : ∀ x y, Z.toFun x y ∈ Set.Icc γ (1 - γ) := by
    intro x y
    have hval : Z.toFun x y = (1 - θ) * ε + θ * W₂.toFun x y := by rw [hZdef]; rfl
    have h1 : γ ≤ (1 - θ) * ε := hγdef ▸ min_le_left _ _
    have h2 : γ ≤ (1 - θ) * (1 - ε) := hγdef ▸ min_le_right _ _
    refine ⟨?_, ?_⟩
    · rw [hval]; nlinarith [W₂.nonneg' x y, hθ.1]
    · rw [hval]; nlinarith [W₂.le_one' x y, hθ.1]
  have hZe : Z.edgeDensity = ε := by rw [hZdef, edgeDensity_Wmix, he₂]; ring
  have hZt : Z.tDensity H = τ := by rw [hZdef]; exact hθeq
  -- suppose `W` is interior on a null set only
  by_contra hcon
  push Not at hcon
  have hnull : gμ {z : ℝ × ℝ | 0 < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1} = 0 := by
    refine measure_mono_null (fun z hz => ?_)
      (measure_iUnion_null (ι := ℕ) fun n => hcon (1 / ((n : ℝ) + 2)) (by positivity))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (show 0 < min (W.toFun z.1 z.2) (1 - W.toFun z.1 z.2) from
        lt_min hz.1 (by linarith [hz.2]))
    have hle : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
    · exact lt_of_le_of_lt hle (lt_of_lt_of_le hn (min_le_left _ _))
    · have := lt_of_le_of_lt hle (lt_of_lt_of_le hn (min_le_right _ _))
      linarith
  have hae : ∀ᵐ z ∂gμ, Jp ε (W.toFun z.1 z.2)
      = Jp ε 0 + (Jp ε 1 - Jp ε 0) * W.toFun z.1 z.2 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    have h01 : W.toFun z.1 z.2 = 0 ∨ W.toFun z.1 z.2 = 1 → False := by
      rintro (h | h) <;> apply hz <;> rw [h] <;> ring
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne (W.nonneg' _ _) fun h => h01 (Or.inl h.symm)
    · exact lt_of_le_of_ne (W.le_one' _ _) fun h => h01 (Or.inr h)
  -- the cost of `W` is the chord value, the cost of `Z` is strictly smaller
  have hchordint : Integrable
      (fun z : ℝ × ℝ => Jp ε 0 + (Jp ε 1 - Jp ε 0) * W.toFun z.1 z.2) gμ :=
    (integrable_const _).add (W.integrable_self.const_mul _)
  have hIW : W.Ip ε = Jp ε 0 + (Jp ε 1 - Jp ε 0) * ε := by
    show (∫ z, Jp ε (W.toFun z.1 z.2) ∂gμ) = _
    rw [integral_congr_ae hae, integral_add (integrable_const _)
      (W.integrable_self.const_mul _), integral_const_mul, integral_const]
    simp only [smul_eq_mul, probReal_univ, one_mul]
    rw [← Graphon.edgeDensity, he]
  -- a uniform gap on `[γ, 1-γ]`
  have hsub : Set.Icc γ (1 - γ) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc hγ0.le (by linarith)
  have hφcont : ContinuousOn (fun t => Jp ε 0 + (Jp ε 1 - Jp ε 0) * t - Jp ε t)
      (Set.Icc γ (1 - γ)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.sub
      ((continuousOn_Jp_Icc hε0 hε1).mono hsub)
  obtain ⟨t₀, ht₀mem, ht₀min⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hγhalf) hφcont
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = Jp ε 0 + (Jp ε 1 - Jp ε 0) * t₀ - Jp ε t₀ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact sub_pos.mpr (Jp_lt_chord hε0 hε1 (lt_of_lt_of_le hγ0 ht₀mem.1)
      (lt_of_le_of_lt ht₀mem.2 (by linarith)))
  have hδle : ∀ x ∈ Set.Icc γ (1 - γ), δ ≤ Jp ε 0 + (Jp ε 1 - Jp ε 0) * x - Jp ε x := by
    intro x hx
    rw [hδdef]
    exact ht₀min hx
  have hZle : Z.Ip ε ≤ Jp ε 0 + (Jp ε 1 - Jp ε 0) * ε - δ := by
    have hpt : ∀ z : ℝ × ℝ, Jp ε (Z.toFun z.1 z.2)
        ≤ Jp ε 0 + (Jp ε 1 - Jp ε 0) * Z.toFun z.1 z.2 - δ := by
      intro z
      linarith [hδle _ (hZmem z.1 z.2)]
    have hJZ : Integrable (fun z : ℝ × ℝ => Jp ε (Z.toFun z.1 z.2)) gμ :=
      Z.integrable_comp (measurable_Jp ε) (continuousOn_Jp_Icc hε0 hε1)
    have hint1 : Integrable (fun z : ℝ × ℝ => (Jp ε 1 - Jp ε 0) * Z.toFun z.1 z.2) gμ :=
      Z.integrable_self.const_mul _
    have hint2 : Integrable
        (fun z : ℝ × ℝ => Jp ε 0 + (Jp ε 1 - Jp ε 0) * Z.toFun z.1 z.2) gμ :=
      (integrable_const _).add hint1
    have hint3 : Integrable
        (fun z : ℝ × ℝ => Jp ε 0 + (Jp ε 1 - Jp ε 0) * Z.toFun z.1 z.2 - δ) gμ :=
      hint2.sub (integrable_const δ)
    have hval : ∫ z, (Jp ε 0 + (Jp ε 1 - Jp ε 0) * Z.toFun z.1 z.2 - δ) ∂gμ
        = Jp ε 0 + (Jp ε 1 - Jp ε 0) * ε - δ := by
      rw [integral_sub hint2 (integrable_const δ), integral_add (integrable_const _) hint1,
        integral_const_mul, integral_const, integral_const]
      simp only [smul_eq_mul, probReal_univ, one_mul]
      rw [← Graphon.edgeDensity, hZe]
    have h := integral_mono hJZ hint3 hpt
    rw [hval] at h
    exact h
  have hge : fixedValue H ε τ ≤ Z.Ip ε := fixedValue_le H hε0 hε1 hZe hZt
  rw [← hI, hIW] at hge
  linarith
end FixedDensities

end UpperTailMultipodality
