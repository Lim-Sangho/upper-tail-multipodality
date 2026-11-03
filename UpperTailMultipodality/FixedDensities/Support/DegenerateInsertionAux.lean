import UpperTailMultipodality.FixedDensities.Support.InteriorWindow
import UpperTailMultipodality.FixedDensities.Support.UniformCorrection

/-!
# Auxiliary estimates for the insertion at a degenerate minimizer

The proof of `lem:degenerate-insertion` compares the insertion of a block of measure `s` into the
smoothed graphon `W_θ = (1-θ)W + θε`, corrected by a multiple of the indicator of `Ω_η(W)`.  The
pieces collected here are the ones that depend on both parameters:

* `abs_insertionPoly_sub_le` — the insertion polynomial is `m`-Lipschitz in the base graphon,
  uniformly in the block measure;
* `Ip_line_le` — a correction supported where the graphon is bounded away from `0` and `1`
  changes `I_p` by at most a constant times its size;
* `exists_bound_integral_Jp` — `∫ J_p(u)` is bounded on rows.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The insertion polynomial is `m`-Lipschitz in the base graphon.** -/
theorem abs_insertionPoly_sub_le (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (Z : Kernel) (g : ℝ → ℝ)
    {G G' : Graphon} {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hK : ∀ x y, (Kernel.ofGraphon G + g s • Z).toFun x y ∈ Set.Icc (0:ℝ) 1)
    (hK' : ∀ x y, (Kernel.ofGraphon G' + g s • Z).toFun x y ∈ Set.Icc (0:ℝ) 1)
    (hc : ∀ x y, |G.toFun x y - G'.toFun x y| ≤ c) :
    |insertionPoly H q u G Z g s - insertionPoly H q u G' Z g s|
      ≤ (H.edgeFinset.card : ℝ) * c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 0)
  have hwnn : ∀ S : Finset V, 0 ≤ s ^ S.card * (1 - s) ^ Sᶜ.card := fun S => by
    have h1 : (0:ℝ) ≤ 1 - s := by linarith
    positivity
  have hKK' : ∀ x y, |(Kernel.ofGraphon G + g s • Z).toFun x y
      - (Kernel.ofGraphon G' + g s • Z).toFun x y| ≤ c := by
    intro x y
    have hE : (Kernel.ofGraphon G + g s • Z).toFun x y
        - (Kernel.ofGraphon G' + g s • Z).toFun x y = G.toFun x y - G'.toFun x y := by
      simp only [Kernel.add_apply, Kernel.smul_apply, Kernel.ofGraphon_apply]; ring
    rw [hE]; exact hc x y
  rw [insertionPoly_eq, insertionPoly_eq, ← Finset.sum_sub_distrib]
  calc |∑ S ∈ (Finset.univ : Finset V).powerset,
          (s ^ S.card * (1 - s) ^ Sᶜ.card
              * blockDensity H S q u (Kernel.ofGraphon G + g s • Z)
            - s ^ S.card * (1 - s) ^ Sᶜ.card
              * blockDensity H S q u (Kernel.ofGraphon G' + g s • Z))|
      ≤ ∑ S ∈ (Finset.univ : Finset V).powerset,
          |s ^ S.card * (1 - s) ^ Sᶜ.card
              * blockDensity H S q u (Kernel.ofGraphon G + g s • Z)
            - s ^ S.card * (1 - s) ^ Sᶜ.card
              * blockDensity H S q u (Kernel.ofGraphon G' + g s • Z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset V).powerset,
          s ^ S.card * (1 - s) ^ Sᶜ.card * ((H.edgeFinset.card : ℝ) * c) := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hwnn S)]
        exact mul_le_mul_of_nonneg_left (abs_blockDensity_sub_le H S hq hu hK hK' hKK') (hwnn S)
    _ = (H.edgeFinset.card : ℝ) * c := by
        rw [← Finset.sum_mul, sum_powerset_weight, one_mul]

/-- **The cost of a correction supported away from the endpoints.**  If `Z` vanishes outside a
set where `G` takes values in `[κ, 1-κ]` and `|ζZ| ≤ ρ ≤ κ/2`, then adding `ζZ` raises `I_p` by
at most `Lρ`, where `L` is a Lipschitz constant for `J_p` on `[κ/2, 1-κ/2]`. -/
theorem Ip_line_le (G : Graphon) (Z : Kernel) {p ζ ρ L κ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hκ0 : 0 < κ) (hL0 : 0 ≤ L) (hρ0 : 0 ≤ ρ)
    (hL : ∀ x ∈ Set.Icc (κ / 2) (1 - κ / 2), ∀ y ∈ Set.Icc (κ / 2) (1 - κ / 2),
      |Jp p x - Jp p y| ≤ L * |x - y|)
    (hsupp : ∀ x y, Z.toFun x y ≠ 0 → G.toFun x y ∈ Set.Icc κ (1 - κ))
    (hζZ : ∀ x y, |ζ * Z.toFun x y| ≤ ρ) (hρκ : ρ ≤ κ / 2)
    (hmem : ∀ x y, (Kernel.ofGraphon G + ζ • Z).toFun x y ∈ Set.Icc (0:ℝ) 1) :
    (Kernel.ofGraphon G + ζ • Z).Ip p ≤ G.Ip p + L * ρ := by
  obtain ⟨Gr, hGrdef⟩ : ∃ Gr : Graphon, Gr = clampGraphon (Kernel.ofGraphon G + ζ • Z) :=
    ⟨_, rfl⟩
  have hGr : ∀ x y, Gr.toFun x y = (Kernel.ofGraphon G + ζ • Z).toFun x y := by
    intro x y
    rw [hGrdef, clampGraphon_apply, min_eq_right (hmem x y).2, max_eq_right (hmem x y).1]
  have hIeq : (Kernel.ofGraphon G + ζ • Z).Ip p = Gr.Ip p :=
    integral_congr_ae (ae_of_all _ fun z => by
      show Jp p ((Kernel.ofGraphon G + ζ • Z).toFun z.1 z.2) = Jp p (Gr.toFun z.1 z.2)
      rw [hGr z.1 z.2])
  have hpt : ∀ z : ℝ × ℝ, Jp p (Gr.toFun z.1 z.2) ≤ Jp p (G.toFun z.1 z.2) + L * ρ := by
    intro z
    by_cases hz : Z.toFun z.1 z.2 = 0
    · have hval : Gr.toFun z.1 z.2 = G.toFun z.1 z.2 := by
        rw [hGr z.1 z.2]
        show G.toFun z.1 z.2 + ζ * Z.toFun z.1 z.2 = G.toFun z.1 z.2
        rw [hz]; ring
      rw [hval]
      nlinarith [mul_nonneg hL0 hρ0]
    · have hGmem := hsupp z.1 z.2 hz
      have hwin1 : G.toFun z.1 z.2 ∈ Set.Icc (κ / 2) (1 - κ / 2) :=
        ⟨by linarith [hGmem.1], by linarith [hGmem.2]⟩
      have hζ := hζZ z.1 z.2
      rw [abs_le] at hζ
      have hval : Gr.toFun z.1 z.2 = G.toFun z.1 z.2 + ζ * Z.toFun z.1 z.2 := hGr z.1 z.2
      have hwin2 : Gr.toFun z.1 z.2 ∈ Set.Icc (κ / 2) (1 - κ / 2) := by
        rw [hval]
        exact ⟨by linarith [hGmem.1, hζ.1], by linarith [hGmem.2, hζ.2]⟩
      have hlip := hL _ hwin2 _ hwin1
      have hdiff : |Gr.toFun z.1 z.2 - G.toFun z.1 z.2| ≤ ρ := by
        rw [hval]
        have hE : G.toFun z.1 z.2 + ζ * Z.toFun z.1 z.2 - G.toFun z.1 z.2
            = ζ * Z.toFun z.1 z.2 := by ring
        rw [hE]; exact hζZ z.1 z.2
      have h2 : L * |Gr.toFun z.1 z.2 - G.toFun z.1 z.2| ≤ L * ρ :=
        mul_le_mul_of_nonneg_left hdiff hL0
      have h3 : Jp p (Gr.toFun z.1 z.2) - Jp p (G.toFun z.1 z.2)
          ≤ |Jp p (Gr.toFun z.1 z.2) - Jp p (G.toFun z.1 z.2)| := le_abs_self _
      linarith
  have hiGr : Integrable (fun z : ℝ × ℝ => Jp p (Gr.toFun z.1 z.2)) gμ :=
    Gr.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hiG : Integrable (fun z : ℝ × ℝ => Jp p (G.toFun z.1 z.2)) gμ :=
    G.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hiG' : Integrable (fun z : ℝ × ℝ => Jp p (G.toFun z.1 z.2) + L * ρ) gμ :=
    hiG.add (integrable_const _)
  have h := integral_mono hiGr hiG' hpt
  rw [integral_add hiG (integrable_const _), integral_const] at h
  simp only [smul_eq_mul, probReal_univ, one_mul] at h
  rw [hIeq]
  exact h

/-! ### Arithmetic of the two-parameter comparison -/

/-- The lower bound for the increment of the `H`-density extracted from the uniform expansion. -/
theorem taylor_lower_bound {X Bt Bq Ctay CB b s θ : ℝ} (h1 : |X - s * Bt| ≤ Ctay * s ^ 2)
    (h2 : |Bt - Bq| ≤ CB * θ) (hs0 : 0 ≤ s) (hBq : Bq = 2 * b)
    (hsmall : Ctay * s + CB * θ ≤ b) : b * s ≤ X := by
  rw [abs_le] at h1 h2
  subst hBq
  nlinarith [h1.1, mul_le_mul_of_nonneg_left h2.1 hs0,
    mul_le_mul_of_nonneg_left hsmall hs0]

/-- The upper bound for the increment of the `H`-density. -/
theorem taylor_upper_bound {X Bt Ctay BB s : ℝ} (h1 : |X - s * Bt| ≤ Ctay * s ^ 2)
    (hBabs : |Bt| ≤ BB) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hC0 : 0 ≤ Ctay) :
    |X| ≤ (Ctay + BB) * s := by
  have h2 : |s * Bt| ≤ s * BB := by
    rw [abs_mul, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hBabs hs0
  have h3 : |X| ≤ |X - s * Bt| + |s * Bt| := by
    have h := abs_add_le (X - s * Bt) (s * Bt)
    simp only [sub_add_cancel] at h
    exact h
  have hss : s ^ 2 ≤ s := by nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1 - s)]
  have h4 : Ctay * s ^ 2 ≤ Ctay * s := mul_le_mul_of_nonneg_left hss hC0
  linarith

/-- The cost of the insertion together with the correction. -/
theorem insertion_cost_le {s MJ L cz IM Y Ju : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hJu0 : 0 ≤ Ju) (hJuM : Ju ≤ MJ) (hY0 : 0 ≤ Y)
    (hY : Y ≤ IM + L * (2 * s * cz)) :
    s ^ 2 * 0 + 2 * s * (1 - s) * Ju + (1 - s) ^ 2 * Y ≤ IM + (2 * MJ + 2 * L * cz) * s := by
  have hs1' : (0:ℝ) ≤ 1 - s := by linarith
  have ha : 2 * s * (1 - s) * Ju ≤ 2 * s * Ju := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs0) hJu0) hs0]
  have hb : 2 * s * Ju ≤ 2 * s * MJ :=
    mul_le_mul_of_nonneg_left hJuM (by positivity)
  have hpow : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have h2 : (1 - s) ^ 2 * Y ≤ Y := by
    have h := mul_le_mul_of_nonneg_right hpow hY0
    linarith
  linarith

/-- **`∫ J_p(u)` is bounded on rows.** -/
theorem exists_bound_integral_Jp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ MJ : ℝ, 0 ≤ MJ ∧ ∀ u : ℝ → ℝ, IsRow u →
      0 ≤ (∫ y, Jp p (u y) ∂unitμ) ∧ (∫ y, Jp p (u y) ∂unitμ) ≤ MJ := by
  obtain ⟨t₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one' ℝ)) (continuousOn_Jp_Icc hp0 hp1).abs
  refine ⟨|Jp p t₀|, abs_nonneg _, fun u hu => ?_⟩
  have hbd : ∀ y, |Jp p (u y)| ≤ |Jp p t₀| := fun y => hmax (hu.2 y)
  have hint : Integrable (fun y => Jp p (u y)) unitμ :=
    integrable_of_abs_le ((measurable_Jp p).comp hu.1) _ hbd
  refine ⟨integral_nonneg fun y => Jp_nonneg_of_mem hp0 hp1 (hu.2 y).1 (hu.2 y).2, ?_⟩
  have h := integral_mono hint (integrable_const (μ := unitμ) (|Jp p t₀|))
    fun y => (le_abs_self _).trans (hbd y)
  simpa using h

end FixedDensities

end UpperTailMultipodality
