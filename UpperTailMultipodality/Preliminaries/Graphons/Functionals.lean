import UpperTailMultipodality.Preliminaries.Graphons.JpConvexity

/-!
# Elementary facts about the edge density and the relative entropy

* `edgeDensity_nonneg`, `edgeDensity_le_one` — `e(W) ∈ [0,1]`.
* `edgeDensity_ae_const` — the edge density of an a.e.-constant graphon.
* `Ip_nonneg` — `I_p(W) ≥ 0`, with `ae_eq_of_Ip_eq_zero` for the case of equality.
* `entropy_le` — the binary-entropy bound `s(W) ≤ ½ log 2`.
* `Ip_jensen` — **Jensen's inequality** `J_p(e(W)) ≤ I_p(W)` (from convexity of `J_p`).
* `Ip_sub_eq`, `abs_Ip_sub_le` — the exact dependence of `I_p(W)` on `p` and the resulting
  uniform-in-`W` modulus of continuity in `p`.
-/

namespace UpperTailMultipodality

open MeasureTheory Real

/-- `0 ≤ e(W)`. -/
theorem edgeDensity_nonneg (W : Graphon) : 0 ≤ W.edgeDensity :=
  integral_nonneg (fun z => W.nonneg' z.1 z.2)

/-- `e(W) ≤ 1`. -/
theorem edgeDensity_le_one (W : Graphon) : W.edgeDensity ≤ 1 := by
  show (∫ z, W.toFun z.1 z.2 ∂gμ) ≤ 1
  have h := integral_mono W.integrable_self (integrable_const (1:ℝ)) (fun z => W.le_one' z.1 z.2)
  simpa using h

/-- If `W = c` almost everywhere then `e(W) = c`. -/
theorem edgeDensity_ae_const (W : Graphon) {c : ℝ} (h : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = c) :
    W.edgeDensity = c := by
  show (∫ z, W.toFun z.1 z.2 ∂gμ) = c
  exact integral_eq_const h

/-- The edge density depends only on the almost-everywhere class of the kernel.  (The
`tDensity` and `entropy` analogues are `tDensity_congr_ae` and
`entropy_congr_ae`.) -/
theorem edgeDensity_congr_ae {W W' : Graphon}
    (h : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = W'.toFun z.1 z.2) : W.edgeDensity = W'.edgeDensity := by
  show (∫ z, W.toFun z.1 z.2 ∂gμ) = ∫ z, W'.toFun z.1 z.2 ∂gμ
  exact integral_congr_ae h

/-- **Jensen's inequality for graphons**: `J_p(e(W)) ≤ I_p(W)`. -/
theorem Ip_jensen (W : Graphon) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Jp p W.edgeDensity ≤ W.Ip p := by
  have hgi : Integrable (fun z : ℝ × ℝ => Jp p (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  exact (convexOn_Jp hp0 hp1).map_integral_le (continuousOn_Jp_Icc hp0 hp1)
    isClosed_Icc (ae_of_all _ (fun z => W.mem_Icc z.1 z.2)) W.integrable_self hgi

/-- `I_p(W) ≥ 0` for every graphon (the relative-entropy cost is nonnegative). -/
theorem Ip_nonneg (W : Graphon) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ W.Ip p := by
  show 0 ≤ ∫ z, Jp p (W.toFun z.1 z.2) ∂gμ
  refine integral_nonneg (fun z => ?_)
  rcases eq_or_ne (W.toFun z.1 z.2) p with h | h
  · have h0 : Jp p (W.toFun z.1 z.2) = 0 := by rw [h, Jp_self hp0 hp1]
    exact h0.ge
  · exact (Jp_pos_of_ne hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2) h).le

/-- **The entropy is bounded above by `½ log 2`** (binary-entropy bound).  Used to show the
fixed-density entropy envelope `S_H` is bounded above. -/
theorem entropy_le (W : Graphon) : W.entropy ≤ (1 / 2) * Real.log 2 := by
  have hpt : ∀ z : ℝ × ℝ, -Real.log 2 ≤ entIntegrand (W.toFun z.1 z.2) := by
    intro z
    have hb : entIntegrand (W.toFun z.1 z.2) = -Real.binEntropy (W.toFun z.1 z.2) := by
      rw [entIntegrand_eq, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]; ring
    rw [hb]; linarith [Real.binEntropy_le_log_two (p := W.toFun z.1 z.2)]
  have hint : Integrable (fun z : ℝ × ℝ => entIntegrand (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp measurable_entIntegrand continuous_entIntegrand.continuousOn
  have hge : -Real.log 2 ≤ ∫ z, entIntegrand (W.toFun z.1 z.2) ∂gμ := by
    have h := integral_mono (integrable_const (-Real.log 2)) hint hpt
    simpa using h
  have hent : W.entropy = -(1 / 2) * ∫ z, entIntegrand (W.toFun z.1 z.2) ∂gμ := rfl
  rw [hent]; linarith

/-- The exact `p`-dependence of `I_p(W)`: the difference `I_p(W) − I_q(W)` depends on `W`
only through its edge density. -/
theorem Ip_sub_eq (W : Graphon) {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    W.Ip p - W.Ip q
      = -(Real.log (1 - p) - Real.log (1 - q))
        + W.edgeDensity * (Real.log ((1 - p) / p) - Real.log ((1 - q) / q)) := by
  rw [W.Ip_eq_entropy hp0 hp1, W.Ip_eq_entropy hq0 hq1]; ring

/-- **Uniform-in-`W` modulus of continuity in `p`**: `|I_p(W) − I_q(W)|` is bounded by the
variation of `log(1−·)` and `log((1−·)/·)`, with no dependence on `W` (because `e(W) ∈ [0,1]`). -/
theorem abs_Ip_sub_le (W : Graphon) {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    |W.Ip p - W.Ip q|
      ≤ |Real.log (1 - p) - Real.log (1 - q)|
        + |Real.log ((1 - p) / p) - Real.log ((1 - q) / q)| := by
  rw [Ip_sub_eq W hp0 hp1 hq0 hq1]
  have he0 : 0 ≤ W.edgeDensity := edgeDensity_nonneg W
  have he1 : W.edgeDensity ≤ 1 := edgeDensity_le_one W
  calc |-(Real.log (1 - p) - Real.log (1 - q))
            + W.edgeDensity * (Real.log ((1 - p) / p) - Real.log ((1 - q) / q))|
      ≤ |-(Real.log (1 - p) - Real.log (1 - q))|
          + |W.edgeDensity * (Real.log ((1 - p) / p) - Real.log ((1 - q) / q))| := abs_add_le _ _
    _ = |Real.log (1 - p) - Real.log (1 - q)|
          + |W.edgeDensity| * |Real.log ((1 - p) / p) - Real.log ((1 - q) / q)| := by
        rw [abs_neg, abs_mul]
    _ ≤ |Real.log (1 - p) - Real.log (1 - q)|
          + 1 * |Real.log ((1 - p) / p) - Real.log ((1 - q) / q)| := by
        gcongr
        rw [abs_of_nonneg he0]; exact he1
    _ = |Real.log (1 - p) - Real.log (1 - q)|
          + |Real.log ((1 - p) / p) - Real.log ((1 - q) / q)| := by rw [one_mul]

/-- If `I_p(W) = 0`, then `W = p` almost everywhere: `J_p` vanishes only at `p`. -/
theorem ae_eq_of_Ip_eq_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {W : Graphon}
    (h : W.Ip p = 0) : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = p := by
  have hint := W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hae0 := (integral_eq_zero_iff_of_nonneg
    (fun z : ℝ × ℝ => Jp_nonneg_of_mem hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2)) hint).mp h
  filter_upwards [hae0] with z hz
  exact Jp_eq_zero_imp hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2) hz

end UpperTailMultipodality
