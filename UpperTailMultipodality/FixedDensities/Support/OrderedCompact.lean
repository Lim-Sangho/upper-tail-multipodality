import UpperTailMultipodality.FixedDensities.Support.MonotoneL1
import UpperTailMultipodality.FixedDensities.Support.Ordered

/-!
# Compactness of ordered graphons (`lem:ordered-compact`)

`sec:degenerate-optimizers` ends by taking an `L¹` limit of minimizers that are multipodal with
ordered blocks.  Two steps are needed, and this file supplies both.

* `exists_hasOrderedRows_of_isOrderedMultipodal` — a multipodal graphon with ordered blocks has
  a representative that is nondecreasing in each variable, with the same `e`, `t(H,·)` and
  `I_p`.  Rather than constructing the measure-preserving relabelling of `[0,1]`, the two
  graphons are compared through their block index maps: a block structure pushes `unitμ`
  forward to a measure on `Fin M` whose weights are the block measures, and every functional of
  the graphon is an integral of the block values against that measure
  (`BlockStructure.integral_eq`, `BlockStructure.tDensity_eq`).  The sorted representative is
  the step kernel on consecutive intervals of the block measures.

* `ordered_compact` — the class of graphons with ordered rows is `L¹`-compact.  The projection
  `Π_k` of the paper is realised as composition with the dyadic floor `x ↦ ⌊2^j x⌋ / 2^j`; the
  error `‖V - Π_k V‖₁ = O(1/k)` is `MonotoneKernel.integral_abs_sub_comp_le`, proved from the
  one-dimensional estimate `integral_sub_translate_le`.  The values on the dyadic grids form a
  sequence in a compact cube `Π_{ℚ × ℚ} [0,1]`, which is metrizable, so a subsequence
  converges at every pair of rationals; `RatKernel.toMonotoneKernel` turns the limit values into
  the representative `W̃` of the paper.  Dyadic levels replace the levels `1/k` of the paper
  because a dyadic grid point stays a grid point at every finer level, which makes the limit
  kernel equal to its own grid projection (`RatKernel.toMonotoneKernel_dyad`) and lets the same
  `O(1/k)` estimate bound the distance from the limit.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology Set

namespace MonotoneKernel

variable (f : MonotoneKernel)

/-- Two values of a monotone kernel differ by at most `1`. -/
theorem abs_sub_le_one (x y u v : ℝ) : |f.toFun x y - f.toFun u v| ≤ 1 :=
  abs_le.mpr ⟨by linarith [f.nonneg' x y, f.le_one' u v], by linarith [f.nonneg' u v, f.le_one' x y]⟩

/-- The two-sided window in the first variable is integrable. -/
theorem integrable_window_fst (h : ℝ) :
    Integrable (fun z : ℝ × ℝ => f.toFun (z.1 + h) z.2 - f.toFun (z.1 - h) z.2) gμ := by
  refine integrable_of_abs_le ?_ 1 fun z => f.abs_sub_le_one _ _ _ _
  exact (f.meas'.comp ((measurable_fst.add_const h).prodMk measurable_snd)).sub
    (f.meas'.comp ((measurable_fst.sub_const h).prodMk measurable_snd))

/-- The two-sided window in the second variable is integrable. -/
theorem integrable_window_snd (a h : ℝ) :
    Integrable (fun z : ℝ × ℝ => f.toFun (z.1 + a) (z.2 + h) - f.toFun (z.1 + a) (z.2 - h)) gμ := by
  refine integrable_of_abs_le ?_ 1 fun z => f.abs_sub_le_one _ _ _ _
  exact (f.meas'.comp ((measurable_fst.add_const a).prodMk (measurable_snd.add_const h))).sub
    (f.meas'.comp ((measurable_fst.add_const a).prodMk (measurable_snd.sub_const h)))

/-- **The `L¹` cost of a window in the first variable is at most `2h`.**  This is
`integral_sub_translate_le` applied in the first variable, with the second variable integrated
out by Fubini. -/
theorem integral_window_fst_le {h : ℝ} (hh : 0 < h) :
    ∫ z, (f.toFun (z.1 + h) z.2 - f.toFun (z.1 - h) z.2) ∂gμ ≤ 2 * h := by
  rw [gμ, integral_prod_symm _ (f.integrable_window_fst h)]
  have hnn : ∀ y : ℝ, 0 ≤ ∫ x, (f.toFun (x + h) y - f.toFun (x - h) y) ∂unitμ := fun y =>
    integral_nonneg fun x => sub_nonneg.mpr (f.mono' y (by linarith))
  have hle : ∀ y : ℝ, (∫ x, (f.toFun (x + h) y - f.toFun (x - h) y) ∂unitμ) ≤ 2 * h :=
    fun y => by
      rw [FixedDensities.integral_unitμ_eq_intervalIntegral]
      exact FixedDensities.integral_sub_translate_le (f.mono' y) (fun t => f.mem_Icc t y) hh
  calc (∫ y, ∫ x, (f.toFun (x + h) y - f.toFun (x - h) y) ∂unitμ ∂unitμ)
      ≤ ∫ _ : ℝ, 2 * h ∂unitμ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (integrable_const _)
          (Filter.Eventually.of_forall hle)
    _ = 2 * h := by simp

/-- **The `L¹` cost of a window in the second variable is at most `2h`.** -/
theorem integral_window_snd_le {a h : ℝ} (hh : 0 < h) :
    ∫ z, (f.toFun (z.1 + a) (z.2 + h) - f.toFun (z.1 + a) (z.2 - h)) ∂gμ ≤ 2 * h := by
  rw [gμ, integral_prod _ (f.integrable_window_snd a h)]
  have hnn : ∀ x : ℝ, 0 ≤ ∫ y, (f.toFun (x + a) (y + h) - f.toFun (x + a) (y - h)) ∂unitμ :=
    fun x => integral_nonneg fun y => sub_nonneg.mpr (f.mono_snd (x + a) (by linarith))
  have hle : ∀ x : ℝ,
      (∫ y, (f.toFun (x + a) (y + h) - f.toFun (x + a) (y - h)) ∂unitμ) ≤ 2 * h := fun x => by
    rw [FixedDensities.integral_unitμ_eq_intervalIntegral]
    exact FixedDensities.integral_sub_translate_le (f.mono_snd (x + a))
      (fun y => f.mem_Icc (x + a) y) hh
  calc (∫ x, ∫ y, (f.toFun (x + a) (y + h) - f.toFun (x + a) (y - h)) ∂unitμ ∂unitμ)
      ≤ ∫ _ : ℝ, 2 * h ∂unitμ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (integrable_const _)
          (Filter.Eventually.of_forall hle)
    _ = 2 * h := by simp

/-- **The pointwise window bound.**  If `u, v` lie in the windows `[x-h, x]` and `[y-h, y]` then
the error `|f x y - f u v|` is dominated by two one-sided increments of `f`. -/
theorem abs_sub_le_window {h : ℝ} {u v x y : ℝ} (hu : x - h ≤ u) (hu' : u ≤ x) (hv : y - h ≤ v)
    (hv' : v ≤ y) (hh : 0 < h) :
    |f.toFun x y - f.toFun u v| ≤ (f.toFun (x + h) y - f.toFun (x - h) y)
      + (f.toFun (x + -h) (y + h) - f.toFun (x + -h) (y - h)) := by
  have h1 : f.toFun u v ≤ f.toFun x y := (f.mono' v hu').trans (f.mono_snd x hv')
  have h2 : f.toFun (x + -h) (y - h) ≤ f.toFun u v :=
    (f.mono' (y - h) (by linarith)).trans (f.mono_snd u hv)
  have h3 : f.toFun x y ≤ f.toFun (x + h) y := f.mono' y (by linarith)
  have h4 : f.toFun (x + -h) y ≤ f.toFun (x + -h) (y + h) := f.mono_snd (x + -h) (by linarith)
  have h5 : f.toFun (x - h) y = f.toFun (x + -h) y := by rw [sub_eq_add_neg]
  rw [abs_of_nonneg (by linarith), h5]
  linarith

/-- **The grid estimate.**  If `r` moves each point by at most `h` to the left, then replacing
`f` by `f ∘ (r, r)` costs at most `4h` in `L¹`.  This is the `‖V - Π_k V‖₁ ≤ 2/k` step of
`lem:ordered-compact`, with the two increments estimated separately. -/
theorem integral_abs_sub_comp_le {h : ℝ} (hh : 0 < h) {r : ℝ → ℝ} (hrm : Measurable r)
    (hr1 : ∀ x, r x ≤ x) (hr2 : ∀ x, x - h ≤ r x) :
    ∫ z, |f.toFun z.1 z.2 - f.toFun (r z.1) (r z.2)| ∂gμ ≤ 4 * h := by
  have hmr : Measurable fun z : ℝ × ℝ => f.toFun (r z.1) (r z.2) :=
    f.meas'.comp ((hrm.comp measurable_fst).prodMk (hrm.comp measurable_snd))
  have hintl : Integrable (fun z : ℝ × ℝ => |f.toFun z.1 z.2 - f.toFun (r z.1) (r z.2)|) gμ := by
    refine integrable_of_abs_le ((f.meas'.sub hmr).abs) 1 fun z => ?_
    rw [abs_abs]; exact f.abs_sub_le_one _ _ _ _
  have hint1 := f.integrable_window_fst h
  have hint2 := f.integrable_window_snd (-h) h
  have hmono := integral_mono hintl (hint1.add hint2) fun z =>
    f.abs_sub_le_window (hr2 z.1) (hr1 z.1) (hr2 z.2) (hr1 z.2) hh
  simp only [Pi.add_apply] at hmono
  rw [integral_add hint1 hint2] at hmono
  have e1 := f.integral_window_fst_le hh
  have e2 := f.integral_window_snd_le (a := -h) hh
  linarith

/-- Two monotone kernels composed with measurable reparametrisations differ by at most `1`. -/
theorem integrable_abs_sub (f g : MonotoneKernel) {r q : ℝ → ℝ} (hr : Measurable r)
    (hq : Measurable q) :
    Integrable (fun z : ℝ × ℝ => |f.toFun (r z.1) (r z.2) - g.toFun (q z.1) (q z.2)|) gμ := by
  refine integrable_of_abs_le (((f.meas'.comp
    ((hr.comp measurable_fst).prodMk (hr.comp measurable_snd))).sub
      (g.meas'.comp ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd)))).abs) 1 fun z => ?_
  rw [abs_abs]
  exact abs_le.mpr ⟨by linarith [f.nonneg' (r z.1) (r z.2), g.le_one' (q z.1) (q z.2)],
    by linarith [g.nonneg' (q z.1) (q z.2), f.le_one' (r z.1) (r z.2)]⟩

end MonotoneKernel

/-! ## The dyadic grid

`Π_k` of `lem:ordered-compact` is realised as composition with the dyadic floor
`x ↦ ⌊2^j x⌋ / 2^j`.  Dyadic levels are used rather than the levels `1/k` of the paper because
a dyadic grid point stays a grid point at every finer level, which identifies the limit kernel
with its own grid projection.
-/

/-- The level-`j` dyadic grid point below `x`, as a rational. -/
noncomputable def dyadQ (j : ℕ) (x : ℝ) : ℚ := (⌊(2:ℝ) ^ j * x⌋ : ℚ) / 2 ^ j

/-- The level-`j` dyadic grid point below `x`, as a real. -/
noncomputable def dyadR (j : ℕ) (x : ℝ) : ℝ := (⌊(2:ℝ) ^ j * x⌋ : ℝ) / 2 ^ j

/-- The rational and the real grid point agree. -/
theorem dyadQ_cast (j : ℕ) (x : ℝ) : ((dyadQ j x : ℚ) : ℝ) = dyadR j x := by
  simp [dyadQ, dyadR]

/-- The grid mesh `2^j` is positive. -/
theorem two_pow_pos (j : ℕ) : (0:ℝ) < 2 ^ j := by positivity

/-- The grid point lies below the point. -/
theorem dyadR_le (j : ℕ) (x : ℝ) : dyadR j x ≤ x := by
  rw [dyadR, div_le_iff₀ (two_pow_pos j), mul_comm x]
  exact Int.floor_le _

/-- The grid point lies within `2^{-j}` of the point. -/
theorem sub_le_dyadR (j : ℕ) (x : ℝ) : x - 1 / 2 ^ j ≤ dyadR j x := by
  have hpos := two_pow_pos j
  have h := Int.lt_floor_add_one ((2:ℝ) ^ j * x)
  rw [dyadR, le_div_iff₀ hpos]
  have hx : (x - 1 / 2 ^ j) * 2 ^ j = (2:ℝ) ^ j * x - 1 := by field_simp
  rw [hx]
  linarith

/-- The dyadic floor is nondecreasing. -/
theorem dyadQ_mono (j : ℕ) : Monotone (dyadQ j) := by
  intro x y hxy
  have h : ⌊(2:ℝ) ^ j * x⌋ ≤ ⌊(2:ℝ) ^ j * y⌋ :=
    Int.floor_mono (by nlinarith [two_pow_pos j])
  have h2 : (0:ℚ) < 2 ^ j := by positivity
  rw [dyadQ, dyadQ, div_le_div_iff_of_pos_right h2]
  exact_mod_cast h

/-- The dyadic floor is measurable. -/
theorem measurable_dyadR (j : ℕ) : Measurable (dyadR j) := by
  have h0 : Measurable fun x : ℝ => ⌊(2:ℝ) ^ j * x⌋ :=
    Int.measurable_floor.comp (measurable_const_mul _)
  have h : Measurable fun x : ℝ => (⌊(2:ℝ) ^ j * x⌋ : ℝ) :=
    (measurable_of_countable fun a : ℤ => (a : ℝ)).comp h0
  exact h.div_const _

/-- A dyadic grid point of level `j` is its own level-`j` grid point. -/
theorem dyadQ_dyadR (j : ℕ) (x : ℝ) : dyadQ j (dyadR j x) = dyadQ j x := by
  have h : (2:ℝ) ^ j * dyadR j x = (⌊(2:ℝ) ^ j * x⌋ : ℝ) := by
    rw [dyadR]; field_simp
  rw [dyadQ, dyadQ, h, Int.floor_intCast]

/-- On `[0,1]` the dyadic grid point has numerator in `{0, …, 2^j}`. -/
theorem floor_mem_Icc {j : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ⌊(2:ℝ) ^ j * x⌋ ∈ Finset.Icc (0:ℤ) (2 ^ j) := by
  have hpos := two_pow_pos j
  have h2 : ((2 ^ j : ℤ) : ℝ) = (2:ℝ) ^ j := by push_cast; ring
  refine Finset.mem_Icc.mpr ⟨Int.floor_nonneg.mpr (by nlinarith [hx.1]), ?_⟩
  have h1 : (2:ℝ) ^ j * x ≤ ((2 ^ j : ℤ) : ℝ) := by rw [h2]; nlinarith [hx.2]
  have h3 := Int.floor_mono h1
  rwa [Int.floor_intCast] at h3

/-- A level-`i` grid point of a level-`j` grid point never exceeds the latter. -/
theorem dyadQ_dyadR_le (i j : ℕ) (x : ℝ) : dyadQ i (dyadR j x) ≤ dyadQ j x := by
  have h : ((dyadQ i (dyadR j x) : ℚ) : ℝ) ≤ ((dyadQ j x : ℚ) : ℝ) := by
    rw [dyadQ_cast, dyadQ_cast]; exact dyadR_le i (dyadR j x)
  exact_mod_cast h

/-! ## From grid values to a monotone kernel

The subsequence produced by `lem:ordered-compact` converges at every pair of rationals.  The
resulting limit values form the following data, and `RatKernel.toMonotoneKernel` is the
representative `W̃` of the paper, defined as the supremum of the values at the grid points
below `(x,y)`.
-/

/-- **A monotone kernel on the rationals**: symmetric, with values in `[0,1]`, nondecreasing in
each variable.  This is the limit data extracted at the grid points in `lem:ordered-compact`. -/
structure RatKernel where
  /-- The values at pairs of rationals. -/
  toFun : ℚ × ℚ → ℝ
  symm' : ∀ r s, toFun (r, s) = toFun (s, r)
  nonneg' : ∀ rs, 0 ≤ toFun rs
  le_one' : ∀ rs, toFun rs ≤ 1
  mono' : ∀ s, Monotone fun r => toFun (r, s)

namespace RatKernel

variable (K : RatKernel)

/-- Monotonicity in the second variable. -/
theorem mono_snd (r : ℚ) : Monotone fun s => K.toFun (r, s) := by
  intro s s' hs
  simp only
  rw [K.symm' r s, K.symm' r s']
  exact K.mono' r hs

/-- Monotonicity in both variables at once. -/
theorem mono₂ {r r' s s' : ℚ} (hr : r ≤ r') (hs : s ≤ s') : K.toFun (r, s) ≤ K.toFun (r', s') :=
  (K.mono' s hr).trans (K.mono_snd r' hs)

/-- The grid values below `(x,y)` are bounded above by `1`. -/
theorem bddAbove_grid (x y : ℝ) :
    BddAbove (Set.range fun i : ℕ => K.toFun (dyadQ i x, dyadQ i y)) := by
  refine ⟨1, ?_⟩
  rintro a ⟨i, rfl⟩
  exact K.le_one' _

/-- **The representative `W̃` of `lem:ordered-compact`**: the supremum of the grid values below
`(x,y)`.  Taking the supremum over dyadic levels makes it measurable, and monotone in each
variable because each grid point is. -/
noncomputable def toMonotoneKernel : MonotoneKernel where
  toFun x y := ⨆ i : ℕ, K.toFun (dyadQ i x, dyadQ i y)
  symm' x y := by
    have h : (fun i : ℕ => K.toFun (dyadQ i x, dyadQ i y))
        = fun i : ℕ => K.toFun (dyadQ i y, dyadQ i x) := funext fun i => K.symm' _ _
    rw [h]
  meas' := by
    show Measurable fun z : ℝ × ℝ => ⨆ i : ℕ, K.toFun (dyadQ i z.1, dyadQ i z.2)
    refine Measurable.iSup fun i => ?_
    have hfl : Measurable fun z : ℝ × ℝ => (⌊(2:ℝ) ^ i * z.1⌋, ⌊(2:ℝ) ^ i * z.2⌋) :=
      (Int.measurable_floor.comp ((measurable_const_mul _).comp measurable_fst)).prodMk
        (Int.measurable_floor.comp ((measurable_const_mul _).comp measurable_snd))
    exact (measurable_of_countable fun ab : ℤ × ℤ =>
      K.toFun ((ab.1 : ℚ) / 2 ^ i, (ab.2 : ℚ) / 2 ^ i)).comp hfl
  nonneg' x y := le_ciSup_of_le (K.bddAbove_grid x y) 0 (K.nonneg' _)
  le_one' x y := ciSup_le fun i => K.le_one' _
  mono' y x x' hx := ciSup_mono (K.bddAbove_grid x' y) fun i => K.mono' _ (dyadQ_mono i hx)

@[simp] theorem toMonotoneKernel_apply (x y : ℝ) :
    K.toMonotoneKernel.toFun x y = ⨆ i : ℕ, K.toFun (dyadQ i x, dyadQ i y) := rfl

/-- **The limit kernel is its own grid projection.**  At a level-`j` grid point the supremum is
attained at level `j`. -/
theorem toMonotoneKernel_dyad (j : ℕ) (x y : ℝ) :
    K.toMonotoneKernel.toFun (dyadR j x) (dyadR j y) = K.toFun (dyadQ j x, dyadQ j y) := by
  rw [toMonotoneKernel_apply]
  refine le_antisymm (ciSup_le fun i => K.mono₂ (dyadQ_dyadR_le i j x) (dyadQ_dyadR_le i j y)) ?_
  refine le_ciSup_of_le (K.bddAbove_grid _ _) j ?_
  rw [dyadQ_dyadR, dyadQ_dyadR]

end RatKernel

/-! ## The compactness statement -/

/-- The level-`j` dyadic grid points of `[0,1]²`, as pairs of rationals. -/
noncomputable def dyadGrid (j : ℕ) : Finset (ℚ × ℚ) :=
  (Finset.Icc (0:ℤ) (2 ^ j) ×ˢ Finset.Icc (0:ℤ) (2 ^ j)).image
    fun ab => ((ab.1 : ℚ) / 2 ^ j, (ab.2 : ℚ) / 2 ^ j)

/-- On `[0,1]²` the grid point of `(x,y)` is one of the finitely many grid points. -/
theorem dyadQ_mem_dyadGrid {j : ℕ} {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) : (dyadQ j x, dyadQ j y) ∈ dyadGrid j :=
  Finset.mem_image.mpr ⟨(⌊(2:ℝ) ^ j * x⌋, ⌊(2:ℝ) ^ j * y⌋),
    Finset.mem_product.mpr ⟨floor_mem_Icc hx, floor_mem_Icc hy⟩, rfl⟩

/-- Almost every point of `[0,1]²` lies in `[0,1]²`. -/
theorem ae_mem_Icc_gμ : ∀ᵐ z ∂gμ, z.1 ∈ Set.Icc (0:ℝ) 1 ∧ z.2 ∈ Set.Icc (0:ℝ) 1 := by
  have h0 : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0:ℝ) 1 := by
    rw [unitμ]; exact ae_restrict_mem measurableSet_Icc
  have h1 : ∀ᵐ z ∂gμ, z.1 ∈ Set.Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae h0
  have h2 : ∀ᵐ z ∂gμ, z.2 ∈ Set.Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_snd.ae h0
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

/-- **Compactness of ordered graphons**, `lem:ordered-compact`.  A sequence of graphons with
ordered rows has a subsequence converging in `L¹` to a graphon with ordered rows.  The paper
states this for graphons with an ordered structure and relabels them first;
`exists_hasOrderedRows_of_isOrderedMultipodal` is that step for the ordered multipodal graphons
this is applied to. -/
theorem ordered_compact (W : ℕ → Graphon) (hW : ∀ n, HasOrderedRows (W n)) :
    ∃ (φ : ℕ → ℕ) (W' : Graphon), StrictMono φ ∧ HasOrderedRows W' ∧
      Filter.Tendsto (fun n => ∫ z, |(W (φ n)).toFun z.1 z.2 - W'.toFun z.1 z.2| ∂gμ)
        Filter.atTop (nhds 0) := by
  classical
  choose f hf using hW
  -- the values at the rationals, a sequence in a compact cube
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → (ℚ × ℚ → ℝ),
      ∀ n rs, A n rs = (f n).toFun ((rs : ℚ × ℚ).1 : ℝ) ((rs : ℚ × ℚ).2 : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  have hcpt : IsCompact (Set.univ.pi fun _ : ℚ × ℚ => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨L, hLmem, φ, hφ, hconv⟩ :=
    hcpt.tendsto_subseq (x := A) fun n =>
      Set.mem_univ_pi.mpr fun rs => (hAdef n rs) ▸ (f n).mem_Icc _ _
  have hpt : ∀ rs : ℚ × ℚ, Filter.Tendsto (fun n => A (φ n) rs) Filter.atTop (nhds (L rs)) :=
    fun rs => tendsto_pi_nhds.mp hconv rs
  have hLIcc : ∀ rs, L rs ∈ Set.Icc (0:ℝ) 1 := fun rs => Set.mem_univ_pi.mp hLmem rs
  -- the limit data is again a monotone kernel on the rationals
  have hLsymm : ∀ r s : ℚ, L (r, s) = L (s, r) := by
    intro r s
    refine tendsto_nhds_unique (hpt (r, s)) ?_
    have h : (fun n => A (φ n) (s, r)) = fun n => A (φ n) (r, s) := by
      funext n
      rw [hAdef, hAdef]
      exact (f (φ n)).symm' _ _
    rw [← h]; exact hpt (s, r)
  have hLmono : ∀ s : ℚ, Monotone fun r => L (r, s) := by
    intro s r r' hr
    refine le_of_tendsto_of_tendsto' (hpt (r, s)) (hpt (r', s)) fun n => ?_
    rw [hAdef, hAdef]
    exact (f (φ n)).mono' (s : ℝ) (by exact_mod_cast hr)
  -- the limit kernel, kept opaque through its defining property at the grid points
  obtain ⟨F, hFdyad⟩ : ∃ F : MonotoneKernel, ∀ (j : ℕ) (x y : ℝ),
      F.toFun (dyadR j x) (dyadR j y) = L (dyadQ j x, dyadQ j y) :=
    ⟨RatKernel.toMonotoneKernel
        ⟨L, hLsymm, fun rs => (hLIcc rs).1, fun rs => (hLIcc rs).2, hLmono⟩,
      fun j x y => RatKernel.toMonotoneKernel_dyad _ j x y⟩
  refine ⟨φ, F.toGraphon, hφ, F.hasOrderedRows, ?_⟩
  -- pass from `W (φ n)` to its monotone representative
  have hcongr : ∀ n : ℕ,
      (∫ z, |(W (φ n)).toFun z.1 z.2 - F.toGraphon.toFun z.1 z.2| ∂gμ)
        = ∫ z, |(f (φ n)).toFun z.1 z.2 - F.toFun z.1 z.2| ∂gμ := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [hf (φ n)] with z hz
    simp only [MonotoneKernel.toGraphon_apply, hz]
  refine Filter.Tendsto.congr (fun n => (hcongr n).symm) ?_
  -- the three-term estimate
  have key : ∀ j m : ℕ, (∫ z, |(f m).toFun z.1 z.2 - F.toFun z.1 z.2| ∂gμ)
      ≤ 8 * (1 / 2 ^ j) + ∑ rs ∈ dyadGrid j, |A m rs - L rs| := by
    intro j m
    have hh : (0:ℝ) < 1 / 2 ^ j := by positivity
    have hd := measurable_dyadR j
    have hI : Integrable (fun z : ℝ × ℝ => |(f m).toFun z.1 z.2 - F.toFun z.1 z.2|) gμ :=
      MonotoneKernel.integrable_abs_sub (f m) F measurable_id measurable_id
    have hI1 : Integrable (fun z : ℝ × ℝ =>
        |(f m).toFun z.1 z.2 - (f m).toFun (dyadR j z.1) (dyadR j z.2)|) gμ :=
      MonotoneKernel.integrable_abs_sub (f m) (f m) measurable_id hd
    have hI2 : Integrable (fun z : ℝ × ℝ =>
        |(f m).toFun (dyadR j z.1) (dyadR j z.2) - F.toFun (dyadR j z.1) (dyadR j z.2)|) gμ :=
      MonotoneKernel.integrable_abs_sub (f m) F hd hd
    have hI3 : Integrable (fun z : ℝ × ℝ =>
        |F.toFun z.1 z.2 - F.toFun (dyadR j z.1) (dyadR j z.2)|) gμ :=
      MonotoneKernel.integrable_abs_sub F F measurable_id hd
    have tri : ∀ z : ℝ × ℝ, |(f m).toFun z.1 z.2 - F.toFun z.1 z.2| ≤
        (|(f m).toFun z.1 z.2 - (f m).toFun (dyadR j z.1) (dyadR j z.2)|
          + |(f m).toFun (dyadR j z.1) (dyadR j z.2) - F.toFun (dyadR j z.1) (dyadR j z.2)|)
        + |F.toFun z.1 z.2 - F.toFun (dyadR j z.1) (dyadR j z.2)| := by
      intro z
      have t1 := abs_sub_le ((f m).toFun z.1 z.2) (F.toFun (dyadR j z.1) (dyadR j z.2))
        (F.toFun z.1 z.2)
      have t2 := abs_sub_le ((f m).toFun z.1 z.2) ((f m).toFun (dyadR j z.1) (dyadR j z.2))
        (F.toFun (dyadR j z.1) (dyadR j z.2))
      have t3 := abs_sub_comm (F.toFun (dyadR j z.1) (dyadR j z.2)) (F.toFun z.1 z.2)
      linarith
    have hI12 : Integrable (fun z : ℝ × ℝ =>
        |(f m).toFun z.1 z.2 - (f m).toFun (dyadR j z.1) (dyadR j z.2)|
          + |(f m).toFun (dyadR j z.1) (dyadR j z.2)
              - F.toFun (dyadR j z.1) (dyadR j z.2)|) gμ := hI1.add hI2
    have hI123 : Integrable (fun z : ℝ × ℝ =>
        (|(f m).toFun z.1 z.2 - (f m).toFun (dyadR j z.1) (dyadR j z.2)|
          + |(f m).toFun (dyadR j z.1) (dyadR j z.2)
              - F.toFun (dyadR j z.1) (dyadR j z.2)|)
          + |F.toFun z.1 z.2 - F.toFun (dyadR j z.1) (dyadR j z.2)|) gμ := hI12.add hI3
    have step := integral_mono hI hI123 tri
    rw [integral_add hI12 hI3, integral_add hI1 hI2] at step
    -- the two grid errors
    have e1 := (f m).integral_abs_sub_comp_le hh hd (dyadR_le j) (sub_le_dyadR j)
    have e3 := F.integral_abs_sub_comp_le hh hd (dyadR_le j) (sub_le_dyadR j)
    -- the middle term is bounded by the finite sum of grid errors
    have e2 : (∫ z, |(f m).toFun (dyadR j z.1) (dyadR j z.2)
          - F.toFun (dyadR j z.1) (dyadR j z.2)| ∂gμ)
        ≤ ∑ rs ∈ dyadGrid j, |A m rs - L rs| := by
      have hbound : ∀ᵐ z ∂gμ, |(f m).toFun (dyadR j z.1) (dyadR j z.2)
          - F.toFun (dyadR j z.1) (dyadR j z.2)| ≤ ∑ rs ∈ dyadGrid j, |A m rs - L rs| := by
        filter_upwards [ae_mem_Icc_gμ] with z hz
        have hval : |(f m).toFun (dyadR j z.1) (dyadR j z.2)
            - F.toFun (dyadR j z.1) (dyadR j z.2)|
            = |A m (dyadQ j z.1, dyadQ j z.2) - L (dyadQ j z.1, dyadQ j z.2)| := by
          rw [hFdyad j z.1 z.2, hAdef m (dyadQ j z.1, dyadQ j z.2), dyadQ_cast, dyadQ_cast]
        rw [hval]
        exact Finset.single_le_sum (f := fun rs : ℚ × ℚ => |A m rs - L rs|)
          (fun rs _ => abs_nonneg _) (dyadQ_mem_dyadGrid hz.1 hz.2)
      calc (∫ z, |(f m).toFun (dyadR j z.1) (dyadR j z.2)
              - F.toFun (dyadR j z.1) (dyadR j z.2)| ∂gμ)
          ≤ ∫ _ : ℝ × ℝ, (∑ rs ∈ dyadGrid j, |A m rs - L rs|) ∂gμ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const _) hbound
        _ = ∑ rs ∈ dyadGrid j, |A m rs - L rs| := by simp
    linarith
  -- the grid errors vanish along the subsequence
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ((1:ℝ) / 2) ^ j < ε / 16 :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  rw [div_pow, one_pow] at hj
  have hterm : ∀ rs : ℚ × ℚ,
      Filter.Tendsto (fun n => |A (φ n) rs - L rs|) Filter.atTop (nhds 0) := fun rs => by
    have := ((hpt rs).sub_const (L rs)).abs
    simpa using this
  have hsum : Filter.Tendsto (fun n => ∑ rs ∈ dyadGrid j, |A (φ n) rs - L rs|)
      Filter.atTop (nhds 0) := by
    have := tendsto_finsetSum (dyadGrid j) fun rs _ => hterm rs
    simpa using this
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨N, hN⟩ := hsum (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hnn : 0 ≤ ∫ z, |(f (φ n)).toFun z.1 z.2 - F.toFun z.1 z.2| ∂gμ :=
    integral_nonneg fun _ => abs_nonneg _
  have hsn := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hsn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hkey := key j (φ n)
  linarith


/-! ## Ordered blocks give ordered rows

`sec:degenerate-optimizers` relabels a multipodal graphon with ordered blocks so that the blocks
become consecutive intervals of `[0,1]`.  Instead of building the relabelling we compare the
two graphons through their block index maps: a block structure pushes `unitμ` forward to a
measure on `Fin M` whose weights are the block measures, and every functional of the graphon
is an integral of the block values against that measure.  Two block structures with the same
values and the same block measures therefore give the same `e`, `t(H,·)` and `I_p`.
-/

namespace BlockStructure

variable {M : ℕ}

/-- A block structure has at least one block: the blocks cover a probability space. -/
theorem pos (B : BlockStructure M) : 0 < M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have h := MeasureTheory.ae_iff.mp B.cover
    have huniv : {x : ℝ | ¬ ∃ i : Fin 0, x ∈ B.block i} = Set.univ :=
      Set.eq_univ_of_forall fun _ h => h.choose.elim0
    rw [huniv, measure_univ] at h
    exact absurd h one_ne_zero
  · exact hM

/-- **The block index map.**  A measurable labelling of `[0,1]` by blocks, arbitrary on the
null set left uncovered. -/
theorem exists_index (B : BlockStructure M) :
    ∃ ι : ℝ → Fin M, Measurable ι ∧ ∀ i x, x ∈ B.block i → ι x = i := by
  classical
  obtain ⟨ι, hι, hout⟩ : ∃ ι : ℝ → Fin M, (∀ i x, x ∈ B.block i → ι x = i) ∧
      (∀ x, (∀ j, x ∉ B.block j) → ι x = ⟨0, B.pos⟩) := by
    refine ⟨fun x => if h : ∃ i, x ∈ B.block i then h.choose else ⟨0, B.pos⟩, ?_, ?_⟩
    · intro i x hx
      have h : ∃ j, x ∈ B.block j := ⟨i, hx⟩
      simp only [dif_pos h]
      by_contra hne
      exact Set.disjoint_left.mp (B.pairwise_disjoint hne) h.choose_spec hx
    · intro x hx
      have h : ¬ ∃ j, x ∈ B.block j := fun hj => hx hj.choose hj.choose_spec
      simp only [dif_neg h]
  refine ⟨ι, ?_, hι⟩
  refine measurable_to_countable' fun i => ?_
  by_cases hi : i = ⟨0, B.pos⟩
  · have hset : ι ⁻¹' {i} = B.block i ∪ (⋃ j, B.block j)ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iUnion, not_exists]
      constructor
      · intro hxi
        by_cases hx : ∃ j, x ∈ B.block j
        · obtain ⟨j, hj⟩ := hx
          left
          rw [← hxi, hι j x hj]
          exact hj
        · exact Or.inr fun j hj => hx ⟨j, hj⟩
      · rintro (h | h)
        · exact hι i x h
        · rw [hi]; exact hout x h
    rw [hset]
    exact (B.measurableSet_block i).union
      (MeasurableSet.iUnion fun j => B.measurableSet_block j).compl
  · have hset : ι ⁻¹' {i} = B.block i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hxi
        by_cases hx : ∃ j, x ∈ B.block j
        · obtain ⟨j, hj⟩ := hx
          rw [← hxi, hι j x hj]
          exact hj
        · exact absurd (hxi.symm.trans (hout x fun j hj => hx ⟨j, hj⟩)) hi
      · exact hι i x
    rw [hset]
    exact B.measurableSet_block i

/-- The masses of the fibres of the index map are the block measures. -/
theorem map_index_singleton (B : BlockStructure M) {ι : ℝ → Fin M} (hιm : Measurable ι)
    (hι : ∀ i x, x ∈ B.block i → ι x = i) (i : Fin M) :
    (unitμ.map ι) {i} = unitμ (B.block i) := by
  rw [Measure.map_apply hιm (measurableSet_singleton i)]
  refine measure_congr ?_
  rw [Filter.eventuallyEq_set]
  filter_upwards [B.cover] with x hx
  obtain ⟨j, hj⟩ := hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hι j x hj]
  exact ⟨fun h => h ▸ hj, fun h => (hι j x hj).symm.trans (hι i x h)⟩

/-- Almost everywhere, the graphon equals the value of the block pair of the point. -/
theorem represents_index (B : BlockStructure M) {W : Graphon} (hB : B.Represents W)
    {ι : ℝ → Fin M} (hι : ∀ i x, x ∈ B.block i → ι x = i) :
    ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = B.value (ι z.1) (ι z.2) := by
  have hall : ∀ᵐ z ∂gμ, ∀ i j, z.1 ∈ B.block i → z.2 ∈ B.block j →
      W.toFun z.1 z.2 = B.value i j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact fun j => hB i j
  have h1 : ∀ᵐ z ∂gμ, ∃ i, z.1 ∈ B.block i := Measure.quasiMeasurePreserving_fst.ae B.cover
  have h2 : ∀ᵐ z ∂gμ, ∃ j, z.2 ∈ B.block j := Measure.quasiMeasurePreserving_snd.ae B.cover
  filter_upwards [hall, h1, h2] with z hz h1z h2z
  obtain ⟨i, hi⟩ := h1z
  obtain ⟨j, hj⟩ := h2z
  rw [hz i j hi hj, hι i z.1 hi, hι j z.2 hj]

/-- **Every two-variable functional of a multipodal graphon is an integral of the block
values.** -/
theorem integral_eq (B : BlockStructure M) {W : Graphon} (hB : B.Represents W) {ι : ℝ → Fin M}
    (hιm : Measurable ι) (hι : ∀ i x, x ∈ B.block i → ι x = i) (g : ℝ → ℝ) :
    (∫ z, g (W.toFun z.1 z.2) ∂gμ)
      = ∫ w, g (B.value w.1 w.2) ∂((unitμ.map ι).prod (unitμ.map ι)) := by
  have : IsProbabilityMeasure (unitμ.map ι) := Measure.isProbabilityMeasure_map hιm.aemeasurable
  have hmpι : MeasurePreserving ι unitμ (unitμ.map ι) := ⟨hιm, rfl⟩
  have hmp : MeasurePreserving (fun z : ℝ × ℝ => (ι z.1, ι z.2)) gμ
      ((unitμ.map ι).prod (unitμ.map ι)) := by
    rw [gμ]; exact hmpι.prod hmpι
  have hint : Measurable fun w : Fin M × Fin M => g (B.value w.1 w.2) := measurable_of_countable _
  have hmap := integral_map (μ := gμ) (φ := fun z : ℝ × ℝ => (ι z.1, ι z.2))
    hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  rw [hmap]
  refine integral_congr_ae ((B.represents_index hB hι).mono fun z hz => ?_)
  simp only [hz]

/-- **The homomorphism density of a multipodal graphon is an integral of the block values.** -/
theorem tDensity_eq (B : BlockStructure M) {W : Graphon} (hB : B.Represents W) {ι : ℝ → Fin M}
    (hιm : Measurable ι) (hι : ∀ i x, x ∈ B.block i → ι x = i) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    W.tDensity H = ∫ y : V → Fin M, ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => B.value (y a) (y b), fun a b => B.value_symm (y a) (y b)⟩ e
      ∂(Measure.pi fun _ : V => unitμ.map ι) := by
  classical
  have : IsProbabilityMeasure (unitμ.map ι) := Measure.isProbabilityMeasure_map hιm.aemeasurable
  have hrep := B.represents_index hB hι
  have hpi : MeasurePreserving (fun x : V → ℝ => fun v => ι (x v))
      (Measure.pi fun _ : V => unitμ) (Measure.pi fun _ : V => unitμ.map ι) :=
    measurePreserving_pi _ _ fun _ => ⟨hιm, rfl⟩
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e
        = Sym2.lift ⟨fun a b => B.value (ι (x a)) (ι (x b)),
            fun a b => B.value_symm _ _⟩ e := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact (measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae_eq hrep
  have hall := (Filter.eventually_all_finset _).mpr hedge
  have hstep : W.tDensity H
      = ∫ x : V → ℝ, ∏ e ∈ H.edgeFinset,
          Sym2.lift ⟨fun a b => B.value (ι (x a)) (ι (x b)),
            fun a b => B.value_symm _ _⟩ e ∂(Measure.pi fun _ : V => unitμ) := by
    unfold Graphon.tDensity
    exact integral_congr_ae (hall.mono fun x hx => Finset.prod_congr rfl fun e he => hx e he)
  have hmeas : Measurable fun y : V → Fin M => ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => B.value (y a) (y b), fun a b => B.value_symm (y a) (y b)⟩ e :=
    measurable_of_countable _
  have hmap := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun x : V → ℝ => fun v => ι (x v)) hpi.measurable.aemeasurable
    (by rw [hpi.map_eq]; exact hmeas.aestronglyMeasurable)
  rw [hpi.map_eq] at hmap
  rw [hstep, hmap]

/-- Specialisation of `BlockStructure.integral_eq` to the edge density. -/
theorem edgeDensity_eq (B : BlockStructure M) {W : Graphon} (hB : B.Represents W)
    {ι : ℝ → Fin M} (hιm : Measurable ι) (hι : ∀ i x, x ∈ B.block i → ι x = i) :
    W.edgeDensity = ∫ w, B.value w.1 w.2 ∂((unitμ.map ι).prod (unitμ.map ι)) :=
  B.integral_eq hB hιm hι fun t => t

/-- Specialisation of `BlockStructure.integral_eq` to `I_p`. -/
theorem Ip_eq (B : BlockStructure M) {W : Graphon} (hB : B.Represents W) {ι : ℝ → Fin M}
    (hιm : Measurable ι) (hι : ∀ i x, x ∈ B.block i → ι x = i) (p : ℝ) :
    W.Ip p = ∫ w, Jp p (B.value w.1 w.2) ∂((unitμ.map ι).prod (unitμ.map ι)) :=
  B.integral_eq hB hιm hι (Jp p)

/-! ### The sorted step graphon

Listing the blocks in order and giving them consecutive intervals of `[0,1]` of the right
lengths produces the representative of `sec:degenerate-optimizers` that is nondecreasing in each
variable.
-/

/-- The cumulative block measures `c_k = m_0 + ⋯ + m_{k-1}`. -/
noncomputable def cum (B : BlockStructure M) (k : ℕ) : ℝ :=
  ∑ i : Fin M, if (i : ℕ) < k then (unitμ (B.block i)).toReal else 0

/-- The cumulative block measures are nonnegative. -/
theorem cum_nonneg (B : BlockStructure M) (k : ℕ) : 0 ≤ B.cum k :=
  Finset.sum_nonneg fun i _ => by
    split
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

/-- The cumulative block measures are nondecreasing. -/
theorem cum_mono (B : BlockStructure M) : Monotone B.cum := by
  intro k l hkl
  refine Finset.sum_le_sum fun i _ => ?_
  split
  · rw [if_pos (by omega)]
  · split
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

/-- The first interval starts at `0`. -/
theorem cum_zero (B : BlockStructure M) : B.cum 0 = 0 := by
  simp [cum]

/-- Consecutive cumulative measures differ by the measure of the block between them. -/
theorem cum_succ (B : BlockStructure M) (i : Fin M) :
    B.cum ((i : ℕ) + 1) = B.cum i + (unitμ (B.block i)).toReal := by
  classical
  have hterm : ∀ j : Fin M, (if (j : ℕ) < (i : ℕ) + 1 then (unitμ (B.block j)).toReal else 0)
      = (if (j : ℕ) < (i : ℕ) then (unitμ (B.block j)).toReal else 0)
        + (if j = i then (unitμ (B.block j)).toReal else 0) := by
    intro j
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
    · have hne : j ≠ i := fun hh => by rw [hh] at h; exact absurd h (lt_irrefl _)
      rw [if_pos (by omega), if_pos h, if_neg hne, add_zero]
    · rw [if_pos (by omega), if_neg (by omega), if_pos (Fin.ext h), zero_add]
    · have hne : j ≠ i := fun hh => by rw [hh] at h; exact absurd h (lt_irrefl _)
      rw [if_neg (by omega), if_neg (by omega), if_neg hne, add_zero]
  simp only [cum]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  simp

/-- The block measures sum to `1`: the blocks are disjoint and cover `[0,1]`. -/
theorem sum_measure_block (B : BlockStructure M) : ∑ i : Fin M, unitμ (B.block i) = 1 := by
  have hnull : unitμ ((⋃ i, B.block i)ᶜ) = 0 := by
    have h0 := MeasureTheory.ae_iff.mp B.cover
    have hset : {x : ℝ | ¬ ∃ i, x ∈ B.block i} = (⋃ i, B.block i)ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    rwa [hset] at h0
  have hfull : unitμ (⋃ i, B.block i) = 1 := by
    have h := measure_add_measure_compl (μ := unitμ)
      (MeasurableSet.iUnion B.measurableSet_block)
    rw [hnull, add_zero, measure_univ] at h
    exact h
  rw [← hfull, measure_iUnion B.pairwise_disjoint B.measurableSet_block, tsum_fintype]

/-- The last interval ends at `1`. -/
theorem cum_all (B : BlockStructure M) : B.cum M = 1 := by
  have h : B.cum M = ∑ i : Fin M, (unitμ (B.block i)).toReal :=
    Finset.sum_congr rfl fun i _ => if_pos i.isLt
  rw [h, ← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), B.sum_measure_block,
    ENNReal.toReal_one]

/-- The cumulative block measures stay in `[0,1]`. -/
theorem cum_le_one (B : BlockStructure M) (k : ℕ) : B.cum k ≤ 1 := by
  rw [← B.cum_all]
  simp only [cum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [if_pos i.isLt]
  split
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

/-- The `i`-th interval of the sorted block structure. -/
noncomputable def sortedBlock (B : BlockStructure M) (i : Fin M) : Set ℝ :=
  Set.Ico (B.cum i) (B.cum ((i : ℕ) + 1))

/-- The sorted blocks are contained in `[0,1]`. -/
theorem sortedBlock_subset (B : BlockStructure M) (i : Fin M) :
    B.sortedBlock i ⊆ Set.Icc (0:ℝ) 1 := fun _ hx =>
  ⟨le_trans (B.cum_nonneg _) hx.1, le_trans hx.2.le (B.cum_le_one _)⟩

/-- The `i`-th interval has the measure of the `i`-th block. -/
theorem measure_sortedBlock (B : BlockStructure M) (i : Fin M) :
    unitμ (B.sortedBlock i) = unitμ (B.block i) := by
  rw [sortedBlock, unitμ, Measure.restrict_apply' measurableSet_Icc,
    Set.inter_eq_self_of_subset_left (by rw [← sortedBlock]; exact B.sortedBlock_subset i),
    Real.volume_Ico, B.cum_succ i, add_sub_cancel_left]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- The label of the interval containing `x`, as a natural number. -/
noncomputable def sortedIdxNat (B : BlockStructure M) (x : ℝ) : ℕ :=
  (Finset.range M).sup fun k => if B.cum k ≤ x then k else 0

/-- The interval label is a valid block label. -/
theorem sortedIdxNat_lt (B : BlockStructure M) (x : ℝ) : B.sortedIdxNat x < M := by
  unfold sortedIdxNat
  refine (Finset.sup_lt_iff B.pos).mpr fun k hk => ?_
  split
  · exact Finset.mem_range.mp hk
  · exact B.pos

/-- The label of the interval containing `x`. -/
noncomputable def sortedIdx (B : BlockStructure M) (x : ℝ) : Fin M :=
  ⟨B.sortedIdxNat x, B.sortedIdxNat_lt x⟩

/-- The interval label is nondecreasing. -/
theorem sortedIdxNat_mono (B : BlockStructure M) : Monotone B.sortedIdxNat := by
  intro x y hxy
  unfold sortedIdxNat
  refine Finset.sup_mono_fun fun k _ => ?_
  by_cases hc : B.cum k ≤ x
  · rw [if_pos hc, if_pos (hc.trans hxy)]
  · rw [if_neg hc]
    exact Nat.zero_le _

/-- The interval label is nondecreasing. -/
theorem sortedIdx_mono (B : BlockStructure M) : Monotone B.sortedIdx := fun _ _ hxy =>
  Fin.mk_le_mk.mpr (B.sortedIdxNat_mono hxy)

/-- The interval label is measurable, being nondecreasing. -/
theorem measurable_sortedIdx (B : BlockStructure M) : Measurable B.sortedIdx :=
  B.sortedIdx_mono.measurable

/-- On the `i`-th interval the label is `i`. -/
theorem sortedIdxNat_eq (B : BlockStructure M) {i : Fin M} {x : ℝ} (hx : x ∈ B.sortedBlock i) :
    B.sortedIdxNat x = (i : ℕ) := by
  refine le_antisymm ?_ ?_
  · unfold sortedIdxNat
    refine Finset.sup_le fun k _ => ?_
    by_cases hc : B.cum k ≤ x
    · rw [if_pos hc]
      by_contra hlt
      have h1 : B.cum ((i : ℕ) + 1) ≤ B.cum k := B.cum_mono (by omega)
      exact absurd (lt_of_lt_of_le hx.2 (h1.trans hc)) (lt_irrefl _)
    · rw [if_neg hc]
      exact Nat.zero_le _
  · have h := Finset.le_sup (f := fun k => if B.cum k ≤ x then k else 0)
      (Finset.mem_range.mpr i.isLt)
    rw [if_pos hx.1] at h
    exact h

/-- On the `i`-th interval the label is `i`. -/
theorem sortedIdx_eq (B : BlockStructure M) {i : Fin M} {x : ℝ} (hx : x ∈ B.sortedBlock i) :
    B.sortedIdx x = i := Fin.ext (B.sortedIdxNat_eq hx)

/-- Every point of `[0,1)` lies in the interval of its own label. -/
theorem mem_sortedBlock_sortedIdx (B : BlockStructure M) {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) :
    x ∈ B.sortedBlock (B.sortedIdx x) := by
  show x ∈ Set.Ico (B.cum (B.sortedIdxNat x)) (B.cum (B.sortedIdxNat x + 1))
  obtain ⟨k, -, hks⟩ := Finset.exists_mem_eq_sup (Finset.range M)
    ⟨0, Finset.mem_range.mpr B.pos⟩ fun k => if B.cum k ≤ x then k else 0
  have hsup : B.sortedIdxNat x = (if B.cum k ≤ x then k else 0) := hks
  have hlow : B.cum (B.sortedIdxNat x) ≤ x := by
    by_cases hc : B.cum k ≤ x
    · rw [hsup, if_pos hc]; exact hc
    · rw [hsup, if_neg hc, B.cum_zero]; exact hx.1
  refine ⟨hlow, ?_⟩
  rcases Nat.lt_or_ge (B.sortedIdxNat x + 1) M with hlt | hge
  · by_contra hcon
    have h := Finset.le_sup (f := fun k => if B.cum k ≤ x then k else 0)
      (Finset.mem_range.mpr hlt)
    rw [if_pos (not_lt.mp hcon)] at h
    have h' : B.sortedIdxNat x + 1 ≤ B.sortedIdxNat x := h
    omega
  · have hEq : B.sortedIdxNat x + 1 = M := le_antisymm (B.sortedIdxNat_lt x) hge
    rw [hEq, B.cum_all]
    exact hx.2

/-- **The sorted step kernel.**  Consecutive intervals carrying the ordered block values give a
kernel that is nondecreasing in each variable. -/
noncomputable def sortedKernel (B : BlockStructure M) (hord : B.Ordered) : MonotoneKernel where
  toFun x y := B.value (B.sortedIdx x) (B.sortedIdx y)
  symm' x y := B.value_symm _ _
  meas' := by
    show Measurable fun z : ℝ × ℝ => B.value (B.sortedIdx z.1) (B.sortedIdx z.2)
    exact (measurable_of_countable fun w : Fin M × Fin M => B.value w.1 w.2).comp
      ((B.measurable_sortedIdx.comp measurable_fst).prodMk
        (B.measurable_sortedIdx.comp measurable_snd))
  nonneg' x y := (B.value_mem _ _).1
  le_one' x y := (B.value_mem _ _).2
  mono' y x x' hx := hord _ _ _ (B.sortedIdx_mono hx)

/-- The block structure of consecutive intervals. -/
noncomputable def sorted (B : BlockStructure M) : BlockStructure M where
  block := B.sortedBlock
  value := B.value
  measurableSet_block _ := measurableSet_Ico
  pairwise_disjoint := by
    have key : ∀ i j : Fin M, (i : ℕ) < (j : ℕ) →
        Disjoint (B.sortedBlock i) (B.sortedBlock j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : B.cum ((i : ℕ) + 1) ≤ B.cum (j : ℕ) := B.cum_mono (by omega)
      exact absurd (lt_of_lt_of_le hx.2 (h1.trans hx'.1)) (lt_irrefl _)
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with h | h
    · exact key i j h
    · exact (key j i (by omega)).symm
  cover := by
    have hone : unitμ {(1:ℝ)} = 0 := by
      refine le_antisymm ?_ zero_le
      calc unitμ {(1:ℝ)} ≤ volume {(1:ℝ)} := by
            rw [unitμ]; exact Measure.restrict_le_self {(1:ℝ)}
        _ = 0 := Real.volume_singleton
    have h2 : ∀ᵐ x ∂unitμ, x ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simpa using hone
    have h1 : ∀ᵐ x ∂unitμ, x ∈ Set.Icc (0:ℝ) 1 := by
      rw [unitμ]; exact ae_restrict_mem measurableSet_Icc
    filter_upwards [h1, h2] with x hx hx1
    exact ⟨B.sortedIdx x, B.mem_sortedBlock_sortedIdx ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩⟩
  value_symm := B.value_symm
  value_mem := B.value_mem

/-- The blocks of the sorted structure are the consecutive intervals. -/
@[simp] theorem sorted_block (B : BlockStructure M) : B.sorted.block = B.sortedBlock := rfl

/-- Sorting keeps the block values. -/
@[simp] theorem sorted_value (B : BlockStructure M) : B.sorted.value = B.value := rfl

/-- The sorted step kernel is represented by the sorted block structure. -/
theorem sorted_represents (B : BlockStructure M) (hord : B.Ordered) :
    B.sorted.Represents (B.sortedKernel hord).toGraphon := by
  intro i j
  refine Filter.Eventually.of_forall fun z hz1 hz2 => ?_
  show B.value (B.sortedIdx z.1) (B.sortedIdx z.2) = B.value i j
  rw [B.sortedIdx_eq hz1, B.sortedIdx_eq hz2]

end BlockStructure

/-- **Ordered blocks give ordered rows.**  A multipodal graphon with ordered blocks has a
relabelling with ordered rows; `sec:degenerate-optimizers` uses it before applying
`lem:ordered-compact`. -/
theorem exists_hasOrderedRows_of_isOrderedMultipodal {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {p : ℝ} {W : Graphon} (hW : IsOrderedMultipodal W) :
    ∃ W' : Graphon, HasOrderedRows W' ∧ W'.edgeDensity = W.edgeDensity ∧
      W'.tDensity H = W.tDensity H ∧ W'.Ip p = W.Ip p := by
  obtain ⟨M, B, hB, hord⟩ := hW
  obtain ⟨ι, hιm, hι⟩ := B.exists_index
  obtain ⟨ι', hι'm, hι'⟩ := B.sorted.exists_index
  have hmap : unitμ.map ι' = unitμ.map ι := by
    refine Measure.ext_of_singleton fun i => ?_
    rw [B.sorted.map_index_singleton hι'm hι' i, B.map_index_singleton hιm hι i,
      BlockStructure.sorted_block]
    exact B.measure_sortedBlock i
  refine ⟨(B.sortedKernel hord).toGraphon, (B.sortedKernel hord).hasOrderedRows, ?_, ?_, ?_⟩
  · rw [B.sorted.edgeDensity_eq (B.sorted_represents hord) hι'm hι',
      B.edgeDensity_eq hB hιm hι, hmap]
    rfl
  · rw [B.sorted.tDensity_eq (B.sorted_represents hord) hι'm hι' H,
      B.tDensity_eq hB hιm hι H, hmap]
    rfl
  · rw [B.sorted.Ip_eq (B.sorted_represents hord) hι'm hι' p, B.Ip_eq hB hιm hι p, hmap]
    rfl


end UpperTailMultipodality
