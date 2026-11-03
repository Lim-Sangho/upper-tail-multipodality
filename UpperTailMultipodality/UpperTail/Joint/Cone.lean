import UpperTailMultipodality.UpperTail.Joint.Basic
import UpperTailMultipodality.Insertion.FirstOrderRows
import UpperTailMultipodality.UpperTail.Support.Multiplier

/-!
# The cone of first-order changes (`lem:upper-tail-multiplier`)

`lem:insertion-first-order` inserts a block of measure `θc` with rows given by a row kernel `U`
and simultaneously moves the old values along a bounded symmetric direction `Z`.  The resulting
first-order changes of `I_p` and of the densities `t(H_j,·)` are

`a(U) = 2∫₀¹∫₀¹ J_p(U) - 2I_p(W)`,     `b_j(U) = ∫₀¹ ℛ_{j,W}(U t) dt - N t(H_j,W)`,
`DI_p(W)[Z] = ∫∫ J_p'(W) Z`,           `Dt_j(W)[Z] = ∫∫ 𝒟_{j,W} Z`,

and `insertionCone` is the set of vectors `(c a(U) + DI_p(W)[Z], (c b_j(U) + Dt_j(W)[Z])_j)`.

Constant row kernels give the single rows `u` of `eq:insertion-rates`; mixing two row kernels
(`Insertion.integral_mixRows`) makes the set convex, which is what the separation of
the proof of `lem:upper-tail-multiplier` needs.  This file proves that `insertionCone` is a convex cone containing `0` and
that it avoids the improving directions `{z | z_0 < 0, z_j > 0 for j active}`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Set Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The four first-order quantities -/

/-- `a(U) = 2∫₀¹∫₀¹ J_p(U) - 2I_p(W)`, the first-order change of `2I_p` under the insertion of
a block with rows `U` (`eq:insertion-rates`). -/
noncomputable def insertionEntropy (p : ℝ) (W : Graphon) (U : ℝ → ℝ → ℝ) : ℝ :=
  2 * ∫ t, (∫ y, Jp p (U t y) ∂unitμ) ∂unitμ - 2 * W.Ip p

/-- `b_j(U) = ∫₀¹ ℛ_{j,W}(U t) dt - N t(H_j,W)`, the first-order change of `t(H_j,·)` under the
insertion of a block with rows `U` (`eq:insertion-rates`). -/
noncomputable def insertionDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (U : ℝ → ℝ → ℝ) : ℝ :=
  (∫ t, totalRootedDensity H W (U t) ∂unitμ) - Fintype.card V * W.tDensity H

/-- `DI_p(W)[Z] = ∫∫ J_p'(W) Z`. -/
noncomputable def variationIp (p : ℝ) (W : Graphon) (Z : Kernel) : ℝ :=
  ∫ z, Jp' p (W.toFun z.1 z.2) * Z.toFun z.1 z.2 ∂gμ

/-- `Dt(H,W)[Z] = ∫∫ 𝒟_W Z`, `eq:density-derivative`. -/
noncomputable def variationDensity (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z : Kernel) : ℝ :=
  ∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ

/-- The directions used by the insertion: bounded symmetric kernels vanishing where `W` comes
within `η` of `0` or `1`, so that `W + sZ` is a graphon for all small `s`. -/
def AdmissibleDir (W : Graphon) (η : ℝ) (Z : Kernel) : Prop :=
  ∀ x y, Z.toFun x y ≠ 0 → η < W.toFun x y ∧ W.toFun x y < 1 - η

/-- **The cone `𝒞` of `lem:upper-tail-multiplier`.** -/
def insertionCone {ι : Type*} (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (p : ℝ) (W : Graphon) (η : ℝ) : Set (ℝ × (ι → ℝ)) :=
  {w | ∃ (c : ℝ) (U : ℝ → ℝ → ℝ) (Z : Kernel), 0 ≤ c ∧ IsRows U ∧ AdmissibleDir W η Z ∧
    w = (c * insertionEntropy p W U + variationIp p W Z,
      fun j => c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z)}

/-! ### Linearity of the first variations -/

section Variation

variable {p : ℝ} {W : Graphon}

/-- `DI_p(W)[·]` is additive, for `W` in a compact subinterval of `(0,1)`. -/
theorem variationIp_add {a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : b < 1)
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc a b) (Z₁ Z₂ : Kernel) :
    variationIp p W (Z₁ + Z₂) = variationIp p W Z₁ + variationIp p W Z₂ := by
  have h1 := integrable_Jp'_mul W Z₁ hp0 hp1 ha hb hW
  have h2 := integrable_Jp'_mul W Z₂ hp0 hp1 ha hb hW
  unfold variationIp
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show Jp' p (W.toFun z.1 z.2) * (Z₁ + Z₂).toFun z.1 z.2 = _
  rw [Kernel.add_apply]
  ring

/-- `DI_p(W)[·]` is homogeneous. -/
theorem variationIp_smul (r : ℝ) (Z : Kernel) :
    variationIp p W (r • Z) = r * variationIp p W Z := by
  unfold variationIp
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show Jp' p (W.toFun z.1 z.2) * (r • Z).toFun z.1 z.2 = _
  rw [Kernel.smul_apply]
  ring

/-- `Dt(H,W)[·]` is additive. -/
theorem variationDensity_add (H : SimpleGraph V) [DecidableRel H.Adj] (Z₁ Z₂ : Kernel) :
    variationDensity H W (Z₁ + Z₂) = variationDensity H W Z₁ + variationDensity H W Z₂ := by
  have h1 := integrable_derivKernel_mul H W Z₁
  have h2 := integrable_derivKernel_mul H W Z₂
  unfold variationDensity
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show derivKernel H W z.1 z.2 * (Z₁ + Z₂).toFun z.1 z.2 = _
  rw [Kernel.add_apply]
  ring

/-- `Dt(H,W)[·]` is homogeneous. -/
theorem variationDensity_smul (H : SimpleGraph V) [DecidableRel H.Adj] (r : ℝ) (Z : Kernel) :
    variationDensity H W (r • Z) = r * variationDensity H W Z := by
  unfold variationDensity
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show derivKernel H W z.1 z.2 * (r • Z).toFun z.1 z.2 = _
  rw [Kernel.smul_apply]
  ring

/-- A scalar multiple of an admissible direction is admissible. -/
theorem AdmissibleDir.smul {η : ℝ} {Z : Kernel} (hZ : AdmissibleDir W η Z) (r : ℝ) :
    AdmissibleDir W η (r • Z) := by
  intro x y h
  refine hZ x y fun hz => h ?_
  rw [Kernel.smul_apply, hz, mul_zero]

/-- A sum of admissible directions is admissible. -/
theorem AdmissibleDir.add {η : ℝ} {Z₁ Z₂ : Kernel} (h₁ : AdmissibleDir W η Z₁)
    (h₂ : AdmissibleDir W η Z₂) : AdmissibleDir W η (Z₁ + Z₂) := by
  intro x y h
  rw [Kernel.add_apply] at h
  by_cases hz₁ : Z₁.toFun x y = 0
  · exact h₂ x y fun hz₂ => h (by rw [hz₁, hz₂, add_zero])
  · exact h₁ x y hz₁

end Variation

/-! ### Mixing the insertion data -/

/-- `|∫ J_p(u)| ≤ C` for a row `u`, where `C` bounds `|J_p|` on `[0,1]`. -/
theorem abs_integral_Jp_row_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {C : ℝ}
    (hC : ∀ z ∈ Icc (0:ℝ) 1, |Jp p z| ≤ C) {u : ℝ → ℝ} (hu : IsRow u) :
    |∫ y, Jp p (u y) ∂unitμ| ≤ C := by
  refine (abs_integral_le_integral_abs).trans ?_
  have h := integral_mono (Rows.integrable_Jp_row hp0 hp1 hu).abs
    (integrable_const (μ := unitμ) C) fun y => hC _ (hu.2 y)
  rw [integral_const, probReal_univ, one_smul] at h
  exact h

/-- **A convex combination of insertion data is realized by a single insertion**: the mixture of
the two row kernels.  This is the convexity of the cone `𝒞`. -/
theorem exists_mix_insertionData {ι : Type*} (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (W : Graphon)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) {U₁ U₂ : ℝ → ℝ → ℝ} (hU₁ : IsRows U₁)
    (hU₂ : IsRows U₂) :
    ∃ U, IsRows U ∧
      (c₁ + c₂) * insertionEntropy p W U
        = c₁ * insertionEntropy p W U₁ + c₂ * insertionEntropy p W U₂ ∧
      ∀ j, (c₁ + c₂) * insertionDensity (Hs j) W U
        = c₁ * insertionDensity (Hs j) W U₁ + c₂ * insertionDensity (Hs j) W U₂ := by
  rcases eq_or_lt_of_le hc₁ with h1 | h1
  · refine ⟨U₂, hU₂, ?_, fun j => ?_⟩
    · rw [← h1]; ring
    · rw [← h1]; ring
  rcases eq_or_lt_of_le hc₂ with h2 | h2
  · refine ⟨U₁, hU₁, ?_, fun j => ?_⟩
    · rw [← h2]; ring
    · rw [← h2]; ring
  -- both coefficients are positive: mix with weight `c₁/(c₁+c₂)`
  set c : ℝ := c₁ + c₂ with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set lam : ℝ := c₁ / c with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlam1 : lam < 1 := by
    rw [hlamdef, div_lt_one hc, hcdef]; linarith
  have hcl : c * lam = c₁ := by rw [hlamdef]; field_simp
  have hcl' : c * (1 - lam) = c₂ := by rw [hlamdef]; field_simp; rw [hcdef]; ring
  refine ⟨mixRows lam U₁ U₂, isRows_mixRows lam hU₁ hU₂, ?_, fun j => ?_⟩
  · obtain ⟨C, hC⟩ := Rows.exists_abs_Jp_le hp0 hp1
    have hmix := integral_mixRows hlam0 hlam1 U₁ U₂
      (Φ := fun u => ∫ y, Jp p (u y) ∂unitμ)
      (measurable_integral_Jp_rows p hU₁) (measurable_integral_Jp_rows p hU₂)
      (fun t => abs_integral_Jp_row_le hp0 hp1 hC (isRow_rows hU₁ t))
      (fun t => abs_integral_Jp_row_le hp0 hp1 hC (isRow_rows hU₂ t))
    unfold insertionEntropy
    rw [hmix]
    linear_combination (2 * (∫ t, (∫ y, Jp p (U₁ t y) ∂unitμ) ∂unitμ) - 2 * W.Ip p) * hcl
      + (2 * (∫ t, (∫ y, Jp p (U₂ t y) ∂unitμ) ∂unitμ) - 2 * W.Ip p) * hcl'
  · have hmix := integral_mixRows hlam0 hlam1 U₁ U₂
      (Φ := fun u => totalRootedDensity (Hs j) W u)
      (measurable_totalRootedDensity_rows (Hs j) W hU₁)
      (measurable_totalRootedDensity_rows (Hs j) W hU₂)
      (fun t => abs_totalRootedDensity_le (Hs j) W (isRow_rows hU₁ t))
      (fun t => abs_totalRootedDensity_le (Hs j) W (isRow_rows hU₂ t))
    unfold insertionDensity
    rw [hmix]
    linear_combination ((∫ t, totalRootedDensity (Hs j) W (U₁ t) ∂unitμ)
        - Fintype.card V * W.tDensity (Hs j)) * hcl
      + ((∫ t, totalRootedDensity (Hs j) W (U₂ t) ∂unitμ)
        - Fintype.card V * W.tDensity (Hs j)) * hcl'

/-! ### The cone -/

section Cone

variable {ι : Type*} (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
variable {p : ℝ} {W : Graphon} {η : ℝ}

/-- The zero kernel, as a direction. -/
noncomputable def zeroKernel : Kernel := (0 : ℝ) • Kernel.ofGraphon (constGraphon 0 ⟨le_rfl, zero_le_one⟩)

@[simp] theorem zeroKernel_apply (x y : ℝ) : zeroKernel.toFun x y = 0 := by
  rw [zeroKernel, Kernel.smul_apply, zero_mul]

/-- `DI_p(W)[0] = 0`. -/
@[simp] theorem variationIp_zeroKernel : variationIp p W zeroKernel = 0 := by
  unfold variationIp
  simp

/-- `Dt(H,W)[0] = 0`. -/
@[simp] theorem variationDensity_zeroKernel (H : SimpleGraph V) [DecidableRel H.Adj] :
    variationDensity H W zeroKernel = 0 := by
  unfold variationDensity
  simp

/-- The zero kernel is an admissible direction. -/
theorem admissibleDir_zeroKernel : AdmissibleDir W η zeroKernel := by
  intro x y h
  exact absurd (zeroKernel_apply x y) h

/-- The constant row kernel with value `p`. -/
theorem isRows_const_p (hp0 : 0 < p) (hp1 : p < 1) : IsRows (fun _ _ => p) :=
  ⟨measurable_const, fun _ _ => ⟨hp0.le, hp1.le⟩⟩

/-- `0` lies in the cone. -/
theorem zero_mem_insertionCone (hp0 : 0 < p) (hp1 : p < 1) :
    (0 : ℝ × (ι → ℝ)) ∈ insertionCone Hs p W η := by
  refine ⟨0, fun _ _ => p, zeroKernel, le_rfl, isRows_const_p hp0 hp1,
    admissibleDir_zeroKernel, ?_⟩
  refine Prod.ext ?_ ?_
  · simp
  · funext j
    simp

/-- The cone is closed under multiplication by nonnegative scalars. -/
theorem smul_mem_insertionCone {r : ℝ} (hr : 0 ≤ r) {w : ℝ × (ι → ℝ)}
    (hw : w ∈ insertionCone Hs p W η) : r • w ∈ insertionCone Hs p W η := by
  obtain ⟨c, U, Z, hc, hU, hZ, rfl⟩ := hw
  refine ⟨r * c, U, r • Z, mul_nonneg hr hc, hU, hZ.smul r, ?_⟩
  refine Prod.ext ?_ ?_
  · show r * (c * insertionEntropy p W U + variationIp p W Z) = _
    rw [variationIp_smul]
    ring
  · funext j
    show r * (c * insertionDensity (Hs j) W U + variationDensity (Hs j) W Z)
      = r * c * insertionDensity (Hs j) W U + variationDensity (Hs j) W (r • Z)
    rw [variationDensity_smul]
    ring

/-- **The cone `𝒞` is convex.** -/
theorem convex_insertionCone {a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : b < 1)
    (hW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc a b) :
    Convex ℝ (insertionCone Hs p W η) := by
  rintro w₁ ⟨c₁, U₁, Z₁, hc₁, hU₁, hZ₁, rfl⟩ w₂ ⟨c₂, U₂, Z₂, hc₂, hU₂, hZ₂, rfl⟩ s t hs ht hst
  obtain ⟨U, hU, hE, hD⟩ := exists_mix_insertionData Hs hp0 hp1 W
    (mul_nonneg hs hc₁) (mul_nonneg ht hc₂) hU₁ hU₂
  refine ⟨s * c₁ + t * c₂, U, s • Z₁ + t • Z₂, by positivity, hU,
    (hZ₁.smul s).add (hZ₂.smul t), ?_⟩
  refine Prod.ext ?_ ?_
  · show s * (c₁ * insertionEntropy p W U₁ + variationIp p W Z₁)
      + t * (c₂ * insertionEntropy p W U₂ + variationIp p W Z₂) = _
    rw [variationIp_add hp0 hp1 ha hb hW, variationIp_smul, variationIp_smul, hE]
    ring
  · funext j
    show s * (c₁ * insertionDensity (Hs j) W U₁ + variationDensity (Hs j) W Z₁)
        + t * (c₂ * insertionDensity (Hs j) W U₂ + variationDensity (Hs j) W Z₂)
      = (s * c₁ + t * c₂) * insertionDensity (Hs j) W U
        + variationDensity (Hs j) W (s • Z₁ + t • Z₂)
    rw [variationDensity_add, variationDensity_smul, variationDensity_smul, hD j]
    ring

/-- For a constant row kernel, `a(U)` is the `a(u)` of `eq:insertion-rates`. -/
theorem insertionEntropy_const (u : ℝ → ℝ) :
    insertionEntropy p W (fun _ => u) = 2 * ∫ y, Jp p (u y) ∂unitμ - 2 * W.Ip p := by
  unfold insertionEntropy
  rw [integral_const, probReal_univ, one_smul]

/-- For a constant row kernel, `b_j(U)` is the `b_j(u)` of `eq:insertion-rates`. -/
theorem insertionDensity_const (H : SimpleGraph V) [DecidableRel H.Adj] (u : ℝ → ℝ) :
    insertionDensity H W (fun _ => u)
      = totalRootedDensity H W u - Fintype.card V * W.tDensity H := by
  unfold insertionDensity
  rw [integral_const, probReal_univ, one_smul]

/-- **The generators of `eq:insertion-rates`**: a single row `u` gives the vector
`(a(u), (b_j(u))_j)` of the cone. -/
theorem singleRow_mem_insertionCone {u : ℝ → ℝ} (hu : IsRow u) :
    ((2 * ∫ y, Jp p (u y) ∂unitμ - 2 * W.Ip p,
        fun j => totalRootedDensity (Hs j) W u - Fintype.card V * W.tDensity (Hs j)) :
      ℝ × (ι → ℝ)) ∈ insertionCone Hs p W η := by
  refine ⟨1, fun _ => u, zeroKernel, zero_le_one, isRows_const hu,
    admissibleDir_zeroKernel, ?_⟩
  refine Prod.ext ?_ ?_
  · show 2 * ∫ y, Jp p (u y) ∂unitμ - 2 * W.Ip p
      = 1 * insertionEntropy p W (fun _ => u) + variationIp p W zeroKernel
    rw [insertionEntropy_const, variationIp_zeroKernel]
    ring
  · funext j
    show totalRootedDensity (Hs j) W u - Fintype.card V * W.tDensity (Hs j)
      = 1 * insertionDensity (Hs j) W (fun _ => u) + variationDensity (Hs j) W zeroKernel
    rw [insertionDensity_const, variationDensity_zeroKernel]
    ring

/-- Every direction contributes a pair of opposite vectors of the cone; hence a linear
functional nonnegative on the cone vanishes on all of them. -/
theorem variation_mem_insertionCone (hp0 : 0 < p) (hp1 : p < 1) {Z : Kernel}
    (hZ : AdmissibleDir W η Z) :
    ((variationIp p W Z, fun j => variationDensity (Hs j) W Z) : ℝ × (ι → ℝ))
      ∈ insertionCone Hs p W η := by
  refine ⟨0, fun _ _ => p, Z, le_rfl, isRows_const_p hp0 hp1, hZ, ?_⟩
  refine Prod.ext ?_ ?_
  · show variationIp p W Z = 0 * insertionEntropy p W (fun _ _ => p) + variationIp p W Z
    ring
  · funext j
    show variationDensity (Hs j) W Z
      = 0 * insertionDensity (Hs j) W (fun _ _ => p) + variationDensity (Hs j) W Z
    ring

end Cone

end UpperTailMultipodality
