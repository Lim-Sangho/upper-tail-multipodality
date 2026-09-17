import UpperTailMultipodality.FixedDensities.Support.KernelFacts

/-!
# Restoring both constraints along the constraint-qualification directions

For a graphon `W`, bounded symmetric kernels `U₁, U₂` with `cqDet H W U₁ U₂ ≠ 0`
(`def:constraint-qualification`) and a further direction `Z`, the two-dimensional implicit
function theorem gives `ξ₁(θ), ξ₂(θ)` with `ξᵢ(0) = 0` such that
`W + θZ + ξ₁(θ)U₁ + ξ₂(θ)U₂` has the same edge density and `H`-density as `W` for small `θ`.
The derivative `(ξ₁'(0), ξ₂'(0))` solves `Γ_W(U₁,U₂) ξ'(0) = -(∫Z, ∫𝒟_W Z)`.

This replaces the Banach-space Lagrange multiplier rule (`lem:lagrange`) in the proofs of
`lem:fixed-interior` and `lem:fixed-multiplier`: only finitely many directions are needed.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The linear functional `(θ, ξ₁, ξ₂) ↦ c₀θ + c₁ξ₁ + c₂ξ₂`. -/
noncomputable def linFun3 (c₀ c₁ c₂ : ℝ) : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  c₀ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
    + c₁ • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    + c₂ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The value of `linFun3`. -/
@[simp] theorem linFun3_apply (c₀ c₁ c₂ : ℝ) (q : ℝ × (ℝ × ℝ)) :
    linFun3 c₀ c₁ c₂ q = c₀ * q.1 + c₁ * q.2.1 + c₂ * q.2.2 := by
  simp [linFun3]

/-- **A two-dimensional implicit function.**  If `T` is strictly differentiable at `0` with
derivative `(θ, ξ) ↦ b₀θ + b₁ξ₁ + b₂ξ₂` and `a₁b₂ - a₂b₁ ≠ 0`, then the system
`a₀θ + a₁ξ₁ + a₂ξ₂ = 0`, `T(θ, ξ) = T(0)` has a solution `ξ(θ)` near `θ = 0`, with `ξ(0) = 0`
and the derivative given by Cramer's rule. -/
theorem exists_implicit_two (T : ℝ × (ℝ × ℝ) → ℝ) (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ)
    (hT : HasStrictFDerivAt T (linFun3 b₀ b₁ b₂) 0)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    ∃ ξ : ℝ → ℝ × ℝ, ξ 0 = 0 ∧
      HasDerivAt ξ ((-a₀ * b₂ + a₂ * b₀) / (a₁ * b₂ - a₂ * b₁),
        (-a₁ * b₀ + a₀ * b₁) / (a₁ * b₂ - a₂ * b₁)) 0 ∧
      ∀ᶠ θ in 𝓝 0, a₀ * θ + a₁ * (ξ θ).1 + a₂ * (ξ θ).2 = 0 ∧ T (θ, ξ θ) = T 0 := by
  set d := a₁ * b₂ - a₂ * b₁ with hd
  let f : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun q => (linFun3 a₀ a₁ a₂ q, T q)
  let f' : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ := (linFun3 a₀ a₁ a₂).prod (linFun3 b₀ b₁ b₂)
  have hf : HasStrictFDerivAt f f' ((0 : ℝ), ((0 : ℝ × ℝ))) :=
    (linFun3 a₀ a₁ a₂).hasStrictFDerivAt.prodMk hT
  -- the partial derivative in `ξ` and its explicit inverse
  let G : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((b₂ / d) • ContinuousLinearMap.fst ℝ ℝ ℝ - (a₂ / d) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((-b₁ / d) • ContinuousLinearMap.fst ℝ ℝ ℝ + (a₁ / d) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hinr : ∀ y : ℝ × ℝ, (f' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y
      = (a₁ * y.1 + a₂ * y.2, b₁ * y.1 + b₂ * y.2) := by
    intro y; simp [f']
  have hG : ∀ y : ℝ × ℝ, G y = ((b₂ * y.1 - a₂ * y.2) / d, (-b₁ * y.1 + a₁ * y.2) / d) := by
    intro y; simp [G]; constructor <;> ring
  have hinv : (f' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.equivOfInverse (f' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) G
      ?_ ?_, rfl⟩
    · intro y
      rw [hinr, hG]
      ext <;> simp only <;> field_simp <;> ring
    · intro y
      rw [hG, hinr]
      ext <;> simp only <;> field_simp <;> ring
  set ψ := hf.implicitFunctionOfProdDomain hinv with hψ
  have hψ0 : ψ 0 = 0 :=
    (hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hev := hf.eventually_apply_implicitFunctionOfProdDomain hinv
  have hder := (hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
  refine ⟨ψ, hψ0, ?_, ?_⟩
  · have hval : ((-(f' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).inverse ∘L
        (f' ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1)
        = ((-a₀ * b₂ + a₂ * b₀) / d, (-a₁ * b₀ + a₀ * b₁) / d) := by
      apply hinv.injective
      obtain ⟨M, hM⟩ : ∃ M, M = f' ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N, N = f' ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ) := ⟨_, rfl⟩
      rw [← hM, ← hN]
      rw [← hM] at hinv hinr
      have hN1 : N 1 = (a₀, b₀) := by rw [hN]; simp [f']
      have hcalc : (-M.inverse ∘L N) 1 = -(M.inverse (N 1)) := rfl
      rw [hcalc, map_neg, hinv.self_apply_inverse, hN1, hinr]
      ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> field_simp <;> ring
    rw [hval] at hder
    exact hder
  · filter_upwards [hev] with θ hθ
    have h1 : linFun3 a₀ a₁ a₂ (θ, ψ θ) = linFun3 a₀ a₁ a₂ (0, 0) := congrArg Prod.fst hθ
    have h2 : T (θ, ψ θ) = T (0, 0) := congrArg Prod.snd hθ
    simp only [linFun3_apply, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at h1
    exact ⟨by linarith, h2⟩

/-- The kernel `W + θZ + x₁U₁ + x₂U₂`. -/
noncomputable def corrKernel (W : Graphon) (Z U₁ U₂ : Kernel) (θ x₁ x₂ : ℝ) : Kernel :=
  (Kernel.ofGraphon W).lincomb ![Z, U₁, U₂] ![θ, x₁, x₂]

/-- The value of the corrected kernel. -/
@[simp] theorem corrKernel_apply (W : Graphon) (Z U₁ U₂ : Kernel) (θ x₁ x₂ x y : ℝ) :
    (corrKernel W Z U₁ U₂ θ x₁ x₂).toFun x y
      = W.toFun x y + θ * Z.toFun x y + x₁ * U₁.toFun x y + x₂ * U₂.toFun x y := by
  simp [corrKernel, Fin.sum_univ_three]
  ring

/-- The edge density of `W + θZ + x₁U₁ + x₂U₂` is affine in `(θ, x₁, x₂)`. -/
theorem edgeDensity_corrKernel (W : Graphon) (Z U₁ U₂ : Kernel) (θ x₁ x₂ : ℝ) :
    (corrKernel W Z U₁ U₂ θ x₁ x₂).edgeDensity
      = W.edgeDensity + θ * (∫ z, Z.toFun z.1 z.2 ∂gμ) + x₁ * (∫ z, U₁.toFun z.1 z.2 ∂gμ)
        + x₂ * (∫ z, U₂.toFun z.1 z.2 ∂gμ) := by
  unfold Kernel.edgeDensity Graphon.edgeDensity
  simp only [corrKernel_apply]
  have hZ := (kernel_integrable Z).const_mul θ
  have h1 := (kernel_integrable U₁).const_mul x₁
  have h2 := (kernel_integrable U₂).const_mul x₂
  have hWZ : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2 + θ * Z.toFun z.1 z.2) gμ :=
    W.integrable_self.add hZ
  have hWZ1 : Integrable (fun z : ℝ × ℝ =>
      W.toFun z.1 z.2 + θ * Z.toFun z.1 z.2 + x₁ * U₁.toFun z.1 z.2) gμ := hWZ.add h1
  rw [integral_add hWZ1 h2, integral_add hWZ h1, integral_add W.integrable_self hZ,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- `t(H, W + θZ + x₁U₁ + x₂U₂)` is strictly differentiable at `0`, with derivative
`(θ, x₁, x₂) ↦ θ∫∫𝒟_W Z + x₁∫∫𝒟_W U₁ + x₂∫∫𝒟_W U₂`. -/
theorem hasStrictFDerivAt_tDensity_corrKernel (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon) (Z U₁ U₂ : Kernel) :
    HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => (corrKernel W Z U₁ U₂ q.1 q.2.1 q.2.2).tDensity H)
      (linFun3 (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)) 0 := by
  set g : (Fin 3 → ℝ) → ℝ := fun s => ((Kernel.ofGraphon W).lincomb ![Z, U₁, U₂] s).tDensity H
    with hgdef
  have hgan : AnalyticAt ℝ g 0 :=
    analyticOnNhd_tDensity_lincomb H (Kernel.ofGraphon W) ![Z, U₁, U₂] 0 trivial
  have hgfd := hasFDerivAt_tDensity_lincomb H W ![Z, U₁, U₂]
  have hgs : HasStrictFDerivAt g
      (∑ i, (∫ z, derivKernel H W z.1 z.2 * (![Z, U₁, U₂] i).toFun z.1 z.2 ∂gμ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) 0 := by
    have := hgan.hasStrictFDerivAt
    rwa [hgfd.fderiv] at this
  let L3 : ℝ × (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]
  have hL3 : ∀ q : ℝ × (ℝ × ℝ), L3 q = ![q.1, q.2.1, q.2.2] := by
    intro q; funext i; fin_cases i <;> rfl
  have hgs0 : HasStrictFDerivAt g
      (∑ i, (∫ z, derivKernel H W z.1 z.2 * (![Z, U₁, U₂] i).toFun z.1 z.2 ∂gμ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) (L3 0) := by
    rw [map_zero]; exact hgs
  have hcomp := hgs0.comp (0 : ℝ × (ℝ × ℝ)) L3.hasStrictFDerivAt
  have hfun : (fun x => g (L3 x))
      = fun q : ℝ × (ℝ × ℝ) => (corrKernel W Z U₁ U₂ q.1 q.2.1 q.2.2).tDensity H := by
    funext q
    simp only [hgdef, hL3, corrKernel]
  have hlin : (∑ i, (∫ z, derivKernel H W z.1 z.2 * (![Z, U₁, U₂] i).toFun z.1 z.2 ∂gμ) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp L3
      = linFun3 (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ)
        (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ) := by
    refine ContinuousLinearMap.ext fun q => ?_
    simp [hL3, Fin.sum_univ_three]
  rw [hfun, hlin] at hcomp
  exact hcomp

/-- **Correction along the constraint-qualification directions.**  If
`cqDet H W U₁ U₂ ≠ 0`, then for every bounded symmetric direction `Z` there are `ξ₁, ξ₂` with
`ξᵢ(0) = 0`, derivatives at `0` given by Cramer's rule, and such that for all small `θ` the kernel
`W + θZ + ξ₁(θ)U₁ + ξ₂(θ)U₂` has the same edge density and `H`-density as `W`. -/
theorem exists_correction (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (Z U₁ U₂ : Kernel) (hdet : cqDet H W U₁ U₂ ≠ 0) :
    ∃ ξ₁ ξ₂ : ℝ → ℝ, ξ₁ 0 = 0 ∧ ξ₂ 0 = 0 ∧
      HasDerivAt ξ₁ ((-(∫ z, Z.toFun z.1 z.2 ∂gμ)
              * (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)
            + (∫ z, U₂.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ))
          / cqDet H W U₁ U₂) 0 ∧
      HasDerivAt ξ₂ ((-(∫ z, U₁.toFun z.1 z.2 ∂gμ)
              * (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
            + (∫ z, Z.toFun z.1 z.2 ∂gμ) * (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ))
          / cqDet H W U₁ U₂) 0 ∧
      ∀ᶠ θ in 𝓝 0, (corrKernel W Z U₁ U₂ θ (ξ₁ θ) (ξ₂ θ)).edgeDensity = W.edgeDensity ∧
        (corrKernel W Z U₁ U₂ θ (ξ₁ θ) (ξ₂ θ)).tDensity H = W.tDensity H := by
  obtain ⟨ξ, hξ0, hξd, hev⟩ := exists_implicit_two
    (fun q : ℝ × (ℝ × ℝ) => (corrKernel W Z U₁ U₂ q.1 q.2.1 q.2.2).tDensity H)
    (∫ z, Z.toFun z.1 z.2 ∂gμ) (∫ z, U₁.toFun z.1 z.2 ∂gμ) (∫ z, U₂.toFun z.1 z.2 ∂gμ)
    (∫ z, derivKernel H W z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
    (∫ z, derivKernel H W z.1 z.2 * U₁.toFun z.1 z.2 ∂gμ)
    (∫ z, derivKernel H W z.1 z.2 * U₂.toFun z.1 z.2 ∂gμ)
    (hasStrictFDerivAt_tDensity_corrKernel H W Z U₁ U₂) hdet
  have hT0 : (corrKernel W Z U₁ U₂ 0 0 0).tDensity H = W.tDensity H := by
    rw [← Kernel.tDensity_ofGraphon]
    exact kernel_tDensity_congr H fun x y => by simp
  refine ⟨fun θ => (ξ θ).1, fun θ => (ξ θ).2, by simp [hξ0], by simp [hξ0], hξd.fst, hξd.snd, ?_⟩
  filter_upwards [hev] with θ ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rw [edgeDensity_corrKernel]; linarith
  · exact h2.trans hT0

/-- The Cramer's-rule derivative of `exists_correction` solves the linearized constraints. -/
theorem correction_deriv_eqs {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    a₁ * ((-a₀ * b₂ + a₂ * b₀) / (a₁ * b₂ - a₂ * b₁))
        + a₂ * ((-a₁ * b₀ + a₀ * b₁) / (a₁ * b₂ - a₂ * b₁)) = -a₀ ∧
      b₁ * ((-a₀ * b₂ + a₂ * b₀) / (a₁ * b₂ - a₂ * b₁))
        + b₂ * ((-a₁ * b₀ + a₀ * b₁) / (a₁ * b₂ - a₂ * b₁)) = -b₀ := by
  constructor <;>
  · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]; ring

end FixedDensities

end UpperTailMultipodality
