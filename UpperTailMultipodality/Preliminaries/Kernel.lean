import UpperTailMultipodality.Preliminaries.Multipodal

/-!
# Bounded symmetric kernels and their homomorphism densities (`sec:derivatives`)

The first variation of `t(H,·)` is taken in the Banach space `L^∞_sym([0,1]²)` of bounded
symmetric measurable functions, where `t(H,·)` is a polynomial.  A `Kernel` is a bounded
symmetric measurable function `ℝ → ℝ → ℝ`; graphons are kernels with values in `[0,1]`, and
`Kernel.tDensity` extends `Graphon.tDensity` by the same integral.
-/

namespace UpperTailMultipodality

open MeasureTheory

/-- The factor `K(x_a, x_b)` attached to an unordered edge `e = ab` of `H` under the vertex
assignment `x`. -/
noncomputable def edgeVal {V : Type*} (K : ℝ → ℝ → ℝ) (hK : ∀ x y, K x y = K y x)
    (x : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => K (x a) (x b), fun a b => hK (x a) (x b)⟩ e

/-- A bounded symmetric measurable kernel. -/
structure Kernel where
  /-- The underlying function. -/
  toFun : ℝ → ℝ → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable (Function.uncurry toFun)
  bdd' : ∃ C, ∀ x y, |toFun x y| ≤ C

namespace Kernel

/-- The homomorphism density `t(H,K)`, defined by the same integral as for graphons. -/
noncomputable def tDensity (K : Kernel) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : ℝ :=
  ∫ x : V → ℝ, ∏ e ∈ H.edgeFinset, edgeVal K.toFun K.symm' x e
    ∂(Measure.pi fun _ => unitμ)

/-- A graphon regarded as a kernel. -/
def ofGraphon (W : Graphon) : Kernel where
  toFun := W.toFun
  symm' := W.symm'
  meas' := W.meas'
  bdd' := ⟨1, fun x y => by
    rw [abs_of_nonneg (W.nonneg' x y)]; exact W.le_one' x y⟩

/-- `t(H,W)` is the homomorphism density of `W` regarded as a kernel. -/
theorem tDensity_ofGraphon (W : Graphon) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (ofGraphon W).tDensity H = W.tDensity H := rfl

/-- The sum of two kernels. -/
instance : Add Kernel where
  add K L :=
    { toFun := fun x y => K.toFun x y + L.toFun x y
      symm' := fun x y => by rw [K.symm', L.symm']
      meas' := K.meas'.add L.meas'
      bdd' := by
        obtain ⟨C, hC⟩ := K.bdd'
        obtain ⟨D, hD⟩ := L.bdd'
        exact ⟨C + D, fun x y => (abs_add_le _ _).trans (add_le_add (hC x y) (hD x y))⟩ }

/-- A scalar multiple of a kernel. -/
instance : SMul ℝ Kernel where
  smul c K :=
    { toFun := fun x y => c * K.toFun x y
      symm' := fun x y => by rw [K.symm']
      meas' := K.meas'.const_mul c
      bdd' := by
        obtain ⟨C, hC⟩ := K.bdd'
        exact ⟨|c| * C, fun x y => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg c)⟩ }

@[simp] theorem add_apply (K L : Kernel) (x y : ℝ) :
    (K + L).toFun x y = K.toFun x y + L.toFun x y := rfl

@[simp] theorem smul_apply (c : ℝ) (K : Kernel) (x y : ℝ) :
    (c • K).toFun x y = c * K.toFun x y := rfl

@[simp] theorem ofGraphon_apply (W : Graphon) (x y : ℝ) :
    (ofGraphon W).toFun x y = W.toFun x y := rfl

end Kernel

end UpperTailMultipodality
