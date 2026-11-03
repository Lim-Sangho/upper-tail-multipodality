import UpperTailMultipodality.Preliminaries.Multipodal

/-!
# Graphons with ordered rows (`lem:ordered-nondegenerate`, `lem:ordered-compact`)

`sec:degenerate-optimizers` uses, for the last step of `thm:fixed-densities`, a representative
of a
graphon that is nondecreasing in each variable.  A multipodal graphon with ordered blocks has
one, after listing the blocks in order and relabelling `[0,1]` so that they become consecutive
intervals; and the class of such graphons is compact in `L¹`.

This file fixes the two notions used there:

* `MonotoneKernel` — a symmetric measurable kernel with values in `[0,1]` that is nondecreasing
  in each variable;
* `HasOrderedRows W` — `W` agrees almost everywhere with such a kernel.

`HasOrderedRows` is strictly weaker than being multipodal with ordered blocks: the number of
distinct rows may be infinite.  That is exactly the generality the limit of
`lem:ordered-compact` needs.
-/

namespace UpperTailMultipodality

open MeasureTheory

/-- **A monotone kernel**: symmetric, measurable, with values in `[0,1]`, and nondecreasing in
each variable.  Monotonicity in the second variable follows from `symm'` and `mono'`. -/
structure MonotoneKernel where
  /-- The underlying kernel. -/
  toFun : ℝ → ℝ → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable (Function.uncurry toFun)
  nonneg' : ∀ x y, 0 ≤ toFun x y
  le_one' : ∀ x y, toFun x y ≤ 1
  mono' : ∀ y, Monotone fun x => toFun x y

namespace MonotoneKernel

variable (f : MonotoneKernel)

/-- The values of a monotone kernel lie in `[0,1]`. -/
theorem mem_Icc (x y : ℝ) : f.toFun x y ∈ Set.Icc (0:ℝ) 1 :=
  ⟨f.nonneg' x y, f.le_one' x y⟩

/-- Monotonicity in the second variable. -/
theorem mono_snd (x : ℝ) : Monotone fun y => f.toFun x y := by
  intro y y' hy
  simp only
  rw [f.symm' x y, f.symm' x y']
  exact f.mono' x hy

/-- A monotone kernel is a graphon. -/
def toGraphon : Graphon where
  toFun := f.toFun
  symm' := f.symm'
  meas' := f.meas'
  nonneg' := f.nonneg'
  le_one' := f.le_one'

@[simp] theorem toGraphon_apply (x y : ℝ) : f.toGraphon.toFun x y = f.toFun x y := rfl

end MonotoneKernel

/-- **`W` has ordered rows**: it agrees almost everywhere with a monotone kernel.  This is
`def:ordered-structure` for the relabelling `φ = id`, and it is the form in which the ordering
travels through `sec:degenerate-optimizers`: the hypothesis of `lem:ordered-nondegenerate`, the
hypothesis and the conclusion of `lem:ordered-compact`.  Where the paper relabels a graphon to
expose its ordered structure, the development instead carries the relabelled graphon itself,
together with the three functionals it has to preserve; see
`exists_hasOrderedRows_of_isOrderedMultipodal`. -/
def HasOrderedRows (W : Graphon) : Prop :=
  ∃ f : MonotoneKernel, ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = f.toFun z.1 z.2

theorem MonotoneKernel.hasOrderedRows (f : MonotoneKernel) : HasOrderedRows f.toGraphon :=
  ⟨f, Filter.Eventually.of_forall fun _ => rfl⟩

end UpperTailMultipodality
