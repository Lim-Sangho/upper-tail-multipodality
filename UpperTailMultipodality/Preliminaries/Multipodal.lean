import UpperTailMultipodality.Preliminaries.Graphons.Attainment

/-!
# Rows, multipodal graphons and ordered blocks (`sec:graphons`)

A graphon is *multipodal* if there are a finite measurable partition
`[0,1] = A_1 ∪ ⋯ ∪ A_M` and numbers `b_{ij} = b_{ji} ∈ [0,1]` with `W = b_{ij}` almost
everywhere on `A_i × A_j`.  Its blocks are *ordered*, `eq:ordered-blocks`, if the labels can be
chosen with `b_{ij} ≤ b_{i'j}` whenever `i ≤ i'`.

The blocks are measurable subsets of `ℝ`; they are pairwise disjoint and cover `[0,1]` up to a
`unitμ`-null set.  Blocks of measure zero are allowed, as in the paper, where a partition may
contain empty sets.
-/

namespace UpperTailMultipodality

open MeasureTheory

/-- The row `W_x = W(x,·)` of a graphon. -/
def Graphon.row (W : Graphon) (x : ℝ) : ℝ → ℝ := fun y => W.toFun x y

@[simp] theorem Graphon.row_apply (W : Graphon) (x y : ℝ) : W.row x y = W.toFun x y := rfl

/-- A finite block structure: `M` measurable, pairwise disjoint blocks covering `[0,1]` up to a
null set, together with symmetric block values in `[0,1]`. -/
structure BlockStructure (M : ℕ) where
  /-- The blocks `A_1, …, A_M`. -/
  block : Fin M → Set ℝ
  /-- The block values `b_{ij}`. -/
  value : Fin M → Fin M → ℝ
  measurableSet_block : ∀ i, MeasurableSet (block i)
  pairwise_disjoint : Pairwise fun i j => Disjoint (block i) (block j)
  cover : ∀ᵐ x ∂unitμ, ∃ i, x ∈ block i
  value_symm : ∀ i j, value i j = value j i
  value_mem : ∀ i j, value i j ∈ Set.Icc (0:ℝ) 1

/-- The block structure `B` represents `W`: `W = b_{ij}` almost everywhere on `A_i × A_j`. -/
def BlockStructure.Represents {M : ℕ} (B : BlockStructure M) (W : Graphon) : Prop :=
  ∀ i j, ∀ᵐ z ∂gμ, z.1 ∈ B.block i → z.2 ∈ B.block j → W.toFun z.1 z.2 = B.value i j

/-- The block values are ordered, `eq:ordered-blocks`: `b_{ij} ≤ b_{i'j}` whenever `i ≤ i'`. -/
def BlockStructure.Ordered {M : ℕ} (B : BlockStructure M) : Prop :=
  ∀ i i' j, i ≤ i' → B.value i j ≤ B.value i' j

/-- **Multipodal graphons.**  `W` agrees almost everywhere with a stochastic block model with
finitely many blocks. -/
def IsMultipodal (W : Graphon) : Prop :=
  ∃ (M : ℕ) (B : BlockStructure M), B.Represents W

/-- **Multipodal graphons with ordered blocks.** -/
def IsOrderedMultipodal (W : Graphon) : Prop :=
  ∃ (M : ℕ) (B : BlockStructure M), B.Represents W ∧ B.Ordered

theorem IsOrderedMultipodal.isMultipodal {W : Graphon} (h : IsOrderedMultipodal W) :
    IsMultipodal W := by
  obtain ⟨M, B, hB, -⟩ := h
  exact ⟨M, B, hB⟩

end UpperTailMultipodality
