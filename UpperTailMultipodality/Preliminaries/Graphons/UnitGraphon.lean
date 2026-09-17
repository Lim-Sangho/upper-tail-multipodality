import UpperTailMultipodality.Preliminaries.Graphons.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Graphons on the unit square, as in the paper

`sec:graphons` defines a graphon as a symmetric measurable function
`W : [0,1]² → [0,1]`, with

  `e(W) = ∫_{[0,1]²} W`,   `t(H,W) = ∫_{[0,1]^{V(H)}} ∏_{ij ∈ E(H)} W(x_i,x_j)`,
  `I_p(W) = ∫_{[0,1]²} J_p(W)`,   `s(W) = -½ ∫_{[0,1]²} [W log W + (1-W) log(1-W)]`.

`UnitGraphon` is that definition, on Mathlib's `unitInterval` with Lebesgue measure.  The
structure `Graphon` used throughout the development stores a kernel on `ℝ²` and integrates it
against Lebesgue measure on `[0,1]` and `[0,1]²`, so its values outside `[0,1]²` are never read.
This file proves that the two notions are the same:

* `Graphon.toUnitGraphon` restricts to `[0,1]²` and `UnitGraphon.toGraphon` extends by
  `W(x,y) := W(proj x, proj y)`; `UnitGraphon.toUnitGraphon_toGraphon` and
  `Graphon.toGraphon_toUnitGraphon_apply` show that they are mutually inverse on `[0,1]²`;
* restriction preserves the edge density, every homomorphism density, `I_p` and the entropy.
-/

namespace UpperTailMultipodality

open MeasureTheory unitInterval

/-- **A graphon, as in the paper**: a symmetric measurable function `W : [0,1]² → [0,1]`. -/
structure UnitGraphon where
  /-- The kernel on the unit square. -/
  toFun : unitInterval → unitInterval → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable fun z : unitInterval × unitInterval => toFun z.1 z.2
  mem' : ∀ x y, toFun x y ∈ Set.Icc (0:ℝ) 1

namespace UnitGraphon

variable (W : UnitGraphon)

/-- The edge density `e(W) = ∫_{[0,1]²} W`. -/
noncomputable def edgeDensity : ℝ := ∫ z : unitInterval × unitInterval, W.toFun z.1 z.2

/-- The homomorphism density `t(H,W) = ∫_{[0,1]^{V(H)}} ∏_{ij ∈ E(H)} W(x_i,x_j)`. -/
noncomputable def tDensity {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : ℝ :=
  ∫ x : V → unitInterval,
    ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e

/-- The relative entropy `I_p(W) = ∫_{[0,1]²} J_p(W)`. -/
noncomputable def Ip (p : ℝ) : ℝ := ∫ z : unitInterval × unitInterval, Jp p (W.toFun z.1 z.2)

/-- The entropy `s(W) = -½ ∫_{[0,1]²} [W log W + (1-W) log(1-W)]`. -/
noncomputable def entropy : ℝ :=
  -(1/2) * ∫ z : unitInterval × unitInterval, (W.toFun z.1 z.2 * Real.log (W.toFun z.1 z.2)
      + (1 - W.toFun z.1 z.2) * Real.log (1 - W.toFun z.1 z.2))

/-- Two `UnitGraphon`s with the same kernel are equal (the other fields are propositions). -/
theorem ext_toFun {V W : UnitGraphon} (h : V.toFun = W.toFun) : V = W := by
  obtain ⟨f, _, _, _⟩ := V
  obtain ⟨g, _, _, _⟩ := W
  cases h
  rfl

/-- The extension of `W` to `ℝ²`, `(x,y) ↦ W(proj x, proj y)`. -/
noncomputable def toGraphon (W : UnitGraphon) : Graphon where
  toFun x y := W.toFun (Set.projIcc 0 1 zero_le_one x) (Set.projIcc 0 1 zero_le_one y)
  symm' x y := W.symm' _ _
  meas' := by
    have hproj : Measurable (Set.projIcc (0:ℝ) 1 zero_le_one) :=
      continuous_projIcc.measurable
    exact W.meas'.comp (hproj.prodMap hproj)
  nonneg' x y := (W.mem' _ _).1
  le_one' x y := (W.mem' _ _).2

theorem toGraphon_apply (W : UnitGraphon) (x y : unitInterval) : W.toGraphon.toFun x y = W.toFun x y := by
  simp only [toGraphon, Set.projIcc_val]

end UnitGraphon

namespace Graphon

/-- **Change of variables `[0,1]² ↔ unitInterval²`.** Integrating `g ∘ (↑, ↑)` against the
product Lebesgue measure on `unitInterval × unitInterval` is integrating `g` against `gμ`. -/
theorem integral_unitSquare (g : ℝ × ℝ → ℝ) :
    ∫ z : unitInterval × unitInterval, g ((z.1 : ℝ), (z.2 : ℝ)) = ∫ z, g z ∂gμ := by
  have hmp : MeasurePreserving (Prod.map ((↑) : unitInterval → ℝ) ((↑) : unitInterval → ℝ))
      (volume : Measure (unitInterval × unitInterval)) gμ :=
    measurePreserving_coe.prod measurePreserving_coe
  exact hmp.integral_comp (measurableEmbedding_coe.prodMap measurableEmbedding_coe) g

/-- The restriction of a graphon to `[0,1]²`. -/
def toUnitGraphon (W : Graphon) : UnitGraphon where
  toFun x y := W.toFun x y
  symm' x y := W.symm' x y
  meas' := W.meas'.comp (measurable_subtype_coe.prodMap measurable_subtype_coe)
  mem' x y := W.mem_Icc x y

theorem toUnitGraphon_apply (W : Graphon) (x y : unitInterval) : W.toUnitGraphon.toFun x y = W.toFun x y := by
  rfl

/-- Restricting and extending gives back `W` on `[0,1]²`. -/
theorem toGraphon_toUnitGraphon_apply (W : Graphon) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) : W.toUnitGraphon.toGraphon.toFun x y = W.toFun x y := by
  simp only [UnitGraphon.toGraphon, toUnitGraphon, Set.projIcc_of_mem _ hx, Set.projIcc_of_mem _ hy]

theorem edgeDensity_toUnitGraphon (W : Graphon) : W.toUnitGraphon.edgeDensity = W.edgeDensity := by
  exact integral_unitSquare (fun z => W.toFun z.1 z.2)

theorem tDensity_toUnitGraphon (W : Graphon) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : W.toUnitGraphon.tDensity H = W.tDensity H := by
  have hmeas : Measurable fun x : V → ℝ => ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e := by
    refine Finset.measurable_prod _ fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b =>
      show Measurable fun x : V → ℝ => W.toFun (x a) (x b)
      have hpair : Measurable fun x : V → ℝ => (x a, x b) := by fun_prop
      exact W.measurable_uncurry.comp hpair
  have hmp : MeasurePreserving (fun (x : V → unitInterval) (i : V) => (x i : ℝ))
      (volume : Measure (V → unitInterval)) (Measure.pi fun _ : V => unitμ) :=
    measurePreserving_pi (fun _ => volume) (fun _ => unitμ) fun _ => measurePreserving_coe
  unfold UnitGraphon.tDensity Graphon.tDensity
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeas.aestronglyMeasurable]
  rfl

theorem Ip_toUnitGraphon (W : Graphon) (p : ℝ) : W.toUnitGraphon.Ip p = W.Ip p := by
  exact integral_unitSquare (fun z => Jp p (W.toFun z.1 z.2))

theorem entropy_toUnitGraphon (W : Graphon) : W.toUnitGraphon.entropy = W.entropy := by
  unfold UnitGraphon.entropy Graphon.entropy
  congr 1
  exact integral_unitSquare (fun z => W.toFun z.1 z.2 * Real.log (W.toFun z.1 z.2)
      + (1 - W.toFun z.1 z.2) * Real.log (1 - W.toFun z.1 z.2))

end Graphon

/-- Extending and restricting gives back `W`. -/
theorem UnitGraphon.toUnitGraphon_toGraphon (W : UnitGraphon) : W.toGraphon.toUnitGraphon = W := by
  exact UnitGraphon.ext_toFun (funext fun x => funext fun y => UnitGraphon.toGraphon_apply W x y)

end UpperTailMultipodality
