import UpperTailMultipodality.RowCriterion.Finite
import UpperTailMultipodality.RowCriterion.Finiteness.Compact
import UpperTailMultipodality.RowCriterion.Finiteness.SecondVariationL2

/-!
# Section 5 on `L^∞([0,1])`

Section 5 of the paper works in `L^∞([0,1])`: that is where the definition of `𝓜_W` at the start
of `sec:row-criterion` places it, where `lem:row-compact` and `lem:row-finite` assert that it is
compact and finite, where `Q_u` is defined, and where `lem:bordered` inverts the bordered
operator.  This file states all of that on Mathlib's `L^∞([0,1]) = Lp ℝ ∞ unitμ`.

The proofs run one level below, in the Banach algebra `BddMeas` of bounded measurable functions,
for two reasons.  `Lp ℝ ∞` carries no multiplication, so it is not a Banach algebra, and the
analytic implicit function theorem of `lem:row-finite` needs one: the fixed point equation
`u = σ(ℓ(q) + α + (1/2)∇𝒫_W(u))` is solved by a power series there.  And point evaluation is
continuous on `BddMeas`, so pointwise identities pass to limits.

The two layers are related by the quotient map `BddMeas.toLinfty`, which is `1`-Lipschitz, and by
its section `BddMeas.ofLinfty`, the truncation of a class at its essential supremum, which has no
larger norm; so the map is onto (`BddMeas.toLinfty_surjective`) and bounded sets correspond.  What
makes the statements transfer is that none of the data sees null sets:
`combinedRowFunctional_congr_ae` for `ℱ_W`, `secondVariationFun_congr` for `Q_u`, and
`borderedOp_congr_ae` for the bordered operator.

The resulting statements are `rowMinimizersLinfty` with `mem_rowMinimizersLinfty_iff` (the two
defining conditions `0 ≤ u ≤ 1` almost everywhere and `ℱ_W(u) = c`), `row_compact_Linfty`,
`row_finite_Linfty`, `secondVariationLinfty`, and `borderedEquivLinfty`.  `lem:row-lower-bound`
is stated on `Lp ℝ 2 unitμ` in `Finiteness/SecondVariationL2.lean`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### The quotient map `BddMeas → L^∞([0,1])` -/

/-- A bounded measurable function is essentially bounded. -/
theorem memLp_top_bddMeas (b : BddMeas) : MemLp (⇑b) ∞ unitμ :=
  memLp_top_of_bound b.measurable.aestronglyMeasurable ‖b‖
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact b.abs_apply_le_norm y)

/-- **A bounded measurable function as an element of `L^∞([0,1])`.**  This is the canonical map
from the Banach algebra in which the proofs run onto the paper's ambient space. -/
noncomputable def BddMeas.toLinfty (b : BddMeas) : Lp ℝ ∞ unitμ := (memLp_top_bddMeas b).toLp ⇑b

/-- The `L^∞` class of a bounded measurable function is represented by it. -/
theorem BddMeas.coeFn_toLinfty (b : BddMeas) : ⇑b.toLinfty =ᵐ[unitμ] ⇑b :=
  (memLp_top_bddMeas b).coeFn_toLp

/-- The map onto `L^∞([0,1])` is additive. -/
theorem BddMeas.toLinfty_sub (a b : BddMeas) : (a - b).toLinfty = a.toLinfty - b.toLinfty := by
  simp only [BddMeas.toLinfty]
  rw [← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (by rw [BddMeas.coe_sub])

/-- The essential supremum is at most the supremum. -/
theorem BddMeas.norm_toLinfty_le (b : BddMeas) : ‖b.toLinfty‖ ≤ ‖b‖ := by
  rw [BddMeas.toLinfty, Lp.norm_toLp, eLpNorm_exponent_top]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg b) ?_
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact b.abs_apply_le_norm y)

/-- The map onto `L^∞([0,1])` is `1`-Lipschitz. -/
theorem BddMeas.lipschitzWith_toLinfty : LipschitzWith 1 BddMeas.toLinfty := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, ← BddMeas.toLinfty_sub]
  simpa using BddMeas.norm_toLinfty_le (a - b)

/-- The map onto `L^∞([0,1])` is continuous. -/
theorem BddMeas.continuous_toLinfty : Continuous BddMeas.toLinfty :=
  BddMeas.lipschitzWith_toLinfty.continuous

/-- Almost everywhere equal bounded measurable functions have the same `L^∞` class. -/
theorem BddMeas.toLinfty_congr {a b : BddMeas} (h : ⇑a =ᵐ[unitμ] ⇑b) :
    a.toLinfty = b.toLinfty :=
  MemLp.toLp_congr _ _ h

/-- The map onto `L^∞([0,1])` is additive. -/
theorem BddMeas.toLinfty_add (a b : BddMeas) : (a + b).toLinfty = a.toLinfty + b.toLinfty := by
  simp only [BddMeas.toLinfty]
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (by rw [BddMeas.coe_add])

/-- The map onto `L^∞([0,1])` is homogeneous. -/
theorem BddMeas.toLinfty_smul (r : ℝ) (b : BddMeas) : (r • b).toLinfty = r • b.toLinfty := by
  refine Lp.ext (((r • b).coeFn_toLinfty).trans ?_)
  refine (Filter.EventuallyEq.symm ?_)
  refine (Lp.coeFn_smul r b.toLinfty).trans ?_
  exact (b.coeFn_toLinfty.const_smul r).trans (by rw [BddMeas.coe_smul])

/-! ### A bounded measurable representative -/

/-- An element of `L^∞([0,1])` is bounded by its norm almost everywhere. -/
theorem ae_abs_le_norm_Linfty (f : Lp ℝ ∞ unitμ) : ∀ᵐ y ∂unitμ, |f y| ≤ ‖f‖ := by
  have h := ae_le_lpNorm_exponent_top (Lp.memLp f)
  have hn : lpNorm (⇑f : ℝ → ℝ) ∞ unitμ = ‖f‖ := by
    rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable f)]
  rw [hn] at h
  exact h.mono fun y hy => by rwa [Real.norm_eq_abs] at hy

/-- **A bounded measurable representative of an `L^∞` class**, obtained by truncating at the
essential supremum.  It is a right inverse of `BddMeas.toLinfty` with no larger norm, so the
quotient map is onto and the two spaces have the same bounded sets. -/
noncomputable def BddMeas.ofLinfty (f : Lp ℝ ∞ unitμ) : BddMeas :=
  BddMeas.mk (fun y => if |f y| ≤ ‖f‖ then f y else 0)
    (Measurable.ite (measurableSet_le (Lp.stronglyMeasurable f).measurable.abs measurable_const)
      (Lp.stronglyMeasurable f).measurable measurable_const) ‖f‖ (fun y => by
      split_ifs with hy
      · exact hy
      · simp [norm_nonneg f])

/-- The representative represents the class. -/
theorem BddMeas.coeFn_ofLinfty (f : Lp ℝ ∞ unitμ) : ⇑(BddMeas.ofLinfty f) =ᵐ[unitμ] ⇑f :=
  (ae_abs_le_norm_Linfty f).mono fun y hy => by
    show (if |f y| ≤ ‖f‖ then f y else 0) = f y
    rw [if_pos hy]

/-- The representative has no larger norm. -/
theorem BddMeas.norm_ofLinfty_le (f : Lp ℝ ∞ unitμ) : ‖BddMeas.ofLinfty f‖ ≤ ‖f‖ :=
  BddMeas.norm_le_of_forall (norm_nonneg f) fun y => by
    show |if |f y| ≤ ‖f‖ then f y else 0| ≤ ‖f‖
    split_ifs with hy
    · exact hy
    · simp [norm_nonneg f]

/-- The representative is a right inverse of the quotient map. -/
@[simp] theorem BddMeas.toLinfty_ofLinfty (f : Lp ℝ ∞ unitμ) :
    (BddMeas.ofLinfty f).toLinfty = f :=
  Lp.ext (((BddMeas.ofLinfty f).coeFn_toLinfty).trans (BddMeas.coeFn_ofLinfty f))

/-- **Every class in `L^∞([0,1])` has a bounded measurable representative.** -/
theorem BddMeas.toLinfty_surjective : Function.Surjective BddMeas.toLinfty :=
  fun f => ⟨BddMeas.ofLinfty f, BddMeas.toLinfty_ofLinfty f⟩

/-- An element of `L^∞([0,1])` is square-integrable. -/
theorem memLp_two_of_Linfty (f : Lp ℝ ∞ unitμ) : MemLp (⇑f) 2 unitμ :=
  (Lp.memLp f).mono_exponent le_top

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι]

/-! ### `𝓜_W` inside `L^∞([0,1])` -/

/-- **`𝓜_W` as a subset of `L^∞([0,1])`**, as `sec:row-criterion` defines it: the classes with a row
representative at which `ℱ_W` takes the value `c`.  By `mem_rowMinimizersLinfty_iff` this is the
set of classes that are between `0` and `1` almost everywhere and on which `ℱ_W` equals `c`. -/
def rowMinimizersLinfty (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj]
    (W : Graphon) (q α : ℝ) (μ : ι → ℝ) (c : ℝ) : Set (Lp ℝ ∞ unitμ) :=
  {f | ∃ u ∈ combinedRowMinimizers Hs W q α μ c, ⇑f =ᵐ[unitμ] u}

/-- **The two conditions defining `𝓜_W`.**  A class lies in `𝓜_W` exactly when it is
between `0` and `1` almost everywhere and `ℱ_W` takes the value `c` on it; by
`combinedRowFunctional_congr_ae` the second condition does not depend on the representative. -/
theorem mem_rowMinimizersLinfty_iff {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
    {W : Graphon} {q α c : ℝ} {μ : ι → ℝ} {f : Lp ℝ ∞ unitμ} :
    f ∈ rowMinimizersLinfty Hs W q α μ c ↔
      (∀ᵐ y ∂unitμ, f y ∈ Set.Icc (0:ℝ) 1) ∧
        ∀ u, IsRow u → ⇑f =ᵐ[unitμ] u → combinedRowFunctional Hs W q α μ u = c := by
  constructor
  · rintro ⟨u, ⟨hu, hFu⟩, hfu⟩
    refine ⟨hfu.mono fun y hy => by rw [hy]; exact hu.2 y, fun v hv hfv => ?_⟩
    exact (combinedRowFunctional_congr_ae Hs W q α μ hv hu (hfv.symm.trans hfu)).trans hFu
  · rintro ⟨hbd, hF⟩
    have hfm : Measurable (fun y => max 0 (min 1 (f y))) :=
      measurable_const.max (measurable_const.min (Lp.stronglyMeasurable f).measurable)
    have hrow : IsRow (fun y => max 0 (min 1 (f y))) :=
      ⟨hfm, fun y => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩
    have hae : ⇑f =ᵐ[unitμ] fun y => max 0 (min 1 (f y)) :=
      hbd.mono fun y hy => by
        show f y = max 0 (min 1 (f y))
        rw [min_eq_right hy.2, max_eq_right hy.1]
    exact ⟨_, ⟨hrow, hF _ hrow hae⟩, hae⟩

/-- **`lem:row-compact` in the paper's form**: `𝓜_W` is a compact subset of `L^∞([0,1])`. -/
theorem row_compact_Linfty (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι}
    (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j)
    (hμ₀ : 0 < μ j₀) (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    IsCompact (rowMinimizersLinfty Hs W q α μ c) := by
  obtain ⟨K, hKc, hKmem, hKcov⟩ :=
    row_compact Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  have hset : rowMinimizersLinfty Hs W q α μ c = BddMeas.toLinfty '' K := by
    ext f
    constructor
    · rintro ⟨u, hu, hfu⟩
      obtain ⟨w, hw, huw⟩ := hKcov u hu
      exact ⟨w, hw, Lp.ext ((BddMeas.coeFn_toLinfty w).trans (huw.symm.trans hfu.symm))⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⇑w, hKmem w hw, BddMeas.coeFn_toLinfty w⟩
  rw [hset]
  exact hKc.image BddMeas.continuous_toLinfty

/-- **`lem:row-finite` in the paper's form**: `𝓜_W` is a finite subset of `L^∞([0,1])`.  In the
quotient the finitely many representatives of `row_finite` become finitely many points, because
two classes with a common representative are equal. -/
theorem row_finite_Linfty (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] {j₀ : ι}
    (W : Graphon) {q α ω c : ℝ} {μ : ι → ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j)
    (hμ₀ : 0 < μ j₀) (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    (rowMinimizersLinfty Hs W q α μ c).Finite := by
  obtain ⟨g, hg⟩ := row_finite Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow
  have hsub : rowMinimizersLinfty Hs W q α μ c
      ⊆ ⋃ g' ∈ (g : Set (ℝ → ℝ)), {f : Lp ℝ ∞ unitμ | ⇑f =ᵐ[unitμ] g'} := by
    rintro f ⟨u, hu, hfu⟩
    obtain ⟨g', hg', hug'⟩ := hg u hu
    exact Set.mem_biUnion hg' (hfu.trans hug')
  refine Set.Finite.subset (Set.Finite.biUnion g.finite_toSet fun g' _ => ?_) hsub
  refine Set.Subsingleton.finite fun f hf f' hf' => Lp.ext ?_
  have h1 : ⇑f =ᵐ[unitμ] g' := hf
  have h2 : ⇑f' =ᵐ[unitμ] g' := hf'
  exact h1.trans h2.symm

/-! ### `Q_u` on `L^∞([0,1])` -/

section SecondVariation

variable {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj] {W : Graphon} {μ : ι → ℝ}

variable (Hs W μ) in
/-- **`Q_u` on `L^∞([0,1])`**, which is the domain the paper gives the second variation.  It is
the restriction of `secondVariationL2` along the inclusion `L^∞([0,1]) ⊆ L^2([0,1])`
(`secondVariationLinfty_eq_secondVariationL2`). -/
noncomputable def secondVariationLinfty (u : BddMeas) (h : Lp ℝ ∞ unitμ) : ℝ :=
  secondVariationFun Hs W μ u ⇑h

/-- `Q_u` on `L^∞([0,1])` is computed by any bounded measurable representative. -/
theorem secondVariationLinfty_toLinfty (u h : BddMeas) :
    secondVariationLinfty Hs W μ u h.toLinfty = secondVariationFun Hs W μ u ⇑h :=
  secondVariationFun_congr u h.coeFn_toLinfty

/-- On `L^∞([0,1])` the second variation is the `L^2` one, restricted along the inclusion. -/
theorem secondVariationLinfty_eq_secondVariationL2 (u : BddMeas) (h : Lp ℝ ∞ unitμ) :
    secondVariationLinfty Hs W μ u h
      = secondVariationL2 Hs W μ u ((memLp_two_of_Linfty h).toLp ⇑h) :=
  (secondVariationL2_toLp u (memLp_two_of_Linfty h)).symm

/-- On a class with a bounded measurable representative, `Q_u` is `secondVariation`. -/
theorem secondVariationLinfty_toLinfty_eq_secondVariation {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d) (h : BddMeas) :
    secondVariationLinfty Hs W μ u h.toLinfty = secondVariation Hs W μ u h := by
  rw [secondVariationLinfty_toLinfty, secondVariationFun_coe hc hd hu]

end SecondVariation

/-! ### `lem:bordered` on `L^∞([0,1]) × ℝ` -/

section Bordered

variable {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj] {W : Graphon} {q α : ℝ}
variable {μ : ι → ℝ}

/-- The value of the bordered operator at a point, with the linearisation written as
`combinedLinFun`. -/
theorem borderedOp_apply_eq {u : BddMeas} (hu : UnitValued u) (b : BddMeas) (lam : ℝ) (y : ℝ) :
    (borderedOp Hs W μ u (b, lam)).1 y
      = b y - (combinedLinFun Hs W μ u ⇑b y + weight u y * (lam / 2)) := by
  rw [borderedOp_apply]
  show b y - (weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b
    + (lam / 2) • (1 : BddMeas))) y = _
  rw [BddMeas.mul_apply, BddMeas.add_apply, BddMeas.smul_apply, BddMeas.smul_apply,
    BddMeas.one_apply, congrFun (combinedLinFun_coe hu b) y, BddMeas.mul_apply,
    BddMeas.smul_apply]
  ring

/-- **The bordered operator does not see null sets**, so it descends to `L^∞([0,1]) × ℝ`. -/
theorem borderedOp_congr_ae {u : BddMeas} (hu : UnitValued u) {b b' : BddMeas} (lam : ℝ)
    (hae : ⇑b =ᵐ[unitμ] ⇑b') :
    (borderedOp Hs W μ u (b, lam)).1.toLinfty = (borderedOp Hs W μ u (b', lam)).1.toLinfty
      ∧ (borderedOp Hs W μ u (b, lam)).2 = (borderedOp Hs W μ u (b', lam)).2 := by
  have hL : combinedLinFun Hs W μ u ⇑b = combinedLinFun Hs W μ u ⇑b' :=
    combinedLinFun_congr u hae
  refine ⟨BddMeas.toLinfty_congr (hae.mono fun y hy => ?_), ?_⟩
  · rw [borderedOp_apply_eq hu, borderedOp_apply_eq hu, hy, hL]
  · rw [borderedOp_apply, borderedOp_apply]
    show BddMeas.integ b = BddMeas.integ b'
    rw [BddMeas.integ_apply, BddMeas.integ_apply]
    exact integral_congr_ae hae

variable (Hs W μ) in
/-- **The bordered second variation on `L^∞([0,1]) × ℝ`.**  The value is computed from the
bounded measurable representative `BddMeas.ofLinfty`; by `borderedOp_congr_ae` the choice of
representative does not matter, which is what makes this well defined and linear. -/
noncomputable def borderedOpLinfty {u : BddMeas} (hu : UnitValued u) :
    (Lp ℝ ∞ unitμ × ℝ) →L[ℝ] (Lp ℝ ∞ unitμ × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun p => (((borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2)).1).toLinfty,
        (borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2)).2)
      map_add' := fun p p' => by
        have hae : ⇑(BddMeas.ofLinfty (p.1 + p'.1))
            =ᵐ[unitμ] ⇑(BddMeas.ofLinfty p.1 + BddMeas.ofLinfty p'.1) := by
          refine (BddMeas.coeFn_ofLinfty _).trans ((Lp.coeFn_add p.1 p'.1).trans ?_)
          exact ((BddMeas.coeFn_ofLinfty p.1).symm.add (BddMeas.coeFn_ofLinfty p'.1).symm)
        obtain ⟨h1, h2⟩ := borderedOp_congr_ae (Hs := Hs) (W := W) (μ := μ) hu (p.2 + p'.2) hae
        have hsum : (BddMeas.ofLinfty p.1 + BddMeas.ofLinfty p'.1, p.2 + p'.2)
            = (BddMeas.ofLinfty p.1, p.2) + (BddMeas.ofLinfty p'.1, p'.2) := rfl
        rw [hsum, map_add] at h1 h2
        refine Prod.ext ?_ ?_
        · show (borderedOp Hs W μ u (BddMeas.ofLinfty (p.1 + p'.1), p.2 + p'.2)).1.toLinfty = _
          rw [h1]
          exact BddMeas.toLinfty_add _ _
        · show (borderedOp Hs W μ u (BddMeas.ofLinfty (p.1 + p'.1), p.2 + p'.2)).2 = _
          exact h2
      map_smul' := fun r p => by
        have hae : ⇑(BddMeas.ofLinfty (r • p.1)) =ᵐ[unitμ] ⇑(r • BddMeas.ofLinfty p.1) := by
          refine (BddMeas.coeFn_ofLinfty _).trans ((Lp.coeFn_smul r p.1).trans ?_)
          exact ((BddMeas.coeFn_ofLinfty p.1).symm.const_smul r).trans
            (by rw [BddMeas.coe_smul])
        obtain ⟨h1, h2⟩ := borderedOp_congr_ae (Hs := Hs) (W := W) (μ := μ) hu (r * p.2) hae
        have hsmul : (r • BddMeas.ofLinfty p.1, r * p.2)
            = r • (BddMeas.ofLinfty p.1, p.2) := rfl
        rw [hsmul, map_smul] at h1 h2
        simp only [RingHom.id_apply]
        refine Prod.ext ?_ ?_
        · show (borderedOp Hs W μ u (BddMeas.ofLinfty (r • p.1), r * p.2)).1.toLinfty = _
          rw [h1]
          exact BddMeas.toLinfty_smul _ _
        · show (borderedOp Hs W μ u (BddMeas.ofLinfty (r • p.1), r * p.2)).2 = _
          exact h2 }
    ‖borderedOp Hs W μ u‖ (fun p => by
      have hp : ‖(BddMeas.ofLinfty p.1, p.2)‖ ≤ ‖p‖ := by
        rw [Prod.norm_def, Prod.norm_def]
        exact max_le_max (BddMeas.norm_ofLinfty_le p.1) le_rfl
      have hop : ‖borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2)‖
          ≤ ‖borderedOp Hs W μ u‖ * ‖p‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      show ‖(((borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2)).1).toLinfty,
        (borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2)).2)‖ ≤ _
      rw [Prod.norm_def]
      exact max_le ((BddMeas.norm_toLinfty_le _).trans
          ((norm_fst_le (borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2))).trans hop))
        ((norm_snd_le (borderedOp Hs W μ u (BddMeas.ofLinfty p.1, p.2))).trans hop))

/-- The value of the descended operator. -/
theorem borderedOpLinfty_apply {u : BddMeas} (hu : UnitValued u) (f : Lp ℝ ∞ unitμ) (lam : ℝ) :
    borderedOpLinfty Hs W μ hu (f, lam)
      = (((borderedOp Hs W μ u (BddMeas.ofLinfty f, lam)).1).toLinfty,
          (borderedOp Hs W μ u (BddMeas.ofLinfty f, lam)).2) := rfl

/-- The descended operator agrees with the bordered operator on bounded representatives. -/
theorem borderedOpLinfty_toLinfty {u : BddMeas} (hu : UnitValued u) (b : BddMeas) (lam : ℝ) :
    borderedOpLinfty Hs W μ hu (b.toLinfty, lam)
      = (((borderedOp Hs W μ u (b, lam)).1).toLinfty, (borderedOp Hs W μ u (b, lam)).2) := by
  have hae : ⇑(BddMeas.ofLinfty b.toLinfty) =ᵐ[unitμ] ⇑b :=
    (BddMeas.coeFn_ofLinfty _).trans b.coeFn_toLinfty
  obtain ⟨h1, h2⟩ := borderedOp_congr_ae (Hs := Hs) (W := W) (μ := μ) hu lam hae
  rw [borderedOpLinfty_apply, h1, h2]

/-- The zero class. -/
@[simp] theorem BddMeas.toLinfty_zero : (0 : BddMeas).toLinfty = (0 : Lp ℝ ∞ unitμ) :=
  Lp.ext (((0 : BddMeas).coeFn_toLinfty).trans ((Lp.coeFn_zero ℝ ∞ unitμ).symm))

/-- Values in a compact subinterval of `(0,1)` are values in `[0,1]`. -/
theorem unitValued_of_mem_Icc {c d : ℝ} (hc : 0 < c) (hd : d < 1) {u : BddMeas}
    (hu : ∀ y, u y ∈ Set.Icc c d) : UnitValued u :=
  fun y => ⟨hc.le.trans (hu y).1, (hu y).2.trans hd.le⟩

/-- **The descended bordered operator is injective.** -/
theorem borderedOpLinfty_injective {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    (hc1 : c ≤ 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    Function.Injective (borderedOpLinfty Hs W μ (unitValued_of_mem_Icc hc hd hu)) := by
  set hUV := unitValued_of_mem_Icc hc hd hu with hUVdef
  have key : ∀ (f : Lp ℝ ∞ unitμ) (lam : ℝ),
      borderedOpLinfty Hs W μ hUV (f, lam) = 0 → f = 0 ∧ lam = 0 := by
    intro f lam hker
    set b := BddMeas.ofLinfty f with hbdef
    set b₁ : BddMeas :=
      weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b + (lam / 2) • (1 : BddMeas))
      with hb₁def
    have hX1 : (borderedOp Hs W μ u (b, lam)).1.toLinfty = (0 : Lp ℝ ∞ unitμ) :=
      congrArg Prod.fst hker
    have hX2 : (borderedOp Hs W μ u (b, lam)).2 = 0 := congrArg Prod.snd hker
    have hXeq : (borderedOp Hs W μ u (b, lam)).1 = b - b₁ := by
      rw [borderedOp_apply, hb₁def]
    have hae0 : ⇑(borderedOp Hs W μ u (b, lam)).1 =ᵐ[unitμ] (0 : ℝ → ℝ) := by
      have hc0 := (borderedOp Hs W μ u (b, lam)).1.coeFn_toLinfty
      rw [hX1] at hc0
      exact hc0.symm.trans (Lp.coeFn_zero ℝ ∞ unitμ)
    have haeb : ⇑b =ᵐ[unitμ] ⇑b₁ := by
      refine hae0.mono fun y hy => ?_
      have h1 : (borderedOp Hs W μ u (b, lam)).1 y = b y - b₁ y := by
        rw [hXeq, BddMeas.sub_apply]
      have h2 : b y - b₁ y = 0 := by rw [← h1]; simpa using hy
      show b y = b₁ y
      linarith
    have hGb : weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b)
        = weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b₁) := by
      have hG : combinedLinFun Hs W μ u ⇑b = combinedLinFun Hs W μ u ⇑b₁ :=
        combinedLinFun_congr u haeb
      rw [combinedLinFun_coe hUV b, combinedLinFun_coe hUV b₁] at hG
      exact DFunLike.coe_injective hG
    have hint : BddMeas.integ b₁ = 0 := by
      have h1 : BddMeas.integ b = 0 := by
        rw [← hX2, borderedOp_apply]
      rw [BddMeas.integ_apply, ← integral_congr_ae haeb, ← BddMeas.integ_apply, h1]
    have hb₁eq : borderedOp Hs W μ u (b₁, lam) = 0 := by
      rw [borderedOp_apply]
      refine Prod.ext ?_ hint
      show b₁ - weight u * ((1 / 2 : ℝ) • combinedGradDeriv Hs W μ u b₁
        + (lam / 2) • (1 : BddMeas)) = 0
      rw [mul_add, ← hGb, ← mul_add, ← hb₁def, sub_self]
    have hz : ((b₁, lam) : BddMeas × ℝ) = 0 :=
      borderedOp_injective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL
        (by show borderedOp Hs W μ u (b₁, lam) = borderedOp Hs W μ u 0
            rw [hb₁eq, map_zero])
    refine ⟨?_, congrArg Prod.snd hz⟩
    have hb₁0 : b₁ = 0 := congrArg Prod.fst hz
    rw [← BddMeas.toLinfty_ofLinfty f, ← hbdef, BddMeas.toLinfty_congr haeb, hb₁0,
      BddMeas.toLinfty_zero]
  intro p p' hpp
  obtain ⟨h1, h2⟩ := key (p.1 - p'.1) (p.2 - p'.2)
    (by show borderedOpLinfty Hs W μ hUV (p - p') = 0
        rw [map_sub, hpp, sub_self])
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

/-- **The descended bordered operator is surjective.** -/
theorem borderedOpLinfty_surjective {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    (hc1 : c ≤ 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    Function.Surjective (borderedOpLinfty Hs W μ (unitValued_of_mem_Icc hc hd hu)) := by
  intro p
  obtain ⟨⟨b, lam⟩, hblam⟩ :=
    borderedOp_surjective (Hs := Hs) (W := W) (μ := μ) hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1
      hu hmin hEL (BddMeas.ofLinfty p.1, p.2)
  refine ⟨(b.toLinfty, lam), ?_⟩
  rw [borderedOpLinfty_toLinfty, hblam]
  exact Prod.ext (BddMeas.toLinfty_ofLinfty p.1) rfl

variable (Hs W μ) in
/-- **`lem:bordered` in the paper's form**: the bordered second variation is a bounded
isomorphism of `L^∞([0,1]) × ℝ`.  Boundedness of the inverse is automatic from the open mapping
theorem, since `L^∞([0,1]) × ℝ` is complete. -/
noncomputable def borderedEquivLinfty {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    (hc1 : c ≤ 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    (Lp ℝ ∞ unitμ × ℝ) ≃L[ℝ] (Lp ℝ ∞ unitμ × ℝ) :=
  ContinuousLinearEquiv.ofBijective (borderedOpLinfty Hs W μ (unitValued_of_mem_Icc hc hd hu))
    (LinearMap.ker_eq_bot.mpr (borderedOpLinfty_injective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1
      hu hmin hEL))
    (LinearMap.range_eq_top.mpr (borderedOpLinfty_surjective hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd
      hc1 hu hmin hEL))

/-- The bordered isomorphism of `L^∞([0,1]) × ℝ` is the descended bordered operator. -/
theorem coe_borderedEquivLinfty {j₀ : ι} (hμ : ∀ j, 0 ≤ μ j) (hμ₀ : 0 < μ j₀)
    (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) (hq0 : 0 < q) (hq1 : q < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c d : ℝ} (hc : 0 < c) (hd : d < 1)
    (hc1 : c ≤ 1) {u : BddMeas} (hu : ∀ y, u y ∈ Set.Icc c d)
    (hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE Hs W q α μ u ≤ rowFunctionalE Hs W q α μ v)
    (hEL : ∀ y, 2 * Jp' q (u y) - 2 * α = combinedGradE Hs W μ u y) :
    ((borderedEquivLinfty Hs W μ hμ hμ₀ hΔ hq0 hq1 hω0 hω1 hWω hc hd hc1 hu hmin hEL :
        (Lp ℝ ∞ unitμ × ℝ) →L[ℝ] (Lp ℝ ∞ unitμ × ℝ)))
      = borderedOpLinfty Hs W μ (unitValued_of_mem_Icc hc hd hu) := rfl

end Bordered

end UpperTailMultipodality
