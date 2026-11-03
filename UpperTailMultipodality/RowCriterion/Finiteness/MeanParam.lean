import UpperTailMultipodality.RowCriterion.Basic
import UpperTailMultipodality.RowCriterion.Finiteness.Canonical

/-!
# The mean parametrization of `𝓜_W`

By `prop:row-ordering` the elements of `𝓜_W` are totally ordered, so the mean separates them, and
by `Finiteness/Canonical.lean` each of them agrees almost everywhere with a canonical
representative that is Lipschitz in the mean.  This file packages that scaffolding once, as
`MeanParam`, so that both `lem:row-compact` (`Finiteness/Compact.lean`) and `lem:row-finite`
(`Finite.lean`) can use it:

* the set `A` of means is a closed subset of `[0,1]`;
* `rep : ℝ → BddMeas` picks a canonical representative for each mean, with values in a fixed
  compact subinterval `[lo,hi] ⊆ (0,1)`, solving the fixed-point form of `eq:row-euler`;
* `rep` realizes its mean, is `L`-Lipschitz in it, and exhausts `𝓜_W` up to null sets.

Compactness of `𝓜_W` needs only the closedness and the Lipschitz bound; finiteness additionally
runs the analytic branch argument of `Finiteness/Branch.lean` on the accumulation points of `A`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] {Hs : ι → SimpleGraph V} [∀ j, DecidableRel (Hs j).Adj]
variable {W : Graphon} {q α : ℝ} {μ : ι → ℝ}

/-- A graphon that is almost everywhere at least `ω` forces `ω ≤ 1`. -/
theorem le_one_of_ae_le {ω : ℝ} {W : Graphon} (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) : ω ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hfalse : ∀ᵐ z ∂gμ, False := by
    filter_upwards [hWω] with z hz
    have := W.le_one' z.1 z.2
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have hone : (gμ Set.univ) = 1 := measure_univ
  rw [hfalse] at hone
  simp at hone

/-- **The mean parametrization of the set of row minimizers.**  The bundled form of the
scaffolding described in the module docstring. -/
structure MeanParam (Hs : ι → SimpleGraph V) [∀ j, DecidableRel (Hs j).Adj] (W : Graphon)
    (q α : ℝ) (μ : ι → ℝ) (c : ℝ) where
  /-- The set of means of row minimizers. -/
  A : Set ℝ
  /-- A canonical representative for each mean. -/
  rep : ℝ → BddMeas
  /-- The lower end of the interval containing all representatives. -/
  lo : ℝ
  /-- The upper end of the interval containing all representatives. -/
  hi : ℝ
  /-- The Lipschitz constant of `rep` in the mean. -/
  L : ℝ
  lo_pos : 0 < lo
  hi_lt_one : hi < 1
  lo_le_one : lo ≤ 1
  L_nonneg : 0 ≤ L
  A_subset : A ⊆ Set.Icc 0 1
  A_closed : IsClosed A
  rep_mem : ∀ a ∈ A, ∀ y, (rep a) y ∈ Set.Icc lo hi
  rep_val : ∀ a ∈ A, rowFunctionalE Hs W q α μ (rep a) = c
  rep_fix : ∀ a ∈ A, rep a = BddMeas.sigma (elArg Hs W q α μ (rep a, 0))
  rep_mean : ∀ a ∈ A, BddMeas.integ (rep a) = a
  rep_lipschitz : ∀ a ∈ A, ∀ a' ∈ A, ‖rep a - rep a'‖ ≤ L * |a - a'|
  mem_iff : ∀ a : ℝ, a ∈ A ↔ ∃ u ∈ combinedRowMinimizers Hs W q α μ c, ∫ y, u y ∂unitμ = a
  rep_ae : ∀ u ∈ combinedRowMinimizers Hs W q α μ c, u =ᵐ[unitμ] ⇑(rep (∫ y, u y ∂unitμ))

namespace MeanParam

variable {c : ℝ} (P : MeanParam Hs W q α μ c)

/-- Every representative is a row. -/
theorem rep_isRow (a : ℝ) (ha : a ∈ P.A) : IsRow (⇑(P.rep a)) :=
  ⟨(P.rep a).measurable, fun y =>
    ⟨P.lo_pos.le.trans (P.rep_mem a ha y).1, (P.rep_mem a ha y).2.trans P.hi_lt_one.le⟩⟩

/-- Every representative is itself a row minimizer. -/
theorem rep_mem_rowMinimizers (a : ℝ) (ha : a ∈ P.A) :
    ⇑(P.rep a) ∈ combinedRowMinimizers Hs W q α μ c :=
  ⟨P.rep_isRow a ha, P.rep_val a ha⟩

/-- `A` is compact, being closed and bounded. -/
theorem A_isCompact : IsCompact P.A :=
  isCompact_Icc.of_isClosed_subset P.A_closed P.A_subset

/-- `rep` is continuous on `A`, by the Lipschitz bound. -/
theorem rep_continuousOn : ContinuousOn P.rep P.A := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hL1 : (0:ℝ) < P.L + 1 := by linarith [P.L_nonneg]
  refine ⟨ε / (P.L + 1), div_pos hε hL1, fun a ha hab => ?_⟩
  have hlip := P.rep_lipschitz a ha b hb
  rw [Real.dist_eq] at hab
  rw [dist_eq_norm]
  calc ‖P.rep a - P.rep b‖ ≤ P.L * |a - b| := hlip
    _ ≤ (P.L + 1) * |a - b| := by nlinarith [abs_nonneg (a - b)]
    _ < (P.L + 1) * (ε / (P.L + 1)) := mul_lt_mul_of_pos_left hab hL1
    _ = ε := by field_simp

end MeanParam

/-- **Existence of the mean parametrization.**  Assembles `row_interior`, `prop:row-ordering`
(through `row_chain`), the canonical representatives of `Finiteness/Canonical.lean` and the
closedness criterion `isClosed_of_lipschitz_rep`. -/
theorem exists_meanParam {j₀ : ι} (hq0 : 0 < q) (hq1 : q < 1) (hμ : ∀ j, 0 ≤ μ j)
    (hμ₀ : 0 < μ j₀) (hΔ : ∃ v, 2 ≤ (Hs j₀).degree v) {ω : ℝ} (hω : 0 < ω)
    (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2) {c : ℝ}
    (hlow : ∀ u, IsRow u → c ≤ combinedRowFunctional Hs W q α μ u) :
    Nonempty (MeanParam Hs W q α μ c) := by
  classical
  -- interiority and the Euler–Lagrange equation
  obtain ⟨δ, hδ0, hδ1, hint⟩ := row_interior Hs W hq0 hq1 hμ hlow
  -- the bounds satisfied by canonical representatives
  set lo : ℝ := BddMeas.logistic (α + logit q) with hlodef
  set hi : ℝ := BddMeas.logistic (α + logit q + 1 / 2 * combinedLipConst Hs μ) with hhidef
  have hlo : 0 < lo := BddMeas.logistic_pos _
  have hhi : hi < 1 := BddMeas.logistic_lt_one _
  have hlo1 : lo ≤ 1 := (BddMeas.logistic_lt_one _).le
  -- the set of means of minimizers
  set A : Set ℝ := {a : ℝ | ∃ u : ℝ → ℝ, u ∈ combinedRowMinimizers Hs W q α μ c ∧
    ∫ y, u y ∂unitμ = a} with hAdef
  -- choose a minimizer for every mean
  have hchoice : ∀ a : ℝ, ∃ w : BddMeas, a ∈ A →
      (IsRow (⇑w) ∧ combinedRowFunctional Hs W q α μ (⇑w) = c ∧ ∫ y, w y ∂unitμ = a) := by
    intro a
    by_cases h : a ∈ A
    · obtain ⟨u, ⟨hu, hcu⟩, hmu⟩ := h
      exact ⟨rowToBdd hu, fun _ => ⟨hu, hcu, hmu⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Uw hUw using hchoice
  set rep : ℝ → BddMeas := fun a => canonical Hs W q α μ (Uw a) with hrepdef
  have hUrow : ∀ a ∈ A, IsRow (⇑(Uw a)) := fun a ha => (hUw a ha).1
  have hUval : ∀ a ∈ A, combinedRowFunctional Hs W q α μ (⇑(Uw a)) = c := fun a ha => (hUw a ha).2.1
  have hUmean : ∀ a ∈ A, ∫ y, (Uw a) y ∂unitμ = a := fun a ha => (hUw a ha).2.2
  have hUmin : ∀ a ∈ A, ⇑(Uw a) ∈ combinedRowMinimizers Hs W q α μ c :=
    fun a ha => ⟨hUrow a ha, hUval a ha⟩
  have hUbounds : ∀ a ∈ A, (∀ᵐ y ∂unitμ, δ ≤ (Uw a) y ∧ (Uw a) y ≤ 1 - δ) :=
    fun a ha => (hint _ (hUmin a ha)).1
  have hUEL : ∀ a ∈ A, ∀ᵐ y ∂unitμ,
      2 * Jp' q ((Uw a) y) - 2 * α = combinedRootedGradient Hs W μ (⇑(Uw a)) y :=
    fun a ha => (hint _ (hUmin a ha)).2
  have hUV : ∀ a ∈ A, UnitValued (Uw a) := fun a ha => (hUrow a ha).2
  -- the canonical representative agrees with the minimizer almost everywhere
  have hrepae : ∀ a ∈ A, ⇑(rep a) =ᵐ[unitμ] ⇑(Uw a) := by
    intro a ha
    have h := canonical_ae_eq (Hs := Hs) (W := W) (μ := μ) hq0 hq1 hδ0 hδ1 (hUrow a ha)
      (hUbounds a ha) (hUEL a ha)
    rwa [rowToBdd_coe] at h
  have hrepmem : ∀ a ∈ A, ∀ y, (rep a) y ∈ Set.Icc lo hi := by
    intro a ha y
    exact canonical_mem_Icc (Hs := Hs) (W := W) (α := α) hμ (hUV a ha) y
  have hreprow : ∀ a ∈ A, IsRow (⇑(rep a)) := by
    intro a ha
    exact ⟨(rep a).measurable, fun y =>
      ⟨hlo.le.trans (hrepmem a ha y).1, (hrepmem a ha y).2.trans hhi.le⟩⟩
  have hrepval : ∀ a ∈ A, rowFunctionalE Hs W q α μ (rep a) = c := by
    intro a ha
    rw [rowFunctionalE, rowFunctional_congr_ae Hs W q α μ (hreprow a ha) (hUrow a ha)
      (hrepae a ha)]
    exact hUval a ha
  have hrepmean : ∀ a ∈ A, BddMeas.integ (rep a) = a := by
    intro a ha
    rw [BddMeas.integ_apply, integral_congr_ae (hrepae a ha)]
    exact hUmean a ha
  have hrepfix : ∀ a ∈ A, rep a = BddMeas.sigma (elArg Hs W q α μ (rep a, 0)) := by
    intro a ha
    have h := canonical_fix (Hs := Hs) (W := W) (μ := μ) hμ hq0 hq1 hδ0 hδ1 (hUrow a ha)
      (hUbounds a ha) (hUEL a ha)
    rwa [rowToBdd_coe] at h
  -- the representatives are Lipschitz in the mean
  have hlip : ∀ a ∈ A, ∀ a' ∈ A,
      ‖rep a - rep a'‖ ≤ 1 / 8 * combinedLipConst Hs μ * |a - a'| := by
    intro a ha a' ha'
    have hord := row_chain Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow (hUmin a ha)
      (hUmin a' ha')
    have h := dist_canonical_le (Hs := Hs) (W := W) (q := q) (α := α) hμ (hUrow a ha)
      (hUrow a' ha') hord
    rw [rowToBdd_coe, rowToBdd_coe, hUmean a ha, hUmean a' ha'] at h
    exact h
  have hL0 : (0:ℝ) ≤ 1 / 8 * combinedLipConst Hs μ := by
    have := combinedLipConst_nonneg (Hs := Hs) hμ
    positivity
  -- `A` is bounded and closed
  have hAbdd : A ⊆ Set.Icc 0 1 := by
    rintro a ⟨u, ⟨hu, -⟩, rfl⟩
    have hiu : Integrable u unitμ := integrable_of_abs_le hu.1 1 fun y => by
      rw [abs_le]; exact ⟨by linarith [(hu.2 y).1], (hu.2 y).2⟩
    constructor
    · exact integral_nonneg fun y => (hu.2 y).1
    · calc ∫ y, u y ∂unitμ ≤ ∫ _y, (1:ℝ) ∂unitμ :=
            integral_mono hiu (integrable_const _) fun y => (hu.2 y).2
        _ = 1 := by simp
  have hext : ∀ b : BddMeas, (∀ y, b y ∈ Set.Icc lo hi) →
      rowFunctionalE Hs W q α μ b = c → BddMeas.integ b ∈ A := by
    intro b hb hbval
    refine ⟨⇑b, ⟨⟨b.measurable, fun y =>
      ⟨hlo.le.trans (hb y).1, (hb y).2.trans hhi.le⟩⟩, hbval⟩, ?_⟩
    rw [BddMeas.integ_apply]
  have hAclosed : IsClosed A :=
    isClosed_of_lipschitz_rep (Hs := Hs) (W := W) (α := α) hq0 hq1 hμ hlo hhi hrepmem hrepval
      hrepmean hL0 hlip hext
  -- every minimizer agrees almost everywhere with the representative of its mean
  have hcover : ∀ u ∈ combinedRowMinimizers Hs W q α μ c,
      u =ᵐ[unitμ] ⇑(rep (∫ y, u y ∂unitμ)) := by
    rintro u ⟨hu, hcu⟩
    have hmemA : (∫ y, u y ∂unitμ) ∈ A := ⟨u, ⟨hu, hcu⟩, rfl⟩
    have hord := row_chain Hs (j₀ := j₀) W hq0 hq1 hμ hμ₀ hΔ hω hWω hlow ⟨hu, hcu⟩
      (hUmin _ hmemA)
    have hmeans : ∫ y, u y ∂unitμ = ∫ y, (Uw (∫ y, u y ∂unitμ)) y ∂unitμ := by
      rw [hUmean _ hmemA]
    have hae : u =ᵐ[unitμ] ⇑(Uw (∫ y, u y ∂unitμ)) :=
      ae_eq_of_mean_eq hu (hUrow _ hmemA) hord hmeans
    exact hae.trans (hrepae _ hmemA).symm
  exact ⟨{ A := A, rep := rep, lo := lo, hi := hi, L := 1 / 8 * combinedLipConst Hs μ
           lo_pos := hlo, hi_lt_one := hhi, lo_le_one := hlo1, L_nonneg := hL0
           A_subset := hAbdd, A_closed := hAclosed
           rep_mem := hrepmem, rep_val := hrepval, rep_fix := hrepfix, rep_mean := hrepmean
           rep_lipschitz := hlip, mem_iff := fun _ => Iff.rfl, rep_ae := hcover }⟩

end UpperTailMultipodality
