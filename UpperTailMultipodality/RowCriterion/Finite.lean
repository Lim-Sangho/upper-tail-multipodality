import UpperTailMultipodality.RowCriterion.Basic
import UpperTailMultipodality.RowCriterion.Finiteness.Canonical

/-!
# Finiteness of the set of row minimizers (`lem:row-finite`)

The set `𝓜_W` is finite up to null sets.  Every minimizer agrees almost everywhere with its
canonical representative `σ(ℓ(q) + α + (μ/2)∇ℛ_W(u))` (`Finiteness/Canonical.lean`), which takes
values in a fixed compact subinterval of `(0,1)`, and by `prop:row-chain` distinct minimizers
have distinct means and their canonical representatives are Lipschitz in the mean.  Hence the
set `A` of means is a closed bounded subset of `ℝ` in bijection with `𝓜_W`.  Around an
accumulation point of `A` the analytic implicit function theorem produces an analytic branch of
solutions of `eq:row-euler` whose multiplier vanishes identically (identity theorem) and along
which `ℱ_W` is constant, so a whole interval of means lies in `A`
(`Finiteness/Branch.lean`).  A bounded closed subset of `ℝ` all of whose accumulation points are
interior is finite, and the finiteness of `𝓜_W` follows.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:row-finite`.**  `𝓜_W` is finite up to null sets: there are finitely many rows such
that every element of `𝓜_W` agrees almost everywhere with one of them. -/
theorem row_finite (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : ∃ v, 2 ≤ H.degree v) (W : Graphon) {q α μ ω c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hμ : 0 < μ) (hω : 0 < ω) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    (hlow : ∀ u, IsRow u → c ≤ rowFunctional H W q α μ u) :
    ∃ g : Finset (ℝ → ℝ), ∀ u ∈ rowMinimizers H W q α μ c, ∃ g' ∈ g, u =ᵐ[unitμ] g' := by
  classical
  -- the lower bound `ω` is at most `1`
  have hω1 : ω ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hfalse : ∀ᵐ z ∂gμ, False := by
      filter_upwards [hWω] with z hz
      have := W.le_one' z.1 z.2
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
    have : (gμ Set.univ) = 1 := measure_univ
    rw [hfalse] at this
    simp at this
  -- interiority and the Euler–Lagrange equation
  obtain ⟨δ, hδ0, hδ1, hint⟩ := row_interior H W hq0 hq1 hμ hlow
  -- the bounds satisfied by canonical representatives
  set lo : ℝ := BddMeas.logistic (α + logit q) with hlodef
  set hi : ℝ := BddMeas.logistic (α + logit q + μ / 2 * lipConst H) with hhidef
  have hlo : 0 < lo := BddMeas.logistic_pos _
  have hhi : hi < 1 := BddMeas.logistic_lt_one _
  have hlo1 : lo ≤ 1 := (BddMeas.logistic_lt_one _).le
  -- the set of means of minimizers
  set A : Set ℝ := {a : ℝ | ∃ u : ℝ → ℝ, u ∈ rowMinimizers H W q α μ c ∧
    ∫ y, u y ∂unitμ = a} with hAdef
  -- choose a minimizer for every mean
  have hchoice : ∀ a : ℝ, ∃ w : BddMeas, a ∈ A →
      (IsRow (⇑w) ∧ rowFunctional H W q α μ (⇑w) = c ∧ ∫ y, w y ∂unitμ = a) := by
    intro a
    by_cases h : a ∈ A
    · obtain ⟨u, ⟨hu, hcu⟩, hmu⟩ := h
      exact ⟨rowToBdd hu, fun _ => ⟨hu, hcu, hmu⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Uw hUw using hchoice
  set rep : ℝ → BddMeas := fun a => canonical H W q α μ (Uw a) with hrepdef
  -- basic properties of the representatives
  have hUrow : ∀ a ∈ A, IsRow (⇑(Uw a)) := fun a ha => (hUw a ha).1
  have hUval : ∀ a ∈ A, rowFunctional H W q α μ (⇑(Uw a)) = c := fun a ha => (hUw a ha).2.1
  have hUmean : ∀ a ∈ A, ∫ y, (Uw a) y ∂unitμ = a := fun a ha => (hUw a ha).2.2
  have hUmin : ∀ a ∈ A, ⇑(Uw a) ∈ rowMinimizers H W q α μ c :=
    fun a ha => ⟨hUrow a ha, hUval a ha⟩
  have hUbounds : ∀ a ∈ A, (∀ᵐ y ∂unitμ, δ ≤ (Uw a) y ∧ (Uw a) y ≤ 1 - δ) :=
    fun a ha => (hint _ (hUmin a ha)).1
  have hUEL : ∀ a ∈ A, ∀ᵐ y ∂unitμ,
      2 * Jp' q ((Uw a) y) - 2 * α = μ * rootedGradient H W (⇑(Uw a)) y :=
    fun a ha => (hint _ (hUmin a ha)).2
  have hUV : ∀ a ∈ A, UnitValued (Uw a) := fun a ha => (hUrow a ha).2
  -- the canonical representative agrees with the minimizer almost everywhere
  have hrepae : ∀ a ∈ A, ⇑(rep a) =ᵐ[unitμ] ⇑(Uw a) := by
    intro a ha
    have h := canonical_ae_eq (H := H) (W := W) (μ := μ) hq0 hq1 hδ0 hδ1 (hUrow a ha)
      (hUbounds a ha) (hUEL a ha)
    rwa [rowToBdd_coe] at h
  have hrepmem : ∀ a ∈ A, ∀ y, (rep a) y ∈ Set.Icc lo hi := by
    intro a ha y
    exact canonical_mem_Icc (H := H) (W := W) (α := α) hμ (hUV a ha) y
  have hreprow : ∀ a ∈ A, IsRow (⇑(rep a)) := by
    intro a ha
    exact ⟨(rep a).measurable, fun y =>
      ⟨hlo.le.trans (hrepmem a ha y).1, (hrepmem a ha y).2.trans hhi.le⟩⟩
  have hrepval : ∀ a ∈ A, rowFunctionalE H W q α μ (rep a) = c := by
    intro a ha
    rw [rowFunctionalE, rowFunctional_congr_ae H W q α μ (hreprow a ha) (hUrow a ha)
      (hrepae a ha)]
    exact hUval a ha
  have hrepmean : ∀ a ∈ A, BddMeas.integ (rep a) = a := by
    intro a ha
    rw [BddMeas.integ_apply, integral_congr_ae (hrepae a ha)]
    exact hUmean a ha
  have hrepfix : ∀ a ∈ A, rep a = BddMeas.sigma (elArg H W q α μ (rep a, 0)) := by
    intro a ha
    have h := canonical_fix (H := H) (W := W) (μ := μ) hq0 hq1 hδ0 hδ1 (hUrow a ha)
      (hUbounds a ha) (hUEL a ha)
    rwa [rowToBdd_coe] at h
  -- the representatives are Lipschitz in the mean
  have hlip : ∀ a ∈ A, ∀ a' ∈ A, ‖rep a - rep a'‖ ≤ μ / 8 * lipConst H * |a - a'| := by
    intro a ha a' ha'
    have hord := row_chain H hΔ W hq0 hq1 hμ hω hWω hlow (hUmin a ha) (hUmin a' ha')
    have h := dist_canonical_le (H := H) (W := W) (q := q) (α := α) hμ (hUrow a ha)
      (hUrow a' ha') hord
    rw [rowToBdd_coe, rowToBdd_coe, hUmean a ha, hUmean a' ha'] at h
    exact h
  have hL0 : (0:ℝ) ≤ μ / 8 * lipConst H := by
    have := lipConst_nonneg (H := H)
    positivity
  -- the row functional bound in the `BddMeas` form
  have hlowE : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) → c ≤ rowFunctionalE H W q α μ v :=
    fun v hv => hlow _ ⟨v.measurable, hv⟩
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
      rowFunctionalE H W q α μ b = c → BddMeas.integ b ∈ A := by
    intro b hb hbval
    refine ⟨⇑b, ⟨⟨b.measurable, fun y =>
      ⟨hlo.le.trans (hb y).1, (hb y).2.trans hhi.le⟩⟩, hbval⟩, ?_⟩
    rw [BddMeas.integ_apply]
  have hAclosed : IsClosed A :=
    isClosed_of_lipschitz_rep (H := H) (W := W) (α := α) hq0 hq1 hμ.le hlo hhi hrepmem hrepval
      hrepmean hL0 hlip hext
  -- accumulation points of `A` are interior
  have hnbhd : ∀ a ∈ A, AccPt a (𝓟 A) → ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A := by
    intro a₀ ha₀ hacc
    obtain ⟨ε, hε, hbranch⟩ := exists_interval_of_accPt (H := H) (W := W) (α := α) hΔ hq0 hq1 hμ
      hω hω1 hWω hlowE hlo hhi hlo1 hrepmem hrepval hrepfix hrepmean hL0 hlip ha₀ hacc
    refine ⟨ε, hε, fun a ha => ?_⟩
    obtain ⟨u, humem, huval, humean⟩ := hbranch a ha
    exact ⟨⇑u, ⟨⟨u.measurable, humem⟩, huval⟩, humean⟩
  have hAfin : A.Finite := finite_of_accPt_interior hAbdd hAclosed hnbhd
  -- the finite set of canonical representatives
  refine ⟨hAfin.toFinset.image (fun a => ⇑(rep a)), ?_⟩
  rintro u ⟨hu, hcu⟩
  have hmemA : (∫ y, u y ∂unitμ) ∈ A := ⟨u, ⟨hu, hcu⟩, rfl⟩
  set a : ℝ := ∫ y, u y ∂unitμ with hadef
  refine ⟨⇑(rep a), ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
    exact Set.Finite.mem_toFinset hAfin |>.mpr hmemA
  · -- `u` agrees almost everywhere with the chosen minimizer of the same mean
    have hord := row_chain H hΔ W hq0 hq1 hμ hω hWω hlow ⟨hu, hcu⟩ (hUmin a hmemA)
    have hmeans : ∫ y, u y ∂unitμ = ∫ y, (Uw a) y ∂unitμ := by rw [hUmean a hmemA]
    have hae : u =ᵐ[unitμ] ⇑(Uw a) := ae_eq_of_mean_eq hu (hUrow a hmemA) hord hmeans
    exact hae.trans (hrepae a hmemA).symm

end UpperTailMultipodality
