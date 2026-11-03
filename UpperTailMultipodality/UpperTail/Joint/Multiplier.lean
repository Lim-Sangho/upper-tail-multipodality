import UpperTailMultipodality.UpperTail.Joint.Disjoint
import UpperTailMultipodality.UpperTail.Joint.Separation
import UpperTailMultipodality.UpperTail.Support.Multiplier
import UpperTailMultipodality.RowCriterion.Defs

/-!
# Multipliers for the joint upper tail (`lem:upper-tail-multiplier`)

`insertionCone_disjoint` and `exists_multipliers_of_cone_disjoint` together give the multiplier
part of `lem:upper-tail-multiplier` for a family of constraints: at a minimizer of
`eq:joint-variational-problem` there are weights `μ_j ≥ 0`, not all zero, with

* `eq:separated-el`, `J_p'(W) = ∑_j μ_j 𝒟_{H_j,W}` almost everywhere, and
* `lem:upper-tail-multiplier`(ii), the lower bound `ℱ_W ≥ 2I_p(W) - ∑_j μ_j N t(H_j,W)` for the row
  functional `eq:row-functional` with `q = p` and `α = 0`.

The normalisation `λ > 0` of the objective's multiplier is the last step of
`lem:upper-tail-multiplier`: the direction that is
constant on the window `{η < W < 1-η}` raises every subgraph density, so a vanishing `λ` would
force all the other multipliers to vanish as well.  Dividing by `λ` gives the weights above.
The Euler-Lagrange equation follows by testing the separating functional on the directions
supported in the window, which is almost all of `[0,1]²`; the row bound, by testing it on the
vector `eq:insertion-rates` of a single row.  Not all the weights vanish, because `J_p'(W) = 0`
would force `W ≡ p`, which is infeasible here.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Set UpperTailSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A kernel cut off outside the window `{η < W < 1-η}`, so that it is an admissible direction
for the insertion. -/
noncomputable def cutKernel (W : Graphon) (η : ℝ) (U : Kernel) : Kernel where
  toFun x y := if η < W.toFun x y ∧ W.toFun x y < 1 - η then U.toFun x y else 0
  symm' x y := by
    show (if η < W.toFun x y ∧ W.toFun x y < 1 - η then U.toFun x y else 0)
      = if η < W.toFun y x ∧ W.toFun y x < 1 - η then U.toFun y x else 0
    rw [W.symm' x y, U.symm' x y]
  meas' := by
    show Measurable fun z : ℝ × ℝ =>
      if η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η then U.toFun z.1 z.2 else 0
    exact Measurable.ite ((measurableSet_lt measurable_const W.measurable_uncurry).inter
      (measurableSet_lt W.measurable_uncurry measurable_const)) U.meas' measurable_const
  bdd' := by
    obtain ⟨C, hC⟩ := U.bdd'
    refine ⟨C, fun x y => ?_⟩
    show |if η < W.toFun x y ∧ W.toFun x y < 1 - η then U.toFun x y else 0| ≤ C
    split_ifs with h
    · exact hC x y
    · rw [abs_zero]
      exact (abs_nonneg (U.toFun x y)).trans (hC x y)

/-- The cut-off kernel is an admissible direction. -/
theorem admissibleDir_cutKernel (W : Graphon) (η : ℝ) (U : Kernel) :
    AdmissibleDir W η (cutKernel W η U) := by
  intro x y h
  by_contra hc
  refine h ?_
  show (if η < W.toFun x y ∧ W.toFun x y < 1 - η then U.toFun x y else 0) = 0
  rw [if_neg hc]

/-- Inside the window the cut-off kernel agrees with the original one. -/
theorem cutKernel_ae_eq {W : Graphon} {η : ℝ}
    (hwin : ∀ᵐ z ∂gμ, η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η) (U : Kernel) :
    ∀ᵐ z ∂gμ, (cutKernel W η U).toFun z.1 z.2 = U.toFun z.1 z.2 := by
  filter_upwards [hwin] with z hz
  show (if η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η then U.toFun z.1 z.2 else 0) = _
  rw [if_pos hz]

/-- **The multipliers of `lem:upper-tail-multiplier` for a family of constraints.**  At a
minimizer of `eq:joint-variational-problem` whose values lie in a compact subinterval of `(0,1)`, there are
weights `μ_j ≥ 0`, not all zero, satisfying `eq:separated-el` and the row bound
`lem:upper-tail-multiplier`(ii). -/
theorem joint_multiplier {ι : Type*} [Fintype ι] (Hs : ι → SimpleGraph V)
    [∀ j, DecidableRel (Hs j).Adj] (hm : ∀ j, 1 ≤ (Hs j).edgeFinset.card) {p : ℝ} {τ : ι → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {W : Graphon} (hfeas : JointFeasible Hs τ W)
    (hmin : ∀ V' : Graphon, JointFeasible Hs τ V' → W.Ip p ≤ V'.Ip p)
    (hnf : ¬ ∀ j, τ j ≤ p ^ (Hs j).edgeFinset.card)
    (hlow : ∀ᵐ z ∂gμ, p ≤ W.toFun z.1 z.2) {γ : ℝ} (hγ : 0 < γ)
    (hup : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ≤ 1 - γ) :
    ∃ μ : ι → ℝ, (∀ j, 0 ≤ μ j) ∧ (∃ j, 0 < μ j) ∧
      (∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = ∑ j, μ j * derivKernel (Hs j) W z.1 z.2) ∧
      ∀ u, IsRow u → 2 * W.Ip p - ∑ j, μ j * ((Fintype.card V : ℝ) * W.tDensity (Hs j))
        ≤ combinedRowFunctional Hs W p 0 μ u := by
  classical
  -- the window `{η < W < 1-η}`, of full measure
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min p γ / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact half_pos (lt_min hp0 hγ)
  have hηp : η < p := by
    rw [hηdef]; linarith [min_le_left p γ, half_lt_self (lt_min hp0 hγ)]
  have hηγ : η < γ := by
    rw [hηdef]; linarith [min_le_right p γ, half_lt_self (lt_min hp0 hγ)]
  have hwin : ∀ᵐ z ∂gμ, η < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η := by
    filter_upwards [hlow, hup] with z h1 h2
    exact ⟨lt_of_lt_of_le hηp h1, by linarith⟩
  have hηW : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc η (1 - η) :=
    hwin.mono fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Icc p (1 - η) := by
    filter_upwards [hlow, hup] with z h1 h2
    exact ⟨h1, by linarith⟩
  have hb1 : (1:ℝ) - η < 1 := by linarith
  -- the active set
  obtain ⟨A, hAdef⟩ : ∃ A : Finset ι,
      A = Finset.univ.filter fun j => W.tDensity (Hs j) = τ j := ⟨_, rfl⟩
  have hA : ∀ j ∈ A, W.tDensity (Hs j) = τ j := by
    intro j hj
    rw [hAdef, Finset.mem_filter] at hj
    exact hj.2
  have hnA : ∀ j ∉ A, τ j < W.tDensity (Hs j) := by
    intro j hj
    refine lt_of_le_of_ne (hfeas j) fun h => hj ?_
    rw [hAdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, h.symm⟩
  -- the cone of first-order changes misses the improving directions, so it can be separated
  have hdisj := insertionCone_disjoint Hs hp0 hp1 hmin hη hηW hA hnA
  obtain ⟨lam, nu, hlam0, hnu0, hnuoff, hne, hfun⟩ :=
    exists_multipliers_of_cone_disjoint A (insertionCone Hs p W η)
      (convex_insertionCone Hs hp0 hp1 hη hb1 hηW) (zero_mem_insertionCone Hs hp0 hp1)
      (fun r hr w hw => smul_mem_insertionCone Hs hr hw) hdisj
  -- the separating functional vanishes on the admissible directions
  have hlin : ∀ Y : Kernel, AdmissibleDir W η Y →
      lam * variationIp p W Y = ∑ j, nu j * variationDensity (Hs j) W Y := by
    intro Y hY
    have h1 : 0 ≤ lam * variationIp p W Y - ∑ j, nu j * variationDensity (Hs j) W Y :=
      hfun _ (variation_mem_insertionCone Hs hp0 hp1 hY)
    have h2 : 0 ≤ lam * variationIp p W ((-1 : ℝ) • Y)
        - ∑ j, nu j * variationDensity (Hs j) W ((-1 : ℝ) • Y) :=
      hfun _ (variation_mem_insertionCone Hs hp0 hp1 (hY.smul (-1)))
    have he : ∑ j, nu j * variationDensity (Hs j) W ((-1 : ℝ) • Y)
        = -∑ j, nu j * variationDensity (Hs j) W Y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [variationDensity_smul]
      ring
    rw [variationIp_smul, he] at h2
    linarith
  -- the constant direction on the window raises every subgraph density
  obtain ⟨Z, hZdef⟩ : ∃ Z : Kernel, Z = cutKernel W η oneKernel := ⟨_, rfl⟩
  have hZadm : AdmissibleDir W η Z := hZdef ▸ admissibleDir_cutKernel W η oneKernel
  have hZ1 : ∀ᵐ z ∂gμ, Z.toFun z.1 z.2 = 1 := by
    filter_upwards [cutKernel_ae_eq hwin oneKernel] with z hz
    rw [hZdef, hz, oneKernel_apply]
  have hDZ : ∀ j, 0 < variationDensity (Hs j) W Z := by
    intro j
    have hc : 0 < ((Hs j).edgeFinset.card : ℝ) * p ^ ((Hs j).edgeFinset.card - 1) :=
      mul_pos (by exact_mod_cast hm j) (pow_pos hp0 _)
    have hle : ∀ᵐ z ∂gμ, ((Hs j).edgeFinset.card : ℝ) * p ^ ((Hs j).edgeFinset.card - 1)
        ≤ derivKernel (Hs j) W z.1 z.2 * Z.toFun z.1 z.2 := by
      filter_upwards [derivKernel_ge (Hs j) W hp0.le hlow, hZ1] with z h1 h2
      rw [h2, mul_one]; exact h1
    have h := integral_mono_ae (integrable_const _)
      (integrable_derivKernel_mul (Hs j) W Z) hle
    rw [integral_const, probReal_univ, one_smul] at h
    unfold variationDensity
    linarith
  -- `λ > 0`
  have hlam : 0 < lam := by
    rcases hlam0.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : ∑ j, nu j * variationDensity (Hs j) W Z = 0 := by
      have := hlin Z hZadm
      rw [← h] at this
      linarith
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ nu j * variationDensity (Hs j) W Z :=
      fun j _ => mul_nonneg (hnu0 j) (hDZ j).le
    have hall : ∀ j, nu j = 0 := by
      intro j
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hz j (Finset.mem_univ j)
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact h'
      · exact absurd h' (hDZ j).ne'
    rcases hne with h' | ⟨j, hj⟩
    · exact h' h.symm
    · exact hj (hall j)
  -- the normalised weights
  obtain ⟨μ, hμdef⟩ : ∃ μ : ι → ℝ, μ = fun j => nu j / lam := ⟨_, rfl⟩
  have hμ0 : ∀ j, 0 ≤ μ j := fun j => by rw [hμdef]; exact div_nonneg (hnu0 j) hlam.le
  have hμlam : ∀ j, nu j = lam * μ j := by
    intro j
    rw [hμdef]
    field_simp
  -- `eq:separated-el` tested against an arbitrary kernel
  have hlinU : ∀ U : Kernel, ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ
      = ∑ j, μ j * ∫ z, derivKernel (Hs j) W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := by
    intro U
    have hY := hlin (cutKernel W η U) (admissibleDir_cutKernel W η U)
    have hcut := cutKernel_ae_eq hwin U
    have hIp : variationIp p W (cutKernel W η U)
        = ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ := by
      unfold variationIp
      refine integral_congr_ae ?_
      filter_upwards [hcut] with z hz
      rw [hz]
    have hD : ∀ j, variationDensity (Hs j) W (cutKernel W η U)
        = ∫ z, derivKernel (Hs j) W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := by
      intro j
      unfold variationDensity
      refine integral_congr_ae ?_
      filter_upwards [hcut] with z hz
      rw [hz]
    rw [hIp] at hY
    have hY' : lam * ∫ z, Jp' p (W.toFun z.1 z.2) * U.toFun z.1 z.2 ∂gμ
        = ∑ j, lam * μ j * ∫ z, derivKernel (Hs j) W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := by
      rw [hY]
      exact Finset.sum_congr rfl fun j _ => by rw [hD j, hμlam j]
    have hfac : ∑ j, lam * μ j * ∫ z, derivKernel (Hs j) W z.1 z.2 * U.toFun z.1 z.2 ∂gμ
        = lam * ∑ j, μ j * ∫ z, derivKernel (Hs j) W z.1 z.2 * U.toFun z.1 z.2 ∂gμ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac] at hY'
    exact mul_left_cancel₀ hlam.ne' hY'
  -- the Euler-Lagrange equation
  have hple : p ≤ 1 - η := by
    obtain ⟨z, hz⟩ := hmem.exists
    exact hz.1.trans hz.2
  obtain ⟨W', hW'mem, hW'ae⟩ := W.exists_clamp hp0.le hple
    (by linarith : (1:ℝ) - η ≤ 1) hmem
  obtain ⟨G, hGdef⟩ : ∃ G : Kernel, ∀ x y, G.toFun x y
      = Jp' p (W'.toFun x y) - ∑ j, μ j * derivKernel (Hs j) W x y := by
    refine ⟨{ toFun := fun x y => Jp' p (W'.toFun x y) - ∑ j, μ j * derivKernel (Hs j) W x y
              symm' := fun x y => by
                show Jp' p (W'.toFun x y) - ∑ j, μ j * derivKernel (Hs j) W x y
                  = Jp' p (W'.toFun y x) - ∑ j, μ j * derivKernel (Hs j) W y x
                rw [W'.symm' x y]
                exact congrArg _ (Finset.sum_congr rfl fun j _ => by
                  rw [derivKernel_symm (Hs j) W x y])
              meas' := ?_
              bdd' := ?_ }, fun _ _ => rfl⟩
    · show Measurable fun z : ℝ × ℝ =>
        Jp' p (W'.toFun z.1 z.2) - ∑ j, μ j * derivKernel (Hs j) W z.1 z.2
      refine ((measurable_Jp' p).comp W'.measurable_uncurry).sub ?_
      exact Finset.measurable_sum _ fun j _ =>
        (measurable_derivKernel (Hs j) W).const_mul (μ j)
    · refine ⟨Jp' p (1 - η) + ∑ j, μ j * (Hs j).edgeFinset.card, fun x y => ?_⟩
      show |Jp' p (W'.toFun x y) - ∑ j, μ j * derivKernel (Hs j) W x y| ≤ _
      refine (abs_sub _ _).trans (add_le_add (abs_Jp'_le hp0 hb1 (hW'mem x y)) ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have hD := derivKernel_mem_Icc (Hs j) W x y
      rw [abs_mul, abs_of_nonneg (hμ0 j), abs_of_nonneg hD.1]
      exact mul_le_mul_of_nonneg_left hD.2 (hμ0 j)
  have hGG : ∫ z, G.toFun z.1 z.2 * G.toFun z.1 z.2 ∂gμ = 0 := by
    have hcongr : ∫ z, G.toFun z.1 z.2 * G.toFun z.1 z.2 ∂gμ
        = ∫ z, (Jp' p (W.toFun z.1 z.2) * G.toFun z.1 z.2
          - ∑ j, μ j * (derivKernel (Hs j) W z.1 z.2 * G.toFun z.1 z.2)) ∂gμ := by
      refine integral_congr_ae ?_
      filter_upwards [hW'ae] with z hz
      have hS : ∀ c : ℝ, ∑ j, μ j * (derivKernel (Hs j) W z.1 z.2 * c)
          = (∑ j, μ j * derivKernel (Hs j) W z.1 z.2) * c := by
        intro c
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      rw [hGdef z.1 z.2, hz, hS]
      ring
    have hint1 := integrable_Jp'_mul W G hp0 hp1 hp0 hb1 hmem
    have hint2 : ∀ j ∈ (Finset.univ : Finset ι), Integrable
        (fun z : ℝ × ℝ => μ j * (derivKernel (Hs j) W z.1 z.2 * G.toFun z.1 z.2)) gμ :=
      fun j _ => (integrable_derivKernel_mul (Hs j) W G).const_mul (μ j)
    rw [hcongr, integral_sub hint1 (integrable_finsetSum _ hint2),
      integral_finsetSum _ hint2]
    have hsum : ∑ j, ∫ z, μ j * (derivKernel (Hs j) W z.1 z.2 * G.toFun z.1 z.2) ∂gμ
        = ∑ j, μ j * ∫ z, derivKernel (Hs j) W z.1 z.2 * G.toFun z.1 z.2 ∂gμ :=
      Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    rw [hsum, hlinU G, sub_self]
  have hEL : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2)
      = ∑ j, μ j * derivKernel (Hs j) W z.1 z.2 := by
    have hG0 : ∀ᵐ z ∂gμ, G.toFun z.1 z.2 * G.toFun z.1 z.2 = 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg _)
        (integrable_kernel_mul G G)).mp hGG
    filter_upwards [hG0, hW'ae] with z h1 h2
    have h3 : G.toFun z.1 z.2 = 0 := mul_self_eq_zero.mp h1
    rw [hGdef z.1 z.2, h2] at h3
    linarith
  -- the row bound
  have hrow : ∀ u, IsRow u →
      2 * W.Ip p - ∑ j, μ j * ((Fintype.card V : ℝ) * W.tDensity (Hs j))
        ≤ combinedRowFunctional Hs W p 0 μ u := by
    intro u hu
    have h : 0 ≤ lam * (2 * ∫ y, Jp p (u y) ∂unitμ - 2 * W.Ip p)
        - ∑ j, nu j * (totalRootedDensity (Hs j) W u
          - (Fintype.card V : ℝ) * W.tDensity (Hs j)) :=
      hfun _ (singleRow_mem_insertionCone Hs hu)
    have hkey : ∑ j, nu j * (totalRootedDensity (Hs j) W u
          - (Fintype.card V : ℝ) * W.tDensity (Hs j))
        = lam * (∑ j, μ j * totalRootedDensity (Hs j) W u)
          - lam * ∑ j, μ j * ((Fintype.card V : ℝ) * W.tDensity (Hs j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hμlam j]; ring
    have hcomb : combinedRowFunctional Hs W p 0 μ u
        = 2 * ∫ y, Jp p (u y) ∂unitμ - ∑ j, μ j * totalRootedDensity (Hs j) W u := by
      unfold combinedRowFunctional combinedRooted
      ring
    rw [hkey] at h
    have h' : 0 ≤ lam * (combinedRowFunctional Hs W p 0 μ u
        - (2 * W.Ip p - ∑ j, μ j * ((Fintype.card V : ℝ) * W.tDensity (Hs j)))) := by
      rw [hcomb]
      linarith
    have h'' : 0 ≤ combinedRowFunctional Hs W p 0 μ u
        - (2 * W.Ip p - ∑ j, μ j * ((Fintype.card V : ℝ) * W.tDensity (Hs j))) :=
      nonneg_of_mul_nonneg_right h' hlam
    linarith
  -- not all the weights vanish
  refine ⟨μ, hμ0, ?_, hEL, hrow⟩
  by_contra hall
  have hzero : ∀ j, μ j = 0 := by
    intro j
    rcases (hμ0 j).lt_or_eq with h | h
    · exact absurd ⟨j, h⟩ hall
    · exact h.symm
  have hJ0 : ∀ᵐ z ∂gμ, Jp' p (W.toFun z.1 z.2) = 0 := by
    filter_upwards [hEL] with z hz
    rw [hz]
    exact Finset.sum_eq_zero fun j _ => by rw [hzero j, zero_mul]
  have hWp : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = p := by
    filter_upwards [hJ0, hwin] with z h1 h2
    refine (Jp'_strictMonoOn hp0 hp1).injOn ⟨by linarith [h2.1], by linarith [h2.2]⟩
      ⟨hp0, hp1⟩ ?_
    rw [h1, Jp'_self hp0 hp1]
  refine hnf fun j => ?_
  rw [← tDensity_ae_const W (Hs j) hWp]
  exact hfeas j

end UpperTailMultipodality
