import UpperTailMultipodality.RowCriterion.Finiteness.Bordered
import UpperTailMultipodality.RowCriterion.Finiteness.ImplicitFunction

/-!
# The analytic branch of minimizers through an accumulation point

The Euler–Lagrange equation `eq:row-euler` with multiplier `λ` is the fixed-point equation
`u = σ(ℓ(q) + α + λ/2 + (μ/2)∇ℛ_W(u))`, and `elMap` is the corresponding map, bordered by the
mean constraint.  It is analytic, and its derivative in `(u,λ)` at a minimizer is the bordered
operator of `lem:bordered`, so the analytic implicit function theorem produces an analytic
branch `a ↦ (u_*(a), λ_*(a))` through it.

If the mean of the given minimizer is an accumulation point of the set of means of minimizers,
then `λ_*` vanishes along a sequence accumulating at it, hence identically by the identity
theorem; the branch then consists of solutions of `eq:row-euler` along which `ℱ_W` is constant,
so a whole interval of means is attained.  This is the heart of `lem:row-finite`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj] {W : Graphon} {q α μ : ℝ}

variable (H W q α μ) in
/-- The argument of the logistic function in the fixed-point form of `eq:row-euler`. -/
noncomputable def elArg (z : BddMeas × ℝ) : BddMeas :=
  algebraMap ℝ BddMeas (α + logit q) + (z.2 / 2) • (1 : BddMeas) + (μ / 2) • gradE H W z.1

variable (H W q α μ) in
/-- The bordered Euler–Lagrange map `Ξ(a; u, λ)` of `lem:row-finite`, in fixed-point form. -/
noncomputable def elMap (z : BddMeas × ℝ) (a : ℝ) : BddMeas × ℝ :=
  (z.1 - BddMeas.sigma (elArg H W q α μ z), BddMeas.integ z.1 - a)

/-- The value of the argument of the logistic function. -/
theorem elArg_apply (z : BddMeas × ℝ) (y : ℝ) :
    elArg H W q α μ z y = α + logit q + z.2 / 2 + μ / 2 * gradE H W z.1 y := by
  rw [elArg]
  simp only [BddMeas.add_apply, BddMeas.smul_apply, BddMeas.coe_algebraMap, BddMeas.one_apply]
  ring

/-- Analyticity of the bordered Euler–Lagrange map. -/
theorem analyticAt_elMap (w : (BddMeas × ℝ) × ℝ) :
    AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => elMap H W q α μ w.1 w.2) w := by
  have hu : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => w.1.1) w :=
    analyticAt_fst.comp analyticAt_fst
  have hlam : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => w.1.2) w :=
    analyticAt_snd.comp analyticAt_fst
  have ha : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => w.2) w := analyticAt_snd
  have hgrad : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => gradE H W w.1.1) w :=
    (analyticAt_gradE _).comp hu
  have harg : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => elArg H W q α μ w.1) w := by
    have h1 : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => (w.1.2 / 2) • (1 : BddMeas)) w :=
      AnalyticAt.smul hlam.div_const analyticAt_const
    have h2 : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => (μ / 2) • gradE H W w.1.1) w := by
      have hmul : AnalyticAt ℝ
          (fun w : (BddMeas × ℝ) × ℝ => algebraMap ℝ BddMeas (μ / 2) * gradE H W w.1.1) w :=
        analyticAt_const.mul hgrad
      refine hmul.congr ?_
      filter_upwards with w'
      exact (Algebra.smul_def _ _).symm
    exact (analyticAt_const.add h1).add h2
  have hsig : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => BddMeas.sigma (elArg H W q α μ w.1)) w :=
    (BddMeas.analyticAt_sigma _).comp harg
  have hint : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => BddMeas.integ w.1.1 - w.2) w :=
    ((BddMeas.integ.analyticAt _).comp hu).sub ha
  exact (hu.sub hsig).prod hint

/-- **The derivative of the bordered Euler–Lagrange map** at a fixed point with zero multiplier
is the bordered operator. -/
theorem hasFDerivAt_elMap {u : BddMeas} (a : ℝ)
    (hfix : u = BddMeas.sigma (elArg H W q α μ (u, 0))) :
    HasFDerivAt (fun z : BddMeas × ℝ => elMap H W q α μ z a) (borderedOp H W μ u) (u, 0) := by
  -- the derivative of the argument of the logistic function
  set A : (BddMeas × ℝ) →L[ℝ] BddMeas :=
    ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ BddMeas ℝ).smulRight (1 : BddMeas))
      + ((μ / 2) • gradDeriv H W u).comp (ContinuousLinearMap.fst ℝ BddMeas ℝ) with hA
  have hargderiv : HasFDerivAt (fun z : BddMeas × ℝ => elArg H W q α μ z) A (u, 0) := by
    have h1 : HasFDerivAt (fun z : BddMeas × ℝ => (z.2 / 2) • (1 : BddMeas))
        ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ BddMeas ℝ).smulRight (1 : BddMeas)) (u, 0) := by
      have : (fun z : BddMeas × ℝ => (z.2 / 2) • (1 : BddMeas))
          = fun z => ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ BddMeas ℝ).smulRight
            (1 : BddMeas)) z := by
        funext z
        simp only [_root_.smul_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.coe_snd', smul_smul]
        congr 1
        ring
      rw [this]
      exact ContinuousLinearMap.hasFDerivAt _
    have h2 : HasFDerivAt (fun z : BddMeas × ℝ => (μ / 2) • gradE H W z.1)
        (((μ / 2) • gradDeriv H W u).comp (ContinuousLinearMap.fst ℝ BddMeas ℝ)) (u, 0) := by
      have hfstd : HasFDerivAt (fun z : BddMeas × ℝ => z.1)
          (ContinuousLinearMap.fst ℝ BddMeas ℝ) ((u, 0) : BddMeas × ℝ) :=
        (ContinuousLinearMap.fst ℝ BddMeas ℝ).hasFDerivAt
      have hg0 := (hasFDerivAt_gradE (H := H) (W := W) u).comp ((u, 0) : BddMeas × ℝ) hfstd
      have hg : HasFDerivAt (fun z : BddMeas × ℝ => gradE H W z.1)
          ((gradDeriv H W u).comp (ContinuousLinearMap.fst ℝ BddMeas ℝ)) (u, 0) := hg0
      have hcs := hg.const_smul (μ / 2)
      refine hcs.congr_fderiv ?_
      refine ContinuousLinearMap.ext fun z => ?_
      rfl
    have h3 := (h1.const_add (algebraMap ℝ BddMeas (α + logit q))).add h2
    have hfun : (fun z : BddMeas × ℝ => elArg H W q α μ z)
        = fun z => (algebraMap ℝ BddMeas (α + logit q) + (z.2 / 2) • (1 : BddMeas))
          + (μ / 2) • gradE H W z.1 := rfl
    rw [hfun, hA]
    exact h3
  -- the derivative of the logistic composition
  have hsig := (BddMeas.hasFDerivAt_sigma (elArg H W q α μ (u, 0))).comp (u, 0) hargderiv
  have hsigma0 : BddMeas.sigma (elArg H W q α μ (u, 0)) = u := hfix.symm
  rw [hsigma0] at hsig
  -- assemble
  have hfst : HasFDerivAt (fun z : BddMeas × ℝ => z.1 - BddMeas.sigma (elArg H W q α μ z))
      ((ContinuousLinearMap.fst ℝ BddMeas ℝ)
        - (BddMeas.mulLeftCLM (u * (1 - u))).comp A) (u, 0) := by
    have hid : HasFDerivAt (fun z : BddMeas × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ BddMeas ℝ) ((u, 0) : BddMeas × ℝ) :=
      (ContinuousLinearMap.fst ℝ BddMeas ℝ).hasFDerivAt
    exact hid.sub hsig
  have hsnd : HasFDerivAt (fun z : BddMeas × ℝ => BddMeas.integ z.1 - a)
      (BddMeas.integ.comp (ContinuousLinearMap.fst ℝ BddMeas ℝ)) (u, 0) := by
    have hfstd : HasFDerivAt (fun z : BddMeas × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ BddMeas ℝ) ((u, 0) : BddMeas × ℝ) :=
      (ContinuousLinearMap.fst ℝ BddMeas ℝ).hasFDerivAt
    have h := (BddMeas.integ.hasFDerivAt (x := u)).comp (u, 0) hfstd
    exact h.sub_const a
  have hprod := hfst.prodMk hsnd
  refine hprod.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
  obtain ⟨h, lam⟩ := z
  rw [borderedOp_apply]
  refine Prod.ext ?_ rfl
  simp only [ContinuousLinearMap.prod_apply, _root_.sub_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply, BddMeas.mulLeftCLM_apply, hA, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
    weight]
  congr 2
  rw [add_comm]
  congr 1
  rw [smul_smul]
  congr 1
  ring

/-- The Euler–Lagrange equation in the form used by `Bordered`, from the fixed-point form. -/
theorem el_of_fix (hq0 : 0 < q) (hq1 : q < 1) {u : BddMeas}
    (hfix : u = BddMeas.sigma (elArg H W q α μ (u, 0))) (y : ℝ) :
    2 * Jp' q (u y) - 2 * α = μ * gradE H W u y := by
  have h1 : u y = BddMeas.logistic (elArg H W q α μ (u, 0) y) := by
    conv_lhs => rw [hfix]
    rw [BddMeas.sigma_apply]
  rw [h1, Jp'_logistic hq0 hq1, elArg_apply]
  simp only
  ring

/-- Values of a fixed point lie strictly between `0` and `1`. -/
theorem fix_mem_Icc {u : BddMeas} (hfix : u = BddMeas.sigma (elArg H W q α μ (u, 0))) (y : ℝ) :
    u y ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : u y = BddMeas.logistic (elArg H W q α μ (u, 0) y) := by
    conv_lhs => rw [hfix]
    rw [BddMeas.sigma_apply]
  rw [h1]
  exact ⟨(BddMeas.logistic_pos _).le, (BddMeas.logistic_lt_one _).le⟩

/-- **The interval of means around an accumulation point** (the core of `lem:row-finite`).
If the mean `a₀` of a minimizer is an accumulation point of the set `A` of means of minimizers,
then every mean in a neighbourhood of `a₀` is attained by a minimizer. -/
theorem exists_interval_of_accPt
    (hΔ : ∃ v, 2 ≤ H.degree v) (hq0 : 0 < q) (hq1 : q < 1) (hμ : 0 < μ)
    {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hWω : ∀ᵐ z ∂gμ, ω ≤ W.toFun z.1 z.2)
    {cval : ℝ}
    (hlow : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) → cval ≤ rowFunctionalE H W q α μ v)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < 1) (hlo1 : lo ≤ 1)
    {A : Set ℝ} {rep : ℝ → BddMeas}
    (hmem : ∀ a ∈ A, ∀ y, (rep a) y ∈ Set.Icc lo hi)
    (hval : ∀ a ∈ A, rowFunctionalE H W q α μ (rep a) = cval)
    (hfixA : ∀ a ∈ A, rep a = BddMeas.sigma (elArg H W q α μ (rep a, 0)))
    (hmeanA : ∀ a ∈ A, BddMeas.integ (rep a) = a)
    {L : ℝ} (hL0 : 0 ≤ L) (hlip : ∀ a ∈ A, ∀ a' ∈ A, ‖rep a - rep a'‖ ≤ L * |a - a'|)
    {a₀ : ℝ} (ha₀ : a₀ ∈ A) (hacc : AccPt a₀ (𝓟 A)) :
    ∃ ε > 0, ∀ a ∈ Set.Ioo (a₀ - ε) (a₀ + ε), ∃ u : BddMeas,
      (∀ y, u y ∈ Set.Icc (0:ℝ) 1) ∧ rowFunctionalE H W q α μ u = cval
        ∧ BddMeas.integ u = a := by
  classical
  set u₀ : BddMeas := rep a₀ with hu₀
  have hu₀mem : ∀ y, u₀ y ∈ Set.Icc lo hi := hmem a₀ ha₀
  have hu₀fix : u₀ = BddMeas.sigma (elArg H W q α μ (u₀, 0)) := hfixA a₀ ha₀
  have hu₀mean : BddMeas.integ u₀ = a₀ := hmeanA a₀ ha₀
  have hEL : ∀ y, 2 * Jp' q (u₀ y) - 2 * α = μ * gradE H W u₀ y := el_of_fix hq0 hq1 hu₀fix
  have hmin : ∀ v : BddMeas, (∀ y, v y ∈ Set.Icc (0:ℝ) 1) →
      rowFunctionalE H W q α μ u₀ ≤ rowFunctionalE H W q α μ v := by
    intro v hv
    rw [hval a₀ ha₀]
    exact hlow v hv
  -- the implicit function theorem at `(u₀, 0)`
  have hF0 : elMap H W q α μ (u₀, 0) a₀ = 0 := by
    have h1 : u₀ - BddMeas.sigma (elArg H W q α μ (u₀, 0)) = 0 := by rw [← hu₀fix, sub_self]
    have h2 : BddMeas.integ u₀ - a₀ = 0 := by rw [hu₀mean, sub_self]
    rw [elMap, h1, h2]
    rfl
  have hjoint : AnalyticAt ℝ (fun w : (BddMeas × ℝ) × ℝ => elMap H W q α μ w.1 w.2)
      ((u₀, 0), a₀) := analyticAt_elMap _
  have hfd := hasFDerivAt_elMap (H := H) (W := W) (q := q) (α := α) (μ := μ) a₀ hu₀fix
  have hstrict : HasStrictFDerivAt (fun z : BddMeas × ℝ => elMap H W q α μ z a₀)
      ((borderedEquiv H W μ hΔ hq0 hq1 hμ hω0 hω1 hWω hlo hhi hlo1 hu₀mem hmin hEL :
        (BddMeas × ℝ) →L[ℝ] (BddMeas × ℝ))) (u₀, 0) := by
    have han : AnalyticAt ℝ (fun z : BddMeas × ℝ => elMap H W q α μ z a₀) (u₀, 0) := by
      have hmap : AnalyticAt ℝ (fun z : BddMeas × ℝ => (z, a₀)) (u₀, 0) :=
        analyticAt_id.prod analyticAt_const
      exact AnalyticAt.comp (g := fun w : (BddMeas × ℝ) × ℝ => elMap H W q α μ w.1 w.2)
        (f := fun z : BddMeas × ℝ => (z, a₀)) hjoint hmap
    have hs := han.hasStrictFDerivAt
    rw [hfd.fderiv] at hs
    rw [coe_borderedEquiv]
    exact hs
  obtain ⟨S, T, zbr, hSopen, hzS, hTopen, ha₀T, hz0, hzan, hzSmem, hzsol, huniq⟩ :=
    analytic_implicit_unique hjoint hF0 _ hstrict
  -- the multiplier along the branch
  set lam : ℝ → ℝ := fun a => (zbr a).2 with hlamdef
  set ub : ℝ → BddMeas := fun a => (zbr a).1 with hubdef
  have hlaman : AnalyticAt ℝ lam a₀ := analyticAt_snd.comp hzan
  have huban : AnalyticAt ℝ ub a₀ := analyticAt_fst.comp hzan
  -- the multiplier vanishes at nearby means of minimizers
  obtain ⟨ρ, hρ, hρS⟩ := Metric.isOpen_iff.mp hSopen (u₀, 0) hzS
  obtain ⟨δ₁, hδ₁, hδ₁T⟩ := Metric.isOpen_iff.mp hTopen a₀ ha₀T
  set δ : ℝ := min δ₁ (ρ / (L + 1)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ (by positivity)
  have hvanish : ∀ a ∈ A, |a - a₀| < δ → lam a = 0 := by
    intro a haA hadist
    have haT : a ∈ T := hδ₁T (by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hadist.trans_le (min_le_left _ _))
    have hrepS : (rep a, (0:ℝ)) ∈ S := by
      refine hρS ?_
      rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, norm_zero]
      have h1 : ‖rep a - u₀‖ ≤ L * |a - a₀| := hlip a haA a₀ ha₀
      have h2 : L * |a - a₀| < ρ := by
        have hd2 : |a - a₀| < ρ / (L + 1) := hadist.trans_le (min_le_right _ _)
        have : L * |a - a₀| ≤ (L + 1) * |a - a₀| := by nlinarith [abs_nonneg (a - a₀)]
        calc L * |a - a₀| ≤ (L + 1) * |a - a₀| := this
          _ < (L + 1) * (ρ / (L + 1)) := by
              refine mul_lt_mul_of_pos_left hd2 (by positivity)
          _ = ρ := by field_simp
      exact lt_of_le_of_lt (le_trans (le_of_eq (by
        simp only [max_eq_left (norm_nonneg _)])) h1) h2
    have hsol : elMap H W q α μ (rep a, 0) a = 0 := by
      have h1 : rep a - BddMeas.sigma (elArg H W q α μ (rep a, 0)) = 0 := by
        rw [← hfixA a haA, sub_self]
      have h2 : BddMeas.integ (rep a) - a = 0 := by rw [hmeanA a haA, sub_self]
      rw [elMap, h1, h2]
      rfl
    have := huniq a haT (rep a, (0:ℝ)) hrepS hsol
    rw [hlamdef]
    simp only
    rw [← this]
  -- hence `λ` vanishes frequently near `a₀`
  have hfreq : ∃ᶠ a in 𝓝[≠] a₀, lam a = 0 := by
    have hev : ∀ᶠ a in 𝓝[≠] a₀ ⊓ 𝓟 A, lam a = 0 := by
      have h1 : ∀ᶠ a in 𝓝[≠] a₀, |a - a₀| < δ := by
        have : ∀ᶠ a in 𝓝 a₀, |a - a₀| < δ := by
          have := Metric.ball_mem_nhds a₀ hδpos
          filter_upwards [this] with a ha
          rwa [Metric.mem_ball, Real.dist_eq] at ha
        exact this.filter_mono nhdsWithin_le_nhds
      have h2 : ∀ᶠ a in 𝓟 A, a ∈ A := Filter.eventually_principal.mpr fun a ha => ha
      filter_upwards [h1.filter_mono inf_le_left, h2.filter_mono inf_le_right] with a ha1 ha2
      exact hvanish a ha2 ha1
    have : (𝓝[≠] a₀ ⊓ 𝓟 A).NeBot := hacc
    exact (hev.frequently).filter_mono inf_le_left
  -- the multiplier vanishes identically near `a₀`
  obtain ⟨r₁, hr₁, hr₁an⟩ : ∃ r > 0, ∀ a, dist a a₀ < r → AnalyticAt ℝ lam a :=
    Metric.eventually_nhds_iff.mp hlaman.eventually_analyticAt
  have hlamOn : AnalyticOnNhd ℝ lam (Metric.ball a₀ r₁) := fun a ha => hr₁an a (by
    rwa [Metric.mem_ball] at ha)
  have hlamzero : Set.EqOn lam 0 (Metric.ball a₀ r₁) :=
    hlamOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball a₀ r₁).isPreconnected (Metric.mem_ball_self hr₁) hfreq
  -- the branch is analytic and stays close to `u₀`
  obtain ⟨r₂, hr₂, hr₂an⟩ : ∃ r > 0, ∀ a, dist a a₀ < r → AnalyticAt ℝ ub a :=
    Metric.eventually_nhds_iff.mp huban.eventually_analyticAt
  have hub0 : ub a₀ = u₀ := by
    rw [hubdef]
    simp only
    rw [hz0]
  set ρ₀ : ℝ := min lo (1 - hi) / 2 with hρ₀def
  have hρ₀ : 0 < ρ₀ := by
    rw [hρ₀def]
    exact half_pos (lt_min hlo (by linarith))
  have hρ₀lo : ρ₀ ≤ lo / 2 := by
    rw [hρ₀def]
    have := min_le_left lo (1 - hi)
    linarith
  have hρ₀hi : ρ₀ ≤ (1 - hi) / 2 := by
    rw [hρ₀def]
    have := min_le_right lo (1 - hi)
    linarith
  obtain ⟨r₃, hr₃, hr₃close⟩ : ∃ r > 0, ∀ a, dist a a₀ < r → ‖ub a - u₀‖ < ρ₀ := by
    have hcont : ContinuousAt ub a₀ := huban.continuousAt
    have hev : ∀ᶠ a in 𝓝 a₀, ‖ub a - u₀‖ < ρ₀ := by
      have hmem := hcont (Metric.ball_mem_nhds (ub a₀) hρ₀)
      filter_upwards [hmem] with a ha
      have ha' : ub a ∈ Metric.ball (ub a₀) ρ₀ := ha
      rw [Metric.mem_ball, dist_eq_norm, hub0] at ha'
      exact ha'
    exact Metric.eventually_nhds_iff.mp hev
  set ε : ℝ := min (min r₁ r₂) (min r₃ δ₁) with hεdef
  have hε : 0 < ε := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hδ₁)
  -- properties of the branch on the ball of radius `ε`
  have hball : ∀ a, |a - a₀| < ε → (zbr a = (ub a, 0) ∧ a ∈ T) := by
    intro a ha
    have hdist : dist a a₀ < ε := by rwa [Real.dist_eq]
    have haT : a ∈ T := hδ₁T (by
      rw [Metric.mem_ball]
      exact hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨?_, haT⟩
    have hlam0 : lam a = 0 := by
      have : a ∈ Metric.ball a₀ r₁ := by
        rw [Metric.mem_ball]
        exact hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      simpa using hlamzero this
    refine Prod.ext rfl ?_
    exact hlam0
  have hfixb : ∀ a, |a - a₀| < ε →
      ub a = BddMeas.sigma (elArg H W q α μ (ub a, 0)) ∧ BddMeas.integ (ub a) = a := by
    intro a ha
    obtain ⟨hz, haT⟩ := hball a ha
    have hsol := hzsol a haT
    rw [hz] at hsol
    have h1 : (elMap H W q α μ (ub a, 0) a).1 = 0 := by rw [hsol]; rfl
    have h2 : (elMap H W q α μ (ub a, 0) a).2 = 0 := by rw [hsol]; rfl
    rw [elMap] at h1 h2
    simp only at h1 h2
    exact ⟨by rw [← sub_eq_zero]; exact h1, by rw [← sub_eq_zero]; exact h2⟩
  have hmemb : ∀ a, |a - a₀| < ε → ∀ y, ub a y ∈ Set.Icc (lo - ρ₀) (hi + ρ₀) := by
    intro a ha y
    have hdist : dist a a₀ < ε := by rwa [Real.dist_eq]
    have hclose : ‖ub a - u₀‖ < ρ₀ :=
      hr₃close a (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hpt : |ub a y - u₀ y| ≤ ‖ub a - u₀‖ := BddMeas.abs_apply_sub_le_dist _ _ y
    have h1 := (hu₀mem y).1
    have h2 := (hu₀mem y).2
    have h3 := abs_le.mp (hpt.trans hclose.le)
    exact ⟨by linarith [h3.1], by linarith [h3.2]⟩


  -- the row functional is constant along the branch
  have hderiv : ∀ a, |a - a₀| < ε →
      HasDerivAt (fun a => rowFunctionalE H W q α μ (ub a)) 0 a := by
    intro a ha
    have hdist : dist a a₀ < ε := by rwa [Real.dist_eq]
    have hana : AnalyticAt ℝ ub a :=
      hr₂an a (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    have hdiff : HasDerivAt ub (deriv ub a) a := hana.differentiableAt.hasDerivAt
    obtain ⟨hfixa, -⟩ := hfixb a ha
    have hELa := el_of_fix hq0 hq1 hfixa
    have hg : ∀ y, (0 : BddMeas) y = 2 * Jp' q (ub a y) - 2 * α - μ * gradE H W (ub a) y := by
      intro y
      rw [BddMeas.zero_apply]
      have := hELa y
      linarith
    have hFd := hasFDerivAt_rowFunctionalE (H := H) (W := W) (α := α) (μ := μ) hq0 hq1
      (show (0:ℝ) < lo - ρ₀ by linarith) (show hi + ρ₀ < 1 by linarith) (hmemb a ha) hg
    have hzeroCLM : BddMeas.integ.comp (BddMeas.mulLeftCLM (0 : BddMeas)) = 0 := by
      refine ContinuousLinearMap.ext fun k => ?_
      simp only [ContinuousLinearMap.comp_apply, BddMeas.mulLeftCLM_apply, zero_mul,
        map_zero, _root_.zero_apply]
    rw [hzeroCLM] at hFd
    have hcomp := hFd.comp_hasDerivAt a hdiff
    exact hcomp
  have hconst : ∀ a, |a - a₀| < ε → rowFunctionalE H W q α μ (ub a) = cval := by
    intro a ha
    have hmemball : a ∈ Metric.ball a₀ ε := by rwa [Metric.mem_ball, Real.dist_eq]
    have hdiffOn : DifferentiableOn ℝ (fun a => rowFunctionalE H W q α μ (ub a))
        (Metric.ball a₀ ε) := by
      intro x hx
      have hx' : |x - a₀| < ε := by rwa [Metric.mem_ball, Real.dist_eq] at hx
      exact ((hderiv x hx').differentiableAt).differentiableWithinAt
    have hfd0 : ∀ x ∈ Metric.ball a₀ ε,
        fderivWithin ℝ (fun a => rowFunctionalE H W q α μ (ub a)) (Metric.ball a₀ ε) x = 0 := by
      intro x hx
      have hx' : |x - a₀| < ε := by rwa [Metric.mem_ball, Real.dist_eq] at hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx, (hderiv x hx').hasFDerivAt.fderiv]
      refine ContinuousLinearMap.ext fun t => ?_
      simp
    have hcc := (convex_ball a₀ ε).is_const_of_fderivWithin_eq_zero hdiffOn hfd0 hmemball
      (Metric.mem_ball_self hε)
    rw [hcc, hub0, hval a₀ ha₀]
  refine ⟨ε, hε, fun a ha => ⟨ub a, ?_, ?_, ?_⟩⟩
  · have habs : |a - a₀| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
    exact fun y => fix_mem_Icc (hfixb a habs).1 y
  · have habs : |a - a₀| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
    exact hconst a habs
  · have habs : |a - a₀| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
    exact (hfixb a habs).2


end UpperTailMultipodality
