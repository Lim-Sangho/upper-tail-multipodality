import UpperTailMultipodality.FixedDensities.DegenerateInsertion
import UpperTailMultipodality.FixedDensities.Support.Ordered

/-!
# Second variations of the rooted density, and the window of an ordered graphon

Ingredients for `lem:ordered-nondegenerate`:

* `exists_deriv_const_on_interior` — the second assertion of `lem:degenerate-forms`, in the form
  needed here: if `W` violates the constraint qualification and some `Ω_η(W)` has positive
  measure, then `𝒟_W` is almost everywhere constant on `Ω = {0 < W < 1}`.  It is the exhaustion
  argument `Ω = ⋃_η Ω_η(W)` inside the proof of `lem:degenerate-forms`, applied without assuming
  that `Ω` has full measure;
* `prod_add_two_sided_nonneg`, `prod_add_two_sided_le` — the even part of a product of affine
  functions of one parameter is nonnegative and dominates its quadratic term;
* `rooted_two_sided` — the resulting lower bound for the second difference
  `ℛ_W(u + th) + ℛ_W(u - th) - 2ℛ_W(u)`, which is `D²ℛ_W(u)[h,h]` up to the factor `t²`;
* `exists_mem_of_measure_ne_zero'` — a set of positive measure meets every full-measure set.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set of positive measure meets every set of full measure. -/
theorem exists_mem_of_measure_ne_zero' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : Set α} (h : μ A ≠ 0) {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) : ∃ x ∈ A, p x := by
  by_contra hc
  have hnot : ∀ x ∈ A, ¬ p x := fun x hx hpx => hc ⟨x, hx, hpx⟩
  have hae : ∀ᵐ x ∂μ, x ∉ A := by
    filter_upwards [hp] with x hx hxA
    exact hnot x hxA hx
  exact h (by simpa [ae_iff] using hae)

/-! ### The derivative kernel is constant on the interior -/

/-- **`lem:degenerate-forms`, the constant on `Ω`.**  If `W` violates the constraint
qualification and one window `Ω_{η₀}(W)` has positive measure, then `𝒟_W` is almost everywhere
constant on `{0 < W < 1}`. -/
theorem exists_deriv_const_on_interior (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    (hdeg : ¬ ConstraintQualification H W) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hpos : gμ {z : ℝ × ℝ | η₀ < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η₀} ≠ 0) :
    ∃ a : ℝ, ∀ᵐ z ∂gμ, 0 < W.toFun z.1 z.2 → W.toFun z.1 z.2 < 1 →
      derivKernel H W z.1 z.2 = a := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (ℝ × ℝ), ∀ n : ℕ, A n =
      {z : ℝ × ℝ | 1 / ((n : ℝ) + 2) < W.toFun z.1 z.2 ∧
        W.toFun z.1 z.2 < 1 - 1 / ((n : ℝ) + 2)} := ⟨_, fun n => rfl⟩
  have hηpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hle2 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hmono : ∀ m n : ℕ, m ≤ n → A m ⊆ A n := by
    intro m n hmn z hz
    rw [hA m] at hz
    rw [hA n]
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have h : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    exact ⟨lt_of_le_of_lt h hz.1, lt_of_lt_of_le hz.2 (by linarith)⟩
  -- one window has positive measure
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, gμ (A n₀) ≠ 0 := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hη₀
    refine ⟨n₀, fun hzero => hpos (measure_mono_null (fun z hz => ?_) hzero)⟩
    have hz' : η₀ < W.toFun z.1 z.2 ∧ W.toFun z.1 z.2 < 1 - η₀ := hz
    have hlt : 1 / ((n₀ : ℝ) + 2) < η₀ := lt_of_le_of_lt (hle2 n₀) hn₀
    rw [hA n₀]
    exact ⟨lt_trans hlt hz'.1, by linarith [hz'.2]⟩
  obtain ⟨c, hc⟩ := ae_const_on_of_not_cq H W hdeg (hηpos n₀) (by rw [← hA n₀]; exact hn₀)
  have hcA : ∀ᵐ z ∂gμ, z ∈ A n₀ → derivKernel H W z.1 z.2 = c := by
    filter_upwards [hc] with z hz hzA
    rw [hA n₀] at hzA
    exact hz hzA.1 hzA.2
  -- the constant does not depend on the window
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂gμ, z ∈ A n → derivKernel H W z.1 z.2 = c := by
    intro n
    by_cases hAn : gμ (A n) = 0
    · have hout : ∀ᵐ z ∂gμ, z ∉ A n := by simpa [ae_iff] using hAn
      filter_upwards [hout] with z hz hzA
      exact absurd hzA hz
    · have hsub : A n₀ ⊆ A (max n n₀) := hmono _ _ (le_max_right n n₀)
      have hposm : gμ (A (max n n₀)) ≠ 0 := fun h =>
        hn₀ (nonpos_iff_eq_zero.mp (h ▸ measure_mono hsub))
      obtain ⟨c', hc'⟩ := ae_const_on_of_not_cq H W hdeg (hηpos (max n n₀))
        (by rw [← hA (max n n₀)]; exact hposm)
      have hc'A : ∀ᵐ z ∂gμ, z ∈ A (max n n₀) → derivKernel H W z.1 z.2 = c' := by
        filter_upwards [hc'] with z hz hzA
        rw [hA (max n n₀)] at hzA
        exact hz hzA.1 hzA.2
      have hboth : ∀ᵐ z ∂gμ, z ∈ A n₀ →
          derivKernel H W z.1 z.2 = c ∧ derivKernel H W z.1 z.2 = c' := by
        filter_upwards [hcA, hc'A] with z h1 h2 hzA
        exact ⟨h1 hzA, h2 (hsub hzA)⟩
      have hcc' : c = c' := by
        obtain ⟨z, -, hz⟩ := exists_mem_of_measure_ne_zero hn₀ hboth
        rw [← hz.1, hz.2]
      filter_upwards [hc'A] with z hz hzA
      rw [hz (hmono _ _ (le_max_left n n₀) hzA), hcc']
  refine ⟨c, ?_⟩
  filter_upwards [ae_all_iff.mpr hstep] with z h1 hz0 hz1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt
    (show 0 < min (W.toFun z.1 z.2) (1 - W.toFun z.1 z.2) from lt_min hz0 (by linarith))
  refine h1 n ?_
  rw [hA n]
  refine ⟨lt_of_le_of_lt (hle2 n) (lt_of_lt_of_le hn (min_le_left _ _)), ?_⟩
  have := lt_of_le_of_lt (hle2 n) (lt_of_lt_of_le hn (min_le_right _ _))
  linarith

/-! ### The even part of a product of affine functions -/

section Products

variable {ι : Type*} [DecidableEq ι] (T : Finset ι) (u h : ι → ℝ)

/-- The expansion `∏ (u + r h) = ∑_S r^{|S|} (∏_S h)(∏_{T∖S} u)`. -/
theorem prod_add_expand (r : ℝ) :
    ∏ i ∈ T, (u i + r * h i)
      = ∑ S ∈ T.powerset, r ^ S.card * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i) := by
  have h1 : ∏ i ∈ T, (u i + r * h i) = ∏ i ∈ T, (r * h i + u i) :=
    Finset.prod_congr rfl fun i _ => add_comm _ _
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- The even part of `r ↦ ∏ (u + r h)` as a sum over nonempty subsets. -/
theorem prod_add_two_sided_eq (t : ℝ) :
    (∏ i ∈ T, (u i + t * h i)) + (∏ i ∈ T, (u i + (-t) * h i)) - 2 * ∏ i ∈ T, u i
      = ∑ S ∈ T.powerset.erase ∅,
          (t ^ S.card + (-t) ^ S.card) * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i) := by
  obtain ⟨c, hcdef⟩ : ∃ c : Finset ι → ℝ, c = fun S =>
      (t ^ S.card + (-t) ^ S.card) * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i) := ⟨_, rfl⟩
  have hone : ∑ S ∈ T.powerset, c S
      = (∏ i ∈ T, (u i + t * h i)) + ∏ i ∈ T, (u i + (-t) * h i) := by
    rw [prod_add_expand T u h t, prod_add_expand T u h (-t), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => by rw [hcdef]; ring
  have hcempty : c ∅ = 2 * ∏ i ∈ T, u i := by
    rw [hcdef]
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, Finset.sdiff_empty, one_mul]
    ring
  have hpeel := Finset.sum_erase_add T.powerset c (Finset.empty_mem_powerset T)
  rw [← hcdef]
  linarith

/-- The terms of the expansion are nonnegative. -/
theorem prod_add_two_sided_term_nonneg (hu : ∀ i, 0 ≤ u i) (hh : ∀ i, 0 ≤ h i) (t : ℝ)
    (S : Finset ι) :
    0 ≤ (t ^ S.card + (-t) ^ S.card) * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i) := by
  refine mul_nonneg ?_ (mul_nonneg (Finset.prod_nonneg fun i _ => hh i)
    (Finset.prod_nonneg fun i _ => hu i))
  rcases Nat.even_or_odd S.card with he | ho
  · rw [he.neg_pow t]
    linarith [he.pow_nonneg t]
  · rw [ho.neg_pow t]
    linarith

/-- **The even part of a product of affine functions is nonnegative.** -/
theorem prod_add_two_sided_nonneg (hu : ∀ i, 0 ≤ u i) (hh : ∀ i, 0 ≤ h i) (t : ℝ) :
    0 ≤ (∏ i ∈ T, (u i + t * h i)) + (∏ i ∈ T, (u i + (-t) * h i)) - 2 * ∏ i ∈ T, u i := by
  rw [prod_add_two_sided_eq T u h t]
  exact Finset.sum_nonneg fun S _ => prod_add_two_sided_term_nonneg T u h hu hh t S

/-- **The even part dominates its quadratic term.** -/
theorem prod_add_two_sided_le (hu : ∀ i, 0 ≤ u i) (hh : ∀ i, 0 ≤ h i) (t : ℝ) {S : Finset ι}
    (hST : S ⊆ T) (hS : S.card = 2) :
    2 * t ^ 2 * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i)
      ≤ (∏ i ∈ T, (u i + t * h i)) + (∏ i ∈ T, (u i + (-t) * h i)) - 2 * ∏ i ∈ T, u i := by
  have hmem : S ∈ T.powerset.erase ∅ := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr hST⟩
    intro hc
    rw [hc, Finset.card_empty] at hS
    exact absurd hS (by norm_num)
  have hterm : (t ^ S.card + (-t) ^ S.card) * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i)
      = 2 * t ^ 2 * ((∏ i ∈ S, h i) * ∏ i ∈ T \ S, u i) := by
    rw [hS]; ring
  rw [prod_add_two_sided_eq T u h t, ← hterm]
  exact Finset.single_le_sum (fun S' _ => prod_add_two_sided_term_nonneg T u h hu hh t S') hmem

end Products

/-! ### The second difference of the rooted density -/

/-- The integrand of `rootedDensity` is bounded and measurable. -/
theorem isBddMeas_rootedIntegrand (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {w : ℝ → ℝ} (hw : IsRow w) (v : V) :
    IsBddMeas fun ξ : V → ℝ =>
      (∏ z ∈ H.neighborFinset v, w (ξ z)) * avoidingProduct H W v ξ :=
  (IsBddMeas.finset_prod _ fun z _ =>
    (IsBddMeas.of_mem_Icc hw.1 hw.2).comp (measurable_pi_apply z)).mul
      (isBddMeas_avoidingProduct H W v)

/-- **The second difference of `ℛ_W` dominates its quadratic term.**  For rows `u` and `h ≥ 0`
with `u ± th` again rows, the even second difference of `ℛ_W` at `u` in the direction `h` is at
least the contribution of one ordered pair of distinct neighbours of one vertex. -/
theorem rooted_two_sided (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon)
    {u h ut um : ℝ → ℝ} (hu : IsRow u) (hh : IsRow h) (hut : IsRow ut) (hum : IsRow um)
    {t : ℝ} (hutv : ∀ y, ut y = u y + t * h y) (humv : ∀ y, um y = u y + (-t) * h y)
    (v₀ : V) {z₁ z₂ : V} (hz₁ : z₁ ∈ H.neighborFinset v₀) (hz₂ : z₂ ∈ H.neighborFinset v₀)
    (hne : z₁ ≠ z₂) :
    (∫ ξ : V → ℝ, 2 * t ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), h (ξ z))
          * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z))
        * avoidingProduct H W v₀ ξ ∂(Measure.pi fun _ : V => unitμ))
      ≤ totalRootedDensity H W ut + totalRootedDensity H W um
        - 2 * totalRootedDensity H W u := by
  obtain ⟨F, hFdef⟩ : ∃ F : (ℝ → ℝ) → V → (V → ℝ) → ℝ, F = fun w v ξ =>
      (∏ z ∈ H.neighborFinset v, w (ξ z)) * avoidingProduct H W v ξ := ⟨_, rfl⟩
  have hFval : ∀ (w : ℝ → ℝ) (v : V) (ξ : V → ℝ),
      F w v ξ = (∏ z ∈ H.neighborFinset v, w (ξ z)) * avoidingProduct H W v ξ := by
    intro w v ξ; rw [hFdef]
  have hrd : ∀ (w : ℝ → ℝ) (v : V),
      rootedDensity H W v w = ∫ ξ, F w v ξ ∂(Measure.pi fun _ : V => unitμ) := by
    intro w v; rw [hFdef]; rfl
  have hFint : ∀ (w : ℝ → ℝ), IsRow w → ∀ v : V,
      Integrable (F w v) (Measure.pi fun _ : V => unitμ) := by
    intro w hw v
    have hb := isBddMeas_rootedIntegrand H W hw v
    refine (hb.integrable).congr ?_
    exact Eventually.of_forall fun ξ => (hFval w v ξ).symm
  -- the pointwise inequalities
  have hptnn : ∀ (v : V) (ξ : V → ℝ), 2 * F u v ξ ≤ F ut v ξ + F um v ξ := by
    intro v ξ
    have hprod := prod_add_two_sided_nonneg (H.neighborFinset v)
      (fun z => u (ξ z)) (fun z => h (ξ z)) (fun z => (hu.2 (ξ z)).1)
      (fun z => (hh.2 (ξ z)).1) t
    have hA := avoidingProduct_mem_Icc H W v ξ
    have hut' : (∏ z ∈ H.neighborFinset v, ut (ξ z))
        = ∏ z ∈ H.neighborFinset v, (u (ξ z) + t * h (ξ z)) :=
      Finset.prod_congr rfl fun z _ => hutv (ξ z)
    have hum' : (∏ z ∈ H.neighborFinset v, um (ξ z))
        = ∏ z ∈ H.neighborFinset v, (u (ξ z) + (-t) * h (ξ z)) :=
      Finset.prod_congr rfl fun z _ => humv (ξ z)
    rw [hFval, hFval, hFval, hut', hum']
    nlinarith [hA.1]
  have hptv₀ : ∀ ξ : V → ℝ,
      2 * t ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), h (ξ z))
          * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z)) * avoidingProduct H W v₀ ξ
        + 2 * F u v₀ ξ ≤ F ut v₀ ξ + F um v₀ ξ := by
    intro ξ
    have hSsub : ({z₁, z₂} : Finset V) ⊆ H.neighborFinset v₀ := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hz₁
      · rw [Finset.mem_singleton] at hz'; subst hz'; exact hz₂
    have hScard : ({z₁, z₂} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
    have hprod := prod_add_two_sided_le (H.neighborFinset v₀)
      (fun z => u (ξ z)) (fun z => h (ξ z)) (fun z => (hu.2 (ξ z)).1)
      (fun z => (hh.2 (ξ z)).1) t hSsub hScard
    have hA := avoidingProduct_mem_Icc H W v₀ ξ
    have hut' : (∏ z ∈ H.neighborFinset v₀, ut (ξ z))
        = ∏ z ∈ H.neighborFinset v₀, (u (ξ z) + t * h (ξ z)) :=
      Finset.prod_congr rfl fun z _ => hutv (ξ z)
    have hum' : (∏ z ∈ H.neighborFinset v₀, um (ξ z))
        = ∏ z ∈ H.neighborFinset v₀, (u (ξ z) + (-t) * h (ξ z)) :=
      Finset.prod_congr rfl fun z _ => humv (ξ z)
    rw [hFval, hFval, hFval, hut', hum']
    nlinarith [hA.1]
  -- integrate
  have hGint : Integrable (fun ξ : V → ℝ =>
      2 * t ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), h (ξ z))
          * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z)) * avoidingProduct H W v₀ ξ)
      (Measure.pi fun _ : V => unitμ) := by
    refine IsBddMeas.integrable ?_
    refine (((IsBddMeas.const (2 * t ^ 2)).mul
      (((IsBddMeas.finset_prod _ fun z _ =>
          (IsBddMeas.of_mem_Icc hh.1 hh.2).comp (measurable_pi_apply z))).mul
        ((IsBddMeas.finset_prod _ fun z _ =>
          (IsBddMeas.of_mem_Icc hu.1 hu.2).comp (measurable_pi_apply z))))).mul
      (isBddMeas_avoidingProduct H W v₀))
  have hv : ∀ v : V, 0 ≤ (∫ ξ, F ut v ξ ∂(Measure.pi fun _ : V => unitμ))
      + (∫ ξ, F um v ξ ∂(Measure.pi fun _ : V => unitμ))
      - 2 * ∫ ξ, F u v ξ ∂(Measure.pi fun _ : V => unitμ) := by
    intro v
    have him : Integrable (fun ξ : V → ℝ => 2 * F u v ξ) (Measure.pi fun _ : V => unitμ) :=
      (hFint u hu v).const_mul 2
    have hiadd : Integrable (fun ξ : V → ℝ => F ut v ξ + F um v ξ)
        (Measure.pi fun _ : V => unitμ) := (hFint ut hut v).add (hFint um hum v)
    have hm := integral_mono him hiadd (hptnn v)
    rw [integral_const_mul, integral_add (hFint ut hut v) (hFint um hum v)] at hm
    linarith
  have hv₀ : (∫ ξ, 2 * t ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), h (ξ z))
          * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z))
        * avoidingProduct H W v₀ ξ ∂(Measure.pi fun _ : V => unitμ))
      ≤ (∫ ξ, F ut v₀ ξ ∂(Measure.pi fun _ : V => unitμ))
        + (∫ ξ, F um v₀ ξ ∂(Measure.pi fun _ : V => unitμ))
        - 2 * ∫ ξ, F u v₀ ξ ∂(Measure.pi fun _ : V => unitμ) := by
    have him : Integrable (fun ξ : V → ℝ => 2 * F u v₀ ξ) (Measure.pi fun _ : V => unitμ) :=
      (hFint u hu v₀).const_mul 2
    have hileft : Integrable (fun ξ : V → ℝ =>
        2 * t ^ 2 * ((∏ z ∈ ({z₁, z₂} : Finset V), h (ξ z))
            * ∏ z ∈ H.neighborFinset v₀ \ {z₁, z₂}, u (ξ z))
          * avoidingProduct H W v₀ ξ + 2 * F u v₀ ξ)
        (Measure.pi fun _ : V => unitμ) := hGint.add him
    have hiadd : Integrable (fun ξ : V → ℝ => F ut v₀ ξ + F um v₀ ξ)
        (Measure.pi fun _ : V => unitμ) := (hFint ut hut v₀).add (hFint um hum v₀)
    have hm := integral_mono hileft hiadd hptv₀
    rw [integral_add hGint him, integral_const_mul,
      integral_add (hFint ut hut v₀) (hFint um hum v₀)] at hm
    linarith
  have hsum : ∑ v : V, ((∫ ξ, F ut v ξ ∂(Measure.pi fun _ : V => unitμ))
        + (∫ ξ, F um v ξ ∂(Measure.pi fun _ : V => unitμ))
        - 2 * ∫ ξ, F u v ξ ∂(Measure.pi fun _ : V => unitμ))
      = totalRootedDensity H W ut + totalRootedDensity H W um
        - 2 * totalRootedDensity H W u := by
    unfold totalRootedDensity
    simp_rw [hrd]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hsum]
  exact hv₀.trans (Finset.single_le_sum (fun v _ => hv v) (Finset.mem_univ v₀))

end FixedDensities

end UpperTailMultipodality
