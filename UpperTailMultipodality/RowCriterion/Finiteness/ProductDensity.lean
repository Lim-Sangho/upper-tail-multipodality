import UpperTailMultipodality.Preliminaries.Graphons.Basic

/-!
# Approximation of kernels by finite sums of products

A bounded measurable function on a product `X × ℝ` of two finite measure spaces is approximated
in `L²` by finite sums `∑ᵢ aᵢ(x) bᵢ(y)` of products of bounded measurable functions
(`exists_isProdSimple_approx`).  This is the finite-rank approximation behind the compactness of
the integral operators of `isCompactOperator_kernelOp`, the Hilbert–Schmidt compactness used for
`lem:bordered`: it is proved by a π-λ argument on rectangles, followed by the approximation of a
bounded measurable function by simple functions.
-/

namespace UpperTailMultipodality

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- A finite sum of products `∑ᵢ aᵢ(x) bᵢ(y)` of bounded measurable functions. -/
def IsProdSimple (Ψ : X × ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → X → ℝ) (b : ι → ℝ → ℝ),
    (∀ i, Measurable (a i)) ∧ (∀ i, Measurable (b i)) ∧
      (∀ i, ∃ C, ∀ x, |a i x| ≤ C) ∧ (∀ i, ∃ C, ∀ y, |b i y| ≤ C) ∧
      ∀ p, Ψ p = ∑ i, a i p.1 * b i p.2

namespace IsProdSimple

/-- A finite sum of products is measurable. -/
theorem measurable {Ψ : X × ℝ → ℝ} (h : IsProdSimple Ψ) : Measurable Ψ := by
  obtain ⟨ι, _, a, b, ha, hb, -, -, hΨ⟩ := h
  have : Ψ = fun p => ∑ i, a i p.1 * b i p.2 := funext hΨ
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    ((ha i).comp measurable_fst).mul ((hb i).comp measurable_snd)

/-- A finite sum of products is bounded. -/
theorem exists_bound {Ψ : X × ℝ → ℝ} (h : IsProdSimple Ψ) : ∃ C, ∀ p, |Ψ p| ≤ C := by
  classical
  obtain ⟨ι, _, a, b, -, -, hab, hbb, hΨ⟩ := h
  choose Ca hCa using hab
  choose Cb hCb using hbb
  refine ⟨∑ i, |Ca i| * |Cb i|, fun p => ?_⟩
  rw [hΨ p]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul ((hCa i p.1).trans (le_abs_self _)) ((hCb i p.2).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- The zero function is a finite sum of products. -/
theorem zero : IsProdSimple (fun _ : X × ℝ => (0:ℝ)) :=
  ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim,
    fun i => i.elim, fun i => i.elim, fun p => by simp⟩

/-- The constant function `1` is a finite sum of products. -/
theorem one : IsProdSimple (fun _ : X × ℝ => (1:ℝ)) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 1, fun _ => measurable_const,
    fun _ => measurable_const, fun _ => ⟨1, fun _ => by norm_num⟩,
    fun _ => ⟨1, fun _ => by norm_num⟩, fun p => by simp⟩

/-- Finite sums of products are closed under addition. -/
theorem add {Ψ₁ Ψ₂ : X × ℝ → ℝ} (h₁ : IsProdSimple Ψ₁) (h₂ : IsProdSimple Ψ₂) :
    IsProdSimple (fun p => Ψ₁ p + Ψ₂ p) := by
  obtain ⟨ι₁, _, a₁, b₁, ha₁, hb₁, hab₁, hbb₁, hΨ₁⟩ := h₁
  obtain ⟨ι₂, _, a₂, b₂, ha₂, hb₂, hab₂, hbb₂, hΨ₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, ?_, ?_, ?_, ?_, fun p => ?_⟩
  · rintro (i | i) <;> simp [ha₁, ha₂]
  · rintro (i | i) <;> simp [hb₁, hb₂]
  · rintro (i | i) <;> simp [hab₁, hab₂]
  · rintro (i | i) <;> simp [hbb₁, hbb₂]
  · show Ψ₁ p + Ψ₂ p = _
    rw [Fintype.sum_sum_type, hΨ₁ p, hΨ₂ p]
    simp

/-- Finite sums of products are closed under scalar multiplication. -/
theorem smul {Ψ : X × ℝ → ℝ} (h : IsProdSimple Ψ) (c : ℝ) :
    IsProdSimple (fun p => c * Ψ p) := by
  obtain ⟨ι, _, a, b, ha, hb, hab, hbb, hΨ⟩ := h
  refine ⟨ι, inferInstance, fun i x => c * a i x, b, fun i => (ha i).const_mul c, hb, ?_, hbb,
    fun p => ?_⟩
  · intro i
    obtain ⟨C, hC⟩ := hab i
    exact ⟨|c| * C, fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩
  · show c * Ψ p = _
    rw [hΨ p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Finite sums of products are closed under subtraction. -/
theorem sub {Ψ₁ Ψ₂ : X × ℝ → ℝ} (h₁ : IsProdSimple Ψ₁) (h₂ : IsProdSimple Ψ₂) :
    IsProdSimple (fun p => Ψ₁ p - Ψ₂ p) := by
  have := h₁.add (h₂.smul (-1))
  simpa [sub_eq_add_neg] using this

/-- Finite sums of products are closed under finite sums. -/
theorem sum {n : ℕ} {Ψ : ℕ → X × ℝ → ℝ} (h : ∀ i, IsProdSimple (Ψ i)) :
    IsProdSimple (fun p => ∑ i ∈ Finset.range n, Ψ i p) := by
  induction n with
  | zero => simpa using zero
  | succ n ih =>
    have : (fun p => ∑ i ∈ Finset.range (n + 1), Ψ i p)
        = fun p => (∑ i ∈ Finset.range n, Ψ i p) + Ψ n p := by
      funext p; rw [Finset.sum_range_succ]
    rw [this]
    exact ih.add (h n)

/-- The indicator of a measurable rectangle is a product. -/
theorem indicator_prod {A : Set X} {B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IsProdSimple ((A ×ˢ B).indicator (fun _ => (1:ℝ))) := by
  refine ⟨Unit, inferInstance, fun _ x => A.indicator (fun _ => (1:ℝ)) x,
    fun _ y => B.indicator (fun _ => (1:ℝ)) y, fun _ => (measurable_indicator_const_iff 1).mpr hA,
    fun _ => (measurable_indicator_const_iff 1).mpr hB, fun _ => ⟨1, fun x => ?_⟩,
    fun _ => ⟨1, fun y => ?_⟩, fun p => ?_⟩
  · by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  · by_cases hy : y ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  · simp only [Finset.univ_unique, Finset.sum_singleton]
    by_cases hp : p ∈ A ×ˢ B
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2, one_mul]
    · rw [Set.indicator_of_notMem hp]
      rw [Set.mem_prod] at hp
      rcases not_and_or.mp hp with h | h
      · rw [Set.indicator_of_notMem h, zero_mul]
      · rw [Set.indicator_of_notMem h, mul_zero]

end IsProdSimple


/-- Bounded measurable functions on the product. -/
def IsBM (f : X × ℝ → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ p, |f p| ≤ C

namespace IsBM

/-- Bounded measurable functions are closed under subtraction. -/
theorem sub {f g : X × ℝ → ℝ} (hf : IsBM f) (hg : IsBM g) : IsBM (fun p => f p - g p) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.sub hgm, C + D, fun p => (abs_sub _ _).trans (add_le_add (hC p) (hD p))⟩

/-- Bounded measurable functions are closed under finite sums. -/
theorem sum {n : ℕ} {F : ℕ → X × ℝ → ℝ} (h : ∀ i, IsBM (F i)) :
    IsBM (fun p => ∑ i ∈ Finset.range n, F i p) := by
  classical
  induction n with
  | zero => exact ⟨measurable_const, 0, fun p => by simp⟩
  | succ n ih =>
    obtain ⟨hm, C, hC⟩ := ih
    obtain ⟨hm', C', hC'⟩ := h n
    refine ⟨?_, C + C', fun p => ?_⟩
    · have : (fun p : X × ℝ => ∑ i ∈ Finset.range (n + 1), F i p)
          = fun p => (∑ i ∈ Finset.range n, F i p) + F n p := by
        funext p; rw [Finset.sum_range_succ]
      rw [this]; exact hm.add hm'
    · show |∑ i ∈ Finset.range (n + 1), F i p| ≤ C + C'
      rw [Finset.sum_range_succ]
      exact (abs_add_le _ _).trans (add_le_add (hC p) (hC' p))

/-- Bounded measurable functions are closed under addition. -/
theorem add' {f g : X × ℝ → ℝ} (hf : IsBM f) (hg : IsBM g) : IsBM (fun p => f p + g p) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.add hgm, C + D, fun p => (abs_add_le _ _).trans (add_le_add (hC p) (hD p))⟩

/-- A finite sum of products is bounded and measurable. -/
theorem of_isProdSimple {Ψ : X × ℝ → ℝ} (h : IsProdSimple Ψ) : IsBM Ψ :=
  ⟨h.measurable, h.exists_bound⟩

/-- The indicator of a measurable set is bounded and measurable. -/
theorem indicator {S : Set (X × ℝ)} (hS : MeasurableSet S) :
    IsBM (S.indicator (fun _ => (1:ℝ))) :=
  ⟨(measurable_indicator_const_iff 1).mpr hS, 1, fun p => by
    by_cases hp : p ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hp]⟩

variable {ν : Measure X} [IsFiniteMeasure ν]

/-- The square of a bounded measurable function is integrable. -/
theorem integrable_sq {f : X × ℝ → ℝ} (hf : IsBM f) :
    Integrable (fun p => (f p) ^ 2) (ν.prod unitμ) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine integrable_of_abs_le (hm.pow_const 2) (C ^ 2) fun p => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC p) 2

omit [IsFiniteMeasure ν] in
/-- Integrals of squares are nonnegative. -/
theorem integral_sq_nonneg {f : X × ℝ → ℝ} :
    0 ≤ ∫ p, (f p) ^ 2 ∂(ν.prod unitμ) := integral_nonneg fun _ => sq_nonneg _

end IsBM

section Estimates

variable {ν : Measure X} [IsFiniteMeasure ν]

/-- `∫ (f - h)² ≤ 2∫ (f - g)² + 2∫ (g - h)²`. -/
theorem integral_sq_sub_le {f g h : X × ℝ → ℝ} (hf : IsBM f) (hg : IsBM g) (hh : IsBM h) :
    ∫ p, (f p - h p) ^ 2 ∂(ν.prod unitμ)
      ≤ 2 * ∫ p, (f p - g p) ^ 2 ∂(ν.prod unitμ) + 2 * ∫ p, (g p - h p) ^ 2 ∂(ν.prod unitμ) := by
  have h1 := (hf.sub hg).integrable_sq (ν := ν)
  have h2 := (hg.sub hh).integrable_sq (ν := ν)
  have h3 := (hf.sub hh).integrable_sq (ν := ν)
  calc ∫ p, (f p - h p) ^ 2 ∂(ν.prod unitμ)
      ≤ ∫ p, (2 * (f p - g p) ^ 2 + 2 * (g p - h p) ^ 2) ∂(ν.prod unitμ) := by
        refine integral_mono h3 ((h1.const_mul 2).add (h2.const_mul 2)) fun p => ?_
        nlinarith [sq_nonneg (f p - g p), sq_nonneg (g p - h p), sq_nonneg (f p - 2 * g p + h p)]
    _ = 2 * ∫ p, (f p - g p) ^ 2 ∂(ν.prod unitμ)
          + 2 * ∫ p, (g p - h p) ^ 2 ∂(ν.prod unitμ) := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul]

/-- `∫ (∑_{n<N} F n)² ≤ N ∑_{n<N} ∫ (F n)²`. -/
theorem integral_sq_sum_le {N : ℕ} {F : ℕ → X × ℝ → ℝ} (hF : ∀ n, IsBM (F n)) :
    ∫ p, (∑ n ∈ Finset.range N, F n p) ^ 2 ∂(ν.prod unitμ)
      ≤ N * ∑ n ∈ Finset.range N, ∫ p, (F n p) ^ 2 ∂(ν.prod unitμ) := by
  have hsum := IsBM.sum (n := N) hF
  calc ∫ p, (∑ n ∈ Finset.range N, F n p) ^ 2 ∂(ν.prod unitμ)
      ≤ ∫ p, (N : ℝ) * ∑ n ∈ Finset.range N, (F n p) ^ 2 ∂(ν.prod unitμ) := by
        refine integral_mono (hsum.integrable_sq (ν := ν))
          ((integrable_finsetSum _ fun n _ => (hF n).integrable_sq (ν := ν)).const_mul _)
          fun p => ?_
        have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => F n p)
        simpa using this
    _ = N * ∑ n ∈ Finset.range N, ∫ p, (F n p) ^ 2 ∂(ν.prod unitμ) := by
        rw [integral_const_mul, integral_finsetSum _ fun n _ => (hF n).integrable_sq (ν := ν)]

end Estimates

section Approx

variable {ν : Measure X} [IsFiniteMeasure ν]

/-- The square of the difference of two bounded functions is integrable. -/
theorem integrable_sq_sub {Φ Ψ : X × ℝ → ℝ} (hΦ : Measurable Φ) {C : ℝ} (hbΦ : ∀ p, |Φ p| ≤ C)
    (hΨ : Measurable Ψ) {D : ℝ} (hbΨ : ∀ p, |Ψ p| ≤ D) :
    Integrable (fun p => (Φ p - Ψ p) ^ 2) (ν.prod unitμ) := by
  refine integrable_of_abs_le ((hΦ.sub hΨ).pow_const 2) ((C + D) ^ 2) fun p => ?_
  rw [abs_pow]
  have h : |Φ p - Ψ p| ≤ C + D := (abs_sub _ _).trans (add_le_add (hbΦ p) (hbΨ p))
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The `L²` approximation property of a set by finite sums of products. -/
def ApproxBySimple (ν : Measure X) (S : Set (X × ℝ)) : Prop :=
  ∀ ε > 0, ∃ Ψ, IsProdSimple Ψ ∧
    ∫ p, (S.indicator (fun _ => (1:ℝ)) p - Ψ p) ^ 2 ∂(ν.prod unitμ) < ε

/-- Indicators of measurable sets are measurable. -/
theorem measurable_indicator_one {S : Set (X × ℝ)} (hS : MeasurableSet S) :
    Measurable (S.indicator (fun _ => (1:ℝ))) := (measurable_indicator_const_iff 1).mpr hS

omit [MeasurableSpace X] in
/-- Indicators are bounded by one. -/
theorem abs_indicator_one_le {S : Set (X × ℝ)} (p : X × ℝ) :
    |S.indicator (fun _ => (1:ℝ)) p| ≤ 1 := by
  by_cases hp : p ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hp]

/-- **Every measurable set of the product is approximated by finite sums of products.** -/
theorem approxBySimple_of_measurableSet {S : Set (X × ℝ)} (hS : MeasurableSet S) :
    ApproxBySimple ν S := by
  classical
  induction S, hS using MeasurableSpace.induction_on_inter
    (h_eq := (generateFrom_prod (α := X) (β := ℝ)).symm)
    (h_inter := isPiSystem_prod) with
  | empty =>
    intro ε hε
    refine ⟨fun _ => 0, IsProdSimple.zero, ?_⟩
    simp only [Set.indicator_empty]
    simpa using hε
  | basic t ht =>
    intro ε hε
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    refine ⟨(A ×ˢ B).indicator (fun _ => (1:ℝ)), IsProdSimple.indicator_prod hA hB, ?_⟩
    simp only [sub_self]
    simpa using hε
  | compl t htm ht =>
    intro ε hε
    obtain ⟨Ψ, hΨ, hΨε⟩ := ht ε hε
    refine ⟨fun p => 1 - Ψ p, IsProdSimple.one.sub hΨ, ?_⟩
    have hpt : ∀ p, (tᶜ.indicator (fun _ => (1:ℝ)) p - (1 - Ψ p)) ^ 2
        = (t.indicator (fun _ => (1:ℝ)) p - Ψ p) ^ 2 := by
      intro p
      by_cases hp : p ∈ t
      · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (by simpa using hp)]
        ring
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_mem (by simpa using hp)]
        ring
    rw [show (∫ p, (tᶜ.indicator (fun _ => (1:ℝ)) p - (1 - Ψ p)) ^ 2 ∂(ν.prod unitμ))
        = ∫ p, (t.indicator (fun _ => (1:ℝ)) p - Ψ p) ^ 2 ∂(ν.prod unitμ) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact hΨε
  | iUnion f hdisj hfm hf =>
    intro ε hε
    set T := ⋃ n, f n with hT
    set TN : ℕ → Set (X × ℝ) := fun N => ⋃ n ∈ Finset.range N, f n with hTN
    have hTNm : ∀ N, MeasurableSet (TN N) := fun N =>
      MeasurableSet.biUnion (Finset.range N).countable_toSet fun n _ => hfm n
    -- the tail error tends to zero
    have hconv : Filter.Tendsto
        (fun N => ∫ p, (T.indicator (fun _ => (1:ℝ)) p - (TN N).indicator (fun _ => (1:ℝ)) p) ^ 2
          ∂(ν.prod unitμ)) Filter.atTop (nhds 0) := by
      have hptwise : ∀ p, Filter.Tendsto
          (fun N => (T.indicator (fun _ => (1:ℝ)) p - (TN N).indicator (fun _ => (1:ℝ)) p) ^ 2)
          Filter.atTop (nhds 0) := by
        intro p
        by_cases hp : p ∈ T
        · obtain ⟨n, hn⟩ : ∃ n, p ∈ f n := by
            rw [hT, Set.mem_iUnion] at hp; exact hp
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [Filter.eventually_ge_atTop (n + 1)] with N hN
          have hpN : p ∈ TN N := by
            rw [hTN]
            exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hn
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpN]
          norm_num
        · have hpN : ∀ N, p ∉ TN N := by
            intro N hpN
            apply hp
            rw [hTN, Set.mem_iUnion₂] at hpN
            obtain ⟨n, -, hn⟩ := hpN
            rw [hT, Set.mem_iUnion]
            exact ⟨n, hn⟩
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards with N
          rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (hpN N)]
          norm_num
      have hdct := tendsto_integral_of_dominated_convergence (μ := ν.prod unitμ)
        (F := fun N p => (T.indicator (fun _ => (1:ℝ)) p
          - (TN N).indicator (fun _ => (1:ℝ)) p) ^ 2)
        (f := fun _ => (0:ℝ)) (bound := fun _ => (1:ℝ)) ?_ (integrable_const _) ?_ ?_
      · simpa using hdct
      · intro N
        exact (((measurable_indicator_one (MeasurableSet.iUnion hfm)).sub
          (measurable_indicator_one (hTNm N))).pow_const 2).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        have h1 := abs_indicator_one_le (S := T) p
        have h2 := abs_indicator_one_le (S := TN N) p
        have hle : |T.indicator (fun _ => (1:ℝ)) p - (TN N).indicator (fun _ => (1:ℝ)) p| ≤ 1 := by
          by_cases hp : p ∈ T
          · by_cases hpN : p ∈ TN N
            · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpN]; norm_num
            · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hpN]; norm_num
          · have hpN : p ∉ TN N := by
              intro hpN
              apply hp
              rw [hTN, Set.mem_iUnion₂] at hpN
              obtain ⟨n, -, hn⟩ := hpN
              rw [hT, Set.mem_iUnion]
              exact ⟨n, hn⟩
            rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hpN]; norm_num
        calc (T.indicator (fun _ => (1:ℝ)) p - (TN N).indicator (fun _ => (1:ℝ)) p) ^ 2
            = |T.indicator (fun _ => (1:ℝ)) p - (TN N).indicator (fun _ => (1:ℝ)) p| ^ 2 :=
              (sq_abs _).symm
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = 1 := one_pow 2
      · exact Filter.Eventually.of_forall hptwise
    obtain ⟨N, hN⟩ := ((hconv.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 4))).exists)
    -- approximate the finite union
    have hNpos : (0:ℝ) < (N + 1) ^ 2 := by positivity
    have hεN : (0:ℝ) < ε / (4 * (N + 1) ^ 2) := by positivity
    choose Ψ hΨ hΨε using fun n => hf n (ε / (4 * (N + 1) ^ 2)) hεN
    refine ⟨fun p => ∑ n ∈ Finset.range N, Ψ n p, IsProdSimple.sum (fun n => hΨ n), ?_⟩
    have hsum : ∀ p, (TN N).indicator (fun _ => (1:ℝ)) p
        = ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) p := by
      have hgen : ∀ M : ℕ, (⋃ n ∈ Finset.range M, f n).indicator (fun _ => (1:ℝ))
          = fun p => ∑ n ∈ Finset.range M, (f n).indicator (fun _ => (1:ℝ)) p := by
        intro M
        induction M with
        | zero => funext p; simp
        | succ M ih =>
          have hunion : (⋃ n ∈ Finset.range (M + 1), f n)
              = (⋃ n ∈ Finset.range M, f n) ∪ f M := by
            ext p
            simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
            constructor
            · rintro ⟨n, hn, hp⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
              · exact Or.inl ⟨n, h, hp⟩
              · exact Or.inr (h ▸ hp)
            · rintro (⟨n, hn, hp⟩ | hp)
              · exact ⟨n, by omega, hp⟩
              · exact ⟨M, by omega, hp⟩
          have hdisj' : Disjoint (⋃ n ∈ Finset.range M, f n) (f M) := by
            rw [Set.disjoint_iUnion₂_left]
            intro n hn
            exact hdisj (by simp only [Finset.mem_range] at hn; omega)
          funext p
          rw [hunion, Set.indicator_union_of_disjoint hdisj', ih, Finset.sum_range_succ]
      intro p
      rw [hTN]
      exact congrFun (hgen N) p
    have hBMT : IsBM (T.indicator (fun _ => (1:ℝ))) :=
      IsBM.indicator (MeasurableSet.iUnion hfm)
    have hBMTN : IsBM ((TN N).indicator (fun _ => (1:ℝ))) := IsBM.indicator (hTNm N)
    have hBMΨ : IsBM (fun p => ∑ n ∈ Finset.range N, Ψ n p) :=
      IsBM.of_isProdSimple (IsProdSimple.sum fun n => hΨ n)
    have hstep1 := integral_sq_sub_le (ν := ν) hBMT hBMTN hBMΨ
    have hstep2 : ∫ p, ((TN N).indicator (fun _ => (1:ℝ)) p
          - ∑ n ∈ Finset.range N, Ψ n p) ^ 2 ∂(ν.prod unitμ)
        ≤ N * ∑ n ∈ Finset.range N,
            ∫ p, ((f n).indicator (fun _ => (1:ℝ)) p - Ψ n p) ^ 2 ∂(ν.prod unitμ) := by
      have heq : (fun p => ((TN N).indicator (fun _ => (1:ℝ)) p
            - ∑ n ∈ Finset.range N, Ψ n p) ^ 2)
          = fun p => (∑ n ∈ Finset.range N,
            ((f n).indicator (fun _ => (1:ℝ)) p - Ψ n p)) ^ 2 := by
        funext p
        rw [hsum p, Finset.sum_sub_distrib]
      rw [heq]
      exact integral_sq_sum_le (ν := ν) fun n =>
        (IsBM.indicator (hfm n)).sub (IsBM.of_isProdSimple (hΨ n))
    have hstep3 : ∑ n ∈ Finset.range N,
        ∫ p, ((f n).indicator (fun _ => (1:ℝ)) p - Ψ n p) ^ 2 ∂(ν.prod unitμ)
          ≤ N * (ε / (4 * (N + 1) ^ 2)) := by
      calc ∑ n ∈ Finset.range N,
            ∫ p, ((f n).indicator (fun _ => (1:ℝ)) p - Ψ n p) ^ 2 ∂(ν.prod unitμ)
          ≤ ∑ _n ∈ Finset.range N, (ε / (4 * (N + 1) ^ 2)) :=
            Finset.sum_le_sum fun n _ => (hΨε n).le
        _ = N * (ε / (4 * (N + 1) ^ 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hNle : (N:ℝ) * ((N:ℝ) * (ε / (4 * ((N:ℝ) + 1) ^ 2))) ≤ ε / 4 := by
      have hpos : (0:ℝ) < 4 * ((N:ℝ) + 1) ^ 2 := by positivity
      have hexp : (N:ℝ) * ((N:ℝ) * (ε / (4 * ((N:ℝ) + 1) ^ 2)))
          = ((N:ℝ) * (N:ℝ) * ε) / (4 * ((N:ℝ) + 1) ^ 2) := by
        field_simp
      rw [hexp, div_le_iff₀ hpos]
      have h4 : ε / 4 * (4 * ((N:ℝ) + 1) ^ 2) = ε * ((N:ℝ) + 1) ^ 2 := by ring
      rw [h4]
      nlinarith [hε.le, Nat.cast_nonneg (α := ℝ) N]
    have hfin : ∫ p, ((TN N).indicator (fun _ => (1:ℝ)) p
        - ∑ n ∈ Finset.range N, Ψ n p) ^ 2 ∂(ν.prod unitμ) ≤ ε / 4 := by
      refine hstep2.trans ?_
      refine le_trans (mul_le_mul_of_nonneg_left hstep3 (Nat.cast_nonneg N)) hNle
    linarith

/-- A simple function is bounded and measurable. -/
theorem SimpleFunc.isBM (s : MeasureTheory.SimpleFunc (X × ℝ) ℝ) : IsBM ⇑s := by
  refine ⟨s.measurable, ∑ c ∈ s.range, |c|, fun p => ?_⟩
  exact Finset.single_le_sum (f := fun c => |c|) (fun c _ => abs_nonneg c)
    (MeasureTheory.SimpleFunc.mem_range_self s p)

/-- `∫ ((f + g) - (Ψ₁ + Ψ₂))² ≤ 2∫ (f - Ψ₁)² + 2∫ (g - Ψ₂)²`. -/
theorem integral_sq_add_sub_le {f g Ψ₁ Ψ₂ : X × ℝ → ℝ} (hf : IsBM f) (hg : IsBM g)
    (h₁ : IsBM Ψ₁) (h₂ : IsBM Ψ₂) :
    ∫ p, ((f p + g p) - (Ψ₁ p + Ψ₂ p)) ^ 2 ∂(ν.prod unitμ)
      ≤ 2 * ∫ p, (f p - Ψ₁ p) ^ 2 ∂(ν.prod unitμ)
        + 2 * ∫ p, (g p - Ψ₂ p) ^ 2 ∂(ν.prod unitμ) := by
  have i1 := (hf.sub h₁).integrable_sq (ν := ν)
  have i2 := (hg.sub h₂).integrable_sq (ν := ν)
  have i3 := ((hf.add' hg).sub (h₁.add' h₂)).integrable_sq (ν := ν)
  calc ∫ p, ((f p + g p) - (Ψ₁ p + Ψ₂ p)) ^ 2 ∂(ν.prod unitμ)
      ≤ ∫ p, (2 * (f p - Ψ₁ p) ^ 2 + 2 * (g p - Ψ₂ p) ^ 2) ∂(ν.prod unitμ) := by
        refine integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun p => ?_
        nlinarith [sq_nonneg ((f p - Ψ₁ p) - (g p - Ψ₂ p))]
    _ = _ := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]

/-- **Simple functions are approximated by finite sums of products.** -/
theorem exists_isProdSimple_approx_simpleFunc (s : MeasureTheory.SimpleFunc (X × ℝ) ℝ) :
    ∀ ε > 0, ∃ Ψ, IsProdSimple Ψ ∧ ∫ p, (s p - Ψ p) ^ 2 ∂(ν.prod unitμ) < ε := by
  classical
  induction s using MeasureTheory.SimpleFunc.induction with
  | @const c S hS =>
    intro ε hε
    obtain ⟨Ψ₀, hΨ₀, hΨ₀ε⟩ := approxBySimple_of_measurableSet (ν := ν) hS (ε / (c ^ 2 + 1))
      (by positivity)
    refine ⟨fun p => c * Ψ₀ p, hΨ₀.smul c, ?_⟩
    have hpt : ∀ p, ((MeasureTheory.SimpleFunc.piecewise S hS
          (MeasureTheory.SimpleFunc.const _ c) (MeasureTheory.SimpleFunc.const _ 0)) p
          - c * Ψ₀ p) ^ 2
        = c ^ 2 * (S.indicator (fun _ => (1:ℝ)) p - Ψ₀ p) ^ 2 := by
      intro p
      by_cases hp : p ∈ S
      · rw [MeasureTheory.SimpleFunc.piecewise_apply, if_pos hp, Set.indicator_of_mem hp]
        simp only [MeasureTheory.SimpleFunc.const_apply]
        ring
      · rw [MeasureTheory.SimpleFunc.piecewise_apply, if_neg hp, Set.indicator_of_notMem hp]
        simp only [MeasureTheory.SimpleFunc.const_apply]
        ring
    have hrw : ∫ p, ((MeasureTheory.SimpleFunc.piecewise S hS
          (MeasureTheory.SimpleFunc.const _ c) (MeasureTheory.SimpleFunc.const _ 0)) p
          - c * Ψ₀ p) ^ 2 ∂(ν.prod unitμ)
        = c ^ 2 * ∫ p, (S.indicator (fun _ => (1:ℝ)) p - Ψ₀ p) ^ 2 ∂(ν.prod unitμ) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [hrw]
    have hnn : 0 ≤ ∫ p, (S.indicator (fun _ => (1:ℝ)) p - Ψ₀ p) ^ 2 ∂(ν.prod unitμ) :=
      integral_nonneg fun p => sq_nonneg _
    have hc2 : (0:ℝ) ≤ c ^ 2 := sq_nonneg c
    calc c ^ 2 * ∫ p, (S.indicator (fun _ => (1:ℝ)) p - Ψ₀ p) ^ 2 ∂(ν.prod unitμ)
        ≤ c ^ 2 * (ε / (c ^ 2 + 1)) := mul_le_mul_of_nonneg_left hΨ₀ε.le hc2
      _ < ε := by
          rw [mul_div_assoc'] at *
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
  | @add f g hdisj hf hg =>
    intro ε hε
    obtain ⟨Ψ₁, hΨ₁, hΨ₁ε⟩ := hf (ε / 4) (by positivity)
    obtain ⟨Ψ₂, hΨ₂, hΨ₂ε⟩ := hg (ε / 4) (by positivity)
    refine ⟨fun p => Ψ₁ p + Ψ₂ p, hΨ₁.add hΨ₂, ?_⟩
    have := integral_sq_add_sub_le (ν := ν) (SimpleFunc.isBM f) (SimpleFunc.isBM g)
      (IsBM.of_isProdSimple hΨ₁) (IsBM.of_isProdSimple hΨ₂)
    have hrw : ∫ p, ((f + g) p - (Ψ₁ p + Ψ₂ p)) ^ 2 ∂(ν.prod unitμ)
        = ∫ p, ((f p + g p) - (Ψ₁ p + Ψ₂ p)) ^ 2 ∂(ν.prod unitμ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      rw [MeasureTheory.SimpleFunc.coe_add]
      rfl
    rw [hrw]
    linarith

/-- **Every bounded measurable function on the product is approximated in `L²` by finite sums of
products.** -/
theorem exists_isProdSimple_approx {Φ : X × ℝ → ℝ} (hm : Measurable Φ) {C : ℝ}
    (hb : ∀ p, |Φ p| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ, IsProdSimple Ψ ∧ ∫ p, (Φ p - Ψ p) ^ 2 ∂(ν.prod unitμ) < ε := by
  classical
  have h0 : (0:ℝ) ∈ Set.range Φ ∪ {0} := by simp
  set s : ℕ → MeasureTheory.SimpleFunc (X × ℝ) ℝ :=
    fun n => MeasureTheory.SimpleFunc.approxOn Φ hm (Set.range Φ ∪ {0}) 0 h0 n with hs
  have hbound : ∀ n p, |s n p| ≤ 2 * C := by
    intro n p
    have := MeasureTheory.SimpleFunc.norm_approxOn_zero_le hm h0 p n
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    calc |s n p| ≤ |Φ p| + |Φ p| := this
      _ ≤ 2 * C := by linarith [hb p]
  have htend : Filter.Tendsto (fun n => ∫ p, (Φ p - s n p) ^ 2 ∂(ν.prod unitμ))
      Filter.atTop (nhds 0) := by
    have hdct := tendsto_integral_of_dominated_convergence (μ := ν.prod unitμ)
      (F := fun n p => (Φ p - s n p) ^ 2) (f := fun _ => (0:ℝ))
      (bound := fun _ => (3 * C) ^ 2) ?_ (integrable_const _) ?_ ?_
    · simpa using hdct
    · intro n
      exact ((hm.sub (s n).measurable).pow_const 2).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_pow]
      have hle : |Φ p - s n p| ≤ 3 * C := by
        have := hbound n p
        have := hb p
        calc |Φ p - s n p| ≤ |Φ p| + |s n p| := abs_sub _ _
          _ ≤ 3 * C := by linarith
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    · refine Filter.Eventually.of_forall fun p => ?_
      have hlim : Filter.Tendsto (fun n => s n p) Filter.atTop (nhds (Φ p)) :=
        MeasureTheory.SimpleFunc.tendsto_approxOn hm h0 (by
          apply subset_closure
          simp)
      have : Filter.Tendsto (fun n => (Φ p - s n p) ^ 2) Filter.atTop (nhds ((Φ p - Φ p) ^ 2)) :=
        ((tendsto_const_nhds.sub hlim).pow 2)
      simpa using this
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 4))).exists
  obtain ⟨Ψ, hΨ, hΨε⟩ := exists_isProdSimple_approx_simpleFunc (ν := ν) (s n)
    (ε / 4) (by positivity)
  refine ⟨Ψ, hΨ, ?_⟩
  have hBMΦ : IsBM Φ := ⟨hm, C, hb⟩
  have := integral_sq_sub_le (ν := ν) hBMΦ (SimpleFunc.isBM (s n)) (IsBM.of_isProdSimple hΨ)
  linarith


end Approx

end UpperTailMultipodality
