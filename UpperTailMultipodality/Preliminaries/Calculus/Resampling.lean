import UpperTailMultipodality.Preliminaries.Kernel

/-!
# Bounded measurable functions and resampling coordinates of `Measure.pi`

The homomorphism densities of `sec:derivatives` and `sec:rooted-densities` are integrals over
`[0,1]^{V(H)}` against `π = Measure.pi (fun _ => unitμ)`.  Almost every identity between them is
an instance of the *resampling identity*: replacing one or two coordinates of `ξ ∼ π` by fresh
independent uniform variables does not change the distribution.

* `IsBddMeas` — measurable real functions with a uniform bound, with closure lemmas;
* `measurePreserving_update_pi`, `measurePreserving_update₂_pi` — resampling one or two
  coordinates preserves `π`;
* `integral_integral_update_pi`, `integral_integral_update₂_pi` — the corresponding Fubini forms;
* `integral_comp_eval_pi` — the one-coordinate marginal of `π` is `unitμ`;
* `measurable_edgeVal`, `isBddMeas_edgeVal`, `edgeVal_mem_Icc` — edge factors of kernels.
-/

namespace UpperTailMultipodality

open MeasureTheory

/-! ### Bounded measurable functions -/

/-- A measurable real function with a uniform bound. -/
def IsBddMeas {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C

namespace IsBddMeas

variable {α : Type*} [MeasurableSpace α] {f g : α → ℝ}

/-- Constants are bounded and measurable. -/
theorem const (c : ℝ) : IsBddMeas fun _ : α => c := ⟨measurable_const, |c|, fun _ => le_rfl⟩

/-- A measurable function with values in `[0,1]` is bounded. -/
theorem of_mem_Icc (hf : Measurable f) (h : ∀ x, f x ∈ Set.Icc (0:ℝ) 1) : IsBddMeas f :=
  ⟨hf, 1, fun x => by rw [abs_of_nonneg (h x).1]; exact (h x).2⟩

/-- Sums of bounded measurable functions. -/
theorem add (hf : IsBddMeas f) (hg : IsBddMeas g) : IsBddMeas fun x => f x + g x := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.add hgm, C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

/-- Differences of bounded measurable functions. -/
theorem sub (hf : IsBddMeas f) (hg : IsBddMeas g) : IsBddMeas fun x => f x - g x := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.sub hgm, C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩

/-- Products of bounded measurable functions. -/
theorem mul (hf : IsBddMeas f) (hg : IsBddMeas g) : IsBddMeas fun x => f x * g x := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  refine ⟨hfm.mul hgm, |C| * |D|, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_abs_self C)) ((hD x).trans (le_abs_self D))
    (abs_nonneg _) (abs_nonneg _)

/-- Constant multiples of bounded measurable functions. -/
theorem const_mul (hf : IsBddMeas f) (c : ℝ) : IsBddMeas fun x => c * f x :=
  (const c).mul hf

/-- Absolute values of bounded measurable functions. -/
theorem abs (hf : IsBddMeas f) : IsBddMeas fun x => |f x| := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact ⟨hfm.abs, C, fun x => by rw [abs_abs]; exact hC x⟩

/-- Composition with a measurable map. -/
theorem comp {β : Type*} [MeasurableSpace β] (hf : IsBddMeas f) {h : β → α}
    (hh : Measurable h) : IsBddMeas fun y => f (h y) := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact ⟨hfm.comp hh, C, fun y => hC (h y)⟩

/-- Finite products of bounded measurable functions. -/
theorem finset_prod {ι : Type*} (s : Finset ι) {F : ι → α → ℝ}
    (hF : ∀ i ∈ s, IsBddMeas (F i)) : IsBddMeas fun x => ∏ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- Finite sums of bounded measurable functions. -/
theorem finset_sum {ι : Type*} (s : Finset ι) {F : ι → α → ℝ}
    (hF : ∀ i ∈ s, IsBddMeas (F i)) : IsBddMeas fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable (hf : IsBddMeas f) {μ : Measure α} [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact integrable_of_abs_le hfm C hC

end IsBddMeas

/-! ### Edge factors -/

section EdgeVal

variable {V : Type*}

/-- An edge factor of a measurable kernel is measurable in the vertex assignment. -/
theorem measurable_edgeVal {K : ℝ → ℝ → ℝ} (hK : ∀ x y, K x y = K y x)
    (hm : Measurable (Function.uncurry K)) (e : Sym2 V) :
    Measurable fun x : V → ℝ => edgeVal K hK x e := by
  induction e using Sym2.ind with
  | _ a b =>
    show Measurable fun x : V → ℝ => K (x a) (x b)
    have hpair : Measurable fun x : V → ℝ => (x a, x b) := by fun_prop
    exact hm.comp hpair

/-- An edge factor of a bounded kernel is a bounded measurable function. -/
theorem isBddMeas_edgeVal (K : Kernel) (e : Sym2 V) :
    IsBddMeas fun x : V → ℝ => edgeVal K.toFun K.symm' x e := by
  obtain ⟨C, hC⟩ := K.bdd'
  refine ⟨measurable_edgeVal K.symm' K.meas' e, C, fun x => ?_⟩
  induction e using Sym2.ind with
  | _ a b => exact hC (x a) (x b)

/-- An edge factor of a graphon lies in `[0,1]`. -/
theorem edgeVal_mem_Icc (W : Graphon) (x : V → ℝ) (e : Sym2 V) :
    edgeVal W.toFun W.symm' x e ∈ Set.Icc (0:ℝ) 1 := by
  induction e using Sym2.ind with
  | _ a b => exact W.mem_Icc (x a) (x b)

/-- A product of edge factors of a graphon lies in `[0,1]`. -/
theorem prod_edgeVal_mem_Icc (W : Graphon) (T : Finset (Sym2 V)) (x : V → ℝ) :
    ∏ e ∈ T, edgeVal W.toFun W.symm' x e ∈ Set.Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg fun e _ => (edgeVal_mem_Icc W x e).1,
    Finset.prod_le_one (fun e _ => (edgeVal_mem_Icc W x e).1)
      fun e _ => (edgeVal_mem_Icc W x e).2⟩

/-- A product of edge factors of a graphon is a bounded measurable function. -/
theorem isBddMeas_prod_edgeVal (W : Graphon) (T : Finset (Sym2 V)) :
    IsBddMeas fun x : V → ℝ => ∏ e ∈ T, edgeVal W.toFun W.symm' x e :=
  IsBddMeas.of_mem_Icc
    (Finset.measurable_prod _ fun e _ => measurable_edgeVal W.symm' W.meas' e)
    (prod_edgeVal_mem_Icc W T)

end EdgeVal

/-! ### Resampling coordinates -/

section Resampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Resampling one coordinate preserves the product measure**: `(ξ, x) ↦ ξ[w ↦ x]` pushes
`π ⊗ unitμ` forward to `π`.  The preimage of a box `∏ᵢ sᵢ` is `(∏_{i ≠ w} sᵢ) × s_w`, so
`Measure.pi_eq` identifies the push-forward with `π`. -/
theorem measurePreserving_update_pi (w : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2)
      ((Measure.pi fun _ : ι => unitμ).prod unitμ) (Measure.pi fun _ : ι => unitμ) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 w p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s w Set.univ)) ×ˢ s w := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = w
        · subst hi; rw [Function.update_self]; exact Set.mem_univ _
        · rw [Function.update_of_ne hi]
          have hpi := hp i
          rwa [Function.update_of_ne hi] at hpi
      · have hpw := hp w
        rwa [Function.update_self] at hpw
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = w
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        have h1i := h1 i
        rwa [Function.update_of_ne hi] at h1i
  have hrest : (∏ i ∈ Finset.univ.erase w, unitμ (Function.update s w Set.univ i))
      = ∏ i ∈ Finset.univ.erase w, unitμ (s i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun i => unitμ (s i)) (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => unitμ (Function.update s w Set.univ i)) (Finset.mem_univ w),
    Function.update_self, measure_univ, hrest]
  ring

/-- **Resampling two coordinates preserves the product measure**:
`(ξ, (x, y)) ↦ ξ[a ↦ x][b ↦ y]` pushes `π ⊗ gμ` forward to `π`. -/
theorem measurePreserving_update₂_pi (a b : ι) :
    MeasurePreserving
      (fun p : (ι → ℝ) × (ℝ × ℝ) => Function.update (Function.update p.1 a p.2.1) b p.2.2)
      ((Measure.pi fun _ : ι => unitμ).prod gμ) (Measure.pi fun _ : ι => unitμ) := by
  have h1 := measurePreserving_update_pi (ι := ι) a
  have h2 := measurePreserving_update_pi (ι := ι) b
  have hassoc := MeasurePreserving.symm _
    (measurePreserving_prodAssoc (Measure.pi fun _ : ι => unitμ) unitμ unitμ)
  have hmap := h1.prod (MeasurePreserving.id unitμ)
  exact (h2.comp hmap).comp hassoc

/-- **The one-coordinate resampling identity** in Fubini form: for bounded measurable `F`,
`∫₀¹ ∫ F(ξ[w ↦ x]) dπ(ξ) dx = ∫ F dπ`. -/
theorem integral_integral_update_pi (w : ι) {F : (ι → ℝ) → ℝ} (hF : IsBddMeas F) :
    ∫ x, ∫ ξ, F (Function.update ξ w x) ∂(Measure.pi fun _ : ι => unitμ) ∂unitμ
      = ∫ ξ, F ξ ∂(Measure.pi fun _ : ι => unitμ) := by
  have hmp := measurePreserving_update_pi (ι := ι) w
  have hint : Integrable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 w p.2))
      ((Measure.pi fun _ : ι => unitμ).prod unitμ) :=
    (hF.comp hmp.measurable).integrable
  have step : ∫ ξ, F ξ ∂(Measure.pi fun _ : ι => unitμ)
      = ∫ p, F (Function.update p.1 w p.2) ∂((Measure.pi fun _ : ι => unitμ).prod unitμ) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hF.1.aestronglyMeasurable
  rw [step, integral_prod_symm _ hint]

/-- The partial integral `x ↦ ∫ F(ξ[w ↦ x]) dπ(ξ)` is integrable. -/
theorem integrable_integral_update_pi (w : ι) {F : (ι → ℝ) → ℝ} (hF : IsBddMeas F) :
    Integrable (fun x => ∫ ξ, F (Function.update ξ w x) ∂(Measure.pi fun _ : ι => unitμ))
      unitμ := by
  have hmp := measurePreserving_update_pi (ι := ι) w
  have hint : Integrable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 w p.2))
      ((Measure.pi fun _ : ι => unitμ).prod unitμ) :=
    (hF.comp hmp.measurable).integrable
  exact hint.integral_prod_right

/-- **The two-coordinate resampling identity** in Fubini form: for bounded measurable `F`,
`∫∫ ∫ F(ξ[a ↦ x][b ↦ y]) dπ(ξ) dx dy = ∫ F dπ`. -/
theorem integral_integral_update₂_pi (a b : ι) {F : (ι → ℝ) → ℝ} (hF : IsBddMeas F) :
    ∫ z, ∫ ξ, F (Function.update (Function.update ξ a z.1) b z.2)
        ∂(Measure.pi fun _ : ι => unitμ) ∂gμ
      = ∫ ξ, F ξ ∂(Measure.pi fun _ : ι => unitμ) := by
  have hmp := measurePreserving_update₂_pi (ι := ι) a b
  have hint : Integrable
      (fun p : (ι → ℝ) × (ℝ × ℝ) => F (Function.update (Function.update p.1 a p.2.1) b p.2.2))
      ((Measure.pi fun _ : ι => unitμ).prod gμ) :=
    (hF.comp hmp.measurable).integrable
  have step : ∫ ξ, F ξ ∂(Measure.pi fun _ : ι => unitμ)
      = ∫ p, F (Function.update (Function.update p.1 a p.2.1) b p.2.2)
          ∂((Measure.pi fun _ : ι => unitμ).prod gμ) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hF.1.aestronglyMeasurable
  rw [step, integral_prod_symm _ hint]

/-- The partial integral `(x, y) ↦ ∫ F(ξ[a ↦ x][b ↦ y]) dπ(ξ)` is measurable. -/
theorem measurable_integral_update₂_pi (a b : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F) :
    Measurable fun z : ℝ × ℝ =>
      ∫ ξ, F (Function.update (Function.update ξ a z.1) b z.2)
        ∂(Measure.pi fun _ : ι => unitμ) := by
  have hmp := measurePreserving_update₂_pi (ι := ι) a b
  have h : StronglyMeasurable fun q : (ℝ × ℝ) × (ι → ℝ) =>
      F (Function.update (Function.update q.2 a q.1.1) b q.1.2) :=
    ((hF.comp hmp.measurable).comp measurable_swap).stronglyMeasurable
  exact h.integral_prod_right'.measurable

omit [DecidableEq ι] in
/-- **The one-coordinate marginal of `π`** is `unitμ`. -/
theorem integral_comp_eval_pi (w : ι) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ξ, f (ξ w) ∂(Measure.pi fun _ : ι => unitμ) = ∫ t, f t ∂unitμ := by
  have hmp := measurePreserving_eval (μ := fun _ : ι => unitμ) w
  conv_rhs => rw [← hmp.map_eq]
  exact (integral_map (measurable_pi_apply w).aemeasurable hf.aestronglyMeasurable).symm

end Resampling

end UpperTailMultipodality
