import UpperTailMultipodality.Preliminaries.Calculus.Resampling

/-!
# Products and sums over the edges of a finite graph

Combinatorial identities used for the derivative kernel and the rooted densities:

* `edgeFinset_filter_mem_eq_image` — the edges at `v` are the pairs `s(v,z)`, `z ∈ N_H(v)`;
* `prod_edgeFinset_eq_star`, `prod_edgeFinset_erase_eq_star` — a product over `E(H)` (or over
  `E(H) ∖ {vz₀}`) splits into the star at `v` and the edges avoiding `v`;
* `sum_neighborFinset_sym2` — summing a function of the edge over the ordered adjacent pairs
  counts every edge twice;
* `sum_ite_adj_eq_sum_neighborFinset` — the sum over ordered adjacent pairs in `if`-form;
* `abs_prod_sub_prod_le_sum` — telescoping for products of numbers in `[0,1]`.
-/

namespace UpperTailMultipodality

open Finset

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The edges of `H` containing `v` are the pairs `s(v,z)` with `z ∈ N_H(v)`. -/
theorem edgeFinset_filter_mem_eq_image (v : V) :
    H.edgeFinset.filter (fun e => v ∈ e) = (H.neighborFinset v).image (fun z => s(v, z)) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff,
      mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hab, rfl | rfl⟩
      · exact ⟨b, hab, rfl⟩
      · exact ⟨a, hab.symm, Sym2.eq_swap⟩
    · rintro ⟨z, hz, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hz, Or.inl rfl⟩
      · exact ⟨hz.symm, Or.inr rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
/-- `z ↦ s(v,z)` is injective. -/
theorem sym2_mk_left_injective (v : V) : Function.Injective fun z : V => s(v, z) :=
  fun _ _ h => Sym2.congr_right.mp h

/-- **The star decomposition of a product over `E(H)`.** -/
theorem prod_edgeFinset_eq_star {M : Type*} [CommMonoid M] (f : Sym2 V → M) (v : V) :
    ∏ e ∈ H.edgeFinset, f e
      = (∏ z ∈ H.neighborFinset v, f s(v, z))
        * ∏ e ∈ H.edgeFinset.filter (fun e => v ∉ e), f e := by
  rw [← prod_filter_mul_prod_filter_not H.edgeFinset (fun e => v ∈ e),
    edgeFinset_filter_mem_eq_image, prod_image (sym2_mk_left_injective v).injOn]

/-- **The star decomposition of a product over `E(H) ∖ {vz₀}`.** -/
theorem prod_edgeFinset_erase_eq_star {M : Type*} [CommMonoid M] (f : Sym2 V → M) (v z₀ : V) :
    ∏ e ∈ H.edgeFinset.erase s(v, z₀), f e
      = (∏ z ∈ (H.neighborFinset v).erase z₀, f s(v, z))
        * ∏ e ∈ H.edgeFinset.filter (fun e => v ∉ e), f e := by
  rw [← prod_filter_mul_prod_filter_not (H.edgeFinset.erase s(v, z₀)) (fun e => v ∈ e),
    filter_erase, filter_erase, edgeFinset_filter_mem_eq_image,
    ← image_erase (sym2_mk_left_injective v),
    prod_image (sym2_mk_left_injective v).injOn]
  congr 1
  rw [erase_eq_of_notMem]
  simp [Sym2.mem_iff]

/-- **Double counting.**  Summing a function of the edge over the ordered adjacent pairs counts
every edge twice. -/
theorem sum_neighborFinset_sym2 {M : Type*} [AddCommMonoid M] (T : Sym2 V → M) :
    ∑ a, ∑ b ∈ H.neighborFinset a, T s(a, b) = 2 • ∑ e ∈ H.edgeFinset, T e := by
  have h1 : ∑ a, ∑ b ∈ H.neighborFinset a, T s(a, b) = ∑ d : H.Dart, T d.edge := by
    refine (sum_sigma univ (fun a => H.neighborFinset a) (fun p => T s(p.1, p.2))).symm.trans ?_
    refine sum_bij' (fun p _ => ⟨(p.1, p.2), (SimpleGraph.mem_neighborFinset _ _ _).mp
        (mem_sigma.mp ‹_›).2⟩)
      (fun d _ => ⟨d.fst, d.snd⟩) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro d _
      exact mem_sigma.mpr ⟨mem_univ _, (SimpleGraph.mem_neighborFinset _ _ _).mpr d.adj⟩
    · intro p _; rfl
    · intro d _; rfl
    · intro p _; rfl
  have h2 : ∑ d : H.Dart, T d.edge
      = ∑ e ∈ H.edgeFinset, ∑ d ∈ univ.filter (fun d : H.Dart => d.edge = e), T d.edge :=
    (sum_fiberwise_of_maps_to (fun d _ => SimpleGraph.mem_edgeFinset.mpr d.edge_mem) _).symm
  rw [h1, h2, smul_sum]
  refine sum_congr rfl fun e he => ?_
  rw [sum_congr rfl fun d hd => by rw [(mem_filter.mp hd).2], sum_const,
    H.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.mp he)]

omit [DecidableEq V] in
/-- The sum over ordered adjacent pairs, written with `if`, is the sum over neighbourhoods. -/
theorem sum_ite_adj_eq_sum_neighborFinset {M : Type*} [AddCommMonoid M] (f : V → V → M) :
    ∑ a, ∑ b, (if H.Adj a b then f a b else 0) = ∑ a, ∑ b ∈ H.neighborFinset a, f a b := by
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_filter, SimpleGraph.neighborFinset_eq_filter]

omit [DecidableEq V] in
/-- The number of ordered adjacent pairs is `2m`. -/
theorem sum_card_neighborFinset :
    ∑ a, ((H.neighborFinset a).card : ℝ) = 2 * H.edgeFinset.card := by
  have h := H.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborFinset_eq_degree] at h
  exact_mod_cast h

end Graph

/-- **Telescoping.**  `|∏ f - ∏ g| ≤ ∑ |f - g|` for factors in `[0,1]`. -/
theorem abs_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1) (hg : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1) :
    |∏ i ∈ T, f i - ∏ i ∈ T, g i| ≤ ∑ i ∈ T, |f i - g i| := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hfT : ∀ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hf i (mem_insert_of_mem hi)
    have hgT : ∀ i ∈ T, g i ∈ Set.Icc (0:ℝ) 1 := fun i hi => hg i (mem_insert_of_mem hi)
    have hga := hg a (mem_insert_self a T)
    have hP : ∏ i ∈ T, f i ∈ Set.Icc (0:ℝ) 1 :=
      ⟨prod_nonneg fun i hi => (hfT i hi).1,
        prod_le_one (fun i hi => (hfT i hi).1) fun i hi => (hfT i hi).2⟩
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have hsplit : f a * ∏ i ∈ T, f i - g a * ∏ i ∈ T, g i
        = (f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i) := by ring
    rw [hsplit]
    calc |(f a - g a) * ∏ i ∈ T, f i + g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)|
        ≤ |(f a - g a) * ∏ i ∈ T, f i| + |g a * (∏ i ∈ T, f i - ∏ i ∈ T, g i)| := abs_add_le _ _
      _ = |f a - g a| * ∏ i ∈ T, f i + g a * |∏ i ∈ T, f i - ∏ i ∈ T, g i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hP.1, abs_of_nonneg hga.1]
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ T, |f i - g i| :=
          add_le_add (mul_le_mul_of_nonneg_left hP.2 (abs_nonneg _))
            (mul_le_mul hga.2 (ih hfT hgT) (abs_nonneg _) zero_le_one)
      _ = |f a - g a| + ∑ i ∈ T, |f i - g i| := by ring

end UpperTailMultipodality
