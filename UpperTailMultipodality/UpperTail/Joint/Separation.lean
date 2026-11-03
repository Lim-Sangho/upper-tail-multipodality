import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separating a cone of first-order changes from the improving directions

This file formalises the finite-dimensional separation step in the proof of
`lem:upper-tail-multiplier`, the device that lets
the proof of `lem:upper-tail-multiplier` dispense with a constraint qualification.

Record the first-order change of the objective and of the constraint densities along a feasible
perturbation as a point of `ℝ × (ι → ℝ)`: the first coordinate is the change of the objective and
the coordinate `j` the change of the `j`-th constraint density.  The attainable changes form a
convex cone `C` containing `0`, and at a minimizer no attainable change improves everything at
once, so `C` is disjoint from the *improving directions*

  `𝒩 = {z | z₀ < 0 and 0 < z_j for every active j}`,

which is an open convex cone.  The geometric Hahn-Banach theorem then separates the two by a
nonzero continuous linear functional, and testing that functional on the coordinate directions of
`𝒩` pins down the signs of its coefficients: the objective receives a nonnegative multiplier `λ`,
each active constraint a nonnegative multiplier `μ_j`, and each inactive constraint the
multiplier `0`.  This is `exists_multipliers_of_cone_disjoint`.
-/

namespace UpperTailMultipodality

open Set

/-- The open convex cone `𝒩` of improving directions of `lem:upper-tail-multiplier`: the
objective strictly
decreases and every active constraint density strictly increases. -/
private def Improving {ι : Type*} (A : Finset ι) : Set (ℝ × (ι → ℝ)) :=
  {z | z.1 < 0 ∧ ∀ j ∈ A, 0 < z.2 j}

private theorem mem_Improving {ι : Type*} {A : Finset ι} {z : ℝ × (ι → ℝ)} :
    z ∈ Improving A ↔ z.1 < 0 ∧ ∀ j ∈ A, 0 < z.2 j := Iff.rfl

/-- `𝒩` is the intersection of an open half-space with finitely many open half-spaces. -/
private theorem Improving_eq_inter {ι : Type*} (A : Finset ι) :
    Improving A
      = {z : ℝ × (ι → ℝ) | z.1 < 0} ∩ ⋂ j ∈ A, {z : ℝ × (ι → ℝ) | 0 < z.2 j} := by
  ext z
  rw [mem_Improving]
  simp

private theorem convex_Improving {ι : Type*} (A : Finset ι) : Convex ℝ (Improving A) := by
  rw [Improving_eq_inter]
  exact (convex_halfSpace_lt (IsLinearMap.mk (fun _ _ => rfl) fun _ _ => rfl) 0).inter
    (convex_iInter fun j => convex_iInter fun _ =>
      convex_halfSpace_gt (IsLinearMap.mk (fun _ _ => rfl) fun _ _ => rfl) 0)

private theorem isOpen_Improving {ι : Type*} (A : Finset ι) : IsOpen (Improving A) := by
  rw [Improving_eq_inter]
  exact (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_biInter_finset fun j _ =>
      isOpen_lt continuous_const ((continuous_apply j).comp continuous_snd))

/-- An affine function of `t` that is negative for every `t > 0` has nonpositive slope. -/
private theorem nonpos_of_forall_pos {c d : ℝ} (h : ∀ t : ℝ, 0 < t → c + t * d < 0) : d ≤ 0 := by
  by_contra hd
  push Not at hd
  -- with positive slope the value at `t = (|c| + 1)/d` is at least `1`
  have ht : 0 < (|c| + 1) / d := div_pos (by positivity) hd
  have hval := h _ ht
  rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hval
  linarith [neg_abs_le c]

/-- An affine function of `t` that is negative for every real `t` has zero slope. -/
private theorem eq_zero_of_forall {c d : ℝ} (h : ∀ t : ℝ, c + t * d < 0) : d = 0 := by
  have h₁ : d ≤ 0 := nonpos_of_forall_pos (c := c) fun t _ => h t
  have h₂ : -d ≤ 0 := nonpos_of_forall_pos (c := c) fun t _ => by linarith [h (-t)]
  linarith

/-- The coefficients of a continuous linear functional on `ℝ × (ι → ℝ)`: it is determined by its
values at `(1,0)` and at the coordinate directions `(0, e_j)`. -/
private theorem apply_eq_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : StrongDual ℝ (ℝ × (ι → ℝ))) (z : ℝ × (ι → ℝ)) :
    f z = f (1, 0) * z.1 + ∑ j, f (0, Pi.single j 1) * z.2 j := by
  -- decompose `z` along the standard basis of `ℝ × (ι → ℝ)`
  have hsnd : ∑ j, z.2 j • ((0 : ℝ), Pi.single j (1 : ℝ)) = ((0 : ℝ), z.2) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum]
      have hterm : ∀ j : ι, (z.2 j • ((0 : ℝ), Pi.single j (1 : ℝ))).2
          = (Pi.single j (z.2 j) : ι → ℝ) := by
        intro j
        show z.2 j • (Pi.single j (1 : ℝ) : ι → ℝ) = (Pi.single j (z.2 j) : ι → ℝ)
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      exact Finset.univ_sum_single z.2
  have hz : z.1 • ((1 : ℝ), (0 : ι → ℝ)) + ∑ j, z.2 j • ((0 : ℝ), Pi.single j (1 : ℝ)) = z := by
    rw [hsnd]
    refine Prod.ext ?_ ?_ <;> simp
  have hterms : ∑ j, f (z.2 j • ((0 : ℝ), Pi.single j (1 : ℝ)))
      = ∑ j, f ((0 : ℝ), Pi.single j (1 : ℝ)) * z.2 j :=
    Finset.sum_congr rfl fun j _ => by rw [f.map_smul, smul_eq_mul, mul_comm]
  conv_lhs => rw [← hz]
  rw [map_add, f.map_smul, map_sum, hterms, smul_eq_mul, mul_comm z.1 (f (1, 0))]

/-- **Separation of a convex cone from the improving directions** (`lem:upper-tail-multiplier`).
Let
`C ⊆ ℝ × (ι → ℝ)` be a convex cone containing `0` and disjoint from the open convex cone
`{z | z.1 < 0 and 0 < z.2 j for every j ∈ A}`.  Then there are `λ ≥ 0` and weights `μ_j ≥ 0`,
vanishing off `A` and not all zero together with `λ`, such that the linear functional
`z ↦ λ z_0 - ∑_j μ_j z_j` is nonnegative on `C`. -/
theorem exists_multipliers_of_cone_disjoint {ι : Type*} [Fintype ι] (A : Finset ι)
    (C : Set (ℝ × (ι → ℝ))) (hconv : Convex ℝ C) (hzero : (0 : ℝ × (ι → ℝ)) ∈ C)
    (hsmul : ∀ r : ℝ, 0 ≤ r → ∀ z ∈ C, r • z ∈ C)
    (hdisj : ∀ z ∈ C, ¬ (z.1 < 0 ∧ ∀ j ∈ A, 0 < z.2 j)) :
    ∃ (lam : ℝ) (μ : ι → ℝ), 0 ≤ lam ∧ (∀ j, 0 ≤ μ j) ∧ (∀ j ∉ A, μ j = 0) ∧
      (lam ≠ 0 ∨ ∃ j, μ j ≠ 0) ∧
      ∀ z ∈ C, 0 ≤ lam * z.1 - ∑ j, μ j * z.2 j := by
  classical
  -- `𝒩` is open and convex, and the hypothesis says exactly that it misses `C`
  have hdisjoint : Disjoint (Improving A) C :=
    Set.disjoint_left.mpr fun z hzN hzC => hdisj z hzC (mem_Improving.mp hzN)
  obtain ⟨f, u, hfN, hfC⟩ :=
    geometric_hahn_banach_open (convex_Improving A) (isOpen_Improving A) hconv hdisjoint
  -- `0 ∈ C` forces the separating level to be nonpositive
  have hu0 : u ≤ 0 := by
    have h := hfC 0 hzero
    rwa [map_zero] at h
  -- on the cone `C` the functional is nonnegative: a negative value could be rescaled below `u`
  have hfCnonneg : ∀ z ∈ C, 0 ≤ f z := by
    intro z hzC
    by_contra hlt
    push Not at hlt
    have hr : 0 < (u - 1) / f z := div_pos_of_neg_of_neg (by linarith) hlt
    have h := hfC (((u - 1) / f z) • z) (hsmul _ hr.le z hzC)
    rw [f.map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_lt hlt)] at h
    linarith
  -- the coefficients of `f`
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = f (1, 0) := ⟨_, rfl⟩
  obtain ⟨nu, hnu⟩ : ∃ n : ι → ℝ, n = fun j => f (0, Pi.single j 1) := ⟨_, rfl⟩
  have hform : ∀ z : ℝ × (ι → ℝ), f z = lam * z.1 + ∑ j, nu j * z.2 j := by
    intro z
    rw [hlam, hnu]
    exact apply_eq_coeff f z
  -- the value of `f` on the directions `(-t, 1)` of `𝒩`
  have hval1 : ∀ t : ℝ, f ((-t : ℝ), (fun _ => (1 : ℝ) : ι → ℝ)) = (∑ j, nu j) + t * (-lam) := by
    intro t
    rw [hform]
    show lam * (-t) + ∑ j, nu j * (1 : ℝ) = (∑ j, nu j) + t * (-lam)
    simp only [mul_one]
    ring
  -- the value of `f` on the directions `(-1, 1 + t e_{j₀})`, affine in `t` with slope `ν_{j₀}`
  have hval2 : ∀ (t : ℝ) (j₀ : ι),
      f ((-1 : ℝ), (fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ))
        = (-lam + ∑ j, nu j) + t * nu j₀ := by
    intro t j₀
    have hone : ∑ j, nu j * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j = nu j₀ := by
      simp [Pi.single_apply]
    have hsum : ∑ j, nu j * ((((fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ)) : ι → ℝ) j)
        = (∑ j, nu j) + t * nu j₀ := by
      calc ∑ j, nu j * ((((fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ)) : ι → ℝ) j)
          = ∑ j, (nu j + t * (nu j * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j)) :=
            Finset.sum_congr rfl fun j _ => by
              show nu j * (1 + t * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j) = _
              ring
        _ = (∑ j, nu j) + t * ∑ j, nu j * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ j, nu j) + t * nu j₀ := by rw [hone]
    rw [hform]
    show lam * (-1) + ∑ j, nu j * ((((fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ)) : ι → ℝ) j) = _
    rw [hsum]
    ring
  -- `λ ≥ 0`: the directions `(-t, 1)` lie in `𝒩` for every `t > 0`
  have hlam0 : 0 ≤ lam := by
    have hslope : -lam ≤ 0 := by
      refine nonpos_of_forall_pos (c := ∑ j, nu j) fun t ht => ?_
      have hmem : ((-t : ℝ), (fun _ => (1 : ℝ) : ι → ℝ)) ∈ Improving A :=
        mem_Improving.mpr ⟨by simpa using ht, fun _ _ => one_pos⟩
      have h := hfN _ hmem
      rw [hval1] at h
      linarith
    linarith
  -- `ν_j ≤ 0` for an active `j`: only `t > 0` keeps the `j`-th entry of `1 + t e_j` positive
  have hnuA : ∀ j₀ ∈ A, nu j₀ ≤ 0 := by
    intro j₀ _
    refine nonpos_of_forall_pos (c := -lam + ∑ j, nu j) fun t ht => ?_
    have hmem : ((-1 : ℝ), (fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ)) ∈ Improving A := by
      refine mem_Improving.mpr ⟨by norm_num, fun j _ => ?_⟩
      show 0 < 1 + t * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j
      rcases eq_or_ne j₀ j with rfl | hne
      · rw [Pi.single_eq_same]; linarith
      · rw [Pi.single_eq_of_ne' hne]; linarith
    have h := hfN _ hmem
    rw [hval2] at h
    linarith
  -- `ν_j = 0` for an inactive `j`: no constraint is imposed there, so every real `t` is allowed
  have hnu0 : ∀ j₀ ∉ A, nu j₀ = 0 := by
    intro j₀ hj₀
    refine eq_zero_of_forall (c := -lam + ∑ j, nu j) fun t => ?_
    have hmem : ((-1 : ℝ), (fun _ => (1 : ℝ)) + t • Pi.single j₀ (1 : ℝ)) ∈ Improving A := by
      refine mem_Improving.mpr ⟨by norm_num, fun j hj => ?_⟩
      have hne : j₀ ≠ j := fun h => hj₀ (h ▸ hj)
      show 0 < 1 + t * (Pi.single j₀ (1 : ℝ) : ι → ℝ) j
      rw [Pi.single_eq_of_ne' hne]
      norm_num
    have h := hfN _ hmem
    rw [hval2] at h
    linarith
  -- `f` is not the zero functional: it is strictly negative somewhere on `𝒩`
  have hnonzero : f ((-1 : ℝ), (fun _ => (1 : ℝ) : ι → ℝ)) ≠ 0 := by
    have hmem : ((-1 : ℝ), (fun _ => (1 : ℝ) : ι → ℝ)) ∈ Improving A :=
      mem_Improving.mpr ⟨by norm_num, fun _ _ => one_pos⟩
    exact ne_of_lt (by linarith [hfN _ hmem])
  obtain ⟨μ, hμ⟩ : ∃ m : ι → ℝ, m = fun j => -nu j := ⟨_, rfl⟩
  refine ⟨lam, μ, hlam0, fun j => ?_, fun j hj => ?_, ?_, fun z hzC => ?_⟩
  · rw [hμ]
    rcases em (j ∈ A) with hjA | hjA
    · simpa using hnuA j hjA
    · simp [hnu0 j hjA]
  · rw [hμ]
    simp [hnu0 j hj]
  · -- nontriviality: `λ = 0` together with all `μ_j = 0` would make `f` vanish identically
    by_contra hall
    push Not at hall
    obtain ⟨hlz, hμz⟩ := hall
    refine hnonzero ?_
    have hnuz : ∀ j, nu j = 0 := fun j => by
      have := hμz j
      rw [hμ] at this
      simpa using this
    rw [hform, hlz]
    simp [hnuz]
  · have h := hfCnonneg z hzC
    rw [hform] at h
    have hrw : ∑ j, μ j * z.2 j = -∑ j, nu j * z.2 j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hμ]; ring
    linarith [hrw, h]

end UpperTailMultipodality
