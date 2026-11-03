import UpperTailMultipodality.Preliminaries.RootedDensity

/-!
# The worked examples of the paper

The paper illustrates the derivative kernel `eq:derivative-kernel` and the rooted densities
`eq:rooted-density` on the triangle `K₃` and the three-vertex path `P₃`:

* `expl:triangle-derivative`: `𝒟_{K₃,W}(x,y) = 3∫W(x,z)W(y,z)dz` (`derivKernel_triangle`);
* `expl:path-derivative`: `𝒟_{P₃,W}(x,y) = d_W(x) + d_W(y)` (`derivKernel_path`);
* `expl:triangle-rooted`: `ℛ_{K₃,W}(u) = 3∫∫W(y,z)u(y)u(z)` (`totalRootedDensity_triangle`);
* `expl:path-rooted`: rooting at the middle vertex gives `(∫u)²` and at an endpoint
  `∫d_W(y)u(y)dy`, so `ℛ_{P₃,W}(u) = (∫u)² + 2∫d_W u` (`rootedDensity_path_mid`,
  `rootedDensity_path_end`, `totalRootedDensity_path`).

The finite combinatorics of the two graphs is decided (`decide`), and the integrals over the
product measure are reduced to one or two coordinates by `integral_pi_eval` and
`integral_pi_pair`, which are the marginal identities behind the paper's "fixing `x_a = x` and
`x_b = y` leaves the factors …".
-/

namespace UpperTailMultipodality

open MeasureTheory SimpleGraph

/-! ### Marginals of the product measure -/

/-- An integral over `(V → ℝ)` of a function of one coordinate is a one-dimensional integral. -/
theorem integral_pi_eval {V : Type*} [Fintype V] (i : V) {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ ξ : V → ℝ, F (ξ i) ∂(Measure.pi fun _ : V => unitμ) = ∫ z, F z ∂unitμ := by
  have hmp := measurePreserving_eval (μ := fun _ : V => unitμ) i
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun ξ : V → ℝ => ξ i) (f := F) (measurable_pi_apply i).aemeasurable
    (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

/-- An integral over `(V → ℝ)` of a function of two distinct coordinates is an integral over
`gμ`. -/
theorem integral_pi_pair {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b)
    {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) :
    ∫ ξ : V → ℝ, F (ξ a) (ξ b) ∂(Measure.pi fun _ : V => unitμ) = ∫ p, F p.1 p.2 ∂gμ := by
  have hmp := measurePreserving_pair (V := V) hab
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun ξ : V → ℝ => (ξ a, ξ b)) (f := fun p : ℝ × ℝ => F p.1 p.2)
    (by fun_prop) (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

/-! ### The degree function `d_W` -/

/-- **`d_W(y) = ∫₀¹ W(y,z)dz`**, the degree function of a graphon. -/
noncomputable def Graphon.deg (W : Graphon) (y : ℝ) : ℝ := ∫ z, W.toFun y z ∂unitμ

/-- `W(y,·)` is measurable for each `y`. -/
theorem Graphon.measurable_right (W : Graphon) (y : ℝ) : Measurable fun z => W.toFun y z :=
  W.measurable_uncurry.comp (measurable_const.prodMk measurable_id)

/-- `W(·,z)` is measurable for each `z`. -/
theorem Graphon.measurable_left (W : Graphon) (z : ℝ) : Measurable fun y => W.toFun y z :=
  W.measurable_uncurry.comp (measurable_id.prodMk measurable_const)

/-! ### The triangle -/

/-- **`expl:triangle-derivative`.**  For `H = K₃`, every edge contributes the same kernel
`∫W(x,z)W(y,z)dz`, so `𝒟_{K₃,W}(x,y) = 3∫W(x,z)W(y,z)dz`. -/
theorem derivKernel_triangle (W : Graphon) (x y : ℝ) :
    derivKernel (⊤ : SimpleGraph (Fin 3)) W x y = 3 * ∫ z, W.toFun x z * W.toFun y z ∂unitμ := by
  have hmeas : Measurable fun z => W.toFun x z * W.toFun y z :=
    (W.measurable_right x).mul (W.measurable_right y)
  -- each oriented edge gives the same kernel
  have hK : ∀ a b : Fin 3, a ≠ b →
      edgeRemovedDensity (⊤ : SimpleGraph (Fin 3)) W a b x y
        = ∫ z, W.toFun x z * W.toFun y z ∂unitμ := by
    intro a b hab
    obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
      revert hab; revert a b; decide
    rw [edgeRemovedDensity]
    have hset : ((⊤ : SimpleGraph (Fin 3)).edgeFinset).erase s(a, b) = {s(a, c), s(b, c)} := by
      revert hca hcb hab; revert a b c; decide
    rw [hset]
    have hpt : ∀ ξ : Fin 3 → ℝ,
        ∏ e ∈ ({s(a, c), s(b, c)} : Finset (Sym2 (Fin 3))),
          edgeVal W.toFun W.symm' (pin ξ a b x y) e
        = W.toFun x (ξ c) * W.toFun y (ξ c) := by
      intro ξ
      have hne : s(a, c) ≠ s(b, c) := by
        revert hca hcb hab; revert a b c; decide
      rw [Finset.prod_insert (by simpa using hne), Finset.prod_singleton]
      have h1 : pin ξ a b x y a = x := by
        rw [pin, Function.update_of_ne hab, Function.update_self]
      have h2 : pin ξ a b x y b = y := by rw [pin, Function.update_self]
      have h3 : pin ξ a b x y c = ξ c := by
        rw [pin, Function.update_of_ne hcb, Function.update_of_ne hca]
      simp only [edgeVal, Sym2.lift_mk, h1, h2, h3]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_pi_eval c hmeas
  have e : ∀ a b : Fin 3, (if (⊤ : SimpleGraph (Fin 3)).Adj a b then
      edgeRemovedDensity (⊤ : SimpleGraph (Fin 3)) W a b x y else 0)
      = if a = b then 0 else ∫ z, W.toFun x z * W.toFun y z ∂unitμ := by
    intro a b
    by_cases hab : a = b
    · rw [if_neg (by simp [hab]), if_pos hab]
    · rw [if_pos (by simpa using hab), if_neg hab, hK a b hab]
  rw [derivKernel]
  simp only [e]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- **`expl:triangle-rooted`.**  Rooting `K₃` at any vertex leaves the single edge joining the
other two, so each root contributes `∫∫W(y,z)u(y)u(z)`. -/
theorem rootedDensity_triangle (W : Graphon) {u : ℝ → ℝ} (hu : Measurable u) (v : Fin 3) :
    rootedDensity (⊤ : SimpleGraph (Fin 3)) W v u
      = ∫ p, W.toFun p.1 p.2 * (u p.1 * u p.2) ∂gμ := by
  obtain ⟨a, b, hab, hva, hvb⟩ : ∃ a b : Fin 3, a ≠ b ∧ v ≠ a ∧ v ≠ b := by revert v; decide
  rw [rootedDensity]
  have hnb : (⊤ : SimpleGraph (Fin 3)).neighborFinset v = {a, b} := by
    revert hab hva hvb; revert v a b; decide
  have havoid : ((⊤ : SimpleGraph (Fin 3)).edgeFinset.filter fun e => v ∉ e) = {s(a, b)} := by
    revert hab hva hvb; revert v a b; decide
  have hpt : ∀ ξ : Fin 3 → ℝ,
      (∏ z ∈ (⊤ : SimpleGraph (Fin 3)).neighborFinset v, u (ξ z))
        * avoidingProduct (⊤ : SimpleGraph (Fin 3)) W v ξ
      = W.toFun (ξ a) (ξ b) * (u (ξ a) * u (ξ b)) := by
    intro ξ
    rw [hnb, avoidingProduct, havoid, Finset.prod_insert (by simpa using hab),
      Finset.prod_singleton, Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  refine integral_pi_pair (F := fun y z => W.toFun y z * (u y * u z)) hab ?_
  exact W.measurable_uncurry.mul ((hu.comp measurable_fst).mul (hu.comp measurable_snd))

/-- **`expl:triangle-rooted`.**  `ℛ_{K₃,W}(u) = 3∫∫W(y,z)u(y)u(z)`. -/
theorem totalRootedDensity_triangle (W : Graphon) {u : ℝ → ℝ} (hu : Measurable u) :
    totalRootedDensity (⊤ : SimpleGraph (Fin 3)) W u
      = 3 * ∫ p, W.toFun p.1 p.2 * (u p.1 * u p.2) ∂gμ := by
  rw [totalRootedDensity, Fin.sum_univ_three, rootedDensity_triangle W hu,
    rootedDensity_triangle W hu, rootedDensity_triangle W hu]
  ring

/-! ### The three-vertex path -/

/-- Adjacency in the path graph is decidable. -/
instance : DecidableRel (SimpleGraph.pathGraph 3).Adj := fun a b =>
  decidable_of_iff' _ (SimpleGraph.pathGraph_adj (n := 3) (u := a) (v := b))

/-- Each oriented edge of `P₃` contributes the degree at the far endpoint. -/
private theorem path_edgeRemoved (W : Graphon) (x y : ℝ) {a b c : Fin 3}
    (hE : ((SimpleGraph.pathGraph 3).edgeFinset).erase s(a, b) = {s(c, b)})
    (hca : c ≠ a) (hcb : c ≠ b) (_hab : a ≠ b) :
    edgeRemovedDensity (SimpleGraph.pathGraph 3) W a b x y = W.deg y := by
  rw [edgeRemovedDensity, hE]
  have hpt : ∀ ξ : Fin 3 → ℝ,
      ∏ e ∈ ({s(c, b)} : Finset (Sym2 (Fin 3))), edgeVal W.toFun W.symm' (pin ξ a b x y) e
      = W.toFun y (ξ c) := by
    intro ξ
    rw [Finset.prod_singleton]
    have h2 : pin ξ a b x y b = y := by rw [pin, Function.update_self]
    have h3 : pin ξ a b x y c = ξ c := by
      rw [pin, Function.update_of_ne hcb, Function.update_of_ne hca]
    simp only [edgeVal, Sym2.lift_mk, h2, h3]
    rw [W.symm']
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_pi_eval c (W.measurable_right y)

/-- **`expl:path-derivative`.**  For `H = P₃`, averaging each edge over its two orientations
gives `½(d_W(x) + d_W(y))`, so the two edges give `𝒟_{P₃,W}(x,y) = d_W(x) + d_W(y)`. -/
theorem derivKernel_path (W : Graphon) (x y : ℝ) :
    derivKernel (SimpleGraph.pathGraph 3) W x y = W.deg x + W.deg y := by
  have k01 : edgeRemovedDensity (SimpleGraph.pathGraph 3) W 0 1 x y = W.deg y :=
    path_edgeRemoved W x y (c := 2) (by decide) (by decide) (by decide) (by decide)
  have k21 : edgeRemovedDensity (SimpleGraph.pathGraph 3) W 2 1 x y = W.deg y :=
    path_edgeRemoved W x y (c := 0) (by decide) (by decide) (by decide) (by decide)
  have k10 : edgeRemovedDensity (SimpleGraph.pathGraph 3) W 1 0 x y = W.deg x := by
    rw [edgeRemovedDensity, show ((SimpleGraph.pathGraph 3).edgeFinset).erase s(1, 0)
      = {s(1, 2)} from by decide]
    have hpt : ∀ ξ : Fin 3 → ℝ,
        ∏ e ∈ ({s(1, 2)} : Finset (Sym2 (Fin 3))),
          edgeVal W.toFun W.symm' (pin ξ 1 0 x y) e = W.toFun x (ξ 2) := by
      intro ξ
      rw [Finset.prod_singleton]
      have h1 : pin ξ 1 0 x y 1 = x := by
        rw [pin, Function.update_of_ne (by decide), Function.update_self]
      have h2 : pin ξ 1 0 x y 2 = ξ 2 := by
        rw [pin, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      simp only [edgeVal, Sym2.lift_mk, h1, h2]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_pi_eval 2 (W.measurable_right x)
  have k12 : edgeRemovedDensity (SimpleGraph.pathGraph 3) W 1 2 x y = W.deg x := by
    rw [edgeRemovedDensity, show ((SimpleGraph.pathGraph 3).edgeFinset).erase s(1, 2)
      = {s(0, 1)} from by decide]
    have hpt : ∀ ξ : Fin 3 → ℝ,
        ∏ e ∈ ({s(0, 1)} : Finset (Sym2 (Fin 3))),
          edgeVal W.toFun W.symm' (pin ξ 1 2 x y) e = W.toFun x (ξ 0) := by
      intro ξ
      rw [Finset.prod_singleton]
      have h1 : pin ξ 1 2 x y 1 = x := by
        rw [pin, Function.update_of_ne (by decide), Function.update_self]
      have h0 : pin ξ 1 2 x y 0 = ξ 0 := by
        rw [pin, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      simp only [edgeVal, Sym2.lift_mk, h1, h0]
      rw [W.symm']
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_pi_eval 0 (W.measurable_right x)
  rw [derivKernel, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  rw [if_neg (by decide), if_pos (by decide), if_neg (by decide),
    if_pos (by decide), if_neg (by decide), if_pos (by decide),
    if_neg (by decide), if_pos (by decide), if_neg (by decide),
    k01, k10, k12, k21]
  ring

/-- **`expl:path-rooted`.**  Rooting `P₃` at the middle vertex leaves no edge, so the rooted
density is `(∫u)²`. -/
theorem rootedDensity_path_mid (W : Graphon) {u : ℝ → ℝ} (hu : Measurable u) :
    rootedDensity (SimpleGraph.pathGraph 3) W 1 u = (∫ y, u y ∂unitμ) * ∫ y, u y ∂unitμ := by
  rw [rootedDensity]
  have hpt : ∀ ξ : Fin 3 → ℝ,
      (∏ z ∈ (SimpleGraph.pathGraph 3).neighborFinset 1, u (ξ z))
        * avoidingProduct (SimpleGraph.pathGraph 3) W 1 ξ = u (ξ 0) * u (ξ 2) := by
    intro ξ
    rw [show (SimpleGraph.pathGraph 3).neighborFinset 1 = {0, 2} from by decide,
      avoidingProduct,
      show ((SimpleGraph.pathGraph 3).edgeFinset.filter fun e => (1 : Fin 3) ∉ e) = ∅ from by
        decide,
      Finset.prod_empty, Finset.prod_insert (by decide), Finset.prod_singleton, mul_one]
  have hm2 : Measurable (Function.uncurry fun y z => u y * u z) :=
    (hu.comp measurable_fst).mul (hu.comp measurable_snd)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_pi_pair (F := fun y z => u y * u z) (by decide) hm2]
  exact integral_prod_mul (μ := unitμ) (ν := unitμ) u u

/-- **`expl:path-rooted`.**  Rooting `P₃` at an endpoint leaves the opposite edge, so the rooted
density is `∫d_W(y)u(y)dy`. -/
theorem rootedDensity_path_end (W : Graphon) {u : ℝ → ℝ} (hu : IsRow u) {v : Fin 3}
    (hv : v = 0 ∨ v = 2) :
    rootedDensity (SimpleGraph.pathGraph 3) W v u = ∫ y, u y * W.deg y ∂unitμ := by
  have hint : Integrable (fun p : ℝ × ℝ => u p.1 * W.toFun p.1 p.2) gμ :=
    integrable_of_abs_le ((hu.1.comp measurable_fst).mul W.measurable_uncurry) 1 fun p => by
      rw [abs_mul, abs_of_nonneg (hu.2 p.1).1, abs_of_nonneg (W.nonneg' p.1 p.2)]
      exact mul_le_one₀ (hu.2 p.1).2 (W.nonneg' p.1 p.2) (W.le_one' p.1 p.2)
  have hfub : ∫ p, u p.1 * W.toFun p.1 p.2 ∂gμ = ∫ y, u y * W.deg y ∂unitμ := by
    show ∫ p, u p.1 * W.toFun p.1 p.2 ∂(unitμ.prod unitμ) = _
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (∫ z, u y * W.toFun y z ∂unitμ) = u y * W.deg y
    rw [integral_const_mul, Graphon.deg]
  have hmW : Measurable (Function.uncurry fun y z => u y * W.toFun y z) :=
    (hu.1.comp measurable_fst).mul W.measurable_uncurry
  rcases hv with rfl | rfl
  · rw [rootedDensity]
    have hpt : ∀ ξ : Fin 3 → ℝ,
        (∏ z ∈ (SimpleGraph.pathGraph 3).neighborFinset 0, u (ξ z))
          * avoidingProduct (SimpleGraph.pathGraph 3) W 0 ξ
        = u (ξ 1) * W.toFun (ξ 1) (ξ 2) := by
      intro ξ
      rw [show (SimpleGraph.pathGraph 3).neighborFinset 0 = {1} from by decide,
        avoidingProduct,
        show ((SimpleGraph.pathGraph 3).edgeFinset.filter fun e => (0 : Fin 3) ∉ e)
          = {s(1, 2)} from by decide, Finset.prod_singleton, Finset.prod_singleton]
      simp only [edgeVal, Sym2.lift_mk]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_pi_pair (F := fun y z => u y * W.toFun y z) (by decide)
        hmW]
    exact hfub
  · rw [rootedDensity]
    have hpt : ∀ ξ : Fin 3 → ℝ,
        (∏ z ∈ (SimpleGraph.pathGraph 3).neighborFinset 2, u (ξ z))
          * avoidingProduct (SimpleGraph.pathGraph 3) W 2 ξ
        = u (ξ 1) * W.toFun (ξ 1) (ξ 0) := by
      intro ξ
      rw [show (SimpleGraph.pathGraph 3).neighborFinset 2 = {1} from by decide,
        avoidingProduct,
        show ((SimpleGraph.pathGraph 3).edgeFinset.filter fun e => (2 : Fin 3) ∉ e)
          = {s(0, 1)} from by decide, Finset.prod_singleton, Finset.prod_singleton]
      simp only [edgeVal, Sym2.lift_mk]
      rw [W.symm']
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_pi_pair (F := fun y z => u y * W.toFun y z) (by decide)
        hmW]
    exact hfub

/-- **`expl:path-rooted`.**  `ℛ_{P₃,W}(u) = (∫u)² + 2∫d_W(y)u(y)dy`. -/
theorem totalRootedDensity_path (W : Graphon) {u : ℝ → ℝ} (hu : IsRow u) :
    totalRootedDensity (SimpleGraph.pathGraph 3) W u
      = (∫ y, u y ∂unitμ) * (∫ y, u y ∂unitμ) + 2 * ∫ y, u y * W.deg y ∂unitμ := by
  rw [totalRootedDensity, Fin.sum_univ_three,
    rootedDensity_path_end W hu (Or.inl rfl), rootedDensity_path_mid W hu.1,
    rootedDensity_path_end W hu (Or.inr rfl)]
  ring

end UpperTailMultipodality
