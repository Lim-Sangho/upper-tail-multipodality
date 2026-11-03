import UpperTailMultipodality.Insertion.Split

/-!
# The graphon with an inserted block

For `θ ∈ (0,1)`, a value `q ∈ [0,1]`, a row `u` and a graphon `K`, `insertGraphon θ q u K` is the
graphon of `eq:vertex-insertion`: a new block `[0,θ)` with value `q` on itself and row `u`
towards the old vertices, and `K`, rescaled from `[0,1]` to `[θ,1]`, on the old vertices.  It is
`blockKernel q u K` composed with the relabelling `insertMap θ`, where `blockKernel` treats the
negative reals as the new block.

* `edgeDensity_insertGraphon`, `Ip_insertGraphon` —
  `∫∫ g(W_θ) = θ² g(q) + 2θ(1-θ) ∫ g(u) + (1-θ)² ∫∫ g(K)`;
* `tDensity_insertGraphon` — `t(H, W_θ) = ∑_S θ^{|S|}(1-θ)^{N-|S|} T_S`, where the block density
  `T_S = blockDensity H S q u K` does not depend on `θ`;
* `blockDensity_empty` — `T_∅ = t(H,K)`; `blockDensity_singleton` — `T_{v} = ℛ_{v,W}(u)`.
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

/-- The kernel of the inserted graphon in relabelled coordinates: the negative reals form the new
block, with value `q` on itself and row `u` towards the old vertices, which carry `K`. -/
noncomputable def blockKernel (q : ℝ) (u : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x < 0 then (if y < 0 then q else u y) else (if y < 0 then u x else K x y)

/-- `blockKernel q u K` is symmetric when `K` is. -/
theorem blockKernel_symm (q : ℝ) (u : ℝ → ℝ) {K : ℝ → ℝ → ℝ} (hK : ∀ x y, K x y = K y x)
    (x y : ℝ) : blockKernel q u K x y = blockKernel q u K y x := by
  unfold blockKernel
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy, hK x y]

/-- `blockKernel q u K` is jointly measurable. -/
theorem measurable_blockKernel (q : ℝ) {u : ℝ → ℝ} (hu : Measurable u) {K : ℝ → ℝ → ℝ}
    (hK : Measurable (Function.uncurry K)) :
    Measurable (fun z : ℝ × ℝ => blockKernel q u K z.1 z.2) := by
  unfold blockKernel
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
      (hu.comp measurable_snd))
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const) (hu.comp measurable_fst) hK)

/-- `blockKernel q u K` takes values in `[0,1]` when `q`, `u` and `K` do. -/
theorem blockKernel_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ}
    (hu : ∀ y, u y ∈ Set.Icc (0:ℝ) 1) {K : ℝ → ℝ → ℝ} (hK : ∀ x y, K x y ∈ Set.Icc (0:ℝ) 1)
    (x y : ℝ) : blockKernel q u K x y ∈ Set.Icc (0:ℝ) 1 := by
  unfold blockKernel
  split_ifs
  exacts [hq, hu y, hu x, hK x y]

/-- On the old vertices, `blockKernel q u K = K`. -/
theorem blockKernel_of_nonneg (q : ℝ) (u : ℝ → ℝ) (K : ℝ → ℝ → ℝ) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : blockKernel q u K x y = K x y := by
  simp [blockKernel, not_lt.2 hx, not_lt.2 hy]

/-- Between the new block and an old vertex, `blockKernel q u K = u`. -/
theorem blockKernel_neg_left (q : ℝ) (u : ℝ → ℝ) (K : ℝ → ℝ → ℝ) {y : ℝ} (hy : 0 ≤ y) :
    blockKernel q u K (-1) y = u y := by
  simp [blockKernel, not_lt.2 hy]

/-! ### Almost every point of `[0,1]` is nonnegative -/

/-- Almost every point of `[0,1]` is nonnegative. -/
theorem ae_nonneg_unitμ : ∀ᵐ y ∂unitμ, 0 ≤ y := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy using hy.1

/-- Almost every point of `[0,1]²` has nonnegative coordinates. -/
theorem ae_nonneg_gμ : ∀ᵐ z ∂gμ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
  have h1 : ∀ᵐ z ∂gμ, 0 ≤ z.1 := Measure.quasiMeasurePreserving_fst.ae ae_nonneg_unitμ
  have h2 : ∀ᵐ z ∂gμ, 0 ≤ z.2 := Measure.quasiMeasurePreserving_snd.ae ae_nonneg_unitμ
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

/-- Almost every point of `[0,1]^V` has nonnegative coordinates. -/
theorem ae_nonneg_pi {V : Type*} [Fintype V] :
    ∀ᵐ y ∂(Measure.pi fun _ : V => unitμ), ∀ v, 0 ≤ y v := by
  rw [ae_all_iff]
  intro v
  exact (measurePreserving_eval (μ := fun _ : V => unitμ) v).quasiMeasurePreserving.ae
    ae_nonneg_unitμ

/-! ### Clamping a kernel into a graphon -/

/-- The graphon `max 0 (min 1 K)`. -/
noncomputable def clampKernel (K : Kernel) : Graphon where
  toFun x y := max 0 (min 1 (K.toFun x y))
  symm' x y := by rw [K.symm']
  meas' := measurable_const.max (measurable_const.min K.meas')
  nonneg' _ _ := le_max_left _ _
  le_one' _ _ := max_le zero_le_one (min_le_left _ _)

/-- Clamping does nothing to a kernel with values in `[0,1]`. -/
theorem clampKernel_apply_of_mem {K : Kernel} (hK : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1)
    (x y : ℝ) : (clampKernel K).toFun x y = K.toFun x y := by
  show max 0 (min 1 (K.toFun x y)) = K.toFun x y
  rw [min_eq_right (hK x y).2, max_eq_right (hK x y).1]

/-! ### The inserted graphon -/

/-- **The graphon with an inserted block**: a block `[0,θ)` with value `q` and row `u`, and the
graphon `K` rescaled onto `[θ,1]`. -/
noncomputable def insertGraphon (θ q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (u : ℝ → ℝ) (hu : IsRow u)
    (K : Graphon) : Graphon where
  toFun x y := blockKernel q u K.toFun (insertMap θ x) (insertMap θ y)
  symm' _ _ := blockKernel_symm q u K.symm' _ _
  meas' := (measurable_blockKernel q hu.1 K.meas').comp
    ((measurable_insertMap θ).prodMap (measurable_insertMap θ))
  nonneg' _ _ := (blockKernel_mem_Icc hq hu.2 K.mem_Icc _ _).1
  le_one' _ _ := (blockKernel_mem_Icc hq hu.2 K.mem_Icc _ _).2

/-- `∫∫ g(W_θ) = θ² g(q) + 2θ(1-θ) ∫ g(u) + (1-θ)² ∫∫ g(K)` for `g` bounded on `[0,1]`. -/
theorem integral_comp_insertGraphon {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (K : Graphon) {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ t ∈ Set.Icc (0:ℝ) 1, |g t| ≤ C) :
    ∫ z, g ((insertGraphon θ q hq u hu K).toFun z.1 z.2) ∂gμ
      = θ ^ 2 * g q + 2 * θ * (1 - θ) * ∫ y, g (u y) ∂unitμ
        + (1 - θ) ^ 2 * ∫ z, g (K.toFun z.1 z.2) ∂gμ := by
  have hG : Measurable fun z : ℝ × ℝ => g (blockKernel q u K.toFun z.1 z.2) :=
    hg.comp (measurable_blockKernel q hu.1 K.meas')
  have hGb : ∀ z : ℝ × ℝ, |g (blockKernel q u K.toFun z.1 z.2)| ≤ C :=
    fun z => hC _ (blockKernel_mem_Icc hq hu.2 K.mem_Icc _ _)
  have key := integral_gμ_insertMap hθ0 hθ1 hG hGb
  have e1 : ∫ y, g (blockKernel q u K.toFun (-1) y) ∂unitμ = ∫ y, g (u y) ∂unitμ :=
    integral_congr_ae (ae_nonneg_unitμ.mono fun y hy => by
      simp only [blockKernel_neg_left q u K.toFun hy])
  have e2 : ∫ x, g (blockKernel q u K.toFun x (-1)) ∂unitμ = ∫ y, g (u y) ∂unitμ := by
    refine integral_congr_ae (ae_nonneg_unitμ.mono fun y hy => ?_)
    simp only [blockKernel_symm q u K.symm' y (-1), blockKernel_neg_left q u K.toFun hy]
  have e3 : ∫ z, g (blockKernel q u K.toFun z.1 z.2) ∂gμ = ∫ z, g (K.toFun z.1 z.2) ∂gμ :=
    integral_congr_ae (ae_nonneg_gμ.mono fun z hz => by
      simp only [blockKernel_of_nonneg q u K.toFun hz.1 hz.2])
  have e0 : blockKernel q u K.toFun (-1) (-1) = q := by simp [blockKernel]
  show ∫ z, g (blockKernel q u K.toFun (insertMap θ z.1) (insertMap θ z.2)) ∂gμ = _
  rw [key, e1, e2, e3, e0]
  ring

/-- `e(W_θ) = θ² q + 2θ(1-θ) ∫ u + (1-θ)² e(K)`. -/
theorem edgeDensity_insertGraphon {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (K : Graphon) :
    (insertGraphon θ q hq u hu K).edgeDensity
      = θ ^ 2 * q + 2 * θ * (1 - θ) * ∫ y, u y ∂unitμ + (1 - θ) ^ 2 * K.edgeDensity := by
  have h := integral_comp_insertGraphon hθ0 hθ1 hq hu K (g := id) measurable_id (C := 1)
    (fun t ht => by rw [id, abs_le]; exact ⟨by linarith [ht.1], ht.2⟩)
  exact h

/-- `I_p(W_θ) = θ² J_p(q) + 2θ(1-θ) ∫ J_p(u) + (1-θ)² I_p(K)`. -/
theorem Ip_insertGraphon {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (K : Graphon) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    (insertGraphon θ q hq u hu K).Ip p
      = θ ^ 2 * Jp p q + 2 * θ * (1 - θ) * ∫ y, Jp p (u y) ∂unitμ + (1 - θ) ^ 2 * K.Ip p := by
  obtain ⟨t₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one' ℝ)) (continuousOn_Jp_Icc hp0 hp1).abs
  exact integral_comp_insertGraphon hθ0 hθ1 hq hu K (measurable_Jp p) (C := |Jp p t₀|)
    (fun t ht => hmax ht)

/-! ### The block densities `T_S` -/

section Block

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The block density `T_S`: the homomorphism density of `H` in `blockKernel q u K` with the
vertices of `S` in the new block. -/
noncomputable def blockDensity (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (q : ℝ)
    (u : ℝ → ℝ) (K : Kernel) : ℝ :=
  ∫ y, ∏ e ∈ H.edgeFinset, edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm')
    (pinNew S y) e ∂(Measure.pi fun _ : V => unitμ)

omit [Fintype V] [DecidableEq V] in
/-- An edge factor of a measurable symmetric kernel is measurable in the vertex assignment. -/
theorem measurable_edgeVal {L : ℝ → ℝ → ℝ} (hL : ∀ x y, L x y = L y x)
    (hLm : Measurable fun z : ℝ × ℝ => L z.1 z.2) (e : Sym2 V) :
    Measurable fun x : V → ℝ => edgeVal L hL x e := by
  induction e using Sym2.ind with
  | _ a b =>
    show Measurable fun x : V → ℝ => L (x a) (x b)
    have hpair : Measurable fun x : V → ℝ => (x a, x b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    exact hLm.comp hpair

omit [Fintype V] [DecidableEq V] in
/-- An edge factor of a kernel with values in `[0,1]` lies in `[0,1]`. -/
theorem edgeVal_mem_Icc {L : ℝ → ℝ → ℝ} (hL : ∀ x y, L x y = L y x)
    (hLb : ∀ x y, L x y ∈ Set.Icc (0:ℝ) 1) (x : V → ℝ) (e : Sym2 V) :
    edgeVal L hL x e ∈ Set.Icc (0:ℝ) 1 := by
  induction e using Sym2.ind with
  | _ a b => exact hLb (x a) (x b)

omit [DecidableEq V] in
/-- The product of edge factors of a kernel with values in `[0,1]` lies in `[0,1]`. -/
theorem prod_edgeVal_mem_Icc (H : SimpleGraph V) [DecidableRel H.Adj] {L : ℝ → ℝ → ℝ}
    (hL : ∀ x y, L x y = L y x) (hLb : ∀ x y, L x y ∈ Set.Icc (0:ℝ) 1) (x : V → ℝ) :
    ∏ e ∈ H.edgeFinset, edgeVal L hL x e ∈ Set.Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg fun e _ => (edgeVal_mem_Icc hL hLb x e).1,
    Finset.prod_le_one (fun e _ => (edgeVal_mem_Icc hL hLb x e).1)
      (fun e _ => (edgeVal_mem_Icc hL hLb x e).2)⟩

/-- **`t(H, W_θ) = ∑_{S ⊆ V} θ^{|S|}(1-θ)^{N-|S|} T_S`.** -/
theorem tDensity_insertGraphon (H : SimpleGraph V) [DecidableRel H.Adj] {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (K : Graphon) :
    (insertGraphon θ q hq u hu K).tDensity H
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          θ ^ S.card * (1 - θ) ^ Sᶜ.card * blockDensity H S q u (Kernel.ofGraphon K) := by
  have hLm := measurable_blockKernel q hu.1 K.meas'
  have hLb := blockKernel_mem_Icc hq hu.2 K.mem_Icc
  have hG : Measurable fun x : V → ℝ =>
      ∏ e ∈ H.edgeFinset, edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') x e :=
    Finset.measurable_prod _ fun e _ => measurable_edgeVal _ hLm e
  have hGb : ∀ x : V → ℝ,
      |∏ e ∈ H.edgeFinset, edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') x e|
        ≤ 1 := fun x => by
    have h := prod_edgeVal_mem_Icc H (blockKernel_symm q u K.symm') hLb x
    rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  exact integral_pi_insertMap hθ0 hθ1 hG hGb

/-- `T_S` depends on the kernel only through its values. -/
theorem blockDensity_congr (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (q : ℝ)
    (u : ℝ → ℝ) {K K' : Kernel} (h : K.toFun = K'.toFun) :
    blockDensity H S q u K = blockDensity H S q u K' := by
  obtain ⟨f, _, _, _⟩ := K
  obtain ⟨f', _, _, _⟩ := K'
  cases h
  rfl

/-- `T_∅ = t(H,K)`. -/
theorem blockDensity_empty (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ) (u : ℝ → ℝ)
    (K : Kernel) : blockDensity H ∅ q u K = K.tDensity H := by
  unfold blockDensity Kernel.tDensity
  refine integral_congr_ae (ae_nonneg_pi.mono fun y hy => Finset.prod_congr rfl fun e _ => ?_)
  induction e using Sym2.ind with
  | _ a b =>
    show blockKernel q u K.toFun (pinNew ∅ y a) (pinNew ∅ y b) = K.toFun (y a) (y b)
    simp only [pinNew, Finset.notMem_empty, if_false]
    exact blockKernel_of_nonneg q u K.toFun (hy a) (hy b)

/-- The edges of `H` at `v` are the pairs `s(v,z)` with `z` a neighbour of `v`. -/
theorem filter_mem_edgeFinset_eq_image (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    H.edgeFinset.filter (fun e => v ∈ e) = (H.neighborFinset v).image (fun z => s(v, z)) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Sym2.mem_iff, Finset.mem_image, SimpleGraph.mem_neighborFinset, Sym2.eq_iff]
    constructor
    · rintro ⟨h, rfl | rfl⟩
      · exact ⟨b, h, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨a, h.symm, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨z, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨h, Or.inl rfl⟩
      · exact ⟨h.symm, Or.inr rfl⟩

/-- `T_{v} = ℛ_{v,W}(u)`. -/
theorem blockDensity_singleton (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (q : ℝ)
    (u : ℝ → ℝ) (W : Graphon) :
    blockDensity H {v} q u (Kernel.ofGraphon W) = rootedDensity H W v u := by
  unfold blockDensity rootedDensity
  refine integral_congr_ae (ae_nonneg_pi.mono fun y hy => ?_)
  beta_reduce
  rw [← Finset.prod_filter_mul_prod_filter_not H.edgeFinset (fun e => v ∈ e),
    filter_mem_edgeFinset_eq_image H v,
    Finset.prod_image (fun z _ z' _ h => Sym2.congr_right.1 h)]
  congr 1
  · refine Finset.prod_congr rfl fun z hz => ?_
    have hzv : z ≠ v := (SimpleGraph.mem_neighborFinset H v z |>.1 hz).ne.symm
    show blockKernel q u W.toFun (pinNew {v} y v) (pinNew {v} y z) = u (y z)
    simp only [pinNew, Finset.mem_singleton, if_true, hzv, if_false]
    exact blockKernel_neg_left q u W.toFun (hy z)
  · unfold avoidingProduct
    refine Finset.prod_congr rfl fun e he => ?_
    have hve : v ∉ e := (Finset.mem_filter.1 he).2
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ≠ v := fun h => hve (h ▸ Sym2.mem_mk_left a b)
      have hb : b ≠ v := fun h => hve (h ▸ Sym2.mem_mk_right a b)
      show blockKernel q u W.toFun (pinNew {v} y a) (pinNew {v} y b) = W.toFun (y a) (y b)
      simp only [pinNew, Finset.mem_singleton, ha, hb, if_false]
      exact blockKernel_of_nonneg q u W.toFun (hy a) (hy b)

end Block

end UpperTailMultipodality.Insertion
