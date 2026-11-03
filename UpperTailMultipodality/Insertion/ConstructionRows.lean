import UpperTailMultipodality.Insertion.Construction
import UpperTailMultipodality.Insertion.SplitRows
import UpperTailMultipodality.RowCriterion.Finiteness.Coordinates
import UpperTailMultipodality.RowCriterion.Rows.Resampling

/-!
# The graphon with an inserted block carrying several rows

For `θ ∈ (0,1)`, a value `q ∈ [0,1]`, a row kernel `U` and a graphon `K`,
`insertGraphonRows θ q U K` is the graphon of `lem:insertion-first-order`: a new block `[0,θ)`
with value `q` on itself and, at the label `t`, the row `U t` towards the old vertices, which
carry `K` rescaled from `[0,1]` to `[θ,1]`.

Taking `U` constant on the intervals of a partition of `[0,1]` of lengths `c_i/c` realizes the
`k` new blocks of measures `θc_i` with rows `u_i` of `lem:insertion-first-order`; this is what
makes the cone of `lem:upper-tail-multiplier` convex.

* `integral_comp_insertGraphonRows` —
  `∫∫ g(W_θ) = θ² g(q) + 2θ(1-θ) ∫∫ g(U) + (1-θ)² ∫∫ g(K)`;
* `tDensity_insertGraphonRows` — `t(H, W_θ) = ∑_S θ^{|S|}(1-θ)^{N-|S|} T_S`, where the block
  density `T_S = blockDensityRows H S q U K` does not depend on `θ`;
* `blockDensityRows_empty` — `T_∅ = t(H,K)`;
  `blockDensityRows_singleton` — `T_{v} = ∫₀¹ ℛ_{v,K}(U t) dt`.
-/

namespace UpperTailMultipodality.Insertion

open MeasureTheory Filter Topology

/-- A *row kernel*: a jointly measurable `U : [0,1]² → [0,1]`, where `U t` is the row of the new
vertex with label `t`. -/
def IsRows (U : ℝ → ℝ → ℝ) : Prop :=
  Measurable (fun z : ℝ × ℝ => U z.1 z.2) ∧ ∀ t y, U t y ∈ Set.Icc (0:ℝ) 1

/-- A single row is a constant row kernel. -/
theorem isRows_const {u : ℝ → ℝ} (hu : IsRow u) : IsRows (fun _ => u) :=
  ⟨hu.1.comp measurable_snd, fun _ y => hu.2 y⟩

/-- The kernel of the inserted graphon in relabelled coordinates: the negative reals form the
new block, with value `q` on itself and, at the label `t - 1`, the row `U t` towards the old
vertices, which carry `K`. -/
noncomputable def blockKernelRows (q : ℝ) (U : ℝ → ℝ → ℝ) (K : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x < 0 then (if y < 0 then q else U (x + 1) y)
  else (if y < 0 then U (y + 1) x else K x y)

/-- `blockKernelRows q U K` is symmetric when `K` is. -/
theorem blockKernelRows_symm (q : ℝ) (U : ℝ → ℝ → ℝ) {K : ℝ → ℝ → ℝ}
    (hK : ∀ x y, K x y = K y x) (x y : ℝ) :
    blockKernelRows q U K x y = blockKernelRows q U K y x := by
  unfold blockKernelRows
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy, hK x y]

/-- `blockKernelRows q U K` is jointly measurable. -/
theorem measurable_blockKernelRows (q : ℝ) {U : ℝ → ℝ → ℝ}
    (hU : Measurable (fun z : ℝ × ℝ => U z.1 z.2)) {K : ℝ → ℝ → ℝ}
    (hK : Measurable (Function.uncurry K)) :
    Measurable (fun z : ℝ × ℝ => blockKernelRows q U K z.1 z.2) := by
  have h1 : Measurable fun z : ℝ × ℝ => U (z.1 + 1) z.2 :=
    hU.comp ((measurable_fst.add measurable_const).prodMk measurable_snd)
  have h2 : Measurable fun z : ℝ × ℝ => U (z.2 + 1) z.1 :=
    hU.comp ((measurable_snd.add measurable_const).prodMk measurable_fst)
  unfold blockKernelRows
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const h1)
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const) h2 hK)

/-- `blockKernelRows q U K` takes values in `[0,1]` when `q`, `U` and `K` do. -/
theorem blockKernelRows_mem_Icc {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ}
    (hU : ∀ t y, U t y ∈ Set.Icc (0:ℝ) 1) {K : ℝ → ℝ → ℝ}
    (hK : ∀ x y, K x y ∈ Set.Icc (0:ℝ) 1) (x y : ℝ) :
    blockKernelRows q U K x y ∈ Set.Icc (0:ℝ) 1 := by
  unfold blockKernelRows
  split_ifs
  exacts [hq, hU _ y, hU _ x, hK x y]

/-- On the old vertices, `blockKernelRows q U K = K`. -/
theorem blockKernelRows_of_nonneg (q : ℝ) (U : ℝ → ℝ → ℝ) (K : ℝ → ℝ → ℝ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : blockKernelRows q U K x y = K x y := by
  simp [blockKernelRows, not_lt.2 hx, not_lt.2 hy]

/-- Between the new vertex with label `newLabel t` and an old vertex `y`,
`blockKernelRows q U K = U t y`. -/
theorem blockKernelRows_newLabel_left (q : ℝ) (U : ℝ → ℝ → ℝ) (K : ℝ → ℝ → ℝ) {t y : ℝ}
    (ht : t < 1) (hy : 0 ≤ y) : blockKernelRows q U K (newLabel t) y = U t y := by
  have h1 : newLabel t < 0 := by unfold newLabel; linarith
  have h2 : newLabel t + 1 = t := by unfold newLabel; ring
  simp only [blockKernelRows, if_pos h1, if_neg (not_lt.2 hy), h2]

/-- Both coordinates in the new block: `blockKernelRows q U K = q`. -/
theorem blockKernelRows_newLabel_both (q : ℝ) (U : ℝ → ℝ → ℝ) (K : ℝ → ℝ → ℝ) {s t : ℝ}
    (hs : s < 1) (ht : t < 1) : blockKernelRows q U K (newLabel s) (newLabel t) = q := by
  have h1 : newLabel s < 0 := by unfold newLabel; linarith
  have h2 : newLabel t < 0 := by unfold newLabel; linarith
  simp only [blockKernelRows, if_pos h1, if_pos h2]

/-- **The graphon with an inserted block carrying several rows.** -/
noncomputable def insertGraphonRows (θ q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (U : ℝ → ℝ → ℝ)
    (hU : IsRows U) (K : Graphon) : Graphon where
  toFun x y := blockKernelRows q U K.toFun (insertMapRows θ x) (insertMapRows θ y)
  symm' _ _ := blockKernelRows_symm q U K.symm' _ _
  meas' := (measurable_blockKernelRows q hU.1 K.meas').comp
    ((measurable_insertMapRows θ).prodMap (measurable_insertMapRows θ))
  nonneg' _ _ := (blockKernelRows_mem_Icc hq hU.2 K.mem_Icc _ _).1
  le_one' _ _ := (blockKernelRows_mem_Icc hq hU.2 K.mem_Icc _ _).2

/-- `∫∫ g(W_θ) = θ² g(q) + 2θ(1-θ) ∫∫ g(U) + (1-θ)² ∫∫ g(K)` for `g` bounded on `[0,1]`. -/
theorem integral_comp_insertGraphonRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) (K : Graphon) {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ t ∈ Set.Icc (0:ℝ) 1, |g t| ≤ C) :
    ∫ z, g ((insertGraphonRows θ q hq U hU K).toFun z.1 z.2) ∂gμ
      = θ ^ 2 * g q + 2 * θ * (1 - θ) * ∫ z, g (U z.1 z.2) ∂gμ
        + (1 - θ) ^ 2 * ∫ z, g (K.toFun z.1 z.2) ∂gμ := by
  have hG : Measurable fun z : ℝ × ℝ => g (blockKernelRows q U K.toFun z.1 z.2) :=
    hg.comp (measurable_blockKernelRows q hU.1 K.meas')
  have hGb : ∀ z : ℝ × ℝ, |g (blockKernelRows q U K.toFun z.1 z.2)| ≤ C :=
    fun z => hC _ (blockKernelRows_mem_Icc hq hU.2 K.mem_Icc _ _)
  have key := integral_gμ_insertMapRows hθ0 hθ1 hG hGb
  -- the three pieces
  have e11 : ∫ z, g (blockKernelRows q U K.toFun (newLabel z.1) (newLabel z.2)) ∂gμ = g q := by
    rw [integral_congr_ae (ae_mem_Ico_gμ.mono fun z hz => by
      show g (blockKernelRows q U K.toFun (newLabel z.1) (newLabel z.2)) = g q
      rw [blockKernelRows_newLabel_both q U K.toFun hz.1.2 hz.2.2])]
    simp
  have e12 : ∫ z, g (blockKernelRows q U K.toFun (newLabel z.1) z.2) ∂gμ
      = ∫ z, g (U z.1 z.2) ∂gμ :=
    integral_congr_ae (ae_mem_Ico_gμ.mono fun z hz => by
      show g (blockKernelRows q U K.toFun (newLabel z.1) z.2) = g (U z.1 z.2)
      rw [blockKernelRows_newLabel_left q U K.toFun hz.1.2 hz.2.1])
  have e21 : ∫ z, g (blockKernelRows q U K.toFun z.1 (newLabel z.2)) ∂gμ
      = ∫ z, g (U z.1 z.2) ∂gμ := by
    have hstep : ∫ z, g (blockKernelRows q U K.toFun z.1 (newLabel z.2)) ∂gμ
        = ∫ z, g (U z.2 z.1) ∂gμ :=
      integral_congr_ae (ae_mem_Ico_gμ.mono fun z hz => by
        show g (blockKernelRows q U K.toFun z.1 (newLabel z.2)) = g (U z.2 z.1)
        rw [blockKernelRows_symm q U K.symm',
          blockKernelRows_newLabel_left q U K.toFun hz.2.2 hz.1.1])
    have hmp : MeasurePreserving Prod.swap gμ gμ := by
      rw [gμ]; exact Measure.measurePreserving_swap
    have hmeas : Measurable fun z : ℝ × ℝ => g (U z.1 z.2) := hg.comp hU.1
    have hswap : ∫ z, g (U z.1 z.2) ∂gμ = ∫ z, g (U z.2 z.1) ∂gμ := by
      conv_lhs => rw [← hmp.map_eq]
      rw [integral_map measurable_swap.aemeasurable hmeas.aestronglyMeasurable]
      rfl
    rw [hstep, hswap]
  show ∫ z, g (blockKernelRows q U K.toFun (insertMapRows θ z.1) (insertMapRows θ z.2)) ∂gμ = _
  have hKold : ∫ z, g (blockKernelRows q U K.toFun z.1 z.2) ∂gμ
      = ∫ z, g (K.toFun z.1 z.2) ∂gμ :=
    integral_congr_ae (ae_nonneg_gμ.mono fun z hz => by
      show g (blockKernelRows q U K.toFun z.1 z.2) = g (K.toFun z.1 z.2)
      rw [blockKernelRows_of_nonneg q U K.toFun hz.1 hz.2])
  rw [key, e11, e12, e21, hKold]
  ring

/-- `e(W_θ) = θ² q + 2θ(1-θ) ∫∫ U + (1-θ)² e(K)`. -/
theorem edgeDensity_insertGraphonRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) (K : Graphon) :
    (insertGraphonRows θ q hq U hU K).edgeDensity
      = θ ^ 2 * q + 2 * θ * (1 - θ) * ∫ z, U z.1 z.2 ∂gμ
        + (1 - θ) ^ 2 * K.edgeDensity :=
  integral_comp_insertGraphonRows hθ0 hθ1 hq hU K (g := id) measurable_id (C := 1)
    (fun t ht => by rw [id, abs_le]; exact ⟨by linarith [ht.1], ht.2⟩)

/-- `I_p(W_θ) = θ² J_p(q) + 2θ(1-θ) ∫∫ J_p(U) + (1-θ)² I_p(K)`. -/
theorem Ip_insertGraphonRows {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ} (hU : IsRows U) (K : Graphon) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (insertGraphonRows θ q hq U hU K).Ip p
      = θ ^ 2 * Jp p q + 2 * θ * (1 - θ) * ∫ z, Jp p (U z.1 z.2) ∂gμ
        + (1 - θ) ^ 2 * K.Ip p := by
  obtain ⟨t₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one' ℝ)) (continuousOn_Jp_Icc hp0 hp1).abs
  exact integral_comp_insertGraphonRows hθ0 hθ1 hq hU K (measurable_Jp p) (C := |Jp p t₀|)
    (fun t ht => hmax ht)

/-! ### Mixing two row kernels -/

/-- **The mixture of two row kernels** with weight `lam`: the label space of the new block is
split into a part of measure `lam` carrying `U₁` and a part of measure `1 - lam` carrying
`U₂`. -/
noncomputable def mixRows (lam : ℝ) (U₁ U₂ : ℝ → ℝ → ℝ) (t : ℝ) (y : ℝ) : ℝ :=
  if insertMapRows lam t < 0 then U₁ (insertMapRows lam t + 1) y else U₂ (insertMapRows lam t) y

/-- A mixture of row kernels is a row kernel. -/
theorem isRows_mixRows (lam : ℝ) {U₁ U₂ : ℝ → ℝ → ℝ} (hU₁ : IsRows U₁) (hU₂ : IsRows U₂) :
    IsRows (mixRows lam U₁ U₂) := by
  refine ⟨?_, fun t y => ?_⟩
  · have hm : Measurable fun z : ℝ × ℝ => insertMapRows lam z.1 :=
      (measurable_insertMapRows lam).comp measurable_fst
    have h1 : Measurable fun z : ℝ × ℝ => U₁ (insertMapRows lam z.1 + 1) z.2 := by
      have hp : Measurable fun z : ℝ × ℝ =>
          ((insertMapRows lam z.1 + 1, z.2) : ℝ × ℝ) :=
        (hm.add measurable_const).prodMk measurable_snd
      have h := hU₁.1.comp hp
      exact h
    have h2 : Measurable fun z : ℝ × ℝ => U₂ (insertMapRows lam z.1) z.2 := by
      have hp : Measurable fun z : ℝ × ℝ => ((insertMapRows lam z.1, z.2) : ℝ × ℝ) :=
        hm.prodMk measurable_snd
      have h := hU₂.1.comp hp
      exact h
    exact Measurable.ite (measurableSet_lt hm measurable_const) h1 h2
  · unfold mixRows
    split_ifs
    exacts [hU₁.2 _ y, hU₂.2 _ y]

/-- **A convex combination of row functionals is realized by the mixture of the row kernels.**
This is what makes the cone of `lem:upper-tail-multiplier` convex. -/
theorem integral_mixRows {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (U₁ U₂ : ℝ → ℝ → ℝ)
    {Φ : (ℝ → ℝ) → ℝ} {C : ℝ} (hm₁ : Measurable fun t => Φ (U₁ t))
    (hm₂ : Measurable fun t => Φ (U₂ t)) (hb₁ : ∀ t, |Φ (U₁ t)| ≤ C)
    (hb₂ : ∀ t, |Φ (U₂ t)| ≤ C) :
    ∫ t, Φ (mixRows lam U₁ U₂ t) ∂unitμ
      = lam * ∫ t, Φ (U₁ t) ∂unitμ + (1 - lam) * ∫ t, Φ (U₂ t) ∂unitμ := by
  set Ψ : ℝ → ℝ := fun x => if x < 0 then Φ (U₁ (x + 1)) else Φ (U₂ x) with hΨdef
  have hΨm : Measurable Ψ := by
    rw [hΨdef]
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (hm₁.comp (measurable_id.add measurable_const)) hm₂
  have hΨb : ∀ x, |Ψ x| ≤ C := by
    intro x
    rw [hΨdef]
    dsimp only
    split_ifs
    exacts [hb₁ _, hb₂ x]
  have hpt : ∀ t, Φ (mixRows lam U₁ U₂ t) = Ψ (insertMapRows lam t) := by
    intro t
    rw [hΨdef]
    dsimp only
    by_cases hx : insertMapRows lam t < 0
    · rw [if_pos hx]
      congr 1
      funext y
      rw [mixRows, if_pos hx]
    · rw [if_neg hx]
      congr 1
      funext y
      rw [mixRows, if_neg hx]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_insertMapRows h0 h1 hΨm hΨb]
  congr 2
  · refine integral_congr_ae (ae_mem_Ico_unitμ.mono fun s hs => ?_)
    have hneg : newLabel s < 0 := by unfold newLabel; linarith [hs.2]
    rw [hΨdef]
    dsimp only
    rw [if_pos hneg]
    congr 2
    unfold newLabel
    ring
  · refine integral_congr_ae (ae_nonneg_unitμ.mono fun s hs => ?_)
    rw [hΨdef]
    dsimp only
    rw [if_neg (not_lt.2 hs)]

/-! ### The block densities `T_S` -/

section Block

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The block density `T_S`: the homomorphism density of `H` in `blockKernelRows q U K` with the
vertices of `S` in the new block. -/
noncomputable def blockDensityRows (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V)
    (q : ℝ) (U : ℝ → ℝ → ℝ) (K : Kernel) : ℝ :=
  ∫ y, ∏ e ∈ H.edgeFinset, edgeVal (blockKernelRows q U K.toFun)
    (blockKernelRows_symm q U K.symm') (pinNewRows S y) e ∂(Measure.pi fun _ : V => unitμ)

/-- **`t(H, W_θ) = ∑_{S ⊆ V} θ^{|S|}(1-θ)^{N-|S|} T_S`.** -/
theorem tDensity_insertGraphonRows (H : SimpleGraph V) [DecidableRel H.Adj] {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {U : ℝ → ℝ → ℝ}
    (hU : IsRows U) (K : Graphon) :
    (insertGraphonRows θ q hq U hU K).tDensity H
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          θ ^ S.card * (1 - θ) ^ Sᶜ.card * blockDensityRows H S q U (Kernel.ofGraphon K) := by
  have hLm := measurable_blockKernelRows q hU.1 K.meas'
  have hLb := blockKernelRows_mem_Icc hq hU.2 K.mem_Icc
  have hG : Measurable fun x : V → ℝ => ∏ e ∈ H.edgeFinset,
      edgeVal (blockKernelRows q U K.toFun) (blockKernelRows_symm q U K.symm') x e :=
    Finset.measurable_prod _ fun e _ => measurable_edgeVal _ hLm e
  have hGb : ∀ x : V → ℝ, |∏ e ∈ H.edgeFinset, edgeVal (blockKernelRows q U K.toFun)
      (blockKernelRows_symm q U K.symm') x e| ≤ 1 := fun x => by
    have h := prod_edgeVal_mem_Icc H (blockKernelRows_symm q U K.symm') hLb x
    rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  exact integral_pi_insertMapRows hθ0 hθ1 hG hGb

/-- `T_S` depends on the kernel only through its values. -/
theorem blockDensityRows_congr (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (q : ℝ)
    (U : ℝ → ℝ → ℝ) {K K' : Kernel} (h : K.toFun = K'.toFun) :
    blockDensityRows H S q U K = blockDensityRows H S q U K' := by
  obtain ⟨f, _, _, _⟩ := K
  obtain ⟨f', _, _, _⟩ := K'
  cases h
  rfl

/-- `T_∅ = t(H,K)`. -/
theorem blockDensityRows_empty (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ)
    (U : ℝ → ℝ → ℝ) (K : Kernel) : blockDensityRows H ∅ q U K = K.tDensity H := by
  unfold blockDensityRows Kernel.tDensity
  refine integral_congr_ae (ae_nonneg_pi.mono fun y hy => Finset.prod_congr rfl fun e _ => ?_)
  induction e using Sym2.ind with
  | _ a b =>
    show blockKernelRows q U K.toFun (pinNewRows ∅ y a) (pinNewRows ∅ y b) = K.toFun (y a) (y b)
    simp only [pinNewRows, Finset.notMem_empty, if_false]
    exact blockKernelRows_of_nonneg q U K.toFun (hy a) (hy b)

/-- `T_{v} = ∫₀¹ ℛ_{v,K}(U t) dt`. -/
theorem blockDensityRows_singleton (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (q : ℝ)
    {U : ℝ → ℝ → ℝ} (hU : IsRows U) (W : Graphon) :
    blockDensityRows H {v} q U (Kernel.ofGraphon W)
      = ∫ t, rootedDensity H W v (U t) ∂unitμ := by
  classical
  -- the integrand of `T_{v}`, rewritten with the row `U (y v)`
  set F : (V → ℝ) → ℝ := fun y =>
    (∏ z ∈ H.neighborFinset v, U (y v) (y z)) * avoidingProduct H W v y with hFdef
  have hUcoord : ∀ z : V, Measurable fun y : V → ℝ => U (y v) (y z) := by
    intro z
    have hp : Measurable fun y : V → ℝ => ((y v, y z) : ℝ × ℝ) :=
      (measurable_pi_apply v).prodMk (measurable_pi_apply z)
    have h := hU.1.comp hp
    exact h
  have hFm : Measurable F := by
    rw [hFdef]
    exact (Finset.measurable_prod _ fun z _ => hUcoord z).mul
      (measurable_avoidingProduct H W v)
  have hFb : ∀ y : V → ℝ, |F y| ≤ 1 := by
    intro y
    rw [hFdef]
    have h1 : ∏ z ∈ H.neighborFinset v, U (y v) (y z) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Finset.prod_nonneg fun z _ => (hU.2 _ _).1,
        Finset.prod_le_one (fun z _ => (hU.2 _ _).1) fun z _ => (hU.2 _ _).2⟩
    have h2 := avoidingProduct_mem_Icc H W v y
    have h3 : (∏ z ∈ H.neighborFinset v, U (y v) (y z)) * avoidingProduct H W v y
        ∈ Set.Icc (0:ℝ) 1 := ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩
    rw [abs_le]
    exact ⟨by linarith [h3.1], h3.2⟩
  have hstep : blockDensityRows H {v} q U (Kernel.ofGraphon W)
      = ∫ y, F y ∂(Measure.pi fun _ : V => unitμ) := by
    unfold blockDensityRows
    refine integral_congr_ae (ae_mem_Ico_pi.mono fun y hy => ?_)
    rw [hFdef]
    beta_reduce
    rw [← Finset.prod_filter_mul_prod_filter_not H.edgeFinset (fun e => v ∈ e),
      filter_mem_edgeFinset_eq_image H v,
      Finset.prod_image (fun z _ z' _ h => Sym2.congr_right.1 h)]
    congr 1
    · refine Finset.prod_congr rfl fun z hz => ?_
      have hzv : z ≠ v := (SimpleGraph.mem_neighborFinset H v z |>.1 hz).ne.symm
      show blockKernelRows q U W.toFun (pinNewRows {v} y v) (pinNewRows {v} y z) = U (y v) (y z)
      simp only [pinNewRows, Finset.mem_singleton, if_true, hzv, if_false]
      exact blockKernelRows_newLabel_left q U W.toFun (hy v).2 (hy z).1
    · unfold avoidingProduct
      refine Finset.prod_congr rfl fun e he => ?_
      have hve : v ∉ e := (Finset.mem_filter.1 he).2
      induction e using Sym2.ind with
      | _ a b =>
        have ha : a ≠ v := fun h => hve (h ▸ Sym2.mem_mk_left a b)
        have hb : b ≠ v := fun h => hve (h ▸ Sym2.mem_mk_right a b)
        show blockKernelRows q U W.toFun (pinNewRows {v} y a) (pinNewRows {v} y b)
          = W.toFun (y a) (y b)
        simp only [pinNewRows, Finset.mem_singleton, ha, hb, if_false]
        exact blockKernelRows_of_nonneg q U W.toFun (hy a).1 (hy b).1
  rw [hstep, ← integral_integral_update v hFm hFb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  unfold rootedDensity
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  rw [hFdef]
  beta_reduce
  rw [Function.update_self, avoidingProduct_update]
  congr 1
  refine Finset.prod_congr rfl fun z hz => ?_
  have hzv : z ≠ v := (SimpleGraph.mem_neighborFinset H v z |>.1 hz).ne.symm
  rw [Function.update_of_ne hzv]

end Block

end UpperTailMultipodality.Insertion
