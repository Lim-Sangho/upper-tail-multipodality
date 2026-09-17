import UpperTailMultipodality.UpperTail.Support.Basic

/-!
# Homomorphism densities of graphs of maximum degree at most one

If every vertex of `H` has degree at most `1`, the edges of `H` are pairwise disjoint, the edge
factors of `t(H,W)` depend on disjoint sets of coordinates, and hence
`t(H,W) = e(W)^m` (`tDensity_eq_edgeDensity_pow`).  The factorization uses the independence of
disjoint blocks of coordinates under the product measure.

For such `H`, Jensen's inequality and its equality case show that every minimizer of
`eq:graphon-variational-problem` is almost everywhere equal to the constant `r`
(`ae_eq_of_degree_le_one`), which is multipodal with one block
(`isOrderedMultipodal_of_ae_const`).
-/

namespace UpperTailMultipodality

namespace UpperTailSupport

open MeasureTheory ProbabilityTheory Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a graph of maximum degree at most one, an edge different from `ab` avoids `a` and `b`. -/
theorem not_mem_of_degree_le_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 1) {a b : V} (hab : H.Adj a b) {e : Sym2 V}
    (he : e ∈ H.edgeFinset) (hne : e ≠ s(a, b)) : a ∉ e ∧ b ∉ e := by
  have two_le : ∀ {u c d : V}, H.Adj u c → H.Adj u d → c ≠ d → 2 ≤ H.degree u := by
    intro u c d huc hud hcd
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : ({c, d} : Finset V) ⊆ H.neighborFinset u := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr huc
      · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hud
    calc 2 = ({c, d} : Finset V).card := (Finset.card_pair hcd).symm
      _ ≤ _ := Finset.card_le_card hsub
  rw [SimpleGraph.mem_edgeFinset] at he
  constructor
  · intro ha
    obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp ha
    have hac : H.Adj a c := he
    have hcb : b ≠ c := fun h => hne (by rw [h])
    have := two_le hab hac hcb
    have := hdeg a
    omega
  · intro hb
    obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp hb
    have hbc : H.Adj b c := he
    have hca : a ≠ c := fun h => hne (by rw [h, Sym2.eq_swap])
    have := two_le hab.symm hbc hca
    have := hdeg b
    omega

/-- The integral of a single edge factor is the edge density. -/
theorem integral_edgeVal_pair (W : Graphon) {a b : V} (hab : a ≠ b) :
    ∫ x, edgeVal W.toFun W.symm' x s(a, b) ∂(Measure.pi fun _ : V => unitμ) = W.edgeDensity := by
  show ∫ x : V → ℝ, W.toFun (x a) (x b) ∂(Measure.pi fun _ => unitμ) = _
  have hmp := measurePreserving_pair (V := V) hab
  unfold Graphon.edgeDensity
  rw [gμ, ← hmp.map_eq, integral_map (by fun_prop) W.measurable_uncurry.aestronglyMeasurable]

/-- **One step of the factorization.**  If `ab` is an edge and the edges in `S` avoid `a` and
`b`, the factor of `ab` is independent of the product over `S`. -/
theorem integral_edgeVal_mul_prod (W : Graphon) {a b : V} (hab : a ≠ b) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, a ∉ e ∧ b ∉ e) :
    ∫ x, edgeVal W.toFun W.symm' x s(a, b) * ∏ e ∈ S, edgeVal W.toFun W.symm' x e
        ∂(Measure.pi fun _ : V => unitμ)
      = W.edgeDensity * ∫ x, ∏ e ∈ S, edgeVal W.toFun W.symm' x e
        ∂(Measure.pi fun _ : V => unitμ) := by
  classical
  set T : Finset V := {a, b} with hT
  set T' : Finset V := Finset.univ \ T with hT'
  have hind : iIndepFun (fun (i : V) (ω : V → ℝ) => ω i) (Measure.pi fun _ : V => unitμ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h2 := hind.indepFun_finset T T' Finset.disjoint_sdiff (fun i => measurable_pi_apply i)
  have haT : a ∈ T := by simp [hT]
  have hbT : b ∈ T := by simp [hT]
  let g₁ : (T → ℝ) → ℝ := fun y => W.toFun (y ⟨a, haT⟩) (y ⟨b, hbT⟩)
  let ext : (T' → ℝ) → V → ℝ := fun y i => if h : i ∈ T' then y ⟨i, h⟩ else 0
  let g₂ : (T' → ℝ) → ℝ := fun y => ∏ e ∈ S, edgeVal W.toFun W.symm' (ext y) e
  have hg₁ : Measurable g₁ := by
    have h := W.measurable_uncurry.comp (f := fun y : T → ℝ => (y ⟨a, haT⟩, y ⟨b, hbT⟩))
      (by fun_prop)
    exact h
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ T'
    · simp only [ext, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext, dif_neg h]; exact measurable_const
  have hg₂ : Measurable g₂ :=
    Finset.measurable_prod _ fun e _ => (measurable_liftEdge W e).comp hext
  have h3 := h2.comp hg₁ hg₂
  have hX : Measurable fun ω : V → ℝ => fun i : T => ω i := by fun_prop
  have hY : Measurable fun ω : V → ℝ => fun i : T' => ω i := by fun_prop
  have hmul := h3.integral_fun_mul_eq_mul_integral (hg₁.comp hX).aestronglyMeasurable
    (hg₂.comp hY).aestronglyMeasurable
  -- identify the two factors
  have hfac₂ : ∀ x : V → ℝ, ∏ e ∈ S, edgeVal W.toFun W.symm' x e
      = (g₂ ∘ fun ω : V → ℝ => fun i : T' => ω i) x := by
    intro x
    refine Finset.prod_congr rfl fun e he => ?_
    obtain ⟨hae, hbe⟩ := hS e he
    revert hae hbe
    induction e using Sym2.ind with
    | _ c d =>
      intro hae hbe
      have hc : c ∈ T' := by
        simp only [hT', hT, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
          Finset.mem_singleton, true_and]
        rintro (rfl | rfl)
        · exact hae (Sym2.mem_mk_left _ _)
        · exact hbe (Sym2.mem_mk_left _ _)
      have hd : d ∈ T' := by
        simp only [hT', hT, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
          Finset.mem_singleton, true_and]
        rintro (rfl | rfl)
        · exact hae (Sym2.mem_mk_right _ _)
        · exact hbe (Sym2.mem_mk_right _ _)
      show W.toFun (x c) (x d)
        = W.toFun (ext (fun i : T' => x i) c) (ext (fun i : T' => x i) d)
      simp only [ext, dif_pos hc, dif_pos hd]
  have hfac₁ : ∀ x : V → ℝ, edgeVal W.toFun W.symm' x s(a, b)
      = (g₁ ∘ fun ω : V → ℝ => fun i : T => ω i) x := fun x => rfl
  calc ∫ x, edgeVal W.toFun W.symm' x s(a, b) * ∏ e ∈ S, edgeVal W.toFun W.symm' x e
          ∂(Measure.pi fun _ : V => unitμ)
      = ∫ x, (g₁ ∘ fun ω : V → ℝ => fun i : T => ω i) x
          * (g₂ ∘ fun ω : V → ℝ => fun i : T' => ω i) x ∂(Measure.pi fun _ : V => unitμ) := by
        simp_rw [hfac₁, hfac₂]
    _ = (∫ x, (g₁ ∘ fun ω : V → ℝ => fun i : T => ω i) x ∂(Measure.pi fun _ : V => unitμ))
          * ∫ x, (g₂ ∘ fun ω : V → ℝ => fun i : T' => ω i) x
            ∂(Measure.pi fun _ : V => unitμ) := hmul
    _ = W.edgeDensity * ∫ x, ∏ e ∈ S, edgeVal W.toFun W.symm' x e
          ∂(Measure.pi fun _ : V => unitμ) := by
        simp_rw [← hfac₁, ← hfac₂]
        rw [integral_edgeVal_pair W hab]

/-- The integral of the product over a set of edges of a graph of maximum degree at most one. -/
theorem integral_prod_edges_of_degree_le_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 1) (W : Graphon) (S : Finset (Sym2 V)) (hS : S ⊆ H.edgeFinset) :
    ∫ x, ∏ e ∈ S, edgeVal W.toFun W.symm' x e ∂(Measure.pi fun _ : V => unitμ)
      = W.edgeDensity ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert e₀ S he₀ ih =>
    have hS' : S ⊆ H.edgeFinset := (Finset.subset_insert _ _).trans hS
    have he₀E : e₀ ∈ H.edgeFinset := hS (Finset.mem_insert_self _ _)
    simp_rw [Finset.prod_insert he₀]
    rw [Finset.card_insert_of_notMem he₀, pow_succ, ← ih hS']
    revert he₀ he₀E
    induction e₀ using Sym2.ind with
    | _ a b =>
      intro he₀ he₀E
      have hab : H.Adj a b := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₀E
      rw [integral_edgeVal_mul_prod W hab.ne S fun e he =>
        not_mem_of_degree_le_one H hdeg hab (hS' he) fun h => he₀ (h ▸ he), mul_comm]

/-- **`t(H,W) = e(W)^m` for graphs of maximum degree at most one.** -/
theorem tDensity_eq_edgeDensity_pow (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 1) (W : Graphon) :
    W.tDensity H = W.edgeDensity ^ H.edgeFinset.card :=
  integral_prod_edges_of_degree_le_one H hdeg W H.edgeFinset subset_rfl

/-- **Minimizers for graphs of maximum degree at most one are constant.**  If every vertex of
`H` has degree at most one, every minimizer of `eq:graphon-variational-problem` equals `r`
almost everywhere. -/
theorem ae_eq_of_degree_le_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 1) (hm : 1 ≤ H.edgeFinset.card) {p r : ℝ} (hp0 : 0 < p)
    (hpr : p < r) (hr1 : r < 1) {W : Graphon} (hW : Feasible H r W)
    (hmin : W.Ip p = phiVar H p r) : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r := by
  have hp1 : p < 1 := lt_trans hpr hr1
  have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨(hp0.trans hpr).le, hr1.le⟩
  have he : r ≤ W.edgeDensity := by
    have h : r ^ H.edgeFinset.card ≤ W.edgeDensity ^ H.edgeFinset.card :=
      tDensity_eq_edgeDensity_pow H hdeg W ▸ hW
    exact le_of_pow_le_pow_left₀ (by omega) (edgeDensity_nonneg W) h
  -- `I_p(W) ≤ J_p(r)`, since the constant graphon `r` is feasible
  have hcfeas : Feasible H r (constGraphon r hr_mem) :=
    le_of_eq (tDensity_constGraphon hr_mem H).symm
  have hcIp : (constGraphon r hr_mem).Ip p = Jp p r := by
    unfold Graphon.Ip; simp only [constGraphon_apply]; rw [integral_const]; simp
  have hle : W.Ip p ≤ Jp p r := hmin ▸ hcIp ▸ phiVar_le_of_feasible H hp0 hp1 hcfeas
  have hjen := Ip_jensen W hp0 hp1
  have hmonoS := Jp_strictMonoOn_right hp0 hp1
  have heW : W.edgeDensity ∈ Set.Icc p 1 := ⟨hpr.le.trans he, edgeDensity_le_one W⟩
  have hmono : Jp p r ≤ Jp p W.edgeDensity :=
    hmonoS.monotoneOn ⟨hpr.le, hr1.le⟩ heW he
  have heq : W.edgeDensity = r := by
    by_contra hne
    have hlt := hmonoS ⟨hpr.le, hr1.le⟩ heW (lt_of_le_of_ne he (Ne.symm hne))
    linarith
  -- the equality case of Jensen's inequality for the strictly convex `J_p`
  have hgi : Integrable (Jp p ∘ fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ :=
    W.integrable_comp (measurable_Jp p) (continuousOn_Jp_Icc hp0 hp1)
  have hWmem : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 ∈ Set.Icc (0:ℝ) 1 :=
    ae_of_all _ fun z : ℝ × ℝ => W.mem_Icc z.1 z.2
  rcases (strictConvexOn_Jp hp0 hp1).ae_eq_const_or_map_average_lt (continuousOn_Jp_Icc hp0 hp1)
      isClosed_Icc hWmem W.integrable_self hgi with h | h
  · filter_upwards [h] with z hz
    rw [hz, Function.const_apply, average_eq_integral]
    exact heq
  · rw [average_eq_integral, average_eq_integral] at h
    have h' : Jp p W.edgeDensity < W.Ip p := h
    linarith

/-- An almost everywhere constant graphon is multipodal with one block. -/
theorem isOrderedMultipodal_of_ae_const {W : Graphon} {r : ℝ} (hr : r ∈ Set.Icc (0:ℝ) 1)
    (h : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = r) : IsOrderedMultipodal W :=
  ⟨1,
    { block := fun _ => Set.univ
      value := fun _ _ => r
      measurableSet_block := fun _ => MeasurableSet.univ
      pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
      cover := ae_of_all _ fun _ => ⟨0, Set.mem_univ _⟩
      value_symm := fun _ _ => rfl
      value_mem := fun _ _ => hr },
    fun _ _ => h.mono fun _ hz _ _ => hz, fun _ _ _ _ => le_rfl⟩

end UpperTailSupport

end UpperTailMultipodality
