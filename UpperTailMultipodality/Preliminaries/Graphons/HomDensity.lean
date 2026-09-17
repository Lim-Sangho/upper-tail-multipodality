import UpperTailMultipodality.Preliminaries.Graphons.Variational

/-!
# Homomorphism density of (a.e.-)constant graphons, and the affine mixing path

* `tDensity_constGraphon` — `t(H, W ≡ c) = c^{e(H)}`.
* `measurePreserving_pair` / `tDensity_ae_const` — `t(H,·)` depends only on the a.e. class:
  if `W = c` almost everywhere then `t(H,W) = c^{e(H)}`.  Proved via the independence of
  the two coordinate evaluations of `Measure.pi`, giving the pair marginal
  `(fun x => (x a, x b))_* (Measure.pi unitμ) = gμ`.
* `Wmix` — the affine mixing graphon `W_θ = (1-θ)p + θW`, and `mixTDensity`, the value of
  `t(H, W_θ)` as a plain real function of `θ`, shown to be continuous on `[0,1]`.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

/-- `t(H, W ≡ c) = c^{e(H)}`. -/
theorem tDensity_constGraphon {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    (constGraphon c hc).tDensity H = c ^ H.edgeFinset.card := by
  have key : ∀ x : V → ℝ,
      ∏ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun a b => (constGraphon c hc).toFun (x a) (x b),
          fun a b => (constGraphon c hc).symm' (x a) (x b)⟩ e = c ^ H.edgeFinset.card := by
    intro x
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    induction e using Sym2.ind with
    | _ a b => rfl
  unfold Graphon.tDensity
  rw [show (fun x : V → ℝ => ∏ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun a b => (constGraphon c hc).toFun (x a) (x b),
          fun a b => (constGraphon c hc).symm' (x a) (x b)⟩ e)
      = (fun _ : V → ℝ => c ^ H.edgeFinset.card) from funext key]
  rw [integral_const]; simp

/-- **The pair marginal of `Measure.pi`.**  For distinct coordinates `a ≠ b`, the map
`x ↦ (x a, x b)` pushes the product measure forward to `gμ = unitμ ⊗ unitμ` (the two
coordinate evaluations are i.i.d. `unitμ`). -/
theorem measurePreserving_pair {V : Type*} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b) :
    MeasurePreserving (fun x : V → ℝ => (x a, x b))
      (Measure.pi fun _ : V => unitμ) (unitμ.prod unitμ) := by
  have hindep : ProbabilityTheory.iIndepFun (fun (i : V) (ω : V → ℝ) => ω i)
      (Measure.pi fun _ : V => unitμ) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  have hpair := hindep.indepFun hab
  have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable).mp hpair
  have ha : (Measure.pi fun _ : V => unitμ).map (fun ω : V → ℝ => ω a) = unitμ :=
    (measurePreserving_eval (μ := fun _ : V => unitμ) a).map_eq
  have hb : (Measure.pi fun _ : V => unitμ).map (fun ω : V → ℝ => ω b) = unitμ :=
    (measurePreserving_eval (μ := fun _ : V => unitμ) b).map_eq
  rw [ha, hb] at hmap
  exact ⟨by fun_prop, hmap⟩

/-- **`t(H,·)` depends only on the a.e. class.**  If `W = c` almost everywhere then
`t(H,W) = c^{e(H)}`. -/
theorem tDensity_ae_const (W : Graphon) {c : ℝ} {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hae : ∀ᵐ z ∂gμ, W.toFun z.1 z.2 = c) :
    W.tDensity H = c ^ H.edgeFinset.card := by
  -- per-edge a.e. equality, using the pair marginal at the (distinct) endpoints
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e = c := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hab : a ≠ b := hadj.ne
    have hpe := (measurePreserving_pair (V := V) hab).quasiMeasurePreserving.ae_eq hae
    filter_upwards [hpe] with x hx
    exact hx
  -- aggregate into one a.e. statement and evaluate the product
  have hall : ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      ∀ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e = c :=
    (eventually_all_finset _).mpr hedge
  have hprod : ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      (∏ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e)
        = c ^ H.edgeFinset.card := by
    filter_upwards [hall] with x hx
    rw [Finset.prod_congr rfl (fun e he => hx e he), Finset.prod_const]
  unfold Graphon.tDensity
  exact integral_eq_const hprod

/-! ### The affine mixing path `W_θ = (1-θ)p + θW` and continuity of `t(H, W_θ)`. -/

/-- The affine mixing graphon `W_θ = (1-θ)p + θW`, valid for `p, θ ∈ [0,1]`. -/
noncomputable def Wmix (W : Graphon) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) : Graphon where
  toFun x y := (1 - θ) * p + θ * W.toFun x y
  symm' x y := by rw [W.symm']
  meas' := by
    have h : Measurable fun z : ℝ × ℝ => (1 - θ) * p + θ * W.toFun z.1 z.2 :=
      measurable_const.add (W.measurable_uncurry.const_mul θ)
    exact h
  nonneg' x y := by nlinarith [W.nonneg' x y, hp.1, hθ.1, hθ.2]
  le_one' x y := by nlinarith [W.le_one' x y, W.nonneg' x y, hp.1, hp.2, hθ.1, hθ.2]

/-- `W_θ(x,y) = (1-θ)·p + θ·W(x,y)`. -/
@[simp] theorem Wmix_apply (W : Graphon) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0:ℝ) 1) (x y : ℝ) :
    (Wmix W p hp θ hθ).toFun x y = (1 - θ) * p + θ * W.toFun x y := rfl

section Mixing

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Each edge factor `Sym2.lift⟨W⟩ e` takes values in `[0,1]`. -/
theorem liftEdge_mem_Icc (W : Graphon) (x : V → ℝ) (e : Sym2 V) :
    Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e
      ∈ Set.Icc (0:ℝ) 1 := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨W.nonneg' (x a) (x b), W.le_one' (x a) (x b)⟩

omit [Fintype V] [DecidableEq V] in
/-- Each edge factor is measurable in the vertex assignment. -/
theorem measurable_liftEdge (W : Graphon) (e : Sym2 V) :
    Measurable (fun x : V → ℝ =>
      Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e) := by
  induction e using Sym2.ind with
  | _ a b =>
    show Measurable (fun x : V → ℝ => W.toFun (x a) (x b))
    have hpair : Measurable (fun x : V → ℝ => (x a, x b)) := by fun_prop
    exact W.measurable_uncurry.comp hpair

omit [Fintype V] [DecidableEq V] in
/-- The Sym2 lift of an affine combination distributes over the affine structure. -/
theorem sym2_lift_affine (W : Graphon) (x : V → ℝ) (θ p : ℝ) (e : Sym2 V) :
    Sym2.lift ⟨fun a b => (1 - θ) * p + θ * W.toFun (x a) (x b),
        fun a b => by show (1 - θ) * p + θ * W.toFun (x a) (x b)
                        = (1 - θ) * p + θ * W.toFun (x b) (x a)
                      rw [W.symm' (x a) (x b)]⟩ e
      = (1 - θ) * p
        + θ * Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e := by
  induction e using Sym2.ind with | _ a b => rfl

/-- The value `t(H, W_θ)` of the homomorphism density along the mixing path, as a plain real
function of `θ` (defined for all `θ`, used on `[0,1]`). -/
noncomputable def mixTDensity (W : Graphon) (p : ℝ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (θ : ℝ) : ℝ :=
  ∫ x : V → ℝ, ∏ e ∈ H.edgeFinset,
    ((1 - θ) * p + θ * Sym2.lift ⟨fun a b => W.toFun (x a) (x b),
      fun a b => W.symm' (x a) (x b)⟩ e) ∂(Measure.pi fun _ : V => unitμ)

/-- For `θ ∈ [0,1]`, `mixTDensity` is exactly `t(H, W_θ)`. -/
theorem mixTDensity_eq_tDensity (W : Graphon) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (H : SimpleGraph V) [DecidableRel H.Adj] {θ : ℝ} (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    mixTDensity W p H θ = (Wmix W p hp θ hθ).tDensity H := by
  unfold mixTDensity Graphon.tDensity
  refine integral_congr_ae (ae_of_all _ (fun x => Finset.prod_congr rfl (fun e _ => ?_)))
  exact (sym2_lift_affine W x θ p e).symm

omit [DecidableEq V] in
/-- `t(H, W_θ)` is continuous in `θ` on `[0,1]` (dominated convergence; the integrand is a
finite product of `[0,1]`-valued affine functions of `θ`). -/
theorem mixTDensity_continuousOn (W : Graphon) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ContinuousOn (mixTDensity W p H) (Set.Icc 0 1) := by
  unfold mixTDensity
  refine continuousOn_of_dominated (bound := fun _ => 1) (fun θ _ => ?_) (fun θ hθ => ?_)
    (integrable_const 1) (ae_of_all _ (fun x => ?_))
  · -- measurability in `x` for each `θ`
    refine Measurable.aestronglyMeasurable (Finset.measurable_prod _ (fun e _ => ?_))
    exact measurable_const.add ((measurable_liftEdge W e).const_mul θ)
  · -- domination by `1` for `θ ∈ [0,1]`
    refine ae_of_all _ (fun x => ?_)
    have hfac : ∀ e ∈ H.edgeFinset,
        (1 - θ) * p + θ * Sym2.lift ⟨fun a b => W.toFun (x a) (x b),
          fun a b => W.symm' (x a) (x b)⟩ e ∈ Set.Icc (0:ℝ) 1 := by
      intro e _
      have ht := liftEdge_mem_Icc W x e
      exact ⟨by nlinarith [ht.1, ht.2, hp.1, hθ.1, hθ.2],
             by nlinarith [ht.1, ht.2, hp.1, hp.2, hθ.1, hθ.2]⟩
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg (fun e he => (hfac e he).1))]
    exact Finset.prod_le_one (fun e he => (hfac e he).1) (fun e he => (hfac e he).2)
  · -- continuity in `θ` for each `x`
    refine Continuous.continuousOn (continuous_finsetProd _ (fun e _ => ?_))
    fun_prop

omit [DecidableEq V] in
/-- `t(H, W_0) = t(H, p ≡) = p^{e(H)}`. -/
theorem mixTDensity_zero (W : Graphon) (p : ℝ) (H : SimpleGraph V) [DecidableRel H.Adj] :
    mixTDensity W p H 0 = p ^ H.edgeFinset.card := by
  unfold mixTDensity
  have key : ∀ x : V → ℝ, ∏ e ∈ H.edgeFinset,
      ((1 - (0:ℝ)) * p + (0:ℝ) * Sym2.lift ⟨fun a b => W.toFun (x a) (x b),
        fun a b => W.symm' (x a) (x b)⟩ e) = p ^ H.edgeFinset.card := by
    intro x
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl (fun e _ => by ring)
  rw [show (fun x : V → ℝ => ∏ e ∈ H.edgeFinset,
        ((1 - (0:ℝ)) * p + (0:ℝ) * Sym2.lift ⟨fun a b => W.toFun (x a) (x b),
          fun a b => W.symm' (x a) (x b)⟩ e)) = (fun _ : V → ℝ => p ^ H.edgeFinset.card)
      from funext key]
  rw [integral_const]; simp

/-- `t(H, W_1) = t(H, W)`. -/
theorem mixTDensity_one (W : Graphon) (p : ℝ) (H : SimpleGraph V) [DecidableRel H.Adj] :
    mixTDensity W p H 1 = W.tDensity H := by
  unfold mixTDensity Graphon.tDensity
  refine integral_congr_ae (ae_of_all _ (fun x => Finset.prod_congr rfl (fun e _ => ?_)))
  ring

end Mixing

/-! ### The edge density as a homomorphism density -/

/-- `e(K_2) = 1`: the complete graph on two vertices has a single edge.  Recorded so that
`Feasible H r` and `phiVar H p r` instantiate at `H = K_2` to the *edge*-density constraint
`e(W) ≥ r`. -/
theorem edgeFinset_card_top_two : ((⊤ : SimpleGraph (Fin 2)).edgeFinset).card = 1 := by decide

/-- **`e(W) = t(K_2, W)`**: the edge density is the
homomorphism density of the single edge `K_2 = ⊤ : SimpleGraph (Fin 2)`.  Consequently
`edgeDensity_cutContinuous` is the `H = K_2` case of `tDensity_cutContinuous`.

The proof evaluates the one-factor product and identifies the two-fold integral over
`Measure.pi` with the integral over `gμ` through the pair marginal
`measurePreserving_pair`. -/
theorem tDensity_top_two (W : Graphon) :
    W.tDensity (⊤ : SimpleGraph (Fin 2)) = W.edgeDensity := by
  unfold Graphon.tDensity Graphon.edgeDensity
  have hE : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  rw [hE, gμ]
  simp only [Finset.prod_singleton]
  show ∫ x : Fin 2 → ℝ, W.toFun (x 0) (x 1) ∂(Measure.pi fun _ => unitμ) = _
  have hmp := measurePreserving_pair (V := Fin 2) (a := 0) (b := 1) (by decide)
  rw [← hmp.map_eq, integral_map (by fun_prop) W.measurable_uncurry.aestronglyMeasurable]

/-- **A null first pode carries no excess.**  If the first block `[0,c]` of a bipodal graphon
is degenerate then the graphon is almost everywhere constant, so its `H`-density is the `m`-th
power of its edge density.  A strictly larger target density therefore forces `0 < c`. -/
theorem blockSize_pos {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (hm : 1 ≤ H.edgeFinset.card) (B : Graphon)
    {c q11 q12 q22 ε r : ℝ} (hc0 : 0 ≤ c) (hε : B.edgeDensity = ε) (hlt : ε < r)
    (htd : B.tDensity H = r ^ H.edgeFinset.card)
    (hae : ∀ᵐ z ∂gμ, B.toFun z.1 z.2 = bipodalValue (Set.Icc 0 c) q11 q12 q22 z) :
    0 < c := by
  classical
  rcases lt_or_eq_of_le hc0 with hpos | hzero
  · exact hpos
  · exfalso
    have hnull : ∀ᵐ x ∂unitμ, x ∉ Set.Icc (0:ℝ) c := by
      have hsing : unitμ {(0:ℝ)} = 0 := by
        rw [unitμ, Measure.restrict_apply (measurableSet_singleton _)]
        exact measure_mono_null Set.inter_subset_left (by simp)
      filter_upwards [compl_mem_ae_iff.mpr hsing] with x hx
      rw [← hzero, Set.Icc_self]
      simpa using hx
    have hn1 : ∀ᵐ z ∂gμ, z.1 ∉ Set.Icc (0:ℝ) c :=
      Measure.quasiMeasurePreserving_fst.ae hnull
    have hn2 : ∀ᵐ z ∂gμ, z.2 ∉ Set.Icc (0:ℝ) c :=
      Measure.quasiMeasurePreserving_snd.ae hnull
    have hconst : ∀ᵐ z ∂gμ, B.toFun z.1 z.2 = q22 := by
      filter_upwards [hae, hn1, hn2] with z hz hz1 hz2
      rw [hz, bipodalValue, if_neg hz1, if_neg hz2]
    have he : ε = q22 := by
      rw [← hε, Graphon.edgeDensity]; exact integral_eq_const hconst
    have ht : r ^ H.edgeFinset.card = q22 ^ H.edgeFinset.card := by
      rw [← htd]; exact tDensity_ae_const B H hconst
    have hε0 : 0 ≤ ε := by
      rw [← hε, Graphon.edgeDensity]
      exact integral_nonneg fun z => B.nonneg' _ _
    have : ε ^ H.edgeFinset.card < r ^ H.edgeFinset.card :=
      pow_lt_pow_left₀ hlt hε0 (by omega)
    rw [ht, ← he] at this
    exact absurd this (lt_irrefl _)

/-- **`t(H,·)` is invariant under relabelling.**  Relabelling the coordinates of the product
measure is measure-preserving, so the homomorphism density integral is unchanged. -/
theorem tDensity_relabel {V : Type*} [Fintype V] [DecidableEq V]
    {W W' : Graphon} {σ : ℝ → ℝ}
    (hσ : MeasurePreserving σ unitμ unitμ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hae : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) :
    W'.tDensity H = W.tDensity H := by
  classical
  have hpi : MeasurePreserving (fun x : V → ℝ => fun v => σ (x v))
      (Measure.pi fun _ : V => unitμ) (Measure.pi fun _ : V => unitμ) :=
    measurePreserving_pi _ _ (fun _ => hσ)
  have hedge : ∀ e ∈ H.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => unitμ),
      Sym2.lift ⟨fun a b => W'.toFun (x a) (x b), fun a b => W'.symm' (x a) (x b)⟩ e
        = Sym2.lift ⟨fun a b => W.toFun (σ (x a)) (σ (x b)),
            fun a b => W.symm' (σ (x a)) (σ (x b))⟩ e := by
    refine Sym2.ind (fun a b => ?_)
    intro he
    have hadj : H.Adj a b := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact (measurePreserving_pair (V := V) hadj.ne).quasiMeasurePreserving.ae_eq hae
  have hall := (eventually_all_finset _).mpr hedge
  have hstep : W'.tDensity H
      = ∫ x : V → ℝ, ∏ e ∈ H.edgeFinset,
          Sym2.lift ⟨fun a b => W.toFun (σ (x a)) (σ (x b)),
            fun a b => W.symm' (σ (x a)) (σ (x b))⟩ e ∂(Measure.pi fun _ : V => unitμ) := by
    unfold Graphon.tDensity
    exact integral_congr_ae (hall.mono fun x hx => Finset.prod_congr rfl fun e he => hx e he)
  have hmeas : Measurable fun y : V → ℝ => ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => W.toFun (y a) (y b), fun a b => W.symm' (y a) (y b)⟩ e :=
    Finset.measurable_prod _ (fun e _ => measurable_liftEdge W e)
  have h := integral_map (μ := Measure.pi fun _ : V => unitμ)
    (φ := fun x : V → ℝ => fun v => σ (x v)) hpi.measurable.aemeasurable
    (by rw [hpi.map_eq]; exact hmeas.aestronglyMeasurable)
  rw [hpi.map_eq] at h
  rw [hstep]
  unfold Graphon.tDensity
  exact h.symm

end UpperTailMultipodality
