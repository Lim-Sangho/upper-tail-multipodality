import UpperTailMultipodality.Preliminaries.Graphons.Jp

/-!
# Graphons and the functionals `e`, `t(H,·)`, `I_p`, `s` (Sections 1–2)

This file formalises the measure-theoretic objects of `sec:graphons`: the edge density `e`, the
homomorphism density `t(H,·)`, the relative entropy `I_p` and the entropy `s`.

A `Graphon` is a symmetric measurable function `[0,1]² → [0,1]`.  We model it as a
total symmetric measurable function `ℝ → ℝ → ℝ` with values in `[0,1]`, and all
integrals are taken against the probability measure `unitμ = volume|_{[0,1]}` (or
its products).  We define:

* `Graphon.edgeDensity W = ∫∫ W`  (the edge density `e(W)`),
* `Graphon.Ip p W = ∫∫ J_p(W)`   (the relative-entropy cost `I_p(W)`),
* `Graphon.entropy W = -½ ∫∫ [W log W + (1-W) log(1-W)]`  (the entropy `s(W)`),
* `Graphon.Wmoment W d = ∫∫ W^d`,
* `Graphon.tDensity H W` (the homomorphism density `t(H,W)`).

The key algebraic identity
`I_p(W) = -2 s(W) - log(1-p) + e(W) log((1-p)/p)`, is `Graphon.Ip_eq_entropy`.

The file also hosts `integrable_of_abs_le`, the `Measurable`-plus-uniform-bound wrapper over
Mathlib's `Integrable.of_bound`: it is the unique module every consumer of that wrapper
reaches, and it used to exist as nine private copies under nine names.
-/

namespace UpperTailMultipodality

open MeasureTheory Real

/-- Lebesgue measure restricted to the unit interval `[0,1]`; a probability measure. -/
noncomputable def unitμ : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unitμ := by
  constructor
  rw [unitμ, Measure.restrict_apply_univ, Real.volume_Icc]
  simp

/-- The probability measure on `[0,1]²` used for the graphon integrals. -/
noncomputable def gμ : Measure (ℝ × ℝ) := unitμ.prod unitμ

instance : IsProbabilityMeasure gμ := by
  rw [gμ]; infer_instance

/-! ## Relabellings of `[0,1]`

`sec:graphons` defines `δ_□` with `σ` ranging over the measure-preserving
*bijections* of `[0,1]`, and identifies two graphons that differ by such a `σ`.  A
Lebesgue-space isomorphism is a bijection only after discarding null sets, so the formal
notion carries an inverse that undoes `σ` almost everywhere in both directions.
-/

/-- **A relabelling of `[0,1]`**: a measure-preserving self-map that is invertible modulo null
sets.  This is the identification used in `sec:graphons`; the inverse is
required only almost everywhere, which is what a measure-space isomorphism provides. -/
def IsRelabelling (σ : ℝ → ℝ) : Prop :=
  MeasurePreserving σ unitμ unitμ ∧
    ∃ τ : ℝ → ℝ, MeasurePreserving τ unitμ unitμ ∧
      (∀ᵐ x ∂unitμ, τ (σ x) = x) ∧ (∀ᵐ y ∂unitμ, σ (τ y) = y)

theorem IsRelabelling.measurePreserving {σ : ℝ → ℝ} (h : IsRelabelling σ) :
    MeasurePreserving σ unitμ unitμ := h.1

theorem IsRelabelling.measurable {σ : ℝ → ℝ} (h : IsRelabelling σ) : Measurable σ :=
  h.1.measurable

theorem isRelabelling_id : IsRelabelling id :=
  ⟨MeasurePreserving.id unitμ, id, MeasurePreserving.id unitμ,
    Filter.Eventually.of_forall fun _ => rfl, Filter.Eventually.of_forall fun _ => rfl⟩

/-- The a.e. inverse of a relabelling is a relabelling. -/
theorem IsRelabelling.exists_symm {σ : ℝ → ℝ} (h : IsRelabelling σ) :
    ∃ τ : ℝ → ℝ, IsRelabelling τ ∧
      (∀ᵐ x ∂unitμ, τ (σ x) = x) ∧ (∀ᵐ y ∂unitμ, σ (τ y) = y) := by
  obtain ⟨hσ, τ, hτ, hτσ, hστ⟩ := h
  exact ⟨τ, ⟨hτ, σ, hσ, hστ, hτσ⟩, hτσ, hστ⟩

/-- Relabellings compose. -/
theorem IsRelabelling.comp {σ τ : ℝ → ℝ} (hσ : IsRelabelling σ) (hτ : IsRelabelling τ) :
    IsRelabelling fun x => σ (τ x) := by
  obtain ⟨hσmp, σ', hσ'mp, hσ'σ, hσσ'⟩ := hσ
  obtain ⟨hτmp, τ', hτ'mp, hτ'τ, hττ'⟩ := hτ
  refine ⟨hσmp.comp hτmp, fun y => τ' (σ' y), hτ'mp.comp hσ'mp, ?_, ?_⟩
  · -- `τ'(σ'(σ(τ x))) = x` a.e.
    filter_upwards [hτ'τ, hτmp.quasiMeasurePreserving.ae hσ'σ] with x h1 h2
    rw [h2, h1]
  · -- `σ(τ(τ'(σ' y))) = y` a.e.
    filter_upwards [hσσ', hσ'mp.quasiMeasurePreserving.ae hττ'] with y h1 h2
    rw [h2, h1]

/-- **A measurable function with a uniform bound on a finite measure space is integrable.**
Mathlib's `Integrable.of_bound` wants `AEStronglyMeasurable` and an a.e. bound on `‖·‖`; this
is the `Measurable`/`|·|`/`∀` wrapper that the whole development uses, stated once. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hm : Measurable g) (C : ℝ) (hb : ∀ x, |g x| ≤ C) :
    Integrable g μ :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- A graphon: a symmetric measurable function with values in `[0,1]`. -/
structure Graphon where
  /-- The underlying kernel. -/
  toFun : ℝ → ℝ → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable (Function.uncurry toFun)
  nonneg' : ∀ x y, 0 ≤ toFun x y
  le_one' : ∀ x y, toFun x y ≤ 1

namespace Graphon

instance : CoeFun Graphon (fun _ => ℝ → ℝ → ℝ) := ⟨Graphon.toFun⟩

/-- Two graphons with the same kernel are equal: the remaining fields are proofs. -/
@[ext] theorem ext {W W' : Graphon} (h : ∀ x y, W.toFun x y = W'.toFun x y) : W = W' := by
  have hfg : W.toFun = W'.toFun := funext fun x => funext fun y => h x y
  obtain ⟨f, hs, hm, hn, hl⟩ := W
  obtain ⟨g, hs', hm', hn', hl'⟩ := W'
  simp only at hfg
  subst hfg
  rfl

variable (W : Graphon)

/-- Measurability of `z ↦ W z.1 z.2`. -/
theorem measurable_uncurry : Measurable (fun z : ℝ × ℝ => W.toFun z.1 z.2) := W.meas'

/-- The values of a graphon lie in `[0,1]`. -/
theorem mem_Icc (x y : ℝ) : W.toFun x y ∈ Set.Icc (0:ℝ) 1 := ⟨W.nonneg' x y, W.le_one' x y⟩

/-- Composition of a graphon with a function continuous on `[0,1]` is integrable. -/
theorem integrable_comp {g : ℝ → ℝ} (hgm : Measurable g) (hgc : ContinuousOn g (Set.Icc 0 1)) :
    Integrable (fun z : ℝ × ℝ => g (W.toFun z.1 z.2)) gμ := by
  have hmeas : Measurable (fun z : ℝ × ℝ => g (W.toFun z.1 z.2)) := hgm.comp W.meas'
  obtain ⟨t₀, ht₀, hmax⟩ :=
    (isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1))
      (hgc.abs))
  refine Integrable.of_bound hmeas.aestronglyMeasurable (|g t₀|) (ae_of_all _ fun z => ?_)
  have hb : |g (W.toFun z.1 z.2)| ≤ |g t₀| := hmax (W.mem_Icc z.1 z.2)
  simpa [Real.norm_eq_abs] using hb

/-- `z ↦ W z.1 z.2` is integrable. -/
theorem integrable_self : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ := by
  have := W.integrable_comp (g := id) measurable_id continuousOn_id
  simpa using this

/-- The edge density `e(W) = ∫∫ W`. -/
noncomputable def edgeDensity : ℝ := ∫ z, W.toFun z.1 z.2 ∂gμ

/-- The relative-entropy cost `I_p(W) = ∫∫ J_p(W)`. -/
noncomputable def Ip (p : ℝ) : ℝ := ∫ z, Jp p (W.toFun z.1 z.2) ∂gμ

/-- The entropy functional `s(W) = -½ ∫∫ [W log W + (1-W) log(1-W)]`. -/
noncomputable def entropy : ℝ :=
  -(1/2) * ∫ z, (W.toFun z.1 z.2 * Real.log (W.toFun z.1 z.2)
      + (1 - W.toFun z.1 z.2) * Real.log (1 - W.toFun z.1 z.2)) ∂gμ

/-- The `d`-th moment `∫∫ W^d`, appearing in the generalized Hölder bound. -/
noncomputable def Wmoment (d : ℕ) : ℝ := ∫ z, (W.toFun z.1 z.2) ^ d ∂gμ

/-- The homomorphism density `t(H,W)` for a finite simple graph `H`. -/
noncomputable def tDensity {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : ℝ :=
  ∫ x : V → ℝ,
    ∏ e ∈ H.edgeFinset, Sym2.lift ⟨fun a b => W.toFun (x a) (x b), fun a b => W.symm' (x a) (x b)⟩ e
    ∂(Measure.pi fun _ => unitμ)

end Graphon

/-! ### The identity relating `I_p` and the entropy `s`. -/

/-- For `t ≥ 0` and `s ≠ 0`, `t log(t/s) = t log t - t log s` (with `0 log 0 = 0`). -/
theorem mul_log_div_aux {t s : ℝ} (ht : 0 ≤ t) (hs : s ≠ 0) :
    t * Real.log (t / s) = t * Real.log t - t * Real.log s := by
  rcases eq_or_lt_of_le ht with h | h
  · simp [← h]
  · rw [Real.log_div (ne_of_gt h) hs]; ring

/-- The entropy integrand `t log t + (1-t) log(1-t)`. -/
noncomputable def entIntegrand (t : ℝ) : ℝ := t * Real.log t + (1 - t) * Real.log (1 - t)

/-- `entIntegrand t = -negMulLog t - negMulLog (1-t)` (bridge to Mathlib's `negMulLog`). -/
theorem entIntegrand_eq (t : ℝ) :
    entIntegrand t = -Real.negMulLog t - Real.negMulLog (1 - t) := by
  unfold entIntegrand Real.negMulLog; ring

/-- The entropy integrand is continuous. -/
theorem continuous_entIntegrand : Continuous entIntegrand := by
  have h : entIntegrand = fun t => -Real.negMulLog t - Real.negMulLog (1 - t) :=
    funext entIntegrand_eq
  rw [h]
  exact Real.continuous_negMulLog.neg.sub
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))

/-- The entropy integrand is measurable. -/
theorem measurable_entIntegrand : Measurable entIntegrand := continuous_entIntegrand.measurable

/-- On `[0,1]`, `J_p` equals `entIntegrand t - t log p - (1-t) log(1-p)`. -/
theorem Jp_eq_entIntegrand {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Jp p t = entIntegrand t - t * Real.log p - (1 - t) * Real.log (1 - p) := by
  unfold Jp entIntegrand
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  rw [mul_log_div_aux ht0 hpne, mul_log_div_aux (by linarith : (0:ℝ) ≤ 1 - t) h1pne]
  ring

/-- `J_p` is measurable. -/
theorem measurable_Jp (p : ℝ) : Measurable (Jp p) := by
  unfold Jp
  fun_prop

/-- `J_p` is continuous on `[0,1]`. -/
theorem continuousOn_Jp_Icc {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (Jp p) (Set.Icc 0 1) := by
  have hcont : Continuous (fun t => entIntegrand t - t * Real.log p - (1 - t) * Real.log (1 - p)) :=
    (continuous_entIntegrand.sub (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)
  apply hcont.continuousOn.congr
  intro t ht
  exact Jp_eq_entIntegrand hp0 hp1 ht.1 ht.2

namespace Graphon
variable (W : Graphon)

/-- `∫ z, 1 ∂gμ = 1` (the graphon measure is a probability measure). -/
theorem integral_one : ∫ _ : ℝ × ℝ, (1:ℝ) ∂gμ = 1 := by simp

/-! ## Relabelling invariance

A relabelling of `[0,1]` changes none of the graphon functionals: the pair measure `gμ` is
invariant under `(σ,σ)`, so every integral of a measurable function of the kernel is.
-/

/-- Integrals of a measurable function of the kernel are invariant under relabelling. -/
theorem integral_comp_relabel {σ : ℝ → ℝ} (hσ : MeasurePreserving σ unitμ unitμ)
    {g : ℝ → ℝ} (hg : Measurable g) (W : Graphon) :
    ∫ z, g (W.toFun (σ z.1) (σ z.2)) ∂gμ = ∫ z, g (W.toFun z.1 z.2) ∂gμ := by
  have hmp : MeasurePreserving (Prod.map σ σ) gμ gμ := hσ.prod hσ
  have hmeas : Measurable fun z : ℝ × ℝ => g (W.toFun z.1 z.2) := hg.comp W.meas'
  have h := integral_map (μ := gμ) (φ := Prod.map σ σ) hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hmeas.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

/-- The edge density is invariant under relabelling. -/
theorem edgeDensity_relabel {W W' : Graphon} {σ : ℝ → ℝ}
    (hσ : MeasurePreserving σ unitμ unitμ)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) :
    W'.edgeDensity = W.edgeDensity := by
  rw [edgeDensity, edgeDensity, integral_congr_ae h]
  exact integral_comp_relabel hσ measurable_id W

/-- The entropy is invariant under relabelling. -/
theorem entropy_relabel {W W' : Graphon} {σ : ℝ → ℝ}
    (hσ : MeasurePreserving σ unitμ unitμ)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) :
    W'.entropy = W.entropy := by
  rw [entropy, entropy]
  congr 1
  rw [integral_congr_ae (h.mono fun z hz => by rw [hz])]
  exact integral_comp_relabel hσ measurable_entIntegrand W

/-- The cost functional is invariant under relabelling. -/
theorem Ip_relabel {W W' : Graphon} {σ : ℝ → ℝ} (p : ℝ)
    (hσ : MeasurePreserving σ unitμ unitμ)
    (h : ∀ᵐ z ∂gμ, W'.toFun z.1 z.2 = W.toFun (σ z.1) (σ z.2)) :
    W'.Ip p = W.Ip p := by
  rw [Ip, Ip, integral_congr_ae (h.mono fun z hz => by rw [hz])]
  exact integral_comp_relabel hσ (measurable_Jp p) W

/-- `I_p(W) = -2 s(W) - log(1-p) + e(W) log((1-p)/p)`. -/
theorem Ip_eq_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    W.Ip p = -2 * W.entropy - Real.log (1 - p) + W.edgeDensity * Real.log ((1 - p) / p) := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1pne : (1 - p) ≠ 0 := ne_of_gt (by linarith)
  -- integrabilities
  have hI_ent : Integrable (fun z : ℝ × ℝ => entIntegrand (W.toFun z.1 z.2)) gμ :=
    W.integrable_comp measurable_entIntegrand continuous_entIntegrand.continuousOn
  have hI_W : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2) gμ := W.integrable_self
  have hI_B : Integrable (fun z : ℝ × ℝ => W.toFun z.1 z.2 * Real.log p) gμ := hI_W.mul_const _
  have hI_1mW : Integrable (fun z : ℝ × ℝ => (1 - W.toFun z.1 z.2)) gμ :=
    (integrable_const (1:ℝ)).sub hI_W
  have hI_C : Integrable (fun z : ℝ × ℝ => (1 - W.toFun z.1 z.2) * Real.log (1 - p)) gμ :=
    hI_1mW.mul_const _
  -- rewrite the integrand of `I_p` pointwise
  have hcongr : W.Ip p = ∫ z, (entIntegrand (W.toFun z.1 z.2)
      - W.toFun z.1 z.2 * Real.log p - (1 - W.toFun z.1 z.2) * Real.log (1 - p)) ∂gμ := by
    unfold Graphon.Ip
    apply integral_congr_ae
    apply ae_of_all
    intro z
    exact Jp_eq_entIntegrand hp0 hp1 (W.nonneg' z.1 z.2) (W.le_one' z.1 z.2)
  rw [hcongr]
  -- split the integral (applied at term level to avoid `rw`-under-binder matching)
  have e1 : ∫ z, (entIntegrand (W.toFun z.1 z.2) - W.toFun z.1 z.2 * Real.log p
        - (1 - W.toFun z.1 z.2) * Real.log (1 - p)) ∂gμ
      = (∫ z, (entIntegrand (W.toFun z.1 z.2) - W.toFun z.1 z.2 * Real.log p) ∂gμ)
        - ∫ z, (1 - W.toFun z.1 z.2) * Real.log (1 - p) ∂gμ :=
    integral_sub (hI_ent.sub hI_B) hI_C
  have e2 : ∫ z, (entIntegrand (W.toFun z.1 z.2) - W.toFun z.1 z.2 * Real.log p) ∂gμ
      = (∫ z, entIntegrand (W.toFun z.1 z.2) ∂gμ) - ∫ z, W.toFun z.1 z.2 * Real.log p ∂gμ :=
    integral_sub hI_ent hI_B
  have e3 : ∫ z, W.toFun z.1 z.2 * Real.log p ∂gμ
      = (∫ z, W.toFun z.1 z.2 ∂gμ) * Real.log p := integral_mul_const _ _
  have e4 : ∫ z, (1 - W.toFun z.1 z.2) * Real.log (1 - p) ∂gμ
      = (∫ z, (1 - W.toFun z.1 z.2) ∂gμ) * Real.log (1 - p) := integral_mul_const _ _
  -- `∫ (1 - W) = 1 - e(W)`
  have hsub : ∫ z, (1 - W.toFun z.1 z.2) ∂gμ = 1 - W.edgeDensity := by
    rw [integral_sub (integrable_const 1) hI_W, integral_one]; rfl
  -- relate `∫ entIntegrand` to entropy
  have hent : ∫ z, entIntegrand (W.toFun z.1 z.2) ∂gμ = -2 * W.entropy := by
    unfold Graphon.entropy entIntegrand
    ring
  rw [e1, e2, e3, e4, hsub, hent, Real.log_div h1pne hpne]
  unfold Graphon.edgeDensity
  ring

end Graphon

end UpperTailMultipodality
