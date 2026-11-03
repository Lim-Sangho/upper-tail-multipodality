import UpperTailMultipodality.Preliminaries.Graphons.CutMetric
import UpperTailMultipodality.Preliminaries.Graphons.Functionals

/-!
# Cut convergence and the graph-limit inputs

The paper uses four standard facts of dense graph-limit theory (Lovász, *Large Networks and Graph
Limits*; Chatterjee–Varadhan), recorded in `sec:graphons`:

* the cut-metric quotient `W̃₀` is **sequentially compact** (`cut_seqCompact`);
* the edge density `e(·)` is **continuous in the cut metric** (`edgeDensity_cutContinuous`);
* the homomorphism density `t(H,·)` is **continuous in the cut metric**
  (`tDensity_cutContinuous`);
* the cost `I_p` is **lower semicontinuous in the cut metric**
  (`Ip_cut_lowerSemicontinuous`).

They are not re-proved here and are recorded **as axioms**, phrased through the predicate
`CutTendsto` (cut convergence of a sequence of graphons).  Attainment of the infimum of
`eq:joint-variational-problem` with `s = 1` is the theorem `feasible_attains` in
`Preliminaries/Graphons/Attainment.lean`, derived from three of these axioms.
-/

namespace UpperTailMultipodality

open MeasureTheory Filter Topology

/-- **Cut-metric convergence** of a sequence of graphons `W n` to a limit graphon `Wlim`:
the cut distances `δ_□(W n, Wlim)` tend to `0`. -/
def CutTendsto (W : ℕ → Graphon) (Wlim : Graphon) : Prop :=
  Filter.Tendsto (fun n => cutDist (W n) Wlim) Filter.atTop (nhds 0)

/-! ### Cut distance depends only on the a.e. class. -/

/-- The iterated integral over any `S × T` depends only on the a.e. class of the kernel
(w.r.t. the product measure `gμ`). -/
theorem iter_integral_congr_ae {U V : ℝ → ℝ → ℝ}
    (h : (fun z : ℝ × ℝ => U z.1 z.2) =ᵐ[gμ] fun z => V z.1 z.2) (S T : Set ℝ) :
    (∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ) = ∫ x in S, ∫ y in T, V x y ∂unitμ ∂unitμ := by
  have h' : (fun z : ℝ × ℝ => U z.1 z.2) =ᵐ[unitμ.prod unitμ] fun z => V z.1 z.2 := h
  have hae := MeasureTheory.Measure.ae_ae_of_ae_prod h'
  have hinner : (fun x => ∫ y in T, U x y ∂unitμ) =ᵐ[unitμ] fun x => ∫ y in T, V x y ∂unitμ := by
    filter_upwards [hae] with x hx
    exact integral_congr_ae (Filter.EventuallyEq.restrict hx)
  exact integral_congr_ae hinner.restrict

/-- **`cutNorm` depends only on the a.e. class** of the kernel. -/
theorem cutNorm_congr_ae {U V : ℝ → ℝ → ℝ}
    (h : (fun z : ℝ × ℝ => U z.1 z.2) =ᵐ[gμ] fun z => V z.1 z.2) :
    cutNorm U = cutNorm V := by
  unfold cutNorm
  have hset : {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
        v = |∫ x in S, ∫ y in T, U x y ∂unitμ ∂unitμ|}
      = {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
        v = |∫ x in S, ∫ y in T, V x y ∂unitμ ∂unitμ|} := by
    ext v
    constructor
    · rintro ⟨S, T, hS, hT, rfl⟩
      exact ⟨S, T, hS, hT, by rw [iter_integral_congr_ae h S T]⟩
    · rintro ⟨S, T, hS, hT, rfl⟩
      exact ⟨S, T, hS, hT, by rw [iter_integral_congr_ae h S T]⟩
  rw [hset]

/-- **`cutDist` is invariant under a.e.-modification of its second argument.**  If `W'` and
`W''` agree a.e. then `δ_□(W, W') = δ_□(W, W'')`. -/
theorem cutDist_congr_right_ae {W W' W'' : Graphon}
    (h : (fun z : ℝ × ℝ => W'.toFun z.1 z.2) =ᵐ[gμ] fun z => W''.toFun z.1 z.2) :
    cutDist W W' = cutDist W W'' := by
  unfold cutDist
  have hset : {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
        v = cutNorm fun x y => W.toFun x y - W'.toFun (σ x) (σ y)}
      = {v | ∃ σ : ℝ → ℝ, IsRelabelling σ ∧
        v = cutNorm fun x y => W.toFun x y - W''.toFun (σ x) (σ y)} := by
    have key : ∀ σ : ℝ → ℝ, IsRelabelling σ →
        (cutNorm fun x y => W.toFun x y - W'.toFun (σ x) (σ y))
          = cutNorm fun x y => W.toFun x y - W''.toFun (σ x) (σ y) := by
      intro σ hσ
      have hmp : MeasurePreserving (Prod.map σ σ) gμ gμ :=
        hσ.measurePreserving.prod hσ.measurePreserving
      have hpull : (fun z : ℝ × ℝ => W'.toFun (σ z.1) (σ z.2)) =ᵐ[gμ]
          fun z => W''.toFun (σ z.1) (σ z.2) := hmp.quasiMeasurePreserving.ae_eq h
      refine cutNorm_congr_ae ?_
      filter_upwards [hpull] with z hz
      rw [hz]
    ext v
    constructor
    · rintro ⟨σ, hσ, rfl⟩; exact ⟨σ, hσ, key σ hσ⟩
    · rintro ⟨σ, hσ, rfl⟩; exact ⟨σ, hσ, (key σ hσ).symm⟩
  rw [hset]

/-- **Sequential compactness of the cut-metric quotient** (Lovász).  Every
sequence of graphons has a subsequence converging in cut distance to some graphon. -/
axiom cut_seqCompact (W : ℕ → Graphon) :
    ∃ (φ : ℕ → ℕ) (Wlim : Graphon), StrictMono φ ∧ CutTendsto (fun n => W (φ n)) Wlim

/-- **Cut-continuity of the edge density** (Lovász).  If `W n → Wlim` in the cut
metric then `e(W n) → e(Wlim)`. -/
axiom edgeDensity_cutContinuous {W : ℕ → Graphon} {Wlim : Graphon} (h : CutTendsto W Wlim) :
    Filter.Tendsto (fun n => (W n).edgeDensity) Filter.atTop (nhds Wlim.edgeDensity)

/-- **Cut-continuity of homomorphism densities** (Lovász).  If `W n → Wlim` in the
cut metric then `t(H, W n) → t(H, Wlim)`. -/
axiom tDensity_cutContinuous {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {W : ℕ → Graphon} {Wlim : Graphon}
    (h : CutTendsto W Wlim) :
    Filter.Tendsto (fun n => (W n).tDensity H) Filter.atTop (nhds (Wlim.tDensity H))

/-- **Lower semicontinuity of `I_p` in the cut metric** (Chatterjee–Varadhan
rate function), in sublevel-closedness form — equivalent to lower semicontinuity: the
sublevel sets `{W : I_p(W) ≤ C}` are cut-closed.  Concretely, if `W n → Wlim` in the cut
metric and `I_p(W n) ≤ C` eventually, then `I_p(Wlim) ≤ C`. -/
axiom Ip_cut_lowerSemicontinuous {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {W : ℕ → Graphon} {Wlim : Graphon} (h : CutTendsto W Wlim) {C : ℝ}
    (hC : ∀ᶠ n in Filter.atTop, (W n).Ip p ≤ C) :
    Wlim.Ip p ≤ C

end UpperTailMultipodality
