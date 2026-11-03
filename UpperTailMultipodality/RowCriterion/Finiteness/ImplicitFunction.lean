import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions

/-!
# A real-analytic implicit function theorem with local uniqueness

`analytic_implicit_unique`: given `F : E → P → E` (unknown in a complete real normed space `E`,
parameter in a complete real normed space `P`) jointly analytic at `(z₀, p₀)` with
`F z₀ p₀ = 0` and invertible partial `z`-derivative `L`, there are neighbourhoods `S ∋ z₀`,
`T ∋ p₀` and an analytic map `z : P → E` through `z₀` such that, for `p ∈ T`, `z p` is the
unique zero of `F · p` in `S`.

The proof is the Φ-trick: `Φ(z,p) = (F z p, p)` has a block upper-triangular invertible strict
derivative, so the analytic inverse function theorem applies to it, and its injectivity clause
is the local uniqueness.  This is the analytic implicit function theorem cited in the proof of
`lem:row-finite`; the development is
taken from the companion formalization `UpperTailOptimizers.LZBoundary.AnalyticIFT`.
-/

open Filter Topology

namespace UpperTailMultipodality

/-- **Real-analytic inverse function theorem** (Krantz–Parks, Theorem 2.5.1).

If `F : E → E` is analytic at `z₀` with invertible strict derivative `L`, then there are
open neighbourhoods `S ∋ z₀` and `T ∋ F z₀`, and an analytic map `Γ : E → E`, such that `F`
maps `S` into `T`, `Γ` maps `T` into `S`, the two are mutually inverse there, and — the
clause that `analytic_implicit` does *not* give — `F` is **injective** on `S`.

Everything is read off the local homeomorphism `HasStrictFDerivAt.toOpenPartialHomeomorph`
attached to `F` at `z₀`; analyticity of its inverse is
`OpenPartialHomeomorph.analyticAt_symm'`. -/
theorem analytic_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ : E} (hF : AnalyticAt ℝ F z₀) (L : E ≃L[ℝ] E)
    (hL : HasStrictFDerivAt F (L : E →L[ℝ] E) z₀) :
    ∃ (S T : Set E) (Γ : E → E),
      IsOpen S ∧ z₀ ∈ S ∧ IsOpen T ∧ F z₀ ∈ T ∧
      Set.MapsTo F S T ∧ Set.MapsTo Γ T S ∧
      (∀ z ∈ S, Γ (F z) = z) ∧ (∀ y ∈ T, F (Γ y) = y) ∧
      Set.InjOn F S ∧ AnalyticAt ℝ Γ (F z₀) := by
  classical
  set R : OpenPartialHomeomorph E E := hL.toOpenPartialHomeomorph F with hRdef
  have hRcoe : (R : E → E) = F := rfl
  have hsrc : z₀ ∈ R.source := hL.mem_toOpenPartialHomeomorph_source
  have htgt : F z₀ ∈ R.target := hL.image_mem_toOpenPartialHomeomorph_target
  have hfderiv : fderiv ℝ (R : E → E) z₀ = (L : E →L[ℝ] E) := by
    rw [hRcoe]; exact hL.hasFDerivAt.fderiv
  have hsymm : AnalyticAt ℝ R.symm (R z₀) :=
    R.analyticAt_symm' (i := L) hsrc (by rw [hRcoe]; exact hF) hfderiv
  refine ⟨R.source, R.target, R.symm, R.open_source, hsrc, R.open_target, htgt,
    ?_, ?_, ?_, ?_, R.injOn, ?_⟩
  · intro z hz; exact R.map_source hz
  · intro y hy; exact R.map_target hy
  · intro z hz; exact R.left_inv hz
  · intro y hy; exact R.right_inv hy
  · rw [hRcoe] at hsymm; exact hsymm

/-- **Real-analytic implicit function theorem, with local uniqueness.**

Same hypotheses as `analytic_implicit`: `F : E → P → E` is jointly analytic at `(z₀, p₀)`,
vanishes there, and its partial `z`-derivative at the base point is the continuous linear
equivalence `L`.  The conclusion adds explicit neighbourhoods `S ∋ z₀` and `T ∋ p₀` and the
uniqueness clause: for `p ∈ T`, the point `z p` is the *only* `w ∈ S` with `F w p = 0`.

The proof is the Φ-trick of `analytic_implicit` — `Φ (z, p) = (F z p, p)` has block
upper-triangular invertible strict derivative, so `analytic_inverse` applies to it — but it
keeps the `Set.InjOn Φ` clause that `analytic_implicit` discards. -/
theorem analytic_implicit_unique {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : E → P → E} {z₀ : E} {p₀ : P}
    (hF : AnalyticAt ℝ (fun w : E × P => F w.1 w.2) (z₀, p₀))
    (hF0 : F z₀ p₀ = 0)
    (L : E ≃L[ℝ] E)
    (hL : HasStrictFDerivAt (fun z : E => F z p₀) (L : E →L[ℝ] E) z₀) :
    ∃ (S : Set E) (T : Set P) (z : P → E),
      IsOpen S ∧ z₀ ∈ S ∧ IsOpen T ∧ p₀ ∈ T ∧
      z p₀ = z₀ ∧ AnalyticAt ℝ z p₀ ∧
      (∀ p ∈ T, z p ∈ S) ∧
      (∀ p ∈ T, F (z p) p = 0) ∧
      (∀ p ∈ T, ∀ w ∈ S, F w p = 0 → w = z p) := by
  classical
  -- The augmented map and its strict derivative, exactly as in `analytic_implicit`.
  set Φ : E × P → E × P := fun w => (F w.1 w.2, w.2) with hΦdef
  set Fjoint : E × P → E := fun w => F w.1 w.2 with hFjdef
  set G : (E × P) →L[ℝ] E := fderiv ℝ Fjoint (z₀, p₀) with hGdef
  have hGstrict : HasStrictFDerivAt Fjoint G (z₀, p₀) := hF.hasStrictFDerivAt
  set inlCLM : E →L[ℝ] (E × P) :=
    (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] P) with hinldef
  have hincl : HasStrictFDerivAt (fun z : E => (z, p₀)) inlCLM z₀ :=
    (hasStrictFDerivAt_id z₀).prodMk (hasStrictFDerivAt_const p₀ z₀)
  have hrestr : HasStrictFDerivAt (fun z : E => F z p₀) (G.comp inlCLM) z₀ := by
    have := hGstrict.comp z₀ hincl
    simpa [hFjdef] using this
  have hGL : G.comp inlCLM = (L : E →L[ℝ] E) :=
    hrestr.hasFDerivAt.unique hL.hasFDerivAt
  set inrCLM : P →L[ℝ] (E × P) :=
    (0 : P →L[ℝ] E).prod (ContinuousLinearMap.id ℝ P) with hinrdef
  set B : P →L[ℝ] E := G.comp inrCLM with hBdef
  have hGdecomp : ∀ w : E × P, G w = L w.1 + B w.2 := by
    intro w
    have hsplit : w = inlCLM w.1 + inrCLM w.2 := by
      simp [hinldef, hinrdef]
    calc
      G w = G (inlCLM w.1 + inrCLM w.2) := by rw [← hsplit]
      _ = G (inlCLM w.1) + G (inrCLM w.2) := by rw [map_add]
      _ = (G.comp inlCLM) w.1 + (G.comp inrCLM) w.2 := by
            simp [ContinuousLinearMap.comp_apply]
      _ = L w.1 + B w.2 := by simp only [hGL, hBdef, ContinuousLinearEquiv.coe_coe]
  set DΦ : ((E × P)) →L[ℝ] (E × P) :=
    G.prod (ContinuousLinearMap.snd ℝ E P) with hDΦdef
  have hΦstrict : HasStrictFDerivAt Φ DΦ (z₀, p₀) := by
    have h2 : HasStrictFDerivAt (fun w : E × P => w.2)
        (ContinuousLinearMap.snd ℝ E P) (z₀, p₀) := hasStrictFDerivAt_snd
    have := hGstrict.prodMk h2
    simpa [hΦdef, hFjdef, hDΦdef] using this
  set Ψ : (E × P) →L[ℝ] (E × P) :=
    ((L.symm : E →L[ℝ] E).comp
        ((ContinuousLinearMap.fst ℝ E P)
          - B.comp (ContinuousLinearMap.snd ℝ E P))).prod
      (ContinuousLinearMap.snd ℝ E P) with hΨdef
  have hΨapply : ∀ w : E × P, Ψ w = (L.symm (w.1 - B w.2), w.2) := by
    intro w
    simp [hΨdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  have hDΦapply : ∀ w : E × P, DΦ w = (G w, w.2) := by
    intro w
    simp [hDΦdef, ContinuousLinearMap.prod_apply]
  have hleft : Function.LeftInverse Ψ DΦ := by
    intro w
    rw [hDΦapply w, hΨapply]
    simp only
    have : G w - B w.2 = L w.1 := by rw [hGdecomp w]; abel
    rw [this]
    simp
  have hright : Function.RightInverse Ψ DΦ := by
    intro w
    rw [hΨapply w, hDΦapply]
    simp only
    have hG' : G (L.symm (w.1 - B w.2), w.2) = w.1 := by
      rw [hGdecomp]
      simp
    rw [hG']
  set DΦcle : (E × P) ≃L[ℝ] (E × P) :=
    ContinuousLinearEquiv.equivOfInverse DΦ Ψ hleft hright with hDΦcledef
  have hcle_coe : (DΦcle : (E × P) →L[ℝ] (E × P)) = DΦ := rfl
  have hΦstrict' : HasStrictFDerivAt Φ (DΦcle : (E × P) →L[ℝ] (E × P)) (z₀, p₀) := by
    rw [hcle_coe]; exact hΦstrict
  have hΦ0 : Φ (z₀, p₀) = (0, p₀) := by simp [hΦdef, hF0]
  have hΦanalytic : AnalyticAt ℝ Φ (z₀, p₀) := by
    have hsnd : AnalyticAt ℝ (fun w : E × P => w.2) (z₀, p₀) := analyticAt_snd
    have := hF.prod hsnd
    simpa [hΦdef, hFjdef] using this
  -- The analytic inverse function theorem, *with* its injectivity clause.
  obtain ⟨S', T', Γ, hS'open, hmemS', hT'open, hmemT', _hmapsΦ, _hmapsΓ, hΓΦ, hΦΓ, hinj,
    hΓan⟩ := analytic_inverse hΦanalytic DΦcle hΦstrict'
  rw [hΦ0] at hmemT' hΓan
  -- The implicit family.
  set z : P → E := fun p => (Γ ((0 : E), p)).1 with hzdef
  have hz0 : z p₀ = z₀ := by
    have h := hΓΦ (z₀, p₀) hmemS'
    rw [hΦ0] at h
    show (Γ ((0 : E), p₀)).1 = z₀
    rw [h]
  have hzan : AnalyticAt ℝ z p₀ := by
    have hmap : AnalyticAt ℝ (fun p : P => ((0 : E), p)) p₀ :=
      AnalyticAt.prod analyticAt_const analyticAt_id
    exact analyticAt_fst.comp (hΓan.comp hmap)
  -- Shrink the source neighbourhood `S'` to a product box `S ×ˢ T₀`.
  obtain ⟨S, T₀, hSopen, hT₀open, hz₀S, hp₀T₀, hbox⟩ :=
    isOpen_prod_iff.mp hS'open z₀ p₀ hmemS'
  -- Cut the parameter set down to those `p` for which the family behaves.
  set A : Set P := {p : P | p ∈ T₀ ∧ ((0 : E), p) ∈ T' ∧ z p ∈ S} with hAdef
  have hA : A ∈ 𝓝 p₀ := by
    have h1 : ∀ᶠ p in 𝓝 p₀, p ∈ T₀ := hT₀open.eventually_mem hp₀T₀
    have h2 : ∀ᶠ p in 𝓝 p₀, ((0 : E), p) ∈ T' := by
      have hc : ContinuousAt (fun p : P => ((0 : E), p)) p₀ := by fun_prop
      exact hc.eventually (hT'open.eventually_mem hmemT')
    have h3 : ∀ᶠ p in 𝓝 p₀, z p ∈ S := by
      have : z p₀ ∈ S := by rw [hz0]; exact hz₀S
      exact hzan.continuousAt.eventually (hSopen.eventually_mem this)
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3 using ⟨hp1, hp2, hp3⟩
  -- For every `p ∈ A`, the inverse map really does invert `Φ` over `(0, p)`.
  have hkey : ∀ p ∈ A, (Γ ((0 : E), p)).2 = p ∧ F (z p) p = 0 := by
    intro p hp
    have h := hΦΓ ((0 : E), p) hp.2.1
    have hsnd : (Γ ((0 : E), p)).2 = p := by
      have := congrArg Prod.snd h
      simpa [hΦdef] using this
    refine ⟨hsnd, ?_⟩
    have hfst : F (Γ ((0 : E), p)).1 (Γ ((0 : E), p)).2 = 0 := by
      have := congrArg Prod.fst h
      simpa [hΦdef] using this
    rw [hsnd] at hfst
    exact hfst
  refine ⟨S, interior A, z, hSopen, hz₀S, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hA, hz0, hzan, ?_, ?_, ?_⟩
  · intro p hp
    exact (interior_subset hp).2.2
  · intro p hp
    exact (hkey p (interior_subset hp)).2
  · intro p hp w hwS hw
    have hp' : p ∈ A := interior_subset hp
    have hmem1 : (w, p) ∈ S' := hbox (Set.mk_mem_prod hwS hp'.1)
    have hmem2 : (z p, p) ∈ S' := hbox (Set.mk_mem_prod hp'.2.2 hp'.1)
    have hΦw : Φ (w, p) = ((0 : E), p) := by simp [hΦdef, hw]
    have hΦz : Φ (z p, p) = ((0 : E), p) := by simp [hΦdef, (hkey p hp').2]
    have := hinj hmem1 hmem2 (hΦw.trans hΦz.symm)
    exact congrArg Prod.fst this


end UpperTailMultipodality
