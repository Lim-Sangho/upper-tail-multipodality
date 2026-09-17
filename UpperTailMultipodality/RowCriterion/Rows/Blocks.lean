import UpperTailMultipodality.RowCriterion.Rows.Resampling

/-!
# Blocks of equal rows (proof of `thm:row-criterion`, last step)

For a row `g`, the block `{x | W_x = g almost everywhere}` of a graphon `W` is measurable, and
`W(x,y) = g(y)` for almost every `(x,y)` with `x` in the block.  If almost every row of `W`
lies in a set of rows that is finite and totally ordered up to null sets, then `W` is
multipodal with ordered blocks (`isOrderedMultipodal_of_rows`).
-/

namespace UpperTailMultipodality.Rows

open MeasureTheory Filter

/-- The block `{x | W_x = g almost everywhere}` of rows of `W` equal to `g`. -/
def rowBlock (W : Graphon) (g : ℝ → ℝ) : Set ℝ := {x | W.row x =ᵐ[unitμ] g}

/-- Membership in a block of rows. -/
theorem mem_rowBlock {W : Graphon} {g : ℝ → ℝ} {x : ℝ} :
    x ∈ rowBlock W g ↔ W.row x =ᵐ[unitμ] g := Iff.rfl

/-- Blocks of rows are measurable. -/
theorem measurableSet_rowBlock (W : Graphon) {g : ℝ → ℝ} (hg : IsRow g) :
    MeasurableSet (rowBlock W g) := by
  have hf : Measurable fun z : ℝ × ℝ => |W.toFun z.1 z.2 - g z.2| :=
    (W.measurable_uncurry.sub (hg.1.comp measurable_snd)).abs
  have hI : Measurable fun x => ∫ y, |W.toFun x y - g y| ∂unitμ :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have heq : rowBlock W g = (fun x => ∫ y, |W.toFun x y - g y| ∂unitμ) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_rowBlock]
    have hint : Integrable (fun y => |W.toFun x y - g y|) unitμ := by
      refine integrable_of_abs_le ((W.measurable_uncurry.comp measurable_prodMk_left).sub hg.1
        |>.abs) 1 fun y => ?_
      rw [abs_abs, abs_le]
      constructor <;> linarith [W.nonneg' x y, W.le_one' x y, (hg.2 y).1, (hg.2 y).2]
    rw [integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hint]
    constructor
    · intro h
      filter_upwards [h] with y hy
      simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero]
      exact hy
    · intro h
      filter_upwards [h] with y hy
      simpa [sub_eq_zero] using hy
  rw [heq]
  exact hI (measurableSet_singleton 0)

/-- For almost every `(x,y)` with `x` in the block of `g`, `W(x,y) = g(y)`. -/
theorem ae_eq_of_mem_rowBlock_fst (W : Graphon) {g : ℝ → ℝ} (hg : IsRow g) :
    ∀ᵐ z ∂gμ, z.1 ∈ rowBlock W g → W.toFun z.1 z.2 = g z.2 := by
  have hm : MeasurableSet {z : ℝ × ℝ | z.1 ∈ rowBlock W g → W.toFun z.1 z.2 = g z.2} :=
    MeasurableSet.imp (measurable_fst (measurableSet_rowBlock W hg))
      (measurableSet_eq_fun W.measurable_uncurry (hg.1.comp measurable_snd))
  rw [gμ, Measure.ae_prod_iff_ae_ae hm]
  refine Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ rowBlock W g
  · filter_upwards [mem_rowBlock.mp hx] with y hy _
    exact hy
  · exact Eventually.of_forall fun y h => absurd h hx

/-- For almost every `(x,y)` with `y` in the block of `g`, `W(x,y) = g(x)`. -/
theorem ae_eq_of_mem_rowBlock_snd (W : Graphon) {g : ℝ → ℝ} (hg : IsRow g) :
    ∀ᵐ z ∂gμ, z.2 ∈ rowBlock W g → W.toFun z.1 z.2 = g z.1 := by
  have h := (Measure.measurePreserving_swap (μ := unitμ) (ν := unitμ)).quasiMeasurePreserving.ae
    (ae_eq_of_mem_rowBlock_fst W hg)
  filter_upwards [h] with z hz hz2
  rw [W.symm']
  exact hz hz2

/-- **A function of `y` equal to a function of `x` on a rectangle is constant.**  If
`f(y) = g(x)` for almost every `(x,y) ∈ A × B` and `A` is not null, then there is `x₀ ∈ A` with
`f = g(x₀)` almost everywhere on `B`; moreover `x₀` can be chosen to satisfy any given
almost-everywhere property. -/
theorem exists_mem_ae_eq_of_rectangle {A B : Set ℝ} {f g : ℝ → ℝ} {P : ℝ → Prop}
    (hA : unitμ A ≠ 0) (hP : ∀ᵐ x ∂unitμ, P x)
    (h : ∀ᵐ z ∂gμ, z.1 ∈ A → z.2 ∈ B → f z.2 = g z.1) :
    ∃ x₀ ∈ A, P x₀ ∧ ∀ᵐ y ∂unitμ, y ∈ B → f y = g x₀ := by
  have h' := Measure.ae_ae_of_ae_prod h
  obtain ⟨x₀, hx₀A, hx₀P, hx₀⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hA (ae_restrict_of_ae (hP.and h'))
  refine ⟨x₀, hx₀A, hx₀P, ?_⟩
  filter_upwards [hx₀] with y hy
  exact hy hx₀A

/-- The average of a function that is almost everywhere constant on a set of positive measure
is that constant. -/
theorem setIntegral_div_eq_of_ae_eq {B : Set ℝ} {f : ℝ → ℝ} {c : ℝ} (hB : MeasurableSet B)
    (hB0 : unitμ B ≠ 0) (h : ∀ᵐ y ∂unitμ, y ∈ B → f y = c) :
    (∫ y in B, f y ∂unitμ) / unitμ.real B = c := by
  have hpos : unitμ.real B ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hB0, measure_ne_top _ _⟩
  rw [setIntegral_congr_ae hB h, setIntegral_const, smul_eq_mul, mul_div_cancel_left₀ _ hpos]

/-- Two rows in a totally ordered family with equal means agree almost everywhere. -/
theorem ae_eq_of_integral_eq_of_le {u₁ u₂ : ℝ → ℝ} (hu₁ : IsRow u₁) (hu₂ : IsRow u₂)
    (hle : u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁)
    (heq : ∫ y, u₁ y ∂unitμ = ∫ y, u₂ y ∂unitμ) : u₁ =ᵐ[unitμ] u₂ := by
  rcases hle with h | h
  · exact (integral_eq_iff_of_ae_le (integrable_of_isRow hu₁) (integrable_of_isRow hu₂) h).mp heq
  · exact ((integral_eq_iff_of_ae_le (integrable_of_isRow hu₂) (integrable_of_isRow hu₁) h).mp
      heq.symm).symm

/-- A set of rows that is finite and totally ordered up to null sets has a finite covering
family of representatives lying in the set. -/
theorem exists_finset_subset_of_finite {M : Set (ℝ → ℝ)}
    (hfin : ∃ g : Finset (ℝ → ℝ), ∀ u ∈ M, ∃ g' ∈ g, u =ᵐ[unitμ] g') :
    ∃ S : Finset (ℝ → ℝ), (∀ s ∈ S, s ∈ M) ∧ ∀ u ∈ M, ∃ s ∈ S, u =ᵐ[unitμ] s := by
  classical
  obtain ⟨g, hg⟩ := hfin
  refine ⟨(g.filter fun g' => ∃ u ∈ M, u =ᵐ[unitμ] g').image
    fun g' => if h : ∃ u ∈ M, u =ᵐ[unitμ] g' then h.choose else g', ?_, ?_⟩
  · intro s hs
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hs
    have hex := (Finset.mem_filter.mp hg').2
    rw [dif_pos hex]
    exact hex.choose_spec.1
  · intro u hu
    obtain ⟨g', hg'mem, hug'⟩ := hg u hu
    have hex : ∃ u ∈ M, u =ᵐ[unitμ] g' := ⟨u, hu, hug'⟩
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hg'mem, hex⟩), ?_⟩
    rw [dif_pos hex]
    exact hug'.trans hex.choose_spec.2.symm

/-- **Rows from a finite chain give ordered blocks.**  If `M` is a set of rows that is finite
and totally ordered up to null sets, and almost every row of `W` lies in `M`, then `W` is
multipodal with ordered blocks. -/
theorem isOrderedMultipodal_of_rows (W : Graphon) {M : Set (ℝ → ℝ)}
    (hMrow : ∀ u ∈ M, IsRow u)
    (hfin : ∃ g : Finset (ℝ → ℝ), ∀ u ∈ M, ∃ g' ∈ g, u =ᵐ[unitμ] g')
    (hchain : ∀ u₁ ∈ M, ∀ u₂ ∈ M, u₁ ≤ᵐ[unitμ] u₂ ∨ u₂ ≤ᵐ[unitμ] u₁)
    (hrows : ∀ᵐ x ∂unitμ, W.row x ∈ M) : IsOrderedMultipodal W := by
  classical
  obtain ⟨S, hSM, hScov⟩ := exists_finset_subset_of_finite hfin
  -- the representatives with non-null blocks, sorted by their means
  obtain ⟨T, hT⟩ : ∃ T : Finset (ℝ → ℝ), T = S.filter fun s => unitμ (rowBlock W s) ≠ 0 :=
    ⟨_, rfl⟩
  have hTS : ∀ s ∈ T, s ∈ S ∧ unitμ (rowBlock W s) ≠ 0 := fun s hs => by
    rw [hT] at hs; exact Finset.mem_filter.mp hs
  obtain ⟨Mn, hMn⟩ : ∃ Mn : Finset ℝ, Mn = T.image fun s => ∫ y, s y ∂unitμ := ⟨_, rfl⟩
  have hr : ∀ k : Fin Mn.card, ∃ s ∈ T, ∫ y, s y ∂unitμ = Mn.orderEmbOfFin rfl k := by
    intro k
    have hk : Mn.orderEmbOfFin rfl k ∈ T.image fun s => ∫ y, s y ∂unitμ := by
      rw [← hMn]; exact Finset.orderEmbOfFin_mem Mn rfl k
    exact Finset.mem_image.mp hk
  choose r hrT hrmean using hr
  have hrM : ∀ k, r k ∈ M := fun k => hSM _ (hTS _ (hrT k)).1
  have hrrow : ∀ k, IsRow (r k) := fun k => hMrow _ (hrM k)
  have hr0 : ∀ k, unitμ (rowBlock W (r k)) ≠ 0 := fun k => (hTS _ (hrT k)).2
  have hrm : ∀ k, MeasurableSet (rowBlock W (r k)) := fun k =>
    measurableSet_rowBlock W (hrrow k)
  -- the representatives are strictly increasing
  have hr_le : ∀ i j, i ≤ j → r i ≤ᵐ[unitμ] r j := by
    intro i j hij
    rcases hchain _ (hrM i) _ (hrM j) with h | h
    · exact h
    · have hint :=
        integral_mono_ae (integrable_of_isRow (hrrow j)) (integrable_of_isRow (hrrow i)) h
      rw [hrmean, hrmean, (Mn.orderEmbOfFin rfl).le_iff_le] at hint
      have : i = j := le_antisymm hij hint
      subst this
      exact h
  have hr_inj : ∀ i j, r i =ᵐ[unitμ] r j → i = j := by
    intro i j h
    have := integral_congr_ae h
    rw [hrmean, hrmean] at this
    exact (Mn.orderEmbOfFin rfl).injective this
  -- the block values
  have hrect : ∀ i j, ∀ᵐ z ∂gμ, z.1 ∈ rowBlock W (r i) → z.2 ∈ rowBlock W (r j) →
      r i z.2 = r j z.1 := by
    intro i j
    filter_upwards [ae_eq_of_mem_rowBlock_fst W (hrrow i), ae_eq_of_mem_rowBlock_snd W (hrrow j)]
      with z h1 h2 hz1 hz2
    rw [← h1 hz1, h2 hz2]
  have hconst : ∀ i j, (∀ᵐ y ∂unitμ, y ∈ rowBlock W (r j) →
      r i y = (∫ y in rowBlock W (r j), r i y ∂unitμ) / unitμ.real (rowBlock W (r j))) ∧
      (∫ y in rowBlock W (r j), r i y ∂unitμ) / unitμ.real (rowBlock W (r j))
        ∈ Set.Icc (0:ℝ) 1 := by
    intro i j
    obtain ⟨x₀, -, -, hx₀⟩ := exists_mem_ae_eq_of_rectangle (P := fun _ => True) (hr0 i)
      (Eventually.of_forall fun _ => trivial) (hrect i j)
    rw [setIntegral_div_eq_of_ae_eq (hrm j) (hr0 j) hx₀]
    exact ⟨hx₀, (hrrow j).2 x₀⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin Mn.card → Fin Mn.card → ℝ, b = fun i j =>
      (∫ y in rowBlock W (r j), r i y ∂unitμ) / unitμ.real (rowBlock W (r j)) := ⟨_, rfl⟩
  have hbconst : ∀ i j, ∀ᵐ y ∂unitμ, y ∈ rowBlock W (r j) → r i y = b i j := fun i j => by
    rw [hb]; exact (hconst i j).1
  have hbmem : ∀ i j, b i j ∈ Set.Icc (0:ℝ) 1 := fun i j => by
    rw [hb]; exact (hconst i j).2
  have hbsymm : ∀ i j, b i j = b j i := by
    intro i j
    -- pick `x ∈ A_i` with `r_j(x) = b_{ji}` and `r_i(y) = r_j(x)` for a.e. `y ∈ A_j`
    obtain ⟨x, hxA, hxP, hx⟩ := exists_mem_ae_eq_of_rectangle (hr0 i) (hbconst j i) (hrect i j)
    obtain ⟨y, hyA, hy⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae (hr0 j) (ae_restrict_of_ae (hx.and (hbconst i j)))
    rw [← hy.2 hyA, hy.1 hyA, hxP hxA]
  refine ⟨Mn.card,
    { block := fun k => rowBlock W (r k)
      value := b
      measurableSet_block := hrm
      pairwise_disjoint := fun i j hij => Set.disjoint_left.mpr fun x hxi hxj =>
        hij (hr_inj i j ((mem_rowBlock.mp hxi).symm.trans (mem_rowBlock.mp hxj)))
      cover := ?_
      value_symm := hbsymm
      value_mem := hbmem }, ?_, ?_⟩
  · -- almost every `x` lies in a non-null block
    have hnull : ∀ᵐ x ∂unitμ, ∀ s ∈ S, unitμ (rowBlock W s) = 0 → x ∉ rowBlock W s :=
      (eventually_all_finset S).mpr fun s _ => by
        by_cases h0 : unitμ (rowBlock W s) = 0
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx _ using hx
        · exact Eventually.of_forall fun x h => absurd h h0
    filter_upwards [hrows, hnull] with x hx hxn
    obtain ⟨s, hsS, hxs⟩ := hScov _ hx
    have hs0 : unitμ (rowBlock W s) ≠ 0 := fun h0 => hxn s hsS h0 hxs
    have hsT : s ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hsS, hs0⟩
    have hmem : ∫ y, s y ∂unitμ ∈ Set.range (Mn.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin, hMn]
      exact Finset.mem_image_of_mem _ hsT
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, mem_rowBlock.mpr (hxs.trans ?_)⟩
    exact ae_eq_of_integral_eq_of_le (hMrow _ (hSM _ hsS)) (hrrow k)
      (hchain _ (hSM _ hsS) _ (hrM k)) (by rw [hrmean, hk])
  · -- `W = b_{ij}` almost everywhere on `A_i × A_j`
    intro i j
    filter_upwards [ae_eq_of_mem_rowBlock_fst W (hrrow i),
      Measure.quasiMeasurePreserving_snd.ae (hbconst i j)] with z h1 h2 hz1 hz2
    exact (h1 hz1).trans (h2 hz2)
  · -- the block values are ordered
    intro i i' j hii'
    show b i j ≤ b i' j
    rw [hb]
    exact div_le_div_of_nonneg_right
      (setIntegral_mono_ae (integrable_of_isRow (hrrow i)).integrableOn
        (integrable_of_isRow (hrrow i')).integrableOn
        (hr_le i i' hii')) measureReal_nonneg

end UpperTailMultipodality.Rows
