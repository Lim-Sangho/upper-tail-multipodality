import UpperTailMultipodality.Insertion.Rows
import UpperTailMultipodality.Insertion.FirstOrder
import UpperTailMultipodality.FixedDensities.Support.KernelFacts

/-!
# Quantitative estimates for the insertion polynomial

The proof of `lem:degenerate-insertion` follows the insertion of a block of measure `s` while a
second, independent parameter — the smoothing `θ` of `lem:degenerate-smoothing` — also varies.
The bookkeeping therefore needs first-order expansions with constants that do not depend on the
base graphon.  This file collects them:

* `abs_prod_add_sub_le` — the second-order remainder of a product of numbers in `[0,1]`;
* `abs_blockDensity_sub_le` — `T_S` is `m`-Lipschitz in the kernel, uniformly in `S`, and hence
  so are `t(H,·)` (`abs_kernel_tDensity_sub_le`) and `ℛ_{·,W}(u)`
  (`abs_rootedDensity_sub_le_kernel`);
* `abs_derivKernel_sub_le` — `𝒟_W` is `m²`-Lipschitz in `W`;
* `abs_tDensity_line_sub_le` — `t(H, W + ζZ) = t(H,W) + ζ∫∫𝒟_W Z + O(ζ²)`, uniformly in `W`;
* `insertionPoly_taylor` — `Q(s) = t(H,W) + s(∫∫𝒟_W Z + ℛ_W(u) - N t(H,W)) + O(s²)`, uniformly
  in `W`, for the reparametrization `g(s) = s/(1-s)` that keeps the edge density exact;
* `exists_insertGraphon` — the inserted graphon of `eq:vertex-insertion` together with the
  exact values of its three functionals, with an explicit admissibility hypothesis;
* `exists_lipschitz_Jp` — `J_p` is Lipschitz on a compact subinterval of `(0,1)`.
-/

namespace UpperTailMultipodality

namespace FixedDensities

open MeasureTheory Filter Topology Insertion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### A second-order remainder for products -/

/-- **The second-order remainder of a product.**  If `b` and `b + z` take values in `[0,1]` and
`|z| ≤ ρ`, then `∏ (b + z)` agrees with `∏ b + ∑ z_i ∏_{j ≠ i} b_j` up to `|T|²ρ²`. -/
theorem abs_prod_add_sub_le {ι : Type*} [DecidableEq ι] (b z : ι → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hb : ∀ i, b i ∈ Set.Icc (0:ℝ) 1) (hbz : ∀ i, b i + z i ∈ Set.Icc (0:ℝ) 1)
    (hz : ∀ i, |z i| ≤ ρ) (T : Finset ι) :
    |∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i - ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j|
      ≤ (T.card : ℝ) ^ 2 * ρ ^ 2 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hAB : |∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i| ≤ (T.card : ℝ) * ρ := by
      refine (abs_prod_sub_prod_le_sum T _ _ (fun i _ => hbz i) (fun i _ => hb i)).trans ?_
      calc ∑ i ∈ T, |b i + z i - b i| = ∑ i ∈ T, |z i| := by
            refine Finset.sum_congr rfl fun i _ => ?_; ring_nf
        _ ≤ ∑ _i ∈ T, ρ := Finset.sum_le_sum fun i _ => hz i
        _ = (T.card : ℝ) * ρ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hprod : ∏ i ∈ insert a T, (b i + z i) = (b a + z a) * ∏ i ∈ T, (b i + z i) :=
      Finset.prod_insert ha
    have hprodb : ∏ i ∈ insert a T, b i = b a * ∏ i ∈ T, b i := Finset.prod_insert ha
    have hsum : ∑ i ∈ insert a T, z i * ∏ j ∈ (insert a T).erase i, b j
        = z a * ∏ i ∈ T, b i + b a * ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j := by
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [hprod, hprodb, hsum]
    have hkey : (b a + z a) * ∏ i ∈ T, (b i + z i) - b a * ∏ i ∈ T, b i
          - (z a * ∏ i ∈ T, b i + b a * ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j)
        = b a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i - ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j)
          + z a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i) := by ring
    rw [hkey]
    have h1 : |b a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i
        - ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j)| ≤ (T.card : ℝ) ^ 2 * ρ ^ 2 := by
      rw [abs_mul]
      calc |b a| * |∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i - ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j|
          ≤ 1 * ((T.card : ℝ) ^ 2 * ρ ^ 2) := by
            refine mul_le_mul ?_ ih (abs_nonneg _) zero_le_one
            rw [abs_of_nonneg (hb a).1]; exact (hb a).2
        _ = (T.card : ℝ) ^ 2 * ρ ^ 2 := one_mul _
    have h2 : |z a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i)| ≤ ρ * ((T.card : ℝ) * ρ) := by
      rw [abs_mul]
      exact mul_le_mul (hz a) hAB (abs_nonneg _) hρ
    have hcard : ((insert a T).card : ℝ) = (T.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem ha]; push_cast; ring
    have hTc : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    calc |b a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i - ∑ i ∈ T, z i * ∏ j ∈ T.erase i, b j)
            + z a * (∏ i ∈ T, (b i + z i) - ∏ i ∈ T, b i)|
        ≤ (T.card : ℝ) ^ 2 * ρ ^ 2 + ρ * ((T.card : ℝ) * ρ) :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ ((insert a T).card : ℝ) ^ 2 * ρ ^ 2 := by
          rw [hcard]; nlinarith [sq_nonneg ρ, mul_nonneg hTc (sq_nonneg ρ)]

/-! ### Lipschitz bounds in the kernel -/

section Lipschitz

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The integrand of `blockDensity` is bounded and measurable. -/
theorem isBddMeas_blockProd (S : Finset V) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ}
    (hu : IsRow u) {K : Kernel} (hK : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1) :
    IsBddMeas fun y : V → ℝ => ∏ e ∈ H.edgeFinset,
      edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') (pinNew S y) e := by
  refine IsBddMeas.of_mem_Icc ((Finset.measurable_prod _ fun e _ =>
    Insertion.measurable_edgeVal _ (measurable_blockKernel q hu.1 K.meas') e).comp
      (measurable_pinNew S)) fun y => ?_
  exact Insertion.prod_edgeVal_mem_Icc H _ (blockKernel_mem_Icc hq hu.2 hK) _

/-- `T_S ∈ [0,1]` for a kernel with values in `[0,1]`. -/
theorem blockDensity_mem_Icc (S : Finset V) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ}
    (hu : IsRow u) {K : Kernel} (hK : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1) :
    blockDensity H S q u K ∈ Set.Icc (0:ℝ) 1 := by
  have hb := isBddMeas_blockProd H S hq hu hK
  have hmem : ∀ y : V → ℝ, (∏ e ∈ H.edgeFinset,
      edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') (pinNew S y) e)
        ∈ Set.Icc (0:ℝ) 1 := fun y =>
    Insertion.prod_edgeVal_mem_Icc H _ (blockKernel_mem_Icc hq hu.2 hK) _
  unfold blockDensity
  refine ⟨integral_nonneg fun y => (hmem y).1, ?_⟩
  have h := integral_mono hb.integrable
    (integrable_const (μ := Measure.pi fun _ : V => unitμ) (1:ℝ)) fun y => (hmem y).2
  simpa using h

/-- **`T_S` is `m`-Lipschitz in the kernel.** -/
theorem abs_blockDensity_sub_le (S : Finset V) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ}
    (hu : IsRow u) {K L : Kernel} (hK : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1)
    (hL : ∀ x y, L.toFun x y ∈ Set.Icc (0:ℝ) 1) {c : ℝ}
    (hc : ∀ x y, |K.toFun x y - L.toFun x y| ≤ c) :
    |blockDensity H S q u K - blockDensity H S q u L| ≤ (H.edgeFinset.card : ℝ) * c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 0)
  have hKb := isBddMeas_blockProd H S hq hu hK
  have hLb := isBddMeas_blockProd H S hq hu hL
  have hedge : ∀ (y : V → ℝ) (e : Sym2 V),
      |edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') (pinNew S y) e
        - edgeVal (blockKernel q u L.toFun) (blockKernel_symm q u L.symm') (pinNew S y) e| ≤ c := by
    intro y e
    induction e using Sym2.ind with
    | _ a b =>
      show |blockKernel q u K.toFun (pinNew S y a) (pinNew S y b)
        - blockKernel q u L.toFun (pinNew S y a) (pinNew S y b)| ≤ c
      unfold blockKernel
      split_ifs
      · simpa using hc0
      · simpa using hc0
      · simpa using hc0
      · exact hc _ _
  have hpt : ∀ y : V → ℝ, |(∏ e ∈ H.edgeFinset,
        edgeVal (blockKernel q u K.toFun) (blockKernel_symm q u K.symm') (pinNew S y) e)
      - ∏ e ∈ H.edgeFinset,
        edgeVal (blockKernel q u L.toFun) (blockKernel_symm q u L.symm') (pinNew S y) e|
      ≤ (H.edgeFinset.card : ℝ) * c := by
    intro y
    refine (abs_prod_sub_prod_le_sum H.edgeFinset _ _
      (fun e _ => Insertion.edgeVal_mem_Icc _ (blockKernel_mem_Icc hq hu.2 hK) _ e)
      (fun e _ => Insertion.edgeVal_mem_Icc _ (blockKernel_mem_Icc hq hu.2 hL) _ e)).trans ?_
    calc ∑ e ∈ H.edgeFinset, |edgeVal (blockKernel q u K.toFun)
            (blockKernel_symm q u K.symm') (pinNew S y) e
          - edgeVal (blockKernel q u L.toFun) (blockKernel_symm q u L.symm') (pinNew S y) e|
        ≤ ∑ _e ∈ H.edgeFinset, c := Finset.sum_le_sum fun e _ => hedge y e
      _ = (H.edgeFinset.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
  unfold blockDensity
  rw [← integral_sub hKb.integrable hLb.integrable]
  refine (abs_integral_le_integral_abs).trans ?_
  have h := integral_mono ((hKb.integrable.sub hLb.integrable).abs)
    (integrable_const (μ := Measure.pi fun _ : V => unitμ) ((H.edgeFinset.card : ℝ) * c)) hpt
  simpa using h

/-- **`t(H,·)` is `m`-Lipschitz in the kernel.** -/
theorem abs_kernel_tDensity_sub_le {K L : Kernel} (hK : ∀ x y, K.toFun x y ∈ Set.Icc (0:ℝ) 1)
    (hL : ∀ x y, L.toFun x y ∈ Set.Icc (0:ℝ) 1) {c : ℝ}
    (hc : ∀ x y, |K.toFun x y - L.toFun x y| ≤ c) :
    |K.tDensity H - L.tDensity H| ≤ (H.edgeFinset.card : ℝ) * c := by
  have hu : IsRow fun _ : ℝ => (0:ℝ) := ⟨measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
  have h := abs_blockDensity_sub_le H ∅ (q := 0) ⟨le_rfl, zero_le_one⟩ hu hK hL hc
  rwa [blockDensity_empty, blockDensity_empty] at h

/-- **`ℛ_{v,·}(u)` is `m`-Lipschitz in the graphon.** -/
theorem abs_rootedDensity_sub_le_graphon (v : V) {u : ℝ → ℝ} (hu : IsRow u) {G G' : Graphon}
    {c : ℝ} (hc : ∀ x y, |G.toFun x y - G'.toFun x y| ≤ c) :
    |rootedDensity H G v u - rootedDensity H G' v u| ≤ (H.edgeFinset.card : ℝ) * c := by
  have h := abs_blockDensity_sub_le H {v} (q := 0) ⟨le_rfl, zero_le_one⟩ hu
    (K := Kernel.ofGraphon G) (L := Kernel.ofGraphon G') (fun x y => G.mem_Icc x y)
    (fun x y => G'.mem_Icc x y) hc
  rwa [blockDensity_singleton, blockDensity_singleton] at h

/-- **`ℛ_·(u)` is `Nm`-Lipschitz in the graphon.** -/
theorem abs_totalRootedDensity_sub_le_graphon {u : ℝ → ℝ} (hu : IsRow u) {G G' : Graphon}
    {c : ℝ} (hc : ∀ x y, |G.toFun x y - G'.toFun x y| ≤ c) :
    |totalRootedDensity H G u - totalRootedDensity H G' u|
      ≤ (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
  unfold totalRootedDensity
  rw [← Finset.sum_sub_distrib]
  calc |∑ v, (rootedDensity H G v u - rootedDensity H G' v u)|
      ≤ ∑ v, |rootedDensity H G v u - rootedDensity H G' v u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, (H.edgeFinset.card : ℝ) * c :=
        Finset.sum_le_sum fun v _ => abs_rootedDensity_sub_le_graphon H v hu hc
    _ = (Fintype.card V : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`𝒟_W` is `m²`-Lipschitz in `W`.** -/
theorem abs_derivKernel_sub_le {G G' : Graphon} {c : ℝ}
    (hc : ∀ x y, |G.toFun x y - G'.toFun x y| ≤ c) (x y : ℝ) :
    |derivKernel H G x y - derivKernel H G' x y| ≤ (H.edgeFinset.card : ℝ) ^ 2 * c := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 0)
  have hstep : ∀ a b : V, |edgeRemovedDensity H G a b x y - edgeRemovedDensity H G' a b x y|
      ≤ (H.edgeFinset.card : ℝ) * c := by
    intro a b
    have hGi : Integrable (fun ξ : V → ℝ =>
        ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal G.toFun G.symm' (pin ξ a b x y) e)
        (Measure.pi fun _ : V => unitμ) :=
      ((isBddMeas_prod_edgeVal G _).comp (measurable_pin a b x y)).integrable
    have hG'i : Integrable (fun ξ : V → ℝ =>
        ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal G'.toFun G'.symm' (pin ξ a b x y) e)
        (Measure.pi fun _ : V => unitμ) :=
      ((isBddMeas_prod_edgeVal G' _).comp (measurable_pin a b x y)).integrable
    have hpt : ∀ ξ : V → ℝ,
        |(∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal G.toFun G.symm' (pin ξ a b x y) e)
          - ∏ e ∈ H.edgeFinset.erase s(a, b), edgeVal G'.toFun G'.symm' (pin ξ a b x y) e|
        ≤ (H.edgeFinset.card : ℝ) * c := by
      intro ξ
      refine (abs_prod_sub_prod_le_sum _ _ _ (fun e _ => edgeVal_mem_Icc G _ e)
        (fun e _ => edgeVal_mem_Icc G' _ e)).trans ?_
      have hbound : ∀ e ∈ H.edgeFinset.erase s(a, b),
          |edgeVal G.toFun G.symm' (pin ξ a b x y) e
            - edgeVal G'.toFun G'.symm' (pin ξ a b x y) e| ≤ c := by
        intro e _
        induction e using Sym2.ind with
        | _ i j => exact hc _ _
      calc ∑ e ∈ H.edgeFinset.erase s(a, b), |edgeVal G.toFun G.symm' (pin ξ a b x y) e
              - edgeVal G'.toFun G'.symm' (pin ξ a b x y) e|
          ≤ ∑ _e ∈ H.edgeFinset.erase s(a, b), c := Finset.sum_le_sum hbound
        _ = ((H.edgeFinset.erase s(a, b)).card : ℝ) * c := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (H.edgeFinset.card : ℝ) * c := by
            refine mul_le_mul_of_nonneg_right ?_ hc0
            exact_mod_cast Finset.card_erase_le
    unfold edgeRemovedDensity
    rw [← integral_sub hGi hG'i]
    refine abs_integral_le_integral_abs.trans ?_
    have h := integral_mono ((hGi.sub hG'i).abs)
      (integrable_const (μ := Measure.pi fun _ : V => unitμ) ((H.edgeFinset.card : ℝ) * c)) hpt
    simpa using h
  rw [derivKernel_eq_sum, derivKernel_eq_sum, ← mul_sub, abs_mul, ← Finset.sum_sub_distrib]
  have habs : |∑ a, ((∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G a b x y)
      - ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G' a b x y)|
      ≤ 2 * (H.edgeFinset.card : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
    calc |∑ a, ((∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G a b x y)
            - ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G' a b x y)|
        ≤ ∑ a, |(∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G a b x y)
            - ∑ b ∈ H.neighborFinset a, edgeRemovedDensity H G' a b x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ((H.neighborFinset a).card : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← Finset.sum_sub_distrib]
          calc |∑ b ∈ H.neighborFinset a, (edgeRemovedDensity H G a b x y
                  - edgeRemovedDensity H G' a b x y)|
              ≤ ∑ b ∈ H.neighborFinset a, |edgeRemovedDensity H G a b x y
                  - edgeRemovedDensity H G' a b x y| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _b ∈ H.neighborFinset a, (H.edgeFinset.card : ℝ) * c :=
                Finset.sum_le_sum fun b _ => hstep a b
            _ = ((H.neighborFinset a).card : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
                rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * (H.edgeFinset.card : ℝ) * ((H.edgeFinset.card : ℝ) * c) := by
          rw [← Finset.sum_mul, sum_card_neighborFinset]
  have h2 : |(1:ℝ) / 2| = 1 / 2 := by norm_num
  rw [h2]
  nlinarith [habs, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (Nat.cast_nonneg (α := ℝ) H.edgeFinset.card)) (mul_nonneg
      (Nat.cast_nonneg (α := ℝ) H.edgeFinset.card) hc0)]

end Lipschitz

/-! ### The second-order expansion of `t(H, W + ζZ)` -/

omit [Fintype V] [DecidableEq V] in
/-- The edge factor of `W + ζZ`. -/
theorem edgeVal_ofGraphon_add_smul (G : Graphon) (Z : Kernel) (ζ : ℝ) (x : V → ℝ) (e : Sym2 V) :
    edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e
      = edgeVal G.toFun G.symm' x e + ζ * edgeVal Z.toFun Z.symm' x e := by
  induction e using Sym2.ind with
  | _ a b => rfl

/-- **`t(H, W + ζZ) = t(H,W) + ζ ∫∫ 𝒟_W Z + O(ζ²)`, with a constant depending only on `H`.** -/
theorem abs_tDensity_line_sub_le (H : SimpleGraph V) [DecidableRel H.Adj] (G : Graphon)
    (Z : Kernel) {ζ ρ : ℝ} (hρ : 0 ≤ ρ) (hZρ : ∀ x y, |ζ * Z.toFun x y| ≤ ρ)
    (hmem : ∀ x y, G.toFun x y + ζ * Z.toFun x y ∈ Set.Icc (0:ℝ) 1) :
    |(Kernel.ofGraphon G + ζ • Z).tDensity H - G.tDensity H
        - ζ * ∫ z, derivKernel H G z.1 z.2 * Z.toFun z.1 z.2 ∂gμ|
      ≤ (H.edgeFinset.card : ℝ) ^ 2 * ρ ^ 2 := by
  have hKmem : ∀ x y, (Kernel.ofGraphon G + ζ • Z).toFun x y ∈ Set.Icc (0:ℝ) 1 := hmem
  have hf : IsBddMeas fun x : V → ℝ => ∏ e ∈ H.edgeFinset,
      edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e :=
    IsBddMeas.finset_prod _ fun e _ => isBddMeas_edgeVal _ e
  have hg : IsBddMeas fun x : V → ℝ => ∏ e ∈ H.edgeFinset, edgeVal G.toFun G.symm' x e :=
    isBddMeas_prod_edgeVal G _
  have hh : IsBddMeas fun x : V → ℝ => ∑ e ∈ H.edgeFinset,
      ζ * edgeVal Z.toFun Z.symm' x e
        * ∏ e' ∈ H.edgeFinset.erase e, edgeVal G.toFun G.symm' x e' :=
    IsBddMeas.finset_sum _ fun e _ =>
      ((isBddMeas_edgeVal Z e).const_mul ζ).mul (isBddMeas_prod_edgeVal G _)
  have hpt : ∀ x : V → ℝ,
      |(∏ e ∈ H.edgeFinset,
          edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e)
        - (∏ e ∈ H.edgeFinset, edgeVal G.toFun G.symm' x e)
        - ∑ e ∈ H.edgeFinset, ζ * edgeVal Z.toFun Z.symm' x e
            * ∏ e' ∈ H.edgeFinset.erase e, edgeVal G.toFun G.symm' x e'|
      ≤ (H.edgeFinset.card : ℝ) ^ 2 * ρ ^ 2 := by
    intro x
    have hkey := abs_prod_add_sub_le (fun e : Sym2 V => edgeVal G.toFun G.symm' x e)
      (fun e : Sym2 V => ζ * edgeVal Z.toFun Z.symm' x e) hρ
      (fun e => edgeVal_mem_Icc G x e)
      (fun e => by
        induction e using Sym2.ind with
        | _ a b => exact hmem (x a) (x b))
      (fun e => by
        induction e using Sym2.ind with
        | _ a b => exact hZρ (x a) (x b))
      H.edgeFinset
    have heq : ∀ e ∈ H.edgeFinset,
        edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e
          = edgeVal G.toFun G.symm' x e + ζ * edgeVal Z.toFun Z.symm' x e :=
      fun e _ => edgeVal_ofGraphon_add_smul G Z ζ x e
    rw [Finset.prod_congr rfl heq]
    exact hkey
  have hint : ∫ x, (∑ e ∈ H.edgeFinset, ζ * edgeVal Z.toFun Z.symm' x e
        * ∏ e' ∈ H.edgeFinset.erase e, edgeVal G.toFun G.symm' x e')
        ∂(Measure.pi fun _ : V => unitμ)
      = ζ * ∫ z, derivKernel H G z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := by
    rw [integral_derivKernel_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun e _ =>
      (((isBddMeas_edgeVal Z e).const_mul ζ).mul (isBddMeas_prod_edgeVal G _)).integrable]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hfg : Integrable (fun x : V → ℝ => (∏ e ∈ H.edgeFinset,
        edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e)
      - ∏ e ∈ H.edgeFinset, edgeVal G.toFun G.symm' x e)
      (Measure.pi fun _ : V => unitμ) := hf.integrable.sub hg.integrable
  have hT : ∫ x, ((∏ e ∈ H.edgeFinset,
            edgeVal (Kernel.ofGraphon G + ζ • Z).toFun (Kernel.ofGraphon G + ζ • Z).symm' x e)
          - (∏ e ∈ H.edgeFinset, edgeVal G.toFun G.symm' x e)
          - ∑ e ∈ H.edgeFinset, ζ * edgeVal Z.toFun Z.symm' x e
              * ∏ e' ∈ H.edgeFinset.erase e, edgeVal G.toFun G.symm' x e')
          ∂(Measure.pi fun _ : V => unitμ)
      = (Kernel.ofGraphon G + ζ • Z).tDensity H - G.tDensity H
        - ζ * ∫ z, derivKernel H G z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := by
    rw [integral_sub hfg hh.integrable, integral_sub hf.integrable hg.integrable, hint]
    rfl
  rw [← hT]
  refine abs_integral_le_integral_abs.trans ?_
  have h := integral_mono (hfg.sub hh.integrable).abs
    (integrable_const (μ := Measure.pi fun _ : V => unitμ)
      ((H.edgeFinset.card : ℝ) ^ 2 * ρ ^ 2)) hpt
  simpa using h

/-! ### The insertion weights -/

/-- `∑_{S ⊆ V(H)} s^{|S|}(1-s)^{N-|S|} = 1`. -/
theorem sum_powerset_weight (s : ℝ) :
    ∑ S ∈ (Finset.univ : Finset V).powerset, s ^ S.card * (1 - s) ^ Sᶜ.card = 1 := by
  calc ∑ S ∈ (Finset.univ : Finset V).powerset, s ^ S.card * (1 - s) ^ Sᶜ.card
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          (∏ _i ∈ S, s) * ∏ _i ∈ (Finset.univ : Finset V) \ S, (1 - s) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.prod_const, Finset.prod_const, Finset.compl_eq_univ_sdiff]
    _ = ∏ _i ∈ (Finset.univ : Finset V), (s + (1 - s)) :=
        (Finset.prod_add (fun _ : V => s) (fun _ : V => 1 - s) (Finset.univ : Finset V)).symm
    _ = 1 := by rw [show s + (1 - s) = (1:ℝ) by ring, Finset.prod_const, one_pow]

/-! ### The inserted graphon with an explicit correction -/

/-- **The inserted graphon.**  If `W + ζZ` takes values in `[0,1]`, the insertion of a block of
measure `s` with value `q` and row `u` into `W + ζZ` is a graphon, and its three functionals are
given in closed form: `t(H,·)` by the exact expansion over the subsets of `V(H)` occupied by the
new block, of which `eq:insertion-density-expansion` keeps the terms of order `s^0` and `s^1`. -/
theorem exists_insertGraphon (H : SimpleGraph V) [DecidableRel H.Adj] (G : Graphon) (Z : Kernel)
    {ζ : ℝ} (hmem : ∀ x y, G.toFun x y + ζ * Z.toFun x y ∈ Set.Icc (0:ℝ) 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ W' : Graphon,
      W'.tDensity H = ∑ S ∈ (Finset.univ : Finset V).powerset,
          s ^ S.card * (1 - s) ^ Sᶜ.card * blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) ∧
      W'.edgeDensity = s ^ 2 * q + 2 * s * (1 - s) * ∫ y, u y ∂unitμ
        + (1 - s) ^ 2 * (G.edgeDensity + ζ * ∫ z, Z.toFun z.1 z.2 ∂gμ) ∧
      ∀ p, 0 < p → p < 1 →
        W'.Ip p = s ^ 2 * Jp p q + 2 * s * (1 - s) * ∫ y, Jp p (u y) ∂unitμ
          + (1 - s) ^ 2 * (Kernel.ofGraphon G + ζ • Z).Ip p := by
  have hKmem : ∀ x y, (Kernel.ofGraphon G + ζ • Z).toFun x y ∈ Set.Icc (0:ℝ) 1 := hmem
  have hcl : (Kernel.ofGraphon (clampKernel (Kernel.ofGraphon G + ζ • Z))).toFun
      = (Kernel.ofGraphon G + ζ • Z).toFun :=
    funext fun x => funext fun y => clampKernel_apply_of_mem hKmem x y
  refine ⟨insertGraphon s q hq u hu (clampKernel (Kernel.ofGraphon G + ζ • Z)), ?_, ?_,
    fun p hp0 hp1 => ?_⟩
  · rw [tDensity_insertGraphon H hs0 hs1 hq hu]
    exact Finset.sum_congr rfl fun S _ => by rw [blockDensity_congr H S q u hcl]
  · rw [edgeDensity_insertGraphon hs0 hs1 hq hu]
    have he : (clampKernel (Kernel.ofGraphon G + ζ • Z)).edgeDensity
        = ∫ z, (G.toFun z.1 z.2 + ζ * Z.toFun z.1 z.2) ∂gμ :=
      integral_congr_ae (ae_of_all _ fun z => clampKernel_apply_of_mem hKmem z.1 z.2)
    rw [he, integral_add G.integrable_self ((kernel_integrable Z).const_mul _),
      integral_const_mul]
    rfl
  · rw [Ip_insertGraphon hs0 hs1 hq hu _ hp0 hp1]
    have hI : (clampKernel (Kernel.ofGraphon G + ζ • Z)).Ip p
        = (Kernel.ofGraphon G + ζ • Z).Ip p :=
      integral_congr_ae (ae_of_all _ fun z => by
        simp only [clampKernel_apply_of_mem hKmem z.1 z.2])
    rw [hI]

/-! ### `J_p` is Lipschitz away from the endpoints -/

/-- **`J_p` is Lipschitz on a compact subinterval of `(0,1)`.** -/
theorem exists_lipschitz_Jp {p c d : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 < c) (hd : d < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, |Jp p x - Jp p y| ≤ L * |x - y| := by
  have hmem : ∀ w ∈ Set.Icc c d, 0 < w ∧ w < 1 := fun w hw =>
    ⟨lt_of_lt_of_le hc hw.1, lt_of_le_of_lt hw.2 hd⟩
  have hcont : ContinuousOn (Jp' p) (Set.Icc c d) := fun w hw =>
    (hasDerivAt_Jp' hp0 hp1 (hmem w hw).1 (hmem w hw).2).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have hderiv : ∀ w ∈ Set.Icc c d, HasDerivWithinAt (Jp p) (Jp' p w) (Set.Icc c d) w :=
    fun w hw => (hasDerivAt_Jp hp0 hp1 (hmem w hw).1 (hmem w hw).2).hasDerivWithinAt
  have hbound : ∀ w ∈ Set.Icc c d, ‖Jp' p w‖ ≤ max M 0 := fun w hw =>
    (hM w hw).trans (le_max_left _ _)
  have h := (convex_Icc c d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy hx
  simpa [Real.norm_eq_abs] using h


/-! ### The first-order expansion of the insertion polynomial -/

/-- The insertion polynomial, unfolded. -/
theorem insertionPoly_eq (H : SimpleGraph V) [DecidableRel H.Adj] (q : ℝ) (u : ℝ → ℝ)
    (G : Graphon) (Z : Kernel) (g : ℝ → ℝ) (s : ℝ) :
    insertionPoly H q u G Z g s = ∑ S ∈ (Finset.univ : Finset V).powerset,
      s ^ S.card * (1 - s) ^ Sᶜ.card * blockDensity H S q u (Kernel.ofGraphon G + g s • Z) := rfl

/-- `|(1-s)^k - 1| ≤ k s` for `s ∈ [0,1]` (Bernoulli). -/
theorem abs_one_sub_pow_sub_one_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    |(1 - s) ^ k - 1| ≤ (k : ℝ) * s := by
  have hle1 : (1 - s) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hber : 1 + (k : ℝ) * (-s) ≤ (1 + (-s)) ^ k := one_add_mul_le_pow (by linarith) _
  have hpow : (1 + (-s)) ^ k = (1 - s) ^ k := by rw [sub_eq_add_neg]
  rw [hpow] at hber
  have hk0 : (0:ℝ) ≤ (k : ℝ) * s := by positivity
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The arithmetic of the remainder bound in `insertionPoly_taylor`. -/
theorem taylor_remainder_arith {m N cz s ρ B : ℝ} (hm0 : 0 ≤ m) (hN0 : 0 ≤ N)
    (hs0 : 0 ≤ s) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * s * cz) :
    m ^ 2 * ρ ^ 2 + 2 * s ^ 2 * (m * cz)
        + s * (N * s * (2 * N) + N * (m * ρ) + N * (m * ρ)) + B * s ^ 2
      ≤ (4 * m ^ 2 * cz ^ 2 + 2 * m * cz + 2 * N ^ 2 + 4 * N * m * cz + B) * s ^ 2 := by
  have h1 : m ^ 2 * ρ ^ 2 ≤ m ^ 2 * (4 * s ^ 2 * cz ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg m)
  have h2 : (2 * N * m) * (ρ * s) ≤ (2 * N * m) * (2 * s ^ 2 * cz) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith [h1, h2]

/-- **The insertion expansion, uniformly in the base graphon.**  With the reparametrization
`g(s) = s/(1-s)` that keeps the edge density exact, the `H`-density of the insertion of a block of
measure `s` with value `q` and row `u` into `W + g(s)Z` is
`t(H,W) + s(∫∫𝒟_W Z + ℛ_W(u) - N t(H,W)) + O(s²)`, with a constant depending only on `H` and on
a bound for `Z`.  This is the uniform version of `hasDerivAt_insertionPoly` needed in
`lem:degenerate-insertion`, where the base graphon moves along the smoothing path. -/
theorem insertionPoly_taylor (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) {u : ℝ → ℝ} (hu : IsRow u) (Z : Kernel) {cz : ℝ} (hcz0 : 0 ≤ cz)
    (hcz : ∀ x y, |Z.toFun x y| ≤ cz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Graphon) (s : ℝ), 0 ≤ s → s ≤ 1 / 2 →
      (∀ x y, G.toFun x y + s / (1 - s) * Z.toFun x y ∈ Set.Icc (0:ℝ) 1) →
      |insertionPoly H q u G Z (fun t => t / (1 - t)) s - G.tDensity H
          - s * ((∫ z, derivKernel H G z.1 z.2 * Z.toFun z.1 z.2 ∂gμ)
              + totalRootedDensity H G u - (Fintype.card V : ℝ) * G.tDensity H)|
        ≤ C * s ^ 2 := by
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (H.edgeFinset.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (Fintype.card V : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := hmdef ▸ Nat.cast_nonneg _
  have hN0 : 0 ≤ N := hNdef ▸ Nat.cast_nonneg _
  refine ⟨4 * m ^ 2 * cz ^ 2 + 2 * m * cz + 2 * N ^ 2 + 4 * N * m * cz
    + 2 ^ (Fintype.card V), by positivity, ?_⟩
  intro G s hs0 hs2 hmem
  have hs1 : (0:ℝ) < 1 - s := by linarith
  have hsle1 : s ≤ 1 := by linarith
  -- the correction and its size
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = s / (1 - s) := ⟨_, rfl⟩
  have hζ0 : 0 ≤ ζ := by rw [hζdef]; positivity
  have hζ2 : ζ ≤ 2 * s := by rw [hζdef, div_le_iff₀ hs1]; nlinarith
  have hζs0 : 0 ≤ ζ - s := by rw [hζdef, le_sub_iff_add_le, zero_add, le_div_iff₀ hs1]; nlinarith
  have hζs : ζ - s ≤ 2 * s ^ 2 := by
    rw [hζdef, sub_le_iff_le_add, div_le_iff₀ hs1]
    nlinarith [mul_nonneg (sq_nonneg s) (by linarith : (0:ℝ) ≤ 1 - 2 * s)]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ζ * cz := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρ2 : ρ ≤ 2 * s * cz := by rw [hρdef]; nlinarith
  have hKmem : ∀ x y, (Kernel.ofGraphon G + ζ • Z).toFun x y ∈ Set.Icc (0:ℝ) 1 := by
    intro x y; rw [hζdef]; exact hmem x y
  have hZρ : ∀ x y, |ζ * Z.toFun x y| ≤ ρ := by
    intro x y
    rw [abs_mul, abs_of_nonneg hζ0, hρdef]
    exact mul_le_mul_of_nonneg_left (hcz x y) hζ0
  have hKG : ∀ x y, |(Kernel.ofGraphon G + ζ • Z).toFun x y - G.toFun x y| ≤ ρ := by
    intro x y
    have hE : (Kernel.ofGraphon G + ζ • Z).toFun x y - G.toFun x y = ζ * Z.toFun x y := by
      simp [Kernel.add_apply, Kernel.smul_apply]
    rw [hE]; exact hZρ x y
  -- the clamped graphon carrying the same values
  obtain ⟨Gr, hGrdef⟩ : ∃ Gr : Graphon, Gr = clampGraphon (Kernel.ofGraphon G + ζ • Z) := ⟨_, rfl⟩
  have hGr : ∀ x y, Gr.toFun x y = (Kernel.ofGraphon G + ζ • Z).toFun x y := by
    intro x y
    rw [hGrdef, clampGraphon_apply, min_eq_right (hKmem x y).2, max_eq_right (hKmem x y).1]
  -- the quantities entering the expansion
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ∫ z, derivKernel H G z.1 z.2 * Z.toFun z.1 z.2 ∂gμ := ⟨_, rfl⟩
  obtain ⟨tG, htGdef⟩ : ∃ t : ℝ, t = G.tDensity H := ⟨_, rfl⟩
  obtain ⟨Rw, hRwdef⟩ : ∃ r : ℝ, r = totalRootedDensity H G u := ⟨_, rfl⟩
  obtain ⟨T0, hT0def⟩ : ∃ t : ℝ, t = blockDensity H ∅ q u (Kernel.ofGraphon G + ζ • Z) := ⟨_, rfl⟩
  obtain ⟨Sv, hSvdef⟩ :
      ∃ t : ℝ, t = ∑ v : V, blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) := ⟨_, rfl⟩
  obtain ⟨P1, hP1def⟩ : ∃ t : ℝ, t = (1 - s) ^ (Fintype.card V - 1) := ⟨_, rfl⟩
  obtain ⟨Ins, hInsdef⟩ :
      ∃ t : ℝ, t = insertionPoly H q u G Z (fun t => t / (1 - t)) s := ⟨_, rfl⟩
  obtain ⟨Rem, hRemdef⟩ : ∃ r : ℝ, r = ∑ S ∈ (Finset.univ : Finset V).powerset,
      (if S.card = 1 then 0
        else s ^ S.card * (1 - s) ^ Sᶜ.card
          * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0)) := ⟨_, rfl⟩
  -- `T_S ∈ [0,1]`
  have hTmem : ∀ S : Finset V,
      blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) ∈ Set.Icc (0:ℝ) 1 := fun S =>
    blockDensity_mem_Icc H S hq hu hKmem
  have hT0mem : T0 ∈ Set.Icc (0:ℝ) 1 := hT0def ▸ hTmem ∅
  -- `|D| ≤ m cz`
  have hD : |D| ≤ m * cz := by
    rw [hDdef]
    refine abs_integral_le_integral_abs.trans ?_
    have hbd : ∀ z : ℝ × ℝ, |derivKernel H G z.1 z.2 * Z.toFun z.1 z.2| ≤ m * cz := by
      intro z
      rw [abs_mul, hmdef]
      exact mul_le_mul (abs_derivKernel_le H G _ _) (hcz _ _) (abs_nonneg _) (Nat.cast_nonneg _)
    have h := integral_mono (integrable_derivKernel_mul H G Z).abs
      (integrable_const (μ := gμ) (m * cz)) hbd
    simpa using h
  -- the second-order bound for the correction, and its first-order Lipschitz form
  have hA1 : |T0 - tG - ζ * D| ≤ m ^ 2 * ρ ^ 2 := by
    rw [hT0def, blockDensity_empty, htGdef, hDdef, hmdef]
    exact abs_tDensity_line_sub_le H G Z hρ0 hZρ (fun x y => by
      have := hKmem x y; simpa [Kernel.add_apply, Kernel.smul_apply] using this)
  have hA2 : |T0 - tG| ≤ m * ρ := by
    rw [hT0def, blockDensity_empty, htGdef, hmdef]
    have h := abs_kernel_tDensity_sub_le H hKmem (K := Kernel.ofGraphon G + ζ • Z)
      (L := Kernel.ofGraphon G) (fun x y => G.mem_Icc x y) hKG
    rwa [Kernel.tDensity_ofGraphon] at h
  -- the rooted densities
  have hSvR : |Sv - Rw| ≤ N * (m * ρ) := by
    have hsing : ∀ v : V, blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z)
        = rootedDensity H Gr v u := by
      intro v
      rw [blockDensity_congr H {v} q u (K := Kernel.ofGraphon G + ζ • Z)
        (K' := Kernel.ofGraphon Gr) (funext fun x => funext fun y => (hGr x y).symm),
        blockDensity_singleton]
    have h := abs_totalRootedDensity_sub_le_graphon H (G := Gr) (G' := G) hu
      (c := ρ) (fun x y => by rw [hGr x y]; exact hKG x y)
    rw [hSvdef, hRwdef, hNdef, hmdef, Finset.sum_congr rfl fun v _ => hsing v]
    exact h
  -- the weights
  have hwnn : ∀ S : Finset V, 0 ≤ s ^ S.card * (1 - s) ^ Sᶜ.card := fun S => by positivity
  have hIns : insertionPoly H q u G Z (fun t => t / (1 - t)) s
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          s ^ S.card * (1 - s) ^ Sᶜ.card
            * blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) := by
    rw [hζdef]; rfl
  have hIT0 : Ins - T0
      = ∑ S ∈ (Finset.univ : Finset V).powerset,
          s ^ S.card * (1 - s) ^ Sᶜ.card
            * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0) := by
    have hexp : ∑ S ∈ (Finset.univ : Finset V).powerset,
        s ^ S.card * (1 - s) ^ Sᶜ.card
          * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0)
        = (∑ S ∈ (Finset.univ : Finset V).powerset,
            s ^ S.card * (1 - s) ^ Sᶜ.card
              * blockDensity H S q u (Kernel.ofGraphon G + ζ • Z))
          - (∑ S ∈ (Finset.univ : Finset V).powerset, s ^ S.card * (1 - s) ^ Sᶜ.card) * T0 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    rw [hexp, sum_powerset_weight, one_mul, hInsdef, hIns]
  have hsplit : Ins - T0
      = (∑ v : V, s ^ ({v} : Finset V).card * (1 - s) ^ ({v} : Finset V)ᶜ.card
            * (blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) - T0)) + Rem := by
    have hdec : ∀ S : Finset V, s ^ S.card * (1 - s) ^ Sᶜ.card
          * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0)
        = (if S.card = 1 then s ^ S.card * (1 - s) ^ Sᶜ.card
              * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0) else 0)
          + (if S.card = 1 then 0
              else s ^ S.card * (1 - s) ^ Sᶜ.card
                * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0)) := by
      intro S; split_ifs <;> ring
    rw [hIT0, hRemdef, Finset.sum_congr rfl fun S _ => hdec S, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, Finset.powersetCard_one,
      Finset.sum_map]
    rfl
  have hsumv : (∑ v : V, s ^ ({v} : Finset V).card * (1 - s) ^ ({v} : Finset V)ᶜ.card
        * (blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) - T0))
      = s * P1 * (Sv - N * T0) := by
    have hcard : ∀ v : V, s ^ ({v} : Finset V).card * (1 - s) ^ ({v} : Finset V)ᶜ.card
        = s * P1 := fun v => by
      rw [Finset.card_singleton, Finset.card_compl, Finset.card_singleton, pow_one, hP1def]
    calc (∑ v : V, s ^ ({v} : Finset V).card * (1 - s) ^ ({v} : Finset V)ᶜ.card
          * (blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) - T0))
        = ∑ v : V, (s * P1)
            * (blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) - T0) :=
          Finset.sum_congr rfl fun v _ => by rw [hcard v]
      _ = (s * P1) * ∑ v : V, (blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) - T0) := by
          rw [← Finset.mul_sum]
      _ = s * P1 * (Sv - N * T0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hSvdef,
            hNdef]
  -- the remainder of order `s²`
  have hRem : |Rem| ≤ 2 ^ (Fintype.card V) * s ^ 2 := by
    have hterm : ∀ S ∈ (Finset.univ : Finset V).powerset,
        |(if S.card = 1 then 0
            else s ^ S.card * (1 - s) ^ Sᶜ.card
              * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0))| ≤ s ^ 2 := by
      intro S _
      by_cases h1 : S.card = 1
      · rw [if_pos h1, abs_zero]; positivity
      rw [if_neg h1]
      by_cases h0 : S.card = 0
      · have hS : S = ∅ := Finset.card_eq_zero.mp h0
        subst hS
        rw [← hT0def, sub_self, mul_zero, abs_zero]; positivity
      have h2 : 2 ≤ S.card := by omega
      have hb1 : |blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0| ≤ 1 := by
        have ha := hTmem S
        rw [abs_le]
        exact ⟨by linarith [ha.1, hT0mem.2], by linarith [ha.2, hT0mem.1]⟩
      have hw1 : s ^ S.card * (1 - s) ^ Sᶜ.card ≤ s ^ 2 :=
        calc s ^ S.card * (1 - s) ^ Sᶜ.card ≤ s ^ S.card * 1 :=
              mul_le_mul_of_nonneg_left
                (pow_le_one₀ (by linarith) (by linarith)) (pow_nonneg hs0 _)
          _ = s ^ S.card := mul_one _
          _ ≤ s ^ 2 := pow_le_pow_of_le_one hs0 hsle1 h2
      calc |s ^ S.card * (1 - s) ^ Sᶜ.card
              * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0)|
          = (s ^ S.card * (1 - s) ^ Sᶜ.card)
              * |blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0| := by
            rw [abs_mul, abs_of_nonneg (hwnn S)]
        _ ≤ s ^ 2 * 1 := mul_le_mul hw1 hb1 (abs_nonneg _) (by positivity)
        _ = s ^ 2 := mul_one _
    have hcardP : ((Finset.univ : Finset V).powerset.card : ℝ) = 2 ^ (Fintype.card V) := by
      rw [Finset.card_powerset, Finset.card_univ]
      push_cast
      ring
    rw [hRemdef]
    calc |∑ S ∈ (Finset.univ : Finset V).powerset,
            (if S.card = 1 then 0
              else s ^ S.card * (1 - s) ^ Sᶜ.card
                * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0))|
        ≤ ∑ S ∈ (Finset.univ : Finset V).powerset,
            |(if S.card = 1 then 0
              else s ^ S.card * (1 - s) ^ Sᶜ.card
                * (blockDensity H S q u (Kernel.ofGraphon G + ζ • Z) - T0))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S ∈ (Finset.univ : Finset V).powerset, s ^ 2 := Finset.sum_le_sum hterm
      _ = ((Finset.univ : Finset V).powerset.card : ℝ) * s ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 ^ (Fintype.card V) * s ^ 2 := by rw [hcardP]
  -- the Bernoulli estimate for the weight `(1-s)^{N-1}`
  have hP1 : |P1 - 1| ≤ N * s := by
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ N := by
      rw [hNdef]; exact_mod_cast Nat.sub_le _ _
    refine (hP1def ▸ abs_one_sub_pow_sub_one_le hs0 hsle1 (Fintype.card V - 1)).trans ?_
    exact mul_le_mul_of_nonneg_right hcast hs0
  -- assemble
  have habs : |Sv - N * T0| ≤ 2 * N := by
    have hSvle : |Sv| ≤ N := by
      rw [hSvdef, hNdef]
      have h0 : (0:ℝ) ≤ ∑ v : V, blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z) :=
        Finset.sum_nonneg fun v _ => (hTmem {v}).1
      rw [abs_of_nonneg h0]
      calc ∑ v : V, blockDensity H {v} q u (Kernel.ofGraphon G + ζ • Z)
          ≤ ∑ _v : V, (1:ℝ) := Finset.sum_le_sum fun v _ => (hTmem {v}).2
        _ = (Fintype.card V : ℝ) := by simp
    have hT0le : |N * T0| ≤ N := by
      rw [abs_mul, abs_of_nonneg hN0, abs_of_nonneg hT0mem.1]
      calc N * T0 ≤ N * 1 := mul_le_mul_of_nonneg_left hT0mem.2 hN0
        _ = N := mul_one N
    calc |Sv - N * T0| ≤ |Sv| + |N * T0| := abs_sub _ _
      _ ≤ 2 * N := by linarith
  have hInseq : Ins = T0 + (s * P1 * (Sv - N * T0) + Rem) := by
    rw [hsumv] at hsplit
    linear_combination hsplit
  have hE2 : |(ζ - s) * D| ≤ 2 * s ^ 2 * (m * cz) := by
    rw [abs_mul, abs_of_nonneg hζs0]
    exact mul_le_mul hζs hD (abs_nonneg _) (by positivity)
  have hE3 : |s * ((P1 - 1) * (Sv - N * T0) + (Sv - Rw) - N * (T0 - tG))|
      ≤ s * (N * s * (2 * N) + N * (m * ρ) + N * (m * ρ)) := by
    rw [abs_mul, abs_of_nonneg hs0]
    refine mul_le_mul_of_nonneg_left ?_ hs0
    calc |(P1 - 1) * (Sv - N * T0) + (Sv - Rw) - N * (T0 - tG)|
        ≤ |(P1 - 1) * (Sv - N * T0)| + |Sv - Rw| + |N * (T0 - tG)| := by
          refine (abs_sub ((P1 - 1) * (Sv - N * T0) + (Sv - Rw)) (N * (T0 - tG))).trans ?_
          linarith [abs_add_le ((P1 - 1) * (Sv - N * T0)) (Sv - Rw)]
      _ ≤ N * s * (2 * N) + N * (m * ρ) + N * (m * ρ) := by
          refine add_le_add (add_le_add ?_ hSvR) ?_
          · rw [abs_mul]
            exact mul_le_mul hP1 habs (abs_nonneg _) (mul_nonneg hN0 hs0)
          · rw [abs_mul, abs_of_nonneg hN0]
            exact mul_le_mul_of_nonneg_left hA2 hN0
  have hsum : |(T0 - tG - ζ * D) + (ζ - s) * D
        + s * ((P1 - 1) * (Sv - N * T0) + (Sv - Rw) - N * (T0 - tG)) + Rem|
      ≤ m ^ 2 * ρ ^ 2 + 2 * s ^ 2 * (m * cz)
        + s * (N * s * (2 * N) + N * (m * ρ) + N * (m * ρ))
        + 2 ^ (Fintype.card V) * s ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ hRem)
    refine (abs_add_le _ _).trans (add_le_add ?_ hE3)
    exact (abs_add_le _ _).trans (add_le_add hA1 hE2)
  have hfinal : |Ins - tG - s * (D + Rw - N * tG)|
      ≤ m ^ 2 * ρ ^ 2 + 2 * s ^ 2 * (m * cz)
        + s * (N * s * (2 * N) + N * (m * ρ) + N * (m * ρ))
        + 2 ^ (Fintype.card V) * s ^ 2 := by
    have hid : Ins - tG - s * (D + Rw - N * tG)
        = (T0 - tG - ζ * D) + (ζ - s) * D
          + s * ((P1 - 1) * (Sv - N * T0) + (Sv - Rw) - N * (T0 - tG)) + Rem := by
      rw [hInseq]; ring
    rw [hid]; exact hsum
  rw [← hDdef, ← htGdef, ← hRwdef, ← hNdef, ← hInsdef]
  exact hfinal.trans (taylor_remainder_arith hm0 hN0 hs0 hρ0 hρ2)

end FixedDensities

end UpperTailMultipodality
