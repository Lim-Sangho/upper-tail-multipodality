# Formalization guide

This guide connects the definitions, proofs and numbered results of the
[paper](paper/paper.tex) to their Lean declarations. It covers the graphon
theory of Sections 1–8. [Appendix A][app:arw], which compares this paper's
assumptions with those of a preprint of Alvarado, Ramon and Wang, is outside the
formalization.

## Definitions and notation

The paper studies two problems: the joint upper-tail problem
`Φ_H(p,r) = min { I_p(W) : t(H_j,W) ≥ r_j^{m_j} for 1 ≤ j ≤ s }` for graphs `H_j`
with `m_j = |E(H_j)| ≥ 1` edges and `p, r_j ∈ (0,1)`, and the maximization of the
entropy at fixed edge density `ε` and `H`-density `τ`. For one graph, `N = |V(H)|`
and `m = |E(H)|`.

| Paper notation or concept | Lean representation |
|---|---|
| A graphon on `[0,1]²` | `Graphon` is a symmetric measurable kernel on `ℝ²` with values in `[0,1]`; integration uses `unitμ` on `[0,1]` and `gμ` on its square. `UnitGraphon` uses the paper's domain directly, and the conversions in [UnitGraphon.lean](UpperTailMultipodality/Preliminaries/Graphons/UnitGraphon.lean) preserve all densities. |
| `e(W)`, `t(H,W)`, `J_p`, `I_p`, `s(W)` | `Graphon.edgeDensity`, `Graphon.tDensity`, `Jp`, `Graphon.Ip`, `Graphon.entropy`. Only `s(W)` carries the factor `1/2`. |
| `Φ_H(p,r)`, feasibility | For one constraint, `phiVar` and `Feasible`; a minimizer is a feasible `W` with `W.Ip p = phiVar H p r`. For a family, [jointVar](UpperTailMultipodality/UpperTail/Joint/Basic.lean#L372) and [JointFeasible](UpperTailMultipodality/UpperTail/Joint/Basic.lean#L30). |
| The row `W_x = W(x,·)` | [`Graphon.row`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L21); a *row* in the sense of `ℱ_W` is any measurable `u : ℝ → ℝ` with values in `[0,1]`, the predicate [`IsRow`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L23). |
| Multipodal, ordered blocks ([Eq. (5)][eq:ordered-blocks]) | [`BlockStructure`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L27) collects finitely many measurable, pairwise disjoint blocks covering `[0,1]` up to a null set, with symmetric values in `[0,1]`; [`IsMultipodal`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L48) and [`IsOrderedMultipodal`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L52). Blocks of measure zero are allowed, as in the paper. |
| An ordered structure ([Definition 2.2][def:ordered-structure]) | [`HasOrderedRows`](UpperTailMultipodality/FixedDensities/Support/Ordered.lean#L72): `W` agrees almost everywhere with a [`MonotoneKernel`](UpperTailMultipodality/FixedDensities/Support/Ordered.lean#L29), that is, `def:ordered-structure` with the relabeling `φ` already applied. The relabeling itself is never carried; see *Differences in proof methods*. |
| `I_p(u) = ∫J_p(u)` for a row `u` | Written out as `∫ y, Jp p (u y) ∂unitμ`; it carries no separate name, while `Graphon.Ip` is the two-variable `I_p(W)`. The Fubini identity `I_p(W) = ∫I_p(W_x)dx` is [integral_gμ_Jp_rows](UpperTailMultipodality/Insertion/FirstOrderRows.lean#L181). |
| Bounded symmetric kernels | [`Kernel`](UpperTailMultipodality/Preliminaries/Kernel.lean#L23), with `Kernel.tDensity`, `Kernel.edgeDensity`, `Kernel.Ip` and `Kernel.lincomb K U s = K + ∑ᵢ sᵢUᵢ`. Perturbation directions are kernels; graphons are kernels with values in `[0,1]`. |
| `𝒟_W` ([Eq. (14)][eq:derivative-kernel]) | [`derivKernel`](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L36), defined as `½ ∑_{(a,b) adjacent} K_{ab,W}` with [`edgeRemovedDensity`](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L30); the two orientations of an edge give the paper's `K_{ab,W}(x,y) + K_{ab,W}(y,x)`. |
| `W_θ`, the inserted graphon ([Eq. (17)][eq:vertex-insertion]) | [`blockKernel`](UpperTailMultipodality/Insertion/Construction.lean#L25), together with the explicit measure-preserving rescaling of `[θ,1]` onto `[0,1]`; `exists_insertGraphon` packages it as a graphon with the exact density formulas. |
| `ℛ_{v,W}(u)`, `ℛ_W(u)` ([Eq. (18)][eq:rooted-density], [Eq. (19)][eq:total-rooted-density]) | [`rootedDensity`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L46), [`totalRootedDensity`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L52). The integrals are over all coordinates; the root variable does not occur in the integrand. |
| `G_{v,z₀}(u)`, `∇ℛ_W(u)` ([Eq. (23)][eq:rooted-gradient-kernel]) | [`rootedGradientTerm`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L57) and [`rootedGradient`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L64), the sum over the oriented edges `(v, z₀)`. |
| `ℱ_W` ([Eq. (30)][eq:row-functional]), `𝓜_W` | [`rowFunctional`](UpperTailMultipodality/RowCriterion/Defs.lean#L29) and [`rowMinimizers`](UpperTailMultipodality/RowCriterion/Defs.lean#L34); for a family of graphs, `combinedRowFunctional` and `combinedRowMinimizers`. These are sets of genuine functions; as the subset of `L^∞([0,1])` that the paper defines, [`rowMinimizersLinfty`](UpperTailMultipodality/RowCriterion/Linfty.lean#L150), whose defining conditions `0 ≤ u ≤ 1` almost everywhere and `ℱ_W(u) = c` are [mem_rowMinimizersLinfty_iff](UpperTailMultipodality/RowCriterion/Linfty.lean#L157). |
| `τ_max(ε)`, `Ψ_ε(τ)` ([Eq. (35)][eq:fixed-problem]), maximizers | [`tauMax`](UpperTailMultipodality/FixedDensities/Defs.lean#L21), [`fixedValue`](UpperTailMultipodality/FixedDensities/Defs.lean#L31), [`IsEntropyMaximizer`](UpperTailMultipodality/FixedDensities/Defs.lean#L26) and [`IsFixedMinimizer`](UpperTailMultipodality/FixedDensities/Defs.lean#L35); they agree by [isEntropyMaximizer_iff](UpperTailMultipodality/FixedDensities/Defs.lean#L40). |
| The constraint qualification ([Definition 6.1][def:constraint-qualification]) | [`ConstraintQualification`](UpperTailMultipodality/FixedDensities/Defs.lean#L71), with the determinant [`cqDet`](UpperTailMultipodality/FixedDensities/Defs.lean#L59) of the matrix `Γ_W(U₁,U₂)` of first variations and the support condition [`SupportedIn`](UpperTailMultipodality/FixedDensities/Defs.lean#L65). |

"`W ≡ r` is the unique minimizer" is formalized as: every minimizer equals `r`
almost everywhere. Since graphons that agree almost everywhere are at cut
distance zero, this is uniqueness up to relabeling.

Two symbols differ from the paper, throughout `FixedDensities/`. The constant of
[Lemma 7.2][lem:degenerate-forms], the paper's `κ`, is written `a` or `c`. The
smoothing parameter of `W_s = (1−s)W + sε` is written `θ` and the measure of an
inserted block is written `s`, which is the paper's Section 7 usage with the two
letters exchanged.

## Proof overview

The two problems share one mechanism. Insert into an optimizer `W` a block of
vertices of small measure `θ` whose row is an arbitrary row `u`, and restore the
constraints. Comparing to first order in `θ` shows that the row functional
`ℱ_W` is bounded below by a constant `c_W` on all rows, and that almost every row
of `W` attains `c_W`
([upper_tail_insertion](UpperTailMultipodality/UpperTail/Insertion.lean#L19),
[fixed_insertion](UpperTailMultipodality/FixedDensities/Insertion.lean#L18)).
All rows of `W` are therefore global minimizers of one and the same functional.

[Theorem 5.1][thm:row-criterion] then says that such a set of rows is finite and
totally ordered. Its proof has three parts. The singularity of `J_q'` at `0` and
`1` confines the minimizers to `[δ, 1-δ]`, where they satisfy an Euler–Lagrange
equation ([row_interior](UpperTailMultipodality/RowCriterion/Basic.lean#L93)).
The lattice inequality for `ℛ_W`, which uses a vertex of degree at least two and
the lower bound `W ≥ ω > 0`, shows that two minimizers cannot cross
([strict_supermodular](UpperTailMultipodality/RowCriterion/Basic.lean#L274),
[row_chain](UpperTailMultipodality/RowCriterion/Basic.lean#L316)). Finally, an
analytic branch of critical rows through each minimizer, parametrized by the
mean, turns an accumulation of minimizers into an interval of minimizers, which
a topological argument excludes
([row_finite](UpperTailMultipodality/RowCriterion/Finite.lean#L27)). Compactness and
finiteness are then stated on `L^∞([0,1])`, where the paper puts `𝓜_W`
([row_compact_Linfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L178) and
[row_finite_Linfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L200)); the proofs run in the
Banach algebra of bounded measurable functions, and `RowCriterion/Linfty.lean` relates the two.

The two applications supply the hypotheses of the criterion. For the upper tail,
a minimizer satisfies `W ≥ p`, has an active constraint and is bounded away from
`1` ([upper_tail_basic](UpperTailMultipodality/UpperTail/Basic.lean#L23)), and
satisfies `J_p'(W) = μ𝒟_W` with `μ > 0`
([upper_tail_multiplier](UpperTailMultipodality/UpperTail/Basic.lean#L37)); for
finitely many constraints the same two conclusions, with `∑_j μ_j 𝒟_{H_j,W}` in
place of `μ𝒟_W`, come from separating the cone of first-order changes
([joint_multiplier](UpperTailMultipodality/UpperTail/Joint/Multiplier.lean#L76)).
For fixed densities, the constraint qualification provides two directions along
which both constraints can be corrected, giving the same two conclusions
([fixed_interior](UpperTailMultipodality/FixedDensities/Interior.lean#L19),
[fixed_multiplier](UpperTailMultipodality/FixedDensities/Interior.lean#L87)).
The values of `τ` at which the constraint qualification can fail form a null set,
because a degenerate maximizer makes the left derivative of the increasing value
function `Ψ_ε` infinite
([degenerate_forms](UpperTailMultipodality/FixedDensities/Degenerate.lean#L26),
[degenerate_slope](UpperTailMultipodality/FixedDensities/Degenerate.lean#L285)).
That set is in fact empty. At a degenerate maximizer almost every row maximizes
`ℛ_W(u) − 2κ∫u` over all rows
([degenerate_insertion](UpperTailMultipodality/FixedDensities/DegenerateInsertion.lean#L40)),
which is impossible for a graphon with an ordered structure
([ordered_nondegenerate](UpperTailMultipodality/FixedDensities/OrderedNondegenerate.lean#L38)).
Such a graphon is produced as an `L¹` limit of maximizers at the good densities
([ordered_compact](UpperTailMultipodality/FixedDensities/Support/OrderedCompact.lean#L316)),
and correcting its two densities along the directions of the qualification bounds
the difference quotients of `Ψ_ε`
([exists_uniform_upward_correction](UpperTailMultipodality/FixedDensities/Support/UniformCorrection.lean#L841)).

## Paper-to-Lean correspondence

Paper citations use the compiled numbers and link to the corresponding LaTeX
source. Lean links point to declaration lines. Names are relative to
`UpperTailMultipodality`.

### Introduction and graphons (Sections 1 and 2)

| Paper result | Lean declaration |
|---|---|
| [Theorem 1.1][thm:joint-upper-tail] — Joint upper tails, finitely many constraints | [joint_upper_tail](UpperTailMultipodality/UpperTail/Joint/Main.lean#L32); for one constraint, [upper_tail](UpperTailMultipodality/UpperTail/Main.lean#L24). The perfect-matching case, which the paper derives inside the proof, is the auxiliary [ae_eq_of_degree_le_one](UpperTailMultipodality/UpperTail/Support/Matching.lean#L171) |
| [Theorem 1.2][thm:fixed-densities] — Fixed edge and subgraph densities | [fixed_densities](UpperTailMultipodality/FixedDensities/Main.lean#L111) |
| [Lemma 2.1][lem:graphon-compactness] — Compactness and continuity in cut distance | Assumed; see *Axioms and dependencies* |
| [Eq. (10)][eq:entropy-identity] — The entropy identity | [entropy_identity](UpperTailMultipodality/Preliminaries/EntropyIdentity.lean#L19) |

### Variations of densities and relative entropy (Section 3)

| Paper result | Lean declaration |
|---|---|
| [Eq. (15)][eq:density-derivative] — First variation of `t(H,·)` | [first_variation](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L203), and for several directions [hasFDerivAt_tDensity_lincomb](UpperTailMultipodality/Preliminaries/Perturbation.lean#L93) |
| [Example 3.1][expl:triangle-derivative] — `𝒟_{K₃,W}(x,y) = 3∫W(x,z)W(y,z)dz` | [derivKernel_triangle](UpperTailMultipodality/Preliminaries/Examples.lean#L67) |
| [Example 3.2][expl:path-derivative] — `𝒟_{P₃,W}(x,y) = d_W(x) + d_W(y)` | [derivKernel_path](UpperTailMultipodality/Preliminaries/Examples.lean#L170), for the degree function [Graphon.deg](UpperTailMultipodality/Preliminaries/Examples.lean#L53) |
| [Eq. (16)][eq:derivative-kernel-lipschitz] — `L¹` Lipschitz bound for `W ↦ 𝒟_{H,W}` | [abs_integral_derivKernel_mul_sub_le](UpperTailMultipodality/FixedDensities/Support/UniformCorrection.lean#L157), in the paired form the proof of [Lemma 7.9][lem:uniform-density-restoration] uses: `\|∫∫ 𝒟_W U − ∫∫ 𝒟_{W'} U\| ≤ m²B‖W − W'‖₁` for `U` bounded by `B`. The constant is `m²` rather than the paper's `m(m−1)`, which is enough for every use. The pointwise form is [abs_derivKernel_sub_le](UpperTailMultipodality/FixedDensities/Support/InsertionEstimates.lean#L198) |
| [Lemma 3.3][lem:upper-tail-basic] — Interiority and active constraints | One constraint: [upper_tail_basic](UpperTailMultipodality/UpperTail/Basic.lean#L23); a family: [joint_ae_ge](UpperTailMultipodality/UpperTail/Joint/Basic.lean#L43), [joint_exists_active](UpperTailMultipodality/UpperTail/Joint/Basic.lean#L77) and [joint_exists_ae_le_one_sub](UpperTailMultipodality/UpperTail/Joint/Basic.lean#L150) |

### Global row minimality for upper-tail optimizers (Section 4)

| Paper result | Lean declaration |
|---|---|
| [Eq. (22)][eq:rooted-average] — `∫ ℛ_W(W_x) dx = N t(H,W)` | [rooted_average](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L192) |
| [Eq. (25)][eq:rooted-lipschitz] — Lipschitz bound for `ℛ_W` | [rooted_lipschitz](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L207) |
| `∇ℛ_W(W_x) = 2𝒟_W(x,·)` — the gradient at a row of `W`, which the paper uses without displaying it | [rootedGradient_row](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L222) |
| [Example 4.1][expl:triangle-rooted] — `ℛ_{K₃,W}(u) = 3∫∫W(y,z)u(y)u(z)` | [rootedDensity_triangle](UpperTailMultipodality/Preliminaries/Examples.lean#L113) and [totalRootedDensity_triangle](UpperTailMultipodality/Preliminaries/Examples.lean#L136) |
| [Example 4.2][expl:path-rooted] — `ℛ^mid = (∫u)²`, `ℛ^end = ∫d_W u`, so `ℛ_{P₃,W}(u) = (∫u)² + 2∫d_W u` | [rootedDensity_path_mid](UpperTailMultipodality/Preliminaries/Examples.lean#L217), [rootedDensity_path_end](UpperTailMultipodality/Preliminaries/Examples.lean#L237), [totalRootedDensity_path](UpperTailMultipodality/Preliminaries/Examples.lean#L286) |
| [Lemma 4.3][lem:insertion-first-order] — First-order changes of insertions | [hasDerivAt_insertionPoly](UpperTailMultipodality/Insertion/FirstOrder.lean#L175) and [hasDerivAt_insertion_Ip](UpperTailMultipodality/Insertion/FirstOrder.lean#L273), for one inserted block and one interior direction; for a block whose rows vary, [hasDerivAt_insertionPolyRows](UpperTailMultipodality/Insertion/FirstOrderRows.lean#L81) and [eventually_exists_insertGraphonRows](UpperTailMultipodality/Insertion/FirstOrderRows.lean#L226) |
| [Lemma 4.4][lem:upper-tail-multiplier] — Lagrange multipliers | [joint_multiplier](UpperTailMultipodality/UpperTail/Joint/Multiplier.lean#L76); one constraint, without the cone, [upper_tail_multiplier](UpperTailMultipodality/UpperTail/Basic.lean#L37). The cone of first-order changes is [insertionCone](UpperTailMultipodality/UpperTail/Joint/Cone.lean#L57), it misses the improving directions by [insertionCone_disjoint](UpperTailMultipodality/UpperTail/Joint/Disjoint.lean#L123), and the separation is [exists_multipliers_of_cone_disjoint](UpperTailMultipodality/UpperTail/Joint/Separation.lean#L106) |
| [Lemma 4.5][lem:global-row-minimality] — Global row minimality | The row bound and the rows attaining it are the last two conclusions of [joint_multiplier](UpperTailMultipodality/UpperTail/Joint/Multiplier.lean#L76) and [ae_combinedRowFunctional_row_eq](UpperTailMultipodality/Insertion/Rows.lean#L165); one constraint: [upper_tail_insertion](UpperTailMultipodality/UpperTail/Insertion.lean#L19) |

### Finiteness of ordered row minimizers (Section 5)

| Paper result | Lean declaration |
|---|---|
| [Theorem 5.1][thm:row-criterion] — Finite ordered row minimizers | [row_criterion_family](UpperTailMultipodality/RowCriterion/Main.lean#L29), with the one-term case [row_criterion](UpperTailMultipodality/RowCriterion/Main.lean#L53) |
| [Lemma 5.2][lem:row-interior] — Row interiority and [Eq. (31)][eq:row-euler] | [row_interior](UpperTailMultipodality/RowCriterion/Basic.lean#L93) |
| [Proposition 5.3][prop:row-ordering] — Total order | [row_chain](UpperTailMultipodality/RowCriterion/Basic.lean#L316); the lattice inequality it rests on, strict when the two rows cross, is [strict_supermodular](UpperTailMultipodality/RowCriterion/Basic.lean#L274) |
| [Lemma 5.4][lem:row-compact] — Compactness of `𝓜_W` | In `L^∞([0,1])`, as the paper states it, [row_compact_Linfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L178); on bounded measurable representatives, [row_compact](UpperTailMultipodality/RowCriterion/Finiteness/Compact.lean#L35), with the sequential form the paper's proof produces, [row_compact_seq](UpperTailMultipodality/RowCriterion/Finiteness/Compact.lean#L55). Proved by a different route; see *Differences in proof methods* |
| [Lemma 5.5][lem:row-lower-bound] — Positive lower bound for the second variation | On bounded directions, [exists_secondVariation_lower_bound](UpperTailMultipodality/RowCriterion/Finiteness/Positivity.lean#L200) with the explicit constant `8κ/(2C+κ)`; on `L²([0,1])`, as the paper states it, [exists_secondVariationL2_lower_bound](UpperTailMultipodality/RowCriterion/Finiteness/SecondVariationL2.lean#L598) for the Banach space `Lp ℝ 2 unitμ` and [exists_secondVariationFun_lower_bound](UpperTailMultipodality/RowCriterion/Finiteness/SecondVariationL2.lean#L544) for square-integrable functions. `Q_u` itself is [secondVariationL2](UpperTailMultipodality/RowCriterion/Finiteness/SecondVariationL2.lean#L181) on `L²([0,1])` and [secondVariationLinfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L228) on `L^∞([0,1])`, the domain the paper gives it. The strict positivity that [Lemma 5.6][lem:bordered] uses is the corollary [secondVariation_pos](UpperTailMultipodality/RowCriterion/Finiteness/Positivity.lean#L228). Proved by a different route; see *Differences in proof methods* |
| [Lemma 5.6][lem:bordered] — Linearization at fixed mean | On `L^∞([0,1]) × ℝ`, as the paper states it, [borderedEquivLinfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L447); on `BddMeas × ℝ`, which is where the implicit function theorem of [Lemma 5.7][lem:row-finite] applies it, [borderedEquiv](UpperTailMultipodality/RowCriterion/Finiteness/Bordered.lean#L720). The first is the second descended along [BddMeas.toLinfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L47), by [borderedOp_congr_ae](UpperTailMultipodality/RowCriterion/Linfty.lean#L271) |
| [Lemma 5.7][lem:row-finite] — Finiteness | In `L^∞([0,1])`, as the paper states it, [row_finite_Linfty](UpperTailMultipodality/RowCriterion/Linfty.lean#L200); on representatives, [row_finite](UpperTailMultipodality/RowCriterion/Finite.lean#L27). The analytic implicit function theorem that its proof cites is proved inside the project, in `RowCriterion/Finiteness/ImplicitFunction.lean` |

### Fixed densities (Section 6)

| Paper result | Lean declaration |
|---|---|
| [Definition 6.1][def:constraint-qualification] — Constraint qualification | [ConstraintQualification](UpperTailMultipodality/FixedDensities/Defs.lean#L71) |
| [Lemma 6.2][lem:fixed-interior] — Interiority | [fixed_interior](UpperTailMultipodality/FixedDensities/Interior.lean#L19) |
| [Lemma 6.3][lem:fixed-monotonicity] — `Ψ_ε` is strictly increasing | The two assertions are [fixedValue_strictMonoOn](UpperTailMultipodality/FixedDensities/Monotone.lean#L68) and, for the comparison `I_ε(U) ≥ Ψ_ε(τ)` with its strict case, [fixedValue_le_Ip](UpperTailMultipodality/FixedDensities/Monotone.lean#L27). Read at a minimizer, the comparison relaxes the equality constraint of [Eq. (35)][eq:fixed-problem] to `t(H,U) ≥ τ`, which is the form the insertion arguments use: [fixed_inequality_minimality](UpperTailMultipodality/FixedDensities/Monotone.lean#L57). `fixed_monotone` bundles the two for the downstream callers |
| [Lemma 6.4][lem:fixed-multiplier] — Lagrange multipliers | [fixed_multiplier](UpperTailMultipodality/FixedDensities/Interior.lean#L87) |
| [Lemma 6.5][lem:fixed-insertion] — Global row minimality | [fixed_insertion](UpperTailMultipodality/FixedDensities/Insertion.lean#L18) |
| [Proposition 6.6][prop:nondegenerate-multipodality] — Maximizers satisfying the qualification | [fixed_densities_of_cq](UpperTailMultipodality/FixedDensities/Qualified.lean#L24), concluding `IsOrderedMultipodal`. The paper states the conclusion as "multipodal with an ordered structure"; for a multipodal graphon the two are the same, and [exists_hasOrderedRows_of_isOrderedMultipodal](UpperTailMultipodality/FixedDensities/Support/OrderedCompact.lean#L872) is the direction [Section 7][sec:degenerate-optimizers] needs |

### Excluding degenerate optimizers (Section 7)

| Paper result | Lean declaration |
|---|---|
| [Proposition 7.1][prop:optimizer-nondegeneracy] — Every optimizer satisfies the qualification | [optimizer_nondegeneracy](UpperTailMultipodality/FixedDensities/Main.lean#L35), from which [fixed_densities](UpperTailMultipodality/FixedDensities/Main.lean#L111) is immediate |
| [Lemma 7.2][lem:degenerate-forms] — `\|Ω\| > 0` and `𝒟_W` constant on `Ω` | [degenerate_interior_const](UpperTailMultipodality/FixedDensities/OrderedNondegenerate.lean#L295), assembled from `\|Ω_η(W)\| > 0` for some `η > 0` ([exists_interior_window](UpperTailMultipodality/FixedDensities/Support/InteriorWindow.lean#L36)) and the constant on `{0 < W < 1}` ([exists_deriv_const_on_interior](UpperTailMultipodality/FixedDensities/Support/OrderedWindow.lean#L44)). [degenerate_forms](UpperTailMultipodality/FixedDensities/Degenerate.lean#L26) is a dichotomy form that [Lemma 7.3][lem:degenerate-smoothing] consumes: either `W ∈ {0,1}` on a set of positive measure, or `0 < W < 1` almost everywhere and `𝒟_W` is almost everywhere constant |
| [Lemma 7.3][lem:degenerate-smoothing] — Smoothing towards the constant graphon | [degenerate_smoothing](UpperTailMultipodality/FixedDensities/Degenerate.lean#L518): positivity of `g_θ` and `d_θ` on `(0,1)` is [smoothing_pos](UpperTailMultipodality/FixedDensities/Degenerate.lean#L383) and the ratio bound is [degenerate_gain](UpperTailMultipodality/FixedDensities/Degenerate.lean#L134), the form [Lemma 7.4][lem:degenerate-slope] and [Lemma 7.6][lem:degenerate-insertion] use. The polynomial order `d_θ = a_kθ^k + O(θ^{k+1})` is [exists_smoothing_deficit_order](UpperTailMultipodality/FixedDensities/Degenerate.lean#L443), from the analyticity [analyticAt_mixTDensity](UpperTailMultipodality/FixedDensities/Degenerate.lean#L429); the two separate rate estimates are not stated on their own |
| [Lemma 7.4][lem:degenerate-slope] — Infinite left derivative of `Ψ_ε` | [degenerate_slope](UpperTailMultipodality/FixedDensities/Degenerate.lean#L285); the form used by [Corollary 7.5][cor:almost-every-tau] is [degenerate_slope_frequently](UpperTailMultipodality/FixedDensities/Degenerate.lean#L367) |
| [Corollary 7.5][cor:almost-every-tau] — Null set of degenerate values | [almost_every_tau](UpperTailMultipodality/FixedDensities/AlmostEvery.lean#L16) |
| [Lemma 7.6][lem:degenerate-insertion] — Insertion at a degenerate minimizer | [degenerate_insertion](UpperTailMultipodality/FixedDensities/DegenerateInsertion.lean#L40) |
| [Lemma 7.7][lem:ordered-nondegenerate] — A minimizer with an ordered structure is nondegenerate | [ordered_nondegenerate](UpperTailMultipodality/FixedDensities/OrderedNondegenerate.lean#L38), for the predicate [HasOrderedRows](UpperTailMultipodality/FixedDensities/Support/Ordered.lean#L72), which is [Definition 2.2][def:ordered-structure] with the relabeling applied |
| [Lemma 7.8][lem:ordered-compact] — `L¹`-compactness of graphons with an ordered structure | [ordered_compact](UpperTailMultipodality/FixedDensities/Support/OrderedCompact.lean#L316), for graphons already relabeled to have ordered rows; [exists_hasOrderedRows_of_isOrderedMultipodal](UpperTailMultipodality/FixedDensities/Support/OrderedCompact.lean#L872) performs the paper's relabeling for the ordered multipodal graphons it is applied to, preserving `e`, `t(H,·)` and `I_ε` |
| [Lemma 7.9][lem:uniform-density-restoration] — Uniform restoration of both densities | [exists_uniform_upward_correction](UpperTailMultipodality/FixedDensities/Support/UniformCorrection.lean#L841), which states the consequence used in the proof of [Theorem 1.2][thm:fixed-densities]: `Ψ_ε(τ) ≤ Ψ_ε(τ_n) + C(τ - τ_n)` for the minimizers `W_n` at `τ_n` |

## Axioms and dependencies

The four external results assumed as axioms are the graph-limit facts recorded
in [CutContinuity.lean](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean).
They are the content of [Lemma 2.1][lem:graphon-compactness].
Lean's foundational axioms `propext`, `Classical.choice` and `Quot.sound` are
excluded from the table.

| Axiom | Exact assumed content |
|---|---|
| [cut_seqCompact](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean#L92) | Every graphon sequence has a subsequence converging in cut distance to a graphon. |
| [edgeDensity_cutContinuous](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean#L97) | If a graphon sequence converges in cut distance, its edge densities converge. |
| [tDensity_cutContinuous](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean#L102) | Under the same convergence, `t(H,W_n) → t(H,W)` for every finite simple graph `H`. |
| [Ip_cut_lowerSemicontinuous](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean#L111) | For `0 < p < 1`, the sublevel sets of `I_p` are closed under cut convergence. |

The table below shows which results use them; a check mark means the proof uses
all four, a dash that it uses none.

| Paper result | Cut axioms |
|---|:---:|
| [Theorem 1.1][thm:joint-upper-tail] — Joint upper tails | — |
| [Proposition 6.6][prop:nondegenerate-multipodality] — Fixed densities under the qualification | ✓ |
| [Corollary 7.5][cor:almost-every-tau] — Almost every `τ` | ✓ |
| [Theorem 1.2][thm:fixed-densities] — Fixed edge and subgraph densities | ✓ |

The cut axioms enter only through the existence of a minimizer of
[Eq. (35)][eq:fixed-problem], which the paper also obtains from compactness. So they
are used by every statement that names `Ψ_ε`, including the monotonicity half of
[Lemma 6.3][lem:fixed-monotonicity]; the comparison half, `fixedValue_le_Ip`, does
not use them.
The development contains no `sorry` and no other axiom.

## Differences in proof methods

Some Lean proofs use different arguments from those in the paper.

- **Lagrange multipliers ([Lemma 6.4][lem:fixed-multiplier]).** The paper applies
  the multiplier rule in the Banach space `L^∞_sym([0,1]²)`. The Lean proofs use
  finitely many directions instead: for a bounded symmetric kernel `U`, the
  constraints are restored along one or two auxiliary directions, by an
  elementary computation for the upper-tail problem and by the two-dimensional
  implicit function theorem for fixed densities, where the invertible matrix
  is the `Γ_W(U₁,U₂)` of the constraint qualification. Taking `U` to be a bounded
  representative of `J_p'(W) − μ𝒟_W` then gives the Euler–Lagrange equation
  almost everywhere.
- **The upper-tail multipliers ([Lemma 4.4][lem:upper-tail-multiplier]).** For a
  family of constraints the cone separation is used, as in the paper. For one
  constraint the formalization keeps a shorter route, which is where `upper_tail`
  gets its multiplier: moving in the direction `𝟙` increases `t(H,·)`, so the sign
  is immediate and no cone is needed.
- **The insertion construction ([Lemma 4.3][lem:insertion-first-order],
  [Lemma 6.5][lem:fixed-insertion]).** The inserted block is described by an
  explicit measure-preserving map of `[0,1]`, which yields the exact expansion of
  `t(H,·)`, `e` and `I_p` in the block measure `θ`: a sum over the subsets of `V(H)`
  occupied by the new block, of which [Eq. (20)][eq:insertion-density-expansion]
  keeps the two leading terms. Because the upper-tail
  constraint is an inequality and, for fixed densities,
  [Lemma 6.3][lem:fixed-monotonicity] turns the equality constraint into
  an inequality one, no implicit function is needed to keep the constraints: it
  suffices to move in a direction that does not decrease the constrained
  densities.
- **Compactness of `𝓜_W` ([Lemma 5.4][lem:row-compact]).** The statement is
  proved, by a different route. The paper writes each term `G_{v,z₀}(u)` of
  [Eq. (23)][eq:rooted-gradient-kernel] as `T_K(u^{⊗k})` for a Hilbert–Schmidt
  operator `T_K : L²([0,1]^k) → L²([0,1])`, so the weighted gradients of rows are
  relatively compact in `L²`, and then transfers the convergence back to the rows.
  In Lean each row minimizer is replaced by its canonical representative
  `σ(ℓ(q) + α + (μ/2)∇ℛ_W(u))`, which satisfies the Euler–Lagrange equation
  everywhere. Since two minimizers are ordered, their `L¹` distance is the
  difference of their means, so the mean is injective on `𝓜_W`, the set `A` of
  means is a closed subset of `[0,1]` and hence compact, and the Lipschitz bound
  [Eq. (26)][eq:gradient-lipschitz] for `∇ℛ_W` makes the representatives a
  continuous image of `A`. The scaffolding is shared with
  [Lemma 5.7][lem:row-finite] through `MeanParam`
  ([Finiteness/MeanParam.lean](UpperTailMultipodality/RowCriterion/Finiteness/MeanParam.lean)),
  and uses no operator between `L²([0,1]^k)` and `L²([0,1])`. It also does not use
  [Lemma 5.7][lem:row-finite], so compactness remains available where the paper
  uses it.
- **The positive lower bound ([Lemma 5.5][lem:row-lower-bound]).** The uniform
  bound `Q_u(h) ≥ c_u‖h‖₂²` on mean-zero directions is proved, with an explicit
  constant, by a different route. The paper obtains the constant from weak `L²`
  compactness together with the compactness of `T_{K_u}`. Lean instead combines two
  elementary estimates: discarding the nonnegative diagonal terms of the
  `h = h₊ - h₋` splitting bounds `Q_u(h)` below by `(κ/2)‖h‖₁²` with
  `κ = μ_{j₀}c^Nω^{m_{j₀}} > 0`, while `J_q'' ≥ 4` and the `L¹`-to-pointwise bound on
  `D∇𝒫_W(u)` give `Q_u(h) ≥ 8‖h‖₂² - C‖h‖₁²`; adding `2C` times the first to `κ`
  times the second cancels `‖h‖₁²` and yields `c_u = 8κ/(2C + κ)`. The bound is proved first
  on bounded directions, where `Q_u` is defined, and then on `L²([0,1])` as the paper states
  it: `secondVariationFun` extends `Q_u` to square-integrable directions, the extension is
  `L²`-continuous (`exists_abs_secondVariationFun_sub_le`), and the mean-zero truncations of
  `exists_bddMeas_approx` carry the bound across with the same constant.
  Independently of the bound, the surjectivity half of
  [Lemma 5.6][lem:bordered] comes from the Fredholm alternative on `L²` for a
  compact operator — whose compactness is proved from scratch through an `L²`
  approximation of the kernel by finite sums of products — rather than from the
  paper's minimization of the quadratic functional `ℰ`.
- **The Banach space of rows.** The paper's ambient space for rows is `L^∞([0,1])`: that is
  where `𝓜_W` lives, where `Q_u` is defined, and where [Lemma 5.6][lem:bordered] inverts the
  bordered operator. All four statements are formalized on Mathlib's `L^∞([0,1]) =
  Lp ℝ ∞ unitμ` in `RowCriterion/Linfty.lean`: `rowMinimizersLinfty`, `row_compact_Linfty`,
  `row_finite_Linfty`, `secondVariationLinfty`, `borderedEquivLinfty`, and
  [Lemma 5.5][lem:row-lower-bound] on `Lp ℝ 2 unitμ` as `exists_secondVariationL2_lower_bound`.

  The *proofs* run one level below, in `BddMeas`: the genuine bounded measurable functions with
  the sup norm, that is, the measurable part of `ℓ^∞(ℝ)`. Two reasons. Mathlib's `Lp ℝ ∞`
  carries no multiplication, so it is not a Banach algebra, and the analytic implicit function
  theorem of [Lemma 5.7][lem:row-finite] needs one: the fixed-point equation
  `u = σ(ℓ(q) + α + ½∇𝒫_W(u))` is solved by a power series in the algebra. And point evaluation
  is continuous on `BddMeas`, so the pointwise identities for `exp` and the logistic function
  are immediate. `BddMeas.toLinfty` is the quotient map, `1`-Lipschitz with
  `BddMeas.ofLinfty` as a norm-non-increasing section, so it is onto and the statements transfer
  both ways; `combinedRowFunctional_congr_ae`, `combinedLinFun_congr` and `borderedOp_congr_ae`
  are the three facts that none of the data sees null sets.

  `L²([0,1])` appears in the paper only inside the proofs of
  [Lemma 5.4][lem:row-compact], [Lemma 5.5][lem:row-lower-bound] and
  [Lemma 5.6][lem:bordered]. The same two layers are used there: `secondVariationFun` is `Q_u`
  on square-integrable measurable functions and `secondVariationL2` is `Q_u` on `Lp ℝ 2 unitμ`.
- **Insertion at a degenerate minimizer ([Lemma 7.6][lem:degenerate-insertion]).**
  The paper solves the two constraints simultaneously, by the implicit function
  theorem applied uniformly in the smoothing parameter. In Lean the edge density
  is affine in the size of the interior correction, so that correction restores it
  exactly, and the `H`-density is then reached by the intermediate value theorem
  in the smoothing parameter at a fixed block measure. The lower bound on the
  increment that this needs is the expansion of the insertion polynomial, uniform
  in the base graphon.
- **Ordered structure ([Definition 2.2][def:ordered-structure],
  [Proposition 6.6][prop:nondegenerate-multipodality],
  [Lemma 7.7][lem:ordered-nondegenerate], [Lemma 7.8][lem:ordered-compact]).** The paper
  calls `W` ordered when *some* measure-preserving relabeling `W^φ` is nondecreasing in
  both variables, and states these three results with that phrase. The formalization
  carries the relabeled graphon instead of the relabeling: `HasOrderedRows` is the case
  `φ = id`, and `ordered_compact` both assumes and concludes it. Nothing is lost, because
  the ordering is used at exactly one point — `optimizer_nondegeneracy` applies
  `ordered_nondegenerate` to the `L¹` limit `W_*`, which has ordered rows outright — and the
  approximating maximizers enter only through
  `exists_hasOrderedRows_of_isOrderedMultipodal`, which replaces each by an ordered-rows
  graphon with the same `e`, `t(H,·)` and `I_ε`, the only three quantities the argument then
  reads. Producing the paper's `φ` itself would need a measure isomorphism from a measurable
  set onto an interval of the same length, which Mathlib does not have.
- **Compactness of ordered graphons ([Lemma 7.8][lem:ordered-compact]).** The
  conditional expectation `Π_k` is realized as composition with the dyadic floor
  `x ↦ ⌊2^j x⌋ / 2^j`, whose `L¹` error comes from the one-dimensional estimate
  [integral_sub_translate_le](UpperTailMultipodality/FixedDensities/Support/MonotoneL1.lean#L32).
  The convergent subsequence is extracted from the values at pairs of rationals, a
  sequence in the compact cube `[0,1]^(ℚ × ℚ)`.

## Scope

Both theorems of the paper are formalized. [Appendix A][app:arw], which compares the
assumptions of the paper with those of Alvarado, Ramon and Wang, is not formalized. Its
first part restates the definitions of that preprint, so there is nothing to prove. Its
single proposition, [Proposition A.1][prop:arw-entropy-counterexample], rests on the finite
forcibility of the half-graphon and on the invariance of the entropy and of the degree
distribution under weak isomorphism of bounded kernels; none of these is available in
Mathlib.

<!-- Paper citations link to the corresponding source labels. -->
[thm:joint-upper-tail]: paper/sections/intro.tex#L167
[thm:fixed-densities]: paper/sections/intro.tex#L264
[lem:graphon-compactness]: paper/sections/graphons.tex#L65
[eq:ordered-blocks]: paper/sections/graphons.tex#L93
[eq:entropy-identity]: paper/sections/graphons.tex#L164
[def:ordered-structure]: paper/sections/graphons.tex#L102
[eq:derivative-kernel]: paper/sections/density_variations.tex#L53
[eq:derivative-kernel-lipschitz]: paper/sections/density_variations.tex#L75
[eq:density-derivative]: paper/sections/density_variations.tex#L58
[lem:upper-tail-basic]: paper/sections/density_variations.tex#L118
[expl:triangle-derivative]: paper/sections/density_variations.tex#L80
[expl:path-derivative]: paper/sections/density_variations.tex#L95
[eq:vertex-insertion]: paper/sections/row_minimality.tex#L40
[eq:rooted-density]: paper/sections/row_minimality.tex#L61
[eq:total-rooted-density]: paper/sections/row_minimality.tex#L69
[eq:insertion-density-expansion]: paper/sections/row_minimality.tex#L75
[eq:rooted-average]: paper/sections/row_minimality.tex#L100
[eq:rooted-gradient-kernel]: paper/sections/row_minimality.tex#L133
[eq:rooted-lipschitz]: paper/sections/row_minimality.tex#L160
[eq:gradient-lipschitz]: paper/sections/row_minimality.tex#L176
[expl:triangle-rooted]: paper/sections/row_minimality.tex#L181
[expl:path-rooted]: paper/sections/row_minimality.tex#L192
[lem:insertion-first-order]: paper/sections/row_minimality.tex#L234
[lem:upper-tail-multiplier]: paper/sections/row_minimality.tex#L321
[eq:row-functional]: paper/sections/row_minimality.tex#L427
[lem:global-row-minimality]: paper/sections/row_minimality.tex#L441
[thm:row-criterion]: paper/sections/row_criterion.tex#L13
[lem:row-interior]: paper/sections/row_criterion.tex#L24
[eq:row-euler]: paper/sections/row_criterion.tex#L28
[prop:row-ordering]: paper/sections/row_criterion.tex#L79
[lem:row-compact]: paper/sections/row_criterion.tex#L178
[lem:row-lower-bound]: paper/sections/row_criterion.tex#L351
[lem:bordered]: paper/sections/row_criterion.tex#L441
[lem:row-finite]: paper/sections/row_criterion.tex#L549
[eq:fixed-problem]: paper/sections/fixed_densities.tex#L6
[def:constraint-qualification]: paper/sections/fixed_densities.tex#L51
[lem:fixed-interior]: paper/sections/fixed_densities.tex#L124
[lem:fixed-monotonicity]: paper/sections/fixed_densities.tex#L268
[lem:fixed-multiplier]: paper/sections/fixed_densities.tex#L311
[lem:fixed-insertion]: paper/sections/fixed_densities.tex#L509
[prop:nondegenerate-multipodality]: paper/sections/fixed_densities.tex#L538
[prop:optimizer-nondegeneracy]: paper/sections/degenerate_optimizers.tex#L6
[lem:degenerate-forms]: paper/sections/degenerate_optimizers.tex#L27
[lem:degenerate-smoothing]: paper/sections/degenerate_optimizers.tex#L55
[lem:degenerate-slope]: paper/sections/degenerate_optimizers.tex#L119
[cor:almost-every-tau]: paper/sections/degenerate_optimizers.tex#L146
[lem:degenerate-insertion]: paper/sections/degenerate_optimizers.tex#L171
[lem:ordered-nondegenerate]: paper/sections/degenerate_optimizers.tex#L369
[lem:ordered-compact]: paper/sections/degenerate_optimizers.tex#L438
[sec:degenerate-optimizers]: paper/sections/degenerate_optimizers.tex#L1
[app:arw]: paper/sections/appendix_arw.tex#L1
[prop:arw-entropy-counterexample]: paper/sections/appendix_arw.tex#L138
[lem:uniform-density-restoration]: paper/sections/degenerate_optimizers.tex#L541