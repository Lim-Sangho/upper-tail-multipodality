# Formalization guide

This guide connects the definitions, proofs and numbered results of the
[paper](paper/paper.tex) to their Lean declarations. It covers the graphon
theory of Sections 1–5. The appendix on the preprints of Alvarado, Ramon and
Wang is outside the formalization.

## Definitions and notation

The paper fixes a finite simple graph `H` with `N = |V(H)|` vertices and
`m = |E(H)| ≥ 1` edges, and studies two problems: the upper-tail problem
`Φ_H(p,r) = inf { I_p(W) : t(H,W) ≥ r^m }` for `0 < p < r < 1`, and the
maximization of the entropy at prescribed edge density `ε` and `H`-density `τ`.

| Paper notation or concept | Lean representation |
|---|---|
| A graphon on `[0,1]²` | `Graphon` is a symmetric measurable kernel on `ℝ²` with values in `[0,1]`; integration uses `unitμ` on `[0,1]` and `gμ` on its square. `UnitGraphon` uses the paper's domain directly, and the conversions in [UnitGraphon.lean](UpperTailMultipodality/Preliminaries/Graphons/UnitGraphon.lean) preserve all densities. |
| `e(W)`, `t(H,W)`, `J_p`, `I_p`, `s(W)` | `Graphon.edgeDensity`, `Graphon.tDensity`, `Jp`, `Graphon.Ip`, `Graphon.entropy`. Only `s(W)` carries the factor `1/2`. |
| `Φ_H(p,r)`, feasibility | `phiVar` and `Feasible`; a minimizer is a feasible `W` with `W.Ip p = phiVar H p r`. |
| The row `W_x = W(x,·)` | [`Graphon.row`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L21); a *row* in the sense of `ℱ_W` is any measurable `u : ℝ → ℝ` with values in `[0,1]`, the predicate [`IsRow`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L23). |
| Multipodal, ordered blocks ([Eq. (2)][eq:ordered-blocks]) | [`BlockStructure`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L26) collects finitely many measurable, pairwise disjoint blocks covering `[0,1]` up to a null set, with symmetric values in `[0,1]`; [`IsMultipodal`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L48) and [`IsOrderedMultipodal`](UpperTailMultipodality/Preliminaries/Multipodal.lean#L52). Blocks of measure zero are allowed, as in the paper. |
| Bounded symmetric kernels | [`Kernel`](UpperTailMultipodality/Preliminaries/Kernel.lean#L23), with `Kernel.tDensity`, `Kernel.edgeDensity`, `Kernel.Ip` and `Kernel.lincomb K U s = K + ∑ᵢ sᵢUᵢ`. Perturbation directions are kernels; graphons are kernels with values in `[0,1]`. |
| `𝒟_W` ([Eq. (9)][eq:derivative-kernel]) | [`derivKernel`](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L36), defined as `½ ∑_{(a,b) adjacent} K_{ab,W}` with [`edgeRemovedDensity`](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L30); the two orientations of an edge give the paper's `K_{ab,W}(x,y) + K_{ab,W}(y,x)`. |
| `ℛ_{v,W}(u)`, `ℛ_W(u)`, `∇ℛ_W(u)` ([Eq. (11)][eq:rooted-density]) | [`rootedDensity`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L31), [`totalRootedDensity`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L37), [`rootedGradient`](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L49). The integrals are over all coordinates; the root variable does not occur in the integrand. |
| `ℱ_W` ([Eq. (16)][eq:row-functional]), `𝓜_W` | [`rowFunctional`](UpperTailMultipodality/RowCriterion/Defs.lean#L20) and [`rowMinimizers`](UpperTailMultipodality/RowCriterion/Defs.lean#L25). |
| `τ_max(ε)`, `Ψ_ε(τ)` ([Eq. (29)][eq:fixed-problem]), maximizers | [`tauMax`](UpperTailMultipodality/FixedDensities/Defs.lean#L21), [`fixedValue`](UpperTailMultipodality/FixedDensities/Defs.lean#L31), [`IsEntropyMaximizer`](UpperTailMultipodality/FixedDensities/Defs.lean#L26) and [`IsFixedMinimizer`](UpperTailMultipodality/FixedDensities/Defs.lean#L35); they agree by [isEntropyMaximizer_iff](UpperTailMultipodality/FixedDensities/Defs.lean#L40). |
| The constraint qualification ([Definition 5.1][def:constraint-qualification]) | [`ConstraintQualification`](UpperTailMultipodality/FixedDensities/Defs.lean#L70), with the determinant [`cqDet`](UpperTailMultipodality/FixedDensities/Defs.lean#L59) of the matrix of first variations and the support condition [`SupportedIn`](UpperTailMultipodality/FixedDensities/Defs.lean#L65). |

"`W ≡ r` is the unique minimizer" is formalized as: every minimizer equals `r`
almost everywhere. Since graphons that agree almost everywhere are at cut
distance zero, this is uniqueness up to relabeling.

## Proof overview

The two theorems share one mechanism. Insert into an optimizer `W` a block of
vertices of small measure `θ` whose row is an arbitrary row `u`, and restore the
constraints. Comparing to first order in `θ` shows that the row functional
`ℱ_W` is bounded below by a constant `c_W` on all rows, and that almost every row
of `W` attains `c_W`
([upper_tail_insertion](UpperTailMultipodality/UpperTail/Insertion.lean#L18),
[fixed_insertion](UpperTailMultipodality/FixedDensities/Insertion.lean#L18)).
All rows of `W` are therefore global minimizers of one and the same functional.

[Theorem 3.1][thm:row-criterion] then says that such a set of rows is finite and
totally ordered. Its proof has three parts. The singularity of `J_q'` at `0` and
`1` confines the minimizers to `[δ, 1-δ]`, where they satisfy an Euler–Lagrange
equation ([row_interior](UpperTailMultipodality/RowCriterion/Basic.lean#L19)).
Strict supermodularity of `ℛ_W`, which uses a vertex of degree at least two and
the lower bound `W ≥ ω > 0`, shows that two minimizers cannot cross
([strict_supermodular](UpperTailMultipodality/RowCriterion/Basic.lean#L185),
[row_chain](UpperTailMultipodality/RowCriterion/Basic.lean#L241)). Finally, an
analytic branch of critical rows through each minimizer, parametrized by the
mean, turns an accumulation of minimizers into an interval of minimizers, which
a topological argument excludes
([row_finite](UpperTailMultipodality/RowCriterion/Finite.lean#L27)).

The two applications supply the hypotheses of the criterion. For the upper tail,
a minimizer satisfies `W ≥ p`, has an active constraint and is bounded away from
`1` ([upper_tail_basic](UpperTailMultipodality/UpperTail/Basic.lean#L19)), and
satisfies `J_p'(W) = μ𝒟_W` with `μ > 0`
([upper_tail_multiplier](UpperTailMultipodality/UpperTail/Basic.lean#L31)). For
prescribed densities, the constraint qualification provides two directions along
which both constraints can be corrected, giving the same two conclusions
([fixed_interior](UpperTailMultipodality/FixedDensities/Interior.lean#L19),
[fixed_multiplier](UpperTailMultipodality/FixedDensities/Interior.lean#L87)).
The values of `τ` at which the constraint qualification can fail form a null set,
because a degenerate maximizer forces the left difference quotients of the
monotone value function `Ψ_ε` to be unbounded
([degenerate_forms](UpperTailMultipodality/FixedDensities/Degenerate.lean#L19),
[degenerate_slope](UpperTailMultipodality/FixedDensities/Degenerate.lean#L126)).

## Paper-to-Lean correspondence

Paper citations use the compiled numbers and link to the corresponding LaTeX
source. Lean links point to declaration lines. Names are relative to
`UpperTailMultipodality`.

### Introduction and preliminaries

| Paper result | Lean declaration |
|---|---|
| [Theorem 1.1][thm:upper-tail] — Upper tails | [upper_tail](UpperTailMultipodality/UpperTail/Main.lean#L23) |
| [Theorem 1.2][thm:fixed-densities] — Prescribed edge and subgraph densities | [fixed_densities](UpperTailMultipodality/FixedDensities/Main.lean#L19) |
| [Corollary 1.3][cor:almost-every-tau] — Almost every subgraph density | [almost_every_tau](UpperTailMultipodality/FixedDensities/AlmostEvery.lean#L16) |
| [Eq. (7)][eq:entropy-identity] — The entropy identity | [entropy_identity](UpperTailMultipodality/Preliminaries/EntropyIdentity.lean#L19) |
| [Eq. (10)][eq:first-variation] — First variation of `t(H,·)` | [first_variation](UpperTailMultipodality/Preliminaries/DerivativeKernel.lean#L203), and for several directions [hasFDerivAt_tDensity_lincomb](UpperTailMultipodality/Preliminaries/Perturbation.lean#L93) |
| [Eq. (13)][eq:rooted-average] — `∫ ℛ_W(W_x) dx = N t(H,W)` | [rooted_average](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L177) |
| [Eq. (14)][eq:rooted-lipschitz] — Lipschitz bound for `ℛ_W` | [rooted_lipschitz](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L192) |
| [Eq. (15)][eq:rooted-gradient-derivative] — `∇ℛ_W(W_x) = 2𝒟_W(x,·)` | [rootedGradient_row](UpperTailMultipodality/Preliminaries/RootedDensity.lean#L206) |
| [Lemma 2.2][lem:lagrange] — Lagrange multipliers | Not used; see *Differences in proof methods* |
| [Lemma 2.3][lem:analytic-ift] — Analytic implicit function theorem | Proved inside the project: `RowCriterion/Finiteness/ImplicitFunction.lean` |
| [Example 2.1][expl:triangle-rooted] — Rooted densities of a triangle | Not formalized separately; the mechanism is [strict_supermodular](UpperTailMultipodality/RowCriterion/Basic.lean#L185) |

### The row criterion

| Paper result | Lean declaration |
|---|---|
| [Theorem 3.1][thm:row-criterion] — Finitely many row types | [row_criterion](UpperTailMultipodality/RowCriterion/Main.lean#L23) |
| [Lemma 3.2][lem:row-interior] — Interiority and Euler–Lagrange | [row_interior](UpperTailMultipodality/RowCriterion/Basic.lean#L19) |
| [Lemma 3.3][lem:strict-supermodular] — Strict supermodularity | [strict_supermodular](UpperTailMultipodality/RowCriterion/Basic.lean#L185) |
| [Proposition 3.4][prop:row-chain] — Total order | [row_chain](UpperTailMultipodality/RowCriterion/Basic.lean#L241) |
| [Lemma 3.5][lem:row-compact] — Compactness of `𝓜_W` | Replaced; see *Differences in proof methods* |
| [Lemma 3.6][lem:coercive] — Coercivity of the second variation | `RowCriterion/Finiteness/Positivity.lean` (strict positivity on mean-zero functions) |
| [Lemma 3.7][lem:bordered] — Bordered second variation | `borderedOp` and its inverse in `RowCriterion/Finiteness/Bordered.lean` |
| [Lemma 3.8][lem:row-finite] — Finiteness | [row_finite](UpperTailMultipodality/RowCriterion/Finite.lean#L27) |

### The upper-tail problem

| Paper result | Lean declaration |
|---|---|
| [Lemma 4.1][lem:upper-tail-basic] — Basic properties of minimizers | [upper_tail_basic](UpperTailMultipodality/UpperTail/Basic.lean#L19) |
| [Lemma 4.2][lem:upper-tail-multiplier] — Positive multiplier | [upper_tail_multiplier](UpperTailMultipodality/UpperTail/Basic.lean#L31) |
| [Lemma 4.3][lem:upper-tail-insertion] — Insertion inequality | [upper_tail_insertion](UpperTailMultipodality/UpperTail/Insertion.lean#L18) |

### Prescribed edge and subgraph densities

| Paper result | Lean declaration |
|---|---|
| [Lemma 5.2][lem:fixed-monotone] — Monotonicity of `Ψ_ε` | [fixed_monotone](UpperTailMultipodality/FixedDensities/Monotone.lean#L16) |
| [Lemma 5.3][lem:fixed-interior] — Interiority | [fixed_interior](UpperTailMultipodality/FixedDensities/Interior.lean#L19) |
| [Lemma 5.4][lem:fixed-multiplier] — Positive multiplier | [fixed_multiplier](UpperTailMultipodality/FixedDensities/Interior.lean#L87) |
| [Lemma 5.5][lem:fixed-insertion] — Insertion inequality | [fixed_insertion](UpperTailMultipodality/FixedDensities/Insertion.lean#L18) |
| [Lemma 5.6][lem:degenerate-forms] — Forms of a degenerate minimizer | [degenerate_forms](UpperTailMultipodality/FixedDensities/Degenerate.lean#L19) |
| [Lemma 5.7][lem:degenerate-slope] — Unbounded difference quotients | [degenerate_slope](UpperTailMultipodality/FixedDensities/Degenerate.lean#L126) |

## Axioms and dependencies

The four external results assumed as axioms are the graph-limit facts recorded
in [CutContinuity.lean](UpperTailMultipodality/Preliminaries/Graphons/CutContinuity.lean).
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
| [Theorem 1.1][thm:upper-tail] — Upper tails | — |
| [Theorem 1.2][thm:fixed-densities] — Prescribed densities | ✓ |
| [Corollary 1.3][cor:almost-every-tau] — Almost every `τ` | ✓ |
| [Theorem 3.1][thm:row-criterion] — Row criterion | — |

The cut axioms enter only through the existence of a minimizer of
[Eq. (29)][eq:fixed-problem], which the paper also obtains from compactness.
The development contains no `sorry` and no other axiom.

## Differences in proof methods

Some Lean proofs use different arguments from those in the paper.

- **Lagrange multipliers ([Lemma 2.2][lem:lagrange]).** The paper applies the
  multiplier rule in the Banach space `L^∞_sym([0,1]²)`. The Lean proofs use
  finitely many directions instead: for a bounded symmetric kernel `U`, the
  constraints are restored along one or two auxiliary directions, by an
  elementary computation for the upper-tail problem and by the two-dimensional
  implicit function theorem for prescribed densities, where the invertible matrix
  is the one of the constraint qualification. Taking `U` to be a bounded
  representative of `J_p'(W) − μ𝒟_W` then gives the Euler–Lagrange equation
  almost everywhere.
- **The insertion construction ([Lemma 4.3][lem:upper-tail-insertion],
  [Lemma 5.5][lem:fixed-insertion]).** The inserted block is described by an
  explicit measure-preserving map of `[0,1]`, which yields the exact expansion of
  `t(H,·)`, `e` and `I_p` in the block measure `θ`. Because the upper-tail
  constraint is an inequality and `Ψ_ε` is monotone, no implicit function is
  needed to keep the constraints: it suffices to move in a direction that does
  not decrease the constrained densities.
- **Compactness of `𝓜_W` ([Lemma 3.5][lem:row-compact]).** The Lean proof does
  not use it. Each row minimizer is replaced by its canonical representative
  `σ(ℓ(q) + α + (μ/2)∇ℛ_W(u))`, which satisfies the Euler–Lagrange equation
  everywhere. Since two minimizers are ordered, their `L¹` distance is the
  difference of their means, and the Lipschitz bound for `∇ℛ_W` upgrades this to
  uniform convergence. This makes the set of means closed with no weak
  compactness.
- **Coercivity ([Lemma 3.6][lem:coercive]).** Only strict positivity of the
  second variation on mean-zero functions is proved, which is what the bordered
  operator needs for injectivity. Surjectivity comes from the Fredholm
  alternative on `L²` for a compact operator, whose compactness is proved from
  scratch through an `L²` approximation of the kernel by finite sums of products.
- **The Banach space of rows.** The analytic implicit function theorem is applied
  in the space `BddMeas` of bounded measurable functions with the sup norm, not
  in `L^∞`. Point evaluation is then continuous, so the pointwise identities for
  `exp` and the logistic function are immediate; almost-everywhere classes appear
  only in the final statement.

## Scope

The appendix of the paper, which discusses two preprints of Alvarado, Ramon and
Wang, is not formalized: its statements are about the definitions of those
preprints, and two of its three propositions rest on Sard's theorem for maps
between spaces of different dimensions and on properties of semialgebraic sets,
neither of which is available in Mathlib.

<!-- Paper citations link to the corresponding source labels. -->
[thm:upper-tail]: paper/sections/intro.tex#L98
[thm:fixed-densities]: paper/sections/intro.tex#L130
[cor:almost-every-tau]: paper/sections/intro.tex#L137
[thm:row-criterion]: paper/sections/row_criterion.tex#L29
[lem:row-interior]: paper/sections/row_criterion.tex#L50
[lem:strict-supermodular]: paper/sections/row_criterion.tex#L80
[prop:row-chain]: paper/sections/row_criterion.tex#L110
[lem:row-compact]: paper/sections/row_criterion.tex#L125
[lem:coercive]: paper/sections/row_criterion.tex#L162
[lem:bordered]: paper/sections/row_criterion.tex#L187
[lem:row-finite]: paper/sections/row_criterion.tex#L217
[lem:upper-tail-basic]: paper/sections/single_constraint.tex#L16
[lem:upper-tail-multiplier]: paper/sections/single_constraint.tex#L72
[lem:upper-tail-insertion]: paper/sections/single_constraint.tex#L105
[def:constraint-qualification]: paper/sections/fixed_densities.tex#L26
[lem:fixed-monotone]: paper/sections/fixed_densities.tex#L51
[lem:fixed-interior]: paper/sections/fixed_densities.tex#L70
[lem:fixed-multiplier]: paper/sections/fixed_densities.tex#L102
[lem:fixed-insertion]: paper/sections/fixed_densities.tex#L129
[lem:degenerate-forms]: paper/sections/fixed_densities.tex#L191
[lem:degenerate-slope]: paper/sections/fixed_densities.tex#L206
[expl:triangle-rooted]: paper/sections/preliminaries.tex#L156
[lem:lagrange]: paper/sections/preliminaries.tex#L179
[lem:analytic-ift]: paper/sections/preliminaries.tex#L190
[eq:ordered-blocks]: paper/sections/preliminaries.tex#L45
[eq:entropy-identity]: paper/sections/preliminaries.tex#L76
[eq:derivative-kernel]: paper/sections/preliminaries.tex#L94
[eq:first-variation]: paper/sections/preliminaries.tex#L100
[eq:rooted-density]: paper/sections/preliminaries.tex#L113
[eq:rooted-average]: paper/sections/preliminaries.tex#L125
[eq:rooted-lipschitz]: paper/sections/preliminaries.tex#L141
[eq:rooted-gradient-derivative]: paper/sections/preliminaries.tex#L148
[eq:row-functional]: paper/sections/row_criterion.tex#L15
[eq:fixed-problem]: paper/sections/fixed_densities.tex#L8
