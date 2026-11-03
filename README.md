# Lean formalization of *Ordered multipodal structure of optimizers in the upper-tail variational problem*

This repository formalizes in Lean 4 and Mathlib the graphon results of
Sangho Lim, Seonghyuk Im, Taeyoung Kim, Kyeongsik Nam, and Hongseok Yang,
*Ordered multipodal structure of optimizers in the upper-tail variational problem*.
Its LaTeX source is also included in this repository, as [paper/paper.tex](paper/paper.tex).

## Main results

Each row identifies the main Lean declaration for a result in the paper. Paper
citations and Lean declarations link directly to their source lines. Declaration
names are relative to the namespace `UpperTailMultipodality`.

| Paper result | Lean declaration |
|---|---|
| [Theorem 1.1][thm:joint-upper-tail] — Every minimizer under finitely many upper-tail constraints is multipodal, with ordered blocks | Multipodality and ordering: [joint_upper_tail](UpperTailMultipodality/UpperTail/Joint/Main.lean#L32); for one constraint: [upper_tail](UpperTailMultipodality/UpperTail/Main.lean#L24) |
| [Theorem 1.2][thm:fixed-densities] — Entropy maximizers at fixed edge and subgraph densities | Multipodality and ordering at every density: [fixed_densities](UpperTailMultipodality/FixedDensities/Main.lean#L111) |

## Assumptions

The proofs use four axioms, together with Lean's foundational axioms
`propext`, `Classical.choice` and `Quot.sound`.

| Axiom | Assumed result |
|---|---|
| `cut_seqCompact` | Sequential compactness in cut distance |
| `edgeDensity_cutContinuous` | Continuity of edge density under cut convergence |
| `tDensity_cutContinuous` | Continuity of homomorphism densities under cut convergence |
| `Ip_cut_lowerSemicontinuous` | Lower semicontinuity of relative entropy under cut convergence |

These four standard facts of dense graph-limit theory are used only where the
paper uses them: to know that the entropy-maximization problem has a solution.
[Theorem 1.1][thm:joint-upper-tail] does not use them, and depends on the
foundational axioms only.
Some proofs use different arguments from the paper; they are described in
[FORMALIZATION.md](FORMALIZATION.md), which also says why Appendix A is outside the
formalization.

## Build

The project pins Lean to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). With `~/.elan/bin`
on `PATH`, run these commands from the repository root:

```sh
lake exe cache get
lake build
```

The first command downloads compiled Mathlib files. Keep `lake-manifest.json`
unchanged to reproduce the pinned dependencies.

After building, inspect a theorem's assumptions with `#print axioms`:

```sh
lake env lean --stdin <<'EOF'
import UpperTailMultipodality
#print axioms UpperTailMultipodality.joint_upper_tail
#print axioms UpperTailMultipodality.fixed_densities
EOF
```

The output lists the theorem's project and foundational axioms; `sorryAx` would
indicate an unproved placeholder. There is none: the development contains no
`sorry`.

For definitions, the proof overview, detailed theorem correspondence and exact
assumptions, read [FORMALIZATION.md](FORMALIZATION.md).

<!-- Paper citations link to the corresponding source labels. -->
[thm:joint-upper-tail]: paper/sections/intro.tex#L167
[thm:fixed-densities]: paper/sections/intro.tex#L264