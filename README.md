# Lean 4 formalization: continuous-time modified-gradient stability

[![DOI](https://img.shields.io/badge/DOI-10.1080%2F17513758.2017.1400598-blue.svg)](https://doi.org/10.1080/17513758.2017.1400598)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24232214.svg)](https://doi.org/10.5281/zenodo.24232214)
[![Lean build](https://github.com/magbenji/continuous-modified-gradient-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/magbenji/continuous-modified-gradient-lean/actions/workflows/lean_action_ci.yml)

Machine-checked proofs (Lean 4 + Mathlib) of the results of the paper
*Stability of equilibria in quantitative genetic models based on modified-gradient systems* by
B. J. Ridenhour and J. R. Ridenhour, Journal of Biological Dynamics 12(1):39–50, 2018
([doi:10.1080/17513758.2017.1400598](https://doi.org/10.1080/17513758.2017.1400598)).
Section, theorem and example numbers below refer to that paper. Every theorem below compiles
with no `sorry` and depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

The discrete-time companion, for the multivariate breeder's equation
`x_{k+1} = x_k + P_k ∇f(x_k)`, is
[discrete-modified-gradient-lean](https://github.com/magbenji/discrete-modified-gradient-lean).

| Paper | Lean name | File |
|---|---|---|
| (TD) trajectory derivative | `trajectory_deriv` | `ContinuousStability/Lyapunov.lean` |
| `V = M - f` is a Lyapunov function | `ascent`, `ascent_weighted` | `Lyapunov.lean` |
| Theorem 2.1(i) | `stable` (and `stable_on`, see below) | `ContinuousStability/Stability.lean` |
| Theorem 2.1(ii) | `asympStable` | `Stability.lean` |
| Example 2.1 | `Example21.stable`, `Example21.not_eigenvalueCondition`, `Example21.not_asympStable` | `ContinuousStability/Examples.lean` |
| Example 2.2 (the mechanism) | `not_asympStable_of_crit_accum` | `Examples.lean` |
| Theorem 3.1, `O_{c,x̄}` is open | `isOpen_Oc`, `isOpen_Ec` | `ContinuousStability/Basin.lean` |
| Theorem 3.1 | `basin_Ec` (and `basin`, for any set with the properties of `E_{c,x̄}`) | `Basin.lean` |

## Dependency graph

An arrow from A to B means the proof of A cites B. The paper's results are highlighted, and
boxes are grouped by file. Definitions and hypotheses (`EigBound`, `LocalHyp`, `IsSolution`, ...)
and Mathlib lemmas are left out.
The [interactive version](https://magbenji.github.io/continuous-modified-gradient-lean/) lets you
click a declaration to trace what it depends on and what depends on it, optionally shows the
definitions too, and lists every declaration with links to its source line.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/dependency-graph-dark.svg">
  <img alt="Dependency graph of the Lean declarations" src="docs/dependency-graph.svg">
</picture>

The trajectory derivative (TD) (`trajectory_deriv`) underlies every result. Theorem 2.1(i) and
(ii) go through the trapping lemma `trap`, Theorem 3.1 goes through the invariance lemma
`basin_invariant`, and both use the first-exit-time argument `first_exit`. Theorem 2.1(ii) and
Theorem 3.1 share the convergence argument `tendsto_of_weighted_ascent`.
`ascent_weighted` (the integrated form of `V_x' ≤ -m λ₁(P(t))`) is proved for completeness; the
convergence argument proves the same inequality inline, so it has no users inside the project.

Both versions are generated from the source by `python3 scripts/dependency_graph.py`
(requires Graphviz). It writes the static images and their Graphviz source
(`docs/dependency-graph.dot`) and the interactive page `docs/index.html`, which GitHub Pages
serves from the `docs/` folder.

## How the paper's hypotheses are encoded

* **Space.** A real inner product space `E` (for example `EuclideanSpace ℝ (Fin n)`).
  Theorems 2.1 and 3.1 assume `[FiniteDimensional ℝ E]` so that closed bounded sets are compact.
* **Gradient.** `f : E → ℝ` with gradient `g : E → E`, written
  `HasFDerivAt f (innerSL ℝ (g z)) z` (that is, `Df(z) h = ⟪g z, h⟫`), with `g` continuous.
* **The matrices `P(t)`.** `P t : E →L[ℝ] E` together with `EigBound (P t) (lo t)` for `t ≥ 0`.
  This says `lo t ‖u‖² ≤ ⟪P t u, u⟫` with `0 ≤ lo t`. For a symmetric matrix this means exactly
  `lo t ≤ λ₁(P(t))`. Taking `lo t = λ₁(P(t))` gives the paper's statements; any weaker lower
  bound also works, and `lo = 0` says that `P(t)` is positive semi-definite.
* **The system (E).** `IsSolution P g t₀ x` means that `x' = P(t) ∇f(x)` on `[t₀, ∞)`, in the
  sense of Mathlib's `IsIntegralCurveOn x (fun t z => P t (g z)) (Ici t₀)`.
  `IsSolutionOn P g I x` is the same on any time interval `I`.
* **Hypotheses H0–H6.**
  * H0 is `LocalHyp f g x̄ r₀` (gradient and its continuity on a closed ball) for Theorem 2.1,
    and the corresponding conditions on an open set `D` for Theorem 3.1.
  * H1 is `IsolatedMax f x̄`.
  * H2 is `IsolatedCrit g x̄`.
  * H3, the eigenvalue condition (EC), is `EigenvalueCondition lo`:
    `Tendsto (fun T => ∫ t in 0..T, lo t) atTop atTop`, for a continuous `lo`.
  * H4 is `Bornology.IsBounded (Ec f D c x̄)` and `closure (Ec f D c x̄) ⊆ D`.
  * H5 is `∀ y ∈ frontier (Ec f D c x̄), f y = c`.
  * H6 is `∀ y ∈ closure (Ec f D c x̄), y ≠ x̄ → g y ≠ 0`.
* **Stability.** `UniformlyStable` and `UniformlyAsympStable` are the paper's (Hartman's)
  definitions with `t_ε = 0`, so `δ` does not depend on the starting time `t₀ ≥ 0`.
* **Theorem 3.1.** `Oc f D c x̄` is `{x̄} ∪ {x ∈ D : c < f(x) < f(x̄)}` and `Ec f D c x̄` is its
  connected component containing `x̄` (`connectedComponentIn`). `basin_Ec` is the paper's
  statement. It is derived from `basin`, which holds for any open set `U ∋ x̄` with the
  properties of `E_{c,x̄}` that the proof uses: `c < f` on `U`, `f < f(x̄)` on `U \ {x̄}`,
  `closure U` compact (H4), H5, H6 and H3.

### Small differences from the written proofs

* **Existence of solutions for all `t ≥ t₀`.** The paper uses H0 (`C¹` data) for existence and
  uniqueness, and Hartman's continuation theorem (Thm. II.3.1) to show that solutions that stay
  in a compact set exist for all `t ≥ t₀`. Mathlib has local existence (Picard–Lindelöf) but no
  continuation theorem, so the stability definitions quantify over solutions that exist on
  `[t₀, ∞)`. The a priori bounds that feed the continuation theorem are proved for a solution on
  any interval `I = [t₀, ω)`: `stable_on` (it stays in `B_ε(x̄)`) and `basin_invariant` (it stays
  in `E_{c,x̄}`).
* **Fewer hypotheses.** The Lean proofs never use uniqueness of solutions (the paper's step
  "we can assume `x(t) ≠ x̄`" is not needed), the symmetry of `P(t)`, the continuity of `P`, or
  the `C¹` smoothness of `∇f`. They use only that `f` has a continuous gradient on the relevant
  set and the lower bound `lo t ≤ λ₁(P(t))`, with `lo` continuous.
* **Theorems 2.1(i) and 3.1, trapping.** The paper argues that a solution "can never reach" the
  sphere `|x - x̄| = r` (respectively `∂E_{c,x̄}`). The Lean proof takes the first exit time
  `s = inf {t ≥ t₀ : x(t) ∉ U}` (`first_exit`), shows `x(s) ∈ ∂U`, and applies the monotonicity
  of `f ∘ x` on `[t₀, s]`. Theorem 2.1(i) uses `U = B_ρ(x̄)` with `ρ = min(ε, r₀, r₁)`.
* **Theorem 2.1(ii) and 3.1, convergence.** Instead of writing
  `V_x(t) = V_x(t₀) + ∫ V_x'`, the Lean proof shows that `f(x(t)) - m₁ ∫₀ᵗ λ₁` is nondecreasing.
  This argument, common to both theorems, is proved once, as `tendsto_of_weighted_ascent`.
* **Example 2.1.** `Example21.eigBound` and `Example21.eigBound_le` show that `(t+1)⁻²` is the
  best lower bound for `P(t)`, i.e. `λ₁(P(t)) = (t+1)⁻²`. `Example21.not_eigenvalueCondition`
  computes `∫₀ᵀ (t+1)⁻² dt = 1 - (T+1)⁻¹`, and `Example21.not_asympStable` uses the solutions
  `x(t) = (1 + c₁ e^{2/(t+1)}, 1)`.
* **Example 2.2.** The radially symmetric cubic spline is not formalized. What it demonstrates
  is proved in general: if critical points `y ≠ x̄` accumulate at `x̄` (H2 fails), then the
  constant solutions `x(t) ≡ y` show that `x̄` is not asymptotically stable, for any `P(t)`.

## Checking that it compiles

You need `elan`, the Lean version manager. Install it once on macOS or Linux with:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Then restart the terminal. Alternatively, install the **Lean 4** extension in VS Code, which
offers to install elan for you.

Clone the repository and build:

```bash
git clone https://github.com/magbenji/continuous-modified-gradient-lean.git
cd continuous-modified-gradient-lean
lake exe cache get            # downloads prebuilt Mathlib (a few GB, a few minutes)
lake build                    # compiles the five files
```

`lake build` should end with `Build completed successfully`. Lean prints
`declaration uses 'sorry'` for any unfinished proof, and there are none.

To list the axioms each main theorem relies on, run:

```bash
lake env lean Axioms.lean
```

Each line should read `depends on axioms: [propext, Classical.choice, Quot.sound]`.

The first `lake` command downloads the exact Lean version pinned in `lean-toolchain`
(`v4.35.0`) and the Mathlib commit pinned in `lake-manifest.json` (the same pins as the
discrete-time project). If you skip `lake exe cache get`, `lake build` compiles about 3,000
Mathlib files from source, which takes an hour or more.

To read the proofs interactively, open this folder in VS Code with the Lean 4 extension. Then
click inside any proof to see the goal state.

The GitHub Actions workflow in `.github/workflows/` runs the same build and axiom check on every
push; the badge at the top shows its latest result.

## Citation and license

If you use this code, please cite the paper (see `CITATION.cff`):

> B. J. Ridenhour and J. R. Ridenhour, Stability of equilibria in quantitative genetic models
> based on modified-gradient systems, Journal of Biological Dynamics 12(1) (2018), 39–50.
> https://doi.org/10.1080/17513758.2017.1400598

To cite the code itself, use the Zenodo archive: https://doi.org/10.5281/zenodo.24232214.

The code is released under the
Apache License 2.0 (see `LICENSE`), the same license as Mathlib.
