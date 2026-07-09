# frank-wolfe-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](FrankWolfe)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20478157.svg)](https://doi.org/10.5281/zenodo.20478157)

**frank-wolfe-lean: Formal Proofs of Frank-Wolfe Convergence in Lean 4**

Lean 4 formal proofs for the Frank-Wolfe, or conditional gradient, method for constrained convex optimisation. The development covers the linear minimisation oracle, the Frank-Wolfe gap, the per-step descent lemma, and an O(1/k) convergence rate.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Frank-Wolfe is a projection-free first-order method for constrained convex optimisation. Instead of projecting onto the feasible region after a gradient step, each iteration calls a **linear minimisation oracle** over the constraint set. This makes the method useful for structured feasible regions where linear optimisation is cheaper than projection.

This library machine-checks the core deterministic convergence argument in Lean 4.

## Setting

A real inner product space `E`, a compact convex nonempty feasible set `C`, a convex objective `f : E -> ℝ`, an abstract gradient map `grad_f`, smoothness constant `L`, and diameter bound `D`.

The linear minimisation oracle chooses `s in C` minimising:

```text
<grad_f x, s>
```

The Frank-Wolfe update is:

```text
x_{k+1} = (1 - gamma_k) x_k + gamma_k s_k
```

with `gamma_k = 2 / (k + 2)`.

## Main result

For an optimal point `xstar in C`, the main theorem proves:

```text
f(x_{k+1}) - f(xstar) <= 2 * L * D^2 / (k + 3)
```

This is the standard O(1/k) convergence rate for Frank-Wolfe under the stated axioms.

## Project structure

```text
FrankWolfe/
├── Defs.lean        — problem setup, linear minimisation oracle, step size,
│                      Frank-Wolfe step, iterate feasibility
├── FWGap.lean       — Frank-Wolfe gap, nonnegativity, suboptimality bound,
│                      optimality certificate
├── Descent.lean     — step displacement identities, norm bound, per-step
│                      descent lemma
└── Convergence.lean — suboptimality recurrence, gap-sum bound, first-iterate
                       bound, O(1/k) convergence theorem
FrankWolfe.lean      — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `stepSize_pos` | `0 < stepSize k` |
| 2 | `stepSize_le_one` | `stepSize k <= 1` |
| 3 | `fwStep_mem` | The Frank-Wolfe convex-combination step remains in `C` |
| 4 | `fwIterates_mem` | Every Frank-Wolfe iterate remains feasible |
| 5 | `fw_gap_nonneg` | The Frank-Wolfe gap is nonnegative |
| 6 | `fw_gap_bounds_subopt` | The Frank-Wolfe gap upper-bounds suboptimality over `C` |
| 7 | `fw_gap_optimality` | Zero Frank-Wolfe gap implies global optimality over `C` |
| 8 | `fw_descent_lemma` | Per-step descent bound |
| 9 | `fw_subopt_recurrence` | One-step recurrence for suboptimality |
| 10 | `fw_gap_sum_bound` | Telescoping sum bound over Frank-Wolfe gaps |
| 11 | `fw_first_iterate_bound` | First-iterate suboptimality bound |
| 12 | `frank_wolfe_convergence` | O(1/k) convergence rate |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [projected-gd-lean](https://github.com/velvetmonkey/projected-gd-lean) — Lean 4 projected gradient descent onto convex sets
- [sgd-lean](https://github.com/velvetmonkey/sgd-lean) — Lean 4 bounded-noise SGD convergence
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
