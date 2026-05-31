/-
# Frank-Wolfe (Conditional Gradient) Algorithm — Lean 4 / Mathlib Library

A projection-free optimisation library. The Linear Minimisation Oracle (LMO)
replaces projection as the only feasibility oracle, making the algorithm
cheap for structured constraint sets (simplex, spectrahedron, nuclear-norm
ball, etc.).

## Module structure

* `Defs`         — problem setup, LMO, iterate sequence
* `FWGap`        — gap definition, nonnegativity, optimality certificate
* `Descent`      — per-step descent bound
* `Convergence`  — O(1/k) convergence: f(x_{k+1}) − f* ≤ 2LD²/(k+3)
-/

import FrankWolfe.Defs
import FrankWolfe.FWGap
import FrankWolfe.Descent
import FrankWolfe.Convergence
