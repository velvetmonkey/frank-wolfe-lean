/-
# Frank-Wolfe Gap

The Frank-Wolfe gap `g_k = ⟪∇f(x_k), x_k − s_k⟫` is the key progress measure.
It is always nonneg and vanishes only at optimality.
-/
import FrankWolfe.Defs

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FrankWolfeSetup

variable (P : FrankWolfeSetup E)

/-! ## Definition of the FW gap -/

/-- The Frank-Wolfe gap at `x` with LMO response `s`:
  `⟪∇f(x), x − s⟫`. -/
def fwGap (x s : E) : ℝ := @inner ℝ E _ (P.grad_f x) (x - s)

/-- FW gap at the `k`-th iterate. -/
noncomputable def fwGapAt (x₀ : E) (k : ℕ) : ℝ :=
  P.fwGap (P.fwIterates x₀ k) (P.linearMinimisationOracle (P.grad_f (P.fwIterates x₀ k)))

/-! ## Gap is nonneg -/

/-- The FW gap is nonneg: since `s` minimises `⟪g, ·⟫` over `C` and `x ∈ C`,
we have `⟪g, s⟫ ≤ ⟪g, x⟫`, so `⟪g, x − s⟫ ≥ 0`. -/
theorem fw_gap_nonneg {x s : E} (hx : x ∈ P.C) (hs : P.IsLMO (P.grad_f x) s) :
    0 ≤ P.fwGap x s := by
  unfold fwGap
  rw [inner_sub_right]
  linarith [hs.2 x hx]

/-- The FW gap at every iterate is nonneg. -/
theorem fwGapAt_nonneg (x₀ : E) (hx₀ : x₀ ∈ P.C) (k : ℕ) :
    0 ≤ P.fwGapAt x₀ k :=
  P.fw_gap_nonneg (P.fwIterates_mem x₀ hx₀ k) (P.linearMinimisationOracle_spec _)

/-! ## Gap bounds the suboptimality -/

/-- The FW gap upper-bounds the suboptimality: for any `y ∈ C`,
  `f(x) − f(y) ≤ fwGap x s`. -/
theorem fw_gap_bounds_subopt {x s : E} (hx : x ∈ P.C) (hs : P.IsLMO (P.grad_f x) s)
    {y : E} (hy : y ∈ P.C) : P.f x - P.f y ≤ P.fwGap x s := by
  unfold fwGap
  rw [inner_sub_right]
  have h1 := P.hf_convex_grad x hx y hy
  rw [inner_sub_right] at h1
  have h2 := hs.2 y hy
  linarith

/-! ## Gap = 0 implies optimality -/

/-- If the FW gap vanishes then `x` is a global minimiser of `f` over `C`. -/
theorem fw_gap_optimality {x s : E} (hx : x ∈ P.C) (hs : P.IsLMO (P.grad_f x) s)
    (hgap : P.fwGap x s = 0) : ∀ y ∈ P.C, P.f x ≤ P.f y := by
  intro y hy
  have := P.fw_gap_bounds_subopt hx hs hy
  linarith

end FrankWolfeSetup

end
