/-
# Frank-Wolfe Descent Lemma

Per-step bound:
  `f(x_{k+1}) ≤ f(x_k) − γ_k · g_k + (γ_k² · L / 2) · D²`
-/
import FrankWolfe.FWGap

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FrankWolfeSetup

variable (P : FrankWolfeSetup E)

/-! ## Auxiliary: the FW step as a displacement -/

set_option linter.unusedSectionVars false in
/-- `fwStep x s γ − x = γ • (s − x)`. -/
theorem fw_step_sub (x s : E) (γ : ℝ) :
    FrankWolfe.fwStep x s γ - x = γ • (s - x) := by
  simp [FrankWolfe.fwStep, smul_sub, sub_smul]
  abel

/-- Rewrite the inner product in terms of the gap. -/
theorem inner_grad_fw_step (x s : E) (γ : ℝ) :
    @inner ℝ E _ (P.grad_f x) (FrankWolfe.fwStep x s γ - x) =
      -(γ * P.fwGap x s) := by
  rw [fw_step_sub]
  rw [real_inner_smul_right]
  unfold fwGap
  rw [inner_sub_right, inner_sub_right]
  ring

/-! ## Norm bound on the step -/

/-- `‖fwStep x s γ − x‖² ≤ γ² D²` when `x, s ∈ C`. -/
theorem fw_step_norm_sq_le {x s : E} (hx : x ∈ P.C) (hs : s ∈ P.C) (γ : ℝ) :
    ‖FrankWolfe.fwStep x s γ - x‖ ^ 2 ≤ γ ^ 2 * P.D ^ 2 := by
  rw [fw_step_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg γ)
  apply sq_le_sq'
  · have := norm_nonneg (s - x)
    linarith [P.hD_nonneg]
  · rw [norm_sub_rev]
    exact P.hD_diam x hx s hs

/-! ## Descent lemma -/

/-
**Per-step descent lemma.**

  `f(x_{k+1}) ≤ f(x_k) − γ · g_k + γ² · (L / 2) · D²`

Uses L-smoothness applied to `y = fwStep x s γ` and `x`.
-/
theorem fw_descent_lemma {x s : E} (hx : x ∈ P.C) (hs : s ∈ P.C)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    P.f (FrankWolfe.fwStep x s γ) ≤
      P.f x - γ * P.fwGap x s + γ ^ 2 * (P.L / 2) * P.D ^ 2 := by
  have := P.hf_smooth x hx ( FrankWolfe.fwStep x s γ ) ( P.fwStep_mem hx hs hγ0 hγ1 );
  convert this.trans _ using 1;
  rw [ FrankWolfeSetup.inner_grad_fw_step ] ; nlinarith [ P.hL_pos, P.fw_step_norm_sq_le hx hs γ ]

end FrankWolfeSetup

end
