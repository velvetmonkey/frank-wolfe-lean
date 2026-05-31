/-
# Frank-Wolfe Convergence

**Main result:** `f(x_{k+1}) − f* ≤ 2 L D² / (k + 3)` for all `k ≥ 0`.

Equivalently, `f(x_n) − f* ≤ 2 L D² / (n + 2)` for `n ≥ 1`.
-/
import FrankWolfe.Descent

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FrankWolfeSetup

variable (P : FrankWolfeSetup E)

/-! ## Per-step recurrence -/

/-- One-step recurrence for the suboptimality `h_k = f(x_k) − f*`:

  `h_{k+1} ≤ (1 − γ_k) · h_k + γ_k² · (L / 2) · D²`

Uses the descent lemma and the fact that `g_k ≥ h_k`. -/
theorem fw_subopt_recurrence (x₀ : E) (hx₀ : x₀ ∈ P.C)
    {xstar : E} (hxstar : xstar ∈ P.C) (_hopt : ∀ y ∈ P.C, P.f xstar ≤ P.f y)
    (k : ℕ) :
    P.f (P.fwIterates x₀ (k + 1)) - P.f xstar ≤
      (1 - FrankWolfe.stepSize k) * (P.f (P.fwIterates x₀ k) - P.f xstar) +
        FrankWolfe.stepSize k ^ 2 * (P.L / 2) * P.D ^ 2 := by
  have h_f_step : P.f (P.fwIterates x₀ (k + 1)) ≤ P.f (P.fwIterates x₀ k) - FrankWolfe.stepSize k * P.fwGap (P.fwIterates x₀ k) (P.linearMinimisationOracle (P.grad_f (P.fwIterates x₀ k))) + (FrankWolfe.stepSize k)^2 * (P.L / 2) * P.D^2 := by
    apply_rules [ FrankWolfeSetup.fw_descent_lemma ]
    · exact P.fwIterates_mem x₀ hx₀ k
    · exact P.lmo_mem _
    · exact div_nonneg zero_le_two ( by positivity )
    · exact FrankWolfe.stepSize_le_one k
  have := P.fw_gap_bounds_subopt ( P.fwIterates_mem x₀ hx₀ k ) ( P.linearMinimisationOracle_spec ( P.grad_f ( P.fwIterates x₀ k ) ) ) hxstar
  nlinarith [ show 0 ≤ FrankWolfe.stepSize k from by exact div_nonneg zero_le_two ( by positivity ) ]

/-! ## Telescoping sum over gaps -/

/-- **Gap-sum bound.** Telescoping the descent lemma. -/
theorem fw_gap_sum_bound (x₀ : E) (hx₀ : x₀ ∈ P.C) (n : ℕ) :
    P.f (P.fwIterates x₀ (n + 1)) - P.f x₀ ≤
      - Finset.sum (Finset.range (n + 1)) (fun i => FrankWolfe.stepSize i * P.fwGapAt x₀ i) +
        P.L / 2 * P.D ^ 2 *
          Finset.sum (Finset.range (n + 1)) (fun i => FrankWolfe.stepSize i ^ 2) := by
  induction' n with n ih
  · have := FrankWolfeSetup.fw_descent_lemma P hx₀ ( FrankWolfeSetup.lmo_mem P ( P.grad_f x₀ ) ) ( FrankWolfe.stepSize_pos 0 |> le_of_lt ) ( FrankWolfe.stepSize_le_one 0 )
    convert sub_le_sub_right this ( P.f x₀ ) using 1 ; norm_num [ FrankWolfeSetup.fwIterates_succ, FrankWolfeSetup.fwGapAt ] ; ring!
  · have h_step : P.f (P.fwIterates x₀ (n + 2)) - P.f (P.fwIterates x₀ (n + 1)) ≤ -FrankWolfe.stepSize (n + 1) * P.fwGapAt x₀ (n + 1) + FrankWolfe.stepSize (n + 1) ^ 2 * (P.L / 2) * P.D ^ 2 := by
      convert sub_le_sub_right ( P.fw_descent_lemma _ _ _ _ ) ( P.f ( P.fwIterates x₀ ( n + 1 ) ) ) using 1 <;> ring_nf!
      · rw [ add_comm ] ; exact P.fwIterates_mem x₀ hx₀ _
      · exact P.lmo_mem _
      · exact div_nonneg zero_le_two ( by positivity )
      · exact FrankWolfe.stepSize_le_one _
    norm_num [ Finset.sum_range_succ ] at * ; linarith

/-! ## Base case: first iterate bound -/

/-
After one FW step with γ₀ = 1, the suboptimality drops to at most `L D² / 2`.
-/
theorem fw_first_iterate_bound (x₀ : E) (hx₀ : x₀ ∈ P.C)
    {xstar : E} (hxstar : xstar ∈ P.C) (hopt : ∀ y ∈ P.C, P.f xstar ≤ P.f y) :
    P.f (P.fwIterates x₀ 1) - P.f xstar ≤ P.L / 2 * P.D ^ 2 := by
  convert P.fw_subopt_recurrence x₀ hx₀ hxstar hopt 0 using 1 ; norm_num [ FrankWolfeSetup.fwIterates ];
  norm_num [ FrankWolfe.stepSize ]

/-! ## Arithmetic helper -/

/-- Key arithmetic fact: `(k+1)*(k+3) ≤ (k+2)^2`. -/
theorem nat_ineq (k : ℕ) : (↑k + 1) * (↑k + 3) ≤ ((↑k : ℝ) + 2) ^ 2 := by
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-! ## Main convergence theorem -/

/-
**O(1/k) convergence of Frank-Wolfe.**

  `f(x_{k+1}) − f* ≤ 2 · L · D² / (k + 3)`

for all `k ≥ 0`, where `γ_k = 2/(k+2)`. Equivalently, for all `n ≥ 1`,
`f(x_n) − f* ≤ 2LD²/(n+2)`.
-/
theorem frank_wolfe_convergence (x₀ : E) (hx₀ : x₀ ∈ P.C)
    {xstar : E} (hxstar : xstar ∈ P.C) (hopt : ∀ y ∈ P.C, P.f xstar ≤ P.f y)
    (k : ℕ) :
    P.f (P.fwIterates x₀ (k + 1)) - P.f xstar ≤
      2 * P.L * P.D ^ 2 / (↑k + 3) := by
  induction' k with k ih;
  · convert P.fw_first_iterate_bound x₀ hx₀ hxstar hopt |> le_trans <| ?_ using 1 ; ring_nf;
    exact mul_le_mul_of_nonneg_left ( by norm_num ) ( mul_nonneg P.hL_pos.le ( sq_nonneg _ ) );
  · refine' le_trans ( P.fw_subopt_recurrence x₀ hx₀ hxstar hopt _ ) _;
    norm_num [ FrankWolfe.stepSize ] at *;
    field_simp;
    rw [ div_add', le_div_iff₀ ] at ih <;> nlinarith [ sq ( k : ℝ ), P.hL_pos, P.hD_nonneg ]

end FrankWolfeSetup

end
