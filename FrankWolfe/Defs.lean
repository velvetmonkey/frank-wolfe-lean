/-
# Frank-Wolfe Algorithm — Definitions

Setting: minimise a convex L-smooth function `f` over a compact convex set `C`
in a real inner product space `E`.

The Frank-Wolfe (conditional gradient) algorithm is **projection-free**: the only
feasibility oracle is a *linear minimisation oracle* (LMO) over `C`, which is
cheap for many structured constraint sets (simplex, spectrahedron, nuclear-norm
ball, etc.).
-/
import Mathlib

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Frank-Wolfe problem setup -/

/-- Axiomatic setup for the Frank-Wolfe algorithm. -/
structure FrankWolfeSetup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  C : Set E
  f : E → ℝ
  grad_f : E → E
  L : ℝ
  D : ℝ
  hC_convex : Convex ℝ C
  hC_nonempty : C.Nonempty
  hC_compact : IsCompact C
  hL_pos : 0 < L
  hD_nonneg : 0 ≤ D
  hf_convex_grad : ∀ x ∈ C, ∀ y ∈ C,
      f x + @inner ℝ E _ (grad_f x) (y - x) ≤ f y
  hf_smooth : ∀ x ∈ C, ∀ y ∈ C,
      f y ≤ f x + @inner ℝ E _ (grad_f x) (y - x) + L / 2 * ‖y - x‖ ^ 2
  hD_diam : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D

namespace FrankWolfe

/-! ## Step size -/

/-- Step size for iteration `k`: `γ_k = 2 / (k + 2)`. -/
def stepSize (k : ℕ) : ℝ := 2 / (↑k + 2)

theorem stepSize_pos (k : ℕ) : (0 : ℝ) < stepSize k := by
  unfold stepSize
  apply div_pos (by norm_num : (0 : ℝ) < 2)
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
  linarith

theorem stepSize_le_one (k : ℕ) : stepSize k ≤ 1 := by
  unfold stepSize
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
  rw [div_le_one (by linarith)]
  linarith

theorem one_sub_stepSize_nonneg (k : ℕ) : 0 ≤ 1 - stepSize k :=
  sub_nonneg.mpr (stepSize_le_one k)

/-! ## Frank-Wolfe step -/

/-- One Frank-Wolfe step: `x_{k+1} = (1 - γ) • x + γ • s`. -/
def fwStep (x s : E) (γ : ℝ) : E := (1 - γ) • x + γ • s

end FrankWolfe

namespace FrankWolfeSetup

variable (P : FrankWolfeSetup E)

/-! ## Linear Minimisation Oracle (LMO) -/

/-- A point `s ∈ C` is an LMO response for direction `g`
if it minimises `⟪g, s⟫` over `C`. -/
def IsLMO (g : E) (s : E) : Prop :=
  s ∈ P.C ∧ ∀ y ∈ P.C, @inner ℝ E _ g s ≤ @inner ℝ E _ g y

/-- The LMO exists by compactness. -/
theorem lmo_exists (g : E) : ∃ s, P.IsLMO g s := by
  obtain ⟨s, hs_mem, hs_min⟩ := P.hC_compact.exists_isMinOn P.hC_nonempty
    (Continuous.continuousOn (Continuous.inner (𝕜 := ℝ) continuous_const continuous_id))
  exact ⟨s, hs_mem, fun y hy => hs_min hy⟩

/-- Non-computable choice of LMO response. -/
noncomputable def linearMinimisationOracle (g : E) : E :=
  (P.lmo_exists g).choose

theorem linearMinimisationOracle_spec (g : E) :
    P.IsLMO g (P.linearMinimisationOracle g) :=
  (P.lmo_exists g).choose_spec

theorem lmo_mem (g : E) : P.linearMinimisationOracle g ∈ P.C :=
  (P.linearMinimisationOracle_spec g).1

theorem lmo_le (g : E) (y : E) (hy : y ∈ P.C) :
    @inner ℝ E _ g (P.linearMinimisationOracle g) ≤ @inner ℝ E _ g y :=
  (P.linearMinimisationOracle_spec g).2 y hy

/-! ## Feasibility of the FW step -/

/-- The Frank-Wolfe step stays in `C` when `x, s ∈ C` and `γ ∈ [0,1]`. -/
theorem fwStep_mem {x s : E} (hx : x ∈ P.C) (hs : s ∈ P.C)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    FrankWolfe.fwStep x s γ ∈ P.C := by
  apply P.hC_convex hx hs (by linarith) hγ0
  ring

/-! ## Frank-Wolfe iterate sequence -/

/-- The full Frank-Wolfe iterate sequence starting from `x₀ ∈ C`. -/
noncomputable def fwIterates (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 =>
    let xk := fwIterates x₀ k
    let sk := P.linearMinimisationOracle (P.grad_f xk)
    FrankWolfe.fwStep xk sk (FrankWolfe.stepSize k)

theorem fwIterates_zero (x₀ : E) : P.fwIterates x₀ 0 = x₀ := rfl

theorem fwIterates_succ (x₀ : E) (k : ℕ) :
    P.fwIterates x₀ (k + 1) =
      FrankWolfe.fwStep (P.fwIterates x₀ k)
        (P.linearMinimisationOracle (P.grad_f (P.fwIterates x₀ k)))
        (FrankWolfe.stepSize k) := rfl

/-- Every iterate stays in `C`. -/
theorem fwIterates_mem (x₀ : E) (hx₀ : x₀ ∈ P.C) : ∀ k, P.fwIterates x₀ k ∈ P.C := by
  intro k
  induction k with
  | zero => exact hx₀
  | succ k ih =>
    simp only [fwIterates_succ]
    exact P.fwStep_mem ih (P.lmo_mem _) (le_of_lt (FrankWolfe.stepSize_pos k))
      (FrankWolfe.stepSize_le_one k)

end FrankWolfeSetup

end
