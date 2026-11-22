import QuantumQueryComplexity.Quantum.AlphabetPolynomialMethod
import QuantumQueryComplexity.Polynomial.IntegerGrid
import QuantumQueryComplexity.LearningGraph.BlockSys

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: the alphabet polynomial method, its approximation theory, block arc systems

Checks for `Quantum/AlphabetPolynomialMethod.lean`, `Polynomial/Markov.lean`,
`Polynomial/IntegerGrid.lean` and `LearningGraph/BlockSys.lean`.

1. **One-hot points**: each row of `oneHot a` has exactly one `true`.
2. **A worked obstruction over an alphabet**: no constant approximates the indicator
   `[a i = j₁]` within `ε < 1/2`, hence `1 ≤ Q_ε` from the alphabet polynomial method alone.
3. **Markov is sharp at the endpoint**: `T₂ = 2X² - 1` is bounded by `1` on `[-1, 1]` and has
   `T₂'(1) = 4 = 2²`, the bound of `abs_derivative_eval_one_le`.
4. **Instances of the derivative and grid lemmas**, including a cubic that vanishes at the grid
   `0, 1, 2` and has a bump of size `6` at `3/2` (so the centre lemma's hypotheses are met by a
   genuine bump, not vacuously).
5. **A block arc system with a nontrivial observation map**: one bit of a promise read through
   `read x = fun _ => x`, one block, one path, dual cost `1` from `hasDualOn_of_paths`.

Axioms are checked by `Test/PolynomialAxioms.lean` (items 1–4) and `Test/AdversaryAxioms.lean`
(the module `LearningGraph/BlockSys`).
-/

namespace QuantumQueryComplexity
namespace AlphabetPolynomialAcceptance

open Polynomial

/-! ## 1. One-hot points -/

/-- Each row of a one-hot point has exactly one `true`. -/
theorem sum_bit_oneHot_row {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (a : ι → σ) (i : ι) : ∑ j : σ, bit (oneHot a (i, j)) = 1 := by
  rw [Finset.sum_eq_single (a i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-! ## 2. A worked obstruction over an alphabet -/

/-- No constant is within `ε < 1/2` of both values of the indicator `[a i = j₁]`. -/
theorem oneHotObstruction_indicator_zero {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] (i : ι) {j₀ j₁ : σ} (hj : j₀ ≠ j₁) {ε : ℝ} (hε : ε < 1 / 2) :
    OneHotPolyObstructionOn (id : (ι → σ) → ι → σ) (fun a => decide (a i = j₁)) ε 0 := by
  intro p hdeg _ happ
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
  have h0 := happ (fun _ => j₀)
  have h1 := happ (fun _ => j₁)
  rw [hC] at h0 h1
  simp only [id, evalBool_C, hj, decide_false, decide_true, bit_true, bit_false,
    sub_zero] at h0 h1
  rw [abs_le] at h0 h1
  linarith [h0.2, h1.1]

/-- `1 ≤ Q_ε([a i = j₁])` for every `0 ≤ ε < 1/2`, from the alphabet polynomial method. -/
example {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (i : ι)
    {j₀ j₁ : σ} (hj : j₀ ≠ j₁) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    1 ≤ qQueryOn (id : (ι → σ) → ι → σ) (fun a => decide (a i = j₁)) ε := by
  have h := lt_two_mul_qQueryOn_oneHot_of_det
    (fun _ _ h => congrArg (fun a : ι → σ => decide (a i = j₁)) h) hε0
    (oneHotObstruction_indicator_zero i hj hε)
  exact Nat.pos_of_mul_pos_left h

/-! ## 3. Markov is sharp at the endpoint -/

/-- `T₂ = 2X² - 1` meets the hypotheses of the endpoint Markov inequality with `d = 2`. -/
example : |(2 * X ^ 2 - 1 : ℝ[X]).derivative.eval 1| ≤ ((2 : ℕ) : ℝ) ^ 2 := by
  refine abs_derivative_eval_one_le ?_ fun x hx => ?_
  · compute_degree!
  · simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2]

/-- …and attains it: `T₂'(1) = 4`. -/
example : (2 * X ^ 2 - 1 : ℝ[X]).derivative.eval 1 = 4 := by
  simp only [derivative_sub, derivative_mul, derivative_X_pow, derivative_one, derivative_ofNat,
    eval_sub, eval_add, eval_mul, eval_ofNat, eval_C, eval_pow, eval_X, eval_zero, zero_mul]
  norm_num

/-! ## 4. Instances of the derivative and grid lemmas -/

/-- Markov on `[0, 2]` for `X²`: `|p'(1)| ≤ 4 · 2² · 4 / 2`. -/
example : |(X ^ 2 : ℝ[X]).derivative.eval 1| ≤ 4 * ((2 : ℕ) : ℝ) ^ 2 * 4 / (2 - 0) := by
  refine abs_derivative_eval_le_markov (by compute_degree!) (by norm_num) (fun x hx => ?_)
    ⟨by norm_num, by norm_num⟩
  simp only [eval_pow, eval_X]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [hx.1, hx.2]

/-- Bernstein at the centre for `X` on `[-1, 1]`: `|p'(0)| ≤ 3`. -/
example : |(X : ℝ[X]).derivative.eval 0| ≤ 3 * ((1 : ℕ) : ℝ) * 1 / 1 := by
  refine abs_derivative_eval_le_bernstein (by simp) one_pos fun x hx => ?_
  simp only [eval_X]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- The cubic `16 x (x - 1)(x - 2)` vanishes on the grid `0, 1, 2`. -/
private lemma cubic_grid (i : ℕ) (hi : i ≤ 2) :
    |(16 * X * (X - 1) * (X - 2) : ℝ[X]).eval (i : ℝ)| ≤ 1 := by
  interval_cases i <;> norm_num

/-- …and has a bump of size `6` at `3/2`, within `2` of the centre `1`: the centre lemma's
hypotheses hold for a genuine bump, and its conclusion `2 ≤ 2000 · deg` follows. -/
example : ((2 : ℕ) : ℝ) ≤ 2000 * (16 * X * (X - 1) * (X - 2) : ℝ[X]).natDegree := by
  refine natDegree_ge_of_center_bump (ξ := 3 / 2) cubic_grid ?_ ?_
  · norm_num
  · norm_num

/-- The endpoint lemma for `X` on the grid `1, …, 5` (`B = 5`, jump `1`). -/
example : min ((((5 : ℕ) : ℝ) - 1) / 4) (1 * (((5 : ℕ) : ℝ) - 1) / (8 * 5))
    ≤ ((X : ℝ[X]).natDegree : ℝ) ^ 2 := by
  refine sq_natDegree_ge_of_endpoint_jump (by norm_num) one_pos (fun i _ hi => ?_) ?_
  · simp only [eval_X]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hi
  · norm_num

/-! ## 5. A block arc system with a nontrivial observation map -/

/-- One bit observed through `read x = fun _ => x`. -/
def bitRead : Bool → Unit → Bool := fun x _ => x

/-- One block: nothing loaded before, the single position loaded, conductance `1`. -/
def oneBlock : BlockSys Unit Bool Unit where
  inn _ := ∅
  load _ := {()}
  cond _ _ := 1

/-- The one-path certificate has dual cost `√(1 · 1)`. -/
theorem hasDualOn_bitRead : HasDualOn bitRead id (Real.sqrt (1 * 1)) := by
  refine hasDualOn_of_paths oneBlock bitRead id (P := Unit) (fun _ _ => 1) (fun _ _ => [()])
    (fun _ _ => zero_le_one) (fun _ _ => List.nodup_singleton _) (fun _ _ => by simp)
    (fun x y _ hx hy _ => ?_) (fun _ _ _ _ => by simp [BlockSys.condOf, oneBlock]) one_pos
    one_pos (fun _ _ => by simp [BlockSys.condOf, oneBlock]) (fun _ _ => ?_)
  · simp only [id] at hx hy
    subst hx hy
    simp [agree, BlockSys.out, oneBlock, bitRead]
  · simp [BlockSys.condOf, oneBlock, pathMass]

end AlphabetPolynomialAcceptance
end QuantumQueryComplexity
