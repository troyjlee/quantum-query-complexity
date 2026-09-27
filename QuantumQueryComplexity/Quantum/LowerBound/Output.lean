import QuantumQueryComplexity.Quantum.LowerBound.Progress
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The output condition

At the end of a successful computation the progress must be *small*: an
adversary matrix is supported on pairs with different `f`-values, and a state
that announces `f x` with probability at least `1 - ε` is nearly orthogonal to
one that announces `f y ≠ f x`.

Split each final state along the outcome it is supposed to announce,

  `ψ x = A x + B x`,  `A x = qRestrict readout (f x) (ψ x)`,

so `‖A x‖² ≥ 1 - ε` and `‖B x‖² ≤ ε`.  The `A`–`A` term of the expanded Gram
form vanishes **entirely**: where `Γ` is nonzero the two outcomes differ, and
distinct outcomes are orthogonal (`qInner_qRestrict_of_ne`); where the outcomes
agree `Γ` is zero.  The remaining three terms are bounded by the bridge, giving

  `|progress| ≤ ‖Γ‖ (2√ε + ε)`.

**On the constant.**  The sharp bound for this step is `2√(ε(1-ε))`, which is
what makes `ε = 1/3` work in the literature.  For general finite outputs the
matrix-level argument here gives `2√ε + ε` instead, which is `< 1` exactly
when `ε < 3 - 2√2 ≈ 0.1716`.  For **Boolean** outputs the sharp constant IS
recovered directly — `OutputBool.lean` (the error parts are orthogonal on the
adversary matrix's support, and the masses are linked), consumed by
`MainBool.lean` for the `ε = 1/3` lower bound.  Amplification remains the
relevant route only for general outputs, where the `B`–`B` term does not
vanish.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {O : Type} [Fintype O] [DecidableEq O]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {H : Type} [Fintype H] [DecidableEq H]

/-- **The output condition.**  On final states that are correct with probability
at least `1 - ε`, the progress of any adversary matrix is at most
`‖Γ‖ (2√ε + ε)`. -/
theorem abs_progress_output_le {Γ : Matrix X X ℝ} {f : X → O}
    (hΓ : ∀ x y, f x = f y → Γ x y = 0)
    {ψ : X → (H → ℂ)} (hψ : ∀ x, IsQState (ψ x))
    {p : H → O} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hp : ∀ x, 1 - ε ≤ qProb p (ψ x) (f x))
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |progress Γ δ δ' ψ| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by
  classical
  set A : X → (H → ℂ) := fun x => qRestrict p (f x) (ψ x) with hA
  set B : X → (H → ℂ) := fun x => ψ x - A x with hB
  have hsplit : ∀ x, ψ x = A x + B x := by
    intro x
    rw [hB]
    simp
  -- the four norms
  have hnormA : ∀ x, qNormSq (A x) = qProb p (ψ x) (f x) := by
    intro x
    rw [hA, qProb_eq_qNormSq_qRestrict]
  have hnormB : ∀ x, qNormSq (B x) = 1 - qProb p (ψ x) (f x) := by
    intro x
    rw [hB, hA, qNormSq_sub_qRestrict, hψ x]
  have hsumA : ∑ x, qNormSq (qScale δ A x) ≤ 1 := by
    calc ∑ x, qNormSq (qScale δ A x) = ∑ x, δ x ^ 2 * qProb p (ψ x) (f x) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormA x]
      _ ≤ ∑ x, δ x ^ 2 * 1 :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (qProb_le_one (hψ x) p (f x)) (sq_nonneg _)
      _ = 1 := by simpa using hδ
  have hsumA' : ∑ y, qNormSq (qScale δ' A y) ≤ 1 := by
    calc ∑ y, qNormSq (qScale δ' A y) = ∑ y, δ' y ^ 2 * qProb p (ψ y) (f y) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormA y]
      _ ≤ ∑ y, δ' y ^ 2 * 1 :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (qProb_le_one (hψ y) p (f y)) (sq_nonneg _)
      _ = 1 := by simpa using hδ'
  have hsumB : ∑ x, qNormSq (qScale δ B x) ≤ ε := by
    calc ∑ x, qNormSq (qScale δ B x) = ∑ x, δ x ^ 2 * (1 - qProb p (ψ x) (f x)) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormB x]
      _ ≤ ∑ x, δ x ^ 2 * ε :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp x]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ, one_mul]
  have hsumB' : ∑ y, qNormSq (qScale δ' B y) ≤ ε := by
    calc ∑ y, qNormSq (qScale δ' B y) = ∑ y, δ' y ^ 2 * (1 - qProb p (ψ y) (f y)) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormB y]
      _ ≤ ∑ y, δ' y ^ 2 * ε :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp y]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ', one_mul]
  -- the `A`–`A` term vanishes
  have hAA : gramForm Γ (qScale δ A) (qScale δ' A) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have : qInner (qScale δ A x) (qScale δ' A y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right, hA]
        rw [qInner_qRestrict_of_ne p hf]
        ring
      rw [this]
      simp
  -- expand and bound the three remaining terms
  have hexp : progress Γ δ δ' ψ
      = gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)
        + gramForm Γ (qScale δ B) (qScale δ' B) := by
    have h1 : qScale δ ψ = fun x => qScale δ A x + qScale δ B x := by
      funext x
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ w x) (funext hsplit)
    have h2 : qScale δ' ψ = fun y => qScale δ' A y + qScale δ' B y := by
      funext y
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ' w y) (funext hsplit)
    rw [progress, h1, h2, gramForm_add_left, gramForm_add_right, gramForm_add_right,
      hAA]
    ring
  have hb1 := abs_gramForm_le Γ (qScale δ A) (qScale δ' B)
  have hb2 := abs_gramForm_le Γ (qScale δ B) (qScale δ' A)
  have hb3 := abs_gramForm_le Γ (qScale δ B) (qScale δ' B)
  have hsqA : Real.sqrt (∑ x, qNormSq (qScale δ A x)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hsumA
  have hsqA' : Real.sqrt (∑ y, qNormSq (qScale δ' A y)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hsumA'
  have hsqB : Real.sqrt (∑ x, qNormSq (qScale δ B x)) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hsumB
  have hsqB' : Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hsumB'
  have hΓ0 : (0 : ℝ) ≤ ‖Γ‖ := norm_nonneg _
  have hεs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hεsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0
  have hb1' : |gramForm Γ (qScale δ A) (qScale δ' B)| ≤ ‖Γ‖ * Real.sqrt ε := by
    refine hb1.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ A x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ 1 * Real.sqrt ε :=
      mul_le_mul hsqA hsqB' (Real.sqrt_nonneg _) zero_le_one
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ A x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' B y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ A x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' B y))) := by ring
      _ ≤ ‖Γ‖ * (1 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * Real.sqrt ε := by ring
  have hb2' : |gramForm Γ (qScale δ B) (qScale δ' A)| ≤ ‖Γ‖ * Real.sqrt ε := by
    refine hb2.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ B x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' A y)) ≤ Real.sqrt ε * 1 :=
      mul_le_mul hsqB hsqA' (Real.sqrt_nonneg _) hεs
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ B x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' A y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ B x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' A y))) := by ring
      _ ≤ ‖Γ‖ * (Real.sqrt ε * 1) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * Real.sqrt ε := by ring
  have hb3' : |gramForm Γ (qScale δ B) (qScale δ' B)| ≤ ‖Γ‖ * ε := by
    refine hb3.trans ?_
    have hp : Real.sqrt (∑ x, qNormSq (qScale δ B x))
        * Real.sqrt (∑ y, qNormSq (qScale δ' B y)) ≤ Real.sqrt ε * Real.sqrt ε :=
      mul_le_mul hsqB hsqB' (Real.sqrt_nonneg _) hεs
    calc ‖Γ‖ * Real.sqrt (∑ x, qNormSq (qScale δ B x))
          * Real.sqrt (∑ y, qNormSq (qScale δ' B y))
        = ‖Γ‖ * (Real.sqrt (∑ x, qNormSq (qScale δ B x))
            * Real.sqrt (∑ y, qNormSq (qScale δ' B y))) := by ring
      _ ≤ ‖Γ‖ * (Real.sqrt ε * Real.sqrt ε) := mul_le_mul_of_nonneg_left hp hΓ0
      _ = ‖Γ‖ * ε := by rw [hεsq]
  rw [hexp]
  calc |gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)
        + gramForm Γ (qScale δ B) (qScale δ' B)|
      ≤ |gramForm Γ (qScale δ A) (qScale δ' B) + gramForm Γ (qScale δ B) (qScale δ' A)|
          + |gramForm Γ (qScale δ B) (qScale δ' B)| := abs_add_le _ _
    _ ≤ (|gramForm Γ (qScale δ A) (qScale δ' B)| + |gramForm Γ (qScale δ B) (qScale δ' A)|)
          + |gramForm Γ (qScale δ B) (qScale δ' B)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by linarith

end QuantumQueryComplexity
