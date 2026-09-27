import QuantumQueryComplexity.Quantum.Walk.WeightedClock
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The clock state of `k` summed uniform clocks

`avgPoly T = T⁻¹·(1 + X + ⋯ + X^{T−1}) ∈ ℝ[X]`; the coefficients of `avgPoly T ^ k` are the law
of a sum of `k` independent uniform clocks (nonnegative, summing to `1`, supported below
`k(T−1)+1`).  `kClock T k : Fin (k(T−1)+1) → ℂ` is the unit clock state with those weights, and

    wAvg (kClock T k) U ψ = (uniform average of the first T powers of U) ^ k *ᵥ ψ

(`wAvg_kClock`), because `aeval U` is a ring homomorphism: the weighted detector of
`WeightedClock.lean` with this clock state deviates from `−1` by twice the **`k`-th power** of
the uniform average.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix Polynomial

/-- `T⁻¹·(1 + X + ⋯ + X^{T−1})`. -/
noncomputable def avgPoly (T : ℕ) : ℝ[X] := C ((T : ℝ)⁻¹) * ∑ c ∈ Finset.range T, X ^ c

lemma coeff_avgPoly (T n : ℕ) : (avgPoly T).coeff n = if n < T then (T : ℝ)⁻¹ else 0 := by
  rw [avgPoly, coeff_C_mul, finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq (Finset.range T) n fun _ => (1 : ℝ)]
  simp [Finset.mem_range]

lemma natDegree_avgPoly_le (T : ℕ) : (avgPoly T).natDegree ≤ T - 1 := by
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun c hc => ?_)
  exact (natDegree_X_pow_le c).trans (by have := Finset.mem_range.mp hc; omega)

lemma eval_one_avgPoly {T : ℕ} (hT : 0 < T) : (avgPoly T).eval 1 = 1 := by
  rw [avgPoly, eval_C_mul, eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hT.ne')

/-- Nonnegative coefficients are preserved by products. -/
lemma coeff_mul_nonneg {p q : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) (n : ℕ) :
    0 ≤ (p * q).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

lemma coeff_avgPoly_pow_nonneg (T k n : ℕ) : 0 ≤ ((avgPoly T) ^ k).coeff n := by
  induction k generalizing n with
  | zero => rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ]
      exact coeff_mul_nonneg ih (fun n => by rw [coeff_avgPoly]; split_ifs <;> positivity) n

lemma natDegree_avgPoly_pow_le (T k : ℕ) : ((avgPoly T) ^ k).natDegree ≤ k * (T - 1) :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left k (natDegree_avgPoly_le T))

lemma sum_coeff_avgPoly_pow {T : ℕ} (hT : 0 < T) (k : ℕ) :
    ∑ m ∈ Finset.range (k * (T - 1) + 1), ((avgPoly T) ^ k).coeff m = 1 := by
  have h := eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_avgPoly_pow_le T k)) (1 : ℝ)
  rw [eval_pow, eval_one_avgPoly hT, one_pow] at h
  simp only [one_pow, mul_one] at h
  exact h.symm

/-- **The clock state of `k` summed uniform clocks.** -/
noncomputable def kClock (T k : ℕ) : Fin (k * (T - 1) + 1) → ℂ :=
  fun m => ((Real.sqrt (((avgPoly T) ^ k).coeff m) : ℝ) : ℂ)

lemma normSq_kClock (T k : ℕ) (m : Fin (k * (T - 1) + 1)) :
    Complex.normSq (kClock T k m) = ((avgPoly T) ^ k).coeff m := by
  rw [kClock, Complex.normSq_ofReal, Real.mul_self_sqrt (coeff_avgPoly_pow_nonneg T k m)]

theorem isQState_kClock {T : ℕ} (hT : 0 < T) (k : ℕ) : IsQState (kClock T k) := by
  rw [IsQState, qNormSq_def]
  simp only [normSq_kClock]
  rw [Fin.sum_univ_eq_sum_range (fun m => ((avgPoly T) ^ k).coeff m)]
  exact sum_coeff_avgPoly_pow hT k

/-- The uniform average of the first `T` powers. -/
noncomputable def avgOp {H : Type} [Fintype H] [DecidableEq H] (T : ℕ) (U : Matrix H H ℂ) :
    Matrix H H ℂ :=
  (T : ℂ)⁻¹ • ∑ c ∈ Finset.range T, U ^ c

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

lemma aeval_avgPoly (T : ℕ) (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    aeval U ((avgPoly T).map (algebraMap ℝ ℂ)) = avgOp T U := by
  rw [avgPoly, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sum, map_mul, aeval_C,
    map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_X, map_pow, aeval_X]
  rw [avgOp, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  congr 1
  push_cast
  rfl

/-- **The weighted average with the `k`-clock state is the `k`-th power of the average.** -/
theorem wAvg_kClock {T : ℕ} (hT : 0 < T) (k : ℕ) (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) :
    wAvg (kClock T k) U ψ = (avgOp T U) ^ k *ᵥ ψ := by
  have hdeg : (((avgPoly T) ^ k).map (algebraMap ℝ ℂ)).natDegree < k * (T - 1) + 1 :=
    Nat.lt_succ_of_le (natDegree_map_le.trans (natDegree_avgPoly_pow_le T k))
  have h1 : aeval U (((avgPoly T) ^ k).map (algebraMap ℝ ℂ)) = (avgOp T U) ^ k := by
    rw [Polynomial.map_pow, map_pow, aeval_avgPoly]
  rw [← h1, aeval_eq_sum_range' hdeg, Matrix.sum_mulVec, wAvg,
    ← Fin.sum_univ_eq_sum_range (fun m => ((((avgPoly T) ^ k).map (algebraMap ℝ ℂ)).coeff m
      • U ^ m) *ᵥ ψ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.smul_mulVec, coeff_map, normSq_kClock]
  rfl

end QuantumQueryComplexity
