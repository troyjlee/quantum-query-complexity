import QuantumQueryComplexity.Quantum.Characterization

/-!
# Turning adversary estimates into query bounds

A lower estimate for the adversary value yields a natural-number lower bound
on bounded-error query complexity. An upper estimate gives a query upper bound.
The input and output here are Boolean; the error convention is `1/3`.
-/

namespace QuantumQueryExamples

open QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- To prove at least `k` queries are needed, it suffices to prove `ADV± ≥ 36k`. -/
theorem query_lower_bound (f : (ι → Bool) → Bool) (k : ℕ)
    (h : 36 * (k : ℝ) ≤ advPM f) : k ≤ boundedErrorQQuery f := by
  have hq := mul_advPM_le_boundedErrorQQuery f
  have hk : (k : ℝ) ≤ (boundedErrorQQuery f : ℝ) := by linarith
  exact_mod_cast hk

/-- An adversary upper estimate gives the library's explicit query budget. -/
theorem query_upper_bound (f : (ι → Bool) → Bool) {budget : ℝ}
    (h : advPM f ≤ budget) : (boundedErrorQQuery f : ℝ) ≤ 16384 * budget := by
  have hq := boundedErrorQQuery_le_advPM f
  linarith

end QuantumQueryExamples
