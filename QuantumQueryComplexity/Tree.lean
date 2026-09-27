import QuantumQueryComplexity.AndOr
set_option linter.style.header false

/-!
# The balanced AND-OR tree

Composing the two-bit AND and OR functions alternately gives the balanced
AND-OR tree on `n = 2^(d+1)` bits.  Since `ADV±(AND₂) = ADV±(OR₂) = √2` is
certified on both the primal and the dual side (`hasAdvValue_and2`,
`hasAdvValue_or2`), perfect composition applies at every level and yields

  `ADV±(balanced AND-OR tree on n bits) = √n`.

This is the tight form of the Barnum–Saks `Ω(√n)` bound (HLŠ Corollary 15):
here we obtain the exact value, with no appeal to general strong duality.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

/-- The balanced alternating AND-OR tree of depth `d+1`, on
`2^(d+1)` input bits.  The gates at the bottom level are `AND`, and the gate
type alternates going up. -/
def andOrTree : (d : ℕ) → ((iterIdx (Fin 2) d → Bool) → Bool)
  | 0 => and2
  | d + 1 => composeFun (if d % 2 = 0 then or2 else and2) (andOrTree d)

lemma hasAdvValue_root (d : ℕ) :
    HasAdvValue (if d % 2 = 0 then or2 else and2) (Real.sqrt 2) := by
  split_ifs
  · exact hasAdvValue_or2
  · exact hasAdvValue_and2

/-- **The balanced AND-OR tree of depth `d+1` has adversary bound
`(√2)^(d+1)`**, certified on both the primal and the dual side. -/
theorem hasAdvValue_andOrTree (d : ℕ) :
    HasAdvValue (andOrTree d) (Real.sqrt 2 ^ (d + 1)) := by
  induction d with
  | zero =>
      rw [pow_one]
      exact hasAdvValue_and2
  | succ d ih =>
      have h := (hasAdvValue_root d).compose ih
      have hpow : Real.sqrt 2 * Real.sqrt 2 ^ (d + 1)
          = Real.sqrt 2 ^ (d + 1 + 1) := by ring
      rw [hpow] at h
      exact h

lemma sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt x ^ k = Real.sqrt (x ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.sqrt_mul (pow_nonneg hx k), pow_succ]

lemma card_iterIdx_fin2 (d : ℕ) :
    Fintype.card (iterIdx (Fin 2) d) = 2 ^ (d + 1) := by
  induction d with
  | zero => simp [iterIdx]
  | succ d ih =>
      show Fintype.card (Fin 2 × iterIdx (Fin 2) d) = _
      rw [Fintype.card_prod, ih, Fintype.card_fin]
      ring

/-- **`ADV±` of the balanced AND-OR tree on `n = 2^(d+1)` bits is `√n`.** -/
theorem advPM_andOrTree (d : ℕ) :
    advPM (andOrTree d) = Real.sqrt (2 ^ (d + 1)) := by
  rw [(hasAdvValue_andOrTree d).1, sqrt_pow_nat (by norm_num : (0:ℝ) ≤ 2)]

/-- The same statement with `n` expressed as the number of input bits. -/
theorem advPM_andOrTree_eq_sqrt_card (d : ℕ) :
    advPM (andOrTree d)
      = Real.sqrt (Fintype.card (iterIdx (Fin 2) d) : ℝ) := by
  rw [advPM_andOrTree, card_iterIdx_fin2]
  norm_num

/-- The dual value agrees, so strong duality holds at every balanced AND-OR
tree. -/
theorem advDual_andOrTree (d : ℕ) :
    advDual (andOrTree d) = Real.sqrt (2 ^ (d + 1)) := by
  rw [(hasAdvValue_andOrTree d).2, sqrt_pow_nat (by norm_num : (0:ℝ) ≤ 2)]

end QuantumQueryComplexity
