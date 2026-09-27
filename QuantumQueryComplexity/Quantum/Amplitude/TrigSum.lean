import QuantumQueryComplexity.Quantum.Amplitude.Geometry
set_option linter.style.header false

/-!
# The averaged success of a uniformly random number of Grover iterations

    sin(2θ) · ∑_{j<m} sin²((2j+1)θ) = m·sin(2θ)/2 − sin(4mθ)/4,

in multiplied form (no denominator), and its consequence: when `a = sin² θ ≤ 1/2` comes from a
success probability `p = 2a ≥ p₀` and `m·√p₀ ≥ 1`, the average of `sin²((2j+1)θ)` over
`j < m` is at least `1/4`.
-/

namespace QuantumQueryComplexity

open Finset

/-- **The telescoping identity, in multiplied form.** -/
theorem sin_two_mul_sum_sin_sq (θ : ℝ) (m : ℕ) :
    Real.sin (2 * θ) * ∑ j ∈ range m, Real.sin ((2 * j + 1) * θ) ^ 2
      = m * Real.sin (2 * θ) / 2 - Real.sin (4 * m * θ) / 4 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, mul_add, ih]
      have hx : (4 * ((m + 1 : ℕ) : ℝ) * θ) = (2 * (2 * m + 1) * θ) + 2 * θ := by
        push_cast; ring
      have hy : (4 * (m : ℝ) * θ) = (2 * (2 * m + 1) * θ) - 2 * θ := by ring
      have hsq : Real.sin ((2 * m + 1) * θ) ^ 2
          = (1 - Real.cos (2 * (2 * m + 1) * θ)) / 2 := by
        have := Real.cos_sq' ((2 * m + 1) * θ)
        have h2 := Real.cos_two_mul ((2 * m + 1) * θ)
        rw [show 2 * ((2 * (m : ℝ) + 1) * θ) = 2 * (2 * m + 1) * θ by ring] at h2
        linarith
      rw [hx, hy, Real.sin_add, Real.sin_sub, hsq]
      push_cast
      ring

/-- `sin(2θ)` at the Grover angle of `a`: `2·√a·√(1−a)`. -/
lemma sin_two_mul_groverAngle {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    Real.sin (2 * groverAngle a) = 2 * Real.sqrt a * Real.sqrt (1 - a) := by
  rw [Real.sin_two_mul, sin_groverAngle h1, groverAngle, Real.cos_arcsin, Real.sq_sqrt h0]

/-- **The averaged success is at least `1/4`**: `a = p/2`, `p₀ ≤ p ≤ 1`, `m·√p₀ ≥ 1`. -/
theorem quarter_le_sum_sin_sq {p p₀ : ℝ} {m : ℕ} (hp₀ : 0 < p₀) (hpp : p₀ ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ (m : ℝ) * Real.sqrt p₀) :
    (m : ℝ) / 4 ≤ ∑ j ∈ range m, Real.sin ((2 * j + 1) * groverAngle (p / 2)) ^ 2 := by
  have hp0 : 0 < p := hp₀.trans_le hpp
  set θ := groverAngle (p / 2) with hθ
  set s := Real.sin (2 * θ) with hs
  have hs_eq : s = 2 * Real.sqrt (p / 2) * Real.sqrt (1 - p / 2) :=
    sin_two_mul_groverAngle (by linarith) (by linarith)
  -- `sin 2θ ≥ √p ≥ √p₀`
  have hs_ge : Real.sqrt p₀ ≤ s := by
    have h1 : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - p / 2) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt p = 2 * Real.sqrt (p / 2) * Real.sqrt (1 / 2) := by
      rw [mul_assoc, ← Real.sqrt_mul (by linarith), show p / 2 * (1 / 2) = p / 4 by ring,
        show p / 4 = p / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (by norm_num)]
      ring
    calc Real.sqrt p₀ ≤ Real.sqrt p := Real.sqrt_le_sqrt hpp
      _ = 2 * Real.sqrt (p / 2) * Real.sqrt (1 / 2) := h2
      _ ≤ 2 * Real.sqrt (p / 2) * Real.sqrt (1 - p / 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s := hs_eq.symm
  have hs_pos : 0 < s := (Real.sqrt_pos.mpr hp₀).trans_le hs_ge
  have hms : 1 ≤ (m : ℝ) * s :=
    hm.trans (mul_le_mul_of_nonneg_left hs_ge (Nat.cast_nonneg m))
  have hid := sin_two_mul_sum_sin_sq θ m
  rw [← hs] at hid
  have hsin : Real.sin (4 * m * θ) ≤ 1 := Real.sin_le_one _
  -- `s·Σ = m s/2 − sin(4mθ)/4 ≥ m s/2 − 1/4 ≥ m s/2 − m s/4 = s·(m/4)`
  have hfin : s * ((m : ℝ) / 4) ≤ s * ∑ j ∈ range m, Real.sin ((2 * j + 1) * θ) ^ 2 := by
    rw [hid]; nlinarith
  exact le_of_mul_le_mul_left hfin hs_pos

end QuantumQueryComplexity
