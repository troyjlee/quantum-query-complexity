import QuantumQueryComplexity.Quantum.ChordWindow
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Uniform-clock suppression on the far window

The spectral half of the uniform-clock detector, and **nothing operational**:
this file knows about a unitary and its chord windows, not about clocks,
routines, or queries.

The statement is that on the far window — chord distance at least `|Δ|` — the
uniform average of the first `T` powers is small:

  `‖T⁻¹ ∑_{c<T} Uᶜ x‖² ≤ 4/(T²Δ²) · ‖x‖²`.

The proof is three lines of mathematics.  Telescoping gives
`(1 - U)·∑_{t<T} Uᵗ = 1 - Uᵀ`, so the average, hit with `1 - U`, becomes
`T⁻¹(1 - Uᵀ)x`, which has norm at most `2/T·‖x‖` because `Uᵀ` is unitary.  On the
far window `‖(1 - U)y‖ ≥ |Δ|·‖y‖` (`chordFar_bound_sq`), and dividing by `Δ`
gives the bound.  The far projector commutes with `U`, so it commutes with the
geometric sum and can be moved wherever it is needed.

The workhorse is stated **multiplied out**, `T²Δ²·‖avg‖² ≤ 4‖x‖²`, which holds
for every `Δ` and every `T` with no positivity hypothesis; the divided form
follows for `0 < Δ` and `0 < T`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- **A unitary moves a vector by at most twice its norm**: `‖(1 - Uᵀ)x‖ ≤ 2‖x‖`,
squared. -/
lemma qNormSq_one_sub_pow_mulVec_le {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (T : ℕ) (x : H → ℂ) :
    qNormSq ((1 - U ^ T) *ᵥ x) ≤ 4 * qNormSq x := by
  have hUT : U ^ T ∈ Matrix.unitaryGroup H ℂ := pow_mem hU T
  have hsplit : x + (-1 : ℂ) • (U ^ T *ᵥ x) = (1 - U ^ T) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    module
  have hneg : qNormSq ((-1 : ℂ) • (U ^ T *ᵥ x)) = qNormSq x := by
    rw [qNormSq_smul, qNormSq_mulVec hUT]
    simp
  have htri := sqrt_qNormSq_add_le x ((-1 : ℂ) • (U ^ T *ᵥ x))
  rw [hsplit, hneg] at htri
  have h0 : (0 : ℝ) ≤ qNormSq x := qNormSq_nonneg x
  have hsq := Real.sq_sqrt (qNormSq_nonneg ((1 - U ^ T) *ᵥ x))
  have hxsq := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (qNormSq ((1 - U ^ T) *ᵥ x)), Real.sqrt_nonneg (qNormSq x)]

/-- The far projector commutes with the geometric sum, since it commutes with
`U`. -/
lemma chordFarProj_commute_geom {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) (T : ℕ) :
    Commute (chordFarProj U Δ) (∑ t ∈ Finset.range T, U ^ t) :=
  Commute.sum_right _ _ _ fun t _ =>
    (show Commute (chordFarProj U Δ) U from chordFarProj_commute hU Δ).pow_right t

/-- **Uniform-clock suppression**, multiplied out.  Holds for every `Δ` and every
`T`, with **no positivity hypothesis**: it is vacuous at `Δ = 0` or `T = 0`,
which is exactly why the divided form below is the one that asks for both to be
positive. -/
theorem qNormSq_avg_pow_chordFar {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) (T : ℕ) (x : H → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      ≤ 4 * qNormSq x := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · -- an empty clock: the left side carries the factor `T² = 0`
    subst hT
    have hq := qNormSq_nonneg x
    have h0 : ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul, zero_mul]
    linarith
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hFU : Commute (chordFarProj U Δ) U := chordFarProj_commute hU Δ
  have hFG := chordFarProj_commute_geom hU Δ T
  -- the sum over `Fin T` is the geometric sum, with the projector moved across
  have hFGx : (∑ t ∈ Finset.range T, U ^ t) *ᵥ (chordFarProj U Δ *ᵥ x)
      = chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hFG.eq]
  have hrewrite : ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      = (T : ℂ)⁻¹ • (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)) := by
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun t => (U ^ t) *ᵥ (chordFarProj U Δ *ᵥ x)) T,
      ← Matrix.sum_mulVec, hFGx]
  -- `(1 - U)` also commutes with the projector, and telescopes against the sum
  have hF1U : (1 - U) * chordFarProj U Δ = chordFarProj U Δ * (1 - U) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hFU.eq]
  have hcomm2 : (1 - U) *ᵥ (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x))
      = chordFarProj U Δ *ᵥ ((1 - U ^ T) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hF1U, Matrix.mul_assoc, one_sub_mul_geom_sum]
  -- coercivity on the far window, then the projector shrinks, then `‖1 - Uᵀ‖ ≤ 2`
  have key : Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x))
      ≤ 4 * qNormSq x := by
    have h1 := chordFar_bound_sq U Δ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)
    rw [hcomm2] at h1
    have h2 : qNormSq (chordFarProj U Δ *ᵥ ((1 - U ^ T) *ᵥ x))
        ≤ qNormSq ((1 - U ^ T) *ᵥ x) :=
      (isQProjector_chordFarProj U Δ).qNormSq_mulVec_le _
    have h3 := qNormSq_one_sub_pow_mulVec_le hU T x
    linarith
  have hnormsq : Complex.normSq ((T : ℂ)⁻¹) = ((T : ℝ) * (T : ℝ))⁻¹ := by
    rw [Complex.normSq_inv, ← Complex.ofReal_natCast, Complex.normSq_ofReal]
  rw [hrewrite, qNormSq_smul, hnormsq]
  calc (T : ℝ) ^ 2 * Δ ^ 2
        * (((T : ℝ) * (T : ℝ))⁻¹
          * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)))
      = Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ ((∑ t ∈ Finset.range T, U ^ t) *ᵥ x)) := by
        field_simp
    _ ≤ 4 * qNormSq x := key

/-- **Uniform-clock suppression**, in the form the detector uses:
`‖T⁻¹ ∑_{c<T} Uᶜ x‖² ≤ 4/(T²Δ²)·‖x‖²` on the far window. -/
theorem qNormSq_avg_pow_chordFar_div {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {Δ : ℝ} (hΔ : 0 < Δ) {T : ℕ} (hT : 0 < T)
    (x : H → ℂ) :
    qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ (chordFarProj U Δ *ᵥ x))
      ≤ 4 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq x := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < (T : ℝ) ^ 2 * Δ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm]
  exact qNormSq_avg_pow_chordFar hU Δ T x

end QuantumQueryComplexity
