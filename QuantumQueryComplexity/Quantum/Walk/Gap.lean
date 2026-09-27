import QuantumQueryComplexity.Quantum.Approximation
import QuantumQueryComplexity.Quantum.ClockGap
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Two spectral-free gap lemmas for quantum walks

Both replace an eigen-decomposition by a quadratic-form or a telescoping argument.

* `hermitian_gap_ineq` — for a Hermitian `J`, `λ² ≤ 1`, and a vector `z` with `‖J z‖ ≤ λ‖z‖`
  and `‖J z₁‖ ≤ λ‖z₁‖`, `z₁ = z + J z`:

      ⟨z₁, (1 − J) z₁⟩  ≥  (1 − λ²)·⟨z, (1 + J) z⟩.

  With `J` the off-diagonal block matrix of the discriminant of a reversible chain, the left
  side is `‖(Π_A − Π_B) v‖²` and the right side `(1 − λ²)‖v‖²` for `v = A x + B y`: the walk
  `W = (2Π_B − 1)(2Π_A − 1)` satisfies `‖(W − 1)v‖ = 2‖(Π_A − Π_B)v‖ ≥ 2√(1−λ²)·‖v‖` on the
  complement of the stationary vector **inside the sum of the two row spaces** (the orthogonal
  complement of that sum is fixed by `W`, and no gap is claimed there).  The proof expands
  every term in `‖z‖², ‖Jz‖², ‖J²z‖², Re⟨z,Jz⟩, Re⟨Jz,J²z⟩` and adds three nonnegative
  quantities: `λ²‖z₁‖² − ‖Jz₁‖²`, `‖(λ² − J²)z‖²`, `(1−λ²)(λ²‖z‖² − ‖Jz‖²)`.
* `qNormSq_avg_le_of_gap` — if `K` is a `U`-invariant subspace on which `‖(U − 1)y‖ ≥ γ‖y‖`,
  then for `v ∈ K` the uniform average of the first `T` powers has
  `T²γ²·‖T⁻¹∑_{c<T} Uᶜ v‖² ≤ 4‖v‖²`: telescoping, no spectral projector.  Iterating it `k`
  times gives the `(2/(Tγ))^k` of a `k`-clock detector.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The Hermitian inequality -/

section Hermitian

variable {J : Matrix H H ℂ}

lemma qInner_mulVec_hermitian (hJ : Jᴴ = J) (u v : H → ℂ) :
    qInner (J *ᵥ u) v = qInner u (J *ᵥ v) := by
  have h := qInner_mulVec_left Jᴴ u (J *ᵥ v)
  have h2 := qInner_mulVec_left J u v
  rw [hJ] at h2
  exact h2

/-- The inequality, for three vectors standing for `z`, `J z`, `J² z`. -/
lemma gap_ineq_aux {lam : ℝ} (hlam : lam ^ 2 ≤ 1) (z0 z1 z2 : H → ℂ)
    (hH : (qInner z0 z2).re = qNormSq z1)
    (h0 : qNormSq z1 ≤ lam ^ 2 * qNormSq z0)
    (h1 : qNormSq (z1 + z2) ≤ lam ^ 2 * qNormSq (z0 + z1)) :
    (1 - lam ^ 2) * (qInner z0 (z0 + z1)).re ≤ (qInner (z0 + z1) ((z0 + z1) - (z1 + z2))).re := by
  have hsym : (qInner z1 z0).re = (qInner z0 z1).re := by
    rw [← qInner_conj z0 z1]; simp
  have hA : (qInner z0 (z0 + z1)).re = qNormSq z0 + (qInner z0 z1).re := by
    rw [qInner_add_right, Complex.add_re, qInner_self, Complex.ofReal_re]
  have hB : (qInner (z0 + z1) ((z0 + z1) - (z1 + z2))).re
      = qNormSq z0 - qNormSq z1 + (qInner z0 z1).re - (qInner z1 z2).re := by
    have : z0 + z1 - (z1 + z2) = z0 - z2 := by abel
    rw [this, qInner_sub_right, qInner_add_left, qInner_add_left, Complex.sub_re,
      Complex.add_re, Complex.add_re, qInner_self, Complex.ofReal_re, hsym, hH]
    ring
  have hC : qNormSq (z0 + z1) = qNormSq z0 + qNormSq z1 + 2 * (qInner z0 z1).re := qNormSq_add _ _
  have hD : qNormSq (z1 + z2) = qNormSq z1 + qNormSq z2 + 2 * (qInner z1 z2).re := qNormSq_add _ _
  have hsq : 0 ≤ lam ^ 4 * qNormSq z0 + qNormSq z2 - 2 * lam ^ 2 * qNormSq z1 := by
    have h := qNormSq_nonneg (((lam ^ 2 : ℝ) : ℂ) • z0 + (-1 : ℂ) • z2)
    rw [qNormSq_add, qNormSq_smul, qNormSq_smul, qInner_smul_left, qInner_smul_right,
      Complex.normSq_ofReal] at h
    have hre : (star (((lam ^ 2 : ℝ) : ℂ)) * (-1 * qInner z0 z2)).re
        = -(lam ^ 2 * qNormSq z1) := by
      rw [Complex.star_def, Complex.conj_ofReal, neg_one_mul, mul_neg, Complex.neg_re,
        Complex.re_ofReal_mul, hH]
    rw [hre] at h
    simp only [Complex.normSq_neg, Complex.normSq_one, one_mul] at h
    nlinarith
  rw [hA, hB]
  rw [hC, hD] at h1
  have hlast : 0 ≤ (1 - lam ^ 2) * (lam ^ 2 * qNormSq z0 - qNormSq z1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **The Hermitian gap inequality.** -/
theorem hermitian_gap_ineq (hJ : Jᴴ = J) {lam : ℝ} (hlam : lam ^ 2 ≤ 1) (z : H → ℂ)
    (h0 : qNormSq (J *ᵥ z) ≤ lam ^ 2 * qNormSq z)
    (h1 : qNormSq (J *ᵥ (z + J *ᵥ z)) ≤ lam ^ 2 * qNormSq (z + J *ᵥ z)) :
    (1 - lam ^ 2) * (qInner z (z + J *ᵥ z)).re
      ≤ (qInner (z + J *ᵥ z) ((z + J *ᵥ z) - J *ᵥ (z + J *ᵥ z))).re := by
  have hJadd : J *ᵥ (z + J *ᵥ z) = J *ᵥ z + J *ᵥ (J *ᵥ z) := Matrix.mulVec_add _ _ _
  have hH : (qInner z (J *ᵥ (J *ᵥ z))).re = qNormSq (J *ᵥ z) := by
    rw [← qInner_mulVec_hermitian hJ, qInner_self, Complex.ofReal_re]
  rw [hJadd] at h1 ⊢
  exact gap_ineq_aux hlam z (J *ᵥ z) (J *ᵥ (J *ᵥ z)) hH h0 h1

end Hermitian

/-! ## Averaging on an invariant subspace with a gap -/

/-- **The uniform average of the first `T` powers is small where `U − 1` is bounded below.** -/
theorem qNormSq_avg_le_of_gap {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (K : Submodule ℂ (H → ℂ)) (hK : ∀ y ∈ K, U *ᵥ y ∈ K) {γ : ℝ}
    (hgap : ∀ y ∈ K, γ ^ 2 * qNormSq y ≤ qNormSq ((1 - U) *ᵥ y)) (T : ℕ) {v : H → ℂ}
    (hv : v ∈ K) :
    (T : ℝ) ^ 2 * γ ^ 2 * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v)
      ≤ 4 * qNormSq v
    ∧ (T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v ∈ K := by
  have hpow : ∀ n : ℕ, (U ^ n) *ᵥ v ∈ K := by
    intro n
    induction n with
    | zero => rwa [pow_zero, Matrix.one_mulVec]
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hK _ ih
  have hmem : (T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v ∈ K :=
    K.smul_mem _ (K.sum_mem fun c _ => hpow c)
  refine ⟨?_, hmem⟩
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have := qNormSq_nonneg v
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    linarith
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  -- telescoping
  have htel : (1 - U) *ᵥ ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v)
      = (T : ℂ)⁻¹ • ((1 - U ^ T) *ᵥ v) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
    congr 1
    have hsum : (∑ c : Fin T, (1 - U) *ᵥ ((U ^ (c : ℕ)) *ᵥ v))
        = ((1 - U) * ∑ c ∈ Finset.range T, U ^ c) *ᵥ v := by
      rw [Fin.sum_univ_eq_sum_range (fun c => (1 - U) *ᵥ ((U ^ c) *ᵥ v)) T, Matrix.mul_sum,
        Matrix.sum_mulVec]
      exact Finset.sum_congr rfl fun c _ => by rw [Matrix.mulVec_mulVec]
    rw [hsum, one_sub_mul_geom_sum]
  have h1 := hgap _ hmem
  rw [htel, qNormSq_smul ((T : ℂ)⁻¹) ((1 - U ^ T) *ᵥ v)] at h1
  have h2 := qNormSq_one_sub_pow_mulVec_le hU T v
  have hn : Complex.normSq ((T : ℂ)⁻¹) = ((T : ℝ) ^ 2)⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_natCast, pow_two]
  rw [hn] at h1
  have hT2 : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
  have h3 : (T : ℝ) ^ 2 * (γ ^ 2 * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v))
      ≤ qNormSq ((1 - U ^ T) *ᵥ v) := by
    have := mul_le_mul_of_nonneg_left h1 hT2.le
    rwa [mul_inv_cancel_left₀ hT2.ne'] at this
  calc (T : ℝ) ^ 2 * γ ^ 2 * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v)
      = (T : ℝ) ^ 2 * (γ ^ 2 * qNormSq ((T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v)) := by
        ring
    _ ≤ qNormSq ((1 - U ^ T) *ᵥ v) := h3
    _ ≤ 4 * qNormSq v := h2

end QuantumQueryComplexity
