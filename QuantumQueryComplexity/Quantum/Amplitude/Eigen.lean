import QuantumQueryComplexity.Quantum.Amplitude.Estimation
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The eigenvectors of the Grover iterate

On the invariant plane of a `GroverSplit ψ g b` with `‖g‖² = sin² θ`, the **unnormalized**
vectors

    w₊ = sin θ · b + i·cos θ · g,        w₋ = sin θ · b − i·cos θ · g

satisfy `G w₊ = e^{−2iθ} w₊` and `G w₋ = e^{+2iθ} w₋` for the iterate
`G = (2|ψ⟩⟨ψ| − I)·S` — eigenphases `∓θ/π` in the convention `e(φ) = exp(2πiφ)` of
`Kernel.lean`.  They are orthogonal, and

    sin 2θ · ψ = e^{−iθ} · w₊ + e^{+iθ} · w₋.

No division by `sin θ` or `cos θ` occurs, so the statements hold at `p = 0` and `p = 1` too
(where they degenerate).  `Estimation.lean` derives the outcome law of amplitude estimation
directly from the state equation and does not depend on this file; the decomposition is
recorded here as the structural explanation of that law, and for reuse.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

lemma eI_eq (x : ℝ) : eI x = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  rw [eI, mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

namespace GroverSplit

variable {ψ g b : H → ℂ}

/-- `w₊ = sin θ·b + i cos θ·g`. -/
noncomputable def wPlus (g b : H → ℂ) (θ : ℝ) : H → ℂ :=
  (Real.sin θ : ℂ) • b + (Complex.I * (Real.cos θ : ℂ)) • g

/-- `w₋ = sin θ·b − i cos θ·g`. -/
noncomputable def wMinus (g b : H → ℂ) (θ : ℝ) : H → ℂ :=
  (Real.sin θ : ℂ) • b - (Complex.I * (Real.cos θ : ℂ)) • g

private lemma coeff_identities (s c : ℂ) :
    (s * (2 * c ^ 2) + Complex.I * c * (1 - 2 * s ^ 2)
        = (((1 - 2 * s ^ 2) - Complex.I * (2 * s * c)) * (Complex.I * c))) ∧
    (s * (1 - 2 * s ^ 2) - Complex.I * c * (2 * s ^ 2)
        = (((1 - 2 * s ^ 2) - Complex.I * (2 * s * c)) * s)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · linear_combination (2 * s * c ^ 2) * hI
  · ring

/-- **`G w₊ = e(−θ/π)·w₊`**, i.e. eigenvalue `e^{−2iθ}`. -/
theorem iterate_wPlus (h : GroverSplit ψ g b) {θ : ℝ} (hθ : Real.sin θ ^ 2 = qNormSq g)
    {G : Matrix H H ℂ}
    (hGg : G *ᵥ g = ((1 - 2 * qNormSq g : ℝ) : ℂ) • g - ((2 * qNormSq g : ℝ) : ℂ) • b)
    (hGb : G *ᵥ b = ((2 * (1 - qNormSq g) : ℝ) : ℂ) • g
      + ((1 - 2 * qNormSq g : ℝ) : ℂ) • b) :
    G *ᵥ wPlus g b θ = cexp1 (-(θ / Real.pi)) • wPlus g b θ := by
  have hpi := Real.pi_ne_zero
  have hcs : (1 - qNormSq g : ℝ) = Real.cos θ ^ 2 := by rw [Real.cos_sq', hθ]
  have heig : cexp1 (-(θ / Real.pi))
      = (1 - 2 * (Real.sin θ : ℂ) ^ 2)
        - Complex.I * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) := by
    rw [cexp1_eq_eI, show 2 * Real.pi * -(θ / Real.pi) = -(2 * θ) by field_simp, eI_eq,
      Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul, Real.cos_sq']
    simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_neg]
    ring
  obtain ⟨hA, hB⟩ := coeff_identities (Real.sin θ : ℂ) (Real.cos θ : ℂ)
  rw [wPlus, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hGg, hGb, ← hθ,
    show (2 * (1 - Real.sin θ ^ 2) : ℝ) = 2 * Real.cos θ ^ 2 by rw [Real.cos_sq'], heig]
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  rw [smul_add, smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul,
    smul_smul, ← hA, ← hB]
  module

/-- **`G w₋ = e(+θ/π)·w₋`**, i.e. eigenvalue `e^{+2iθ}`. -/
theorem iterate_wMinus (h : GroverSplit ψ g b) {θ : ℝ} (hθ : Real.sin θ ^ 2 = qNormSq g)
    {G : Matrix H H ℂ}
    (hGg : G *ᵥ g = ((1 - 2 * qNormSq g : ℝ) : ℂ) • g - ((2 * qNormSq g : ℝ) : ℂ) • b)
    (hGb : G *ᵥ b = ((2 * (1 - qNormSq g) : ℝ) : ℂ) • g
      + ((1 - 2 * qNormSq g : ℝ) : ℂ) • b) :
    G *ᵥ wMinus g b θ = cexp1 (θ / Real.pi) • wMinus g b θ := by
  have hpi := Real.pi_ne_zero
  have heig : cexp1 (θ / Real.pi)
      = (1 - 2 * (Real.sin θ : ℂ) ^ 2)
        + Complex.I * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) := by
    rw [cexp1_eq_eI, show 2 * Real.pi * (θ / Real.pi) = 2 * θ by field_simp, eI_eq,
      Real.cos_two_mul, Real.sin_two_mul, Real.cos_sq']
    simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_neg]
    ring
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hA : (Real.sin θ : ℂ) * (2 * (Real.cos θ : ℂ) ^ 2)
      - Complex.I * (Real.cos θ : ℂ) * (1 - 2 * (Real.sin θ : ℂ) ^ 2)
      = -(((1 - 2 * (Real.sin θ : ℂ) ^ 2)
          + Complex.I * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)))
        * (Complex.I * (Real.cos θ : ℂ))) := by
    linear_combination (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) ^ 2) * hI
  have hB : (Real.sin θ : ℂ) * (1 - 2 * (Real.sin θ : ℂ) ^ 2)
      + Complex.I * (Real.cos θ : ℂ) * (2 * (Real.sin θ : ℂ) ^ 2)
      = ((1 - 2 * (Real.sin θ : ℂ) ^ 2)
          + Complex.I * (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ))) * (Real.sin θ : ℂ) := by
    ring
  rw [wMinus, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hGg, hGb, ← hθ,
    show (2 * (1 - Real.sin θ ^ 2) : ℝ) = 2 * Real.cos θ ^ 2 by rw [Real.cos_sq'], heig]
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  calc (Real.sin θ : ℂ) • ((2 * (Real.cos θ : ℂ) ^ 2) • g + (1 - 2 * (Real.sin θ : ℂ) ^ 2) • b)
        - (Complex.I * (Real.cos θ : ℂ)) • ((1 - 2 * (Real.sin θ : ℂ) ^ 2) • g
          - (2 * (Real.sin θ : ℂ) ^ 2) • b)
      = ((Real.sin θ : ℂ) * (2 * (Real.cos θ : ℂ) ^ 2)
          - Complex.I * (Real.cos θ : ℂ) * (1 - 2 * (Real.sin θ : ℂ) ^ 2)) • g
        + ((Real.sin θ : ℂ) * (1 - 2 * (Real.sin θ : ℂ) ^ 2)
          + Complex.I * (Real.cos θ : ℂ) * (2 * (Real.sin θ : ℂ) ^ 2)) • b := by module
    _ = _ := by rw [hA, hB]; module

/-- **The two eigenvectors are orthogonal.** -/
theorem qInner_wPlus_wMinus (h : GroverSplit ψ g b) {θ : ℝ}
    (hθ : Real.sin θ ^ 2 = qNormSq g) : qInner (wPlus g b θ) (wMinus g b θ) = 0 := by
  have hgb : qInner g b = 0 := h.orth
  have hbg : qInner b g = 0 := by rw [← qInner_conj g b, hgb]; simp
  have hnb : qNormSq b = Real.cos θ ^ 2 := by rw [h.qNormSq_bad, Real.cos_sq', hθ]
  simp only [wPlus, wMinus, qInner_add_left, qInner_sub_right, qInner_smul_left,
    qInner_smul_right, qInner_self, hgb, hbg, ← hθ, hnb, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  linear_combination ((Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) * hI

/-- **The decomposition of the prepared state**:
`sin 2θ · ψ = e^{−iθ}·w₊ + e^{+iθ}·w₋`. -/
theorem sin_two_mul_smul_eq (h : GroverSplit ψ g b) (θ : ℝ) :
    ((Real.sin (2 * θ) : ℝ) : ℂ) • ψ = eI (-θ) • wPlus g b θ + eI θ • wMinus g b θ := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [h.split, eI_eq, eI_eq, Real.cos_neg, Real.sin_neg, wPlus, wMinus, Real.sin_two_mul]
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  have hA : (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ))
      = ((Real.cos θ : ℂ) + Complex.I * -(Real.sin θ : ℂ)) * (Complex.I * (Real.cos θ : ℂ))
        - ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.cos θ : ℂ)) := by
    linear_combination (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) * hI
  have hB : (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ))
      = ((Real.cos θ : ℂ) + Complex.I * -(Real.sin θ : ℂ)) * (Real.sin θ : ℂ)
        + ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) * (Real.sin θ : ℂ) := by
    ring
  calc (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) • (g + b)
      = (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) • g
        + (2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ)) • b := smul_add _ _ _
    _ = (((Real.cos θ : ℂ) + Complex.I * -(Real.sin θ : ℂ)) * (Complex.I * (Real.cos θ : ℂ))
          - ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) * (Complex.I * (Real.cos θ : ℂ))) • g
        + (((Real.cos θ : ℂ) + Complex.I * -(Real.sin θ : ℂ)) * (Real.sin θ : ℂ)
          + ((Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ)) * (Real.sin θ : ℂ)) • b := by
        rw [← hA, ← hB]
    _ = _ := by module

end GroverSplit

end QuantumQueryComplexity
