import QuantumQueryComplexity.Quantum.FiniteHilbert
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Fidelity bounds for a unitary, against a fixed vector and against a far pair

The two generic Hilbert-space estimates behind the state-conversion
measurement.  The quantity a Hadamard test reads out is `Re⟪ψ, Uψ⟫`, and the
detector `U` of `InputDetector.lean` is designed to make it large on one kind
of input and small on the other.  This file proves the two sides in the
abstract, for an arbitrary unitary `U` on an arbitrary finite space:

* **the positive side** (`le_mul_re_qInner_mulVec_of_fixed`): if `U` fixes
  `φ`, then `Re⟪ψ, Uψ⟫ ≥ 2|⟪φ,ψ⟫|²/‖φ‖² − ‖ψ‖²` — stated multiplied out by
  `‖φ‖⁴`, so `φ = 0` needs no special case and no division appears;
* **the negative side** (`re_qInner_mulVec_le_of_perp`): if `ψ = ψN + ψF`
  orthogonally and `‖UψF + ψF‖` is small — `U` is close to `−1` on the far
  part — then `Re⟪ψ, Uψ⟫ ≤ ‖ψ‖‖ψN‖ + ‖ψ‖‖UψF + ψF‖ − ‖ψF‖²`.

No spectral decomposition of `U` occurs.  The positive bound is one
Cauchy–Schwarz application to the auxiliary vector `χ = ‖φ‖²ψ − ⟪φ,ψ⟫φ`, the
component of `‖φ‖²ψ` orthogonal to `φ`: since `U` and `Uᴴ` both fix `φ`, the
plane spanned by `φ` and the pair `χ, Uχ` splits the form `⟪ψ, Uψ⟫` exactly,
and Cauchy–Schwarz on the `χ`-part is the only estimate.  The negative bound
is Cauchy–Schwarz three times, with the orthogonality supplying the exact
`−‖ψF‖²` term.

Also here: `qInner_mulVec_one_sub_mulVec`, the orthogonality of a projector's
range and its complement's range on the same vector — the form in which the
chord windows enter the negative side downstream.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- A unitary that fixes a vector: so does its adjoint. -/
lemma conjTranspose_mulVec_of_fixed {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {φ : H → ℂ} (hφ : U *ᵥ φ = φ) :
    Uᴴ *ᵥ φ = φ := by
  conv_lhs => rw [← hφ]
  rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary hU,
    Matrix.one_mulVec]

private lemma star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.conj_ofReal]

private lemma star_mul_self_eq (b : ℂ) :
    star b * b = ((Complex.normSq b : ℝ) : ℂ) := by
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]

private lemma mul_star_self_eq (b : ℂ) :
    b * star b = ((Complex.normSq b : ℝ) : ℂ) := by
  rw [mul_comm]; exact star_mul_self_eq b

/-- `Re z ≥ −‖ψ‖‖φ‖` for an inner product `z = ⟪ψ, φ⟫`. -/
private lemma neg_le_re_qInner (ψ φ : H → ℂ) :
    -(Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ)) ≤ (qInner ψ φ).re := by
  have h1 := Complex.abs_re_le_norm (qInner ψ φ)
  have h2 := qInner_norm_le ψ φ
  have := abs_le.mp (h1.trans h2)
  linarith [this.1]

/-- `Re z ≤ ‖ψ‖‖φ‖` for an inner product `z = ⟪ψ, φ⟫`. -/
private lemma re_qInner_le (ψ φ : H → ℂ) :
    (qInner ψ φ).re ≤ Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ) := by
  have h1 := Complex.abs_re_le_norm (qInner ψ φ)
  have h2 := qInner_norm_le ψ φ
  have := abs_le.mp (h1.trans h2)
  linarith [this.2]

/-- **The fidelity lower bound.**  A unitary that fixes `φ` satisfies, on every
`ψ`, `Re⟪ψ, Uψ⟫ ≥ 2|⟪φ,ψ⟫|²/‖φ‖² − ‖ψ‖²` — multiplied out by `‖φ‖⁴`, so no
positivity of `‖φ‖` is assumed and no division appears. -/
theorem le_mul_re_qInner_mulVec_of_fixed {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {φ : H → ℂ} (hφ : U *ᵥ φ = φ)
    (ψ : H → ℂ) :
    2 * Complex.normSq (qInner φ ψ) * qNormSq φ - qNormSq φ ^ 2 * qNormSq ψ
      ≤ qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re := by
  set b : ℂ := qInner φ ψ with hb
  set χ : H → ℂ := ((qNormSq φ : ℝ) : ℂ) • ψ + (-b) • φ with hχ
  -- the orthogonality facts: `φ ⊥ χ` and `φ ⊥ Uχ`
  have hφχ : qInner φ χ = 0 := by
    rw [hχ, qInner_add_right, qInner_smul_right, qInner_smul_right,
      qInner_self, ← hb]
    ring
  have hχφ : qInner χ φ = 0 := by
    have h := congrArg star hφχ
    rwa [qInner_conj, star_zero] at h
  have hUχ : U *ᵥ χ = ((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ) + (-b) • φ := by
    rw [hχ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hφ]
  have hφUχ : qInner φ (U *ᵥ χ) = 0 := by
    have h1 : qInner (U *ᵥ χ) φ = qInner χ φ := by
      rw [qInner_mulVec_left, conjTranspose_mulVec_of_fixed hU hφ]
    have h := congrArg star (h1.trans hχφ)
    rwa [qInner_conj, star_zero] at h
  -- the split of `‖φ‖²ψ` along `φ` and its complement
  have hdec : ((qNormSq φ : ℝ) : ℂ) • ψ = χ + b • φ := by
    rw [hχ]; module
  have hUdec : ((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ) = U *ᵥ χ + b • φ := by
    rw [hUχ]; module
  have hψφ : qInner ψ φ = star b := by rw [hb, qInner_conj]
  -- the exact complex identity: `‖φ‖⁴⟪ψ,Uψ⟫ = ⟪χ,Uχ⟫ + |⟪φ,ψ⟫|²‖φ‖²`
  have hmain : ((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ)
      = qInner χ (U *ᵥ χ)
        + ((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ) := by
    have hL : qInner (((qNormSq φ : ℝ) : ℂ) • ψ)
          (((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ))
        = ((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ) := by
      rw [qInner_smul_left, qInner_smul_right, star_ofReal]
      ring
    have hR : qInner (χ + b • φ) (U *ᵥ χ + b • φ)
        = qInner χ (U *ᵥ χ)
          + ((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ) := by
      simp only [qInner_add_left, qInner_add_right, qInner_smul_left,
        qInner_smul_right, qInner_self]
      rw [hχφ, hφUχ]
      linear_combination ((qNormSq φ : ℝ) : ℂ) * mul_star_self_eq b
    rw [← hL, hdec, hUdec, hR]
  -- extract real parts
  have hre : qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re
      = (qInner χ (U *ᵥ χ)).re + Complex.normSq b * qNormSq φ := by
    have h := congrArg Complex.re hmain
    rwa [Complex.add_re,
      show (((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ)).re
          = qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re from by
        rw [← Complex.ofReal_pow, Complex.re_ofReal_mul],
      show (((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ)).re
          = Complex.normSq b * qNormSq φ from by
        rw [← Complex.ofReal_mul, Complex.ofReal_re]] at h
  -- Cauchy–Schwarz on the `χ`-part
  have hCS : -(qNormSq χ) ≤ (qInner χ (U *ᵥ χ)).re := by
    have h := neg_le_re_qInner χ (U *ᵥ χ)
    rwa [qNormSq_mulVec hU, Real.mul_self_sqrt (qNormSq_nonneg χ)] at h
  -- the norm of `χ`, exactly
  have hχnorm : qNormSq χ
      = qNormSq φ ^ 2 * qNormSq ψ - Complex.normSq b * qNormSq φ := by
    have hcross : qInner (((qNormSq φ : ℝ) : ℂ) • ψ) ((-b) • φ)
        = ((-(qNormSq φ * Complex.normSq b) : ℝ) : ℂ) := by
      rw [qInner_smul_left, qInner_smul_right, star_ofReal, hψφ]
      push_cast
      linear_combination (-((qNormSq φ : ℝ) : ℂ)) * mul_star_self_eq b
    rw [hχ, qNormSq_add, qNormSq_smul, qNormSq_smul, Complex.normSq_ofReal,
      Complex.normSq_neg, hcross, Complex.ofReal_re]
    ring
  rw [hχnorm] at hCS
  linarith [hre, hCS]

/-- **The fidelity upper bound.**  If `ψ` splits orthogonally into a near part
`ψN` and a far part `ψF` on which the unitary is close to `−1`, then
`Re⟪ψ, Uψ⟫ ≤ ‖ψ‖‖ψN‖ + ‖ψ‖‖UψF + ψF‖ − ‖ψF‖²`. -/
theorem re_qInner_mulVec_le_of_perp {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {ψN ψF : H → ℂ}
    (horth : qInner ψN ψF = 0) :
    (qInner (ψN + ψF) (U *ᵥ (ψN + ψF))).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq ψN)
        + Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq (U *ᵥ ψF + ψF))
        - qNormSq ψF := by
  have hsplit : qInner (ψN + ψF) (U *ᵥ (ψN + ψF))
      = qInner (ψN + ψF) (U *ᵥ ψN) + qInner (ψN + ψF) (U *ᵥ ψF + ψF)
        - qInner (ψN + ψF) ψF := by
    rw [Matrix.mulVec_add, qInner_add_right, qInner_add_right]
    ring
  have hlast : qInner (ψN + ψF) ψF = ((qNormSq ψF : ℝ) : ℂ) := by
    rw [qInner_add_left, horth, zero_add, qInner_self]
  have h1 : (qInner (ψN + ψF) (U *ᵥ ψN)).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq ψN) := by
    have h := re_qInner_le (ψN + ψF) (U *ᵥ ψN)
    rwa [qNormSq_mulVec hU] at h
  have h2 : (qInner (ψN + ψF) (U *ᵥ ψF + ψF)).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq (U *ᵥ ψF + ψF)) :=
    re_qInner_le _ _
  have hre := congrArg Complex.re hsplit
  rw [hlast] at hre
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- **A projector's range is orthogonal to its complement's range**, on the
same vector.  The form in which the chord-window decomposition enters the
fidelity bound. -/
lemma qInner_mulVec_one_sub_mulVec {P : Matrix H H ℂ} (hP : IsQProjector P)
    (x : H → ℂ) : qInner (P *ᵥ x) ((1 - P) *ᵥ x) = 0 := by
  rw [qInner_mulVec_left, Matrix.mulVec_mulVec, hP.1]
  rw [show P * (1 - P) = 0 from by rw [Matrix.mul_sub, Matrix.mul_one, hP.2,
    sub_self], Matrix.zero_mulVec, qInner_zero_right]

end QuantumQueryComplexity
