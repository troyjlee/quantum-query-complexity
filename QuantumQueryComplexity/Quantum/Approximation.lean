import QuantumQueryComplexity.Quantum.Measurement
import QuantumQueryComplexity.Quantum.Amplitude.Marker
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Norm-error calculus

Vector errors, as opposed to probability errors: a probability error `e` generally becomes a
vector error of order `√e`, and the two are kept distinct throughout.

* `qNorm ψ = √(qNormSq ψ)`, with the triangle inequality, homogeneity and unitary invariance;
  vectors are **unnormalized** throughout, so branches of probability zero need no case split.
* `qNorm_restrict_le`, `sqrt_qProb_le_add` — a measurement is a contraction: amplitudes of an
  outcome differ by at most the distance of the states.
* `qNorm_mulVec_sub_le` — the telescoping estimate for a composition of an exact and an
  approximate operator.
* `IsApproxRefl R s D β` — **the clean-ancilla approximate-reflection contract**: `R` fixes
  the designated unit vector `s` *exactly*, and on the allowed set `D` (logical subspace,
  fresh ancillas blank; made explicit by the caller) it is within `β·‖w − ⟨s,w⟩s‖` of the
  exact reflection `2|s⟩⟨s| − 1`.  The error is proportional to the component orthogonal to
  `s`; this is what the recursion exploits.
* `IsApproxRefl.conj` — conjugating by a unitary `A` gives an approximate reflection about
  `A s` **with the same `β`**: the errors of `A` itself cancel.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The norm of a vector. -/
noncomputable def qNorm (ψ : H → ℂ) : ℝ := Real.sqrt (qNormSq ψ)

lemma qNorm_nonneg (ψ : H → ℂ) : 0 ≤ qNorm ψ := Real.sqrt_nonneg _

lemma qNorm_sq (ψ : H → ℂ) : qNorm ψ ^ 2 = qNormSq ψ := Real.sq_sqrt (qNormSq_nonneg ψ)

lemma qNorm_mul_self (ψ : H → ℂ) : qNorm ψ * qNorm ψ = qNormSq ψ :=
  Real.mul_self_sqrt (qNormSq_nonneg ψ)

lemma qNorm_eq_one {ψ : H → ℂ} (h : IsQState ψ) : qNorm ψ = 1 := by
  rw [qNorm, h, Real.sqrt_one]

@[simp] lemma qNorm_zero : qNorm (0 : H → ℂ) = 0 := by
  rw [qNorm, qNormSq_eq_zero_iff.mpr rfl, Real.sqrt_zero]

lemma qNorm_le_of_qNormSq_le {ψ : H → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : qNormSq ψ ≤ c ^ 2) :
    qNorm ψ ≤ c := by
  rw [qNorm]
  exact (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hc))

lemma qNorm_add_le (ψ φ : H → ℂ) : qNorm (ψ + φ) ≤ qNorm ψ + qNorm φ :=
  sqrt_qNormSq_add_le ψ φ

lemma qNorm_smul (c : ℂ) (ψ : H → ℂ) : qNorm (c • ψ) = ‖c‖ * qNorm ψ := by
  rw [qNorm, qNormSq_smul, Real.sqrt_mul (Complex.normSq_nonneg c), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg c)]
  rfl

lemma qNorm_neg (ψ : H → ℂ) : qNorm (-ψ) = qNorm ψ := by
  have : -ψ = (-1 : ℂ) • ψ := by rw [neg_one_smul]
  rw [this, qNorm_smul, norm_neg, norm_one, one_mul]

lemma qNorm_sub_le (ψ φ : H → ℂ) : qNorm (ψ - φ) ≤ qNorm ψ + qNorm φ := by
  rw [sub_eq_add_neg]
  exact (qNorm_add_le _ _).trans (by rw [qNorm_neg])

lemma qNorm_sub_comm (ψ φ : H → ℂ) : qNorm (ψ - φ) = qNorm (φ - ψ) := by
  rw [← qNorm_neg, neg_sub]

/-- The reverse triangle inequality. -/
lemma qNorm_sub_le_qNorm_add (ψ φ : H → ℂ) : qNorm ψ - qNorm φ ≤ qNorm (ψ + φ) := by
  have h := qNorm_add_le (ψ + φ) (-φ)
  rw [add_neg_cancel_right, qNorm_neg] at h
  linarith

lemma qNorm_le_add_sub (ψ φ : H → ℂ) : qNorm ψ ≤ qNorm φ + qNorm (ψ - φ) := by
  have h := qNorm_add_le φ (ψ - φ)
  rwa [add_sub_cancel] at h

lemma qNorm_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (ψ : H → ℂ) :
    qNorm (U *ᵥ ψ) = qNorm ψ := by
  rw [qNorm, qNormSq_mulVec hU, qNorm]

/-- Cauchy–Schwarz. -/
lemma norm_qInner_le (ψ φ : H → ℂ) : ‖qInner ψ φ‖ ≤ qNorm ψ * qNorm φ :=
  qInner_norm_le ψ φ

/-- **Pythagoras for the component orthogonal to a unit vector.** -/
lemma qNormSq_sub_proj {ψ : H → ℂ} (hψ : IsQState ψ) (ν : H → ℂ) :
    qNormSq (ν - qInner ψ ν • ψ) = qNormSq ν - Complex.normSq (qInner ψ ν) := by
  have h : ν - qInner ψ ν • ψ = ν + (-qInner ψ ν) • ψ := by rw [neg_smul, sub_eq_add_neg]
  rw [h, qNormSq_add, qNormSq_smul, hψ, qInner_smul_right, Complex.normSq_neg, ← qInner_conj ψ ν]
  have : (-qInner ψ ν * star (qInner ψ ν)).re = -Complex.normSq (qInner ψ ν) := by
    rw [neg_mul, Complex.neg_re, Complex.star_def, Complex.mul_conj]
    simp
  rw [this]
  ring

lemma qNorm_sub_proj_le {ψ : H → ℂ} (hψ : IsQState ψ) (ν : H → ℂ) :
    qNorm (ν - qInner ψ ν • ψ) ≤ qNorm ν := by
  refine Real.sqrt_le_sqrt ?_
  rw [qNormSq_sub_proj hψ]
  linarith [Complex.normSq_nonneg (qInner ψ ν)]

/-! ## Measurements are contractions -/

section Measure

variable {O : Type} [Fintype O] [DecidableEq O]

lemma qRestrict_sub (rd : H → O) (o : O) (ψ φ : H → ℂ) :
    qRestrict rd o (ψ - φ) = qRestrict rd o ψ - qRestrict rd o φ := by
  funext h
  simp only [qRestrict, Pi.sub_apply]
  split_ifs <;> simp

lemma qNorm_qRestrict_le (rd : H → O) (o : O) (ψ : H → ℂ) :
    qNorm (qRestrict rd o ψ) ≤ qNorm ψ := by
  rw [qNorm, qNorm, ← qProb_eq_qNormSq_qRestrict]
  exact Real.sqrt_le_sqrt (qProb_le_qNormSq rd ψ o)

/-- **Amplitudes of an outcome differ by at most the distance of the states.** -/
theorem sqrt_qProb_le_add (rd : H → O) (o : O) (ψ φ : H → ℂ) :
    Real.sqrt (qProb rd ψ o) ≤ Real.sqrt (qProb rd φ o) + qNorm (ψ - φ) := by
  rw [qProb_eq_qNormSq_qRestrict, qProb_eq_qNormSq_qRestrict]
  have h := qNorm_le_add_sub (qRestrict rd o ψ) (qRestrict rd o φ)
  rw [← qRestrict_sub] at h
  exact h.trans (add_le_add_right (qNorm_qRestrict_le rd o _) _)

end Measure

/-! ## Compositions -/

/-- **Telescoping**: replacing `V₁, V₂` by `U₁, U₂` (with `U₁` unitary) costs the two
individual errors. -/
theorem qNorm_mulVec_sub_le {U₁ : Matrix H H ℂ} (hU₁ : U₁ ∈ Matrix.unitaryGroup H ℂ)
    (U₂ V₁ V₂ : Matrix H H ℂ) (ψ : H → ℂ) :
    qNorm ((U₁ * U₂) *ᵥ ψ - (V₁ * V₂) *ᵥ ψ)
      ≤ qNorm (U₂ *ᵥ ψ - V₂ *ᵥ ψ) + qNorm (U₁ *ᵥ (V₂ *ᵥ ψ) - V₁ *ᵥ (V₂ *ᵥ ψ)) := by
  have hsplit : (U₁ * U₂) *ᵥ ψ - (V₁ * V₂) *ᵥ ψ
      = U₁ *ᵥ (U₂ *ᵥ ψ - V₂ *ᵥ ψ) + (U₁ *ᵥ (V₂ *ᵥ ψ) - V₁ *ᵥ (V₂ *ᵥ ψ)) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  rw [hsplit]
  exact (qNorm_add_le _ _).trans (by rw [qNorm_mulVec hU₁])

/-! ## The approximate-reflection contract -/

/-- **A `β`-approximate reflection about `s` on the allowed set `D`.** -/
structure IsApproxRefl (R : Matrix H H ℂ) (s : H → ℂ) (D : Set (H → ℂ)) (β : ℝ) : Prop where
  /-- The designated vector is fixed exactly. -/
  fix : R *ᵥ s = s
  /-- On allowed vectors the error is proportional to the component orthogonal to `s`. -/
  near : ∀ w ∈ D, qNorm (R *ᵥ w - stateRefl s *ᵥ w) ≤ β * qNorm (w - qInner s w • s)

/-- The exact reflection is a `0`-approximate reflection, on everything. -/
lemma isApproxRefl_stateRefl {s : H → ℂ} (hs : IsQState s) :
    IsApproxRefl (stateRefl s) s Set.univ 0 where
  fix := by
    rw [stateRefl_mulVec, qInner_self, hs]
    simp only [Complex.ofReal_one, mul_one]
    rw [two_smul, add_sub_cancel_right]
  near := fun w _ => by rw [sub_self, qNorm_zero, zero_mul]

/-- **Conjugation keeps `β`.**  For a unitary `A`, `A R A†` is a `β`-approximate reflection
about `A s`, on the vectors whose preimage is allowed: the errors of `A` cancel. -/
theorem IsApproxRefl.conj {R : Matrix H H ℂ} {s : H → ℂ} {D : Set (H → ℂ)} {β : ℝ}
    (h : IsApproxRefl R s D β) {A : Matrix H H ℂ} (hA : A ∈ Matrix.unitaryGroup H ℂ) :
    IsApproxRefl (A * R * Aᴴ) (A *ᵥ s) {χ | Aᴴ *ᵥ χ ∈ D} β where
  fix := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec s Aᴴ A, conjTranspose_mul_self_of_unitary hA, Matrix.one_mulVec, h.fix]
  near := fun χ hχ => by
    have hAH : Aᴴ ∈ Matrix.unitaryGroup H ℂ := conjTranspose_mem_qUnitary hA
    have hAA : A * Aᴴ = 1 := by
      have := conjTranspose_mul_self_of_unitary hAH
      rwa [Matrix.conjTranspose_conjTranspose] at this
    have hrefl : stateRefl (A *ᵥ s) *ᵥ χ = A *ᵥ (stateRefl s *ᵥ (Aᴴ *ᵥ χ)) := by
      rw [stateRefl_mulVec, stateRefl_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, qInner_mulVec_left]
    have hin : qInner (A *ᵥ s) χ = qInner s (Aᴴ *ᵥ χ) := qInner_mulVec_left A s χ
    have hL : (A * R * Aᴴ) *ᵥ χ - stateRefl (A *ᵥ s) *ᵥ χ
        = A *ᵥ (R *ᵥ (Aᴴ *ᵥ χ) - stateRefl s *ᵥ (Aᴴ *ᵥ χ)) := by
      rw [hrefl, Matrix.mulVec_sub, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
    have hR : χ - qInner (A *ᵥ s) χ • (A *ᵥ s)
        = A *ᵥ (Aᴴ *ᵥ χ - qInner s (Aᴴ *ᵥ χ) • s) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec,
        hin]
    rw [hL, hR, qNorm_mulVec hA, qNorm_mulVec hA]
    exact h.near _ hχ

end QuantumQueryComplexity
