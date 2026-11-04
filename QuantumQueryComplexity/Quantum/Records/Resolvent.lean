import Mathlib.Analysis.Matrix.Order

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The resolvent `(I + H/R)⁻¹` of a positive semidefinite matrix

For a positive semidefinite `H` and `R > 0`, the matrix `I + H/R` is positive definite, and its
inverse `resolvent R H = (I + H/R)⁻¹` is the averaging operator of conditional resampling
(Cornelissen–Gilani–Zhou, Section 4.2, equation (4.6)).  This file proves the facts about it
that use only positivity of `H`:

* it is Hermitian and `0 ≤ F² ≤ F ≤ I` (part of Lemma 4.2, (4.7));
* inversion reverses order: `H ≤ H'` gives `F' ≤ F` ((4.8));
* the commutator identity `[B, F] = R⁻¹ F [H, B] F` ((4.9));
* the energy bound `F H F ≤ (R/4) I` ((4.10));
* `H v = 0` gives `F v = v`, and `H F = R (I − F)`.

The facts that need the structure of conditional expectations (preservation of `|ρ⟩` and the
infinity-norm contraction) are in `Records/Resampling.lean`.

The order is Mathlib's Loewner order on matrices, scoped to `MatrixOrder`.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A]

/-- **The averaging operator** `F = (I + H/R)⁻¹`. -/
noncomputable def resolvent (R : ℝ) (H : Matrix X X ℂ) : Matrix X X ℂ :=
  (1 + ((R⁻¹ : ℝ) : ℂ) • H)⁻¹

variable {R : ℝ} {H H' : Matrix X X ℂ}

private lemma ofReal_inv_nonneg (hR : 0 < R) : (0 : ℂ) ≤ ((R⁻¹ : ℝ) : ℂ) :=
  Complex.zero_le_real.mpr (inv_nonneg.mpr hR.le)

private lemma ofReal_mul_ofReal_inv (hR : 0 < R) : (R : ℂ) * ((R⁻¹ : ℝ) : ℂ) = 1 := by
  rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne')]

private lemma posDef_one_add_smul (hR : 0 < R) (hH : H.PosSemidef) :
    (1 + ((R⁻¹ : ℝ) : ℂ) • H).PosDef :=
  PosDef.one.add_posSemidef (hH.smul (ofReal_inv_nonneg hR))

private lemma isUnit_det_one_add_smul (hR : 0 < R) (hH : H.PosSemidef) :
    IsUnit (1 + ((R⁻¹ : ℝ) : ℂ) • H).det :=
  (isUnit_iff_isUnit_det _).mp (posDef_one_add_smul hR hH).isUnit

/-- `I + H/R` is invertible, with inverse `resolvent R H`. -/
theorem one_add_smul_mul_resolvent (hR : 0 < R) (hH : H.PosSemidef) :
    (1 + ((R⁻¹ : ℝ) : ℂ) • H) * resolvent R H = 1 :=
  mul_nonsing_inv _ (isUnit_det_one_add_smul hR hH)

theorem resolvent_mul_one_add_smul (hR : 0 < R) (hH : H.PosSemidef) :
    resolvent R H * (1 + ((R⁻¹ : ℝ) : ℂ) • H) = 1 :=
  nonsing_inv_mul _ (isUnit_det_one_add_smul hR hH)

theorem resolvent_isHermitian (hR : 0 < R) (hH : H.PosSemidef) :
    (resolvent R H).IsHermitian :=
  (posDef_one_add_smul hR hH).isHermitian.inv

theorem resolvent_posDef (hR : 0 < R) (hH : H.PosSemidef) : (resolvent R H).PosDef :=
  (posDef_one_add_smul hR hH).inv

/-- `I − F = R⁻¹ H F`. -/
private lemma one_sub_resolvent (hR : 0 < R) (hH : H.PosSemidef) :
    1 - resolvent R H = ((R⁻¹ : ℝ) : ℂ) • (H * resolvent R H) := by
  have h := one_add_smul_mul_resolvent hR hH
  rw [add_mul, one_mul, smul_mul_assoc] at h
  rw [← h, add_sub_cancel_left]

theorem resolvent_sq_nonneg (hR : 0 < R) (hH : H.PosSemidef) :
    0 ≤ resolvent R H * resolvent R H := by
  have h := posSemidef_conjTranspose_mul_self (resolvent R H)
  rw [(resolvent_isHermitian hR hH).eq] at h
  exact h.nonneg

/-- `F − F² = R⁻¹ F H F`. -/
private lemma resolvent_sub_sq (hR : 0 < R) (hH : H.PosSemidef) :
    resolvent R H - resolvent R H * resolvent R H
      = ((R⁻¹ : ℝ) : ℂ) • (resolvent R H * H * resolvent R H) := by
  rw [show resolvent R H - resolvent R H * resolvent R H
      = resolvent R H * (1 - resolvent R H) by noncomm_ring, one_sub_resolvent hR hH,
    mul_smul_comm, mul_assoc]

private lemma posSemidef_resolvent_sub_sq (hR : 0 < R) (hH : H.PosSemidef) :
    (resolvent R H - resolvent R H * resolvent R H).PosSemidef := by
  rw [resolvent_sub_sq hR hH]
  refine PosSemidef.smul ?_ (ofReal_inv_nonneg hR)
  have h := hH.conjTranspose_mul_mul_same (resolvent R H)
  rwa [(resolvent_isHermitian hR hH).eq] at h

theorem resolvent_sq_le (hR : 0 < R) (hH : H.PosSemidef) :
    resolvent R H * resolvent R H ≤ resolvent R H :=
  le_iff.mpr (posSemidef_resolvent_sub_sq hR hH)

theorem resolvent_le_one (hR : 0 < R) (hH : H.PosSemidef) : resolvent R H ≤ 1 := by
  rw [le_iff]
  set F := resolvent R H
  have hFh : F.IsHermitian := resolvent_isHermitian hR hH
  have h1 : (1 - F).IsHermitian := isHermitian_one.sub hFh
  have h2 := posSemidef_conjTranspose_mul_self (1 - F)
  rw [h1.eq] at h2
  have key : 1 - F = (F - F * F) + (1 - F) * (1 - F) := by noncomm_ring
  rw [key]
  exact (posSemidef_resolvent_sub_sq hR hH).add h2

/-- **Inversion reverses order**: more conditional variance means more averaging. -/
theorem resolvent_le_resolvent (hR : 0 < R) (hH : H.PosSemidef) (hHH' : H ≤ H') :
    resolvent R H' ≤ resolvent R H := by
  rw [le_iff] at hHH' ⊢
  have hH' : H'.PosSemidef := by simpa using hH.add hHH'
  set c : ℂ := ((R⁻¹ : ℝ) : ℂ)
  set F := resolvent R H
  set F' := resolvent R H'
  set D : Matrix X X ℂ := c • (H' - H) with hD
  have hD_psd : D.PosSemidef := hHH'.smul (ofReal_inv_nonneg hR)
  have hFG : F * (1 + c • H) = 1 := resolvent_mul_one_add_smul hR hH
  have hGF : (1 + c • H) * F = 1 := one_add_smul_mul_resolvent hR hH
  have hF'G' : F' * (1 + c • H') = 1 := resolvent_mul_one_add_smul hR hH'
  have hG'F' : (1 + c • H') * F' = 1 := one_add_smul_mul_resolvent hR hH'
  have hDG : D = (1 + c • H') - (1 + c • H) := by
    rw [hD, smul_sub]; abel
  -- `F − F' = F' D F` and `F = F' + F D F'`
  have e1 : F - F' = F' * D * F := by
    rw [hDG, mul_sub, sub_mul, hF'G', one_mul, mul_assoc, hGF, mul_one]
  have e2 : F = F' + F * D * F' := by
    rw [hDG, mul_sub, sub_mul, hFG, one_mul, mul_assoc, hG'F', mul_one]; abel
  have e3 : F - F' = F' * D * F' + (D * F')ᴴ * F * (D * F') := by
    rw [conjTranspose_mul, (resolvent_isHermitian hR hH').eq, hD_psd.isHermitian.eq, e1]
    conv_lhs => rw [e2]
    noncomm_ring
  rw [e3]
  refine PosSemidef.add ?_ ?_
  · have h := hD_psd.conjTranspose_mul_mul_same F'
    rwa [(resolvent_isHermitian hR hH').eq] at h
  · exact (resolvent_posDef hR hH).posSemidef.conjTranspose_mul_mul_same _

theorem commute_resolvent (hR : 0 < R) (hH : H.PosSemidef) : Commute H (resolvent R H) := by
  have hFG := resolvent_mul_one_add_smul hR hH
  have hGF := one_add_smul_mul_resolvent hR hH
  have hHG : H * (1 + ((R⁻¹ : ℝ) : ℂ) • H) = (1 + ((R⁻¹ : ℝ) : ℂ) • H) * H := by
    rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  unfold Commute SemiconjBy
  calc H * resolvent R H
      = (resolvent R H * (1 + ((R⁻¹ : ℝ) : ℂ) • H)) * H * resolvent R H := by
        rw [hFG, one_mul]
    _ = resolvent R H * (H * (1 + ((R⁻¹ : ℝ) : ℂ) • H)) * resolvent R H := by
        rw [hHG]; noncomm_ring
    _ = resolvent R H * H := by
        rw [mul_assoc, mul_assoc, hGF, mul_one]

/-- `H F = R (I − F)`. -/
theorem mul_resolvent (hR : 0 < R) (hH : H.PosSemidef) :
    H * resolvent R H = (R : ℂ) • (1 - resolvent R H) := by
  rw [one_sub_resolvent hR hH, smul_smul, ofReal_mul_ofReal_inv hR, one_smul]

/-- **The commutator identity** `[B, F] = R⁻¹ F [H, B] F`. -/
theorem commutator_resolvent (hR : 0 < R) (hH : H.PosSemidef) (B : Matrix X X ℂ) :
    B * resolvent R H - resolvent R H * B
      = ((R⁻¹ : ℝ) : ℂ) • (resolvent R H * (H * B - B * H) * resolvent R H) := by
  have hFG := resolvent_mul_one_add_smul hR hH
  have hGF := one_add_smul_mul_resolvent hR hH
  have h1 : B * resolvent R H - resolvent R H * B
      = resolvent R H * ((1 + ((R⁻¹ : ℝ) : ℂ) • H) * B - B * (1 + ((R⁻¹ : ℝ) : ℂ) • H))
        * resolvent R H := by
    rw [mul_sub, sub_mul, ← mul_assoc, hFG, one_mul, mul_assoc, mul_assoc, hGF, mul_one]
  have h2 : (1 + ((R⁻¹ : ℝ) : ℂ) • H) * B - B * (1 + ((R⁻¹ : ℝ) : ℂ) • H)
      = ((R⁻¹ : ℝ) : ℂ) • (H * B - B * H) := by
    rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
  rw [h1, h2, mul_smul_comm, smul_mul_assoc]

/-- **The energy bound** `F H F ≤ (R/4) I`, from `u/(1 + u/R)² ≤ R/4` for `u ≥ 0`. -/
theorem resolvent_mul_mul_resolvent_le (hR : 0 < R) (hH : H.PosSemidef) :
    resolvent R H * H * resolvent R H ≤ ((R / 4 : ℝ) : ℂ) • (1 : Matrix X X ℂ) := by
  rw [le_iff]
  set F := resolvent R H
  set M : Matrix X X ℂ := F - (1 / 2 : ℂ) • 1 with hM
  have hFh : Fᴴ = F := resolvent_isHermitian hR hH
  have hMh : Mᴴ = M := by
    simp [hM, hFh]
  have hFHF : F * H * F = (R : ℂ) • (F - F * F) := by
    rw [mul_assoc, mul_resolvent hR hH, mul_smul_comm, mul_sub, mul_one]
  have key : ((R / 4 : ℝ) : ℂ) • (1 : Matrix X X ℂ) - F * H * F = (R : ℂ) • (Mᴴ * M) := by
    rw [hFHF, hMh, hM]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    push_cast
    module
  rw [key]
  exact (posSemidef_conjTranspose_mul_self M).smul (Complex.zero_le_real.mpr hR.le)

/-- A vector annihilated by `H` is fixed by `F`. -/
theorem resolvent_mulVec_of_mulVec_eq_zero (hR : 0 < R) (hH : H.PosSemidef) {v : X → ℂ}
    (hv : H *ᵥ v = 0) : resolvent R H *ᵥ v = v := by
  have hGv : (1 + ((R⁻¹ : ℝ) : ℂ) • H) *ᵥ v = v := by
    rw [add_mulVec, one_mulVec, smul_mulVec, hv, smul_zero, add_zero]
  conv_lhs => rw [← hGv, mulVec_mulVec, resolvent_mul_one_add_smul hR hH, one_mulVec]

end QuantumQueryComplexity
