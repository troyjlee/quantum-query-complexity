import QuantumQueryComplexity.Quantum.Amplitude.Kernel
import QuantumQueryComplexity.Quantum.Routine
set_option linter.style.header false

/-!
# The normalized finite Fourier matrix

For `M ≥ 1`, on `Fin M`:

    fourierMat M y c = (1/√M) · exp(+2πi·y·c/M)            (forward, **positive** exponent)
    (fourierMat M)ᴴ y c = (1/√M) · exp(−2πi·y·c/M)          (inverse, negative exponent)

`fourierMat_mem_unitaryGroup` proves unitarity from the root-of-unity sum
`∑_{y<M} e(y·d/M) = 0` for an integer `0 < |d| < M` (no division by `1 − e(d/M)` without the
nonvanishing).  The Fourier transform is an input-independent unitary: it costs no queries
in this model, and no gate decomposition is claimed.

The inverse transform of a pure phase ramp is the phase-estimation kernel
(`fourierMat_conjTranspose_mulVec_ramp`); with Parseval this gives
`sum_normSq_peKernel : ∑_y |k(φ − y/M)|² = 1`, and with `bad_mass_le`

    five_sixths_le_good_mass :  5/6 ≤ ∑_{y : circDist(φ − y/M) ≤ 4/M} |k(φ − y/M)|²

(`three_quarters_le_good_mass` is the compatibility weakening).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix Finset

/-- **The normalized Fourier matrix**, forward sign `+`. -/
noncomputable def fourierMat (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun y c => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((y : ℕ) * (c : ℕ) / M)

lemma fourierMat_apply (M : ℕ) (y c : Fin M) :
    fourierMat M y c = (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((y : ℕ) * (c : ℕ) / M) := rfl

/-- The inverse matrix entry, with the **negative** exponent. -/
lemma fourierMat_conjTranspose_apply (M : ℕ) (y c : Fin M) :
    (fourierMat M)ᴴ y c = (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 (-((c : ℕ) * (y : ℕ) / M)) := by
  rw [Matrix.conjTranspose_apply, fourierMat_apply, star_mul', star_cexp1]
  simp

/-- **The root-of-unity sum** vanishes off the diagonal. -/
lemma sum_cexp1_eq_zero {M : ℕ} {d : ℤ} (hd : d ≠ 0) (hdM : |d| < M) :
    ∑ y ∈ range M, cexp1 ((y : ℕ) * ((d : ℝ) / M)) = 0 := by
  have hM : (M : ℝ) ≠ 0 := by
    have : (0 : ℤ) < M := lt_of_le_of_lt (abs_nonneg d) hdM
    exact_mod_cast this.ne'
  set z := cexp1 ((d : ℝ) / M) with hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, cexp1, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : (d : ℝ) / M = n := by
      have h2 : ((2 * Real.pi * ((d : ℝ) / M) : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
        have hI : Complex.I ≠ 0 := Complex.I_ne_zero
        apply mul_left_cancel₀ hI
        rw [hn]; push_cast; ring
      have h3 := Complex.ofReal_injective h2
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      exact mul_left_cancel₀ hpi h3
    have hdn : d = n * M := by
      have : (d : ℝ) = n * M := by rw [← hre]; field_simp
      exact_mod_cast this
    rcases eq_or_ne n 0 with h0 | h0
    · exact hd (by rw [hdn, h0, zero_mul])
    · have : (M : ℤ) ≤ |d| := by
        rw [hdn, abs_mul, Nat.abs_cast]
        exact le_mul_of_one_le_left (Nat.cast_nonneg M) (Int.one_le_abs h0)
      omega
  have hzM : z ^ M = 1 := by
    rw [hz, ← cexp1_nat_mul, show (M : ℝ) * ((d : ℝ) / M) = d by field_simp, cexp1_int]
  have hgeom := geom_sum_mul z M
  rw [hzM, sub_self] at hgeom
  have hsum : ∑ i ∈ range M, z ^ i = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz1)
  rw [← hsum]
  exact sum_congr rfl fun y _ => cexp1_nat_mul y _

/-- **The normalized Fourier matrix is unitary.** -/
theorem fourierMat_mem_unitaryGroup {M : ℕ} (hM : 0 < M) :
    fourierMat M ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext c c'
  rw [Matrix.mul_apply]
  simp_rw [fourierMat_conjTranspose_apply, fourierMat_apply]
  have hterm : ∀ y : Fin M,
      (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 (-(((y : ℕ) : ℝ) * (c : ℕ) / M))
        * ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 (((y : ℕ) : ℝ) * (c' : ℕ) / M))
      = (1 / (M : ℂ)) * cexp1 (((y : ℕ) : ℝ) * ((((c' : ℕ) : ℤ) - (c : ℕ) : ℤ) / M)) := by
    intro y
    have hs : ((((Real.sqrt M)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) = 1 / (M : ℂ) := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
      push_cast; rw [one_div]
    rw [mul_mul_mul_comm, hs, ← cexp1_add]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun y => cexp1 ((y : ℝ) * ((((c' : ℕ) : ℤ) - (c : ℕ) : ℤ) / M))) M]
  by_cases hcc : c = c'
  · subst hcc
    simp only [sub_self, Int.cast_zero, zero_div, mul_zero, cexp1_zero, sum_const, card_range,
      nsmul_eq_mul, mul_one, Matrix.one_apply_eq]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  · rw [Matrix.one_apply_ne hcc]
    have hd : (((c' : ℕ) : ℤ) - (c : ℕ)) ≠ 0 := by
      intro h
      exact hcc (Fin.ext (by omega))
    have hdM : |((c' : ℕ) : ℤ) - (c : ℕ)| < M := by
      rw [abs_lt]; constructor <;> omega
    rw [sum_cexp1_eq_zero hd hdM, mul_zero]

/-- **The inverse Fourier transform of a phase ramp is the kernel.** -/
theorem fourierMat_conjTranspose_mulVec_ramp {M : ℕ} (hM : 0 < M) (φ : ℝ) (y : Fin M) :
    ((fourierMat M)ᴴ *ᵥ fun c : Fin M => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((c : ℕ) * φ)) y
      = peKernel M (φ - (y : ℕ) / M) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [Matrix.mulVec, dotProduct, peKernel, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range (fun c => 1 / (M : ℂ) * cexp1 ((c : ℝ) * (φ - (y : ℕ) / M))) M]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : ((((Real.sqrt M)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) = 1 / (M : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
    push_cast; rw [one_div]
  rw [fourierMat_conjTranspose_apply, mul_mul_mul_comm, hs, ← cexp1_add]
  congr 2
  ring

/-- **Parseval for the kernel**: the phase-estimation outcome law is normalized. -/
theorem sum_normSq_peKernel {M : ℕ} (hM : 0 < M) (φ : ℝ) :
    ∑ y : Fin M, Complex.normSq (peKernel M (φ - (y : ℕ) / M)) = 1 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hU : (fourierMat M)ᴴ ∈ Matrix.unitaryGroup (Fin M) ℂ :=
    conjTranspose_mem_qUnitary (fourierMat_mem_unitaryGroup hM)
  have h := qNormSq_mulVec hU
    (fun c : Fin M => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((c : ℕ) * φ))
  rw [qNormSq_def, qNormSq_def] at h
  rw [show (∑ y : Fin M, Complex.normSq (peKernel M (φ - (y : ℕ) / M)))
      = ∑ y : Fin M, Complex.normSq (((fourierMat M)ᴴ *ᵥ
          fun c : Fin M => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((c : ℕ) * φ)) y) from
    Finset.sum_congr rfl fun y _ => by rw [fourierMat_conjTranspose_mulVec_ramp hM], h]
  have hone : ∀ c : Fin M,
      Complex.normSq ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((c : ℕ) * φ)) = 1 / (M : ℝ) := by
    intro c
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, norm_cexp1,
      ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg M)]
    simp
  rw [Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The concentration bound**: the grid points within circular distance `4/M` of the
phase carry at least `5/6` of the mass — total mass one (`sum_normSq_peKernel`) minus the
bad mass `≤ 1/6` (`bad_mass_le`); the non-strict good event and the strict bad event are
complementary. -/
theorem five_sixths_le_good_mass {M : ℕ} (hM : 0 < M) (φ : ℝ) :
    5 / 6 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then Complex.normSq (peKernel M (φ - (y : ℕ) / M)) else 0 := by
  have htot := sum_normSq_peKernel hM φ
  have hbad := bad_mass_le hM φ
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range
    (fun y => if 4 / (M : ℝ) < circDist (φ - (y : ℝ) / M)
      then Complex.normSq (peKernel M (φ - (y : ℝ) / M)) else 0) M] at hbad
  have hsplit : ∀ y : Fin M, Complex.normSq (peKernel M (φ - (y : ℕ) / M))
      = (if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
          then Complex.normSq (peKernel M (φ - (y : ℕ) / M)) else 0)
        + (if 4 / (M : ℝ) < circDist (φ - ((y : ℕ) : ℝ) / M)
          then Complex.normSq (peKernel M (φ - ((y : ℕ) : ℝ) / M)) else 0) := by
    intro y
    by_cases h : circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (not_le.mp h), zero_add]
  rw [Finset.sum_congr rfl fun y _ => hsplit y, Finset.sum_add_distrib] at htot
  linarith

/-- The `3/4` form, kept for compatibility: a weakening of `five_sixths_le_good_mass`. -/
theorem three_quarters_le_good_mass {M : ℕ} (hM : 0 < M) (φ : ℝ) :
    3 / 4 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then Complex.normSq (peKernel M (φ - (y : ℕ) / M)) else 0 :=
  le_trans (by norm_num) (five_sixths_le_good_mass hM φ)

end QuantumQueryComplexity
