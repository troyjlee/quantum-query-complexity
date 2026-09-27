import QuantumQueryComplexity.Quantum.FiniteHilbert
import QuantumQueryComplexity.Spectral
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The real-matrix / complex-vector bridge

The adversary side of this project is real: `advPMOn` is a supremum of L2
operator norms of **real** matrices, and `Spectral.lean` supplies the bilinear
bound `|x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ √(x⬝ᵥx) √(y⬝ᵥy)`.  The quantum side is complex.  The
progress measure of the lower bound lives in between: it is a real matrix `Γ`
contracted against a family of **complex** vectors,

  `∑ x, ∑ y, Γ x y * Re ⟪u x, v y⟫`.

This file proves the one inequality that connects them,

  `|∑ x, ∑ y, Γ x y * Re ⟪u x, v y⟫| ≤ ‖Γ‖ · √(∑ x, ‖u x‖²) · √(∑ y, ‖v y‖²)`,

which is Risk 2 of the plan discharged: no complex operator-norm theory is
needed, and the existing real API is used unchanged.

The proof is the obvious one once the real part is expanded coordinatewise:
`Re ⟪u, v⟫ = ∑ h, (Re uₕ Re vₕ + Im uₕ Im vₕ)`, so the double sum is
`∑ h, (aᵣ(h) ⬝ᵥ Γ *ᵥ bᵣ(h) + aᵢ(h) ⬝ᵥ Γ *ᵥ bᵢ(h))`, a sum over the basis of
**real** bilinear forms.  Bounding each by `Spectral.lean` and applying
Cauchy–Schwarz twice — once to combine the real and imaginary parts at a fixed
basis vector, once to sum over the basis — gives the claim.  Working with the
real part throughout (rather than the complex Gram value and its modulus) is
what keeps this elementary; the progress measure is defined with `Re` for the
same reason.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The real part of the inner product, expanded over the basis. -/
lemma qInner_re (ψ φ : H → ℂ) :
    (qInner ψ φ).re = ∑ h, ((ψ h).re * (φ h).re + (ψ h).im * (φ h).im) := by
  rw [qInner_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [Complex.mul_re]

/-- The squared norm, expanded over the basis. -/
lemma qNormSq_eq_sum_re_im (ψ : H → ℂ) :
    qNormSq ψ = ∑ h, ((ψ h).re * (ψ h).re + (ψ h).im * (ψ h).im) := by
  rw [qNormSq_def]
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_apply (ψ h)

/-- Scaling a state by a real number. -/
lemma qNormSq_real_smul (c : ℝ) (ψ : H → ℂ) :
    qNormSq ((c : ℂ) • ψ) = c ^ 2 * qNormSq ψ := by
  rw [qNormSq_def, qNormSq_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  simp [Complex.normSq_ofReal, sq]

/-! ## The bridge -/

section

variable (Γ : Matrix X X ℝ) (u v : X → (H → ℂ))

/-- The real parts of `u` at a fixed basis vector, as a real vector indexed by
the promise domain. -/
private def reAt (u : X → (H → ℂ)) (h : H) : X → ℝ := fun x => (u x h).re

private def imAt (u : X → (H → ℂ)) (h : H) : X → ℝ := fun x => (u x h).im

private lemma sum_gram_re_eq (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) :
    (∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re)
      = ∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)) := by
  have hexp : ∀ x y, Γ x y * (qInner (u x) (v y)).re
      = ∑ h, (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) := by
    intro x y
    rw [qInner_re, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [reAt, imAt]
    ring
  calc (∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re)
      = ∑ x, ∑ y, ∑ h,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) := by
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hexp x y
    _ = ∑ x, ∑ h, ∑ y,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ h, ∑ x, ∑ y,
          (reAt u h x * Γ x y * reAt v h y + imAt u h x * Γ x y * imAt v h y) :=
        Finset.sum_comm
    _ = ∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib

private lemma sum_reAt_imAt (u : X → (H → ℂ)) :
    (∑ h, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h)))
      = ∑ x, qNormSq (u x) := by
  have h1 : ∀ h : H, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
      = ∑ x, ((u x h).re * (u x h).re + (u x h).im * (u x h).im) := by
    intro h
    simp only [dotProduct, reAt, imAt]
    exact Finset.sum_add_distrib.symm
  rw [Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) => h1 h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (qNormSq_eq_sum_re_im (u x)).symm

/-- Cauchy–Schwarz in two terms, in the square-root form used twice below. -/
private lemma sqrt_mul_add_sqrt_mul_le {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt A * Real.sqrt B + Real.sqrt C * Real.sqrt D
      ≤ Real.sqrt (A + C) * Real.sqrt (B + D) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := ![A, C]) (g := ![B, D]) Finset.univ
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- **The bridge.**  A real matrix contracted against complex vector families is
bounded by its operator norm times the two total squared norms. -/
theorem abs_sum_gram_re_le :
    |∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) := by
  have hnn : ∀ (w : X → (H → ℂ)) (h : H), 0 ≤ (reAt w h) ⬝ᵥ (reAt w h) :=
    fun w h => dotProduct_self_nonneg _
  have hnn' : ∀ (w : X → (H → ℂ)) (h : H), 0 ≤ (imAt w h) ⬝ᵥ (imAt w h) :=
    fun w h => dotProduct_self_nonneg _
  -- at each basis vector, the real and imaginary bilinear forms
  have hstep : ∀ h : H,
      |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)|
        ≤ ‖Γ‖ * (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
            * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) := by
    intro h
    have h1 := abs_dotProduct_mulVec_le Γ (reAt u h) (reAt v h)
    have h2 := abs_dotProduct_mulVec_le Γ (imAt u h) (imAt v h)
    have h3 := sqrt_mul_add_sqrt_mul_le (hnn u h) (hnn v h) (hnn' u h) (hnn' v h)
    have h4 : |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)|
        ≤ ‖Γ‖ * Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h)) * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h))
          + ‖Γ‖ * Real.sqrt ((imAt u h) ⬝ᵥ (imAt u h))
            * Real.sqrt ((imAt v h) ⬝ᵥ (imAt v h)) :=
      (abs_add_le _ _).trans (add_le_add h1 h2)
    have hΓ : 0 ≤ ‖Γ‖ := norm_nonneg _
    nlinarith [h3, h4, hΓ]
  -- sum over the basis
  calc |∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re|
      = |∑ h, ((reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h))| := by
        rw [sum_gram_re_eq]
    _ ≤ ∑ h, |(reAt u h) ⬝ᵥ Γ *ᵥ (reAt v h) + (imAt u h) ⬝ᵥ Γ *ᵥ (imAt v h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, ‖Γ‖ * (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
          * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) :=
        Finset.sum_le_sum fun h _ => hstep h
    _ = ‖Γ‖ * ∑ h, (Real.sqrt ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h))
          * Real.sqrt ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h))) := by
        rw [Finset.mul_sum]
    _ ≤ ‖Γ‖ * (Real.sqrt (∑ h, ((reAt u h) ⬝ᵥ (reAt u h) + (imAt u h) ⬝ᵥ (imAt u h)))
          * Real.sqrt (∑ h, ((reAt v h) ⬝ᵥ (reAt v h) + (imAt v h) ⬝ᵥ (imAt v h)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Real.sum_sqrt_mul_sqrt_le _
          (fun h => add_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))
          (fun h => add_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))
    _ = ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) := by
        rw [sum_reAt_imAt, sum_reAt_imAt, mul_assoc]

end

end QuantumQueryComplexity
