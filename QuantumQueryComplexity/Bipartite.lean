import QuantumQueryComplexity.Defs
set_option linter.style.header false

/-!
# Bipartite support structure of adversary matrices

An adversary matrix `N` for `g` vanishes on same-colored pairs (`g u = g v`),
so it maps vectors supported on one color class into the other class.
Consequently an eigenvector with nonzero eigenvalue must have nonzero
restriction to *both* color classes (`brestrict_ne_zero`,
`IsAdvMatrix.exists_eigenvector_support`).  This is the nonvanishing input to
the `≥` direction of the composed-matrix norm formula (HLŠ Lemma 16).
-/

namespace QuantumQueryComplexity

open Matrix

variable {U : Type*} [Fintype U]

/-- Restriction of a vector to a color class of the coloring `χ`. -/
def brestrict (χ : U → Bool) (b : Bool) (w : U → ℝ) : U → ℝ :=
  fun u => if χ u = b then w u else 0

@[simp] lemma brestrict_apply (χ : U → Bool) (b : Bool) (w : U → ℝ) (u : U) :
    brestrict χ b w u = if χ u = b then w u else 0 := rfl

lemma brestrict_add_not (χ : U → Bool) (b : Bool) (w : U → ℝ) :
    brestrict χ b w + brestrict χ (!b) w = w := by
  funext u
  simp only [Pi.add_apply, brestrict_apply]
  cases hb : χ u <;> cases b <;> simp

/-- A matrix vanishing on same-colored pairs maps a `b`-supported vector to a
`!b`-supported one, with the values of the full product. -/
lemma mulVec_brestrict {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) (w : U → ℝ) (b : Bool) :
    M *ᵥ brestrict χ b w = brestrict χ (!b) (M *ᵥ w) := by
  funext u
  simp only [Matrix.mulVec, dotProduct, brestrict_apply, mul_ite, mul_zero]
  by_cases hu : χ u = b
  · rw [if_neg (by rw [hu]; cases b <;> simp)]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : χ v = b
    · rw [if_pos hv, hM u v (hu.trans hv.symm), zero_mul]
    · rw [if_neg hv]
  · have hu' : χ u = !b := by cases hcu : χ u <;> cases b <;> simp_all
    rw [if_pos hu']
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : χ v = b
    · rw [if_pos hv]
    · have hv' : χ v = χ u := by
        cases hcv : χ v <;> cases hcu : χ u <;> cases b <;> simp_all
      rw [if_neg hv, hM u v hv'.symm, zero_mul]

lemma mulVec_brestrict_eigen {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) {w : U → ℝ} {θ : ℝ}
    (hw : M *ᵥ w = θ • w) (b : Bool) :
    M *ᵥ brestrict χ b w = θ • brestrict χ (!b) w := by
  rw [mulVec_brestrict hM, hw]
  funext u
  by_cases h : χ u = !b <;> simp [brestrict_apply, h]

/-- An eigenvector with nonzero eigenvalue of a color-bipartite matrix has
nonzero restriction to each color class. -/
theorem brestrict_ne_zero {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) {w : U → ℝ} {θ : ℝ}
    (hw : M *ᵥ w = θ • w) (hθ : θ ≠ 0) (hw0 : w ≠ 0) (b : Bool) :
    brestrict χ b w ≠ 0 := by
  intro hb
  have h1 : θ • brestrict χ (!b) w = 0 := by
    rw [← mulVec_brestrict_eigen hM hw b, hb, Matrix.mulVec_zero]
  have h2 : brestrict χ (!b) w = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hθ
    · exact h
  exact hw0 (by rw [← brestrict_add_not χ b w, hb, h2, add_zero])

/-- Wrapper for the composition layer: an eigenvector with nonzero eigenvalue
of an adversary matrix for `g` has support in every color class of `g`. -/
theorem IsAdvMatrix.exists_eigenvector_support {ι : Type*} [Fintype ι]
    [DecidableEq ι] {g : (ι → Bool) → Bool}
    {N : Matrix (ι → Bool) (ι → Bool) ℝ} (hN : IsAdvMatrix g N)
    {v : (ι → Bool) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (hθ : θ ≠ 0)
    (hv0 : v ≠ 0) (a : Bool) : ∃ u, g u = a ∧ v u ≠ 0 := by
  have h := brestrict_ne_zero (fun u w' huw => hN.2 u w' huw) hv hθ hv0 a
  obtain ⟨u, hu⟩ := Function.ne_iff.mp h
  simp only [brestrict_apply, Pi.zero_apply] at hu
  by_cases hgu : g u = a
  · rw [if_pos hgu] at hu
    exact ⟨u, hgu, hu⟩
  · rw [if_neg hgu] at hu
    exact absurd rfl hu

end QuantumQueryComplexity
