import QuantumQueryComplexity.Quantum.FiniteHilbert
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The chord form of a unitary

**A spike for the spectral layer.**  Spectral windows for a unitary `U` are
usually stated with `Complex.arg` of its eigenvalues, which drags in branch cuts
and trigonometry.  The **chord distance** `‖1 - z‖` avoids that, and it has a
matrix avatar that avoids diagonalizing `U` at all:

  `chordSq U = (1 - U)ᴴ (1 - U)`.

This matrix is Hermitian (`chordSq_conjTranspose`) and positive semidefinite, so
Mathlib's spectral theory
for *Hermitian* matrices applies directly — no eigenbasis for a general unitary
is needed.  Its quadratic form is exactly the squared chord distance
(`qNormSq_sub_mulVec`), so "the eigenvalues of `chordSq U` are at most `Δ²`" is
precisely "the chord-distance window of threshold `Δ²`" (equivalently of radius
`|Δ|` — nothing here assumes `Δ` nonnegative).

Two facts make one Hermitian decomposition serve both halves of the phase
detector:

* `chordSq_commute` — `chordSq U` commutes with `U`, so `U` preserves each of
  its spectral subspaces.  This is what removes the need for simultaneous
  diagonalization: the windows are defined by a Hermitian matrix, and `U` acts
  within them.
* `one_sub_mul_geom_sum` — `(1 - U) ∑_{t<T} U^t = 1 - U^T`, the telescoping
  identity behind the uniform-clock estimate on the far window.

On a unitary the chord form collapses to `2 - U - Uᴴ`, which is where both
facts come from.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The chord form of `U`: `(1 - U)ᴴ (1 - U)`. -/
def chordSq (U : Matrix H H ℂ) : Matrix H H ℂ := (1 - U)ᴴ * (1 - U)

/-- The chord form is Hermitian — stated as the raw identity, so this file needs
no extra Mathlib import. -/
lemma chordSq_conjTranspose (U : Matrix H H ℂ) : (chordSq U)ᴴ = chordSq U := by
  unfold chordSq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **The quadratic form of `chordSq` is the squared chord distance.**  This is
what makes a spectral window of `chordSq U` a chord-distance window. -/
theorem qNormSq_sub_mulVec (U : Matrix H H ℂ) (ψ : H → ℂ) :
    qNormSq ((1 - U) *ᵥ ψ) = (qInner ψ (chordSq U *ᵥ ψ)).re := by
  have h : qInner ((1 - U) *ᵥ ψ) ((1 - U) *ᵥ ψ) = qInner ψ (chordSq U *ᵥ ψ) := by
    rw [qInner_mulVec_left, chordSq, ← Matrix.mulVec_mulVec]
  rw [← h, qInner_self, Complex.ofReal_re]

/-- On a unitary the chord form collapses. -/
theorem chordSq_eq_of_unitary {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : chordSq U = 1 + 1 - U - Uᴴ := by
  have h1 : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  unfold chordSq
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub,
    Matrix.one_mul, Matrix.mul_one, h1]
  abel

/-- **The chord form commutes with the unitary**, so `U` preserves each spectral
subspace of `chordSq U`.  No simultaneous diagonalization is needed. -/
theorem chordSq_commute {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    chordSq U * U = U * chordSq U := by
  have h1 : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [chordSq_eq_of_unitary hU]
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2]

/-- The chord form kills exactly what `1 - U` kills. -/
theorem chordSq_mulVec_eq_zero_iff (U : Matrix H H ℂ) (ψ : H → ℂ) :
    chordSq U *ᵥ ψ = 0 ↔ (1 - U) *ᵥ ψ = 0 := by
  constructor
  · intro h
    have hq := qNormSq_sub_mulVec U ψ
    rw [h, qInner_zero_right, Complex.zero_re] at hq
    exact qNormSq_eq_zero_iff.mp hq
  · intro h
    rw [chordSq, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- **The core identity of the effective gap.**  If `L` (the plan's `Λ`) kills
`w`, the product of the two reflections moves `w` by exactly `2 P w` (the plan's
`2 Π w`).  `Π` is reserved notation in Lean, hence the renaming. -/
theorem one_sub_qRefl_mul_qRefl_mulVec {P L : Matrix H H ℂ} {w : H → ℂ}
    (hw : L *ᵥ w = 0) :
    (1 - qRefl P * qRefl L) *ᵥ w = (2 : ℂ) • (P *ᵥ w) := by
  have h1 : qRefl L *ᵥ w = -w := by
    rw [qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, hw, Matrix.one_mulVec, smul_zero,
      zero_sub]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h1, qRefl,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg]
  module

/-- **The telescoping identity** behind the uniform clock. -/
theorem one_sub_mul_geom_sum (U : Matrix H H ℂ) (T : ℕ) :
    (1 - U) * (∑ t ∈ Finset.range T, U ^ t) = 1 - U ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, mul_add, ih, sub_mul, Matrix.one_mul, ← pow_succ']
      abel

end QuantumQueryComplexity
