import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Finite-dimensional complex Hilbert space for the query model

A quantum state on a finite basis type `H` is a function `ψ : H → ℂ`, an operator
is a `Matrix H H ℂ`, and the action of an operator on a state is `U *ᵥ ψ`.  We
keep this *raw*, in the same spirit as the adversary side of the project: the
inner product is a plain finite sum

  `qInner ψ φ = ∑ h, star (ψ h) * φ h`,

conjugate-linear in the first argument, and the squared norm is
`qNormSq ψ = ∑ h, ‖ψ h‖²`.

Why not `EuclideanSpace ℂ H`?  Because most arguments downstream — the query
decomposition of a state by its index register, the progress measure of the
adversary lower bound, the oracle's action on a product basis — are
manipulations of finite sums over the basis, and `WithLp`/`PiLp` coercions get
in the way of exactly those.  So the raw form is the default.

It is not a quarantine, though: `qInner_eq_euclidean` and `qNormSq_eq_euclidean`
below are **public**, and `Quantum/Projector.lean` crosses by them deliberately,
building subspaces and orthogonal projectors in `EuclideanSpace` where Mathlib's
theory lives and carrying the results back as matrices.  Raw by default, Euclidean
where Mathlib is stronger.

## Main definitions

* `qInner`, `qNormSq`, `IsQState` (a unit vector).
* `qBasis h` — the computational basis state `|h⟩`.
* `Matrix.unitaryGroup H ℂ` is Mathlib's; `qPerm e` is the unitary that sends
  `|b⟩` to `|e b⟩`, which is how every permutation oracle enters.
* `IsQProjector P` and the reflection `qRefl P = 2P - 1`.

## Main results

* `qInner_mulVec_mulVec`, `qNormSq_mulVec`, `IsQState.mulVec` — a unitary
  preserves inner products, squared norms, and unit states.
* `qInner_norm_le` — Cauchy–Schwarz.
* `qInner_mulVec_left` — moving an operator across the inner product.
* `qPerm_mem_unitaryGroup`, `qPerm_mulVec`, `qPerm_involutive`.
* `qRefl_mem_unitaryGroup`, `qRefl_mul_self`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## The inner product -/

/-- The Hermitian inner product on `H → ℂ`, conjugate-linear in the **first**
argument (the physicists' convention, and Mathlib's). -/
def qInner (ψ φ : H → ℂ) : ℂ := star ψ ⬝ᵥ φ

lemma qInner_def (ψ φ : H → ℂ) : qInner ψ φ = ∑ h, star (ψ h) * φ h := rfl

/-- The squared norm of a state, as a real number. -/
def qNormSq (ψ : H → ℂ) : ℝ := ∑ h, Complex.normSq (ψ h)

lemma qNormSq_def (ψ : H → ℂ) : qNormSq ψ = ∑ h, Complex.normSq (ψ h) := rfl

/-- A (pure) quantum state: a unit vector. -/
def IsQState (ψ : H → ℂ) : Prop := qNormSq ψ = 1

lemma qNormSq_nonneg (ψ : H → ℂ) : 0 ≤ qNormSq ψ :=
  Finset.sum_nonneg fun h _ => Complex.normSq_nonneg (ψ h)

@[simp] lemma qInner_self (ψ : H → ℂ) : qInner ψ ψ = (qNormSq ψ : ℂ) := by
  rw [qInner_def, qNormSq_def]
  push_cast
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_eq_conj_mul_self.symm

lemma qInner_conj (ψ φ : H → ℂ) : star (qInner ψ φ) = qInner φ ψ := by
  rw [qInner_def, qInner_def, star_sum]
  exact Finset.sum_congr rfl fun h _ => by rw [star_mul, star_star, mul_comm]

@[simp] lemma qInner_zero_left (φ : H → ℂ) : qInner (0 : H → ℂ) φ = 0 := by
  simp [qInner_def]

@[simp] lemma qInner_zero_right (ψ : H → ℂ) : qInner ψ (0 : H → ℂ) = 0 := by
  simp [qInner_def]

lemma qInner_add_right (ψ φ χ : H → ℂ) :
    qInner ψ (φ + χ) = qInner ψ φ + qInner ψ χ := by
  simp only [qInner_def, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

lemma qInner_add_left (ψ φ χ : H → ℂ) :
    qInner (ψ + φ) χ = qInner ψ χ + qInner φ χ := by
  simp only [qInner_def, Pi.add_apply, star_add, add_mul]
  exact Finset.sum_add_distrib

lemma qInner_sub_left (ψ φ χ : H → ℂ) :
    qInner (ψ - φ) χ = qInner ψ χ - qInner φ χ := by
  simp only [qInner_def, Pi.sub_apply, star_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

lemma qInner_sub_right (ψ φ χ : H → ℂ) :
    qInner ψ (φ - χ) = qInner ψ φ - qInner ψ χ := by
  simp only [qInner_def, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

lemma qInner_smul_right (c : ℂ) (ψ φ : H → ℂ) :
    qInner ψ (c • φ) = c * qInner ψ φ := by
  simp only [qInner_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

lemma qInner_smul_left (c : ℂ) (ψ φ : H → ℂ) :
    qInner (c • ψ) φ = star c * qInner ψ φ := by
  simp only [qInner_def, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

lemma qInner_sum_right {α : Type*} (ψ : H → ℂ) (s : Finset α) (F : α → (H → ℂ)) :
    qInner ψ (∑ i ∈ s, F i) = ∑ i ∈ s, qInner ψ (F i) := by
  simp only [qInner_def]
  rw [show (∑ h, star (ψ h) * (∑ i ∈ s, F i) h) = ∑ h, ∑ i ∈ s, star (ψ h) * F i h from
    Finset.sum_congr rfl fun h _ => by rw [Finset.sum_apply, Finset.mul_sum]]
  exact Finset.sum_comm

lemma qInner_sum_left {α : Type*} (s : Finset α) (F : α → (H → ℂ)) (φ : H → ℂ) :
    qInner (∑ i ∈ s, F i) φ = ∑ i ∈ s, qInner (F i) φ := by
  simp only [qInner_def]
  rw [show (∑ h, star ((∑ i ∈ s, F i) h) * φ h) = ∑ h, ∑ i ∈ s, star (F i h) * φ h from
    Finset.sum_congr rfl fun h _ => by
      rw [Finset.sum_apply, star_sum, Finset.sum_mul]]
  exact Finset.sum_comm

@[simp] lemma qNormSq_zero : qNormSq (0 : H → ℂ) = 0 := by simp [qNormSq_def]

lemma qNormSq_smul (c : ℂ) (ψ : H → ℂ) :
    qNormSq (c • ψ) = Complex.normSq c * qNormSq ψ := by
  rw [qNormSq_def, qNormSq_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by
    rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]

/-- The parallelogram expansion. -/
lemma qNormSq_add (ψ φ : H → ℂ) :
    qNormSq (ψ + φ) = qNormSq ψ + qNormSq φ + 2 * (qInner ψ φ).re := by
  have h : qInner (ψ + φ) (ψ + φ)
      = qInner ψ ψ + qInner φ φ + (qInner ψ φ + qInner φ ψ) := by
    rw [qInner_add_left, qInner_add_right, qInner_add_right]
    ring
  have h2 : (qInner φ ψ).re = (qInner ψ φ).re := by
    rw [← qInner_conj ψ φ]
    simp
  have h3 := congrArg Complex.re h
  rw [qInner_self, qInner_self, qInner_self] at h3
  simp only [Complex.add_re, Complex.ofReal_re] at h3
  rw [h3, h2]
  ring

lemma qNormSq_eq_zero_iff {ψ : H → ℂ} : qNormSq ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun h _ => Complex.normSq_nonneg (ψ h))).mp h k (Finset.mem_univ k)
    simpa using Complex.normSq_eq_zero.mp this
  · rintro rfl
    simp

/-! ## The Euclidean bridge

The sanctioned crossing between the raw representation used everywhere here and
Mathlib's inner-product-space library.  These two lemmas are **public on
purpose**: the reflection constructors of the upper bound build a subspace in
`EuclideanSpace ℂ H`, take Mathlib's `Submodule.starProjection`, transport it
back through `WithLp.linearEquiv`, and turn it into a matrix with
`LinearMap.toMatrix'`.  That route needs to state its correctness in raw terms,
and these are the lemmas that let it.

Everything *else* in this file stays raw: the bridge is a door, not a move.
-/

lemma qInner_eq_euclidean (ψ φ : H → ℂ) :
    qInner ψ φ = inner ℂ (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) (WithLp.toLp 2 φ) := by
  rw [EuclideanSpace.inner_toLp_toLp, qInner_def, dotProduct]
  exact Finset.sum_congr rfl fun h _ => by rw [mul_comm]; rfl

lemma qNormSq_eq_euclidean (ψ : H → ℂ) :
    qNormSq ψ = ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ H)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun h _ => by positivity)]
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_eq_norm_sq (ψ h)

/-- **Cauchy–Schwarz.** -/
theorem qInner_norm_le (ψ φ : H → ℂ) :
    ‖qInner ψ φ‖ ≤ Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ) := by
  rw [qInner_eq_euclidean, qNormSq_eq_euclidean, qNormSq_eq_euclidean,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

/-- The triangle inequality, in squared-norm form. -/
theorem sqrt_qNormSq_add_le (ψ φ : H → ℂ) :
    Real.sqrt (qNormSq (ψ + φ)) ≤ Real.sqrt (qNormSq ψ) + Real.sqrt (qNormSq φ) := by
  rw [qNormSq_eq_euclidean, qNormSq_eq_euclidean, qNormSq_eq_euclidean,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact norm_add_le _ _

/-! ## Basis states -/

/-- The computational basis state `|h⟩`. -/
def qBasis (h : H) : H → ℂ := Pi.single h 1

@[simp] lemma qBasis_apply (h k : H) : qBasis h k = if k = h then 1 else 0 := by
  rw [qBasis, Pi.single_apply]

@[simp] lemma qNormSq_qBasis (h : H) : qNormSq (qBasis h) = 1 := by
  rw [qNormSq_def, Finset.sum_eq_single h]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma isQState_qBasis (h : H) : IsQState (qBasis h) := qNormSq_qBasis h

/-! ## Unitaries -/

lemma one_mem_qUnitary : (1 : Matrix H H ℂ) ∈ Matrix.unitaryGroup H ℂ :=
  one_mem _

lemma mul_mem_qUnitary {U V : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) : U * V ∈ Matrix.unitaryGroup H ℂ :=
  mul_mem hU hV

lemma conjTranspose_mul_self_of_unitary {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : Uᴴ * U = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hU
  rwa [Matrix.star_eq_conjTranspose] at this

/-- **Moving an operator across the inner product.** -/
lemma qInner_mulVec_left (M : Matrix H H ℂ) (ψ φ : H → ℂ) :
    qInner (M *ᵥ ψ) φ = qInner ψ (Mᴴ *ᵥ φ) := by
  rw [qInner, qInner, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

/-- **A unitary preserves the inner product.** -/
theorem qInner_mulVec_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (ψ φ : H → ℂ) : qInner (U *ᵥ ψ) (U *ᵥ φ) = qInner ψ φ := by
  rw [qInner, qInner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, conjTranspose_mul_self_of_unitary hU, Matrix.vecMul_one]

/-- **A unitary preserves the squared norm.** -/
theorem qNormSq_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (ψ : H → ℂ) : qNormSq (U *ᵥ ψ) = qNormSq ψ := by
  have h := qInner_mulVec_mulVec hU ψ ψ
  rw [qInner_self, qInner_self] at h
  exact_mod_cast h

/-- **A unitary maps states to states.** -/
theorem IsQState.mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    {ψ : H → ℂ} (hψ : IsQState ψ) : IsQState (U *ᵥ ψ) := by
  rw [IsQState, qNormSq_mulVec hU]
  exact hψ

/-! ## Permutation unitaries

Every oracle in this development is a permutation of the computational basis, so
this is the workhorse.  Note the inverse in the definition: Mathlib's
`Equiv.Perm.permMatrix σ` acts on *coordinates* by `v ∘ σ`, i.e. it sends the
basis state `|b⟩` to `|σ⁻¹ b⟩`; `qPerm e` is normalized so that it sends `|b⟩` to
`|e b⟩`. -/

/-- The unitary that sends the basis state `|b⟩` to `|e b⟩`. -/
def qPerm (e : Equiv.Perm H) : Matrix H H ℂ := (e⁻¹).permMatrix ℂ

lemma qPerm_mulVec (e : Equiv.Perm H) (ψ : H → ℂ) : qPerm e *ᵥ ψ = ψ ∘ ⇑(e⁻¹) := by
  rw [qPerm, Matrix.permMatrix_mulVec]

lemma qPerm_mulVec_apply (e : Equiv.Perm H) (ψ : H → ℂ) (h : H) :
    (qPerm e *ᵥ ψ) h = ψ (e.symm h) := by
  rw [qPerm_mulVec]
  rfl

/-- **A permutation unitary sends basis states to basis states.** -/
lemma qPerm_mulVec_qBasis (e : Equiv.Perm H) (p : H) :
    qPerm e *ᵥ qBasis p = qBasis (e p) := by
  funext k
  rw [qPerm_mulVec_apply, qBasis_apply, qBasis_apply]
  by_cases h : k = e p
  · simp [h]
  · have h' : ¬ (e.symm k = p) := fun hk => h (by rw [← hk, Equiv.apply_symm_apply])
    simp [h, h']

@[simp] lemma qPerm_one : qPerm (1 : Equiv.Perm H) = 1 := by
  simp [qPerm]

lemma qPerm_mul (e f : Equiv.Perm H) : qPerm (e * f) = qPerm e * qPerm f := by
  rw [qPerm, qPerm, qPerm, _root_.mul_inv_rev, Matrix.permMatrix_mul]

lemma qPerm_mem_unitaryGroup (e : Equiv.Perm H) :
    qPerm e ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, qPerm,
    Matrix.conjTranspose_permMatrix, inv_inv, ← Matrix.permMatrix_mul]
  simp

/-- An involutive permutation gives a self-inverse unitary: query = unquery. -/
lemma qPerm_mul_self_of_involutive {e : Equiv.Perm H} (he : Function.Involutive e) :
    qPerm e * qPerm e = 1 := by
  rw [← qPerm_mul]
  have : e * e = 1 := Equiv.ext fun h => he h
  rw [this, qPerm_one]

/-! ## Projectors and reflections -/

/-- An orthogonal projector. -/
def IsQProjector (P : Matrix H H ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- The reflection about the range of a projector, `2P - 1`. -/
def qRefl (P : Matrix H H ℂ) : Matrix H H ℂ := (2 : ℂ) • P - 1

lemma qRefl_conjTranspose {P : Matrix H H ℂ} (hP : IsQProjector P) :
    (qRefl P)ᴴ = qRefl P := by
  rw [qRefl, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.1,
    Matrix.conjTranspose_one]
  norm_num

/-- **A reflection is involutive.** -/
lemma qRefl_mul_self {P : Matrix H H ℂ} (hP : IsQProjector P) :
    qRefl P * qRefl P = 1 := by
  rw [qRefl, sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP.2,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  match_scalars <;> ring

/-- **A projector shrinks**: `‖Pψ‖ ≤ ‖ψ‖`. -/
theorem IsQProjector.qNormSq_mulVec_le {P : Matrix H H ℂ} (hP : IsQProjector P)
    (ψ : H → ℂ) : qNormSq (P *ᵥ ψ) ≤ qNormSq ψ := by
  have horth : (qInner (P *ᵥ ψ) (ψ - P *ᵥ ψ)).re = 0 := by
    rw [qInner_mulVec_left, hP.1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.2,
      sub_self, qInner_zero_right, Complex.zero_re]
  have hsplit : P *ᵥ ψ + (ψ - P *ᵥ ψ) = ψ := by abel
  have hexp := qNormSq_add (P *ᵥ ψ) (ψ - P *ᵥ ψ)
  rw [hsplit, horth] at hexp
  have := qNormSq_nonneg (ψ - P *ᵥ ψ)
  linarith

/-- **Conjugating a projector by a unitary gives a projector.** -/
lemma IsQProjector.conj {P U : Matrix H H ℂ} (hP : IsQProjector P)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : IsQProjector (U * P * Uᴴ) := by
  have h : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  constructor
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.1,
      Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, h, Matrix.one_mul, ← Matrix.mul_assoc P P, hP.2]

/-- **A reflection is unitary.** -/
lemma qRefl_mem_unitaryGroup {P : Matrix H H ℂ} (hP : IsQProjector P) :
    qRefl P ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    qRefl_conjTranspose hP]
  exact qRefl_mul_self hP

end QuantumQueryComplexity
