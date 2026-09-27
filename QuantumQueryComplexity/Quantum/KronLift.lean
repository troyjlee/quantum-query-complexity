import QuantumQueryComplexity.Quantum.Routine
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Lifting an operator along a factorizing equivalence

The generic tool of the independent-run compiler.  A basis equivalence
`e : β ≃ γ × δ` splits a space into a system and an environment;
`kronLift e M` is `M ⊗ 1` read through `e`, so its algebra is inherited from
Mathlib's Kronecker product exactly as `blockFam`'s came from
`blockDiagonal`.  The two working lemmas:

* `kronLift_mulVec_splitVec` — on a **split state**
  `splitVec e φ ξ = φ((e·).1)·ξ((e·).2)` the lift acts on the system factor
  alone;
* `kronLiftRoutine_runUpto_splitVec` — a routine's steps lifted along an
  **oracle-compatible** equivalence (one that carries the global query
  registers into the system factor: `e (oracleMap a p)
  = (oracleMap a (e p).1, (e p).2)`) run, against the real oracle, as the
  original routine on the system factor.  The compatibility is stated at the
  *map* level, so no matrix identity for the oracle is ever needed.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

section Generic

variable {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype δ] [DecidableEq δ]

/-- `M ⊗ 1`, read through the factorizing equivalence `e`. -/
def kronLift (e : β ≃ γ × δ) (M : Matrix γ γ ℂ) : Matrix β β ℂ :=
  (Matrix.kroneckerMap (· * ·) M (1 : Matrix δ δ ℂ)).submatrix e e

lemma kronLift_mul (e : β ≃ γ × δ) (M N : Matrix γ γ ℂ) :
    kronLift e M * kronLift e N = kronLift e (M * N) := by
  rw [kronLift, kronLift, kronLift, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, one_mul]

lemma kronLift_one (e : β ≃ γ × δ) :
    kronLift e (1 : Matrix γ γ ℂ) = 1 := by
  rw [kronLift, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

lemma kronLift_conjTranspose (e : β ≃ γ × δ) (M : Matrix γ γ ℂ) :
    (kronLift e M)ᴴ = kronLift e Mᴴ := by
  rw [kronLift, kronLift, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma kronLift_mem_unitaryGroup (e : β ≃ γ × δ) {M : Matrix γ γ ℂ}
    (hM : M ∈ Matrix.unitaryGroup γ ℂ) :
    kronLift e M ∈ Matrix.unitaryGroup β ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    kronLift_conjTranspose, kronLift_mul,
    conjTranspose_mul_self_of_unitary hM, kronLift_one]

/-- A state of split form: `φ` on the system factor, `ξ` on the
environment. -/
def splitVec (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ) : β → ℂ :=
  fun b => φ (e b).1 * ξ (e b).2

@[simp] lemma splitVec_apply (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ)
    (b : β) : splitVec e φ ξ b = φ (e b).1 * ξ (e b).2 := rfl

/-- **The lift acts on the system factor of a split state.** -/
theorem kronLift_mulVec_splitVec (e : β ≃ γ × δ) (M : Matrix γ γ ℂ)
    (φ : γ → ℂ) (ξ : δ → ℂ) :
    kronLift e M *ᵥ splitVec e φ ξ = splitVec e (M *ᵥ φ) ξ := by
  funext b
  rw [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp e.symm
    (fun b' => kronLift e M b b' * splitVec e φ ξ b')]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (c : γ) (d : δ),
      kronLift e M b (e.symm (c, d)) * splitVec e φ ξ (e.symm (c, d))
        = (M (e b).1 c * φ c) * (if (e b).2 = d then ξ d else 0) := by
    intro c d
    rw [kronLift, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      Matrix.kroneckerMap_apply, splitVec_apply, Equiv.apply_symm_apply]
    rw [Matrix.one_apply]
    by_cases h : (e b).2 = d
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  simp only [hterm]
  have hinner : ∀ c : γ,
      (∑ d, (M (e b).1 c * φ c) * (if (e b).2 = d then ξ d else 0))
        = (M (e b).1 c * φ c) * ξ (e b).2 := by
    intro c
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ (e b).2 ξ, if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun c _ => hinner c, splitVec_apply,
    ← Finset.sum_mul]
  congr 1

/-- The squared norm of a split state is the product of the factors'. -/
lemma qNormSq_splitVec (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ) :
    qNormSq (splitVec e φ ξ) = qNormSq φ * qNormSq ξ := by
  rw [qNormSq_def, ← Equiv.sum_comp e.symm
    (fun b => Complex.normSq (splitVec e φ ξ b)), Fintype.sum_prod_type]
  rw [qNormSq_def, qNormSq_def, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [splitVec_apply, Equiv.apply_symm_apply, Complex.normSq_mul]

end Generic

/-! ## The lifted routine -/

section Routine

variable {ι σ W W' D : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']
  [Fintype D] [DecidableEq D]

/-- `e` is **oracle-compatible** when it carries the global query registers
into the system factor and the environment rides along. -/
def OracleCompat (e : QBasis ι σ W' ≃ QBasis ι σ W × D) : Prop :=
  ∀ (a : ι → σ) (p : QBasis ι σ W'),
    e (oracleMap a p) = (oracleMap a (e p).1, (e p).2)

/-- The oracle preserves split states along an oracle-compatible
equivalence, acting on the system factor. -/
lemma oracleMat_mulVec_splitVec {e : QBasis ι σ W' ≃ QBasis ι σ W × D}
    (he : OracleCompat e) (a : ι → σ) (φ : QBasis ι σ W → ℂ) (ξ : D → ℂ) :
    oracleMat a *ᵥ splitVec e φ ξ = splitVec e (oracleMat a *ᵥ φ) ξ := by
  funext p
  rw [oracleMat_mulVec_apply, splitVec_apply, splitVec_apply, he a p,
    oracleMat_mulVec_apply]

/-- A routine's steps, lifted along `e`. -/
def QRoutine.kronLift (e : QBasis ι σ W' ≃ QBasis ι σ W × D)
    (R : QRoutine ι σ W) : QRoutine ι σ W' where
  len := R.len
  step := fun t => QuantumQueryComplexity.kronLift e (R.step t)
  step_unitary := fun t => kronLift_mem_unitaryGroup e (R.step_unitary t)

@[simp] lemma QRoutine.kronLift_len (e : QBasis ι σ W' ≃ QBasis ι σ W × D)
    (R : QRoutine ι σ W) : (R.kronLift e).len = R.len := rfl

/-- **The lifted routine runs as the original on the system factor.** -/
theorem QRoutine.kronLift_runUpto_splitVec
    {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) (φ : QBasis ι σ W → ℂ)
    (ξ : D → ℂ) :
    (R.kronLift e).runUpto a t *ᵥ splitVec e φ ξ
      = splitVec e (R.runUpto a t *ᵥ φ) ξ := by
  induction t with
  | zero => exact kronLift_mulVec_splitVec e (R.step 0) φ ξ
  | succ t ih =>
      show ((R.kronLift e).step (t + 1)
          * (oracleMat a * (R.kronLift e).runUpto a t)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        oracleMat_mulVec_splitVec he]
      rw [show (R.kronLift e).step (t + 1)
          = QuantumQueryComplexity.kronLift e (R.step (t + 1)) from rfl,
        kronLift_mulVec_splitVec]
      rw [QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]

end Routine

end QuantumQueryComplexity
