import QuantumQueryComplexity.Duality.Gram
import QuantumQueryComplexity.Promise.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Gram encoding of the dual program, on a promise domain

The promise-domain mirror of `Duality/Gram.lean`: the input space is an
abstract finite `X` read through `read : X → ι → σ`, the constraint mask is
`read x i = read y i`, and the target is `[f x ≠ f y]`.  Everything else —
the convexification by passing to Gram matrices, the rank-one decomposition
back to a `DualPairOn` — is the same change of variables.

The total case is the instance `X = ι → σ`, `read = id`; it is kept as the
separate `Duality/Gram.lean` because its statements (`DualPair`, `advPM`) are
pinned by downstream consumers.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} [DecidableEq O]

/-- Index type for the Gram matrix of a promise dual solution: `(x, i, false)`
indexes the vector `u x i` and `(x, i, true)` indexes `v x i`. -/
abbrev GramIdxOn (X ι : Type*) : Type _ := X × ι × Bool

/-! ## The affine data of the promise dual program -/

/-- The right-hand side of the dual feasibility constraint on the promise
domain: `1` on pairs with distinct values, `0` otherwise. -/
def dualTargetOn (f : X → O) : Matrix X X ℝ :=
  Matrix.of fun x y => if f x = f y then 0 else 1

@[simp] lemma dualTargetOn_apply (f : X → O) (x y : X) :
    dualTargetOn f x y = if f x = f y then 0 else 1 := rfl

lemma dualTargetOn_comm (f : X → O) (x y : X) :
    dualTargetOn f y x = dualTargetOn f x y := by
  simp [eq_comm]

/-- The left-hand side of the dual feasibility constraint, as a function of
the Gram matrix, with the mask read through `read`. -/
def gramROn (read : X → ι → σ) (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    Matrix X X ℝ :=
  Matrix.of fun x y =>
    ∑ i, if read x i = read y i then 0 else G (x, i, false) (y, i, true)

@[simp] lemma gramROn_apply (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x y : X) :
    gramROn read G x y
      = ∑ i, if read x i = read y i then 0 else G (x, i, false) (y, i, true) :=
  rfl

/-- The dual objective, as a function of the Gram matrix. -/
def gramCostOn (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (b : Bool)
    (x : X) : ℝ :=
  ∑ i, G (x, i, b) (x, i, b)

/-! ### Linearity -/

lemma gramROn_add (read : X → ι → σ)
    (G H : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramROn read (G + H) = gramROn read G + gramROn read H := by
  ext x y
  simp only [gramROn_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : read x i = read y i <;> simp [h]

lemma gramROn_smul (read : X → ι → σ) (c : ℝ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramROn read (c • G) = c • gramROn read G := by
  ext x y
  simp only [gramROn_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : read x i = read y i <;> simp [h]

lemma gramCostOn_add (G H : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ)
    (b : Bool) (x : X) :
    gramCostOn (G + H) b x = gramCostOn G b x + gramCostOn H b x := by
  simp [gramCostOn, Finset.sum_add_distrib]

lemma gramCostOn_smul (c : ℝ) (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ)
    (b : Bool) (x : X) : gramCostOn (c • G) b x = c * gramCostOn G b x := by
  simp [gramCostOn, Finset.mul_sum]

/-- A positive semidefinite Gram matrix has nonnegative costs. -/
lemma gramCostOn_nonneg {G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ}
    (hG : G.PosSemidef) (b : Bool) (x : X) : 0 ≤ gramCostOn G b x :=
  Finset.sum_nonneg fun _ _ => hG.diag_nonneg

/-! ## Rank-one Gram matrices -/

@[simp] lemma gramROn_vecMulVec (read : X → ι → σ) (w : GramIdxOn X ι → ℝ)
    (x y : X) :
    gramROn read (vecMulVec w w) x y
      = ∑ i, if read x i = read y i then 0
          else w (x, i, false) * w (y, i, true) := by
  simp [gramROn, vecMulVec_apply]

@[simp] lemma gramCostOn_vecMulVec (w : GramIdxOn X ι → ℝ) (b : Bool)
    (x : X) :
    gramCostOn (vecMulVec w w) b x = ∑ i, w (x, i, b) * w (x, i, b) := by
  simp [gramCostOn, vecMulVec_apply]

lemma trace_vecMulVec_on (w : GramIdxOn X ι → ℝ) :
    (vecMulVec w w).trace = ∑ z, w z * w z := by
  simp [Matrix.trace, vecMulVec_apply]

lemma posSemidef_vecMulVec_self_on (w : GramIdxOn X ι → ℝ) :
    (vecMulVec w w).PosSemidef := by
  have h : vecMulVec w w
      = (Matrix.of fun (z : GramIdxOn X ι) (_ : Unit) => w z) *
        (Matrix.of fun (z : GramIdxOn X ι) (_ : Unit) => w z)ᴴ := by
    ext z z'
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ## From a Gram matrix to a dual solution -/

variable {read : X → ι → σ} {f : X → O}

/-- Every positive semidefinite matrix satisfying the promise dual constraints
is the Gram matrix of a feasible `DualPairOn` of the same cost. -/
theorem exists_dualPairOn_of_gram
    {G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ}
    (hG : G.PosSemidef) (hR : gramROn read G = dualTargetOn f) {c : ℝ}
    (hc : ∀ b x, gramCostOn G b x ≤ c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c := by
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have hentry : ∀ z z' : GramIdxOn X ι, G z z' = ∑ k, w k z * w k z' := by
    intro z z'
    rw [hw]
    simp [Matrix.sum_apply, vecMulVec_apply]
  refine ⟨m, { u := fun x i k => w k (x, i, false)
               v := fun x i k => w k (x, i, true)
               constraint := ?_ }, ?_, ?_⟩
  · intro x y
    have := congrArg (fun M => M x y) hR
    simp only [gramROn_apply, dualTargetOn_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases h : read x i = read y i
      · simp [h]
      · simp only [if_neg h]
        exact (hentry (x, i, false) (y, i, true)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc false x)
    exact Finset.sum_congr rfl fun i _ =>
      (hentry (x, i, false) (x, i, false)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc true x)
    exact Finset.sum_congr rfl fun i _ =>
      (hentry (x, i, true) (x, i, true)).symm

end QuantumQueryComplexity
