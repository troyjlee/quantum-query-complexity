import QuantumQueryComplexity.Dual
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Positive

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Gram encoding of the dual program

A feasible dual solution (`DualPair`) is a pair of vector families `u x i`,
`v y i`; the dual constraints and the dual cost depend on those families only
through their inner products, i.e. only through the Gram matrix of the whole
family.  This file makes that change of variables explicit, which is what
convexifies the dual program: the set of feasible *Gram matrices* is the
intersection of the (convex) positive semidefinite cone with affine
constraints, whereas the set of feasible vector families is not convex.

Indexing the combined family by `GramIdx ι σ = (ι → σ) × ι × Bool` — `false`
tagging a `u`-vector and `true` a `v`-vector — the dictionary is

* `gramR G = dualTarget g` ⟺ the `DualPair.constraint` equations,
* `gramCost G b x ≤ c` for all `b`, `x` ⟺ `DualPair.IsCostLe c`.

Both directions of the translation are proved: `gramOfDual` builds the Gram
matrix of a dual solution, and `exists_dualPair_of_gram` extracts a dual
solution of dimension `Fin m` from any positive semidefinite `G` satisfying the
constraints, via the rank-one decomposition
`Matrix.posSemidef_iff_eq_sum_vecMulVec`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- Index type for the Gram matrix of a dual solution: `(x, i, false)` indexes
the vector `u x i` and `(x, i, true)` indexes `v x i`. -/
abbrev GramIdx (ι σ : Type*) : Type _ := (ι → σ) × ι × Bool

/-! ## The affine data of the dual program -/

/-- The right-hand side of the dual feasibility constraint:
`dualTarget g x y = 1` if `g x ≠ g y` and `0` otherwise. -/
def dualTarget (g : (ι → σ) → O) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y => if g x = g y then 0 else 1

@[simp] lemma dualTarget_apply (g : (ι → σ) → O) (x y : ι → σ) :
    dualTarget g x y = if g x = g y then 0 else 1 := rfl

lemma dualTarget_comm (g : (ι → σ) → O) (x y : ι → σ) :
    dualTarget g y x = dualTarget g x y := by
  simp [eq_comm]

/-- The left-hand side of the dual feasibility constraint, as a function of the
Gram matrix. -/
def gramR (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y => ∑ i, if x i = y i then 0 else G (x, i, false) (y, i, true)

@[simp] lemma gramR_apply (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x y : ι → σ) :
    gramR G x y = ∑ i, if x i = y i then 0 else G (x, i, false) (y, i, true) :=
  rfl

/-- The dual objective, as a function of the Gram matrix: `gramCost G false x`
is `∑ i, ‖u x i‖²` and `gramCost G true x` is `∑ i, ‖v x i‖²`. -/
def gramCost (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) (b : Bool)
    (x : ι → σ) : ℝ :=
  ∑ i, G (x, i, b) (x, i, b)

/-! ### Linearity -/

lemma gramR_add (G H : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramR (G + H) = gramR G + gramR H := by
  ext x y
  simp only [gramR_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by by_cases h : x i = y i <;> simp [h]

lemma gramR_smul (c : ℝ) (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramR (c • G) = c • gramR G := by
  ext x y
  simp only [gramR_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by by_cases h : x i = y i <;> simp [h]

lemma gramCost_add (G H : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) (b : Bool)
    (x : ι → σ) : gramCost (G + H) b x = gramCost G b x + gramCost H b x := by
  simp [gramCost, Finset.sum_add_distrib]

lemma gramCost_smul (c : ℝ) (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (b : Bool) (x : ι → σ) : gramCost (c • G) b x = c * gramCost G b x := by
  simp [gramCost, Finset.mul_sum]

/-- The trace splits as the total cost of the two sides. -/
lemma trace_eq_sum_gramCost (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    G.trace = (∑ x, gramCost G false x) + ∑ x, gramCost G true x := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, gramCost, gramCost, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [Fintype.sum_bool, add_comm]

/-- A positive semidefinite Gram matrix has nonnegative costs. -/
lemma gramCost_nonneg {G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ}
    (hG : G.PosSemidef) (b : Bool) (x : ι → σ) : 0 ≤ gramCost G b x :=
  Finset.sum_nonneg fun _ _ => hG.diag_nonneg

/-! ## Rank-one Gram matrices -/

@[simp] lemma gramR_vecMulVec (w : GramIdx ι σ → ℝ) (x y : ι → σ) :
    gramR (vecMulVec w w) x y
      = ∑ i, if x i = y i then 0 else w (x, i, false) * w (y, i, true) := by
  simp [gramR, vecMulVec_apply]

@[simp] lemma gramCost_vecMulVec (w : GramIdx ι σ → ℝ) (b : Bool)
    (x : ι → σ) :
    gramCost (vecMulVec w w) b x = ∑ i, w (x, i, b) * w (x, i, b) := by
  simp [gramCost, vecMulVec_apply]

lemma trace_vecMulVec (w : GramIdx ι σ → ℝ) :
    (vecMulVec w w).trace = ∑ z, w z * w z := by
  simp [Matrix.trace, vecMulVec_apply]

lemma posSemidef_vecMulVec_self (w : GramIdx ι σ → ℝ) :
    (vecMulVec w w).PosSemidef := by
  have h : vecMulVec w w
      = (Matrix.of fun (z : GramIdx ι σ) (_ : Unit) => w z) *
        (Matrix.of fun (z : GramIdx ι σ) (_ : Unit) => w z)ᴴ := by
    ext z z'
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ## From a dual solution to its Gram matrix -/

variable {K : Type*} [Fintype K] {g : (ι → σ) → O}

/-- The two vector families of a dual solution, packed into a single matrix
whose rows are indexed by `GramIdx ι σ`. -/
def dualVec (P : DualPair K g) : Matrix (GramIdx ι σ) K ℝ :=
  Matrix.of fun z k => if z.2.2 then P.v z.1 z.2.1 k else P.u z.1 z.2.1 k

@[simp] lemma dualVec_false (P : DualPair K g) (x : ι → σ) (i : ι) (k : K) :
    dualVec P (x, i, false) k = P.u x i k := rfl

@[simp] lemma dualVec_true (P : DualPair K g) (x : ι → σ) (i : ι) (k : K) :
    dualVec P (x, i, true) k = P.v x i k := rfl

/-- The Gram matrix of a dual solution. -/
def gramOfDual (P : DualPair K g) :
    Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ := dualVec P * (dualVec P)ᴴ

lemma gramOfDual_apply (P : DualPair K g) (z w : GramIdx ι σ) :
    gramOfDual P z w = ∑ k, dualVec P z k * dualVec P w k := by
  simp [gramOfDual, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma gramOfDual_posSemidef (P : DualPair K g) : (gramOfDual P).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

lemma gramR_gramOfDual (P : DualPair K g) : gramR (gramOfDual P) = dualTarget g := by
  ext x y
  rw [gramR_apply, dualTarget_apply, ← P.constraint x y]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]
  · simp only [if_neg h]
    exact gramOfDual_apply P (x, i, false) (y, i, true)

lemma gramCost_gramOfDual_false (P : DualPair K g) (x : ι → σ) :
    gramCost (gramOfDual P) false x = ∑ i, ∑ k, P.u x i k * P.u x i k :=
  Finset.sum_congr rfl fun i _ => gramOfDual_apply P (x, i, false) (x, i, false)

lemma gramCost_gramOfDual_true (P : DualPair K g) (x : ι → σ) :
    gramCost (gramOfDual P) true x = ∑ i, ∑ k, P.v x i k * P.v x i k :=
  Finset.sum_congr rfl fun i _ => gramOfDual_apply P (x, i, true) (x, i, true)

lemma gramCost_gramOfDual_le {P : DualPair K g} {c : ℝ} (h : P.IsCostLe c)
    (b : Bool) (x : ι → σ) : gramCost (gramOfDual P) b x ≤ c := by
  cases b with
  | false => rw [gramCost_gramOfDual_false]; exact h.1 x
  | true => rw [gramCost_gramOfDual_true]; exact h.2 x

/-! ## From a Gram matrix back to a dual solution -/

/-- Every positive semidefinite matrix satisfying the dual constraints is the
Gram matrix of a feasible dual solution of the same cost.  The dimension comes
out as `Fin m`, which is the shape `advDual` normalises to. -/
theorem exists_dualPair_of_gram {G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ}
    (hG : G.PosSemidef) (hR : gramR G = dualTarget g) {c : ℝ}
    (hc : ∀ b x, gramCost G b x ≤ c) :
    ∃ (m : ℕ) (P : DualPair (Fin m) g), P.IsCostLe c := by
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have hentry : ∀ z z' : GramIdx ι σ, G z z' = ∑ k, w k z * w k z' := by
    intro z z'
    rw [hw]
    simp [Matrix.sum_apply, vecMulVec_apply]
  refine ⟨m, { u := fun x i k => w k (x, i, false)
               v := fun x i k => w k (x, i, true)
               constraint := ?_ }, ?_, ?_⟩
  · intro x y
    have := congrArg (fun M => M x y) hR
    simp only [gramR_apply, dualTarget_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases h : x i = y i
      · simp [h]
      · simp only [if_neg h]
        exact (hentry (x, i, false) (y, i, true)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc false x)
    exact Finset.sum_congr rfl fun i _ => (hentry (x, i, false) (x, i, false)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc true x)
    exact Finset.sum_congr rfl fun i _ => (hentry (x, i, true) (x, i, true)).symm

end QuantumQueryComplexity
