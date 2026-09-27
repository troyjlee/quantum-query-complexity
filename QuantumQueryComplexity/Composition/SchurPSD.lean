import QuantumQueryComplexity.Composition.Hat
import Mathlib.Analysis.Matrix.Order
set_option linter.style.header false

/-!
# The outer auxiliary matrices `Γf ⊙ Emat` and their PSD structure

For an assignment of eigenvalues `lamv i` (with `|lamv i| ≤ R i`), the matrix

  `Emat R lamv a b = ∏ i, if a i = b i then R i else lamv i`

is positive semidefinite: it is the entrywise product over `i : α` of lifts of
the `2×2` seeds `[[R i, lamv i], [lamv i, R i]]` along the coordinate maps
`a ↦ a i` (mathlib's `Matrix.PosSemidef.submatrix` — BL Fact 2 — plus the
Schur product theorem `Matrix.PosSemidef.hadamard`).  Its diagonal is
`∏ i, R i`, so the Schur-multiplier bound gives
`‖Γf ⊙ Emat R lamv‖ ≤ (∏ i, R i) * ‖Γf‖` — replacing the sign-flipping
analysis of HLŠ Lemma 16.

At a "vertex" (`lamv i = ε i * R i` with `ε i = ±1`), `Γf ⊙ Emat` becomes a
`±1`-diagonal conjugate of `(∏ R) • Γf` (`hadamard_Emat_vertex`), which is the
witness used in the `≥` direction.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Entrywise products of PSD matrices lifted along arbitrary maps are PSD
(`Finset` induction from the Schur product theorem; BL Facts 2 and 3). -/
lemma posSemidef_prod_lift {ι E κ : Type*} [Fintype E]
    {F : ι → Matrix κ κ ℝ} (hF : ∀ i, (F i).PosSemidef) (e : ι → E → κ)
    (s : Finset ι) :
    Matrix.PosSemidef (Matrix.of fun a b : E => ∏ i ∈ s, F i (e i a) (e i b)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using posSemidef_allOnes (n := E)
  | @insert j s hj ih =>
      have heq : (Matrix.of fun a b : E => ∏ i ∈ insert j s, F i (e i a) (e i b))
          = ((F j).submatrix (e j) (e j)) ⊙
            (Matrix.of fun a b : E => ∏ i ∈ s, F i (e i a) (e i b)) := by
        ext a b
        simp [Finset.prod_insert hj, Matrix.hadamard_apply,
          Matrix.submatrix_apply]
      rw [heq]
      exact ((hF j).submatrix _).hadamard ih

/-- Entrywise products of PSD matrices lifted along coordinate evaluations
are PSD. -/
lemma posSemidef_prod_eval {F : α → Matrix Bool Bool ℝ}
    (hF : ∀ i, (F i).PosSemidef) (s : Finset α) :
    Matrix.PosSemidef
      (Matrix.of fun a b : α → Bool => ∏ i ∈ s, F i (a i) (b i)) :=
  posSemidef_prod_lift hF (fun i (a : α → Bool) => a i) s

/-- The outer auxiliary matrix of HLŠ Lemma 16 (denoted `A_c` there, with
`lamv i` the eigenvalue selected in slot `i`). -/
noncomputable def Emat (R lamv : α → ℝ) : Matrix (α → Bool) (α → Bool) ℝ :=
  Matrix.of fun a b => ∏ i, if a i = b i then R i else lamv i

@[simp] lemma Emat_apply (R lamv : α → ℝ) (a b : α → Bool) :
    Emat R lamv a b = ∏ i, if a i = b i then R i else lamv i := rfl

lemma Emat_isHermitian (R lamv : α → ℝ) : (Emat R lamv).IsHermitian := by
  show (Emat R lamv)ᴴ = Emat R lamv
  ext a b
  simp only [Matrix.conjTranspose_apply, Emat_apply, star_trivial]
  exact Finset.prod_congr rfl fun i _ => if_congr eq_comm rfl rfl

lemma Emat_posSemidef {R lamv : α → ℝ} (h : ∀ i, |lamv i| ≤ R i) :
    (Emat R lamv).PosSemidef :=
  posSemidef_prod_eval
    (F := fun i => Matrix.of fun s t : Bool => if s = t then R i else lamv i)
    (fun i => posSemidef_boolPair (h i)) Finset.univ

lemma Emat_diag (R lamv : α → ℝ) (a : α → Bool) :
    Emat R lamv a a = ∏ i, R i :=
  Finset.prod_congr rfl fun i _ => if_pos rfl

/-- The Schur-multiplier estimate for the outer auxiliary matrix. -/
lemma norm_hadamard_Emat_le (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    {R lamv : α → ℝ} (hR : ∀ i, 0 ≤ R i) (h : ∀ i, |lamv i| ≤ R i) :
    ‖Γf ⊙ Emat R lamv‖ ≤ (∏ i, R i) * ‖Γf‖ :=
  norm_hadamard_posSemidef_le Γf (Emat_posSemidef h)
    (Finset.prod_nonneg fun i _ => hR i) fun a => (Emat_diag R lamv a).le

/-- The `±1` character vector attached to a sign assignment. -/
def chiSign (ε : α → ℝ) : (α → Bool) → ℝ := fun a => ∏ i, if a i then ε i else 1

lemma chiSign_mul_self {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) (a : α → Bool) :
    chiSign ε a * chiSign ε a = 1 := by
  rw [chiSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : a i <;> simp [h, hε i]

lemma Emat_vertex {R ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) (a b : α → Bool) :
    Emat R (fun i => ε i * R i) a b
      = (∏ i, R i) * (chiSign ε a * chiSign ε b) := by
  simp only [Emat_apply, chiSign]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hab : a i = b i
  · rw [if_pos hab, hab]
    by_cases hb : b i <;> simp [hb, hε i]
  · rw [if_neg hab]
    cases ha : a i <;> cases hb : b i <;> simp_all <;> ring

lemma diagonal_chiSign_mul_self {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) :
    Matrix.diagonal (chiSign ε) * Matrix.diagonal (chiSign ε) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun a => chiSign ε a * chiSign ε a) = fun _ => (1 : ℝ) from
    funext fun a => chiSign_mul_self hε a]
  exact Matrix.diagonal_one

lemma chiSign_diagonal_mulVec_ne_zero {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1)
    {w : (α → Bool) → ℝ} (hw0 : w ≠ 0) :
    Matrix.diagonal (chiSign ε) *ᵥ w ≠ 0 := by
  intro h0
  apply hw0
  calc w = (1 : Matrix (α → Bool) (α → Bool) ℝ) *ᵥ w :=
      (Matrix.one_mulVec w).symm
    _ = (Matrix.diagonal (chiSign ε) * Matrix.diagonal (chiSign ε)) *ᵥ w := by
        rw [diagonal_chiSign_mul_self hε]
    _ = Matrix.diagonal (chiSign ε) *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

/-- At a sign vertex, `Γf ⊙ Emat` is a `±1`-diagonal conjugate of
`(∏ R) • Γf`. -/
lemma hadamard_Emat_vertex (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    {R ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) :
    Γf ⊙ Emat R (fun i => ε i * R i)
      = (∏ i, R i) •
        (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε)) := by
  ext a b
  rw [Matrix.hadamard_apply, Emat_vertex hε, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end QuantumQueryComplexity
