import QuantumQueryComplexity.Spectral
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hadamard

set_option linter.style.header false

/-!
# The Schur-multiplier norm bound

The key estimate `‖X ⊙ P‖ ≤ d * ‖X‖` for a positive semidefinite `P` whose
diagonal entries are at most `d` (`norm_hadamard_posSemidef_le`), proved via a
Gram decomposition of `P` and Cauchy–Schwarz.  In the composition theorem this
replaces the sign-flipping analysis of HLŠ Lemma 16 (following the PSD
viewpoint of Belovs–Lee, arXiv:2004.06439 §4).

Also: small PSD facts — the all-ones matrix, the `2×2` seed
`[[R, λ], [λ, R]]` for `|λ| ≤ R`, and `M + ‖M‖ • 1 ⪰ 0` for symmetric `M`
(BL Lemma 18).  The "PSD lift" fact (BL Fact 2) is mathlib's
`Matrix.PosSemidef.submatrix`, which takes an arbitrary index map.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {n : Type*} [Fintype n]

/-- The all-ones matrix is positive semidefinite. -/
lemma posSemidef_allOnes :
    (Matrix.of fun _ _ : n => (1 : ℝ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show _ᴴ = _
    ext i j
    simp [Matrix.conjTranspose_apply]
  · have hmul : (Matrix.of fun _ _ : n => (1 : ℝ)) *ᵥ x
        = fun _ => ∑ j, x j := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    rw [star_trivial, hmul]
    have hdp : x ⬝ᵥ (fun _ => ∑ j, x j) = (∑ i, x i) * (∑ j, x j) := by
      simp [dotProduct, ← Finset.sum_mul]
    rw [hdp]
    exact mul_self_nonneg _

/-- The `2×2` seed: `[[R, lam], [lam, R]]` is PSD when `|lam| ≤ R`. -/
lemma posSemidef_boolPair {R lam : ℝ} (h : |lam| ≤ R) :
    (Matrix.of fun a b : Bool => if a = b then R else lam).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show _ᴴ = _
    ext a b
    simp [Matrix.conjTranspose_apply, eq_comm]
  · rw [star_trivial]
    rcases abs_le.mp h with ⟨h1, h2⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (x true + x false), sq_nonneg (x true - x false)]

variable [DecidableEq n]

/-- **Schur-multiplier bound** (Belovs–Lee): if `P` is positive semidefinite
with all diagonal entries at most `d`, then `‖X ⊙ P‖ ≤ d * ‖X‖`. -/
theorem norm_hadamard_posSemidef_le (X : Matrix n n ℝ) {P : Matrix n n ℝ}
    (hP : P.PosSemidef) {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ a, P a a ≤ d) :
    ‖X ⊙ P‖ ≤ d * ‖X‖ := by
  obtain ⟨m, gv, hgv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  have hPab : ∀ a b, P a b = ∑ k, gv k a * gv k b := by
    intro a b
    rw [hgv]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  refine l2_opNorm_le_of_forall_dotProduct _ (mul_nonneg hd (norm_nonneg X))
    fun x y => ?_
  -- Step 1: expand the bilinear form along the Gram decomposition.
  have step1 : x ⬝ᵥ (X ⊙ P) *ᵥ y
      = ∑ k, (fun a => gv k a * x a) ⬝ᵥ X *ᵥ (fun b => gv k b * y b) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.hadamard_apply, Finset.mul_sum]
    have e1 : ∀ a b, x a * (X a b * P a b * y b)
        = ∑ k, (gv k a * x a) * (X a b * (gv k b * y b)) := by
      intro a b
      rw [hPab a b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ a, ∑ b, x a * (X a b * P a b * y b)
        = ∑ a, ∑ b, ∑ k, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e1 a b
      _ = ∑ a, ∑ k, ∑ b, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_comm
  rw [step1]
  -- Notation for the reweighted vectors and their lengths.
  set xk : Fin m → n → ℝ := fun k a => gv k a * x a with hxk
  set yk : Fin m → n → ℝ := fun k b => gv k b * y b with hyk
  -- Step 5 (used twice): the total squared length is controlled by the
  -- diagonal of `P`.
  have hlen : ∀ (z : n → ℝ) (zk : Fin m → n → ℝ),
      (∀ k a, zk k a = gv k a * z a) →
      ∑ k, zk k ⬝ᵥ zk k ≤ d * (z ⬝ᵥ z) := by
    intro z zk hzk
    have hz : ∑ k, zk k ⬝ᵥ zk k = ∑ a, (z a * z a) * P a a := by
      simp only [dotProduct, hzk]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hPab a a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hz]
    calc ∑ a, (z a * z a) * P a a ≤ ∑ a, (z a * z a) * d :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hdiag a) (mul_self_nonneg _)
      _ = d * (z ⬝ᵥ z) := by
        rw [← Finset.sum_mul, mul_comm]
        rfl
  -- Steps 2–4: triangle inequality, the master bound per `k`, and
  -- Cauchy–Schwarz over `k`.
  calc |∑ k, xk k ⬝ᵥ X *ᵥ yk k|
      ≤ ∑ k, |xk k ⬝ᵥ X *ᵥ yk k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖X‖ * (Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := abs_dotProduct_mulVec_le X (xk k) (yk k)
        calc |xk k ⬝ᵥ X *ᵥ yk k|
            ≤ ‖X‖ * Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k) := this
          _ = ‖X‖ * (Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k)) :=
              mul_assoc _ _ _
    _ = ‖X‖ * ∑ k, Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ‖X‖ * (Real.sqrt (∑ k, xk k ⬝ᵥ xk k) * Real.sqrt (∑ k, yk k ⬝ᵥ yk k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg X)
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k => Real.sqrt (xk k ⬝ᵥ xk k)) (fun k => Real.sqrt (yk k ⬝ᵥ yk k))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _)] using hcs
    _ ≤ ‖X‖ * (Real.sqrt (d * (x ⬝ᵥ x)) * Real.sqrt (d * (y ⬝ᵥ y))) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg X)
        exact mul_le_mul (Real.sqrt_le_sqrt (hlen x xk fun k a => rfl))
          (Real.sqrt_le_sqrt (hlen y yk fun k a => rfl)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = d * ‖X‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul hd, Real.sqrt_mul hd]
        rw [show Real.sqrt d * Real.sqrt (x ⬝ᵥ x) *
            (Real.sqrt d * Real.sqrt (y ⬝ᵥ y))
            = Real.sqrt d * Real.sqrt d *
              (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) from by ring,
          Real.mul_self_sqrt hd]
        ring

/-- `M + ‖M‖ • 1` is positive semidefinite for symmetric `M`
(BL Lemma 18). -/
theorem posSemidef_add_norm_smul_one {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (M + ‖M‖ • (1 : Matrix n n ℝ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hM.add (Matrix.isHermitian_one.smul (star_trivial _))) fun x => ?_
  rw [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul]
  have h1 := abs_dotProduct_mulVec_le M x x
  have h2 := Real.mul_self_sqrt (dotProduct_self_nonneg x)
  have h3 := neg_abs_le (x ⬝ᵥ M *ᵥ x)
  rw [smul_eq_mul]
  nlinarith [Real.sqrt_nonneg (x ⬝ᵥ x), norm_nonneg M]

end QuantumQueryComplexity
