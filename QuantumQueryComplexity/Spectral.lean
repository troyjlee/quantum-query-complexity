import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option linter.style.header false

/-!
# Spectral-norm infrastructure for the adversary bound

Layer-0 lemmas about the L2 operator norm of real matrices.  All
`EuclideanSpace`/`WithLp` friction is quarantined inside the proofs of this
file: every exported statement is phrased with raw `Matrix`, `*ᵥ`, `⬝ᵥ` and
`Real.sqrt (x ⬝ᵥ x)`.

Main results:
* `abs_dotProduct_mulVec_le` — the master bilinear bound
  `|x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * √(x ⬝ᵥ x) * √(y ⬝ᵥ y)`;
* `l2_opNorm_le_of_forall_dotProduct` — its converse;
* `abs_entry_le_l2_opNorm` — entries are bounded by the norm;
* `l2_opNorm_le_sum_abs` — the crude bound `‖A‖ ≤ ∑ |A x y|`;
* `abs_eigenvalue_le_norm` — eigenvalues are bounded by the norm.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

variable {n : Type*} [Fintype n]

lemma dotProduct_self_nonneg (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma norm_toLp_eq (x : n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

lemma inner_toLp (x y : n → ℝ) :
    ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ n), WithLp.toLp 2 y⟫ = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]

lemma abs_apply_le_sqrt_dotProduct_self (x : n → ℝ) (i : n) :
    |x i| ≤ Real.sqrt (x ⬝ᵥ x) := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  simpa [sq, dotProduct] using
    Finset.single_le_sum (f := fun j => x j * x j)
      (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

lemma dotProduct_mulVec_eq_sum (A : Matrix n n ℝ) (u w : n → ℝ) :
    u ⬝ᵥ A *ᵥ w = ∑ x, ∑ y, u x * A x y * w y := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

variable [DecidableEq n]

/-- Master bilinear bound for the L2 operator norm. -/
theorem abs_dotProduct_mulVec_le (A : Matrix n n ℝ) (x y : n → ℝ) :
    |x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have h := Matrix.inner_toEuclideanCLM A (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  calc |x ⬝ᵥ A *ᵥ y|
      = |⟪(WithLp.toLp 2 x : EuclideanSpace ℝ n),
          Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 y)⟫| := by rw [h]
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 y)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
            ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
          (norm_nonneg _)
    _ = ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [← Matrix.cstar_norm_def, norm_toLp_eq, norm_toLp_eq]; ring

/-- Converse of the master bilinear bound. -/
theorem l2_opNorm_le_of_forall_dotProduct (A : Matrix n n ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ x y, |x ⬝ᵥ A *ᵥ y| ≤ c * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) :
    ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  set y : n → ℝ := WithLp.ofLp v with hy
  set w : n → ℝ := A *ᵥ y with hw
  have hval : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = WithLp.toLp 2 w := by
    conv_lhs => rw [show v = WithLp.toLp 2 y from rfl]
    rw [Matrix.toEuclideanCLM_toLp]
  have hnv : ‖v‖ = Real.sqrt (y ⬝ᵥ y) := by
    rw [show v = WithLp.toLp 2 y from rfl, norm_toLp_eq]
  rw [hval, norm_toLp_eq, hnv]
  have key := h w y
  rw [← hw] at key
  have habs : |w ⬝ᵥ w| = w ⬝ᵥ w := abs_of_nonneg (dotProduct_self_nonneg w)
  have hww : w ⬝ᵥ w = Real.sqrt (w ⬝ᵥ w) * Real.sqrt (w ⬝ᵥ w) :=
    (Real.mul_self_sqrt (dotProduct_self_nonneg w)).symm
  set s := Real.sqrt (w ⬝ᵥ w) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · rw [← h0]
    positivity
  · rw [habs, hww] at key
    nlinarith [key, h0, Real.sqrt_nonneg (y ⬝ᵥ y)]

/-- Every entry is bounded by the L2 operator norm. -/
theorem abs_entry_le_l2_opNorm (A : Matrix n n ℝ) (x y : n) : |A x y| ≤ ‖A‖ := by
  have h := abs_dotProduct_mulVec_le A (Pi.single x 1) (Pi.single y 1)
  have h1 : (Pi.single x 1 : n → ℝ) ⬝ᵥ A *ᵥ Pi.single y 1 = A x y := by
    simp [mulVec_single_one, single_dotProduct]
  have h2 : (Pi.single x 1 : n → ℝ) ⬝ᵥ Pi.single x 1 = 1 := by
    simp [single_dotProduct]
  have h3 : (Pi.single y 1 : n → ℝ) ⬝ᵥ Pi.single y 1 = 1 := by
    simp [single_dotProduct]
  rw [h1, h2, h3, Real.sqrt_one] at h
  simpa using h

/-- Crude norm bound: the L2 operator norm is at most the sum of the absolute
values of the entries. -/
theorem l2_opNorm_le_sum_abs (A : Matrix n n ℝ) :
    ‖A‖ ≤ ∑ x, ∑ y, |A x y| := by
  refine l2_opNorm_le_of_forall_dotProduct A
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun u v => ?_
  rw [dotProduct_mulVec_eq_sum]
  calc |∑ a, ∑ b, u a * A a b * v b|
      ≤ ∑ a, ∑ b, |u a * A a b * v b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, |A a b| * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_mul]
        have h12 : |u a| * |v b| ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
          mul_le_mul (abs_apply_le_sqrt_dotProduct_self u a)
            (abs_apply_le_sqrt_dotProduct_self v b) (abs_nonneg _)
            (Real.sqrt_nonneg _)
        calc |u a| * |A a b| * |v b| = |A a b| * (|u a| * |v b|) := by ring
          _ ≤ |A a b| * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) :=
              mul_le_mul_of_nonneg_left h12 (abs_nonneg _)
    _ = (∑ x, ∑ y, |A x y|) * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
        simp_rw [← Finset.sum_mul]
    _ = (∑ x, ∑ y, |A x y|) * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
        (mul_assoc _ _ _).symm

/-- An eigenvalue of any square real matrix is bounded by the L2 operator
norm. -/
theorem abs_eigenvalue_le_norm {A : Matrix n n ℝ} {v : n → ℝ} {θ : ℝ}
    (hv : A *ᵥ v = θ • v) (hv0 : v ≠ 0) : |θ| ≤ ‖A‖ := by
  have h := abs_dotProduct_mulVec_le A v v
  rw [hv] at h
  have hsmul : v ⬝ᵥ (θ • v) = θ * (v ⬝ᵥ v) := by
    simp [dotProduct_smul, smul_eq_mul]
  rw [hsmul, abs_mul, abs_of_nonneg (dotProduct_self_nonneg v)] at h
  have hvv : 0 < v ⬝ᵥ v := by
    rcases (dotProduct_self_nonneg v).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (dotProduct_self_eq_zero.mp h'.symm) hv0
  have hsq : Real.sqrt (v ⬝ᵥ v) * Real.sqrt (v ⬝ᵥ v) = v ⬝ᵥ v :=
    Real.mul_self_sqrt (dotProduct_self_nonneg v)
  rw [mul_assoc, hsq] at h
  exact le_of_mul_le_mul_right h hvv

/-- Reindexing a square matrix along an injection of index types does not
increase the L2 operator norm. -/
theorem l2_opNorm_submatrix_le {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (e : m ≃ n) : ‖A.submatrix e e‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg A) fun x y => ?_
  have hdot : ∀ z : m → ℝ,
      (fun a => z (e.symm a)) ⬝ᵥ (fun a => z (e.symm a)) = z ⬝ᵥ z := fun z =>
    Equiv.sum_comp e.symm fun a => z a * z a
  have hbil : x ⬝ᵥ (A.submatrix e e) *ᵥ y
      = (fun a => x (e.symm a)) ⬝ᵥ A *ᵥ (fun b => y (e.symm b)) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum,
      ← Equiv.sum_comp e (fun a => ∑ b, x (e.symm a) * A a b * y (e.symm b))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Equiv.sum_comp e
      (fun b => x (e.symm (e p)) * A (e p) b * y (e.symm b))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Matrix.submatrix_apply]
  rw [hbil, ← hdot x, ← hdot y]
  exact abs_dotProduct_mulVec_le _ _ _

/-- Reindexing a square matrix by a bijection preserves the L2 operator
norm. -/
theorem l2_opNorm_submatrix_equiv {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (e : m ≃ n) : ‖A.submatrix e e‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_submatrix_le A e) ?_
  have h := l2_opNorm_submatrix_le (A.submatrix e e) e.symm
  rwa [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at h

/-! ## The eigenvalue layer -/

/-- For a real symmetric matrix, the L2 operator norm equals the sup norm of
the eigenvalue vector.  Proof: spectral theorem plus unitary invariance of the
C*-norm, plus `‖diagonal v‖ = ‖v‖`. -/
theorem norm_eq_norm_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _
      (Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.prop,
    Matrix.l2_opNorm_diagonal, RCLike.ofReal_real_eq_id, Function.id_comp]

theorem abs_eigenvalues_le_norm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (j : n) : |hA.eigenvalues j| ≤ ‖A‖ := by
  rw [norm_eq_norm_eigenvalues hA]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hA.eigenvalues j

theorem exists_abs_eigenvalues_eq_norm [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ∃ j, |hA.eigenvalues j| = ‖A‖ := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset n)
    Finset.univ_nonempty (fun i => ‖hA.eigenvalues i‖₊)
  refine ⟨j, ?_⟩
  rw [norm_eq_norm_eigenvalues hA, Pi.norm_def, hj]
  simp [Real.norm_eq_abs]

theorem norm_le_of_forall_abs_eigenvalues_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j, |hA.eigenvalues j| ≤ B) : ‖A‖ ≤ B := by
  rw [norm_eq_norm_eigenvalues hA]
  refine (pi_norm_le_iff_of_nonneg hB).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact h j

/-- **Spanning-eigenvector bound.**  If a family of eigenvectors of a real
symmetric matrix spans the whole space and all its eigenvalues are bounded by
`B` in absolute value, then `‖A‖ ≤ B`.  Members of the family are allowed to
be zero. -/
theorem norm_le_of_eigenvector_family [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {κ : Type*} (v : κ → n → ℝ) (μ : κ → ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (heig : ∀ k, A *ᵥ v k = μ k • v k)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hμ : ∀ k, |μ k| ≤ B) : ‖A‖ ≤ B := by
  refine norm_le_of_forall_abs_eigenvalues_le hA hB fun j => ?_
  by_contra hlt
  push_neg at hlt
  set w : n → ℝ := WithLp.ofLp (hA.eigenvectorBasis j) with hwdef
  have hw0 : w ≠ 0 := fun h0 =>
    hA.eigenvectorBasis.orthonormal.ne_zero j (by
      have hb : hA.eigenvectorBasis j = WithLp.toLp 2 w := rfl
      rw [hb, h0]
      rfl)
  have hAw : A *ᵥ w = hA.eigenvalues j • w := hA.mulVec_eigenvectorBasis j
  have hAT : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA)
  have horth : ∀ k, w ⬝ᵥ v k = 0 := by
    intro k
    have hsymm : w ⬝ᵥ A *ᵥ v k = v k ⬝ᵥ A *ᵥ w := by
      conv_lhs => rw [← hAT]
      exact Matrix.dotProduct_transpose_mulVec ..
    have h1 : w ⬝ᵥ A *ᵥ v k = μ k * (w ⬝ᵥ v k) := by
      rw [heig k, dotProduct_smul, smul_eq_mul]
    have h2 : v k ⬝ᵥ A *ᵥ w = hA.eigenvalues j * (v k ⬝ᵥ w) := by
      rw [hAw, dotProduct_smul, smul_eq_mul]
    have key : hA.eigenvalues j * (w ⬝ᵥ v k) = μ k * (w ⬝ᵥ v k) := by
      calc hA.eigenvalues j * (w ⬝ᵥ v k)
          = hA.eigenvalues j * (v k ⬝ᵥ w) := by rw [dotProduct_comm]
        _ = v k ⬝ᵥ A *ᵥ w := h2.symm
        _ = w ⬝ᵥ A *ᵥ v k := hsymm.symm
        _ = μ k * (w ⬝ᵥ v k) := h1
    have hne : hA.eigenvalues j ≠ μ k := fun hEq =>
      absurd (by rw [hEq]; exact hμ k) (not_le.mpr hlt)
    have hfac : (hA.eigenvalues j - μ k) * (w ⬝ᵥ v k) = 0 := by
      linarith [key]
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact h'
  let φ : (n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => w ⬝ᵥ u
      map_add' := fun a b => dotProduct_add w a b
      map_smul' := fun c u => by simp [dotProduct_smul] }
  have hker : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact horth k
  have hw_in : w ∈ LinearMap.ker φ :=
    hker (by rw [hspan]; exact Submodule.mem_top)
  have hww : w ⬝ᵥ w = 0 := LinearMap.mem_ker.mp hw_in
  exact hw0 (dotProduct_self_eq_zero.mp hww)

/-- Conjugation by a `±1` diagonal matrix preserves the L2 operator norm. -/
theorem l2_opNorm_conj_diagonal_sign {s : n → ℝ}
    (hs : ∀ a, s a = 1 ∨ s a = -1) (X : Matrix n n ℝ) :
    ‖Matrix.diagonal s * X * Matrix.diagonal s‖ = ‖X‖ := by
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hss : (fun a => s a * s a) = fun _ => (1 : ℝ) := by
      funext a
      rcases hs a with h | h <;> rw [h] <;> norm_num
    rw [hss, Matrix.diagonal_one]
  have hstar : star (Matrix.diagonal s) = Matrix.diagonal s := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  have hmem : Matrix.diagonal s ∈ unitary (Matrix n n ℝ) :=
    Unitary.mem_iff.mpr ⟨by rw [hstar, hDD], by rw [hstar, hDD]⟩
  rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ hmem,
    CStarRing.norm_mul_mem_unitary _ hmem]

end QuantumQueryComplexity
