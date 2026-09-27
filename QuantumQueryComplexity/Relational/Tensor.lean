import QuantumQueryComplexity.Relational.Defs
import QuantumQueryComplexity.Composition.Eigen
set_option linter.style.header false

/-!
# Tensor machinery for the relational composition theorem

Ingredients for BL Theorem 22 beyond the functional case:

* the **half-mass property** of eigenvectors of bipartite matrices
  (`brestrict_mass_eq_half`) — BL's `‖z^{(0)}‖² = ‖z^{(1)}‖² = 1/2`;
* the inner-product factorization of tensor vectors
  (`tensorVec_dotProduct`);
* preservation of the `±1`-diagonal-conjugation inner product
  (`diagonal_chiSign_mulVec_dotProduct`);
* positive semidefiniteness of composed matrices with PSD outer matrix
  (`posSemidef_compose`), and the `χ_a χ_aᵀ` mask identity
  (`compose_hadamard_vecMulVec`), giving that composition preserves the
  relational adversary constraints (`isRelAdvMatrix_compose`).
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

section Mass

variable {U : Type*} [Fintype U]

lemma dotProduct_mulVec_comm {A : Matrix U U ℝ} (hA : A.IsHermitian)
    (x y : U → ℝ) : x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  conv_lhs => rw [← (Matrix.isHermitian_iff_isSymm.mp hA)]
  exact Matrix.dotProduct_transpose_mulVec ..

lemma sum_ite_sq_eq_brestrict (χb : U → Bool) (z : U → ℝ) (b : Bool) :
    ∑ u, (if χb u = b then z u * z u else 0)
      = brestrict χb b z ⬝ᵥ brestrict χb b z := by
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : χb u = b <;> simp [h]

/-- **Half-mass**: a unit eigenvector with nonzero eigenvalue of a
color-bipartite symmetric matrix has squared mass exactly `1/2` on each
color class (BL Eq. (3) observation). -/
theorem brestrict_mass_eq_half {M : Matrix U U ℝ} {χb : U → Bool}
    (hM : M.IsHermitian) (hzero : ∀ u v, χb u = χb v → M u v = 0)
    {z : U → ℝ} {θ : ℝ} (hz : M *ᵥ z = θ • z) (hθ : θ ≠ 0)
    (hunit : z ⬝ᵥ z = 1) (b : Bool) :
    brestrict χb b z ⬝ᵥ brestrict χb b z = 1 / 2 := by
  -- the restricted dot with `z` equals the class mass
  have hm : ∀ b' : Bool, brestrict χb b' z ⬝ᵥ z
      = brestrict χb b' z ⬝ᵥ brestrict χb b' z := by
    intro b'
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : χb u = b' <;> simp [h]
  -- masses of the two classes are equal
  have hmeq : brestrict χb b z ⬝ᵥ brestrict χb b z
      = brestrict χb (!b) z ⬝ᵥ brestrict χb (!b) z := by
    have h1 : brestrict χb b z ⬝ᵥ M *ᵥ z = θ * (brestrict χb b z ⬝ᵥ z) := by
      rw [hz, dotProduct_smul, smul_eq_mul]
    have h2 : brestrict χb b z ⬝ᵥ M *ᵥ z
        = θ * (brestrict χb (!b) z ⬝ᵥ z) := by
      rw [dotProduct_mulVec_comm hM, mulVec_brestrict_eigen hzero hz,
        dotProduct_smul, smul_eq_mul, dotProduct_comm]
    have h3 : θ * (brestrict χb b z ⬝ᵥ z)
        = θ * (brestrict χb (!b) z ⬝ᵥ z) := by rw [← h1, h2]
    have h4 := mul_left_cancel₀ hθ h3
    rw [hm b, hm (!b)] at h4
    exact h4
  -- masses sum to one
  have hsum : brestrict χb b z ⬝ᵥ brestrict χb b z
      + brestrict χb (!b) z ⬝ᵥ brestrict χb (!b) z = 1 := by
    rw [← hunit]
    rw [show z ⬝ᵥ z = ∑ u, z u * z u from rfl]
    rw [show brestrict χb b z ⬝ᵥ brestrict χb b z
        + brestrict χb (!b) z ⬝ᵥ brestrict χb (!b) z
      = ∑ u, ((if χb u = b then z u else 0) * (if χb u = b then z u else 0)
        + (if χb u = !b then z u else 0) * (if χb u = !b then z u else 0))
      from (Finset.sum_add_distrib).symm]
    refine Finset.sum_congr rfl fun u _ => ?_
    cases hb : χb u <;> cases b <;> simp
  linarith [hmeq, hsum]

end Mass

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma diagonal_chiSign_mulVec_dotProduct {ε : α → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (a b : (α → Bool) → ℝ) :
    (Matrix.diagonal (chiSign ε) *ᵥ a) ⬝ᵥ (Matrix.diagonal (chiSign ε) *ᵥ b)
      = a ⬝ᵥ b := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc chiSign ε x * a x * (chiSign ε x * b x)
      = chiSign ε x * chiSign ε x * (a x * b x) := by ring
    _ = a x * b x := by rw [chiSign_mul_self hε x, one_mul]

/-- The fiber decomposition of a tilde-weighted product sum. -/
lemma sum_tilde_mul_prod_slice {g : α → (β → Bool) → Bool}
    (F : (α → Bool) → ℝ) (G : α → (β → Bool) → ℝ) :
    ∑ x : (α × β) → Bool, F (tilde g x) * ∏ i, G i (slice x i)
      = ∑ b : α → Bool, F b * ∏ i, ∑ u, (if g i u = b i then G i u else 0) := by
  have hins : ∀ x : (α × β) → Bool, F (tilde g x) * ∏ i, G i (slice x i)
      = ∑ b : α → Bool, F b *
          ∏ i, (if g i (slice x i) = b i then G i (slice x i) else 0) := by
    intro x
    symm
    rw [Finset.sum_eq_single (tilde g x)]
    · congr 1
      exact Finset.prod_congr rfl fun i _ => if_pos rfl
    · intro b _ hb
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (if_neg fun h => hi (h.symm.trans (tilde_apply g x i).symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun x _ => hins x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact sum_prod_slice fun i u => if g i u = b i then G i u else 0

/-- Inner products of tensor vectors factor through class masses. -/
lemma tensorVec_dotProduct {g : α → (β → Bool) → Bool}
    (v : α → (β → Bool) → ℝ) (w₁ w₂ : (α → Bool) → ℝ) :
    tensorVec g v w₁ ⬝ᵥ tensorVec g v w₂
      = ∑ b : α → Bool, w₁ b * w₂ b *
          ∏ i, ∑ u, (if g i u = b i then v i u * v i u else 0) := by
  calc tensorVec g v w₁ ⬝ᵥ tensorVec g v w₂
      = ∑ x : (α × β) → Bool, (w₁ (tilde g x) * w₂ (tilde g x)) *
          ∏ i, (v i (slice x i) * v i (slice x i)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [tensorVec_apply]
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ b : α → Bool, w₁ b * w₂ b *
          ∏ i, ∑ u, (if g i u = b i then v i u * v i u else 0) :=
        sum_tilde_mul_prod_slice (fun b => w₁ b * w₂ b)
          (fun i u => v i u * v i u)

/-- The composed matrix as a Hadamard product of a lifted outer matrix and a
PSD product of lifted hats. -/
lemma compose_eq_submatrix_hadamard (g : α → (β → Bool) → Bool)
    (B : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) :
    compose g B M = (B.submatrix (tilde g) (tilde g)) ⊙
      (Matrix.of fun x y : (α × β) → Bool =>
        ∏ i, hat (M i) (slice x i) (slice y i)) := by
  ext x y
  rw [compose_apply, Matrix.hadamard_apply, Matrix.submatrix_apply,
    Matrix.of_apply]

/-- Composition with a PSD outer matrix is PSD (BL Facts 2–3 + Lemma 18). -/
lemma posSemidef_compose {g : α → (β → Bool) → Bool}
    {B : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hB : B.PosSemidef) (hM : ∀ i, (M i).IsHermitian) :
    (compose g B M).PosSemidef := by
  rw [compose_eq_submatrix_hadamard]
  refine (hB.submatrix _).hadamard ?_
  exact posSemidef_prod_lift (F := fun i => hat (M i))
    (fun i => posSemidef_add_norm_smul_one (hM i))
    (fun i (x : (α × β) → Bool) => slice x i) Finset.univ

lemma compose_neg (g : α → (β → Bool) → Bool)
    (B : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) :
    compose g (-B) M = -(compose g B M) := by
  ext x y
  simp only [compose_apply, Matrix.neg_apply]
  ring

/-- The `χ_a χ_aᵀ` mask identity (BL Theorem 22, item (2) mechanism). -/
lemma compose_hadamard_vecMulVec (g : α → (β → Bool) → Bool)
    (B : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) (φ : (α → Bool) → ℝ) :
    compose g B M ⊙ Matrix.vecMulVec (fun x => φ (tilde g x))
        (fun x => φ (tilde g x))
      = compose g (B ⊙ Matrix.vecMulVec φ φ) M := by
  ext x y
  simp only [Matrix.hadamard_apply, compose_apply, Matrix.vecMulVec_apply]
  ring

/-- Composition preserves the relational adversary constraints. -/
lemma isRelAdvMatrix_compose {κ' : Type*} {χ : κ' → (α → Bool) → Bool}
    {g : α → (β → Bool) → Bool} {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hf : IsRelAdvMatrix χ Γf) (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    IsRelAdvMatrix (fun a x => χ a (tilde g x)) (compose g Γf M) := by
  refine ⟨compose_isHermitian g hf.1 fun i => (hM i).isHermitian, fun a => ?_⟩
  have hphi : chiVec (fun a x => χ a (tilde g x)) a
      = fun x => chiVec χ a (tilde g x) := rfl
  rw [hphi, compose_hadamard_vecMulVec g Γf M (chiVec χ a), ← compose_neg]
  exact posSemidef_compose (hf.2 a) fun i => (hM i).isHermitian

end QuantumQueryComplexity
