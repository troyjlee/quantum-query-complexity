import QuantumQueryComplexity.Spectral
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Single-cell projectors and the Hamming scheme, entrywise

The lower bound for element distinctness (Belovs, arXiv:1204.5074)
manipulates matrices on `(ι → σ)` built cell by
cell from the two projectors

    E₀ = (1/q)·J     and     E₁ = I − E₀        (q = card σ),

with no auxiliary eigenbasis: everything here is an entry computation.

* `piMat M` — the cellwise product matrix `(x,y) ↦ ∏ c, M c (x c) (y c)`;
  multiplicative (`piMat_mul`) by Fubini over the product of cells.
* `schemeProd T` — `E₁` on the cells of `T`, `E₀` elsewhere; two of these
  multiply to `0` unless the sets coincide.
* `weightProj k` — the weight-`k` projector of the Hamming association
  scheme, `∑_{|T|=k} schemeProd T`: pairwise-orthogonal symmetric idempotents
  summing to `1`.
* `norm_combo_le` — a nonnegative combination of pairwise-orthogonal
  symmetric projectors dominated by the identity has norm at most the largest
  coefficient.  This is the only norm fact the Gram analysis needs.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The two single-cell projectors -/

/-- The averaging projector: all entries `1/q`. -/
noncomputable def cellE0 : Matrix σ σ ℝ :=
  Matrix.of fun _ _ => (Fintype.card σ : ℝ)⁻¹

/-- The complement `I − E₀`. -/
noncomputable def cellE1 : Matrix σ σ ℝ :=
  Matrix.of fun u v =>
    (if u = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹

lemma cellE1_eq : (cellE1 : Matrix σ σ ℝ) = 1 - cellE0 := by
  ext u v
  simp [cellE1, cellE0, Matrix.one_apply]

lemma cellE1_add_cellE0 : (cellE1 : Matrix σ σ ℝ) + cellE0 = 1 := by
  rw [cellE1_eq]
  abel

lemma cellE0_transpose : (cellE0 : Matrix σ σ ℝ)ᵀ = cellE0 := rfl

lemma cellE1_transpose : (cellE1 : Matrix σ σ ℝ)ᵀ = cellE1 := by
  ext u v
  simp only [Matrix.transpose_apply, cellE1, Matrix.of_apply]
  by_cases h : u = v
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg fun hc => h hc.symm, if_neg h]

lemma cellE0_mul_cellE0 [Nonempty σ] :
    (cellE0 : Matrix σ σ ℝ) * cellE0 = cellE0 := by
  ext u v
  simp only [Matrix.mul_apply, cellE0, Matrix.of_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma cellE0_mul_cellE1 [Nonempty σ] :
    (cellE0 : Matrix σ σ ℝ) * cellE1 = 0 := by
  rw [cellE1_eq, Matrix.mul_sub, Matrix.mul_one, cellE0_mul_cellE0, sub_self]

lemma cellE1_mul_cellE0 [Nonempty σ] :
    (cellE1 : Matrix σ σ ℝ) * cellE0 = 0 := by
  rw [cellE1_eq, Matrix.sub_mul, Matrix.one_mul, cellE0_mul_cellE0, sub_self]

lemma cellE1_mul_cellE1 [Nonempty σ] :
    (cellE1 : Matrix σ σ ℝ) * cellE1 = cellE1 := by
  have h := cellE0_mul_cellE0 (σ := σ)
  rw [cellE1_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, h]
  abel

/-! ## Cellwise product matrices -/

/-- The cellwise product of a family of single-cell matrices. -/
noncomputable def piMat (M : ι → Matrix σ σ ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y => ∏ c, M c (x c) (y c)

lemma piMat_apply (M : ι → Matrix σ σ ℝ) (x y : ι → σ) :
    piMat M x y = ∏ c, M c (x c) (y c) := rfl

/-- Fubini over the cells: cellwise products multiply cellwise. -/
lemma piMat_mul (M N : ι → Matrix σ σ ℝ) :
    piMat M * piMat N = piMat fun c => M c * N c := by
  ext x y
  simp only [Matrix.mul_apply, piMat, Matrix.of_apply]
  calc ∑ z : ι → σ, (∏ c, M c (x c) (z c)) * ∏ c, N c (z c) (y c)
      = ∑ z : ι → σ, ∏ c, (M c (x c) (z c) * N c (z c) (y c)) :=
        Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib.symm
    _ = ∑ z ∈ Fintype.piFinset fun _ : ι => (Finset.univ : Finset σ),
          ∏ c, (M c (x c) (z c) * N c (z c) (y c)) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ c, ∑ s : σ, M c (x c) s * N c s (y c) :=
        Finset.sum_prod_piFinset Finset.univ
          fun c s => M c (x c) s * N c s (y c)
    _ = ∏ c, (M c * N c) (x c) (y c) :=
        Finset.prod_congr rfl fun c _ => (Matrix.mul_apply).symm

lemma piMat_transpose (M : ι → Matrix σ σ ℝ) :
    (piMat M)ᵀ = piMat fun c => (M c)ᵀ := by
  ext x y
  simp [piMat, Matrix.transpose_apply]

lemma piMat_one : piMat (fun _ : ι => (1 : Matrix σ σ ℝ)) = 1 := by
  ext x y
  simp only [piMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy]
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc])

/-! ## Scheme products and weight projectors -/

/-- `E₁` on the cells of `T`, `E₀` elsewhere. -/
noncomputable def schemeProd (T : Finset ι) : Matrix (ι → σ) (ι → σ) ℝ :=
  piMat fun c => if c ∈ T then cellE1 else cellE0

lemma schemeProd_transpose (T : Finset ι) :
    (schemeProd (σ := σ) T)ᵀ = schemeProd T := by
  rw [schemeProd, piMat_transpose]
  congr 1
  funext c
  by_cases hc : c ∈ T
  · rw [if_pos hc, cellE1_transpose]
  · rw [if_neg hc, cellE0_transpose]

lemma schemeProd_mul [Nonempty σ] (T U : Finset ι) :
    schemeProd (σ := σ) T * schemeProd U
      = if T = U then schemeProd T else 0 := by
  rw [schemeProd, schemeProd, piMat_mul]
  by_cases hTU : T = U
  · subst hTU
    rw [if_pos rfl]
    congr 1
    funext c
    by_cases hc : c ∈ T
    · rw [if_pos hc, cellE1_mul_cellE1]
    · rw [if_neg hc, cellE0_mul_cellE0]
  · rw [if_neg hTU]
    obtain ⟨c, hc⟩ : ∃ c, ¬ (c ∈ T ↔ c ∈ U) := by
      by_contra hall
      push_neg at hall
      exact hTU (Finset.ext fun c => hall c)
    ext x y
    simp only [piMat, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    by_cases h1 : c ∈ T
    · have h2 : c ∉ U := fun h => hc ⟨fun _ => h, fun _ => h1⟩
      rw [if_pos h1, if_neg h2, cellE1_mul_cellE0, Matrix.zero_apply]
    · have h2 : c ∈ U := by
        by_contra h2
        exact hc ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      rw [if_neg h1, if_pos h2, cellE0_mul_cellE1, Matrix.zero_apply]

/-- The weight-`k` projector of the Hamming scheme. -/
noncomputable def weightProj (k : ℕ) : Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ T ∈ Finset.powersetCard k (Finset.univ : Finset ι),
    schemeProd (σ := σ) T

lemma weightProj_transpose (k : ℕ) :
    (weightProj (σ := σ) (ι := ι) k)ᵀ = weightProj k := by
  rw [weightProj, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun T _ => schemeProd_transpose T

lemma weightProj_mul [Nonempty σ] (k l : ℕ) :
    weightProj (σ := σ) (ι := ι) k * weightProj l
      = if k = l then weightProj k else 0 := by
  rw [weightProj, weightProj, Finset.sum_mul]
  have hstep : ∀ T ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      (schemeProd (σ := σ) T *
        ∑ U ∈ Finset.powersetCard l (Finset.univ : Finset ι), schemeProd U)
      = if k = l then schemeProd T else 0 := by
    intro T hT
    rw [Finset.mul_sum,
      Finset.sum_congr rfl fun U _ => schemeProd_mul T U,
      Finset.sum_ite_eq (Finset.powersetCard l (Finset.univ : Finset ι)) T
        fun _ => schemeProd T]
    have hcard := (Finset.mem_powersetCard.mp hT).2
    by_cases hkl : k = l
    · rw [if_pos (Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by omega⟩), if_pos hkl]
    · rw [if_neg fun hc =>
        hkl (by rw [← hcard, (Finset.mem_powersetCard.mp hc).2]), if_neg hkl]
  rw [Finset.sum_congr rfl hstep]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    exact Finset.sum_congr rfl fun T _ => if_pos hkl
  · rw [if_neg hkl]
    rw [Finset.sum_congr rfl fun T (_ : T ∈ _) => if_neg hkl,
      Finset.sum_const, smul_zero]

/-- The weight projectors resolve the identity. -/
lemma sum_weightProj [Nonempty σ] :
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
      weightProj (σ := σ) (ι := ι) k) = 1 := by
  have hpow : (∑ k ∈ Finset.range (Fintype.card ι + 1),
      weightProj (σ := σ) (ι := ι) k)
      = ∑ T ∈ (Finset.univ : Finset ι).powerset, schemeProd (σ := σ) T := by
    rw [Finset.sum_powerset, Finset.card_univ]
    rfl
  rw [hpow, ← piMat_one]
  ext x y
  rw [Matrix.sum_apply]
  calc (∑ T ∈ (Finset.univ : Finset ι).powerset,
        schemeProd (σ := σ) T x y)
      = ∑ T ∈ (Finset.univ : Finset ι).powerset,
          (∏ c ∈ T, cellE1 (x c) (y c)) *
            ∏ c ∈ Finset.univ \ T, cellE0 (x c) (y c) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [schemeProd, piMat_apply,
          Finset.prod_congr rfl fun c (_ : c ∈ Finset.univ) =>
            apply_ite (fun M : Matrix σ σ ℝ => M (x c) (y c)) (c ∈ T)
              cellE1 cellE0,
          Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
          ← Finset.sdiff_eq_filter]
    _ = ∏ c, (cellE1 (x c) (y c) + cellE0 (x c) (y c)) :=
        (Finset.prod_add _ _ _).symm
    _ = piMat (fun _ : ι => (1 : Matrix σ σ ℝ)) x y := by
        rw [piMat_apply]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [show cellE1 (x c) (y c) + cellE0 (x c) (y c)
            = (cellE1 + cellE0 : Matrix σ σ ℝ) (x c) (y c) from rfl,
          cellE1_add_cellE0]

/-! ## Norms of projector combinations -/

/-- The quadratic form of a symmetric idempotent is the squared length of the
projection. -/
lemma proj_quadform {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hsymm : Pᵀ = P) (hidem : P * P = P) (v : X → ℝ) :
    (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ v) := by
  calc (P *ᵥ v) ⬝ᵥ (P *ᵥ v)
      = v ᵥ* Pᵀ ⬝ᵥ (P *ᵥ v) := by rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ (Pᵀ *ᵥ (P *ᵥ v)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = v ⬝ᵥ (P *ᵥ (P *ᵥ v)) := by rw [hsymm]
    _ = v ⬝ᵥ ((P * P) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = v ⬝ᵥ (P *ᵥ v) := by rw [hidem]

/-- A symmetric idempotent contracts lengths. -/
lemma proj_contraction {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hsymm : Pᵀ = P) (hidem : P * P = P) (v : X → ℝ) :
    (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ v := by
  have h1 := proj_quadform hsymm hidem v
  have hCS : v ⬝ᵥ (P *ᵥ v)
      ≤ Real.sqrt (v ⬝ᵥ v) * Real.sqrt ((P *ᵥ v) ⬝ᵥ (P *ᵥ v)) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v (P *ᵥ v)
    simpa [dotProduct, pow_two] using h
  have ha0 : 0 ≤ (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := dotProduct_self_nonneg _
  have hb0 : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg _
  nlinarith [h1, hCS, Real.mul_self_sqrt ha0, Real.mul_self_sqrt hb0,
    Real.sqrt_nonneg ((P *ᵥ v) ⬝ᵥ (P *ᵥ v)), Real.sqrt_nonneg (v ⬝ᵥ v),
    sq_nonneg (Real.sqrt (v ⬝ᵥ v) - Real.sqrt ((P *ᵥ v) ⬝ᵥ (P *ᵥ v)))]

/-- Multiplying a symmetric matrix on the left of a vector, `vecMul` form. -/
lemma symm_vecMul {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hsymm : Pᵀ = P) (v : X → ℝ) : v ᵥ* P = P *ᵥ v := by
  conv_lhs => rw [← hsymm]
  rw [Matrix.vecMul_transpose]

/-- The summed quadratic form of a pairwise-orthogonal projector family. -/
lemma sum_proj_quadform {X : Type*} [Fintype X] {J : Type*} (S : Finset J)
    {P : J → Matrix X X ℝ} (hsymm : ∀ j ∈ S, (P j)ᵀ = P j)
    (hproj : ∀ j ∈ S, P j * P j = P j) (v : X → ℝ) :
    (∑ j ∈ S, (P j *ᵥ v) ⬝ᵥ (P j *ᵥ v)) = v ⬝ᵥ ((∑ j ∈ S, P j) *ᵥ v) := by
  rw [Finset.sum_congr rfl fun j hj =>
    proj_quadform (hsymm j hj) (hproj j hj) v]
  rw [Matrix.sum_mulVec]
  exact (dotProduct_sum _ _ _).symm

/-- **Nonnegative combinations of orthogonal projectors**: if the family is
symmetric, pairwise orthogonal and dominated by the identity, the norm of
`∑ c_j P_j` is at most `max c_j`. -/
theorem norm_combo_le {X : Type*} [Fintype X] [DecidableEq X] {J : Type*}
    [DecidableEq J] (S : Finset J) {P : J → Matrix X X ℝ}
    (hsymm : ∀ j ∈ S, (P j)ᵀ = P j)
    (hproj : ∀ j ∈ S, ∀ j' ∈ S, P j * P j' = if j = j' then P j else 0)
    (hdom : ∀ v : X → ℝ,
      (∑ j ∈ S, (P j *ᵥ v) ⬝ᵥ (P j *ᵥ v)) ≤ v ⬝ᵥ v)
    {c : J → ℝ} (hc : ∀ j ∈ S, 0 ≤ c j) {b : ℝ} (hb : ∀ j ∈ S, c j ≤ b)
    (hb0 : 0 ≤ b) :
    ‖∑ j ∈ S, c j • P j‖ ≤ b := by
  refine l2_opNorm_le_of_forall_dotProduct _ hb0 fun v w => ?_
  have hexp : v ⬝ᵥ ((∑ j ∈ S, c j • P j) *ᵥ w)
      = ∑ j ∈ S, c j * ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ w)) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    calc v ⬝ᵥ (P j *ᵥ w)
        = v ⬝ᵥ ((P j * P j) *ᵥ w) := by rw [hproj j hj j hj, if_pos rfl]
      _ = v ⬝ᵥ (P j *ᵥ (P j *ᵥ w)) := by rw [Matrix.mulVec_mulVec]
      _ = v ᵥ* P j ⬝ᵥ (P j *ᵥ w) := Matrix.dotProduct_mulVec _ _ _
      _ = (P j *ᵥ v) ⬝ᵥ (P j *ᵥ w) := by rw [symm_vecMul (hsymm j hj)]
  rw [hexp]
  calc |∑ j ∈ S, c j * ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ w))|
      ≤ ∑ j ∈ S, |c j * ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ w))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S, b * (Real.sqrt ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ v))
          * Real.sqrt ((P j *ᵥ w) ⬝ᵥ (P j *ᵥ w))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (hc j hj)]
        have hCSj : |(P j *ᵥ v) ⬝ᵥ (P j *ᵥ w)|
            ≤ Real.sqrt ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ v))
              * Real.sqrt ((P j *ᵥ w) ⬝ᵥ (P j *ᵥ w)) := by
          rw [abs_le]
          constructor
          · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
              (fun t => -(P j *ᵥ v) t) (P j *ᵥ w)
            simp only [dotProduct, pow_two] at this ⊢
            have hrw : (∑ t, -(P j *ᵥ v) t * (P j *ᵥ w) t)
                = -(∑ t, (P j *ᵥ v) t * (P j *ᵥ w) t) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun t _ => by ring
            rw [hrw] at this
            have hsq : (∑ t, -(P j *ᵥ v) t * -(P j *ᵥ v) t)
                = ∑ t, (P j *ᵥ v) t * (P j *ᵥ v) t :=
              Finset.sum_congr rfl fun t _ => by ring
            rw [hsq] at this
            linarith
          · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
              (P j *ᵥ v) (P j *ᵥ w)
            simpa [dotProduct, pow_two] using this
        calc c j * |(P j *ᵥ v) ⬝ᵥ (P j *ᵥ w)|
            ≤ b * |(P j *ᵥ v) ⬝ᵥ (P j *ᵥ w)| :=
              mul_le_mul_of_nonneg_right (hb j hj) (abs_nonneg _)
          _ ≤ b * (Real.sqrt ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ v))
                * Real.sqrt ((P j *ᵥ w) ⬝ᵥ (P j *ᵥ w))) :=
              mul_le_mul_of_nonneg_left hCSj hb0
    _ = b * ∑ j ∈ S, Real.sqrt ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ v))
          * Real.sqrt ((P j *ᵥ w) ⬝ᵥ (P j *ᵥ w)) := by
        rw [Finset.mul_sum]
    _ ≤ b * (Real.sqrt (∑ j ∈ S, (P j *ᵥ v) ⬝ᵥ (P j *ᵥ v))
          * Real.sqrt (∑ j ∈ S, (P j *ᵥ w) ⬝ᵥ (P j *ᵥ w))) := by
        refine mul_le_mul_of_nonneg_left ?_ hb0
        have := Real.sum_mul_le_sqrt_mul_sqrt S
          (fun j => Real.sqrt ((P j *ᵥ v) ⬝ᵥ (P j *ᵥ v)))
          (fun j => Real.sqrt ((P j *ᵥ w) ⬝ᵥ (P j *ᵥ w)))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _)] using this
    _ ≤ b * (Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.sqrt_le_sqrt (hdom v)) (Real.sqrt_le_sqrt (hdom w))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hb0
    _ = b * Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w) := by ring

end QuantumQueryComplexity
