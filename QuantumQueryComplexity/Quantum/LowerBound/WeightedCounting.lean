import Mathlib.Analysis.CStarAlgebra.Matrix

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Weighted counting

A bound on a sum of local maps, used to estimate the denominator `‖Γ ∘ Δ_i‖` of an adversary
bound by counting [CGKLPZ26, Lemma 6.7]. Let `D_j` (`j ∈ ι`) be matrices from `n` to `m` such that

* the target spaces are pairwise orthogonal: `D_jᴴ D_{j'} = 0` for `j ≠ j'`;
* `D_j` reads only the source coordinates in `I_j`: its other columns are zero;
* `‖D_j‖ ≤ w_j`.

Then for every vector `f`,

    ‖∑_j D_j f‖² ≤ ∑_i (∑_{j : i ∈ I_j} w_j²) |f_i|²     (`weighted_counting`).

Each source coordinate is charged once for every local map that can read it, so the bound holds
for arbitrary vectors even when different maps read some of the same coordinates. If every
coordinate's total charge is at most `c²`, then `‖∑_j D_j‖ ≤ c`
(`l2_opNorm_sum_le_weighted_counting`). Maps with no common nonzero row have orthogonal target
spaces (`conjTranspose_mul_eq_zero_of_rows`).

Proof: with `Q_j` the coordinate projection onto `I_j`, `D_j = D_j Q_j`, so
`‖D_j f‖² ≤ w_j² ‖Q_j f‖²`; orthogonality gives `‖∑_j D_j f‖² = ∑_j ‖D_j f‖²`; interchange the
two sums.

Norms of matrices are `L²` operator norms; vectors are measured by their sums of squared entries.

## References

* [CGKLPZ26] Cornelissen, Gilani, Kintali, Le Gall, Patro and Zhou, *Breaking the quantum barriers
  for Graph Collision*, arXiv:2611.05356v1, Lemma 6.7.
-/

namespace QuantumQueryComplexity

open Matrix
open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq n]

/-- A matrix whose columns outside `s` vanish and with `‖A‖ ≤ w` satisfies
`‖A f‖² ≤ w² ∑_{i ∈ s} |f_i|²`. -/
private lemma sum_norm_mulVec_sq_le (A : Matrix m n 𝕜) (s : Finset n) {w : ℝ}
    (hread : ∀ a i, i ∉ s → A a i = 0) (hnorm : ‖A‖ ≤ w) (f : n → 𝕜) :
    ∑ a, ‖(A *ᵥ f) a‖ ^ 2 ≤ w ^ 2 * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  set g : n → 𝕜 := fun i => if i ∈ s then f i else 0
  have hAg : A *ᵥ f = A *ᵥ g := by
    ext a
    simp only [mulVec, dotProduct, g]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ s <;> simp [hi, hread a i]
  have hg : ‖(EuclideanSpace.equiv n 𝕜).symm g‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [g, apply_ite]
  have hAf : ∑ a, ‖(A *ᵥ f) a‖ ^ 2 = ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ g)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, hAg]
    rfl
  have h := l2_opNorm_mulVec A ((EuclideanSpace.equiv n 𝕜).symm g)
  rw [hAf, ← hg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h.trans <|
    mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) 2

/-- Pairwise orthogonal targets: `‖∑_j D_j f‖² = ∑_j ‖D_j f‖²`. -/
private lemma sum_norm_sum_mulVec_sq (D : ι → Matrix m n 𝕜)
    (horth : ∀ j j', j ≠ j' → (D j)ᴴ * D j' = 0) (f : n → 𝕜) :
    ∑ a, ‖((∑ j, D j) *ᵥ f) a‖ ^ 2 = ∑ j, ∑ a, ‖(D j *ᵥ f) a‖ ^ 2 := by
  have key : ∀ v : m → 𝕜, ((∑ a, ‖v a‖ ^ 2 : ℝ) : 𝕜) = star v ⬝ᵥ v := by
    intro v
    simp [dotProduct, RCLike.conj_mul]
  have hcross : ∀ j j', j ≠ j' → star (D j *ᵥ f) ⬝ᵥ (D j' *ᵥ f) = 0 := by
    intro j j' hjj'
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, horth j j' hjj', vecMul_zero,
      zero_dotProduct]
  have h𝕜 : ((∑ a, ‖((∑ j, D j) *ᵥ f) a‖ ^ 2 : ℝ) : 𝕜) =
      ((∑ j, ∑ a, ‖(D j *ᵥ f) a‖ ^ 2 : ℝ) : 𝕜) := by
    rw [key, RCLike.ofReal_sum]
    simp_rw [key]
    rw [sum_mulVec, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_sum]
    exact Finset.sum_eq_single j (fun j' _ hj' => hcross j j' (Ne.symm hj')) (by simp)
  exact_mod_cast h𝕜

/-- **Weighted counting** [CGKLPZ26, Lemma 6.7]: if the maps `D_j` have pairwise orthogonal
target spaces, `D_j` reads only the coordinates in `I_j`, and `‖D_j‖ ≤ w_j`, then
`‖∑_j D_j f‖² ≤ ∑_i (∑_{j : i ∈ I_j} w_j²) |f_i|²` for every vector `f`. -/
theorem weighted_counting (D : ι → Matrix m n 𝕜) (I : ι → Finset n) (w : ι → ℝ)
    (horth : ∀ j j', j ≠ j' → (D j)ᴴ * D j' = 0) (hread : ∀ j a i, i ∉ I j → D j a i = 0)
    (hnorm : ∀ j, ‖D j‖ ≤ w j) (f : n → 𝕜) :
    ∑ a, ‖((∑ j, D j) *ᵥ f) a‖ ^ 2 ≤ ∑ i, (∑ j with i ∈ I j, w j ^ 2) * ‖f i‖ ^ 2 := by
  calc ∑ a, ‖((∑ j, D j) *ᵥ f) a‖ ^ 2 = ∑ j, ∑ a, ‖(D j *ᵥ f) a‖ ^ 2 :=
        sum_norm_sum_mulVec_sq D horth f
    _ ≤ ∑ j, w j ^ 2 * ∑ i ∈ I j, ‖f i‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => sum_norm_mulVec_sq_le (D j) (I j) (hread j) (hnorm j) f
    _ = ∑ i, (∑ j with i ∈ I j, w j ^ 2) * ‖f i‖ ^ 2 := by
        simp_rw [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp

/-- **Weighted counting, operator form**: under the hypotheses of `weighted_counting`, if every
source coordinate has total charge `∑_{j : i ∈ I_j} w_j² ≤ c²`, then `‖∑_j D_j‖ ≤ c`. -/
theorem l2_opNorm_sum_le_weighted_counting (D : ι → Matrix m n 𝕜) (I : ι → Finset n)
    (w : ι → ℝ) (horth : ∀ j j', j ≠ j' → (D j)ᴴ * D j' = 0)
    (hread : ∀ j a i, i ∉ I j → D j a i = 0) (hnorm : ∀ j, ‖D j‖ ≤ w j) {c : ℝ} (hc : 0 ≤ c)
    (hcount : ∀ i, ∑ j with i ∈ I j, w j ^ 2 ≤ c ^ 2) :
    ‖∑ j, D j‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  change ‖(EuclideanSpace.equiv m 𝕜).symm ((∑ j, D j) *ᵥ x)‖ ≤ c * ‖x‖
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  calc ∑ a, ‖(EuclideanSpace.equiv m 𝕜).symm ((∑ j, D j) *ᵥ x) a‖ ^ 2
      = ∑ a, ‖((∑ j, D j) *ᵥ x) a‖ ^ 2 := rfl
    _ ≤ ∑ i, (∑ j with i ∈ I j, w j ^ 2) * ‖x i‖ ^ 2 :=
        weighted_counting D I w horth hread hnorm x
    _ ≤ ∑ i, c ^ 2 * ‖x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcount i) (sq_nonneg _)

/-- **Orthogonal targets from disjoint rows**: if no row is nonzero in both `A` and `B`, then
`Aᴴ B = 0`. -/
theorem conjTranspose_mul_eq_zero_of_rows (A B : Matrix m n 𝕜)
    (h : ∀ a, (∀ i, A a i = 0) ∨ (∀ i, B a i = 0)) : Aᴴ * B = 0 := by
  ext i k
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [conjTranspose_apply]
  rcases h a with ha | hb
  · rw [ha i, star_zero, zero_mul]
  · rw [hb k, mul_zero]

end QuantumQueryComplexity
