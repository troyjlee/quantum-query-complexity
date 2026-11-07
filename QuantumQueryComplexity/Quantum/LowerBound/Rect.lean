import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.ReadFactor
import QuantumQueryComplexity.Promise.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The general adversary bound for rectangular matrices

Lower bounds by the general adversary method are often stated with a rectangular matrix `Γ`
whose rows are indexed by positive inputs `Y` and whose columns are indexed by negative inputs
`X` [HLŠ07]; e.g. [CGKLPZ26, Lemma 2.10]. For a query index `i`, `Γ ∘ Δ_i` keeps the entries whose
two inputs disagree at `i` (`rectDOn`).

The symmetric block matrix `[[0, Γ], [Γᵀ, 0]]` on `Y ⊕ X` is an adversary matrix for the Boolean
function that is `true` on `Y` and `false` on `X`; its norm is `‖Γ‖` and its masked norms are
`‖Γ ∘ Δ_i‖`. So the promise adversary bound gives `‖Γ‖ / c ≤ advPMOn` whenever every masked norm
is at most `c` (`norm_div_le_advPMOn_rect`), and the sharp Boolean bound gives
`(1/36)(‖Γ‖/c) ≤ q` for every algorithm computing `f` with error `1/3` in `q` queries
(`le_of_computes_rect`), hence `(1/36)(‖Γ‖/c) ≤ Q_{1/3}(f)` (`le_boundedErrorQQuery_rect`).
Norms are `L²` operator norms.

## Main definitions

* `rectDOn readY readX i`: the disagreement mask `Δ_i` of a rectangular matrix.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {Y X : Type} [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]

/-- **The disagreement mask** `Δ_i(y, x) = 1[y_i ≠ x_i]` of a rectangular matrix with rows read by
`readY` and columns read by `readX` [CGKLPZ26, Lemma 2.10]. -/
def rectDOn (readY : Y → ι → σ) (readX : X → ι → σ) (i : ι) : Matrix Y X ℝ :=
  Matrix.of fun y x => if readY y i = readX x i then 0 else 1

/-! ## The L² operator norm of rectangular and symmetric block matrices -/

section BlockNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The bilinear bound for a rectangular matrix**:
`|x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * √(x ⬝ᵥ x) * √(y ⬝ᵥ y)`. -/
theorem abs_dotProduct_mulVec_le_rect (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    |x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have h1 : |x ⬝ᵥ A *ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) := by
    rw [← inner_toLp, ← norm_toLp_eq, ← norm_toLp_eq]
    exact abs_real_inner_le_norm _ _
  have h2 : Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ ‖A‖ * Real.sqrt (y ⬝ᵥ y) := by
    rw [← norm_toLp_eq, ← norm_toLp_eq]
    exact A.l2_opNorm_mulVec (WithLp.toLp 2 y)
  calc |x ⬝ᵥ A *ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * (‖A‖ * Real.sqrt (y ⬝ᵥ y)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    _ = ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by ring

/-- **The converse of the bilinear bound for a rectangular matrix**: a bound on the bilinear
form bounds the L² operator norm. -/
theorem l2_opNorm_le_of_forall_dotProduct_rect (A : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, |x ⬝ᵥ A *ᵥ y| ≤ c * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) :
    ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  set y : n → ℝ := WithLp.ofLp v with hy
  set w : m → ℝ := A *ᵥ y with hw
  have hval : (toEuclideanLin.trans LinearMap.toContinuousLinearMap) A v
      = (WithLp.toLp 2 w : EuclideanSpace ℝ m) := rfl
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

/-- The bilinear form of the symmetric block matrix `[[0, A], [Aᵀ, 0]]` in terms of `A`. -/
lemma dotProduct_fromBlocks_transpose_mulVec (A : Matrix m n ℝ) (u w : m ⊕ n → ℝ) :
    u ⬝ᵥ fromBlocks 0 A Aᵀ 0 *ᵥ w
      = (u ∘ Sum.inl) ⬝ᵥ A *ᵥ (w ∘ Sum.inr) + (w ∘ Sum.inl) ⬝ᵥ A *ᵥ (u ∘ Sum.inr) := by
  rw [fromBlocks_mulVec, mulVec_transpose]
  simp only [zero_mulVec, zero_add, add_zero, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Function.comp]
  congr 1
  rw [← dotProduct, ← dotProduct, dotProduct_comm, ← dotProduct_mulVec]
  rfl

/-- The squared length of a vector on `m ⊕ n` splits over the two summands. -/
lemma dotProduct_self_sum (u : m ⊕ n → ℝ) :
    u ⬝ᵥ u = (u ∘ Sum.inl) ⬝ᵥ (u ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (u ∘ Sum.inr) := by
  simp only [dotProduct, Fintype.sum_sum_type, Function.comp]

/-- **The norm of a symmetric block matrix**: `‖[[0, A], [Aᵀ, 0]]‖ = ‖A‖`. -/
theorem l2_opNorm_fromBlocks_transpose (A : Matrix m n ℝ) :
    ‖fromBlocks 0 A Aᵀ 0‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg A) fun u w => ?_
    rw [dotProduct_fromBlocks_transpose_mulVec, dotProduct_self_sum u, dotProduct_self_sum w]
    set u₁ := u ∘ Sum.inl
    set u₂ := u ∘ Sum.inr
    set w₁ := w ∘ Sum.inl
    set w₂ := w ∘ Sum.inr
    have h1 := abs_dotProduct_mulVec_le_rect A u₁ w₂
    have h2 := abs_dotProduct_mulVec_le_rect A w₁ u₂
    have hu₁ := dotProduct_self_nonneg u₁
    have hu₂ := dotProduct_self_nonneg u₂
    have hw₁ := dotProduct_self_nonneg w₁
    have hw₂ := dotProduct_self_nonneg w₂
    set a₁ := Real.sqrt (u₁ ⬝ᵥ u₁) with ha₁
    set a₂ := Real.sqrt (u₂ ⬝ᵥ u₂) with ha₂
    set b₁ := Real.sqrt (w₁ ⬝ᵥ w₁) with hb₁
    set b₂ := Real.sqrt (w₂ ⬝ᵥ w₂) with hb₂
    have hcs : a₁ * b₂ + b₁ * a₂
        ≤ Real.sqrt (u₁ ⬝ᵥ u₁ + u₂ ⬝ᵥ u₂) * Real.sqrt (w₁ ⬝ᵥ w₁ + w₂ ⬝ᵥ w₂) := by
      rw [← Real.sqrt_mul (show 0 ≤ u₁ ⬝ᵥ u₁ + u₂ ⬝ᵥ u₂ by positivity)]
      refine Real.le_sqrt_of_sq_le ?_
      have ea₁ : a₁ ^ 2 = u₁ ⬝ᵥ u₁ := Real.sq_sqrt hu₁
      have ea₂ : a₂ ^ 2 = u₂ ⬝ᵥ u₂ := Real.sq_sqrt hu₂
      have eb₁ : b₁ ^ 2 = w₁ ⬝ᵥ w₁ := Real.sq_sqrt hw₁
      have eb₂ : b₂ ^ 2 = w₂ ⬝ᵥ w₂ := Real.sq_sqrt hw₂
      rw [← ea₁, ← ea₂, ← eb₁, ← eb₂]
      nlinarith [sq_nonneg (a₁ * b₁ - a₂ * b₂)]
    calc |u₁ ⬝ᵥ A *ᵥ w₂ + w₁ ⬝ᵥ A *ᵥ u₂|
        ≤ |u₁ ⬝ᵥ A *ᵥ w₂| + |w₁ ⬝ᵥ A *ᵥ u₂| := abs_add_le _ _
      _ ≤ ‖A‖ * a₁ * b₂ + ‖A‖ * b₁ * a₂ := add_le_add h1 h2
      _ = ‖A‖ * (a₁ * b₂ + b₁ * a₂) := by ring
      _ ≤ ‖A‖ * (Real.sqrt (u₁ ⬝ᵥ u₁ + u₂ ⬝ᵥ u₂) * Real.sqrt (w₁ ⬝ᵥ w₁ + w₂ ⬝ᵥ w₂)) :=
        mul_le_mul_of_nonneg_left hcs (norm_nonneg A)
      _ = _ := by ring
  · refine l2_opNorm_le_of_forall_dotProduct_rect _ (norm_nonneg _) fun x y => ?_
    have h := abs_dotProduct_mulVec_le (fromBlocks 0 A Aᵀ 0)
      (Sum.elim x 0) (Sum.elim 0 y)
    rw [dotProduct_fromBlocks_transpose_mulVec, dotProduct_self_sum (Sum.elim x 0),
      dotProduct_self_sum (Sum.elim 0 y)] at h
    simpa [Function.comp_def] using h

end BlockNorm

/-! ## The symmetric block adversary matrix -/

/-- Masking the symmetric block matrix `[[0, Γ], [Γᵀ, 0]]` by `Δ_i` on `Y ⊕ X` masks `Γ` by the
rectangular disagreement mask `rectDOn readY readX i`. -/
lemma fromBlocks_hadamard_advDOn (readY : Y → ι → σ) (readX : X → ι → σ) (Γ : Matrix Y X ℝ)
    (i : ι) :
    fromBlocks 0 Γ Γᵀ 0 ⊙ advDOn (Sum.elim readY readX) i
      = fromBlocks 0 (Γ ⊙ rectDOn readY readX i) (Γ ⊙ rectDOn readY readX i)ᵀ 0 := by
  ext (a | a) (b | b)
  · simp
  · by_cases hab : readY a i = readX b i <;> simp [rectDOn, hab]
  · by_cases hab : readY b i = readX a i <;> simp [rectDOn, hab, eq_comm (a := readX a i)]
  · simp

/-- The symmetric block matrix `[[0, Γ], [Γᵀ, 0]]` is an adversary matrix for the Boolean
function that is `true` on `Y` and `false` on `X`. -/
lemma isAdvMatrixOn_fromBlocks (Γ : Matrix Y X ℝ) :
    IsAdvMatrixOn (Sum.elim (fun _ => true) (fun _ => false) : Y ⊕ X → Bool)
      (fromBlocks 0 Γ Γᵀ 0) := by
  refine ⟨?_, ?_⟩
  · rw [IsHermitian, fromBlocks_conjTranspose]
    simp [conjTranspose_eq_transpose_of_trivial]
  · rintro (a | a) (b | b) h <;> simp_all

/-- **The rectangular adversary bound, adversary form**: if no row input equals a column input,
and every masked norm `‖Γ ∘ Δ_i‖` is at most `c > 0`, then `‖Γ‖ / c` is at most the promise
adversary bound of the function that is `true` on the rows and `false` on the columns. -/
theorem norm_div_le_advPMOn_rect (readY : Y → ι → σ) (readX : X → ι → σ)
    (hne : ∀ y x, readY y ≠ readX x) (Γ : Matrix Y X ℝ) {c : ℝ} (hc : 0 < c)
    (h : ∀ i, ‖Γ ⊙ rectDOn readY readX i‖ ≤ c) :
    ‖Γ‖ / c ≤ advPMOn (Sum.elim readY readX)
      (Sum.elim (fun _ => true) (fun _ => false) : Y ⊕ X → Bool) := by
  have hdet : ∀ z z' : Y ⊕ X, Sum.elim readY readX z = Sum.elim readY readX z' →
      (Sum.elim (fun _ => true) (fun _ => false) : Y ⊕ X → Bool) z =
        (Sum.elim (fun _ => true) (fun _ => false) : Y ⊕ X → Bool) z' := by
    rintro (a | a) (b | b) hab
    · rfl
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · rfl
  have hM := norm_div_le_advPMOn hdet (isAdvMatrixOn_fromBlocks Γ) (c := c)
    (fun i => by
      rw [fromBlocks_hadamard_advDOn, l2_opNorm_fromBlocks_transpose]
      exact h i) hc
  rwa [l2_opNorm_fromBlocks_transpose] at hM

/-- **The general adversary bound, rectangular form** [HLŠ07; CGKLPZ26, Lemma 2.10]: for a Boolean
function `f`, a matrix `Γ` with rows read by positive inputs and columns read by negative inputs,
and `c > 0` bounding every masked norm, every algorithm computing `f` with error at most `1/3` in
`q` queries, on every finite workspace, has `(1/36)(‖Γ‖/c) ≤ q`. -/
theorem le_of_computes_rect (f : (ι → σ) → Bool) (readY : Y → ι → σ) (readX : X → ι → σ)
    (hY : ∀ y, f (readY y) = true) (hX : ∀ x, f (readX x) = false) (Γ : Matrix Y X ℝ) {c : ℝ}
    (hc : 0 < c) (h : ∀ i, ‖Γ ⊙ rectDOn readY readX i‖ ≤ c) {W : Type} [Fintype W]
    [DecidableEq W] (A : QAlg ι σ Bool W) (q : ℕ) (hA : ComputesWithErrorOn A q id f (1 / 3)) :
    (1 / 36 : ℝ) * (‖Γ‖ / c) ≤ q := by
  have hcomp : ComputesWithErrorOn A q (Sum.elim readY readX)
      (Sum.elim (fun _ => true) (fun _ => false) : Y ⊕ X → Bool) (1 / 3) := by
    rintro (y | x)
    · simpa [hY y] using hA (readY y)
    · simpa [hX x] using hA (readX x)
  have hne : ∀ y x, readY y ≠ readX x := fun y x hyx => by
    have hy := hY y
    rw [hyx, hX x] at hy
    exact Bool.false_ne_true hy
  have hadv := norm_div_le_advPMOn_rect readY readX hne Γ hc h
  have hs : Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3)) ≤ 17 / 36 := by
    calc Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))
        ≤ Real.sqrt ((17 / 36 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 17 / 36 := Real.sqrt_sq (by norm_num)
  have hb := advPMOn_le_of_computes_bool (by norm_num) (by norm_num) (by linarith [hs]) hcomp
  have h0 : 0 ≤ ‖Γ‖ / c := div_nonneg (norm_nonneg _) hc.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (h0.trans hadv)]

/-- **The general adversary bound, rectangular form**, for the bounded-error query complexity
`Q_{1/3}(f)` [HLŠ07; CGKLPZ26, Lemma 2.10]. -/
theorem le_boundedErrorQQuery_rect (f : (ι → σ) → Bool) (readY : Y → ι → σ)
    (readX : X → ι → σ) (hY : ∀ y, f (readY y) = true) (hX : ∀ x, f (readX x) = false)
    (Γ : Matrix Y X ℝ) {c : ℝ} (hc : 0 < c) (h : ∀ i, ‖Γ ⊙ rectDOn readY readX i‖ ≤ c) :
    (1 / 36 : ℝ) * (‖Γ‖ / c) ≤ boundedErrorQQuery f := by
  exact le_qQueryOn_real (queryCounts_nonempty (fun _ _ hxy => congrArg f hxy) (by norm_num))
    fun q _ _ _ A hA => le_of_computes_rect f readY readX hY hX Γ hc h A q hA

end QuantumQueryComplexity
