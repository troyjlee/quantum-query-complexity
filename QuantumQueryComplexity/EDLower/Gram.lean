import QuantumQueryComplexity.EDLower.PairOps
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Recognizing block Grams as scheme projectors

The Gram of two block terms factorizes (`blockTerm_transpose_mul`); this file
identifies the results.  With `T, U` inside the pair complement:

* two `F'`-terms: `if T = U then schemeProd (T ∪ {b}) else 0`, and the
  mirror for `F''` with `T ∪ {a}`;
* two `F₀`-terms: `if T = U then schemeProd T else 0`;
* an `F₀`-term against an `F₁`-term (either order): `0`;
* two `F₁`-terms: for `T = U`, the sum of `schemeProd (T ∪ {a})`,
  `schemeProd (T ∪ {b})`, and the two *swap couplings* — the same two
  projectors with the columns reindexed by the coordinate transposition
  `swapInput a b`.  Reindexing the columns by a bijection does not increase
  the operator norm (`l2_opNorm_submatrix_id_le`), which is all the norm
  analysis will need.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Column reindexing -/

/-- Reindexing only the columns by a bijection does not increase the norm. -/
theorem l2_opNorm_submatrix_id_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (e : n ≃ n) : ‖A.submatrix id ⇑e‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg A) fun x y => ?_
  have hdot : (fun b => y (e.symm b)) ⬝ᵥ (fun b => y (e.symm b)) = y ⬝ᵥ y :=
    Equiv.sum_comp e.symm fun b => y b * y b
  have hbil : x ⬝ᵥ (A.submatrix id ⇑e) *ᵥ y
      = x ⬝ᵥ A *ᵥ (fun b => y (e.symm b)) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Equiv.sum_comp e (fun b => x p * A p b * y (e.symm b))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Matrix.submatrix_apply]
  rw [hbil, ← hdot]
  exact abs_dotProduct_mulVec_le _ _ _

/-- The coordinate transposition acting on inputs. -/
def swapInput (a b : ι) : (ι → σ) ≃ (ι → σ) :=
  Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl σ)

lemma swapInput_apply (a b : ι) (z : ι → σ) (c : ι) :
    swapInput (σ := σ) a b z c = z (Equiv.swap a b c) := by
  simp [swapInput, Equiv.arrowCongr]

lemma swapInput_apply_left (a b : ι) (z : ι → σ) :
    swapInput (σ := σ) a b z a = z b := by
  rw [swapInput_apply, Equiv.swap_apply_left]

lemma swapInput_apply_right (a b : ι) (z : ι → σ) :
    swapInput (σ := σ) a b z b = z a := by
  rw [swapInput_apply, Equiv.swap_apply_right]

lemma swapInput_apply_of_ne {a b c : ι} (hca : c ≠ a) (hcb : c ≠ b)
    (z : ι → σ) : swapInput (σ := σ) a b z c = z c := by
  rw [swapInput_apply, Equiv.swap_apply_of_ne_of_ne hca hcb]

/-! ## Splitting a scheme projector at the pair -/

lemma schemeProd_apply_pair {a b : ι} (hab : a ≠ b) (S : Finset ι)
    (y z : ι → σ) :
    schemeProd (σ := σ) S y z
      = ((if a ∈ S then cellE1 else cellE0 : Matrix σ σ ℝ) (y a) (z a))
        * ((if b ∈ S then cellE1 else cellE0 : Matrix σ σ ℝ) (y b) (z b))
        * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
            ((if c ∈ S then cellE1 else cellE0 : Matrix σ σ ℝ) (y c) (z c)) :=
  prod_univ_pair_compl hab _

/-- Membership bookkeeping: `a` is not in `T ∪ {b}` when `T` avoids the
pair. -/
lemma left_notMem_insert_right {a b : ι} (hab : a ≠ b) {T : Finset ι}
    (hT : T ⊆ ({a, b} : Finset ι)ᶜ) : a ∉ insert b T := by
  intro h
  rcases Finset.mem_insert.mp h with h | h
  · exact hab h
  · exact (Finset.mem_compl.mp (hT h)) (Finset.mem_insert_self a {b})

lemma right_notMem_insert_left {a b : ι} (hab : a ≠ b) {T : Finset ι}
    (hT : T ⊆ ({a, b} : Finset ι)ᶜ) : b ∉ insert a T := by
  intro h
  rcases Finset.mem_insert.mp h with h | h
  · exact hab h.symm
  · exact (Finset.mem_compl.mp (hT h))
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))

lemma mem_insert_iff_of_compl {x c : ι} {T : Finset ι}
    (hcx : c ≠ x) : (c ∈ insert x T) ↔ c ∈ T := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact absurd h hcx
    · exact h
  · exact Finset.mem_insert_of_mem

/-- Zero from a differing pattern cell: if `T ≠ U` (both inside the pair
complement), some cell kills the product. -/
lemma prod_pattern_mul_eq_zero {a b : ι} {T U : Finset ι} [Nonempty σ]
    (hT : T ⊆ ({a, b} : Finset ι)ᶜ) (hU : U ⊆ ({a, b} : Finset ι)ᶜ)
    (hTU : T ≠ U) (y z : ι → σ) :
    (∏ c ∈ ({a, b} : Finset ι)ᶜ,
      (((if c ∈ T then cellE1 else cellE0)
        * (if c ∈ U then cellE1 else cellE0) : Matrix σ σ ℝ) (y c) (z c)))
    = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, ¬ (c ∈ T ↔ c ∈ U) := by
    by_contra hall
    push_neg at hall
    exact hTU (Finset.ext fun c => hall c)
  have hcmem : c ∈ ({a, b} : Finset ι)ᶜ := by
    by_cases hcT : c ∈ T
    · exact hT hcT
    · by_cases hcU : c ∈ U
      · exact hU hcU
      · exact absurd ⟨fun h => absurd h hcT, fun h => absurd h hcU⟩ hc
  refine Finset.prod_eq_zero hcmem ?_
  by_cases hcT : c ∈ T
  · have hcU : c ∉ U := fun h => hc ⟨fun _ => h, fun _ => hcT⟩
    rw [if_pos hcT, if_neg hcU, cellE1_mul_cellE0, Matrix.zero_apply]
  · have hcU : c ∈ U := by
      by_contra hcU
      exact hc ⟨fun h => absurd h hcT, fun h => absurd h hcU⟩
    rw [if_neg hcT, if_pos hcU, cellE0_mul_cellE1, Matrix.zero_apply]

/-- The diagonal pattern product collapses by idempotence. -/
lemma pattern_mul_self {c : ι} (T : Finset ι) [Nonempty σ] (u v : σ) :
    (((if c ∈ T then cellE1 else cellE0)
      * (if c ∈ T then cellE1 else cellE0) : Matrix σ σ ℝ) u v)
    = ((if c ∈ T then cellE1 else cellE0 : Matrix σ σ ℝ) u v) := by
  by_cases hcT : c ∈ T
  · rw [if_pos hcT, cellE1_mul_cellE1]
  · rw [if_neg hcT, cellE0_mul_cellE0]

/-! ## The `F'`, `F''` and `F₀` Grams -/

/-- Gram of two `F'` block terms: the scheme projector on `T ∪ {b}`. -/
lemma gram_blockTerm_edF' [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T U : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ)
    (hU : U ⊆ ({a, b} : Finset ι)ᶜ) :
    (blockTerm a b (edF' (σ := σ)) T)ᵀ * blockTerm a b edF' U
      = if T = U then schemeProd (insert b T) else 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_edF'_edF']
  by_cases hTU : T = U
  · subst hTU
    rw [if_pos rfl]
    ext y z
    rw [Matrix.of_apply, schemeProd_apply_pair hab,
      if_neg (left_notMem_insert_right hab hT),
      if_pos (Finset.mem_insert_self b T), Matrix.of_apply]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [pattern_mul_self]
    have hcb : c ≠ b := fun h => (Finset.mem_compl.mp hc)
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    by_cases hcT : c ∈ T
    · rw [if_pos hcT, if_pos ((mem_insert_iff_of_compl hcb).mpr hcT)]
    · rw [if_neg hcT, if_neg (fun h => hcT ((mem_insert_iff_of_compl hcb).mp h))]
  · rw [if_neg hTU]
    ext y z
    rw [Matrix.of_apply, prod_pattern_mul_eq_zero hT hU hTU y z, mul_zero,
      Matrix.zero_apply]

/-- Gram of two `F''` block terms: the scheme projector on `T ∪ {a}`. -/
lemma gram_blockTerm_edF'' [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T U : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ)
    (hU : U ⊆ ({a, b} : Finset ι)ᶜ) :
    (blockTerm a b (edF'' (σ := σ)) T)ᵀ * blockTerm a b edF'' U
      = if T = U then schemeProd (insert a T) else 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_edF''_edF'']
  by_cases hTU : T = U
  · subst hTU
    rw [if_pos rfl]
    ext y z
    rw [Matrix.of_apply, schemeProd_apply_pair hab,
      if_pos (Finset.mem_insert_self a T),
      if_neg (right_notMem_insert_left hab hT), Matrix.of_apply]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [pattern_mul_self]
    have hca : c ≠ a := fun h => (Finset.mem_compl.mp hc)
      (by rw [h]; exact Finset.mem_insert_self a {b})
    by_cases hcT : c ∈ T
    · rw [if_pos hcT, if_pos ((mem_insert_iff_of_compl hca).mpr hcT)]
    · rw [if_neg hcT, if_neg (fun h => hcT ((mem_insert_iff_of_compl hca).mp h))]
  · rw [if_neg hTU]
    ext y z
    rw [Matrix.of_apply, prod_pattern_mul_eq_zero hT hU hTU y z, mul_zero,
      Matrix.zero_apply]

/-- Gram of two `F₀` block terms: the scheme projector on `T` itself. -/
lemma gram_blockTerm_edF0 [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T U : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ)
    (hU : U ⊆ ({a, b} : Finset ι)ᶜ) :
    (blockTerm a b (edF0 (σ := σ)) T)ᵀ * blockTerm a b edF0 U
      = if T = U then schemeProd T else 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_edF0_edF0]
  by_cases hTU : T = U
  · subst hTU
    rw [if_pos rfl]
    ext y z
    have haT : a ∉ T := fun h =>
      (Finset.mem_compl.mp (hT h)) (Finset.mem_insert_self a {b})
    have hbT : b ∉ T := fun h => (Finset.mem_compl.mp (hT h))
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    rw [Matrix.of_apply, schemeProd_apply_pair hab, if_neg haT, if_neg hbT,
      Matrix.of_apply]
    congr 1
    exact Finset.prod_congr rfl fun c hc => pattern_mul_self T _ _
  · rw [if_neg hTU]
    ext y z
    rw [Matrix.of_apply, prod_pattern_mul_eq_zero hT hU hTU y z, mul_zero,
      Matrix.zero_apply]

/-! ## The mixed Grams vanish -/

lemma pairGram_comm (φ ψ : σ → σ × σ → ℝ) :
    pairGram ψ φ = (pairGram φ ψ)ᵀ := by
  ext s t
  simp only [pairGram, Matrix.of_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

lemma gram_blockTerm_edF0_edF1 [Nonempty σ] {a b : ι} (hab : a ≠ b)
    (T U : Finset ι) :
    (blockTerm a b (edF0 (σ := σ)) T)ᵀ * blockTerm a b edF1 U = 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_edF0_edF1]
  ext y z
  rw [Matrix.of_apply, Matrix.zero_apply, Matrix.zero_apply, zero_mul]

lemma gram_blockTerm_edF1_edF0 [Nonempty σ] {a b : ι} (hab : a ≠ b)
    (T U : Finset ι) :
    (blockTerm a b (edF1 (σ := σ)) T)ᵀ * blockTerm a b edF0 U = 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_comm, pairGram_edF0_edF1]
  ext y z
  rw [Matrix.of_apply, Matrix.transpose_zero, Matrix.zero_apply,
    Matrix.zero_apply, zero_mul]

/-! ## The `F₁` Gram: two projectors and two swap couplings -/

lemma gram_blockTerm_edF1 [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T U : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ)
    (hU : U ⊆ ({a, b} : Finset ι)ᶜ) :
    (blockTerm a b (edF1 (σ := σ)) T)ᵀ * blockTerm a b edF1 U
      = if T = U then
          schemeProd (insert a T) + schemeProd (insert b T)
          + ((schemeProd (insert a T)).submatrix id ⇑(swapInput (σ := σ) a b)
            + (schemeProd (insert b T)).submatrix id ⇑(swapInput (σ := σ) a b))
        else 0 := by
  rw [blockTerm_transpose_mul hab, pairGram_edF1_edF1]
  by_cases hTU : T = U
  · subst hTU
    rw [if_pos rfl]
    ext y z
    have hca : ∀ c ∈ ({a, b} : Finset ι)ᶜ, c ≠ a := fun c hc h =>
      (Finset.mem_compl.mp hc) (by rw [h]; exact Finset.mem_insert_self a {b})
    have hcb : ∀ c ∈ ({a, b} : Finset ι)ᶜ, c ≠ b := fun c hc h =>
      (Finset.mem_compl.mp hc) (by
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    rw [Matrix.of_apply,
      Finset.prod_congr rfl fun c (hc : c ∈ ({a, b} : Finset ι)ᶜ) =>
        pattern_mul_self (c := c) T (y c) (z c),
      Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
      Matrix.submatrix_apply, Matrix.submatrix_apply, id_eq]
    set Pi0 := ∏ c ∈ ({a, b} : Finset ι)ᶜ,
      ((if c ∈ T then cellE1 else cellE0 : Matrix σ σ ℝ) (y c) (z c))
      with hPi0
    have hprodS : ∀ (S : Finset ι) (w : ι → σ),
        (∀ c ∈ ({a, b} : Finset ι)ᶜ, ((c ∈ S) ↔ c ∈ T)) →
        (∀ c ∈ ({a, b} : Finset ι)ᶜ, w c = z c) →
        (∏ c ∈ ({a, b} : Finset ι)ᶜ,
          ((if c ∈ S then cellE1 else cellE0 : Matrix σ σ ℝ) (y c) (w c)))
        = Pi0 := by
      intro S w hS hw
      rw [hPi0]
      refine Finset.prod_congr rfl fun c hc => ?_
      rw [hw c hc]
      by_cases hcT : c ∈ T
      · rw [if_pos ((hS c hc).mpr hcT), if_pos hcT]
      · rw [if_neg (fun h => hcT ((hS c hc).mp h)), if_neg hcT]
    have hmema : ∀ c ∈ ({a, b} : Finset ι)ᶜ, ((c ∈ insert a T) ↔ c ∈ T) :=
      fun c hc => mem_insert_iff_of_compl (hca c hc)
    have hmemb : ∀ c ∈ ({a, b} : Finset ι)ᶜ, ((c ∈ insert b T) ↔ c ∈ T) :=
      fun c hc => mem_insert_iff_of_compl (hcb c hc)
    have h1 : schemeProd (σ := σ) (insert a T) y z
        = cellE1 (y a) (z a) * cellE0 (y b) (z b) * Pi0 := by
      rw [schemeProd_apply_pair hab, if_pos (Finset.mem_insert_self a T),
        if_neg (right_notMem_insert_left hab hT),
        hprodS (insert a T) z hmema fun c _ => rfl]
    have h2 : schemeProd (σ := σ) (insert b T) y z
        = cellE0 (y a) (z a) * cellE1 (y b) (z b) * Pi0 := by
      rw [schemeProd_apply_pair hab,
        if_neg (left_notMem_insert_right hab hT),
        if_pos (Finset.mem_insert_self b T),
        hprodS (insert b T) z hmemb fun c _ => rfl]
    have h3 : schemeProd (σ := σ) (insert a T) y (swapInput (σ := σ) a b z)
        = cellE1 (y a) (z b) * cellE0 (y b) (z a) * Pi0 := by
      rw [schemeProd_apply_pair hab, if_pos (Finset.mem_insert_self a T),
        if_neg (right_notMem_insert_left hab hT),
        swapInput_apply_left, swapInput_apply_right,
        hprodS (insert a T) (swapInput (σ := σ) a b z) hmema
          fun c hc => swapInput_apply_of_ne (hca c hc) (hcb c hc) z]
    have h4 : schemeProd (σ := σ) (insert b T) y (swapInput (σ := σ) a b z)
        = cellE0 (y a) (z b) * cellE1 (y b) (z a) * Pi0 := by
      rw [schemeProd_apply_pair hab,
        if_neg (left_notMem_insert_right hab hT),
        if_pos (Finset.mem_insert_self b T),
        swapInput_apply_left, swapInput_apply_right,
        hprodS (insert b T) (swapInput (σ := σ) a b z) hmemb
          fun c hc => swapInput_apply_of_ne (hca c hc) (hcb c hc) z]
    rw [h1, h2, h3, h4]
    simp only [Matrix.of_apply]
    ring
  · rw [if_neg hTU]
    ext y z
    rw [Matrix.of_apply, prod_pattern_mul_eq_zero hT hU hTU y z, mul_zero,
      Matrix.zero_apply]

end QuantumQueryComplexity
