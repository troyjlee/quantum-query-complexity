import QuantumQueryComplexity.WeightedDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The first-difference dual: `ADV±(f) ≤ 2n` for every `f`

Order the coordinates arbitrarily.  For inputs `x ≠ y` there is exactly one
coordinate at which they *first* differ, so

  `∑_{i : x i ≠ y i} [x agrees with y before i] = 1`.

Tensoring that indicator with a cheap factorization of the "different output"
matrix, `⟨φ_a, ψ_b⟩ = [a ≠ b]`, turns it into a feasible dual solution: the
count `1` is switched on precisely when `f x ≠ f y`, and the LMRSS equality
constraints hold because the `φψ` factor already vanishes there.  Each input
puts mass `‖φ‖² = 2` on each of the `n` coordinates, so the cost is `2n`.

This is the dual attached to the trivial decision tree that reads every
coordinate in order.  Its point here is that **the bound carries no alphabet
dependence at all**, so it complements `QuantumQueryComplexity/Max/Dyadic.lean`, whose
`2⌈log₂ m⌉√n` degrades for very large alphabets.

The same construction applied to an arbitrary decision tree gives
`ADV±(f) ≤ 2 D(f)`, and averaging duals (which is legitimate, since the
constraint is linear in `⟨u, v⟩`) gives `ADV±(f) ≤ 2 R₀(f)`.  Neither helps for
maximum finding, where every coordinate must be read: `D(MAX) = R₀(MAX) = n`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]

/-! ## An arbitrary ordering of the coordinates -/

/-- An arbitrary injective ranking of the finite index type; it supplies the
"reading order" of the trivial decision tree. -/
noncomputable def idxRank (i : ι) : Fin (Fintype.card ι) := Fintype.equivFin ι i

lemma idxRank_inj : Function.Injective (idxRank : ι → Fin (Fintype.card ι)) :=
  (Fintype.equivFin ι).injective

/-- What has been read about `x` before coordinate `i` is queried. -/
noncomputable def prefixOf (x : ι → σ) (i : ι) : ι → Option σ :=
  fun j => if idxRank j < idxRank i then some (x j) else none

lemma prefixOf_eq_iff {x y : ι → σ} {i : ι} :
    prefixOf x i = prefixOf y i ↔ ∀ j, idxRank j < idxRank i → x j = y j := by
  constructor
  · intro h j hj
    have hj' := congrFun h j
    simp only [prefixOf, if_pos hj, Option.some.injEq] at hj'
    exact hj'
  · intro h
    funext j
    simp only [prefixOf]
    by_cases hj : idxRank j < idxRank i
    · rw [if_pos hj, if_pos hj, h j hj]
    · rw [if_neg hj, if_neg hj]

/-! ## Exactly one first difference -/

/-- The coordinates at which `x` and `y` differ for the first time. -/
noncomputable def firstDiffSet (x y : ι → σ) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i ∧ prefixOf x i = prefixOf y i

/-- **Distinct inputs have exactly one first difference.** -/
lemma card_firstDiffSet {x y : ι → σ} (h : x ≠ y) :
    (firstDiffSet x y).card = 1 := by
  classical
  have hD : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i₀, hmem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i => x i ≠ y i) idxRank hD
  rw [Finset.mem_filter] at hmem
  have hlow : ∀ j, idxRank j < idxRank i₀ → x j = y j := by
    intro j hj
    by_contra hne
    exact absurd (hmin j (by simpa using hne)) (by omega)
  rw [Finset.card_eq_one]
  refine ⟨i₀, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun i hi => ?_⟩⟩
  · simp only [firstDiffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmem.2, prefixOf_eq_iff.2 hlow⟩
  · simp only [firstDiffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : idxRank i₀ ≤ idxRank i := hmin i (by simpa using hi.1)
    have h2 : ¬ idxRank i₀ < idxRank i := fun hlt =>
      hmem.2 (prefixOf_eq_iff.1 hi.2 i₀ hlt)
    exact idxRank_inj (le_antisymm (by omega) h1)

/-! ## A cheap factorization of the "different output" matrix -/

/-- `φ a` and `ψ b` pair to `1` exactly when `a ≠ b`, with squared norms `2`. -/
def phiVec (a : O) : Option O → ℝ :=
  fun t => if t = none then 1 else if t = some a then -1 else 0

/-- The partner of `phiVec`. -/
def psiVec (b : O) : Option O → ℝ :=
  fun t => if t = none then 1 else if t = some b then 1 else 0

lemma sum_phiVec_mul_psiVec (a b : O) :
    (∑ t : Option O, phiVec a t * psiVec b t) = if a = b then 0 else 1 := by
  rw [Fintype.sum_option]
  have hnone : phiVec a none * psiVec b none = 1 := by simp [phiVec, psiVec]
  have hsome : ∀ c : O, phiVec a (some c) * psiVec b (some c)
      = if c = a then (if c = b then (-1 : ℝ) else 0) else 0 := by
    intro c
    simp only [phiVec, psiVec, reduceCtorEq, if_false, Option.some.injEq]
    by_cases h1 : c = a <;> by_cases h2 : c = b <;> simp [h1, h2]
  rw [hnone, Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ a fun c => if c = b then (-1 : ℝ) else 0,
    if_pos (Finset.mem_univ a)]
  by_cases hab : a = b <;> simp [hab]

lemma sum_phiVec_sq (a : O) : (∑ t : Option O, phiVec a t * phiVec a t) = 2 := by
  rw [Fintype.sum_option]
  have hsome : ∀ c : O, phiVec a (some c) * phiVec a (some c)
      = if c = a then (1 : ℝ) else 0 := by
    intro c
    simp only [phiVec, reduceCtorEq, if_false, Option.some.injEq]
    by_cases h1 : c = a <;> simp [h1]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ a fun _ => (1 : ℝ), if_pos (Finset.mem_univ a)]
  norm_num [phiVec]

lemma sum_psiVec_sq (b : O) : (∑ t : Option O, psiVec b t * psiVec b t) = 2 := by
  rw [Fintype.sum_option]
  have hsome : ∀ c : O, psiVec b (some c) * psiVec b (some c)
      = if c = b then (1 : ℝ) else 0 := by
    intro c
    simp only [psiVec, reduceCtorEq, if_false, Option.some.injEq]
    by_cases h1 : c = b <;> simp [h1]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ b fun _ => (1 : ℝ), if_pos (Finset.mem_univ b)]
  norm_num [psiVec]

/-! ## The dual solution -/

/-- The dual solution of the trivial decision tree that reads every coordinate
in the order given by `idxRank`. -/
noncomputable def firstDiffDual (f : (ι → σ) → O) :
    DualPair ((ι → Option σ) × Option O) f where
  u x i := fun c => (if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2
  v y i := fun c => (if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
            ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2))
        = (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1) := by
      intro i
      rw [Fintype.sum_prod_type, ← sum_phiVec_mul_psiVec (f x) (f y)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
              ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
          = ((if p = prefixOf x i then (1 : ℝ) else 0) *
              (if p = prefixOf y i then (1 : ℝ) else 0))
            * ∑ t : Option O, phiVec (f x) t * psiVec (f y) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show ((if p = prefixOf x i then (1 : ℝ) else 0) *
            (if p = prefixOf y i then (1 : ℝ) else 0))
          = (if p = prefixOf x i then
              (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0) else 0) from by
          by_cases h1 : p = prefixOf x i <;> by_cases h2 : p = prefixOf y i <;>
            simp [h1, h2] <;> grind]
      rw [Finset.sum_ite_eq' Finset.univ (prefixOf x i)
        fun _ => (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0),
        if_pos (Finset.mem_univ _)]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1))
        = (if i ∈ firstDiffSet x y then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1) := by
      intro i
      have hmem : i ∈ firstDiffSet x y
          ↔ (x i ≠ y i ∧ prefixOf x i = prefixOf y i) := by
        simp [firstDiffSet]
      by_cases h : x i = y i
      · have hnot : i ∉ firstDiffSet x y := fun hc => (hmem.mp hc).1 h
        rw [if_pos h, if_neg hnot, zero_mul]
      · by_cases h2 : prefixOf x i = prefixOf y i
        · rw [if_neg h, if_pos h2, if_pos (hmem.mpr ⟨h, h2⟩)]
        · have hnot : i ∉ firstDiffSet x y := fun hc => h2 (hmem.mp hc).2
          rw [if_neg h, if_neg h2, if_neg hnot]
    simp only [hmask]
    rw [← Finset.sum_mul]
    by_cases hf : f x = f y
    · rw [if_pos hf, mul_zero]
    · rw [if_neg hf, mul_one]
      have hxy : x ≠ y := fun h => hf (by rw [h])
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        card_firstDiffSet hxy, Nat.cast_one, mul_one]

/-- **`ADV±(f) ≤ 2n` for every function on `n` variables**, with no dependence
on the input alphabet or the output type. -/
theorem advPM_le_two_mul_card (f : (ι → σ) → O) :
    advPM f ≤ 2 * (Fintype.card ι : ℝ) := by
  refine advPM_le_of_dualPair (firstDiffDual f) (by positivity) ⟨fun x => ?_, fun y => ?_⟩
  · have hstep : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          (firstDiffDual f).u x i c * (firstDiffDual f).u x i c) = 2 := by
      intro i
      show (∑ c : (ι → Option σ) × Option O,
        ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
          ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2)) = 2
      rw [Fintype.sum_prod_type, ← sum_phiVec_sq (f x)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
              ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t))
          = (if p = prefixOf x i then (1 : ℝ) else 0)
            * ∑ t : Option O, phiVec (f x) t * phiVec (f x) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by
            by_cases h : p = prefixOf x i <;> simp [h] <;> ring]
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf x i)
        fun _ => (1 : ℝ), if_pos (Finset.mem_univ _), one_mul]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)
  · have hstep : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          (firstDiffDual f).v y i c * (firstDiffDual f).v y i c) = 2 := by
      intro i
      show (∑ c : (ι → Option σ) × Option O,
        ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2) *
          ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2)) = 2
      rw [Fintype.sum_prod_type, ← sum_psiVec_sq (f y)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t) *
              ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
          = (if p = prefixOf y i then (1 : ℝ) else 0)
            * ∑ t : Option O, psiVec (f y) t * psiVec (f y) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by
            by_cases h : p = prefixOf y i <;> simp [h] <;> ring]
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf y i)
        fun _ => (1 : ℝ), if_pos (Finset.mem_univ _), one_mul]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)

/-- Each input puts mass exactly `‖φ‖² = 2` on each coordinate. -/
lemma sum_firstDiffDual_u_sq (f : (ι → σ) → O) (x : ι → σ) (i : ι) :
    (∑ c : (ι → Option σ) × Option O,
      (firstDiffDual f).u x i c * (firstDiffDual f).u x i c) = 2 := by
  show (∑ c : (ι → Option σ) × Option O,
    ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
      ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2)) = 2
  rw [Fintype.sum_prod_type, ← sum_phiVec_sq (f x)]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show (∑ t : Option O,
        ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
          ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t))
      = (if p = prefixOf x i then (1 : ℝ) else 0)
        * ∑ t : Option O, phiVec (f x) t * phiVec (f x) t from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by
        by_cases h : p = prefixOf x i <;> simp [h] <;> ring]
  rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf x i)
    fun _ => (1 : ℝ), if_pos (Finset.mem_univ _), one_mul]

lemma sum_firstDiffDual_v_sq (f : (ι → σ) → O) (y : ι → σ) (i : ι) :
    (∑ c : (ι → Option σ) × Option O,
      (firstDiffDual f).v y i c * (firstDiffDual f).v y i c) = 2 := by
  show (∑ c : (ι → Option σ) × Option O,
    ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2) *
      ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2)) = 2
  rw [Fintype.sum_prod_type, ← sum_psiVec_sq (f y)]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show (∑ t : Option O,
        ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t) *
          ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
      = (if p = prefixOf y i then (1 : ℝ) else 0)
        * ∑ t : Option O, psiVec (f y) t * psiVec (f y) t from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by
        by_cases h : p = prefixOf y i <;> simp [h] <;> ring]
  rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf y i)
    fun _ => (1 : ℝ), if_pos (Finset.mem_univ _), one_mul]

/-- The weighted cost of the first-difference dual: mass `2` on every
coordinate, so the `c`-weighted cost is `2 ∑ c`. -/
theorem firstDiffDual_isWeightedCostLe (f : (ι → σ) → O) (c : ι → ℝ) :
    (firstDiffDual f).IsWeightedCostLe c (2 * ∑ i, c i) := by
  constructor
  · intro x
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_firstDiffDual_u_sq f x i], Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · intro y
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_firstDiffDual_v_sq f y i], Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end QuantumQueryComplexity
