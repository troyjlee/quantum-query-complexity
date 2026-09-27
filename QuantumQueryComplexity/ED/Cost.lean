import QuantumQueryComplexity.ED.Count
import QuantumQueryComplexity.LearningGraph.Dual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The half-weights and the two complexities

The half-weight profile, by level `t = |S|` (with `n` coordinates,
`m = n - 2`):

* `t < r`:   `ω² = 1/(C(m,t)·(m-t))` — equal to the stage-I flow value, so
  stage I contributes exactly `1` to `𝒞₁` per level;
* `t = r`:   `ω² = β = 1/√(C(n,r)·(n-r)·C(m,r))`;
* `t = r+1`: `ω² = γ = 1/√(C(n,r+1)·(n-r-1)·C(m,r))`;
* `ω = 0` above level `r+1` and on non-loading edges.

`β` and `γ` are balanced so that the stage-II and stage-III contributions to
`𝒞₀` and `𝒞₁` agree: both equal `√(C(n,r)(n-r)/C(m,r)) ≤ √(2n)` at level
`r`, and `√(C(n,r+1)(n-r-1)/C(m,r)) ≤ n/√(r+1)` at level `r+1`.  Under
`2r + 2 ≤ n`,

  `𝒞₀ ≤ 4r + √(2n) + n/√(r+1)`,   `𝒞₁ ≤ r + √(2n) + n/√(r+1)`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The half-weight -/

/-- The squared half-weight at level `r`. -/
noncomputable def edBeta (n r : ℕ) : ℝ :=
  (Real.sqrt ((n.choose r * (n - r) * ((n - 2).choose r) : ℕ) : ℝ))⁻¹

/-- The squared half-weight at level `r + 1`. -/
noncomputable def edGamma (n r : ℕ) : ℝ :=
  (Real.sqrt ((n.choose (r + 1) * (n - (r + 1)) * ((n - 2).choose r) : ℕ) : ℝ))⁻¹

/-- The squared half-weight profile by level. -/
noncomputable def edLevel (n r t : ℕ) : ℝ :=
  if t < r then edW (n - 2) t
  else if t = r then edBeta n r
  else if t = r + 1 then edGamma n r
  else 0

/-- The half-weight itself. -/
noncomputable def edOmega (n r : ℕ) (e : Finset ι × ι) : ℝ :=
  if e.2 ∈ e.1 then 0 else Real.sqrt (edLevel n r e.1.card)

lemma edW_nonneg (m t : ℕ) : 0 ≤ edW m t := by
  rw [edW]
  positivity

lemma edLevel_nonneg (n r t : ℕ) : 0 ≤ edLevel n r t := by
  rw [edLevel, edBeta, edGamma]
  split_ifs
  · exact edW_nonneg _ _
  · positivity
  · positivity
  · exact le_refl 0

lemma edLevel_pos {n r t : ℕ} (hrn : 2 * r + 2 ≤ n) (ht : t ≤ r + 1) :
    0 < edLevel n r t := by
  rw [edLevel]
  by_cases h1 : t < r
  · rw [if_pos h1, edW]
    refine inv_pos.mpr (mul_pos ?_ ?_)
    · exact_mod_cast Nat.choose_pos (show t ≤ n - 2 by omega)
    · exact_mod_cast show 0 < n - 2 - t by omega
  · rw [if_neg h1]
    by_cases h2 : t = r
    · rw [if_pos h2, edBeta]
      refine inv_pos.mpr (Real.sqrt_pos.mpr ?_)
      exact_mod_cast Nat.mul_pos
        (Nat.mul_pos (Nat.choose_pos (by omega)) (show 0 < n - r by omega))
        (Nat.choose_pos (show r ≤ n - 2 by omega))
    · rw [if_neg h2, if_pos (by omega), edGamma]
      refine inv_pos.mpr (Real.sqrt_pos.mpr ?_)
      exact_mod_cast Nat.mul_pos
        (Nat.mul_pos (Nat.choose_pos (by omega))
          (show 0 < n - (r + 1) by omega))
        (Nat.choose_pos (show r ≤ n - 2 by omega))

/-- The half-weight is nonzero on every loading edge of the first `r + 2`
levels — the hypothesis `edLGFlow` asks for. -/
lemma edOmega_ne_zero {n r : ℕ} (hrn : 2 * r + 2 ≤ n)
    {e : Finset ι × ι} (hj : e.2 ∉ e.1) (hc : e.1.card ≤ r + 1) :
    edOmega n r e ≠ 0 := by
  rw [edOmega, if_neg hj]
  exact (Real.sqrt_pos.mpr (edLevel_pos hrn hc)).ne'

/-! ## Square-root bookkeeping -/

private lemma mul_inv_sqrt_mul {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * (Real.sqrt (A * B))⁻¹ = Real.sqrt (A / B) := by
  rw [Real.sqrt_mul hA.le, mul_inv, ← mul_assoc, ← div_eq_mul_inv A,
    Real.div_sqrt, ← div_eq_mul_inv, ← Real.sqrt_div hA.le]

private lemma sqrt_mul_div {A B : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (A * B) / B = Real.sqrt (A / B) := by
  rw [Real.sqrt_mul hA, mul_div_assoc, Real.sqrt_div_self', mul_one_div,
    ← Real.sqrt_div hA]

/-- The shared level-`r` ratio bound. -/
private lemma sqrt_ratio_II_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    Real.sqrt (((n.choose r * (n - r) : ℕ) : ℝ)
        / (((n - 2).choose r : ℕ) : ℝ))
      ≤ Real.sqrt (2 * n) := by
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hB]
  exact_mod_cast stageII_count_bound hrn

/-- The shared level-`r+1` ratio bound. -/
private lemma sqrt_ratio_III_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    Real.sqrt (((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ)
        / (((n - 2).choose r : ℕ) : ℝ))
      ≤ (n : ℝ) / Real.sqrt (r + 1) := by
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hrhs : (n : ℝ) / Real.sqrt (r + 1)
      = Real.sqrt ((n : ℝ) * n / ((r : ℝ) + 1)) := by
    rw [Real.sqrt_div (by positivity) ((r : ℝ) + 1),
      Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  rw [hrhs]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ hB hrp]
  have h := stageIII_count_bound n r
  calc ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ) * ((r : ℝ) + 1)
      = ((n.choose (r + 1) * (n - (r + 1)) * (r + 1) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((n * n * ((n - 2).choose r) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (n : ℝ) * n * (((n - 2).choose r : ℕ) : ℝ) := by push_cast; ring

/-! ## The negative complexity -/

/-- The stage-II contribution to `𝒞₀`. -/
lemma stageII_weight_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    (n.choose r : ℝ) * (((n - r : ℕ)) : ℝ) * edBeta n r
      ≤ Real.sqrt (2 * n) := by
  have hA : (0 : ℝ) < ((n.choose r * (n - r) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - r by omega)
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  have hcast : (n.choose r : ℝ) * (((n - r : ℕ)) : ℝ)
      = ((n.choose r * (n - r) : ℕ) : ℝ) := by push_cast; ring
  rw [edBeta, show ((n.choose r * (n - r) * ((n - 2).choose r) : ℕ) : ℝ)
      = ((n.choose r * (n - r) : ℕ) : ℝ) * (((n - 2).choose r : ℕ) : ℝ) from by
      push_cast; ring,
    hcast, mul_inv_sqrt_mul hA hB]
  exact sqrt_ratio_II_le hrn

/-- The stage-III contribution to `𝒞₀`. -/
lemma stageIII_weight_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    (n.choose (r + 1) : ℝ) * (((n - (r + 1) : ℕ)) : ℝ) * edGamma n r
      ≤ (n : ℝ) / Real.sqrt (r + 1) := by
  have hA : (0 : ℝ) < ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - (r + 1) by omega)
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  have hcast : (n.choose (r + 1) : ℝ) * (((n - (r + 1) : ℕ)) : ℝ)
      = ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ) := by push_cast; ring
  rw [edGamma,
    show ((n.choose (r + 1) * (n - (r + 1)) * ((n - 2).choose r) : ℕ) : ℝ)
      = ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ)
        * (((n - 2).choose r : ℕ) : ℝ) from by push_cast; ring,
    hcast, mul_inv_sqrt_mul hA hB]
  exact sqrt_ratio_III_le hrn

/-- **The negative complexity**: `𝒞₀ ≤ 4r + √(2n) + n/√(r+1)`. -/
theorem sum_edOmega_sq_le {r : ℕ} (hrn : 2 * r + 2 ≤ Fintype.card ι) :
    (∑ e : Finset ι × ι, edOmega (Fintype.card ι) r e ^ 2)
      ≤ 4 * r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)) := by
  have hsq : ∀ e : Finset ι × ι, edOmega (Fintype.card ι) r e ^ 2
      = if e.2 ∈ e.1 then (0 : ℝ)
        else edLevel (Fintype.card ι) r e.1.card := by
    intro e
    rw [edOmega]
    by_cases hj : e.2 ∈ e.1
    · rw [if_pos hj, if_pos hj]
      norm_num
    · rw [if_neg hj, if_neg hj, Real.sq_sqrt (edLevel_nonneg _ _ _)]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hsq e,
    sum_edge_levelWeight (edLevel (Fintype.card ι) r)]
  have htrunc : (∑ t ∈ Finset.range (Fintype.card ι + 1),
      ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
        * edLevel (Fintype.card ι) r t)
      = ∑ t ∈ Finset.range (r + 2),
        ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
          * edLevel (Fintype.card ι) r t := by
    refine (Finset.sum_subset
      (Finset.range_subset_range.mpr (show r + 2 ≤ Fintype.card ι + 1 by omega))
      fun t ht hnt => ?_).symm
    have h1 : r + 2 ≤ t := by
      rcases Nat.lt_or_ge t (r + 2) with h | h
      · exact absurd (Finset.mem_range.mpr h) hnt
      · exact h
    rw [edLevel, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      mul_zero]
  rw [htrunc, Finset.sum_range_succ, Finset.sum_range_succ]
  have hstageI : (∑ t ∈ Finset.range r,
      ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
        * edLevel (Fintype.card ι) r t) ≤ 4 * r := by
    have hbound : ∀ t ∈ Finset.range r,
        ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
          * edLevel (Fintype.card ι) r t ≤ 4 := by
      intro t ht
      have htr : t < r := Finset.mem_range.mp ht
      rw [edLevel, if_pos htr, edW]
      have hY : (0 : ℝ) < (((Fintype.card ι - 2).choose t : ℕ) : ℝ)
          * (((Fintype.card ι - 2 - t : ℕ)) : ℝ) := by
        refine mul_pos ?_ ?_
        · exact_mod_cast Nat.choose_pos (show t ≤ Fintype.card ι - 2 by omega)
        · exact_mod_cast show 0 < Fintype.card ι - 2 - t by omega
      rw [mul_inv_le_iff₀ hY]
      calc ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
          = (((Fintype.card ι).choose t * (Fintype.card ι - t) : ℕ) : ℝ) := by
            push_cast; ring
        _ ≤ ((4 * ((Fintype.card ι - 2).choose t
              * (Fintype.card ι - 2 - t)) : ℕ) : ℝ) := by
            exact_mod_cast stageI_count_bound htr hrn
        _ = 4 * ((((Fintype.card ι - 2).choose t : ℕ) : ℝ)
              * (((Fintype.card ι - 2 - t : ℕ)) : ℝ)) := by push_cast; ring
    calc (∑ t ∈ Finset.range r,
        ((Fintype.card ι).choose t : ℝ) * (((Fintype.card ι - t : ℕ)) : ℝ)
          * edLevel (Fintype.card ι) r t)
        ≤ ∑ _t ∈ Finset.range r, (4 : ℝ) := Finset.sum_le_sum hbound
      _ = 4 * r := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hII : ((Fintype.card ι).choose r : ℝ)
      * (((Fintype.card ι - r : ℕ)) : ℝ) * edLevel (Fintype.card ι) r r
      ≤ Real.sqrt (2 * Fintype.card ι) := by
    rw [edLevel, if_neg (lt_irrefl r), if_pos rfl]
    exact stageII_weight_le hrn
  have hIII : ((Fintype.card ι).choose (r + 1) : ℝ)
      * (((Fintype.card ι - (r + 1) : ℕ)) : ℝ)
      * edLevel (Fintype.card ι) r (r + 1)
      ≤ (Fintype.card ι : ℝ) / Real.sqrt (r + 1) := by
    rw [edLevel, if_neg (by omega), if_neg (by omega), if_pos rfl]
    exact stageIII_weight_le hrn
  linarith

/-! ## The positive complexity -/

/-- The stage-II contribution to `𝒞₁`. -/
lemma stageII_term_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    (((n - 2).choose r : ℕ) : ℝ)
      * (edV (n - 2) r ^ 2 * (edBeta n r)⁻¹) ≤ Real.sqrt (2 * n) := by
  have hA : (0 : ℝ) < ((n.choose r * (n - r) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - r by omega)
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  rw [edV, edBeta, inv_inv]
  have hstep : (((n - 2).choose r : ℕ) : ℝ)
      * (((((n - 2).choose r : ℕ) : ℝ))⁻¹ ^ 2
        * Real.sqrt ((n.choose r * (n - r) * ((n - 2).choose r) : ℕ) : ℝ))
      = Real.sqrt ((n.choose r * (n - r) * ((n - 2).choose r) : ℕ) : ℝ)
        / (((n - 2).choose r : ℕ) : ℝ) := by
    field_simp
  rw [hstep, show ((n.choose r * (n - r) * ((n - 2).choose r) : ℕ) : ℝ)
      = ((n.choose r * (n - r) : ℕ) : ℝ) * (((n - 2).choose r : ℕ) : ℝ) from by
      push_cast; ring,
    sqrt_mul_div hA.le]
  exact sqrt_ratio_II_le hrn

/-- The stage-III contribution to `𝒞₁`. -/
lemma stageIII_term_le {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    (((n - 2).choose r : ℕ) : ℝ)
      * (edV (n - 2) r ^ 2 * (edGamma n r)⁻¹)
      ≤ (n : ℝ) / Real.sqrt (r + 1) := by
  have hA : (0 : ℝ) < ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - (r + 1) by omega)
  have hB : (0 : ℝ) < (((n - 2).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - 2 by omega)
  rw [edV, edGamma, inv_inv]
  have hstep : (((n - 2).choose r : ℕ) : ℝ)
      * (((((n - 2).choose r : ℕ) : ℝ))⁻¹ ^ 2
        * Real.sqrt ((n.choose (r + 1) * (n - (r + 1))
            * ((n - 2).choose r) : ℕ) : ℝ))
      = Real.sqrt ((n.choose (r + 1) * (n - (r + 1))
            * ((n - 2).choose r) : ℕ) : ℝ)
        / (((n - 2).choose r : ℕ) : ℝ) := by
    field_simp
  rw [hstep,
    show ((n.choose (r + 1) * (n - (r + 1)) * ((n - 2).choose r) : ℕ) : ℝ)
      = ((n.choose (r + 1) * (n - (r + 1)) : ℕ) : ℝ)
        * (((n - 2).choose r : ℕ) : ℝ) from by push_cast; ring,
    sqrt_mul_div hA.le]
  exact sqrt_ratio_III_le hrn

/-! ## The pair complement -/

lemma edBeta_nonneg (n r : ℕ) : 0 ≤ edBeta n r := by
  rw [edBeta]; positivity

lemma edGamma_nonneg (n r : ℕ) : 0 ≤ edGamma n r := by
  rw [edGamma]; positivity

private lemma subset_sdiff_pair {S : Finset ι} {a b : ι} (ha : a ∉ S)
    (hb : b ∉ S) : S ⊆ Finset.univ \ ({a, b} : Finset ι) := by
  intro z hz
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hzab => ?_⟩
  rcases Finset.mem_insert.mp hzab with h | h
  · rw [h] at hz; exact ha hz
  · rw [Finset.mem_singleton.mp h] at hz; exact hb hz

private lemma left_notMem_of_subset_sdiff_pair {S : Finset ι} {a b : ι}
    (hS : S ⊆ Finset.univ \ ({a, b} : Finset ι)) : a ∉ S := fun h =>
  (Finset.mem_sdiff.mp (hS h)).2 (Finset.mem_insert_self a {b})

private lemma right_notMem_of_subset_sdiff_pair {S : Finset ι} {a b : ι}
    (hS : S ⊆ Finset.univ \ ({a, b} : Finset ι)) : b ∉ S := fun h =>
  (Finset.mem_sdiff.mp (hS h)).2
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))

private lemma mem_sdiff_pair {j a b : ι} (hja : j ≠ a) (hjb : j ≠ b) :
    j ∈ Finset.univ \ ({a, b} : Finset ι) := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hj => ?_⟩
  rcases Finset.mem_insert.mp hj with h | h
  · exact hja h
  · exact hjb (Finset.mem_singleton.mp h)

private lemma ne_left_of_mem_sdiff_pair {j a b : ι}
    (hj : j ∈ Finset.univ \ ({a, b} : Finset ι)) : j ≠ a := fun h =>
  (Finset.mem_sdiff.mp hj).2 (by rw [h]; exact Finset.mem_insert_self a {b})

private lemma ne_right_of_mem_sdiff_pair {j a b : ι}
    (hj : j ∈ Finset.univ \ ({a, b} : Finset ι)) : j ≠ b := fun h =>
  (Finset.mem_sdiff.mp hj).2
    (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))

lemma card_sdiff_pair {a b : ι} (hab : a ≠ b) :
    (Finset.univ \ ({a, b} : Finset ι)).card = Fintype.card ι - 2 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
    Finset.card_univ, Finset.card_pair hab]

/-- **The positive complexity**: for every collision pair,
`𝒞₁ ≤ r + √(2n) + n/√(r+1)`. -/
theorem sum_edFlow_div_sq_le {r : ℕ} {a b : ι} (hab : a ≠ b)
    (hrn : 2 * r + 2 ≤ Fintype.card ι) :
    (∑ e : Finset ι × ι,
      (edFlow r a b e.1 e.2 / edOmega (Fintype.card ι) r e) ^ 2)
      ≤ r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)) := by
  classical
  have hD := card_sdiff_pair (ι := ι) hab
  have hsplit : ∀ e : Finset ι × ι,
      (edFlow r a b e.1 e.2 / edOmega (Fintype.card ι) r e) ^ 2
      = (if e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
            ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1
          then (if e.1.card < r then edW (Fintype.card ι - 2) e.1.card else 0)
          else 0)
        + ((if e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
              ∧ e.1.card = r ∧ e.2 = a
            then edV (Fintype.card ι - 2) r ^ 2
              * (edBeta (Fintype.card ι) r)⁻¹ else 0)
          + (if a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b
              then edV (Fintype.card ι - 2) r ^ 2
                * (edGamma (Fintype.card ι) r)⁻¹ else 0)) := by
    intro e
    rw [edFlow]
    by_cases h1 : a ∉ e.1 ∧ b ∉ e.1 ∧ e.2 ∉ e.1 ∧ e.2 ≠ a ∧ e.2 ≠ b
        ∧ e.1.card < r
    · have hI : e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
          ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1 :=
        ⟨subset_sdiff_pair h1.1 h1.2.1,
          mem_sdiff_pair h1.2.2.2.1 h1.2.2.2.2.1, h1.2.2.1⟩
      have hnotII : ¬ (e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
          ∧ e.1.card = r ∧ e.2 = a) := fun hc => h1.2.2.2.1 hc.2.2
      have hnotIII : ¬ (a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b) :=
        fun hc => h1.1 hc.1
      rw [if_pos h1, if_pos hI, if_neg hnotII, if_neg hnotIII, add_zero,
        add_zero, if_pos h1.2.2.2.2.2, edOmega, if_neg h1.2.2.1, edLevel,
        if_pos h1.2.2.2.2.2, Real.div_sqrt, Real.sq_sqrt (edW_nonneg _ _)]
    · rw [if_neg h1]
      by_cases h2 : a ∉ e.1 ∧ b ∉ e.1 ∧ e.1.card = r ∧ e.2 = a
      · have hII : e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
            ∧ e.1.card = r ∧ e.2 = a :=
          ⟨subset_sdiff_pair h2.1 h2.2.1, h2.2.2.1, h2.2.2.2⟩
        have hnotI : ¬ (e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
            ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1) :=
          fun hc => ne_left_of_mem_sdiff_pair hc.2.1 h2.2.2.2
        have hnotIII : ¬ (a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b) :=
          fun hc => h2.1 hc.1
        have hjS : e.2 ∉ e.1 := by rw [h2.2.2.2]; exact h2.1
        have hcr : e.1.card = r := h2.2.2.1
        rw [if_pos h2, if_neg hnotI, if_pos hII, if_neg hnotIII, zero_add,
          add_zero, edOmega, if_neg hjS, edLevel,
          if_neg (show ¬ e.1.card < r by omega), if_pos hcr, div_pow,
          Real.sq_sqrt (edBeta_nonneg _ _), div_eq_mul_inv]
      · rw [if_neg h2]
        by_cases h3 : a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b
        · have hnotI : ¬ (e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
              ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1) :=
            fun hc => left_notMem_of_subset_sdiff_pair hc.1 h3.1
          have hnotII : ¬ (e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
              ∧ e.1.card = r ∧ e.2 = a) :=
            fun hc => left_notMem_of_subset_sdiff_pair hc.1 h3.1
          have hjS : e.2 ∉ e.1 := by rw [h3.2.2.2]; exact h3.2.1
          have hcr : e.1.card = r + 1 := h3.2.2.1
          rw [if_pos h3, if_neg hnotI, if_neg hnotII, if_pos h3, zero_add,
            zero_add, edOmega, if_neg hjS, edLevel,
            if_neg (show ¬ e.1.card < r by omega),
            if_neg (show ¬ e.1.card = r by omega), if_pos hcr, div_pow,
            Real.sq_sqrt (edGamma_nonneg _ _), div_eq_mul_inv]
        · have hnotII : ¬ (e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
              ∧ e.1.card = r ∧ e.2 = a) := fun hc =>
            h2 ⟨left_notMem_of_subset_sdiff_pair hc.1,
              right_notMem_of_subset_sdiff_pair hc.1, hc.2.1, hc.2.2⟩
          rw [if_neg h3, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
            if_neg hnotII, if_neg h3, zero_add, add_zero]
          by_cases hI : e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
              ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1
          · rw [if_pos hI, if_neg (show ¬ e.1.card < r from fun hlt =>
              h1 ⟨left_notMem_of_subset_sdiff_pair hI.1,
                right_notMem_of_subset_sdiff_pair hI.1, hI.2.2,
                ne_left_of_mem_sdiff_pair hI.2.1,
                ne_right_of_mem_sdiff_pair hI.2.1, hlt⟩)]
          · rw [if_neg hI]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hsplit e,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hI : (∑ e : Finset ι × ι,
      if e.1 ⊆ Finset.univ \ ({a, b} : Finset ι)
          ∧ e.2 ∈ Finset.univ \ ({a, b} : Finset ι) ∧ e.2 ∉ e.1
        then (if e.1.card < r then edW (Fintype.card ι - 2) e.1.card else 0)
        else 0) = r := by
    rw [sum_edge_levelWeight_sub (Finset.univ \ ({a, b} : Finset ι))
        (fun t => if t < r then edW (Fintype.card ι - 2) t else 0), hD]
    have hsub : Finset.range r ⊆ Finset.range (Fintype.card ι - 2 + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hvan : ∀ t ∈ Finset.range (Fintype.card ι - 2 + 1),
        t ∉ Finset.range r →
        ((Fintype.card ι - 2).choose t : ℝ)
          * (((Fintype.card ι - 2 - t : ℕ)) : ℝ)
          * (if t < r then edW (Fintype.card ι - 2) t else 0) = 0 := by
      intro t _ hnt
      have hrt : r ≤ t := by
        rcases Nat.lt_or_ge t r with h | h
        · exact absurd (Finset.mem_range.mpr h) hnt
        · exact h
      rw [if_neg (by omega), mul_zero]
    rw [(Finset.sum_subset hsub hvan).symm,
      Finset.sum_congr rfl fun t ht => show
        ((Fintype.card ι - 2).choose t : ℝ)
          * (((Fintype.card ι - 2 - t : ℕ)) : ℝ)
          * (if t < r then edW (Fintype.card ι - 2) t else 0) = 1 from by
        have htr : t < r := Finset.mem_range.mp ht
        rw [if_pos htr, edW]
        refine mul_inv_cancel₀ (mul_pos ?_ ?_).ne'
        · exact_mod_cast Nat.choose_pos (show t ≤ Fintype.card ι - 2 by omega)
        · exact_mod_cast show 0 < Fintype.card ι - 2 - t by omega,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hII : (∑ e : Finset ι × ι,
      if e.1 ⊆ Finset.univ \ ({a, b} : Finset ι) ∧ e.1.card = r ∧ e.2 = a
        then edV (Fintype.card ι - 2) r ^ 2 * (edBeta (Fintype.card ι) r)⁻¹
        else 0)
      ≤ Real.sqrt (2 * Fintype.card ι) := by
    rw [sum_edge_stageII (Finset.univ \ ({a, b} : Finset ι)) a r
        (edV (Fintype.card ι - 2) r ^ 2 * (edBeta (Fintype.card ι) r)⁻¹), hD]
    exact stageII_term_le hrn
  have hIII : (∑ e : Finset ι × ι,
      if a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b
        then edV (Fintype.card ι - 2) r ^ 2 * (edGamma (Fintype.card ι) r)⁻¹
        else 0)
      ≤ (Fintype.card ι : ℝ) / Real.sqrt (r + 1) := by
    rw [sum_edge_stageIII hab r
        (edV (Fintype.card ι - 2) r ^ 2 * (edGamma (Fintype.card ι) r)⁻¹), hD]
    exact stageIII_term_le hrn
  linarith

end QuantumQueryComplexity
