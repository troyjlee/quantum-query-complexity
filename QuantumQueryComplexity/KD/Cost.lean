import QuantumQueryComplexity.KD.Count
import QuantumQueryComplexity.ED.Cost
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Costs of the k-distinctness learning graph

Half-weights by level: the stage-I flow value below level `r`, and the
balancing value `kdBeta n k r ℓ = 1/√(C(n,r+ℓ)·(n-r-ℓ)·C(n-k,r))` at level
`r + ℓ` for `ℓ < k`.  Both complexities are bounded by

    B(k,r) = 2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ)

under `2(r+k) ≤ n`: stage I of `𝒞₀` pays at most `2^{k+1}` per level
(`kd_stageI_count_bound`) while stage I of `𝒞₁` pays exactly `1`; each
stage-`ℓ` transition pays `E_ℓ = √(C(n,r+ℓ)(n-r-ℓ)/C(n-k,r))` on both
sides — that is the point of `kdBeta` — and `E_ℓ` is bounded by
`kd_stageL_count_bound`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The half-weight profile -/

/-- The squared half-weight at level `r + ℓ`. -/
noncomputable def kdBeta (n k r ℓ : ℕ) : ℝ :=
  (Real.sqrt ((n.choose (r + ℓ) * (n - (r + ℓ))
    * ((n - k).choose r) : ℕ) : ℝ))⁻¹

/-- The squared half-weight profile by level. -/
noncomputable def kdLevel (n k r t : ℕ) : ℝ :=
  if t < r then edW (n - k) t
  else if t < r + k then kdBeta n k r (t - r)
  else 0

/-- The half-weight itself. -/
noncomputable def kdOmega (n k r : ℕ) (e : Finset ι × ι) : ℝ :=
  if e.2 ∈ e.1 then 0 else Real.sqrt (kdLevel n k r e.1.card)

lemma kdBeta_nonneg (n k r ℓ : ℕ) : 0 ≤ kdBeta n k r ℓ := by
  rw [kdBeta]
  positivity

lemma kdLevel_nonneg (n k r t : ℕ) : 0 ≤ kdLevel n k r t := by
  rw [kdLevel]
  split_ifs
  · exact edW_nonneg _ _
  · exact kdBeta_nonneg _ _ _ _
  · exact le_refl 0

lemma kdLevel_pos {n k r t : ℕ} (hk : 1 ≤ k) (hrn : 2 * (r + k) ≤ n)
    (ht : t ≤ r + k - 1) : 0 < kdLevel n k r t := by
  rw [kdLevel]
  by_cases h1 : t < r
  · rw [if_pos h1, edW]
    refine inv_pos.mpr (mul_pos ?_ ?_)
    · exact_mod_cast Nat.choose_pos (show t ≤ n - k by omega)
    · exact_mod_cast show 0 < n - k - t by omega
  · rw [if_neg h1, if_pos (by omega), kdBeta]
    refine inv_pos.mpr (Real.sqrt_pos.mpr ?_)
    exact_mod_cast Nat.mul_pos (Nat.mul_pos
      (Nat.choose_pos (show r + (t - r) ≤ n by omega))
      (show 0 < n - (r + (t - r)) by omega))
      (Nat.choose_pos (show r ≤ n - k by omega))

/-- The half-weight is nonzero on every loading edge of the first `r + k`
levels — the hypothesis `kdLGFlow` asks for. -/
lemma kdOmega_ne_zero {n k r : ℕ} (hk : 1 ≤ k) (hrn : 2 * (r + k) ≤ n)
    {e : Finset ι × ι} (hj : e.2 ∉ e.1) (hc : e.1.card ≤ r + k - 1) :
    kdOmega n k r e ≠ 0 := by
  rw [kdOmega, if_neg hj]
  exact (Real.sqrt_pos.mpr (kdLevel_pos hk hrn hc)).ne'

/-! ## Square-root bookkeeping -/

private lemma mul_inv_sqrt_mul {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * (Real.sqrt (A * B))⁻¹ = Real.sqrt (A / B) := by
  rw [Real.sqrt_mul hA.le, mul_inv, ← mul_assoc, ← div_eq_mul_inv A,
    Real.div_sqrt, ← div_eq_mul_inv, ← Real.sqrt_div hA.le]

private lemma sqrt_mul_div {A B : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (A * B) / B = Real.sqrt (A / B) := by
  rw [Real.sqrt_mul hA, mul_div_assoc, Real.sqrt_div_self', mul_one_div,
    ← Real.sqrt_div hA]

/-- The shared level-`r+ℓ` ratio bound. -/
private lemma kd_sqrt_ratio_le {n k r ℓ : ℕ} (hrn : 2 * (r + k) ≤ n)
    (hℓ : ℓ < k) :
    Real.sqrt (((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ)
        / (((n - k).choose r : ℕ) : ℝ))
      ≤ Real.sqrt (((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
        / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
  have hB : (0 : ℝ) < (((n - k).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - k by omega)
  have hrp : (0 : ℝ) < (((r + 1) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (show 0 < r + 1 by omega) ℓ
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ hB hrp]
  calc ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ)
        * (((r + 1) ^ ℓ : ℕ) : ℝ)
      = ((n.choose (r + ℓ) * (n - r - ℓ) * (r + 1) ^ ℓ : ℕ) : ℝ) := by
        rw [show n - (r + ℓ) = n - r - ℓ from by omega]
        push_cast
        ring
    _ ≤ ((2 ^ k * n ^ (ℓ + 1) * ((n - k).choose r) : ℕ) : ℝ) := by
        exact_mod_cast kd_stageL_count_bound hrn
    _ = ((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
          * (((n - k).choose r : ℕ) : ℝ) := by
        push_cast
        ring

/-! ## Per-stage bounds -/

/-- The stage-`ℓ` contribution to `𝒞₀`. -/
lemma kd_stage_weight_le {n k r ℓ : ℕ} (hrn : 2 * (r + k) ≤ n)
    (hℓ : ℓ < k) :
    (n.choose (r + ℓ) : ℝ) * (((n - (r + ℓ) : ℕ)) : ℝ) * kdBeta n k r ℓ
      ≤ Real.sqrt (((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
        / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
  have hA : (0 : ℝ) < ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - (r + ℓ) by omega)
  have hB : (0 : ℝ) < (((n - k).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - k by omega)
  have hcast : (n.choose (r + ℓ) : ℝ) * (((n - (r + ℓ) : ℕ)) : ℝ)
      = ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [kdBeta,
    show ((n.choose (r + ℓ) * (n - (r + ℓ))
        * ((n - k).choose r) : ℕ) : ℝ)
      = ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ)
        * (((n - k).choose r : ℕ) : ℝ) from by push_cast; ring,
    hcast, mul_inv_sqrt_mul hA hB]
  exact kd_sqrt_ratio_le hrn hℓ

/-- The stage-`ℓ` contribution to `𝒞₁`. -/
lemma kd_stage_term_le {n k r ℓ : ℕ} (hrn : 2 * (r + k) ≤ n)
    (hℓ : ℓ < k) :
    (((n - k).choose r : ℕ) : ℝ)
      * (edV (n - k) r ^ 2 * (kdBeta n k r ℓ)⁻¹)
      ≤ Real.sqrt (((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
        / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
  have hA : (0 : ℝ) < ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega))
      (show 0 < n - (r + ℓ) by omega)
  have hB : (0 : ℝ) < (((n - k).choose r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ n - k by omega)
  rw [edV, kdBeta, inv_inv]
  have hstep : (((n - k).choose r : ℕ) : ℝ)
      * (((((n - k).choose r : ℕ) : ℝ))⁻¹ ^ 2
        * Real.sqrt ((n.choose (r + ℓ) * (n - (r + ℓ))
            * ((n - k).choose r) : ℕ) : ℝ))
      = Real.sqrt ((n.choose (r + ℓ) * (n - (r + ℓ))
            * ((n - k).choose r) : ℕ) : ℝ)
        / (((n - k).choose r : ℕ) : ℝ) := by
    field_simp
  rw [hstep,
    show ((n.choose (r + ℓ) * (n - (r + ℓ))
        * ((n - k).choose r) : ℕ) : ℝ)
      = ((n.choose (r + ℓ) * (n - (r + ℓ)) : ℕ) : ℝ)
        * (((n - k).choose r : ℕ) : ℝ) from by push_cast; ring,
    sqrt_mul_div hA.le]
  exact kd_sqrt_ratio_le hrn hℓ

/-! ## The negative complexity -/

private lemma sum_range_add_split (f : ℕ → ℝ) (r k : ℕ) :
    (∑ t ∈ Finset.range (r + k), f t)
      = (∑ t ∈ Finset.range r, f t)
        + ∑ ℓ ∈ Finset.range k, f (r + ℓ) := by
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show r + (k + 1) = (r + k) + 1 from rfl, Finset.sum_range_succ,
      IH, Finset.sum_range_succ, add_assoc]

/-- **The negative complexity**:
`𝒞₀ ≤ 2^{k+1}·r + ∑_{ℓ<k} √(2^k n^{ℓ+1}/(r+1)^ℓ)`. -/
theorem sum_kdOmega_sq_le {k r : ℕ} (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    (∑ e : Finset ι × ι, kdOmega (Fintype.card ι) k r e ^ 2)
      ≤ 2 ^ (k + 1) * r
        + ∑ ℓ ∈ Finset.range k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
              / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
  have hsq : ∀ e : Finset ι × ι, kdOmega (Fintype.card ι) k r e ^ 2
      = if e.2 ∈ e.1 then (0 : ℝ)
        else kdLevel (Fintype.card ι) k r e.1.card := by
    intro e
    rw [kdOmega]
    by_cases hj : e.2 ∈ e.1
    · rw [if_pos hj, if_pos hj]
      norm_num
    · rw [if_neg hj, if_neg hj, Real.sq_sqrt (kdLevel_nonneg _ _ _ _)]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hsq e,
    sum_edge_levelWeight (kdLevel (Fintype.card ι) k r)]
  have htrunc : (∑ t ∈ Finset.range (Fintype.card ι + 1),
      ((Fintype.card ι).choose t : ℝ)
        * (((Fintype.card ι - t : ℕ)) : ℝ)
        * kdLevel (Fintype.card ι) k r t)
      = ∑ t ∈ Finset.range (r + k),
        ((Fintype.card ι).choose t : ℝ)
          * (((Fintype.card ι - t : ℕ)) : ℝ)
          * kdLevel (Fintype.card ι) k r t := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr
      (show r + k ≤ Fintype.card ι + 1 by omega))
      fun t ht hnt => ?_).symm
    have h1 : r + k ≤ t := by
      rcases Nat.lt_or_ge t (r + k) with h | h
      · exact absurd (Finset.mem_range.mpr h) hnt
      · exact h
    rw [kdLevel, if_neg (by omega), if_neg (by omega), mul_zero]
  rw [htrunc, sum_range_add_split
    (fun t => ((Fintype.card ι).choose t : ℝ)
      * (((Fintype.card ι - t : ℕ)) : ℝ)
      * kdLevel (Fintype.card ι) k r t) r k]
  have hstageI : (∑ t ∈ Finset.range r,
      ((Fintype.card ι).choose t : ℝ)
        * (((Fintype.card ι - t : ℕ)) : ℝ)
        * kdLevel (Fintype.card ι) k r t) ≤ 2 ^ (k + 1) * r := by
    have hbound : ∀ t ∈ Finset.range r,
        ((Fintype.card ι).choose t : ℝ)
          * (((Fintype.card ι - t : ℕ)) : ℝ)
          * kdLevel (Fintype.card ι) k r t ≤ 2 ^ (k + 1) := by
      intro t ht
      have htr : t < r := Finset.mem_range.mp ht
      rw [kdLevel, if_pos htr, edW]
      have hY : (0 : ℝ) < (((Fintype.card ι - k).choose t : ℕ) : ℝ)
          * (((Fintype.card ι - k - t : ℕ)) : ℝ) := by
        refine mul_pos ?_ ?_
        · exact_mod_cast Nat.choose_pos
            (show t ≤ Fintype.card ι - k by omega)
        · exact_mod_cast show 0 < Fintype.card ι - k - t by omega
      rw [mul_inv_le_iff₀ hY]
      calc ((Fintype.card ι).choose t : ℝ)
            * (((Fintype.card ι - t : ℕ)) : ℝ)
          = (((Fintype.card ι).choose t
              * (Fintype.card ι - t) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ (k + 1) * ((Fintype.card ι - k).choose t
              * (Fintype.card ι - k - t)) : ℕ) : ℝ) := by
            exact_mod_cast kd_stageI_count_bound htr hrn
        _ = 2 ^ (k + 1) * ((((Fintype.card ι - k).choose t : ℕ) : ℝ)
              * (((Fintype.card ι - k - t : ℕ)) : ℝ)) := by
            push_cast
            ring
    calc (∑ t ∈ Finset.range r,
        ((Fintype.card ι).choose t : ℝ)
          * (((Fintype.card ι - t : ℕ)) : ℝ)
          * kdLevel (Fintype.card ι) k r t)
        ≤ ∑ _t ∈ Finset.range r, ((2 : ℝ) ^ (k + 1)) :=
          Finset.sum_le_sum hbound
      _ = 2 ^ (k + 1) * r := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hstages : (∑ ℓ ∈ Finset.range k,
      ((Fintype.card ι).choose (r + ℓ) : ℝ)
        * (((Fintype.card ι - (r + ℓ) : ℕ)) : ℝ)
        * kdLevel (Fintype.card ι) k r (r + ℓ))
      ≤ ∑ ℓ ∈ Finset.range k,
          Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
            / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have hℓk := Finset.mem_range.mp hℓ
    rw [kdLevel, if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
    exact kd_stage_weight_le hrn hℓk
  linarith

/-! ## The positive complexity -/

private lemma kd_subset_sdiff {k : ℕ} {a : Fin k → ι} {S : Finset ι}
    (ha : ∀ i, a i ∉ S) :
    S ⊆ Finset.univ \ Finset.image a Finset.univ := by
  intro z hz
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun himg => ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp himg
  exact ha i hz

private lemma kd_all_notMem {k : ℕ} {a : Fin k → ι} {S : Finset ι}
    (hS : S ⊆ Finset.univ \ Finset.image a Finset.univ) :
    ∀ i, a i ∉ S := fun i h =>
  (Finset.mem_sdiff.mp (hS h)).2
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private lemma kd_mem_sdiff {k : ℕ} {a : Fin k → ι} {j : ι}
    (hj : ∀ i, j ≠ a i) :
    j ∈ Finset.univ \ Finset.image a Finset.univ := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun himg => ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp himg
  exact hj i hi.symm

private lemma kd_ne_of_mem_sdiff {k : ℕ} {a : Fin k → ι} {j : ι}
    (hj : j ∈ Finset.univ \ Finset.image a Finset.univ) :
    ∀ i, j ≠ a i := fun i h =>
  (Finset.mem_sdiff.mp hj).2
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)

lemma kd_card_sdiff {k : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) :
    (Finset.univ \ Finset.image a Finset.univ).card
      = Fintype.card ι - k := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
    Finset.card_univ, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

/-- **The positive complexity**: for every collision tuple,
`𝒞₁ ≤ r + ∑_{ℓ<k} √(2^k n^{ℓ+1}/(r+1)^ℓ)`. -/
theorem sum_kdFlow_div_sq_le {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    (∑ e : Finset ι × ι,
      (kdFlow k r a e.1 e.2 / kdOmega (Fintype.card ι) k r e) ^ 2)
      ≤ r + ∑ ℓ ∈ Finset.range k,
          Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
            / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
  classical
  have hD := kd_card_sdiff (ι := ι) hinj
  have hsplit : ∀ e : Finset ι × ι,
      (kdFlow k r a e.1 e.2 / kdOmega (Fintype.card ι) k r e) ^ 2
      = (if e.1 ⊆ Finset.univ \ Finset.image a Finset.univ
            ∧ e.2 ∈ Finset.univ \ Finset.image a Finset.univ ∧ e.2 ∉ e.1
          then (if e.1.card < r then edW (Fintype.card ι - k) e.1.card
            else 0)
          else 0)
        + ∑ ℓ : Fin k,
            (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ)
                ∧ e.2 = a ℓ
              then edV (Fintype.card ι - k) r ^ 2
                * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0) := by
    intro e
    rw [kdFlow]
    by_cases h1 : (∀ i, a i ∉ e.1) ∧ e.2 ∉ e.1 ∧ (∀ i, e.2 ≠ a i)
        ∧ e.1.card < r
    · have hI : e.1 ⊆ Finset.univ \ Finset.image a Finset.univ
          ∧ e.2 ∈ Finset.univ \ Finset.image a Finset.univ
          ∧ e.2 ∉ e.1 :=
        ⟨kd_subset_sdiff h1.1, kd_mem_sdiff h1.2.2.1, h1.2.1⟩
      have hstages : (∑ ℓ : Fin k,
          (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ)
              ∧ e.2 = a ℓ
            then edV (Fintype.card ι - k) r ^ 2
              * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0))
          = 0 :=
        Finset.sum_eq_zero fun ℓ _ => if_neg fun hc => by
          have hc1 := hc.2.1
          have hlt := h1.2.2.2
          omega
      rw [if_pos h1, if_pos hI, hstages, add_zero, if_pos h1.2.2.2,
        kdOmega, if_neg h1.2.1, kdLevel, if_pos h1.2.2.2, Real.div_sqrt,
        Real.sq_sqrt (edW_nonneg _ _)]
    · rw [if_neg h1]
      by_cases h2 : ∃ ℓ : Fin k, kdPrefix a (ℓ : ℕ) e.1
          ∧ e.1.card = r + (ℓ : ℕ) ∧ e.2 = a ℓ
      · obtain ⟨ℓ₀, hpre₀, hcard₀, hj₀⟩ := h2
        have hℓ₀ : (ℓ₀ : ℕ) < k := ℓ₀.isLt
        have hjS : e.2 ∉ e.1 := by
          rw [hj₀]
          exact hpre₀.2 ℓ₀ (le_refl _)
        have hnotI : ¬ (e.1 ⊆ Finset.univ \ Finset.image a Finset.univ
            ∧ e.2 ∈ Finset.univ \ Finset.image a Finset.univ
            ∧ e.2 ∉ e.1) :=
          fun hc => (kd_ne_of_mem_sdiff hc.2.1) ℓ₀ hj₀
        have hstage : (∑ ℓ : Fin k,
            (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ)
                ∧ e.2 = a ℓ
              then edV (Fintype.card ι - k) r ^ 2
                * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0))
            = edV (Fintype.card ι - k) r ^ 2
              * (kdBeta (Fintype.card ι) k r (ℓ₀ : ℕ))⁻¹ := by
          rw [Finset.sum_eq_single_of_mem ℓ₀ (Finset.mem_univ _)
            (fun ℓ _ hne => if_neg fun hc => hne (Fin.ext (by
              have hc1 := hc.2.1
              omega))),
            if_pos ⟨hpre₀, hcard₀, hj₀⟩]
        rw [if_pos ⟨ℓ₀, hpre₀, hcard₀, hj₀⟩, if_neg hnotI, hstage,
          zero_add, kdOmega, if_neg hjS, kdLevel, if_neg (by omega),
          if_pos (by omega : e.1.card < r + k),
          show e.1.card - r = (ℓ₀ : ℕ) from by omega, div_pow,
          Real.sq_sqrt (kdBeta_nonneg _ _ _ _), div_eq_mul_inv]
      · have hstages : (∑ ℓ : Fin k,
            (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ)
                ∧ e.2 = a ℓ
              then edV (Fintype.card ι - k) r ^ 2
                * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0))
            = 0 :=
          Finset.sum_eq_zero fun ℓ _ => if_neg fun hc => h2 ⟨ℓ, hc⟩
        rw [if_neg h2, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          hstages, add_zero]
        by_cases hI : e.1 ⊆ Finset.univ \ Finset.image a Finset.univ
            ∧ e.2 ∈ Finset.univ \ Finset.image a Finset.univ ∧ e.2 ∉ e.1
        · rw [if_pos hI, if_neg (show ¬ e.1.card < r from fun hlt =>
            h1 ⟨kd_all_notMem hI.1, hI.2.2,
              kd_ne_of_mem_sdiff hI.2.1, hlt⟩)]
        · rw [if_neg hI]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hsplit e,
    Finset.sum_add_distrib]
  have hIsum : (∑ e : Finset ι × ι,
      if e.1 ⊆ Finset.univ \ Finset.image a Finset.univ
          ∧ e.2 ∈ Finset.univ \ Finset.image a Finset.univ ∧ e.2 ∉ e.1
        then (if e.1.card < r then edW (Fintype.card ι - k) e.1.card
          else 0)
        else 0) = r := by
    rw [sum_edge_levelWeight_sub
        (Finset.univ \ Finset.image a Finset.univ)
        (fun t => if t < r then edW (Fintype.card ι - k) t else 0), hD]
    have hsub : Finset.range r
        ⊆ Finset.range (Fintype.card ι - k + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hvan : ∀ t ∈ Finset.range (Fintype.card ι - k + 1),
        t ∉ Finset.range r →
        ((Fintype.card ι - k).choose t : ℝ)
          * (((Fintype.card ι - k - t : ℕ)) : ℝ)
          * (if t < r then edW (Fintype.card ι - k) t else 0) = 0 := by
      intro t _ hnt
      have hrt : r ≤ t := by
        rcases Nat.lt_or_ge t r with h | h
        · exact absurd (Finset.mem_range.mpr h) hnt
        · exact h
      rw [if_neg (by omega), mul_zero]
    rw [(Finset.sum_subset hsub hvan).symm,
      Finset.sum_congr rfl fun t ht => show
        ((Fintype.card ι - k).choose t : ℝ)
          * (((Fintype.card ι - k - t : ℕ)) : ℝ)
          * (if t < r then edW (Fintype.card ι - k) t else 0) = 1 from by
        have htr : t < r := Finset.mem_range.mp ht
        rw [if_pos htr, edW]
        refine mul_inv_cancel₀ (mul_pos ?_ ?_).ne'
        · exact_mod_cast Nat.choose_pos
            (show t ≤ Fintype.card ι - k by omega)
        · exact_mod_cast show 0 < Fintype.card ι - k - t by omega,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hstagesum : (∑ e : Finset ι × ι, ∑ ℓ : Fin k,
      (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ) ∧ e.2 = a ℓ
        then edV (Fintype.card ι - k) r ^ 2
          * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0))
      ≤ ∑ ℓ ∈ Finset.range k,
          Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
            / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
    rw [Finset.sum_comm]
    calc (∑ ℓ : Fin k, ∑ e : Finset ι × ι,
        (if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ)
            ∧ e.2 = a ℓ
          then edV (Fintype.card ι - k) r ^ 2
            * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹ else 0))
        = ∑ ℓ : Fin k, (((Fintype.card ι - k).choose r : ℕ) : ℝ)
            * (edV (Fintype.card ι - k) r ^ 2
              * (kdBeta (Fintype.card ι) k r (ℓ : ℕ))⁻¹) := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [kd_sum_edge_stage hinj ℓ r _, hD]
      _ ≤ ∑ ℓ : Fin k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ ((ℓ : ℕ) + 1) : ℕ) : ℝ)
              / (((r + 1) ^ (ℓ : ℕ) : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun ℓ _ => kd_stage_term_le hrn ℓ.isLt
      _ = ∑ ℓ ∈ Finset.range k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
              / (((r + 1) ^ ℓ : ℕ) : ℝ)) :=
          Fin.sum_univ_eq_sum_range
            (fun ℓ => Real.sqrt
              (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
                / (((r + 1) ^ ℓ : ℕ) : ℝ))) k
  linarith

end QuantumQueryComplexity
