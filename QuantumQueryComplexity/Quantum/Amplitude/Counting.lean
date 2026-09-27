import QuantumQueryComplexity.Quantum.Amplitude.Estimation
import QuantumQueryComplexity.Quantum.Amplitude.Search
set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Endpoints of amplitude estimation, and approximate counting

* `aeAlg_prob_zero_of_succProb_eq_zero`: at `p = 0` the clock reads `0` surely, and the
  estimate is exactly `0`;
* `aeAlg_prob_half_of_succProb_eq_one`: at `p = 1` **with an even clock** `M = 2·h` the clock
  reads `h` surely, and the estimate is exactly `1`.  Nothing of the sort is claimed for an
  odd `M`.

**Approximate counting.**  For `n ≥ 1` and the search setup (`S = 0`, `C = 2` native
queries), `p = t/n` with `t` the number of marked indices.  `countAlg n M` is the
amplitude-estimation algorithm of that setup, with `2·(M − 1)` native queries and the
real-valued decoder `countEstimate n M y = n·sin²(π·y/M)`:

    Pr[ |countEstimate − t| ≤ 8π·√(t(n−t))/M + 16π²·n/M² ] ≥ 5/6,

and `|countEstimate − t| ≤ η·n` for `M ≥ 8π/η`.  The output stays a finite label with a
decoder; no integer rounding is performed (it would add its own error).  `n = 0` is trivial:
there is nothing to count (`markedCount_fin_zero`).  A relative-error statement needs a
positive lower bound on `t/n`; adaptive estimation without it is future work.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix Finset

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

namespace AmpSetup

variable (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

/-- **`p = 0`: the clock reads `0` surely.** -/
theorem aeAlg_prob_zero_of_succProb_eq_zero (hP : P.Marks read Good) (x : X) {M : ℕ}
    (hM : 0 < M) (h0 : P.succProb read Good x = 0) :
    (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len ⟨0, hM⟩ = 1 := by
  rw [P.aeAlg_prob hP x hM, h0, groverAngle, Real.sqrt_zero, Real.arcsin_zero]
  have hk := peKernel_int hM 0
  simp only [Int.cast_zero] at hk
  simp only [zero_div, neg_zero, Nat.cast_zero, sub_zero, hk, map_one]
  norm_num

/-- The estimate decoded from the label `0` is exactly `0`. -/
lemma aeEstimate_zero {M : ℕ} (hM : 0 < M) : aeEstimate M ⟨0, hM⟩ = 0 := by
  simp [aeEstimate]

/-- **`p = 1`, even clock `M = 2h`: the clock reads `h` surely.** -/
theorem aeAlg_prob_half_of_succProb_eq_one (hP : P.Marks read Good) (x : X) {h : ℕ}
    (hh : 0 < h) (h1 : P.succProb read Good x = 1) :
    (P.aeAlg (by omega : 0 < 2 * h)).prob (read x) (P.aeRoutine (by omega : 0 < 2 * h)).len
      ⟨h, by omega⟩ = 1 := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hpi := Real.pi_ne_zero
  rw [P.aeAlg_prob hP x _, h1, groverAngle, Real.sqrt_one, Real.arcsin_one]
  have e1 : Real.pi / 2 / Real.pi - ((h : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) = ((0 : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  have e2 : -(Real.pi / 2 / Real.pi) - ((h : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) = ((-1 : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e1, e2, peKernel_int (by omega), peKernel_int (by omega)]
  norm_num

/-- The estimate decoded from the middle label of an even clock is exactly `1`. -/
lemma aeEstimate_half {h : ℕ} (hh : 0 < h) : aeEstimate (2 * h) ⟨h, by omega⟩ = 1 := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [aeEstimate]
  have : Real.pi * ((h : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) = Real.pi / 2 := by
    push_cast; field_simp
  rw [this, Real.sin_pi_div_two, one_pow]

end AmpSetup

/-! ## Approximate counting -/

open AmpSetup (aeError)

variable {n : ℕ}

/-- **The counting algorithm**: amplitude estimation of the search setup. -/
noncomputable def countAlg (hn : 0 < n) {M : ℕ} (hM : 0 < M) := (searchSetup hn).aeAlg hM

/-- Its budget: `2·(M − 1)` native queries. -/
def countBudget (M : ℕ) : ℕ := 2 * (M - 1)

lemma searchSetup_aeRoutine_len (hn : 0 < n) {M : ℕ} (hM : 0 < M) :
    ((searchSetup hn).aeRoutine hM).len = countBudget M := by
  rw [AmpSetup.aeRoutine_len, countBudget]
  change 0 + (M - 1) * (2 * 0 + 2) = 2 * (M - 1)
  omega

/-- The real-valued count decoder `n·sin²(π·y/M)`. -/
noncomputable def countEstimate (n M : ℕ) (y : Fin M) : ℝ := n * aeEstimate M y

/-- The coarse counting error `8π·√(t(n−t))/M + 16π²·n/M²`. -/
noncomputable def countError (n M t : ℕ) : ℝ :=
  8 * Real.pi * Real.sqrt ((t : ℝ) * ((n : ℝ) - t)) / M + 16 * Real.pi ^ 2 * n / (M : ℝ) ^ 2

lemma mul_aeError (hn : 0 < n) (M t : ℕ) :
    (n : ℝ) * aeError M ((t : ℝ) / n) = countError n M t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (n : ℝ) * Real.sqrt ((t : ℝ) / n * (1 - (t : ℝ) / n))
      = Real.sqrt ((t : ℝ) * ((n : ℝ) - t)) := by
    rw [← Real.sqrt_sq hn'.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn'.le]
    congr 1
    field_simp
  rw [aeError, countError, mul_add, ← hsq]
  ring

/-- **Approximate counting**: with probability at least `5/6` the decoded count is within
`8π·√(t(n−t))/M + 16π²·n/M²` of the number `t` of marked indices. -/
theorem five_sixths_le_count_accurate (hn : 0 < n) {M : ℕ} (hM : 0 < M) (x : Fin n → Bool) :
    5 / 6 ≤ ∑ y : Fin M,
      if |countEstimate n M y - markedCount x| ≤ countError n M (markedCount x)
      then (countAlg hn hM).prob x (countBudget M) y else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (searchSetup hn).five_sixths_le_ae_accurate (searchSetup_marks hn) x hM
  rw [searchSetup_succProb, searchSetup_aeRoutine_len hn hM] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
  have hiff : |aeEstimate M y - (markedCount x : ℝ) / n| ≤ aeError M ((markedCount x : ℝ) / n)
      ↔ |countEstimate n M y - markedCount x| ≤ countError n M (markedCount x) := by
    rw [← mul_aeError hn, countEstimate,
      show (n : ℝ) * aeEstimate M y - markedCount x
        = n * (aeEstimate M y - (markedCount x : ℝ) / n) by field_simp,
      abs_mul, abs_of_pos hn']
    exact (mul_le_mul_iff_right₀ hn').symm
  by_cases hc : |aeEstimate M y - (markedCount x : ℝ) / n| ≤ aeError M ((markedCount x : ℝ) / n)
  · rw [if_pos hc, if_pos (hiff.mp hc)]; rfl
  · rw [if_neg hc, if_neg (fun h' => hc (hiff.mpr h'))]

/-- The `3/4` form, kept for compatibility. -/
theorem three_quarters_le_count_accurate (hn : 0 < n) {M : ℕ} (hM : 0 < M) (x : Fin n → Bool) :
    3 / 4 ≤ ∑ y : Fin M,
      if |countEstimate n M y - markedCount x| ≤ countError n M (markedCount x)
      then (countAlg hn hM).prob x (countBudget M) y else 0 :=
  le_trans (by norm_num) (five_sixths_le_count_accurate hn hM x)

/-- **Additive accuracy `η·n`** with probability at least `5/6`, for `M ≥ 8π/η`,
`0 < η ≤ 1`. -/
theorem count_additive_five_sixths (hn : 0 < n) {M : ℕ} (hM : 0 < M) (x : Fin n → Bool) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hMη : 8 * Real.pi / η ≤ M) :
    5 / 6 ≤ ∑ y : Fin M, if |countEstimate n M y - markedCount x| ≤ η * n
      then (countAlg hn hM).prob x (countBudget M) y else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (searchSetup hn).ae_additive_five_sixths (searchSetup_marks hn) x hM hη hη1 hMη
  rw [searchSetup_succProb, searchSetup_aeRoutine_len hn hM] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
  have hiff : |aeEstimate M y - (markedCount x : ℝ) / n| ≤ η
      ↔ |countEstimate n M y - markedCount x| ≤ η * n := by
    rw [countEstimate,
      show (n : ℝ) * aeEstimate M y - markedCount x
        = n * (aeEstimate M y - (markedCount x : ℝ) / n) by field_simp,
      abs_mul, abs_of_pos hn', mul_comm η (n : ℝ)]
    exact (mul_le_mul_iff_right₀ hn').symm
  by_cases hc : |aeEstimate M y - (markedCount x : ℝ) / n| ≤ η
  · rw [if_pos hc, if_pos (hiff.mp hc)]; rfl
  · rw [if_neg hc, if_neg (fun h' => hc (hiff.mpr h'))]

/-- The `3/4` form, kept for compatibility. -/
theorem count_additive (hn : 0 < n) {M : ℕ} (hM : 0 < M) (x : Fin n → Bool) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hMη : 8 * Real.pi / η ≤ M) :
    3 / 4 ≤ ∑ y : Fin M, if |countEstimate n M y - markedCount x| ≤ η * n
      then (countAlg hn hM).prob x (countBudget M) y else 0 :=
  le_trans (by norm_num) (count_additive_five_sixths hn hM x hη hη1 hMη)

/-- `n = 0`: there is nothing to count. -/
theorem markedCount_fin_zero (x : Fin 0 → Bool) : markedCount x = 0 := by
  simp [markedCount]

end QuantumQueryComplexity
