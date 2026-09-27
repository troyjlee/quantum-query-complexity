import QuantumQueryComplexity.ED.Cost
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The element distinctness upper bound

Assembling the flow (`QuantumQueryComplexity/ED/Flow.lean`), the half-weights and the two
complexities (`QuantumQueryComplexity/ED/Cost.lean`) through the learning-graph theorem
(`QuantumQueryComplexity/LearningGraph/Dual.lean`) gives, for `2r + 2 ≤ n`,

  `ADV±(edFun) ≤ 4r + √(2n) + n/√(r+1)`,

and choosing `r = ⌊n^{2/3}⌋` (with the read-everything dual `2n` covering
`n ≤ 64`),

  `ADV±(edFun) ≤ 8 · n^{2/3}`,

matching Ambainis' quantum walk up to the constant, uniformly in the
alphabet `σ`.  By weak duality this bounds the negative-weight adversary;
the bounded-error quantum query complexity follows operationally in
`Quantum/EDApplications.lean` — natively `ed_qQuery_le_min`
(`Q_{1/3}(ED) ≤ min{n, 8192·(1 + 8·n^{2/3})}`, through the cardinality-free
extraction on this file's `hasDual_edFun`, so no `√|σ|`), and in the
canonical one-hot XOR model `ed_oneHotQQuery_le_min` at `16384` with the
same exact read-all cap.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Positivity of the parametric bound, needed on both sides of the
learning-graph theorem. -/
private lemma edBound_pos (r : ℕ) (hrn : 2 * r + 2 ≤ Fintype.card ι) :
    (0 : ℝ) < 4 * r + (Real.sqrt (2 * Fintype.card ι)
      + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)) := by
  have h1 : (0 : ℝ) < Real.sqrt (2 * Fintype.card ι) := by
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast show 0 < Fintype.card ι by omega
    linarith
  have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / Real.sqrt (r + 1) := by
    positivity
  linarith

/-- **The parametric bound, as a dual solution**: element distinctness has a
feasible dual of cost `4r + √(2n) + n/√(r+1)` whenever `2r + 2 ≤ n`.  The
bundled form is what a *windowed* use needs (`LDS/Window.lean`): a dual
solution restricts along an injection of index types, an `advPM` inequality
does not. -/
theorem hasDual_edFun_param (r : ℕ) (hrn : 2 * r + 2 ≤ Fintype.card ι) :
    HasDual (edFun (ι := ι) (σ := σ))
      (4 * r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1))) := by
  have hBpos : (0 : ℝ) < 4 * r + (Real.sqrt (2 * Fintype.card ι)
      + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)) := edBound_pos r hrn
  have hr : r ≤ Fintype.card ι - 2 := by omega
  have hhas : HasDual (edFun (ι := ι) (σ := σ))
      (Real.sqrt ((4 * r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)))
        * (4 * r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1))))) := by
    refine LGFlow.hasDual (edLGFlow (σ := σ) r hr
      (edOmega (Fintype.card ι) r)
      (fun e hj hc => edOmega_ne_zero hrn hj hc)) hBpos hBpos ?_ ?_
    · show (∑ e : Finset ι × ι, edOmega (Fintype.card ι) r e ^ 2) ≤ _
      exact sum_edOmega_sq_le hrn
    · intro x hx
      have hex := edFun_eq_true_iff.mp hx
      show (∑ e : Finset ι × ι,
        ((if h : ∃ q : ι × ι, q.1 ≠ q.2 ∧ x q.1 = x q.2
            then edFlow r h.choose.1 h.choose.2 e.1 e.2 else 0)
          / edOmega (Fintype.card ι) r e) ^ 2) ≤ _
      simp only [dif_pos hex]
      refine (sum_edFlow_div_sq_le hex.choose_spec.1 hrn).trans ?_
      have h0 : (0 : ℝ) ≤ 3 * (r : ℝ) := by positivity
      linarith
  rw [Real.sqrt_mul_self hBpos.le] at hhas
  exact hhas

/-- **The parametric bound**: `ADV±(ED) ≤ 4r + √(2n) + n/√(r+1)` whenever
`2r + 2 ≤ n`. -/
theorem advPM_edFun_le_param (r : ℕ) (hrn : 2 * r + 2 ≤ Fintype.card ι) :
    advPM (edFun (ι := ι) (σ := σ))
      ≤ 4 * r + (Real.sqrt (2 * Fintype.card ι)
          + (Fintype.card ι : ℝ) / Real.sqrt (r + 1)) :=
  advPM_le_of_hasDual (edBound_pos r hrn).le (hasDual_edFun_param r hrn)

/-- `64^{1/3} = 4`. -/
private lemma rpow_third_64 : ((64 : ℝ)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [show (64 : ℝ) = 4 ^ ((3 : ℕ) : ℝ) from by
      rw [Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- **The element distinctness upper bound, as a dual solution**:
`edFun` has a feasible dual of cost `8 · n^{2/3}`, for every finite index type
and alphabet. -/
theorem hasDual_edFun (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Type) [Fintype σ] [DecidableEq σ] :
    HasDual (edFun (ι := ι) (σ := σ))
      (8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) := by
  by_cases hn : Fintype.card ι ≤ 64
  · -- small `n`: the read-everything dual costs `2n ≤ 8 n^{2/3}`
    refine (hasDual_two_mul_card (edFun (ι := ι) (σ := σ))).mono ?_
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · rw [h0]
      norm_num [Real.zero_rpow]
    · have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
      have hsplit : ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3)
          * ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) = (Fintype.card ι : ℝ) := by
        rw [← Real.rpow_add hnpos]
        norm_num
      have hthird : ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3) ≤ 4 := by
        rw [← rpow_third_64]
        exact Real.rpow_le_rpow hnpos.le (by exact_mod_cast hn) (by norm_num)
      have h23 : (0 : ℝ) ≤ ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) :=
        Real.rpow_nonneg hnpos.le _
      calc 2 * (Fintype.card ι : ℝ)
          = 2 * (((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3)
              * ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by rw [hsplit]
        _ ≤ 2 * (4 * ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_right hthird h23
        _ = 8 * ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) := by ring
  · -- large `n`: the three-stage flow at `r = ⌊n^{2/3}⌋`
    push_neg at hn
    have hn' : (64 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
    have hn1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by linarith
    have hfloor : ((⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ))
        ≤ ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) :=
      Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have hfloor' : ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)
        < (⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hsplit : ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)
        * ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3) = (Fintype.card ι : ℝ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hthird : (4 : ℝ) ≤ ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← rpow_third_64]
      exact Real.rpow_le_rpow (by norm_num) hn'.le (by norm_num)
    have hquarter : 4 * (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3))
        ≤ (Fintype.card ι : ℝ) := by
      calc 4 * (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3))
          ≤ ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3)
            * ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right hthird (Real.rpow_nonneg hnpos.le _)
        _ = (Fintype.card ι : ℝ) := by rw [mul_comm]; exact hsplit
    have hkey : 2 * ⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ + 2
        ≤ Fintype.card ι := by
      have : ((2 * ⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ + 2 : ℕ) : ℝ)
          ≤ (Fintype.card ι : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    refine (hasDual_edFun_param (σ := σ)
      ⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ hkey).mono ?_
    -- the three pieces
    have hb1 : 4 * ((⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ))
        ≤ 4 * (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by linarith
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hb2 : Real.sqrt (2 * (Fintype.card ι : ℝ))
        ≤ 2 * (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hhalf : Real.sqrt (Fintype.card ι : ℝ)
          ≤ ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      calc Real.sqrt 2 * Real.sqrt (Fintype.card ι : ℝ)
          ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
        _ ≤ 2 * (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by
            exact mul_le_mul_of_nonneg_left hhalf (by norm_num)
    have hb3 : (Fintype.card ι : ℝ)
        / Real.sqrt ((⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) + 1)
        ≤ ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) := by
      have hthirdpos : (0 : ℝ) < ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3) := by
        linarith
      have hden : ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3)
          ≤ Real.sqrt ((⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) + 1) := by
        have h13 : ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3)
            = Real.sqrt (((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
          norm_num
        rw [h13]
        exact Real.sqrt_le_sqrt (by linarith)
      calc (Fintype.card ι : ℝ)
          / Real.sqrt ((⌊((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) + 1)
          ≤ (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 3) := by
            exact div_le_div_of_nonneg_left hnpos.le hthirdpos hden
        _ = ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) := by
            rw [eq_comm, eq_div_iff hthirdpos.ne']
            exact hsplit
    have h23 : (0 : ℝ) ≤ ((Fintype.card ι : ℝ)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg hnpos.le _
    linarith

/-- **The element distinctness upper bound**:
`ADV±(edFun) ≤ 8 · n^{2/3}`, for every finite index type and alphabet. -/
theorem advPM_edFun_le (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Type) [Fintype σ] [DecidableEq σ] :
    advPM (edFun (ι := ι) (σ := σ))
      ≤ 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) :=
  advPM_le_of_hasDual (by positivity) (hasDual_edFun ι σ)

end QuantumQueryComplexity
