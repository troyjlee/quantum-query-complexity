import QuantumQueryComplexity.Quantum.Amplitude.Counting
import QuantumQueryComplexity.Quantum.Amplitude.Median
import QuantumQueryComplexity.Quantum.IndexCopy

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Counting and sampling the marked labels of a known set

[CGKLPZ26, Lemma 2.4; BHMT02]. A known set `S` of `a` labels, a subset of the input indices,
contains `r` marked labels (`markedIn S x`, the labels `i ∈ S` with `x i = true`); only the marks
are queried.

**Counting** (`exists_count`). With `labelCountBudget a ε ≤ 3000 (√a + 1)(1 + ln(1/ε))` queries, an
estimate `r̂ ∈ {0, …, a}` is good (`CountGood r r̂`) except with probability `ε`:
`r̂ = 0 ↔ r = 0`, `r/2 ≤ r̂ ≤ 2r` and `|r̂ − r| ≤ √r / 2`. When `r = 0` the estimate is `0`
surely. Construction: phase estimation on `⌈80π√a⌉ + 1` clock values gives additive error
`√r/10 + 1/100` with probability `5/6` (`five_sixths_le_count_accurate`, on the label set);
rounding makes the error at most `√r/2`; the median of `2⌈ln(1/ε)/ln(3/2)⌉ + 1` runs gives error
probability `ε` and keeps the sure `0` (`Realizes.median_pointMass`).

**Samples** (`exists_sample`). For any `r̂` and batch size `s`, with the fixed budget
`sampleBudget a r̂ s ε`, at most `80 (s + 1 + ln(1/ε)) √(a/r̂)` when `0 < r̂ ≤ a`
(`sampleBudget_le`), the output is either `none` (failure) or `s` labels. **Whatever `r̂`, the
labels are independent and uniform over the marked labels given success**:
`P(some y) = P(success) · ∏_j 1[y_j marked]/r`. If `0 < r̂ ≤ 2r`, failure has probability at
most `ε`. Construction: `4s + 2⌈ln(1/ε)/ln(9/4)⌉` verified randomized Grover trials of
`⌈√(2a/r̂)⌉` iterations, keeping the first `s` successes; each success is uniform over the marked
labels (`markedCount_mul_searchAlg_prob_some`), and each trial succeeds with probability `≥ 2/3`
when `r̂/(2a) ≤ r/a`.

Here `ln` is the natural logarithm. A call's guarantee concerns its own run, so inside a program
(`Prog`) it holds conditionally on every earlier outcome, which may have chosen `r̂`.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The marked labels** of the known set `S`. -/
def markedIn (S : Finset ι) (x : ι → Bool) : Finset ι := S.filter fun i => x i = true

/-- **A good count estimate** [CGKLPZ26, Lemma 2.4]: zero exactly when there is no marked label,
within a factor `2`, and within `√r / 2`. -/
def CountGood (r rh : ℕ) : Prop :=
  (rh = 0 ↔ r = 0) ∧ r ≤ 2 * rh ∧ rh ≤ 2 * r ∧ |(rh : ℝ) - r| ≤ Real.sqrt r / 2

/-! ## Counting -/

/-- The number of median repetitions for error `ε`: `⌈ln(1/ε)/ln(3/2)⌉`. -/
noncomputable def labelCountReps (ε : ℝ) : ℕ := ⌈Real.log (1 / ε) / Real.log (3 / 2)⌉₊

/-- The phase-estimation clock for additive error `√r/10 + 1/100` on `a` labels. -/
noncomputable def labelCountClock (a : ℕ) : ℕ := ⌈80 * Real.pi * Real.sqrt a⌉₊ + 1

/-- **The counting budget**: `2j + 1` runs of `2(M − 1)` queries, `M = labelCountClock a`. -/
noncomputable def labelCountBudget (a : ℕ) (ε : ℝ) : ℕ :=
  (2 * labelCountReps ε + 1) * (2 * (labelCountClock a - 1))

/-- `2/5 < ln(3/2)`. -/
private lemma lsc_two_fifths_lt_log : 2 / 5 < Real.log (3 / 2) := by
  have h := Real.exp_bound (x := 2 / 5) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [(abs_le.mp h).2]

/-- **The counting budget is `O(√a log(1/ε))`.** -/
theorem labelCountBudget_le (a : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (labelCountBudget a ε : ℝ) ≤ 3000 * (Real.sqrt a + 1) * (1 + Real.log (1 / ε)) := by
  have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  have hc := lsc_two_fifths_lt_log
  have hpi := Real.pi_lt_d2
  have hs : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  set L := Real.log (1 / ε) with hL_def
  set j := labelCountReps ε with hj_def
  set C := ⌈80 * Real.pi * Real.sqrt a⌉₊ with hC_def
  have hj : (j : ℝ) ≤ 5 / 2 * L + 1 := by
    have h1 : (j : ℝ) < L / Real.log (3 / 2) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hL (by linarith))
    have h2 : L / Real.log (3 / 2) ≤ 5 / 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hC : (C : ℝ) ≤ 252 * Real.sqrt a + 1 := by
    have h1 : (C : ℝ) < 80 * Real.pi * Real.sqrt a + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hbud : (labelCountBudget a ε : ℝ) = (2 * j + 1) * (2 * C) := by
    simp only [labelCountBudget, labelCountClock, Nat.add_sub_cancel, hj_def, hC_def]
    push_cast
    ring
  rw [hbud]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  calc (2 * (j : ℝ) + 1) * (2 * C) ≤ (5 * L + 3) * (2 * (252 * Real.sqrt a + 1)) := by
        exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 3000 * (Real.sqrt a + 1) * (1 + L) := by nlinarith [mul_nonneg hL hs]

/-- `√t ≤ t` for a natural number `t`. -/
private lemma lsc_sqrt_le_self (t : ℕ) : Real.sqrt t ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

/-- A count estimate is good iff it is within `√r / 2` and zero when `r` is. -/
private lemma lsc_countGood_iff (t f : ℕ) :
    CountGood t f ↔ |(f : ℝ) - t| ≤ Real.sqrt t / 2 ∧ (t = 0 → f = 0) := by
  constructor
  · rintro ⟨h0, -, -, h⟩
    exact ⟨h, h0.mpr⟩
  · rintro ⟨h, h0⟩
    have hs := lsc_sqrt_le_self t
    have hab := abs_le.mp h
    refine ⟨⟨fun hf => ?_, h0⟩, ?_, ?_, h⟩
    · subst hf
      by_contra ht
      have h1 : (1 : ℝ) ≤ t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht
      push_cast at hab
      linarith [hab.1]
    · have h1 : (t : ℝ) ≤ 2 * f := by linarith [hab.1]
      exact_mod_cast h1
    · have h1 : (f : ℝ) ≤ 2 * t := by linarith [hab.2, (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      exact_mod_cast h1

/-- The good estimates form an interval. -/
private lemma lsc_countGood_convex (t a b c : ℕ) (ha : CountGood t a) (hc : CountGood t c)
    (hab : a ≤ b) (hbc : b ≤ c) : CountGood t b := by
  rw [lsc_countGood_iff] at ha hc ⊢
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, fun ht => ?_⟩
  · linarith [(abs_le.mp ha.1).1]
  · linarith [(abs_le.mp hc.1).2]
  · have := hc.2 ht
    omega

/-- **Rounding**: a nonnegative estimate within `√t/10 + 1/100` of `t`, rounded to the nearest
integer, is good. -/
private lemma lsc_round_good (t : ℕ) {e : ℝ} (he : 0 ≤ e)
    (h : |e - t| ≤ Real.sqrt t / 10 + 1 / 100) : CountGood t ⌊e + 1 / 2⌋₊ := by
  rw [lsc_countGood_iff]
  have hab := abs_le.mp h
  have hfl : (⌊e + 1 / 2⌋₊ : ℝ) ≤ e + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : e + 1 / 2 < ⌊e + 1 / 2⌋₊ + 1 := Nat.lt_floor_add_one _
  rcases Nat.lt_or_ge t 25 with ht | ht
  · have ht' : (t : ℝ) ≤ 24 := by exact_mod_cast Nat.lt_succ_iff.mp ht
    have hs : Real.sqrt t < 49 / 10 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith
    have hf : ⌊e + 1 / 2⌋₊ = t := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> linarith [hab.1, hab.2]
    rw [hf, sub_self, abs_zero]
    exact ⟨by positivity, fun h0 => h0⟩
  · have hs : (5 : ℝ) ≤ Real.sqrt t := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have : (25 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    refine ⟨abs_le.mpr ⟨by linarith [hab.1], by linarith [hab.2]⟩, fun h0 => by omega⟩

/-- The coarse counting error is at most `√t/10 + 1/100` once the clock exceeds `80π√a`. -/
private lemma lsc_countError_le {a : ℕ} (ha : 0 < a) {M : ℕ}
    (hM : 80 * Real.pi * Real.sqrt a ≤ M) {t : ℕ} (ht : t ≤ a) :
    countError a M t ≤ Real.sqrt t / 10 + 1 / 100 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hta : (t : ℝ) ≤ a := by exact_mod_cast ht
  have hsa : 1 ≤ Real.sqrt a := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hpi := Real.pi_gt_three
  have hMpos : (0 : ℝ) < M := by nlinarith
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h1 : Real.sqrt ((t : ℝ) * ((a : ℝ) - t)) ≤ Real.sqrt t * Real.sqrt a := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (by nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
  have h2 : 8 * Real.pi * Real.sqrt ((t : ℝ) * ((a : ℝ) - t)) / M ≤ Real.sqrt t / 10 := by
    rw [div_le_iff₀ hMpos]
    calc 8 * Real.pi * Real.sqrt ((t : ℝ) * ((a : ℝ) - t))
        ≤ 8 * Real.pi * (Real.sqrt t * Real.sqrt a) := by gcongr
      _ = Real.sqrt t / 10 * (80 * Real.pi * Real.sqrt a) := by ring
      _ ≤ Real.sqrt t / 10 * M := by gcongr
  have h3 : 16 * Real.pi ^ 2 * a / (M : ℝ) ^ 2 ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (80 * Real.pi * Real.sqrt a) ^ 2 ≤ (M : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hM 2
    have hsq' : Real.sqrt (a : ℝ) ^ 2 = a := Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith [sq_nonneg Real.pi]
  unfold countError
  linarith


/-- Summing a pushforward over a predicate of the image. -/
private lemma lsc_sum_fiber {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β)
    (f : α → ℝ) (B : β → Prop) [DecidablePred B] :
    (∑ b, if B b then ∑ y ∈ Finset.univ.filter (fun y => g y = b), f y else 0)
      = ∑ y, if B (g y) then f y else 0 := by
  rw [← Finset.sum_fiberwise Finset.univ g (fun y => if B (g y) then f y else 0)]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.mp hy).2]
    simp only [hb, ite_true]
  · refine (Finset.sum_eq_zero fun y hy => ?_).symm
    rw [(Finset.mem_filter.mp hy).2]
    simp only [hb, ite_false]

/-- **The exponential-moment tail at base `5`**: if each run is bad with probability at most
`1/6`, the records with at least `t` bad runs, weighted by `5^t`, carry at most `(5/3)^k`. -/
private lemma lsc_tail {O : Type} [Fintype O] {k t : ℕ} (p : O → ℝ) (B : O → Prop)
    [DecidablePred B] (hp0 : ∀ o, 0 ≤ p o) (hp1 : ∑ o, p o = 1)
    (hpB : (∑ o, if B o then p o else 0) ≤ 1 / 6) :
    (∑ y ∈ Finset.univ.filter
        (fun y : Fin k → O => t ≤ (Finset.univ.filter fun i => B (y i)).card),
        ∏ i, p (y i)) * 5 ^ t ≤ (5 / 3) ^ k := by
  have hw0 : ∀ o, (0 : ℝ) ≤ if B o then 5 else 1 := fun o => by split_ifs <;> norm_num
  have hfactor : (∑ o, p o * (if B o then (5 : ℝ) else 1)) ≤ 5 / 3 := by
    have hsplit : ∀ o, p o * (if B o then (5 : ℝ) else 1) = p o + 4 * (if B o then p o else 0) :=
      fun o => by split_ifs <;> ring
    simp only [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp1]
    linarith
  have hstep : ∀ y ∈ Finset.univ.filter
      (fun y : Fin k → O => t ≤ (Finset.univ.filter fun i => B (y i)).card),
      (∏ i, p (y i)) * 5 ^ t ≤ ∏ i, p (y i) * (if B (y i) then (5 : ℝ) else 1) := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hy')
      (Finset.prod_nonneg fun i _ => hp0 _)
  calc (∑ y ∈ Finset.univ.filter
          (fun y : Fin k → O => t ≤ (Finset.univ.filter fun i => B (y i)).card),
          ∏ i, p (y i)) * 5 ^ t
      = ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → O => t ≤ (Finset.univ.filter fun i => B (y i)).card),
          (∏ i, p (y i)) * 5 ^ t := Finset.sum_mul _ _ _
    _ ≤ ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → O => t ≤ (Finset.univ.filter fun i => B (y i)).card),
          ∏ i, p (y i) * (if B (y i) then (5 : ℝ) else 1) := Finset.sum_le_sum hstep
    _ ≤ ∑ y : Fin k → O, ∏ i, p (y i) * (if B (y i) then (5 : ℝ) else 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun y _ _ => Finset.prod_nonneg fun i _ => mul_nonneg (hp0 _) (hw0 _)
    _ = ∏ _i : Fin k, ∑ o, p o * (if B o then (5 : ℝ) else 1) :=
        (Fintype.prod_sum fun (_ : Fin k) o => p o * (if B o then (5 : ℝ) else 1)).symm
    _ ≤ ∏ _i : Fin k, (5 / 3 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun o _ => mul_nonneg (hp0 o) (hw0 o))
          (fun _ _ => hfactor)
    _ = (5 / 3) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The point mass at `o` is realized with no queries. -/
private lemma lsc_realizes_ret {O : Type} [DecidableEq O] (o : O) :
    Realizes (id : (ι → Bool) → ι → Bool) 0 fun _ o' => if o' = o then (1 : ℝ) else 0 := by
  refine ⟨Unit, inferInstance, inferInstance, constAlg ι Bool o, fun a o' => ?_⟩
  simp only [QAlg.prob, constAlg]
  simp [eq_comm]

/-- The rounded estimate lies in `{0, …, a}`. -/
private lemma lsc_floor_lt (a M : ℕ) (y : Fin M) :
    ⌊countEstimate a M y + 1 / 2⌋₊ < a + 1 := by
  have h0 := aeEstimate_nonneg M y
  have h1 := aeEstimate_le_one M y
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  rw [Nat.floor_lt (by unfold countEstimate; positivity)]
  unfold countEstimate
  push_cast
  nlinarith

/-- The decoded count, rounded to the nearest integer. -/
private noncomputable def lsc_round (a M : ℕ) (y : Fin M) : Fin (a + 1) :=
  ⟨⌊countEstimate a M y + 1 / 2⌋₊, lsc_floor_lt a M y⟩

/-- Reading the marks through an enumeration of `S` counts the marked labels of `S`. -/
private lemma lsc_markedCount (S : Finset ι) (x : ι → Bool) :
    markedCount (x ∘ fun k => (S.equivFin.symm k : ι)) = (markedIn S x).card := by
  unfold markedCount markedIn
  refine Finset.card_nbij (fun k => (S.equivFin.symm k : ι)) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
    exact ⟨(S.equivFin.symm k).2, hk⟩
  · intro k₁ _ k₂ _ h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro i hi
    simp only [Finset.coe_filter] at hi
    exact ⟨S.equivFin ⟨i, hi.1⟩, by simpa using hi.2, by simp⟩

open Classical in
/-- **One rounded count** on the label set, with `2(M − 1)` queries: good with probability at
least `5/6`, and surely `0` when no label is marked. -/
private lemma lsc_base (S : Finset ι) :
    ∃ Q : (ι → Bool) → Fin (S.card + 1) → ℝ,
      Realizes (id : (ι → Bool) → ι → Bool) (2 * (labelCountClock S.card - 1)) Q ∧
      (∀ x, (markedIn S x).card = 0 → Q x 0 = 1) ∧
      ∀ x, 5 / 6 ≤ ∑ rh : Fin (S.card + 1),
        if CountGood (markedIn S x).card rh then Q x rh else 0 := by
  rcases Nat.eq_zero_or_pos S.card with ha | ha
  · -- no labels: return `0` with no queries
    have hS : S = ∅ := Finset.card_eq_zero.mp ha
    have hq : 2 * (labelCountClock S.card - 1) = 0 := by simp [labelCountClock, ha]
    refine ⟨fun _ o => if o = 0 then 1 else 0, by rw [hq]; exact lsc_realizes_ret 0,
      fun x _ => by simp, fun x => ?_⟩
    have hm : (markedIn S x).card = 0 := by simp [markedIn, hS]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    have hg : CountGood (markedIn S x).card ((0 : Fin (S.card + 1)) : ℕ) := by
      rw [hm, Fin.val_zero, lsc_countGood_iff]
      simp
    simp only [hg, ite_true]
    norm_num
  · set a := S.card with ha_def
    set M := labelCountClock a with hM_def
    have hM : 0 < M := Nat.succ_pos _
    have hMge : 80 * Real.pi * Real.sqrt a ≤ M := by
      rw [hM_def, labelCountClock]
      push_cast
      linarith [Nat.le_ceil (80 * Real.pi * Real.sqrt a)]
    set φ : Fin a → ι := fun k => (S.equivFin.symm k : ι) with hφ
    have hbase : Realizes (id : (Fin a → Bool) → Fin a → Bool) (countBudget M)
        (fun z y => (countAlg ha hM).prob z (countBudget M) y) :=
      ⟨_, inferInstance, inferInstance, countAlg ha hM, fun _ _ => rfl⟩
    have hre := (hbase.map (lsc_round a M)).reindex φ
    refine ⟨fun x o => ∑ y ∈ Finset.univ.filter (fun y => lsc_round a M y = o),
      (countAlg ha hM).prob (x ∘ φ) (countBudget M) y, hre, fun x hx => ?_, fun x => ?_⟩
    · -- nothing marked: the clock reads `0` surely, decoded and rounded to `0`
      have hc : markedCount (x ∘ φ) = 0 := by rw [hφ, lsc_markedCount]; exact hx
      have h0 : (searchSetup ha).succProb id Marked (x ∘ φ) = 0 := by
        rw [searchSetup_succProb, hc]
        simp
      have h1 := (searchSetup ha).aeAlg_prob_zero_of_succProb_eq_zero (searchSetup_marks ha)
        (x ∘ φ) hM h0
      rw [searchSetup_aeRoutine_len] at h1
      have hr0 : lsc_round a M ⟨0, hM⟩ = 0 := by
        ext
        norm_num [lsc_round, countEstimate, AmpSetup.aeEstimate_zero hM]
      apply le_antisymm
      · calc _ ≤ ∑ y, (countAlg ha hM).prob (x ∘ φ) (countBudget M) y :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun y _ _ => QAlg.prob_nonneg _ _ _ _
          _ = 1 := QAlg.sum_prob _ _ _
      · calc (1 : ℝ) = (countAlg ha hM).prob (x ∘ φ) (countBudget M) ⟨0, hM⟩ := h1.symm
          _ ≤ _ := Finset.single_le_sum (f := fun y => (countAlg ha hM).prob (x ∘ φ)
              (countBudget M) y) (fun y _ => QAlg.prob_nonneg _ _ _ _)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩)
    · -- accuracy: an accurate decoded count rounds to a good estimate
      have hc := lsc_markedCount S x
      have hta : markedCount (x ∘ φ) ≤ a :=
        (Finset.card_filter_le _ _).trans (by simp)
      rw [lsc_sum_fiber]
      refine (five_sixths_le_count_accurate ha hM (x ∘ φ)).trans
        (Finset.sum_le_sum fun y _ => ?_)
      split_ifs with hacc hg hg
      · exact le_rfl
      · exfalso
        apply hg
        have hgood := lsc_round_good (markedCount (x ∘ φ))
          (mul_nonneg (Nat.cast_nonneg _) (aeEstimate_nonneg _ _))
          (hacc.trans (lsc_countError_le ha hMge hta))
        rw [← hc]
        exact hgood
      · exact QAlg.prob_nonneg _ _ _ _
      · exact le_rfl

/-- `(2/3)^j / 3 ≤ ε` for `j = labelCountReps ε`. -/
private lemma lsc_reps_le {ε : ℝ} (hε0 : 0 < ε) :
    (2 / 3 : ℝ) ^ labelCountReps ε / 3 ≤ ε := by
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hj : Real.log (1 / ε) ≤ labelCountReps ε * Real.log (3 / 2) := by
    have := Nat.le_ceil (Real.log (1 / ε) / Real.log (3 / 2))
    rwa [div_le_iff₀ hlog] at this
  have h32 : 1 / ε ≤ (3 / 2 : ℝ) ^ labelCountReps ε := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow]
    exact hj
  have hpow : (2 / 3 : ℝ) ^ labelCountReps ε = 1 / (3 / 2) ^ labelCountReps ε := by
    rw [one_div, ← inv_pow]
    norm_num
  rw [div_le_iff₀ hε0] at h32
  rw [hpow, div_div, div_le_iff₀ (by positivity)]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3 / 2) (labelCountReps ε)]

open Classical in
/-- **Counting** [CGKLPZ26, Lemma 2.4]: an estimate in `{0, …, a}` that is good except with
probability `ε`, and surely `0` when no label is marked. -/
theorem exists_count (S : Finset ι) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ P : (ι → Bool) → Fin (S.card + 1) → ℝ,
      Realizes (id : (ι → Bool) → ι → Bool) (labelCountBudget S.card ε) P ∧
      (∀ x, (markedIn S x).card = 0 → P x 0 = 1) ∧
      ∀ x, 1 - ε ≤ ∑ rh : Fin (S.card + 1),
        if CountGood (markedIn S x).card rh then P x rh else 0 := by
  obtain ⟨Q, hQ, hQ0, hQg⟩ := lsc_base S
  obtain ⟨P, hP, hP0, hPg⟩ := hQ.median_pointMass (fun x rh => CountGood (markedIn S x).card rh)
    (fun x a b c ha hc hab hbc => lsc_countGood_convex _ _ _ _ ha hc hab hbc) hQg
    (labelCountReps ε)
  refine ⟨P, hP, fun x hx => hP0 x 0 (hQ0 x hx), fun x => ?_⟩
  linarith [hPg x, lsc_reps_le hε0]

/-! ## Batches of samples -/

/-- Grover iterations per trial: `⌈√(2a/r̂)⌉`. -/
noncomputable def sampleIters (a rh : ℕ) : ℕ := ⌈Real.sqrt (2 * a / rh)⌉₊

/-- The number of trials for `s` samples with failure probability `ε`. -/
noncomputable def sampleTrials (s : ℕ) (ε : ℝ) : ℕ :=
  4 * s + 2 * ⌈Real.log (1 / ε) / Real.log (9 / 4)⌉₊

/-- **The sampling budget**, fixed by `a`, `r̂`, `s` and `ε`; zero when `r̂ = 0`. -/
noncomputable def sampleBudget (a rh s : ℕ) (ε : ℝ) : ℕ :=
  if rh = 0 then 0 else sampleTrials s ε * (8 * sampleIters a rh)

/-! ## Collecting the first `s` successes of independent trials -/

section Collect

variable {α : Type}

/-- The first `s` successes (`some` entries) of a record of `T` trials, in order, or `none` if
there are fewer than `s`. -/
private def lss_collect : (s T : ℕ) → (Fin T → Option α) → Option (Fin s → α)
  | 0, _, _ => some Fin.elim0
  | _ + 1, 0, _ => none
  | s + 1, T + 1, y =>
    match y 0 with
    | some k => (lss_collect s T (Fin.tail y)).map fun w => (Fin.cons k w : Fin (s + 1) → α)
    | none => lss_collect (s + 1) T (Fin.tail y)

/-- A leading success is the first collected label. -/
private lemma lss_collect_cons_some (s T : ℕ) (k : α) (t : Fin T → Option α) :
    lss_collect (s + 1) (T + 1) (Fin.cons (some k) t : Fin (T + 1) → Option α) =
      (lss_collect s T t).map fun w => (Fin.cons k w : Fin (s + 1) → α) := by
  simp [lss_collect]

/-- A leading failure is skipped. -/
private lemma lss_collect_cons_none (s T : ℕ) (t : Fin T → Option α) :
    lss_collect (s + 1) (T + 1) (Fin.cons none t : Fin (T + 1) → Option α) =
      lss_collect (s + 1) T t := by
  simp [lss_collect]

/-- Prepending `k` gives `w` exactly when `k` is the head of `w` and the rest its tail. -/
private lemma lss_map_cons_eq_some {s : ℕ} (k : α) (o : Option (Fin s → α))
    (w : Fin (s + 1) → α) :
    (o.map fun v => (Fin.cons k v : Fin (s + 1) → α)) = some w ↔
      k = w 0 ∧ o = some (Fin.tail w) := by
  rcases o with _ | v
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      simp
    · rintro ⟨rfl, rfl⟩
      exact Fin.cons_self_tail w

/-- Summing over records of `T + 1` trials: the first trial, then the rest. -/
private lemma lss_sum_cons {O : Type} [Fintype O] (T : ℕ) (f : (Fin (T + 1) → O) → ℝ) :
    ∑ y, f y = ∑ o, ∑ t : Fin T → O, f (Fin.cons o t) := by
  classical
  rw [← (consEquiv O T).sum_comp, Fintype.sum_prod_type]
  rfl

variable [Fintype α] [DecidableEq α]

/-- The law of the collected outcome when the `T` trials are independent with law `p`. -/
private noncomputable def lss_law (p : Option α → ℝ) (s T : ℕ) (w : Option (Fin s → α)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin T → Option α => lss_collect s T y = w), ∏ j, p (y j)

/-- The law as a sum over all records. -/
private lemma lss_law_eq (p : Option α → ℝ) (s T : ℕ) (w : Option (Fin s → α)) :
    lss_law p s T w =
      ∑ y : Fin T → Option α, if lss_collect s T y = w then ∏ j, p (y j) else 0 :=
  Finset.sum_filter _ _

/-- The total mass of the law. -/
private lemma lss_law_sum (p : Option α → ℝ) (s T : ℕ) :
    ∑ w, lss_law p s T w = (∑ o, p o) ^ T := by
  rw [Fintype.sum_pow]
  exact Finset.sum_fiberwise _ _ _

/-- No sample is needed: always collected. -/
private lemma lss_law_zero_some (p : Option α → ℝ) (T : ℕ) (w : Fin 0 → α) :
    lss_law p 0 T (some w) = (∑ o, p o) ^ T := by
  rw [lss_law_eq, Fintype.sum_pow]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h : lss_collect 0 T y = some w := by
    simp only [lss_collect]
    exact congrArg some (Subsingleton.elim _ _)
  simp [h]

/-- No sample is needed: never a failure. -/
private lemma lss_law_zero_none (p : Option α → ℝ) (T : ℕ) : lss_law p 0 T none = 0 := by
  rw [lss_law_eq]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp [lss_collect]

/-- No trial left but a sample needed: failure. -/
private lemma lss_law_succ_zero (p : Option α → ℝ) (s : ℕ) (w : Option (Fin (s + 1) → α)) :
    lss_law p (s + 1) 0 w = if w = none then 1 else 0 := by
  rw [lss_law_eq, Fintype.sum_unique]
  rcases w with _ | w <;> simp [lss_collect]

/-- The recursion of the law of a batch, by the first trial. -/
private lemma lss_law_succ_succ_some (p : Option α → ℝ) (s T : ℕ) (w : Fin (s + 1) → α) :
    lss_law p (s + 1) (T + 1) (some w) =
      p none * lss_law p (s + 1) T (some w) +
        p (some (w 0)) * lss_law p s T (some (Fin.tail w)) := by
  rw [lss_law_eq, lss_sum_cons, Fintype.sum_option, lss_law_eq, lss_law_eq, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [lss_collect_cons_none, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_ite, mul_zero]
  · rw [Finset.sum_eq_single (w 0)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lss_collect_cons_some, lss_map_cons_eq_some, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, true_and, mul_ite, mul_zero]
    · intro k _ hk
      refine Finset.sum_eq_zero fun t _ => ?_
      simp only [lss_collect_cons_some, lss_map_cons_eq_some, hk, false_and, ite_false]
    · simp

/-- The recursion of the failure probability, by the first trial. -/
private lemma lss_law_succ_succ_none (p : Option α → ℝ) (s T : ℕ) :
    lss_law p (s + 1) (T + 1) none =
      p none * lss_law p (s + 1) T none + (∑ k, p (some k)) * lss_law p s T none := by
  rw [lss_law_eq, lss_sum_cons, Fintype.sum_option, lss_law_eq, lss_law_eq, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [lss_collect_cons_none, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_ite, mul_zero]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [lss_collect_cons_some, Option.map_eq_none_iff, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, mul_ite, mul_zero]

/-- **The product form**: a batch `w` has probability `G · ∏ᵢ p(some wᵢ)`, with `G` independent
of `w`. -/
private lemma lss_law_some_eq (p : Option α → ℝ) :
    ∀ T s, ∃ G : ℝ, ∀ w : Fin s → α, lss_law p s T (some w) = G * ∏ i, p (some (w i)) := by
  intro T
  induction T with
  | zero =>
    intro s
    rcases s with _ | s
    · exact ⟨(∑ o, p o) ^ 0, fun w => by rw [lss_law_zero_some]; simp⟩
    · exact ⟨0, fun w => by rw [lss_law_succ_zero]; simp⟩
  | succ T ih =>
    intro s
    rcases s with _ | s
    · exact ⟨(∑ o, p o) ^ (T + 1), fun w => by rw [lss_law_zero_some]; simp⟩
    · obtain ⟨G₁, h₁⟩ := ih (s + 1)
      obtain ⟨G₂, h₂⟩ := ih s
      refine ⟨p none * G₁ + G₂, fun w => ?_⟩
      rw [lss_law_succ_succ_some, h₁, h₂, Fin.prod_univ_succ (fun i => p (some (w i)))]
      simp only [Fin.tail]
      ring

/-- **The exact law of a batch**: the samples are independent with law `c`, given success, if
each trial succeeds with label `i` with probability `(1 − p none) · c i`. -/
private lemma lss_law_some_formula (p : Option α → ℝ) (hp1 : ∑ o, p o = 1) (c : α → ℝ)
    (hc : ∀ i, p (some i) = (1 - p none) * c i) (s T : ℕ) (y : Fin s → α) :
    lss_law p s T (some y) = (1 - lss_law p s T none) * ∏ j, c (y j) := by
  obtain ⟨G, hG⟩ := lss_law_some_eq p T s
  have hsum := lss_law_sum p s T
  rw [hp1, one_pow, Fintype.sum_option] at hsum
  have hβ : ∑ i, p (some i) = 1 - p none := by
    rw [Fintype.sum_option] at hp1
    linarith
  have h1 : 1 - lss_law p s T none = G * (1 - p none) ^ s := by
    rw [← hβ, Fintype.sum_pow, Finset.mul_sum]
    simp_rw [← hG]
    linarith
  rw [hG, h1]
  simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The failure tail**, by the exponential moment `E[2^{#failures}] = (1 + p none)^T`. -/
private lemma lss_law_none_le (p : Option α → ℝ) (hp0 : ∀ o, 0 ≤ p o) (hp1 : ∑ o, p o = 1) :
    ∀ T s, lss_law p s T none * 2 ^ (T + 1) ≤ (1 + p none) ^ T * 2 ^ s := by
  have hβ : ∑ k, p (some k) = 1 - p none := by
    rw [Fintype.sum_option] at hp1
    linarith
  have hβ0 : 0 ≤ 1 - p none := hβ ▸ Finset.sum_nonneg fun k _ => hp0 _
  have hpos : ∀ T s, (0 : ℝ) ≤ (1 + p none) ^ T * 2 ^ s := fun T s =>
    mul_nonneg (pow_nonneg (by linarith [hp0 none]) _) (by positivity)
  intro T
  induction T with
  | zero =>
    intro s
    rcases s with _ | s
    · rw [lss_law_zero_none, zero_mul]
      exact hpos _ _
    · rw [lss_law_succ_zero]
      simp only [ite_true, zero_add, pow_one, pow_zero, one_mul]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  | succ T ih =>
    intro s
    rcases s with _ | s
    · rw [lss_law_zero_none, zero_mul]
      exact hpos _ _
    · rw [lss_law_succ_succ_none, hβ]
      have h₁ := mul_le_mul_of_nonneg_left (ih (s + 1)) (hp0 none)
      have h₂ := mul_le_mul_of_nonneg_left (ih s) hβ0
      rw [pow_succ 2 (T + 1), pow_succ (1 + p none) T, pow_succ 2 s]
      rw [pow_succ 2 s] at h₁
      nlinarith

end Collect

/-! ## One Grover trial on the labels of `S` -/

/-- The labels of `S`, enumerated by `Fin S.card`. -/
private noncomputable def lss_enum (S : Finset ι) (k : Fin S.card) : ι := (S.equivFin.symm k : ι)

/-- The enumeration is injective. -/
private lemma lss_enum_injective (S : Finset ι) : Function.Injective (lss_enum S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

/-- The enumeration lands in `S`. -/
private lemma lss_enum_mem (S : Finset ι) (k : Fin S.card) : lss_enum S k ∈ S :=
  (S.equivFin.symm k).2

/-- The enumeration reaches every label of `S`. -/
private lemma lss_enum_equivFin (S : Finset ι) {i : ι} (hi : i ∈ S) :
    lss_enum S (S.equivFin ⟨i, hi⟩) = i := by
  simp [lss_enum]

/-- The marks of the enumerated labels are the marked labels of `S`. -/
private lemma lss_markedCount (S : Finset ι) (x : ι → Bool) :
    markedCount (x ∘ lss_enum S) = (markedIn S x).card := by
  rw [markedCount, markedIn]
  refine Finset.card_bij (fun k _ => lss_enum S k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
    exact ⟨lss_enum_mem S k, hk⟩
  · intro k₁ _ k₂ _ h
    exact lss_enum_injective S h
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨S.equivFin ⟨i, hi.1⟩, ?_, lss_enum_equivFin S hi.1⟩
    simp [lss_enum_equivFin S hi.1, hi.2]

set_option synthInstance.maxSize 100000 in
/-- **One trial**: Grover search on the enumerated labels, read as an optional label. -/
private noncomputable def lss_trial (S : Finset ι) {m : ℕ} (ha : 0 < S.card) (hm : 0 < m)
    (x : ι → Bool) (o' : Option ι) : ℝ :=
  ∑ o ∈ Finset.univ.filter (fun o => Option.map (lss_enum S) o = o'),
    (searchAlg ha m hm).prob (x ∘ lss_enum S) (searchBudget m) o

set_option synthInstance.maxSize 100000 in
/-- A trial is realized with the search budget. -/
private lemma lss_trial_realizes (S : Finset ι) {m : ℕ} (ha : 0 < S.card) (hm : 0 < m) :
    Realizes (id : (ι → Bool) → ι → Bool) (searchBudget m) (lss_trial S ha hm) := by
  have hsearch : Realizes (id : (Fin S.card → Bool) → Fin S.card → Bool) (searchBudget m)
      (fun z o => (searchAlg ha m hm).prob z (searchBudget m) o) :=
    ⟨_, inferInstance, inferInstance, searchAlg ha m hm, fun _ _ => rfl⟩
  exact (hsearch.reindex (lss_enum S)).map (Option.map (lss_enum S))

/-- A realized law has total mass one. -/
private lemma lss_realizes_sum {X O : Type} [Fintype X] [Fintype O] [DecidableEq O]
    {read : X → ι → Bool} {q : ℕ} {P : X → O → ℝ} (h : Realizes read q P) (x : X) :
    ∑ o, P x o = 1 := by
  obtain ⟨W, _, _, A, hA⟩ := h
  simp_rw [← hA x]
  exact A.sum_prob _ _

set_option synthInstance.maxSize 100000 in
/-- A trial fails exactly when the search fails. -/
private lemma lss_trial_none (S : Finset ι) {m : ℕ} (ha : 0 < S.card) (hm : 0 < m)
    (x : ι → Bool) :
    lss_trial S ha hm x none = (searchAlg ha m hm).prob (x ∘ lss_enum S) (searchBudget m) none := by
  have hfilt : Finset.univ.filter (fun o => Option.map (lss_enum S) o = none) = {none} := by
    ext o
    simp
  rw [lss_trial, hfilt, Finset.sum_singleton]

set_option synthInstance.maxSize 100000 in
/-- **A successful trial is uniform over the marked labels.** -/
private lemma lss_trial_some (S : Finset ι) {m : ℕ} (ha : 0 < S.card) (hm : 0 < m)
    (x : ι → Bool) (i : ι) :
    lss_trial S ha hm x (some i) = if i ∈ markedIn S x then
      (1 - lss_trial S ha hm x none) / (markedIn S x).card else 0 := by
  rw [lss_trial_none]
  by_cases hi : i ∈ S
  · have hk : lss_enum S (S.equivFin ⟨i, hi⟩) = i := lss_enum_equivFin S hi
    have hfilt : Finset.univ.filter (fun o => Option.map (lss_enum S) o = some i) =
        {some (S.equivFin ⟨i, hi⟩)} := by
      ext o
      rcases o with _ | o
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.map_some,
          Option.some.injEq, Finset.mem_singleton]
        constructor
        · intro h
          exact lss_enum_injective S (h.trans hk.symm)
        · rintro rfl
          exact hk
    rw [lss_trial, hfilt, Finset.sum_singleton]
    by_cases hxi : x i = true
    · have hmem : i ∈ markedIn S x := by simp [markedIn, hi, hxi]
      simp only [hmem, ite_true]
      have hr := markedCount_mul_searchAlg_prob_some ha hm (x ∘ lss_enum S)
        (i := S.equivFin ⟨i, hi⟩) (by simp [hk, hxi])
      rw [lss_markedCount, searchReturnProb] at hr
      have hr0 : ((markedIn S x).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr ⟨i, hmem⟩).ne'
      rw [eq_div_iff hr0]
      linarith
    · have hmem : i ∉ markedIn S x := by simp [markedIn, hxi]
      simp only [hmem, ite_false]
      exact searchAlg_prob_some_of_unmarked ha hm (x ∘ lss_enum S) (by simpa [hk] using hxi)
  · have hmem : i ∉ markedIn S x := by simp [markedIn, hi]
    have hfilt : Finset.univ.filter (fun o => Option.map (lss_enum S) o = some i) = ∅ := by
      ext o
      rcases o with _ | o
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.map_some,
          Option.some.injEq, Finset.notMem_empty, iff_false]
        intro h
        exact hi (h ▸ lss_enum_mem S o)
    rw [lss_trial, hfilt, Finset.sum_empty]
    simp only [hmem, ite_false]

set_option synthInstance.maxSize 100000 in
/-- **A trial succeeds with probability at least `2/3`** when `r̂ ≤ 2r`. -/
private lemma lss_trial_none_le (S : Finset ι) {rh : ℕ} (ha : 0 < S.card)
    (hm : 0 < sampleIters S.card rh) (x : ι → Bool) (hrh : 0 < rh)
    (hr : rh ≤ 2 * (markedIn S x).card) : lss_trial S ha hm x none ≤ 1 / 3 := by
  rw [lss_trial_none]
  have hr0 : 0 < (markedIn S x).card := by omega
  have hrh' : (0 : ℝ) < rh := by exact_mod_cast hrh
  have ha' : (0 : ℝ) < S.card := by exact_mod_cast ha
  have hr' : (0 : ℝ) < (markedIn S x).card := by exact_mod_cast hr0
  have hmp : 1 ≤ (sampleIters S.card rh : ℝ) *
      Real.sqrt (((markedIn S x).card : ℝ) / S.card) := by
    have h1 : Real.sqrt (2 * S.card / rh) ≤ sampleIters S.card rh := Nat.le_ceil _
    have h2 : 1 ≤ Real.sqrt (2 * S.card / rh) *
        Real.sqrt (((markedIn S x).card : ℝ) / S.card) := by
      rw [← Real.sqrt_mul (by positivity)]
      have he : 2 * (S.card : ℝ) / rh * ((markedIn S x).card / S.card) =
          2 * (markedIn S x).card / rh := by
        field_simp
      have hle : (1 : ℝ) ≤ 2 * (markedIn S x).card / rh := by
        rw [le_div_iff₀ hrh', one_mul]
        exact_mod_cast hr
      rw [he]
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ _ := Real.sqrt_le_sqrt hle
    calc (1 : ℝ) ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  have h := two_thirds_le_searchReturnProb ha hm (x ∘ lss_enum S) hr0
    (lss_markedCount S x).ge hmp
  rw [searchReturnProb] at h
  linarith

/-! ## Arithmetic of the trial count -/

/-- `(4/9)^j ≤ ε` for `j = ⌈ln(1/ε)/ln(9/4)⌉`. -/
private lemma lss_pow_le {ε : ℝ} (hε0 : 0 < ε) :
    (4 / 9 : ℝ) ^ ⌈Real.log (1 / ε) / Real.log (9 / 4)⌉₊ ≤ ε := by
  set j := ⌈Real.log (1 / ε) / Real.log (9 / 4)⌉₊
  have hl : 0 < Real.log (9 / 4) := Real.log_pos (by norm_num)
  have hj : Real.log (1 / ε) ≤ j * Real.log (9 / 4) := by
    rw [← div_le_iff₀ hl]
    exact Nat.le_ceil _
  have h1 : 1 / ε ≤ (9 / 4 : ℝ) ^ j := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow]
    exact hj
  have he : (4 / 9 : ℝ) ^ j = 1 / (9 / 4 : ℝ) ^ j := by
    rw [div_pow, div_pow, one_div_div]
  rw [div_le_iff₀ hε0] at h1
  rw [he, div_le_iff₀ (by positivity)]
  linarith

/-- **The failure tail of the trial count**: `(4/3)^T · 2^s ≤ ε · 2^(T+1)`. -/
private lemma lss_tail_le (s : ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    (4 / 3 : ℝ) ^ sampleTrials s ε * 2 ^ s ≤ ε * 2 ^ (sampleTrials s ε + 1) := by
  set j := ⌈Real.log (1 / ε) / Real.log (9 / 4)⌉₊
  have hj := lss_pow_le hε0
  rw [show sampleTrials s ε = 4 * s + 2 * j from rfl]
  have hA : ((4 / 3 : ℝ) ^ 4 * 2) ^ s ≤ ((2 : ℝ) ^ 4) ^ s :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) s
  have hB : ((4 / 3 : ℝ) ^ 2) ^ j ≤ ε * ((2 : ℝ) ^ 2) ^ j := by
    rw [show (4 / 3 : ℝ) ^ 2 = 2 ^ 2 * (4 / 9) by norm_num, mul_pow, mul_comm ε]
    exact mul_le_mul_of_nonneg_left hj (by positivity)
  calc (4 / 3 : ℝ) ^ (4 * s + 2 * j) * 2 ^ s
      = ((4 / 3 : ℝ) ^ 4 * 2) ^ s * ((4 / 3 : ℝ) ^ 2) ^ j := by
        rw [pow_add, pow_mul, pow_mul, mul_pow]
        ring
    _ ≤ ((2 : ℝ) ^ 4) ^ s * (ε * ((2 : ℝ) ^ 2) ^ j) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ ≤ ε * 2 ^ (4 * s + 2 * j + 1) := by
        rw [pow_succ 2 (4 * s + 2 * j), pow_add, pow_mul, pow_mul]
        nlinarith [show (0 : ℝ) ≤ ε * ((2 : ℝ) ^ 4) ^ s * ((2 : ℝ) ^ 2) ^ j by positivity]

/-- The constant `none` algorithm, with no query. -/
private lemma lss_realizes_none (s : ℕ) :
    Realizes (id : (ι → Bool) → ι → Bool) 0
      (fun _ (w : Option (Fin s → ι)) => if w = none then (1 : ℝ) else 0) := by
  refine ⟨Unit, inferInstance, inferInstance, constAlg ι Bool (none : Option (Fin s → ι)), ?_⟩
  intro x w
  rcases w with _ | w <;> simp [QAlg.prob, constAlg]

/-- With `r̂ > 0` and a nonempty `S`, each trial runs at least one Grover iteration. -/
private lemma lss_sampleIters_pos {a rh : ℕ} (ha : 0 < a) (hrh : 0 < rh) : 0 < sampleIters a rh :=
  Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (div_pos (mul_pos two_pos (Nat.cast_pos.mpr ha))
    (Nat.cast_pos.mpr hrh)))

/-- **The sampling budget is `O((s + 1 + log(1/ε)) √(a/r̂))`.** -/
theorem sampleBudget_le {a rh : ℕ} (s : ℕ) (hr0 : 0 < rh) (hra : rh ≤ a) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    (sampleBudget a rh s ε : ℝ) ≤ 80 * (s + 1 + Real.log (1 / ε)) * Real.sqrt (a / rh) := by
  have hrh0 : rh ≠ 0 := hr0.ne'
  simp only [sampleBudget, hrh0, ite_false, sampleTrials, sampleIters]
  push_cast
  set L := Real.log (1 / ε) with hL_def
  set u := Real.sqrt (a / rh) with hu_def
  have hrr : (0 : ℝ) < rh := by exact_mod_cast hr0
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  have hu1 : 1 ≤ u := by
    have h : (1 : ℝ) ≤ a / rh := by
      rw [le_div_iff₀ hrr, one_mul]
      exact_mod_cast hra
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ u := Real.sqrt_le_sqrt h
  have hj : (⌈L / Real.log (9 / 4)⌉₊ : ℝ) ≤ 2 * L + 1 := by
    have hl : 1 / 2 ≤ Real.log (9 / 4) := by
      have := Real.one_sub_inv_le_log_of_pos (x := 9 / 4) (by norm_num)
      norm_num at this ⊢
      linarith
    have h1 := Nat.ceil_lt_add_one (div_nonneg hL (by linarith) : 0 ≤ L / Real.log (9 / 4))
    have h2 : L / Real.log (9 / 4) ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hm : (⌈Real.sqrt (2 * a / rh)⌉₊ : ℝ) ≤ 5 / 2 * u := by
    have h1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * a / rh))
    have h2 : Real.sqrt (2 * a / rh) = Real.sqrt 2 * u := by
      rw [mul_div_assoc, Real.sqrt_mul (by norm_num)]
    have h3 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    nlinarith
  calc (4 * (s : ℝ) + 2 * ⌈L / Real.log (9 / 4)⌉₊) * (8 * ⌈Real.sqrt (2 * a / rh)⌉₊)
      ≤ (4 * (s : ℝ) + 2 * (2 * L + 1)) * (8 * (5 / 2 * u)) := by gcongr
    _ ≤ 80 * (s + 1 + L) * u := by nlinarith

/-- **Samples** [CGKLPZ26, Lemma 2.4]: with a fixed budget, either failure (`none`) or `s` labels
that, whatever `r̂`, are independent and uniform over the marked labels given success; if
`0 < r̂ ≤ 2r`, failure has probability at most `ε`. The budget is at most
`80 (s + 1 + ln(1/ε)) √(a/r̂)` when `0 < r̂ ≤ a` (`sampleBudget_le`). -/
theorem exists_sample (S : Finset ι) (rh s : ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ P : (ι → Bool) → Option (Fin s → ι) → ℝ,
      Realizes (id : (ι → Bool) → ι → Bool) (sampleBudget S.card rh s ε) P ∧
      (∀ x y, P x (some y) = (1 - P x none) *
        ∏ j, if y j ∈ markedIn S x then 1 / ((markedIn S x).card : ℝ) else 0) ∧
      ∀ x, 0 < rh → rh ≤ 2 * (markedIn S x).card → P x none ≤ ε := by
  by_cases h0 : rh = 0 ∨ S.card = 0
  · refine ⟨fun _ w => if w = none then 1 else 0, ?_, fun x y => by simp, fun x hrh hr => ?_⟩
    · have hb : sampleBudget S.card rh s ε = 0 := by
        rcases h0 with h | h
        · simp [sampleBudget, h]
        · simp [sampleBudget, sampleIters, h]
      rw [hb]
      exact lss_realizes_none s
    · have hcard : (markedIn S x).card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
      omega
  · push Not at h0
    obtain ⟨hrh0, ha0⟩ := h0
    have ha : 0 < S.card := Nat.pos_of_ne_zero ha0
    have hrh : 0 < rh := Nat.pos_of_ne_zero hrh0
    have hm : 0 < sampleIters S.card rh := lss_sampleIters_pos ha hrh
    have hfold := Realizes.foldRec (sampleTrials s ε)
      (fun _ => searchBudget (sampleIters S.card rh)) (fun _ => lss_trial S ha hm)
      (fun _ => lss_trial_realizes S ha hm)
    have hq : (∑ _j : Fin (sampleTrials s ε), searchBudget (sampleIters S.card rh)) =
        sampleBudget S.card rh s ε := by
      simp [sampleBudget, hrh0, searchBudget]
    rw [hq] at hfold
    refine ⟨fun x w => lss_law (lss_trial S ha hm x) s (sampleTrials s ε) w,
      (hfold.map (lss_collect s (sampleTrials s ε))).congr fun x w => rfl, fun x y => ?_,
      fun x _ hr => ?_⟩
    · have hp1 := lss_realizes_sum (lss_trial_realizes S ha hm) x
      refine lss_law_some_formula (c := fun i =>
        if i ∈ markedIn S x then 1 / ((markedIn S x).card : ℝ) else 0) _ hp1 (fun i => ?_) _ _ y
      rw [lss_trial_some]
      split_ifs <;> ring
    · have hp0 := (lss_trial_realizes S ha hm).nonneg x
      have hp1 := lss_realizes_sum (lss_trial_realizes S ha hm) x
      have h := lss_law_none_le _ hp0 hp1 (sampleTrials s ε) s
      have h3 := lss_trial_none_le S ha hm x hrh hr
      have h4 : (1 + lss_trial S ha hm x none) ^ sampleTrials s ε ≤
          (4 / 3 : ℝ) ^ sampleTrials s ε :=
        pow_le_pow_left₀ (by linarith [hp0 none]) (by linarith) _
      have h5 := lss_tail_le s hε0
      have h6 : lss_law (lss_trial S ha hm x) s (sampleTrials s ε) none *
          2 ^ (sampleTrials s ε + 1) ≤ ε * 2 ^ (sampleTrials s ε + 1) :=
        h.trans ((mul_le_mul_of_nonneg_right h4 (by positivity)).trans h5)
      exact le_of_mul_le_mul_right h6 (by positivity)

end QuantumQueryComplexity
