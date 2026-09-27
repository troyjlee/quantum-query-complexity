import QuantumQueryComplexity.Quantum.Amplitude.Randomized
import QuantumQueryComplexity.Quantum.Amplitude.FirstSuccess
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 1000000
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Amplitude amplification: the public, fixed-budget theorem

From a setup `P` (preparation `S` queries, marker `C` queries) and a number `m ≥ 1` of
iteration counts, `P.amplified m` is an **actual algorithm** with output `Option O`:

    four independent randomized verified trials, the first flagged candidate returned.

Its budget is `P.amplifiedBudget m = 4·(S + (m−1)(2S+C) + C) ≤ 4·m·(2S+C)`, and with
`m = ampIterations p₀ = ⌈1/√p₀⌉` this is at most `16·(S+C)/√p₀`.

For every promise input `x`, with `pₓ = P.succProb read Good x` and any marker that marks the
prepared states (`P.Marks read Good`):

* `amplified_prob_some_of_not_good`: an invalid candidate is **never** returned;
* `two_thirds_le_returnProb`: if `pₓ ≥ p₀` (and `m·√p₀ ≥ 1`), a candidate is returned with
  probability at least `2/3` — pointwise in `x`, so inputs without any solution are allowed;
* `amplified_prob_none_of_succProb_eq_zero`: if `pₓ = 0`, the output is `none` surely;
* `succProb_mul_amplified_prob_some`: the conditional law survives the random iteration
  count, the padding/mixture and the first-success selection:

      pₓ · Pr[B(x) = some y] = Pr[B(x) ≠ none] · (if Good x y then Pr[A(x) = y] else 0);

* `amplified_cond_law`: the divided form, for `pₓ > 0` and `Pr[B(x) ≠ none] > 0`;
* `solvesWithErrorOn_amplified`: under `∀ x, p₀ ≤ pₓ`, the relation accepting exactly the
  valid `some y` is solved with error `1/3`.

A `none` on an input with `pₓ > 0` is not a certificate that no solution exists.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X] [Fintype O] [DecidableEq O]

namespace AmpSetup

variable (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

/-- The original probability of `y`, counted only if `y` is valid. -/
noncomputable def goodWeight (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (y : O) : ℝ :=
  if Good x y then P.origAlg.prob (read x) P.prep.len y else 0

lemma sum_goodWeight (x : X) : ∑ y, P.goodWeight read Good x y = P.succProb read Good x := by
  rw [succProb, goodProb_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [goodWeight, QAlg.prob, origAlg_state]
  rfl

lemma goodWeight_nonneg (x : X) (y : O) : 0 ≤ P.goodWeight read Good x y := by
  rw [goodWeight]; split_ifs
  · exact QAlg.prob_nonneg _ _ _ _
  · exact le_rfl

/-! ## One randomized trial: the failure probability -/

/-- The failure probability of one randomized trial is `1 − c·pₓ`. -/
theorem randTrial_prob_none (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) :
    (P.randTrial m hm).prob (read x) (P.trialBudget m) none
      = 1 - P.randWeight read Good x m * P.succProb read Good x := by
  have hsum := QAlg.sum_prob (P.randTrial m hm) (read x) (P.trialBudget m)
  rw [Fintype.sum_option] at hsum
  have hs : (∑ y, (P.randTrial m hm).prob (read x) (P.trialBudget m) (some y))
      = P.randWeight read Good x m * P.succProb read Good x := by
    rw [← sum_goodWeight, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => P.randTrial_prob_some hP x hm y
  rw [hs] at hsum
  linarith

/-! ## Four trials, first success -/

/-- Two randomized trials, first success. -/
noncomputable def twoTrials (m : ℕ) (hm : 0 < m) :=
  QAlg.orElse (P.randTrial m hm) (P.trialBudget m) (P.randTrial m hm) (P.trialBudget m)

/-- **The amplified algorithm**: four randomized verified trials, first success. -/
noncomputable def amplified (m : ℕ) (hm : 0 < m) :=
  QAlg.orElse (P.twoTrials m hm) (P.trialBudget m + P.trialBudget m)
    (P.twoTrials m hm) (P.trialBudget m + P.trialBudget m)

/-- The query budget of the amplified algorithm. -/
def amplifiedBudget (m : ℕ) : ℕ :=
  (P.trialBudget m + P.trialBudget m) + (P.trialBudget m + P.trialBudget m)

lemma amplifiedBudget_eq (m : ℕ) : P.amplifiedBudget m = 4 * P.trialBudget m := by
  rw [amplifiedBudget]; omega

/-- **`budget ≤ 4·m·(2S+C)`.** -/
theorem amplifiedBudget_le (m : ℕ) (hm : 0 < m) :
    P.amplifiedBudget m ≤ 4 * (m * (2 * P.prep.len + P.mark.len)) := by
  rw [amplifiedBudget_eq]
  exact Nat.mul_le_mul_left 4 (P.trialBudget_le m hm)

/-- The failure probability `n = 1 − c·pₓ` of one trial. -/
noncomputable def trialFail (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (m : ℕ) : ℝ :=
  1 - P.randWeight read Good x m * P.succProb read Good x

/-- **The exact law of the amplified algorithm on candidates.** -/
theorem amplified_prob_some (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) (y : O) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y)
      = P.randWeight read Good x m * (1 + P.trialFail read Good x m)
          * (1 + P.trialFail read Good x m ^ 2) * P.goodWeight read Good x y := by
  have h1 := P.randTrial_prob_some hP x hm y
  have h0 := P.randTrial_prob_none hP x hm
  have t1 : (P.twoTrials m hm).prob (read x) (P.trialBudget m + P.trialBudget m) (some y)
      = P.randWeight read Good x m * (1 + P.trialFail read Good x m)
          * P.goodWeight read Good x y := by
    rw [twoTrials, QAlg.orElse_prob_some, h1, h0, trialFail, goodWeight]; ring
  have t0 : (P.twoTrials m hm).prob (read x) (P.trialBudget m + P.trialBudget m) none
      = P.trialFail read Good x m ^ 2 := by
    rw [twoTrials, QAlg.orElse_prob_none, h0, trialFail]; ring
  rw [amplified, amplifiedBudget, QAlg.orElse_prob_some, t1, t0]
  ring

theorem amplified_prob_none (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) none
      = P.trialFail read Good x m ^ 4 := by
  have h0 := P.randTrial_prob_none hP x hm
  have t0 : (P.twoTrials m hm).prob (read x) (P.trialBudget m + P.trialBudget m) none
      = P.trialFail read Good x m ^ 2 := by
    rw [twoTrials, QAlg.orElse_prob_none, h0, trialFail]; ring
  rw [amplified, amplifiedBudget, QAlg.orElse_prob_none, t0]
  ring

/-- **No invalid output is ever returned.** -/
theorem amplified_prob_some_of_not_good (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m)
    {y : O} (hy : ¬ Good x y) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) = 0 := by
  rw [P.amplified_prob_some hP, goodWeight, if_neg hy, mul_zero]

/-- The probability of returning a candidate. -/
noncomputable def returnProb (read : X → ι → σ) (x : X) (m : ℕ) (hm : 0 < m) : ℝ :=
  1 - (P.amplified m hm).prob (read x) (P.amplifiedBudget m) none

lemma returnProb_eq_sum (x : X) {m : ℕ} (hm : 0 < m) :
    P.returnProb read x m hm
      = ∑ y, (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) := by
  have hsum := QAlg.sum_prob (P.amplified m hm) (read x) (P.amplifiedBudget m)
  rw [Fintype.sum_option] at hsum
  rw [returnProb]; linarith

/-- **If `pₓ = 0`, the output is `none` with probability one.** -/
theorem amplified_prob_none_of_succProb_eq_zero (hP : P.Marks read Good) (x : X) {m : ℕ}
    (hm : 0 < m) (h0 : P.succProb read Good x = 0) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) none = 1 := by
  rw [P.amplified_prob_none hP, trialFail, h0]; norm_num

/-- **A candidate is returned with probability at least `2/3`** whenever `pₓ ≥ p₀` and
`m·√p₀ ≥ 1`. -/
theorem two_thirds_le_returnProb (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hpp : p₀ ≤ P.succProb read Good x)
    (hmp : 1 ≤ (m : ℝ) * Real.sqrt p₀) : 2 / 3 ≤ P.returnProb read x m hm := by
  have hq := P.quarter_le_randWeight_mul x hm hp₀ hpp hmp
  have hn0 : 0 ≤ P.trialFail read Good x m := by
    rw [trialFail, ← P.randTrial_prob_none hP x hm]
    exact QAlg.prob_nonneg _ _ _ _
  have hn1 : P.trialFail read Good x m ≤ 3 / 4 := by rw [trialFail]; linarith
  rw [returnProb, P.amplified_prob_none hP]
  have h2 : P.trialFail read Good x m ^ 2 ≤ (3 / 4) ^ 2 := pow_le_pow_left₀ hn0 hn1 2
  have h4 : P.trialFail read Good x m ^ 4 ≤ (3 / 4) ^ 4 := pow_le_pow_left₀ hn0 hn1 4
  norm_num at h4 ⊢
  linarith

/-- **The conditional law, in product form**, through the random iteration count, the
mixture and the first-success selection. -/
theorem succProb_mul_amplified_prob_some (hP : P.Marks read Good) (x : X) {m : ℕ}
    (hm : 0 < m) (y : O) :
    P.succProb read Good x * (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y)
      = P.returnProb read x m hm * P.goodWeight read Good x y := by
  rw [returnProb, P.amplified_prob_none hP, P.amplified_prob_some hP, trialFail]
  ring

/-- **The conditional law, divided**: given that a candidate is returned, it is distributed
as the original output conditioned on validity. -/
theorem amplified_cond_law (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) (y : O)
    (hp : 0 < P.succProb read Good x) (hs : 0 < P.returnProb read x m hm) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) / P.returnProb read x m hm
      = P.goodWeight read Good x y / P.succProb read Good x := by
  rw [div_eq_div_iff hs.ne' hp.ne']
  have := P.succProb_mul_amplified_prob_some hP x hm y
  linarith

/-! ## The relation on `Option O` -/

/-- The relation accepting exactly the valid candidates. -/
def OptGood (Good : X → O → Prop) (x : X) (o : Option O) : Prop := ∃ y, o = some y ∧ Good x y

instance (x : X) : DecidablePred (OptGood Good x) := fun o =>
  match o with
  | none => isFalse (by rintro ⟨y, h, -⟩; exact absurd h (by simp))
  | some y => decidable_of_iff (Good x y)
      ⟨fun h => ⟨y, rfl, h⟩, by rintro ⟨z, h, hz⟩; rwa [Option.some.inj h]⟩

/-- The success probability for `OptGood` is the probability of returning a candidate. -/
theorem successProbOn_amplified (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) :
    successProbOn (P.amplified m hm) (P.amplifiedBudget m) read (OptGood Good) x
      = P.returnProb read x m hm := by
  rw [successProbOn, goodProb_eq_sum, Fintype.sum_option, returnProb_eq_sum]
  have hnone : ¬ OptGood Good x none := by rintro ⟨y, h, -⟩; exact absurd h (by simp)
  rw [if_neg hnone, zero_add]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : Good x y
  · rw [if_pos ⟨y, rfl, hy⟩]; rfl
  · rw [if_neg (by rintro ⟨z, h, hz⟩; exact hy (Option.some.inj h ▸ hz))]
    exact (P.amplified_prob_some_of_not_good hP x hm hy).symm

/-- **Under a uniform lower bound the amplified algorithm solves the relation** with error
`1/3`. -/
theorem solvesWithErrorOn_amplified (hP : P.Marks read Good) {m : ℕ} (hm : 0 < m) {p₀ : ℝ}
    (hp₀ : 0 < p₀) (hpp : ∀ x, p₀ ≤ P.succProb read Good x)
    (hmp : 1 ≤ (m : ℝ) * Real.sqrt p₀) :
    SolvesWithErrorOn (P.amplified m hm) (P.amplifiedBudget m) read (OptGood Good) (1 / 3) := by
  intro x
  rw [P.successProbOn_amplified hP]
  have := P.two_thirds_le_returnProb hP x hm hp₀ (hpp x) hmp
  linarith

end AmpSetup

/-! ## The number of iteration counts -/

/-- `m = ⌈1/√p₀⌉`. -/
noncomputable def ampIterations (p₀ : ℝ) : ℕ := ⌈1 / Real.sqrt p₀⌉₊

lemma ampIterations_pos {p₀ : ℝ} (hp₀ : 0 < p₀) : 0 < ampIterations p₀ :=
  Nat.ceil_pos.mpr (by have := Real.sqrt_pos.mpr hp₀; positivity)

lemma one_le_ampIterations_mul_sqrt {p₀ : ℝ} (hp₀ : 0 < p₀) :
    1 ≤ (ampIterations p₀ : ℝ) * Real.sqrt p₀ := by
  have hs := Real.sqrt_pos.mpr hp₀
  have h := Nat.le_ceil (1 / Real.sqrt p₀)
  rw [div_le_iff₀ hs] at h
  exact h

/-- `⌈1/√p₀⌉ ≤ 2/√p₀` for `0 < p₀ ≤ 1`. -/
lemma ampIterations_le {p₀ : ℝ} (hp₀ : 0 < p₀) (hp1 : p₀ ≤ 1) :
    (ampIterations p₀ : ℝ) ≤ 2 / Real.sqrt p₀ := by
  have hs := Real.sqrt_pos.mpr hp₀
  have hs1 : Real.sqrt p₀ ≤ 1 := Real.sqrt_le_one.mpr hp1 |>.trans_eq rfl
  have h1 : 1 ≤ 1 / Real.sqrt p₀ := by rw [le_div_iff₀ hs]; linarith
  have h := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt p₀)).le
  calc (ampIterations p₀ : ℝ) ≤ 1 / Real.sqrt p₀ + 1 := h
    _ ≤ 1 / Real.sqrt p₀ + 1 / Real.sqrt p₀ := by linarith
    _ = 2 / Real.sqrt p₀ := by ring

/-- **The real-valued budget: at most `16·(S+C)/√p₀`.** -/
theorem AmpSetup.amplifiedBudget_le_real (P : AmpSetup ι σ W O) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp1 : p₀ ≤ 1) :
    (P.amplifiedBudget (ampIterations p₀) : ℝ)
      ≤ 16 * ((P.prep.len : ℝ) + P.mark.len) / Real.sqrt p₀ := by
  have hs := Real.sqrt_pos.mpr hp₀
  have h1 := P.amplifiedBudget_le (ampIterations p₀) (ampIterations_pos hp₀)
  have h1' : (P.amplifiedBudget (ampIterations p₀) : ℝ)
      ≤ 4 * ((ampIterations p₀ : ℝ) * (2 * P.prep.len + P.mark.len)) := by exact_mod_cast h1
  have h2 := ampIterations_le hp₀ hp1
  have hSC : (2 * (P.prep.len : ℝ) + P.mark.len) ≤ 2 * ((P.prep.len : ℝ) + P.mark.len) := by
    have : (0 : ℝ) ≤ P.mark.len := Nat.cast_nonneg _
    linarith
  calc (P.amplifiedBudget (ampIterations p₀) : ℝ)
      ≤ 4 * ((ampIterations p₀ : ℝ) * (2 * P.prep.len + P.mark.len)) := h1'
    _ ≤ 4 * ((2 / Real.sqrt p₀) * (2 * ((P.prep.len : ℝ) + P.mark.len))) := by
        gcongr
    _ = 16 * ((P.prep.len : ℝ) + P.mark.len) / Real.sqrt p₀ := by ring

end QuantumQueryComplexity
