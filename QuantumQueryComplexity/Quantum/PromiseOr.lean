import QuantumQueryComplexity.Quantum.Amplitude.Amplification
import QuantumQueryComplexity.Quantum.CoherentMajority
import QuantumQueryComplexity.Quantum.SelectRoutine
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Combining one-sided promise tests with unequal costs

[CGKLPZ26, Lemma 2.5 and Appendix A; Amb08]. A **promise test** with error `ε` accepts every input
in `Pos` and rejects every input in `Neg` with probability at least `1 − ε` (`IsPromiseLaw`);
nothing is promised elsewhere. In the paper `Pos` is "positive for its own edge list" and `Neg`
is "negative and within its stated bound", so a child gives no guarantee on a positive global
input that is not positive for its own edges.

Given `m` children with known budgets `q i`, each a promise test with error `1/3`, their **OR**
is a promise test with error `ε` for `Pos = ∃ i, Pos i` and `Neg = ∀ i, Neg i`, with
`promiseOrBudget q ε` queries (`exists_promiseOr`), and

    promiseOrBudget q ε ≤ 10⁵ · √(∑_i (q_i + 1)²) · (1 + log₂ m) · (3 + log₂(1 + ∑_i q_i))²
                             · (1 + log₂(1/ε))        (`promiseOrBudget_le`).

The existing `robustOr_computes` charges every child the largest budget and needs every child to
be correct on every input; neither holds here.

Construction (variable-time search with known costs, by dyadic cost classes):
* a child of budget `q` is in class `g = ⌈log₂(q + 1)⌉` (`costClass`), so `q < 2^g ≤ 2(q + 1)`;
* in a class with `r` children, each child's error is reduced to `(1/2)^n ≤ 1/(1000 r)` by a
  majority of `12n` runs, `n = ⌈log₂(1000 r)⌉` (`childReps`, `maj_twelve_le`), padded to `2^g`;
* a uniform coherent choice of child accepts with probability at least `(1 − 1/(1000r))/r` if
  some child of the class is in its `Pos`, **whatever the other children do**, and at most
  `1/(1000r)` if every child is in its `Neg`;
* randomized amplitude amplification with `⌈√(2r)⌉` iterations (`amplified`) then accepts with
  probability `≥ 2/3` in the first case and `≤ 1/10` in the second;
* a majority of `12⌈log₂(G/ε)⌉` runs (`classReps`) reduces each class's error to `ε/G`, `G` the
  number of classes, and the OR of the class decisions errs with probability at most `ε`.
The cost of class `g` is `classReps · 8⌈√(2r)⌉ · childReps · 2^g`; Cauchy–Schwarz over the classes
gives the bound.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **A one-sided promise test**: accept every input in `Pos`, reject every input in `Neg`, each
with probability at least `1 − ε`; no guarantee elsewhere. -/
def IsPromiseLaw (P : (ι → σ) → Bool → ℝ) (Pos Neg : (ι → σ) → Prop) (ε : ℝ) : Prop :=
  (∀ a, Pos a → 1 - ε ≤ P a true) ∧ ∀ a, Neg a → 1 - ε ≤ P a false

/-! ## The budget -/

/-- **The cost class** of a budget `c`: `⌈log₂(c + 1)⌉`, so `c < 2^g ≤ 2(c + 1)`. -/
def costClass (c : ℕ) : ℕ := Nat.clog 2 (c + 1)

/-- The number of children in class `g`. -/
def classSize {m : ℕ} (q : Fin m → ℕ) (g : ℕ) : ℕ :=
  (Finset.univ.filter fun i => costClass (q i) = g).card

/-- The number of classes: one more than the largest class. -/
def numClasses {m : ℕ} (q : Fin m → ℕ) : ℕ := (Finset.univ.sup fun i => costClass (q i)) + 1

/-- Majority runs per child in a class of `r`: `12 ⌈log₂(1000 r)⌉`. -/
def childReps (r : ℕ) : ℕ := 12 * Nat.clog 2 (1000 * r)

/-- Amplification iterations in a class of `r`: `⌈√(2r)⌉`. -/
noncomputable def classIters (r : ℕ) : ℕ := ⌈Real.sqrt (2 * r)⌉₊

/-- Majority runs per class decision for overall error `ε` among `G` classes:
`12 ⌈log₂(G/ε)⌉`. -/
noncomputable def classReps (G : ℕ) (ε : ℝ) : ℕ := 12 * ⌈Real.logb 2 (G / ε)⌉₊

/-- **The budget of the OR**: the sum over the nonempty classes `g` of
`classReps · 8 ⌈√(2r)⌉ · childReps r · 2^g`, `r` the class size. -/
noncomputable def promiseOrBudget {m : ℕ} (q : Fin m → ℕ) (ε : ℝ) : ℕ :=
  ∑ g ∈ Finset.range (numClasses q),
    if classSize q g = 0 then 0 else
      classReps (numClasses q) ε *
        (8 * classIters (classSize q g) * (childReps (classSize q g) * 2 ^ g))

/-- `log₂ n ≥ 0` for a natural number `n` (with `log₂ 0 = 0`). -/
private lemma pob_logb_nonneg (n : ℕ) : 0 ≤ Real.logb 2 n :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.log_nonneg one_le_two)

/-- The natural ceiling logarithm exceeds the real logarithm by less than one. -/
private lemma pob_clog_le (n : ℕ) : (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := by
  have h := Real.natCeil_logb_natCast 2 n
  push_cast at h
  rw [← h]
  exact (Nat.ceil_lt_add_one (pob_logb_nonneg n)).le

/-- A budget `c` in class `g = ⌈log₂(c + 1)⌉` has `2^g ≤ 2 (c + 1)`. -/
private lemma pob_two_pow_le (c : ℕ) : 2 ^ costClass c ≤ 2 * (c + 1) := by
  unfold costClass
  rcases Nat.lt_or_ge 1 (c + 1) with h | h
  · have h1 := Nat.pow_pred_clog_lt_self one_lt_two h
    rcases hk : Nat.clog 2 (c + 1) with _ | k
    · simp only [pow_zero]
      omega
    · rw [hk, Nat.pred_succ] at h1
      rw [pow_succ]
      omega
  · rw [Nat.clog_of_right_le_one h]
    omega

/-- A class `g` of size `r` has `r · (2^g)² ≤ 4 ∑_i (q_i + 1)²`. -/
private lemma pob_class_sq {m : ℕ} (q : Fin m → ℕ) (g : ℕ) :
    (classSize q g : ℝ) * ((2 : ℝ) ^ g) ^ 2 ≤ 4 * ∑ i, ((q i : ℝ) + 1) ^ 2 := by
  unfold classSize
  rw [Finset.mul_sum]
  calc ((Finset.univ.filter fun i => costClass (q i) = g).card : ℝ) * ((2 : ℝ) ^ g) ^ 2
      = ∑ _i ∈ Finset.univ.filter (fun i => costClass (q i) = g), ((2 : ℝ) ^ g) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => costClass (q i) = g), 4 * ((q i : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_filter] at hi
        have h := pob_two_pow_le (q i)
        rw [hi.2] at h
        have h' : (2 : ℝ) ^ g ≤ 2 * ((q i : ℝ) + 1) := by exact_mod_cast h
        have h0 : (0 : ℝ) ≤ 2 ^ g := by positivity
        nlinarith
    _ ≤ ∑ i, 4 * ((q i : ℝ) + 1) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => mul_nonneg (by norm_num) (sq_nonneg _))

/-- A nonempty class `g` has `⌈√(2r)⌉ · 2^g ≤ 6 √(∑_i (q_i + 1)²)`, `r` its size. -/
private lemma pob_iters_le {m : ℕ} (q : Fin m → ℕ) (g : ℕ) (hr : classSize q g ≠ 0) :
    (classIters (classSize q g) : ℝ) * 2 ^ g ≤ 6 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) := by
  have hr1 : (1 : ℝ) ≤ classSize q g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have hsq := pob_class_sq q g
  have hS : (0 : ℝ) ≤ ∑ i, ((q i : ℝ) + 1) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 : (0 : ℝ) ≤ 2 ^ g := by positivity
  have h1 : (classIters (classSize q g) : ℝ) ≤ 3 * Real.sqrt (classSize q g) := by
    unfold classIters
    have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * (classSize q g : ℝ)))
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h3 : 1 ≤ Real.sqrt (classSize q g) := Real.one_le_sqrt.mpr hr1
    rw [Real.sqrt_mul (by norm_num)] at hc ⊢
    have h5 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (classSize q g : ℝ))
    linarith
  have h4 : Real.sqrt (classSize q g) * 2 ^ g ≤ 2 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) := by
    have e1 : Real.sqrt (classSize q g) * 2 ^ g =
        Real.sqrt ((classSize q g : ℝ) * ((2 : ℝ) ^ g) ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h0]
    have e2 : Real.sqrt (4 * ∑ i, ((q i : ℝ) + 1) ^ 2) =
        2 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [e1, ← e2]
    exact Real.sqrt_le_sqrt hsq
  calc (classIters (classSize q g) : ℝ) * 2 ^ g ≤ 3 * Real.sqrt (classSize q g) * 2 ^ g := by
        gcongr
    _ = 3 * (Real.sqrt (classSize q g) * 2 ^ g) := by ring
    _ ≤ 3 * (2 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) := by gcongr
    _ = 6 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) := by ring

/-- A nonempty class of size `r` has `⌈log₂(1000 r)⌉ ≤ 11 (1 + log₂ m)`. -/
private lemma pob_child_le {m : ℕ} (q : Fin m → ℕ) (g : ℕ) (hr : classSize q g ≠ 0) :
    (Nat.clog 2 (1000 * classSize q g) : ℝ) ≤ 11 * (1 + Real.logb 2 m) := by
  have hrm : classSize q g ≤ m := by
    unfold classSize
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hr1 : (1 : ℝ) ≤ classSize q g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have h := pob_clog_le (1000 * classSize q g)
  push_cast at h
  rw [Real.logb_mul (by norm_num) (by positivity)] at h
  have h1000 : Real.logb 2 1000 ≤ 10 := by
    have h' : Real.logb 2 1000 ≤ Real.logb 2 (2 ^ 10) :=
      Real.logb_le_logb_of_le one_lt_two (by norm_num) (by norm_num)
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h'
    norm_num at h'
    exact h'
  have hlog : Real.logb 2 (classSize q g) ≤ Real.logb 2 m :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) (by exact_mod_cast hrm)
  have := pob_logb_nonneg m
  linarith

/-- The number of classes is at most `2 + log₂(1 + ∑_i q_i)`. -/
private lemma pob_numClasses_le {m : ℕ} (q : Fin m → ℕ) :
    (numClasses q : ℝ) ≤ 2 + Real.logb 2 (1 + ∑ i, (q i : ℝ)) := by
  have hsup : (Finset.univ.sup fun i => costClass (q i)) ≤ Nat.clog 2 ((∑ i, q i) + 1) := by
    apply Finset.sup_le
    intro i _
    apply Nat.clog_mono_right
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
    omega
  have h := pob_clog_le ((∑ i, q i) + 1)
  have hsup' : ((Finset.univ.sup fun i => costClass (q i) : ℕ) : ℝ) ≤
      Nat.clog 2 ((∑ i, q i) + 1) := by exact_mod_cast hsup
  push_cast at h
  unfold numClasses
  push_cast
  rw [add_comm (1 : ℝ)]
  linarith

/-- `1 + log₂ G ≤ G` for the number of classes `G`. -/
private lemma pob_log_numClasses_le {m : ℕ} (q : Fin m → ℕ) :
    1 + Real.logb 2 (numClasses q) ≤ numClasses q := by
  unfold numClasses
  set M := Finset.univ.sup fun i => costClass (q i)
  have h1 : M + 1 ≤ 2 ^ M := M.lt_two_pow_self
  have h2 : Real.logb 2 ((M + 1 : ℕ) : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ M) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by exact_mod_cast h1)
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h2
  push_cast at h2 ⊢
  linarith

/-- The majority repetitions satisfy `classReps G ε ≤ 12 (1 + log₂ G)(1 + log₂(1/ε))`. -/
private lemma pob_classReps_le {m : ℕ} (q : Fin m → ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (classReps (numClasses q) ε : ℝ) ≤
      12 * (1 + Real.logb 2 (numClasses q)) * (1 + Real.logb 2 (1 / ε)) := by
  have hG : (1 : ℝ) ≤ numClasses q := by
    unfold numClasses
    push_cast
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((Finset.univ.sup fun i => costClass (q i) : ℕ)))]
  have hε' : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have ha := pob_logb_nonneg (numClasses q)
  have hb : 0 ≤ Real.logb 2 (1 / ε) := Real.logb_nonneg one_lt_two hε'
  have e : Real.logb 2 ((numClasses q : ℝ) / ε) =
      Real.logb 2 (numClasses q) + Real.logb 2 (1 / ε) := by
    rw [div_eq_mul_one_div, Real.logb_mul (by positivity) (by positivity)]
  unfold classReps
  push_cast
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 ((numClasses q : ℝ) / ε) by
    rw [e]; positivity)
  rw [e] at hc ⊢
  nlinarith [mul_nonneg ha hb]

/-- **The budget is `Õ(√(∑ q_i²))`**, with explicit constant and logarithms. -/
theorem promiseOrBudget_le {m : ℕ} (q : Fin m → ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (promiseOrBudget q ε : ℝ) ≤
      100000 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) * (1 + Real.logb 2 m) *
        (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) ^ 2 * (1 + Real.logb 2 (1 / ε)) := by
  have hlm := pob_logb_nonneg m
  have hle : 0 ≤ Real.logb 2 (1 / ε) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hε0]; linarith)
  have hL : 0 ≤ Real.logb 2 (1 + ∑ i, (q i : ℝ)) :=
    Real.logb_nonneg one_lt_two (by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      (Nat.cast_nonneg (q i) : (0 : ℝ) ≤ q i)])
  have hS := Real.sqrt_nonneg (∑ i, ((q i : ℝ) + 1) ^ 2)
  have hG := pob_numClasses_le q
  have hlogG := pob_log_numClasses_le q
  have hR := pob_classReps_le q hε0 hε1
  have hGR : (numClasses q : ℝ) * classReps (numClasses q) ε ≤
      12 * (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) ^ 2 * (1 + Real.logb 2 (1 / ε)) := by
    have hG0 : (0 : ℝ) ≤ numClasses q := Nat.cast_nonneg _
    calc (numClasses q : ℝ) * classReps (numClasses q) ε
        ≤ numClasses q * (12 * (1 + Real.logb 2 (numClasses q)) * (1 + Real.logb 2 (1 / ε))) :=
          mul_le_mul_of_nonneg_left hR hG0
      _ = 12 * (numClasses q * (1 + Real.logb 2 (numClasses q))) * (1 + Real.logb 2 (1 / ε)) := by
          ring
      _ ≤ 12 * ((3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) * (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))))
            * (1 + Real.logb 2 (1 / ε)) := by
          have hA : (numClasses q : ℝ) * (1 + Real.logb 2 (numClasses q)) ≤
              (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) * (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) :=
            mul_le_mul (by linarith) (by linarith)
              (by linarith [pob_logb_nonneg (numClasses q)]) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num))
            (by linarith)
      _ = 12 * (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) ^ 2 * (1 + Real.logb 2 (1 / ε)) := by ring
  have hterm : ∀ g ∈ Finset.range (numClasses q),
      (((if classSize q g = 0 then 0 else classReps (numClasses q) ε *
        (8 * classIters (classSize q g) * (childReps (classSize q g) * 2 ^ g)) : ℕ)) : ℝ) ≤
        6336 * classReps (numClasses q) ε * (1 + Real.logb 2 m) *
          Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) := by
    intro g _
    split_ifs with h
    · simp only [Nat.cast_zero]
      positivity
    · have h1 := pob_iters_le q g h
      have h2 := pob_child_le q g h
      unfold childReps
      push_cast
      calc (classReps (numClasses q) ε : ℝ) * (8 * classIters (classSize q g) *
            (12 * Nat.clog 2 (1000 * classSize q g) * 2 ^ g))
          = 96 * classReps (numClasses q) ε * (Nat.clog 2 (1000 * classSize q g) : ℝ) *
              (classIters (classSize q g) * 2 ^ g) := by ring
        _ ≤ 96 * classReps (numClasses q) ε * (11 * (1 + Real.logb 2 m)) *
              (6 * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) := by
            gcongr
        _ = _ := by ring
  have hsum : (promiseOrBudget q ε : ℝ) ≤ numClasses q * (6336 * classReps (numClasses q) ε *
      (1 + Real.logb 2 m) * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) := by
    unfold promiseOrBudget
    rw [Nat.cast_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine hsum.trans ?_
  have hX : 0 ≤ (1 + Real.logb 2 m) * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2) :=
    mul_nonneg (by linarith) hS
  calc (numClasses q : ℝ) * (6336 * classReps (numClasses q) ε * (1 + Real.logb 2 m) *
        Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2))
      = 6336 * ((1 + Real.logb 2 m) * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) *
          ((numClasses q : ℝ) * classReps (numClasses q) ε) := by ring
    _ ≤ 6336 * ((1 + Real.logb 2 m) * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) *
          (12 * (3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) ^ 2 * (1 + Real.logb 2 (1 / ε))) :=
        mul_le_mul_of_nonneg_left hGR (by linarith)
    _ ≤ _ := by
        have hY : 0 ≤ ((1 + Real.logb 2 m) * Real.sqrt (∑ i, ((q i : ℝ) + 1) ^ 2)) *
            ((3 + Real.logb 2 (1 + ∑ i, (q i : ℝ))) ^ 2 * (1 + Real.logb 2 (1 / ε))) :=
          mul_nonneg hX (mul_nonneg (by positivity) (by linarith))
        nlinarith

/-! ## The OR -/

section Generic

variable {X : Type} [Fintype X]

/-- Padding a realization to a larger budget. -/
private lemma por_realizes_mono {O : Type} [DecidableEq O] {read : X → ι → σ} {q q' : ℕ}
    {P : X → O → ℝ} (h : Realizes read q P) (hq : q ≤ q') : Realizes read q' P := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  refine ⟨CtrlWork ι W, inferInstance, inferInstance, padAlg A q (q' - q), fun x o => ?_⟩
  have h1 := padAlg_prob A q (q' - q) (read x) o
  rw [show q + (q' - q) = q' by omega] at h1
  rw [h1, hA]

/-- A realized Boolean law sums to one. -/
private lemma por_bool_sum {read : X → ι → σ} {q : ℕ} {P : X → Bool → ℝ}
    (h : Realizes read q P) (x : X) : P x true + P x false = 1 := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  have h1 := A.sum_prob (read x) q
  rw [Fintype.sum_bool, hA, hA] at h1
  exact h1

/-- The constant `false` law needs no queries. -/
private lemma por_realizes_false (read : X → ι → σ) :
    Realizes read 0 (fun (_ : X) (o : Bool) => if o then (0 : ℝ) else 1) := by
  refine ⟨Unit, inferInstance, inferInstance, constAlg ι σ false, fun x o => ?_⟩
  cases o <;> simp [QAlg.prob, constAlg]

/-- **Majority of `12 n` runs**: a wrong value of probability at most `1/3` becomes one of
probability at most `2^{-n}`. -/
private lemma por_majority {read : X → ι → σ} {q : ℕ} {P : X → Bool → ℝ}
    (h : Realizes read q P) (n : ℕ) :
    ∃ M : X → Bool → ℝ, Realizes read (12 * n * q) M ∧
      ∀ x b, P x (!b) ≤ 1 / 3 → M x (!b) ≤ (1 / 2) ^ n := by
  have hfold := Realizes.fold (12 * n) (fun _ => q) (fun _ => P) (fun _ => h)
  have hcost : (∑ _j : Fin (12 * n), q) = 12 * n * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  refine ⟨_, hfold.map (majVote (12 * n)), fun x b hb => ?_⟩
  have hnn := h.nonneg
  have hsub : Finset.univ.filter (fun y : Fin (12 * n) → Bool => majVote (12 * n) y = !b)
      ⊆ Finset.univ.filter (fun y : Fin (12 * n) → Bool =>
          6 * n ≤ wrongCount y (fun _ => b)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have := le_card_wrong_of_majVote_ne (b := b) (by rw [hy]; cases b <;> simp)
    have hk : (12 * n + 1) / 2 = 6 * n := by omega
    rw [hk] at this
    exact this
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun y => ∏ j, P x (y j)) hsub
    (fun y _ _ => Finset.prod_nonneg fun j _ => hnn x (y j))
  have htail := sum_prod_tail_le (k := 12 * n) (t := 6 * n) (ε := 1 / 3) (fun _ o => P x o)
    (fun _ => b)
    (fun _ o => hnn x o) (fun _ => le_of_eq (by rw [Fintype.sum_bool]; exact por_bool_sum h x))
    (fun _ => by
      have : Finset.univ.filter (fun o : Bool => o ≠ b) = {!b} := by
        ext o; cases o <;> cases b <;> simp
      rw [this, Finset.sum_singleton]
      exact hb)
  change ∑ y ∈ Finset.univ.filter (fun y => majVote (12 * n) y = !b), ∏ j, P x (y j) ≤ _
  have h2 : ((1 : ℝ) + 1 / 3) ^ (12 * n) ≤ (1 / 2) ^ n * 2 ^ (6 * n) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) n
  have hpos : (0 : ℝ) < 2 ^ (6 * n) := by positivity
  have h3 := le_trans htail h2
  have h4 := (mul_le_mul_iff_left₀ hpos).mp h3
  linarith

/-! ### Amplitude amplification of a realized test -/

/-- The phase `−1` on the accepting basis states: a zero-query exact marker. -/
private noncomputable def por_phase {W : Type} [Fintype W] [DecidableEq W]
    (rd : QBasis ι σ W → Bool) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  Matrix.diagonal fun β => if rd β = true then -1 else 1

/-- The phase is unitary. -/
private lemma por_phase_mem {W : Type} [Fintype W] [DecidableEq W]
    (rd : QBasis ι σ W → Bool) : por_phase rd ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, por_phase, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext β
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- The amplification setup of an algorithm with Boolean output: prepare by running it, mark
acceptance by a phase. -/
private noncomputable def por_setup {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ Bool W) (q : ℕ) : AmpSetup ι σ W Bool where
  prep := ⟨q, A.step, A.step_unitary⟩
  init := A.init
  init_isQState := A.init_isQState
  mark := QRoutine.ofUnitary (por_phase A.readout) (por_phase_mem A.readout)
  readout := A.readout

/-- The prepared state is the algorithm's state after `q` queries. -/
private lemma por_setup_prepared {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ Bool W) (q : ℕ) (a : ι → σ) : (por_setup A q).prepared a = A.state a q :=
  (A.state_eq_runUpto ⟨q, A.step, A.step_unitary⟩ rfl a q).symm

/-- The phase marks acceptance exactly. -/
private lemma por_setup_marks {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ Bool W) (q : ℕ) (read : X → ι → σ) :
    (por_setup A q).Marks read (fun _ y => y = true) := by
  intro x
  constructor
  · funext β
    simp only [por_setup, QRoutine.ofUnitary_run, por_phase, Matrix.mulVec_diagonal,
      goodPart_apply, Pi.neg_apply]
    split_ifs <;> simp
  · funext β
    simp only [por_setup, QRoutine.ofUnitary_run, por_phase, Matrix.mulVec_diagonal,
      badPart_apply]
    split_ifs <;> simp

/-- The success probability of the setup is the acceptance probability. -/
private lemma por_setup_succProb {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ Bool W) (q : ℕ) (read : X → ι → σ) (x : X) :
    (por_setup A q).succProb read (fun _ y => y = true) x = A.prob (read x) q true := by
  rw [AmpSetup.succProb, por_setup_prepared, goodProb, QAlg.prob]
  congr 1

/-- The bad coefficient is bounded: `β_j² ≤ 2` for `p ≤ 1/2`. -/
private lemma por_ampB_sq_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1 / 2) (j : ℕ) :
    ampB p j ^ 2 ≤ 2 := by
  have h := mul_ampB_sq h0 (by linarith) j
  have hc := Real.cos_sq_le_one ((2 * j + 1) * groverAngle p)
  nlinarith [sq_nonneg (ampB p j)]

/-- `(1 − p)·|β_j| ≤ 1`. -/
private lemma por_abs_mul_ampB_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (j : ℕ) :
    |(1 - p) * ampB p j| ≤ 1 := by
  have h := mul_ampB_sq h0 h1 j
  have hc := Real.cos_sq_le_one ((2 * j + 1) * groverAngle p)
  have hsq : ((1 - p) * ampB p j) ^ 2 ≤ 1 := by
    have : ((1 - p) * ampB p j) ^ 2 = (1 - p) * ((1 - p) * ampB p j ^ 2) := by ring
    rw [this]
    nlinarith [sq_nonneg (ampB p j)]
  exact (sq_le_one_iff_abs_le_one _).mp hsq

/-- The good coefficient grows at most linearly: `|α_j| ≤ 2j + 1`. -/
private lemma por_abs_ampA_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∀ j : ℕ, |ampA p j| ≤ 2 * j + 1
  | 0 => by simp
  | j + 1 => by
    have ih := por_abs_ampA_le h0 h1 j
    have hB := por_abs_mul_ampB_le h0 h1 j
    have h2 : |1 - 2 * p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [ampA_succ]
    calc |(1 - 2 * p) * ampA p j + 2 * (1 - p) * ampB p j|
        ≤ |(1 - 2 * p) * ampA p j| + |2 * ((1 - p) * ampB p j)| := by
          rw [← mul_assoc]; exact abs_add_le _ _
      _ = |1 - 2 * p| * |ampA p j| + 2 * |(1 - p) * ampB p j| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 1 * (2 * j + 1) + 2 * 1 := by
          gcongr
      _ = 2 * ((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

/-- The weight of one randomized trial is at most `((2m−1)² + 2)/2`. -/
private lemma por_randWeight_le {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ Bool W) (q : ℕ) (read : X → ι → σ) (x : X) {m : ℕ} (hm : 0 < m) :
    (por_setup A q).randWeight read (fun _ y => y = true) x m
      ≤ ((2 * (m : ℝ) - 1) ^ 2 + 2) / 2 := by
  set S := por_setup A q
  set p := S.succProb read (fun _ y => y = true) x
  have hp0 : 0 ≤ p := S.succProb_nonneg x
  have hp1 : p ≤ 1 := S.succProb_le_one x
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : ∀ j : Fin m, S.trialWeight read (fun _ y => y = true) x j
      ≤ ((2 * (m : ℝ) - 1) ^ 2 + 2) / 2 := by
    intro j
    rw [AmpSetup.trialWeight]
    have hA := por_abs_ampA_le (p := p / 2) (by linarith) (by linarith) j
    have hB := por_ampB_sq_le (p := p / 2) (by linarith) (by linarith) j
    have hjm : (2 * ((j : ℕ) : ℝ) + 1) ≤ 2 * (m : ℝ) - 1 := by
      have : ((j : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast j.2
      linarith
    have hA2 : ampA (p / 2) j ^ 2 ≤ (2 * (m : ℝ) - 1) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA.trans hjm) 2
    change (ampA (p / 2) j ^ 2 + ampB (p / 2) j ^ 2) / 2 ≤ _
    linarith
  rw [AmpSetup.randWeight, div_le_iff₀ hm']
  calc (∑ j : Fin m, S.trialWeight read (fun _ y => y = true) x j)
      ≤ ∑ _j : Fin m, ((2 * (m : ℝ) - 1) ^ 2 + 2) / 2 := Finset.sum_le_sum fun j _ => hj j
    _ = ((2 * (m : ℝ) - 1) ^ 2 + 2) / 2 * m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

set_option synthInstance.maxSize 100000 in
/-- **Amplitude amplification of a realized Boolean test** with `m` random iteration counts:
acceptance at least `2/3` above a threshold `p₀` with `m √p₀ ≥ 1`, and at most
`2((2m−1)² + 2)` times the original acceptance in every case. -/
private lemma por_amplify {read : X → ι → σ} {L : ℕ} {U : X → Bool → ℝ}
    (h : Realizes read L U) {m : ℕ} (hm : 0 < m) :
    ∃ V : X → Bool → ℝ, Realizes read (4 * (L + (m - 1) * (2 * L))) V ∧
      ∀ x, (∀ p₀ : ℝ, 0 < p₀ → p₀ ≤ U x true → 1 ≤ (m : ℝ) * Real.sqrt p₀ →
          2 / 3 ≤ V x true) ∧
        V x true ≤ 2 * ((2 * (m : ℝ) - 1) ^ 2 + 2) * U x true := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  set S := por_setup A L with hS
  have hmk := por_setup_marks A L read
  have hbud : S.amplifiedBudget m = 4 * (L + (m - 1) * (2 * L)) := by
    rw [AmpSetup.amplifiedBudget_eq, AmpSetup.trialBudget]
    rfl
  have hR : Realizes read (S.amplifiedBudget m)
      (fun x o => (S.amplified m hm).prob (read x) (S.amplifiedBudget m) o) :=
    ⟨_, inferInstance, inferInstance, S.amplified m hm, fun _ _ => rfl⟩
  have hret : ∀ x, (∑ o ∈ Finset.univ.filter (fun o : Option Bool => o.isSome = true),
      (S.amplified m hm).prob (read x) (S.amplifiedBudget m) o)
      = S.returnProb read x m hm := by
    intro x
    rw [S.returnProb_eq_sum, Finset.sum_filter, Fintype.sum_option]
    simp
  refine ⟨fun x b => ∑ o ∈ Finset.univ.filter (fun o : Option Bool => o.isSome = b),
      (S.amplified m hm).prob (read x) (S.amplifiedBudget m) o, ?_,
    fun x => ⟨fun p₀ hp₀ hpp hmp => ?_, ?_⟩⟩
  · rw [← hbud]
    exact hR.map Option.isSome
  · beta_reduce
    rw [hret]
    refine S.two_thirds_le_returnProb hmk x hm hp₀ ?_ hmp
    rwa [por_setup_succProb, hA]
  · beta_reduce
    rw [hret, AmpSetup.returnProb, S.amplified_prob_none hmk, AmpSetup.trialFail]
    have hsp : S.succProb read (fun _ y => y = true) x = U x true := by
      rw [por_setup_succProb, hA]
    have hw0 := S.randWeight_nonneg (read := read) (Good := fun _ y => y = true) x m
    have hw1 := por_randWeight_le A L read x hm
    have hn0 : 0 ≤ 1 - S.randWeight read (fun _ y => y = true) x m
        * S.succProb read (fun _ y => y = true) x := by
      rw [← S.randTrial_prob_none hmk x hm]
      exact QAlg.prob_nonneg _ _ _ _
    rw [hsp] at hn0 ⊢
    have hU0 : 0 ≤ U x true := by rw [← hsp]; exact S.succProb_nonneg x
    set t := 1 - S.randWeight read (fun _ y => y = true) x m * U x true with ht
    have ht1 : t ≤ 1 := by rw [ht]; nlinarith
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have ht3 : t ^ 3 ≤ 1 := by nlinarith
    have h4 : 1 - t ^ 4 ≤ 4 * (1 - t) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by linarith : (0 : ℝ) ≤ 3 - t - t ^ 2 - t ^ 3)]
    have hwU : S.randWeight read (fun _ y => y = true) x m * U x true
        ≤ ((2 * (m : ℝ) - 1) ^ 2 + 2) / 2 * U x true :=
      mul_le_mul_of_nonneg_right hw1 hU0
    linarith

end Generic

/-! ### One cost class -/

/-- **A uniform mixture** of realized laws of costs at most `L`. -/
private lemma por_mixture {Ω : Type} [Fintype Ω] [DecidableEq Ω] {c : Ω → ℕ} {L : ℕ}
    (hc : ∀ ω, c ω ≤ L) {M : Ω → (ι → σ) → Bool → ℝ}
    (hM : ∀ ω, Realizes (id : (ι → σ) → ι → σ) (c ω) (M ω)) (hcard : 0 < Fintype.card Ω) :
    Realizes (id : (ι → σ) → ι → σ) L
      (fun a o => ∑ ω, (1 / (Fintype.card Ω : ℝ)) * M ω a o) := by
  choose W hW hW' A hA using hM
  have hc0 : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hcard
  have hsum : ∑ _ω : Ω, (1 / (Fintype.card Ω : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  obtain ⟨W', h1, h2, B, hB⟩ := exists_mixture (fun _ => 1 / (Fintype.card Ω : ℝ))
    (fun _ => by positivity) hsum c L hc A
  exact ⟨W', h1, h2, B, fun a o => by
    rw [hB]
    exact Finset.sum_congr rfl fun ω _ => by rw [hA]⟩

/-- The majority over `classReps G ε` runs errs with probability at most `ε / G`. -/
private lemma por_half_pow_classReps_le {G : ℕ} (hG : 0 < G) {ε : ℝ} (hε : 0 < ε) :
    (1 / 2 : ℝ) ^ ⌈Real.logb 2 (G / ε)⌉₊ ≤ ε / G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have hGε : 0 < (G : ℝ) / ε := div_pos hG' hε
  have h1 : (G : ℝ) / ε ≤ 2 ^ ⌈Real.logb 2 (G / ε)⌉₊ := by
    rw [← Real.rpow_natCast]
    calc (G : ℝ) / ε = 2 ^ Real.logb 2 (G / ε) := (Real.rpow_logb (by norm_num)
          (by norm_num) hGε).symm
      _ ≤ 2 ^ (⌈Real.logb 2 (G / ε)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [one_div_pow, div_le_div_iff₀ (by positivity) hG', one_mul]
  rw [div_le_iff₀ hε] at h1
  linarith

/-- The child majority errs with probability at most `1/(1000 r)`. -/
private lemma por_half_pow_clog_le {r : ℕ} (hr : 0 < r) :
    (1 / 2 : ℝ) ^ Nat.clog 2 (1000 * r) ≤ 1 / (1000 * r) := by
  have h : 1000 * r ≤ 2 ^ Nat.clog 2 (1000 * r) := Nat.le_pow_clog (by norm_num) _
  have h' : (1000 * r : ℝ) ≤ 2 ^ Nat.clog 2 (1000 * r) := by exact_mod_cast h
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) h'

/-- The amplification threshold is reached: `⌈√(2r)⌉ · √((1 − 1/(1000r))/r) ≥ 1`. -/
private lemma por_one_le_iters_mul {r : ℕ} (hr : 0 < r) :
    1 ≤ (classIters r : ℝ) * Real.sqrt ((1 - 1 / (1000 * r)) / r) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hs0 : 0 ≤ Real.sqrt (2 * r) := Real.sqrt_nonneg _
  have hm : Real.sqrt (2 * r) ≤ classIters r := Nat.le_ceil _
  have hinv : 1 / (1000 * (r : ℝ)) ≤ 1 / 1000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp0 : 0 ≤ (1 - 1 / (1000 * (r : ℝ))) / r := div_nonneg (by linarith) (by linarith)
  have hprod : Real.sqrt (2 * r) * Real.sqrt ((1 - 1 / (1000 * r)) / r)
      = Real.sqrt (2 * (1 - 1 / (1000 * r))) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have h1 : 1 ≤ Real.sqrt (2 * (1 - 1 / (1000 * (r : ℝ)))) :=
    Real.one_le_sqrt.mpr (by linarith)
  calc (1 : ℝ) ≤ Real.sqrt (2 * r) * Real.sqrt ((1 - 1 / (1000 * r)) / r) := hprod ▸ h1
    _ ≤ classIters r * Real.sqrt ((1 - 1 / (1000 * r)) / r) :=
        mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)

/-- The negative side of the amplification: `2((2m−1)² + 2) · u ≤ 1/3` for `m = ⌈√(2r)⌉`
and `u ≤ 1/(1000 r)`. -/
private lemma por_iters_neg {r : ℕ} (hr : 0 < r) {u : ℝ} (hu : u ≤ 1 / (1000 * r)) :
    2 * ((2 * (classIters r : ℝ) - 1) ^ 2 + 2) * u ≤ 1 / 3 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set s := Real.sqrt (2 * r) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  have hm : s ≤ classIters r := Nat.le_ceil _
  have hm' : (classIters r : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hs1 : 1 ≤ s := by nlinarith
  have h1 : (2 * (classIters r : ℝ) - 1) ^ 2 ≤ (2 * s + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (2 * (classIters r : ℝ) - 1) ^ 2 ≤ 10 * r + 5 := by
    nlinarith [sq_nonneg (s - 2)]
  have hru : (r : ℝ) * u ≤ 1 / 1000 := by
    rw [le_div_iff₀ (by positivity)] at hu
    nlinarith
  nlinarith


/-- The padded amplification budget: `4(L + (m−1)·2L) ≤ 8mL`. -/
private lemma por_amp_budget_le {L m : ℕ} (hm : 0 < m) :
    4 * (L + (m - 1) * (2 * L)) ≤ 8 * m * L := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith

/-- **One cost class**: the `r > 0` children of class `g` combined into a decision with
error `ε / G`, at cost `classReps G ε · 8⌈√(2r)⌉ · childReps r · 2^g`. -/
private lemma por_class {m : ℕ} {q : Fin m → ℕ} {P : Fin m → (ι → σ) → Bool → ℝ}
    {Pos Neg : Fin m → (ι → σ) → Prop}
    (hP : ∀ i, Realizes (id : (ι → σ) → ι → σ) (q i) (P i))
    (hT : ∀ i, IsPromiseLaw (P i) (Pos i) (Neg i) (1 / 3)) {ε : ℝ} (hε0 : 0 < ε) {G : ℕ}
    (hG : 0 < G) (g : ℕ) (hr : 0 < classSize q g) :
    ∃ D : (ι → σ) → Bool → ℝ,
      Realizes (id : (ι → σ) → ι → σ)
        (classReps G ε * (8 * classIters (classSize q g) * (childReps (classSize q g) * 2 ^ g)))
        D ∧
      (∀ a, (∃ i, costClass (q i) = g ∧ Pos i a) → D a false ≤ ε / G) ∧
      (∀ a, (∀ i, costClass (q i) = g → Neg i a) → D a true ≤ ε / G) := by
  set r := classSize q g with hr_def
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  -- each child: a majority of `childReps r` runs, error `1/(1000 r)`
  obtain ⟨M, hM, hMb⟩ : ∃ M : Fin m → (ι → σ) → Bool → ℝ,
      (∀ i, Realizes (id : (ι → σ) → ι → σ) (childReps r * q i) (M i)) ∧
      ∀ i a b, P i a (!b) ≤ 1 / 3 → M i a (!b) ≤ 1 / (1000 * r) := by
    choose M hM hMb using fun i => por_majority (hP i) (Nat.clog 2 (1000 * r))
    exact ⟨M, hM, fun i a b h => (hMb i a b h).trans (por_half_pow_clog_le hr)⟩
  have hMpos : ∀ i a, Pos i a → 1 - 1 / (1000 * r) ≤ M i a true := by
    intro i a ha
    have h1 := (hT i).1 a ha
    have h2 := por_bool_sum (hP i) a
    have h3 := hMb i a true (by simp only [Bool.not_true]; linarith)
    have h4 := por_bool_sum (hM i) a
    simp only [Bool.not_true] at h3
    linarith
  have hMneg : ∀ i a, Neg i a → M i a true ≤ 1 / (1000 * r) := by
    intro i a ha
    have h1 := (hT i).2 a ha
    have h2 := por_bool_sum (hP i) a
    exact hMb i a false (by simp only [Bool.not_false]; linarith)
  -- the uniform mixture over the class
  have hcard : Fintype.card {i : Fin m // costClass (q i) = g} = r := by
    rw [Fintype.card_subtype]; rfl
  have hcL : ∀ ω : {i : Fin m // costClass (q i) = g},
      childReps r * q ω.1 ≤ childReps r * 2 ^ g := by
    intro ω
    have h := Nat.le_pow_clog (b := 2) (by norm_num) (q ω.1 + 1)
    have hω : Nat.clog 2 (q ω.1 + 1) = g := ω.2
    rw [hω] at h
    exact Nat.mul_le_mul_left _ (by omega)
  have hU := por_mixture (c := fun ω : {i : Fin m // costClass (q i) = g} => childReps r * q ω.1)
    hcL (fun ω => hM ω.1) (by omega)
  rw [hcard] at hU
  have hUpos : ∀ a, (∃ i, costClass (q i) = g ∧ Pos i a) →
      (1 - 1 / (1000 * r)) / r
        ≤ ∑ ω : {i : Fin m // costClass (q i) = g}, (1 / (r : ℝ)) * M ω.1 a true := by
    rintro a ⟨i, hi, ha⟩
    have h1 := Finset.single_le_sum
      (f := fun ω : {i : Fin m // costClass (q i) = g} => (1 / (r : ℝ)) * M ω.1 a true)
      (s := Finset.univ) (fun ω _ => mul_nonneg (by positivity) ((hM ω.1).nonneg a true))
      (Finset.mem_univ ⟨i, hi⟩)
    have h2 := hMpos i a ha
    calc (1 - 1 / (1000 * r)) / r = (1 / (r : ℝ)) * (1 - 1 / (1000 * r)) := by ring
      _ ≤ (1 / (r : ℝ)) * M i a true := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := h1
  have hUneg : ∀ a, (∀ i, costClass (q i) = g → Neg i a) →
      ∑ ω : {i : Fin m // costClass (q i) = g}, (1 / (r : ℝ)) * M ω.1 a true
        ≤ 1 / (1000 * r) := by
    intro a ha
    calc ∑ ω : {i : Fin m // costClass (q i) = g}, (1 / (r : ℝ)) * M ω.1 a true
        ≤ ∑ _ω : {i : Fin m // costClass (q i) = g}, (1 / (r : ℝ)) * (1 / (1000 * r)) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hMneg ω.1 a (ha ω.1 ω.2)) (by positivity)
      _ = 1 / (1000 * r) := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          field_simp
  -- amplitude amplification with `⌈√(2r)⌉` iteration counts
  have hm' : 0 < classIters r := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨V, hV, hVb⟩ := por_amplify hU hm'
  have hV8 := por_realizes_mono hV (por_amp_budget_le (L := childReps r * 2 ^ g) hm')
  -- the class decision: a majority of `classReps G ε` runs
  obtain ⟨D, hD, hDb⟩ := por_majority hV8 ⌈Real.logb 2 (G / ε)⌉₊
  have hhalf := por_half_pow_classReps_le hG hε0
  refine ⟨D, hD, fun a ha => ?_, fun a ha => ?_⟩
  · have h1 := (hVb a).1 _ (by
      have : (0 : ℝ) < 1 - 1 / (1000 * r) := by
        have : 1 / (1000 * (r : ℝ)) ≤ 1 / 1000 :=
          one_div_le_one_div_of_le (by norm_num)
            (by linarith [(by exact_mod_cast hr : (1 : ℝ) ≤ r)])
        linarith
      positivity) (hUpos a ha) (por_one_le_iters_mul hr)
    have h2 := por_bool_sum hV8 a
    have h3 := hDb a true (by simp only [Bool.not_true]; linarith)
    simp only [Bool.not_true] at h3
    linarith
  · have h1 := (hVb a).2
    have h2 := por_iters_neg hr (hUneg a ha)
    have h3 := hDb a false (by simp only [Bool.not_false]; linarith)
    simp only [Bool.not_false] at h3
    linarith

/-! ### The OR of the classes -/

/-- **The OR of Boolean decisions**: realized at the sum of the costs, rejecting with the
product of the rejection probabilities. -/
private lemma por_or {b : ℕ → ℕ} {D : ℕ → (ι → σ) → Bool → ℝ}
    (hD : ∀ g, Realizes (id : (ι → σ) → ι → σ) (b g) (D g)) :
    ∀ n, ∃ Q : (ι → σ) → Bool → ℝ,
      Realizes (id : (ι → σ) → ι → σ) (∑ g ∈ Finset.range n, b g) Q ∧
        ∀ a, Q a false = ∏ g ∈ Finset.range n, D g a false
  | 0 => ⟨fun _ o => if o then 0 else 1,
      by rw [Finset.sum_range_zero]; exact por_realizes_false id, fun a => by simp⟩
  | n + 1 => by
    obtain ⟨Q, hQ, hQf⟩ := por_or hD n
    have h := (hQ.pair (hD n)).map (fun o : Bool × Bool => o.1 || o.2)
    refine ⟨_, by rw [Finset.sum_range_succ]; exact h, fun a => ?_⟩
    rw [Finset.prod_range_succ, ← hQf, Finset.sum_filter, Fintype.sum_prod_type]
    simp

/-- Weierstrass: a product of `n` numbers in `[1 − e, 1]` is at least `1 − n e`. -/
private lemma por_one_sub_le_prod {x : ℕ → ℝ} {e : ℝ} (he : 0 ≤ e) (h0 : ∀ g, 0 ≤ x g)
    (h1 : ∀ g, x g ≤ 1) (h : ∀ g, 1 - e ≤ x g) :
    ∀ n : ℕ, 1 - n * e ≤ ∏ g ∈ Finset.range n, x g
  | 0 => by simp
  | n + 1 => by
    have ih := por_one_sub_le_prod he h0 h1 h n
    rw [Finset.prod_range_succ]
    have hP0 : 0 ≤ ∏ g ∈ Finset.range n, x g := Finset.prod_nonneg fun g _ => h0 g
    have hP1 : ∏ g ∈ Finset.range n, x g ≤ 1 :=
      Finset.prod_le_one₀ (fun g _ => h0 g) fun g _ => h1 g
    push_cast
    nlinarith [mul_nonneg hP0 (sub_nonneg.mpr (h n)), mul_nonneg he (sub_nonneg.mpr hP1)]

/-- **Combining tests** [CGKLPZ26, Lemma 2.5]: the OR of `m` one-sided promise tests with
budgets `q i` and error `1/3` is a promise test with error `ε` for `∃ i, Pos i` versus
`∀ i, Neg i`, with `promiseOrBudget q ε` queries. -/
theorem exists_promiseOr {m : ℕ} {q : Fin m → ℕ} {P : Fin m → (ι → σ) → Bool → ℝ}
    {Pos Neg : Fin m → (ι → σ) → Prop}
    (hP : ∀ i, Realizes (id : (ι → σ) → ι → σ) (q i) (P i))
    (hT : ∀ i, IsPromiseLaw (P i) (Pos i) (Neg i) (1 / 3)) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ P' : (ι → σ) → Bool → ℝ,
      Realizes (id : (ι → σ) → ι → σ) (promiseOrBudget q ε) P' ∧
      IsPromiseLaw P' (fun a => ∃ i, Pos i a) (fun a => ∀ i, Neg i a) ε := by
  have hG : 0 < numClasses q := Nat.succ_pos _
  have hG' : (1 : ℝ) ≤ numClasses q := by exact_mod_cast hG
  have hεG : ε / numClasses q ≤ ε := div_le_self hε0.le hG'
  have hcls : ∀ g, ∃ D : (ι → σ) → Bool → ℝ,
      Realizes (id : (ι → σ) → ι → σ)
        (if classSize q g = 0 then 0 else classReps (numClasses q) ε *
          (8 * classIters (classSize q g) * (childReps (classSize q g) * 2 ^ g))) D ∧
      (∀ a, (∃ i, costClass (q i) = g ∧ Pos i a) → D a false ≤ ε / numClasses q) ∧
      (∀ a, (∀ i, costClass (q i) = g → Neg i a) → D a true ≤ ε / numClasses q) := by
    intro g
    by_cases h0 : classSize q g = 0
    · refine ⟨fun _ o => if o then 0 else 1, ?_, ?_,
        fun a _ => by simp only [↓reduceIte]; positivity⟩
      · simp only [h0, ite_true]
        exact por_realizes_false id
      · rintro a ⟨i, hi, -⟩
        have hmem : i ∈ Finset.univ.filter (fun i => costClass (q i) = g) := by simp [hi]
        have := Finset.card_pos.mpr ⟨i, hmem⟩
        rw [classSize] at h0
        omega
    · obtain ⟨D, hD, h1, h2⟩ := por_class hP hT hε0 hG g (Nat.pos_of_ne_zero h0)
      exact ⟨D, by simpa only [h0, ite_false] using hD, h1, h2⟩
  choose D hD hDpos hDneg using hcls
  obtain ⟨Q, hQ, hQf⟩ := por_or hD (numClasses q)
  have hD01 : ∀ g a, 0 ≤ D g a false ∧ D g a false ≤ 1 := fun g a =>
    ⟨(hD g).nonneg a false, by linarith [por_bool_sum (hD g) a, (hD g).nonneg a true]⟩
  refine ⟨Q, hQ, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨i, hi⟩ := ha
    have hg : costClass (q i) ∈ Finset.range (numClasses q) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Finset.le_sup (f := fun i => costClass (q i)) (Finset.mem_univ i)))
    have h1 := hDpos (costClass (q i)) a ⟨i, rfl, hi⟩
    have h2 : Q a false ≤ D (costClass (q i)) a false := by
      rw [hQf, ← Finset.mul_prod_erase _ _ hg]
      exact mul_le_of_le_one_right (hD01 _ a).1
        (Finset.prod_le_one₀ (fun g _ => (hD01 g a).1) fun g _ => (hD01 g a).2)
    have h3 := por_bool_sum hQ a
    linarith
  · have h1 := por_one_sub_le_prod (x := fun g => D g a false) (e := ε / numClasses q)
      (by positivity) (fun g => (hD01 g a).1) (fun g => (hD01 g a).2)
      (fun g => by linarith [hDneg g a (fun i _ => ha i), por_bool_sum (hD g) a])
      (numClasses q)
    rw [mul_div_cancel₀ _ (by positivity)] at h1
    rw [← hQf] at h1
    exact h1

end QuantumQueryComplexity
