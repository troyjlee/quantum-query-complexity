import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Tail
set_option synthInstance.maxSize 1600

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Folding the pair compiler: tuples, majority, and joint correctness

The `k`-fold iteration of `Realizes.pair`, and its two consumers:

* **`amplify`** — majority over `k` independent runs of a Boolean algorithm.
  The record statistics are an exact product, so the failure probability is
  the pattern count `sum_prod_majority_le`: at per-run error `ε` the
  amplified error is `2^k·ε^{⌈k/2⌉}`; at the native `ε = 1/16` this is
  `≤ 2^{-k}`.
* **`exists_tuple_computes`** — `B` Boolean algorithms joined into one
  computing the tuple, with error `∑ εᵢ` (the product of the diagonal
  probabilities, bounded by Weierstrass).

Costs add exactly throughout — the bank-swap compiler has no uncompute
overhead.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## The base and the cons step -/

/-- Prepending a coordinate to a Boolean tuple. -/
def finConsEquiv (k : ℕ) : Bool × (Fin k → Bool) ≃ (Fin (k + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun y := (y 0, fun j => y j.succ)
  left_inv := by
    rintro ⟨b, t⟩
    refine Prod.ext (by simp) (funext fun j => ?_)
    simp
  right_inv := by
    intro y
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- The trivial realization: no runs, the constant distribution `1` on the
empty tuple. -/
lemma realizes_zero_tuple (read : X → ι → σ) :
    Realizes read 0 (fun (_ : X) (_ : Fin 0 → Bool) => (1 : ℝ)) := by
  classical
  refine ⟨Unit, inferInstance, inferInstance,
    constAlg ι σ (fun j : Fin 0 => j.elim0), ?_⟩
  intro x o
  have ho : o = fun j : Fin 0 => j.elim0 := funext fun j => j.elim0
  subst ho
  simp [QAlg.prob, constAlg]

/-- **The `k`-fold product realization**: costs add, distributions
multiply. -/
theorem Realizes.fold {read : X → ι → σ} :
    ∀ (k : ℕ) (q : Fin k → ℕ) (P : Fin k → X → Bool → ℝ),
    (∀ j, Realizes read (q j) (P j)) →
    Realizes read (∑ j, q j)
      (fun x (y : Fin k → Bool) => ∏ j, P j x (y j)) := by
  intro k
  induction k with
  | zero =>
      intro q P _
      rw [show (∑ j : Fin 0, q j) = 0 from by simp]
      exact (realizes_zero_tuple read).congr fun x y => by simp
  | succ k ih =>
      intro q P h
      have hfold := ih (fun j => q j.succ) (fun j => P j.succ)
        (fun j => h j.succ)
      have hpair := (h 0).pair hfold
      have hmapped := hpair.map_equiv (finConsEquiv k)
      rw [Fin.sum_univ_succ]
      refine hmapped.congr fun x y => ?_
      rw [show (finConsEquiv k).symm y = (y 0, fun j => y j.succ) from rfl]
      rw [Fin.prod_univ_succ]

/-- Probabilities sum to one. -/
lemma QAlg.sum_prob {O W : Type} [DecidableEq O] [Fintype O] [Fintype W]
    [DecidableEq W] (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    ∑ o, A.prob a t o = 1 := by
  show (∑ o, qProb A.readout (A.state a t) o) = 1
  rw [sum_qProb, A.state_isQState]

/-- The full pattern sum of a product distribution is the product of the
totals. -/
lemma sum_pattern_prod {k : ℕ} (p : Bool → ℝ) :
    (∑ y : Fin k → Bool, ∏ j, p (y j)) = (∑ b, p b) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← Equiv.sum_comp (finConsEquiv k)
        (fun y => ∏ j, p (y j)), Fintype.sum_prod_type]
      rw [show (∑ b, ∑ t : Fin k → Bool, ∏ j, p (finConsEquiv k (b, t) j))
          = ∑ b, ∑ t : Fin k → Bool, p b * ∏ j, p (t j) from by
        refine Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun t _ => ?_
        rw [show (finConsEquiv k (b, t)) = Fin.cons b t from rfl,
          Fin.prod_univ_succ]
        simp]
      rw [show (∑ b, ∑ t : Fin k → Bool, p b * ∏ j, p (t j))
          = ∑ b, p b * ∑ t : Fin k → Bool, ∏ j, p (t j) from
        Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]]
      rw [← Finset.sum_mul, ih, pow_succ]
      ring

/-! ## Majority amplification -/

/-- The majority vote. -/
def majVote (k : ℕ) (y : Fin k → Bool) : Bool :=
  decide (k < 2 * (Finset.univ.filter (fun j => y j = true)).card)

/-- A wrong majority has at least `⌈k/2⌉` wrong votes. -/
lemma le_card_wrong_of_majVote_ne {k : ℕ} {y : Fin k → Bool} {b : Bool}
    (h : majVote k y ≠ b) :
    (k + 1) / 2 ≤ (Finset.univ.filter (fun j => y j ≠ b)).card := by
  have hsplit : (Finset.univ.filter (fun j => y j = true)).card
      + (Finset.univ.filter (fun j => ¬(y j = true))).card = k := by
    rw [Finset.card_filter_add_card_filter_not (fun j => y j = true),
      Finset.card_univ, Fintype.card_fin]
  cases b with
  | true =>
      have hmaj : ¬(k < 2 * (Finset.univ.filter
          (fun j => y j = true)).card) := by
        intro hcon
        exact h (by simp [majVote, hcon])
      have hwrong : (Finset.univ.filter (fun j => y j ≠ true)).card
          = (Finset.univ.filter (fun j => ¬(y j = true))).card := rfl
      rw [hwrong]
      omega
  | false =>
      have hmaj : k < 2 * (Finset.univ.filter
          (fun j => y j = true)).card := by
        by_contra hcon
        exact h (by simp [majVote, hcon])
      have hwrong : (Finset.univ.filter (fun j => y j ≠ false)).card
          = (Finset.univ.filter (fun j => y j = true)).card := by
        congr 1
        ext j
        simp [Finset.mem_filter]
      rw [hwrong]
      omega

/-- **Majority amplification.**  `k` independent runs of a Boolean algorithm
with error `ε ≤ 1` compute the same function with error `2^k·ε^{⌈k/2⌉}`, at
`k` times the cost. -/
theorem amplify {read : X → ι → σ} {f : X → Bool} {q : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hex : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W), ComputesWithErrorOn A q read f ε) (k : ℕ) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ Bool W'),
      ComputesWithErrorOn A' (k * q) read f
        (2 ^ k * ε ^ ((k + 1) / 2)) := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := hex
  -- the base realization
  have hbase : Realizes read q (fun x b => A.prob (read x) q b) :=
    ⟨W, hW, hW', A, fun _ _ => rfl⟩
  have hfold := Realizes.fold k (fun _ => q)
    (fun _ x b => A.prob (read x) q b) (fun _ => hbase)
  have hcost : (∑ _j : Fin k, q) = k * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  have hmaj := hfold.map (majVote k)
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hmaj
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (f x)]
  -- the correct-majority mass is the total minus the wrong-majority mass
  have htotal : (∑ y : Fin k → Bool, ∏ _j : Fin k,
      A.prob (read x) q (y _j)) = 1 := by
    rw [show (∑ y : Fin k → Bool, ∏ j : Fin k, A.prob (read x) q (y j))
        = (∑ b, A.prob (read x) q b) ^ k from
      sum_pattern_prod (fun b => A.prob (read x) q b),
      A.sum_prob, one_pow]
  have hsplitsum : (∑ y ∈ Finset.univ.filter
        (fun y : Fin k → Bool => majVote k y = f x),
      ∏ j, A.prob (read x) q (y j))
      + (∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => ¬(majVote k y = f x)),
        ∏ j, A.prob (read x) q (y j)) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact htotal
  -- the wrong-majority mass is small
  have hwrongmass : (∑ y ∈ Finset.univ.filter
        (fun y : Fin k → Bool => ¬(majVote k y = f x)),
      ∏ j, A.prob (read x) q (y j))
      ≤ 2 ^ k * ε ^ ((k + 1) / 2) := by
    have hsub : Finset.univ.filter
        (fun y : Fin k → Bool => ¬(majVote k y = f x))
        ⊆ Finset.univ.filter (fun y : Fin k → Bool =>
          (k + 1) / 2 ≤ (Finset.univ.filter (fun j => y j ≠ f x)).card) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact le_card_wrong_of_majVote_ne hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun y _ _ => Finset.prod_nonneg fun j _ => A.prob_nonneg _ _ _) ?_
    refine sum_prod_majority_le hε0 hε1 (fun _ b => A.prob (read x) q b)
      (fun _ => f x) (fun _ b => A.prob_nonneg _ _ _)
      (fun _ b => A.prob_le_one _ _ _) fun _ => ?_
    -- the wrong value's probability is at most `ε`
    have hsum2 : A.prob (read x) q (f x)
        + A.prob (read x) q (!(f x)) = 1 := by
      have := A.sum_prob (read x) q
      rw [Fintype.sum_bool] at this
      cases hfx : f x <;> simp [hfx] at this ⊢ <;> linarith
    have := hA x
    linarith
  linarith [hsplitsum, hwrongmass]

/-! ## Joining Boolean algorithms into a tuple -/

/-- Weierstrass: the product of near-one probabilities is near one. -/
lemma one_sub_sum_le_prod {k : ℕ} (p e : Fin k → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (he0 : ∀ j, 0 ≤ e j)
    (h : ∀ j, 1 - e j ≤ p j) :
    1 - (∑ j, e j) ≤ ∏ j, p j := by
  induction k with
  | zero => simp
  | succ k ih =>
      have htail := ih (fun j => p j.succ) (fun j => e j.succ)
        (fun j => hp0 j.succ) (fun j => hp1 j.succ) (fun j => he0 j.succ)
        (fun j => h j.succ)
      have hS0 : (0 : ℝ) ≤ ∑ j : Fin k, e j.succ :=
        Finset.sum_nonneg fun j _ => he0 j.succ
      have hT0 : (0 : ℝ) ≤ ∏ j : Fin k, p j.succ :=
        Finset.prod_nonneg fun j _ => hp0 j.succ
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      rcases le_or_gt (1 - ∑ j : Fin k, e j.succ) 0 with hneg | hpos
      · have h1 : 1 - (e 0 + ∑ j : Fin k, e j.succ) ≤ 0 := by
          linarith [he0 0]
        exact le_trans h1 (mul_nonneg (hp0 0) hT0)
      · have h1 : p 0 * (1 - ∑ j : Fin k, e j.succ)
            ≤ p 0 * ∏ j : Fin k, p j.succ :=
          mul_le_mul_of_nonneg_left htail (hp0 0)
        nlinarith [h 0, he0 0, hp1 0]

/-- **The tuple compiler**: `B` Boolean algorithms joined into one computing
the tuple function, at the sum of the costs and the sum of the errors. -/
theorem exists_tuple_computes {read : X → ι → σ} {B : ℕ}
    {g : Fin B → X → Bool} {q : Fin B → ℕ} {ε : Fin B → ℝ}
    (hε0 : ∀ i, 0 ≤ ε i)
    (hex : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W), ComputesWithErrorOn A (q i) read (g i) (ε i)) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ (Fin B → Bool) W'),
      ComputesWithErrorOn A' (∑ i, q i) read (fun x i => g i x)
        (∑ i, ε i) := by
  classical
  choose W hW hW' A hA using hex
  have hbase : ∀ i, Realizes read (q i)
      (fun x b => (A i).prob (read x) (q i) b) := fun i =>
    ⟨W i, hW i, hW' i, A i, fun _ _ => rfl⟩
  have hfold := Realizes.fold B q
    (fun i x b => (A i).prob (read x) (q i) b) hbase
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hfold
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (fun i => g i x)]
  refine le_trans ?_ (le_of_eq rfl)
  refine one_sub_sum_le_prod _ ε
    (fun i => (A i).prob_nonneg _ _ _)
    (fun i => (A i).prob_le_one _ _ _) hε0 fun i => hA i x

end QuantumQueryComplexity
