import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The two counting bounds of the independent-run analysis

Pure finite probability, stated over an arbitrary weight; no quantum imports.

* `sum_filter_ne_le_sum_coord` — **the union bound over coordinates**: any
  weight of the patterns different from a target is at most the sum over
  coordinates of the weight of the patterns wrong at that coordinate.
  (A standalone utility, currently unused: the tuple join ended up using
  Weierstrass on the diagonal instead, and plurality amplification
  (Milestone H, `Plurality.lean`) uses the sharper exponential-moment
  argument `sum_prod_tail_le` rather than a union bound.)
* `sum_prod_majority_le` — **the majority tail**: if each coordinate's wrong
  value carries probability at most `ε ≤ 1`, the product weight of the
  patterns with at least `t` wrong coordinates is at most `2^k·εᵗ`.  With
  per-run error `1/16` and `t = ⌈k/2⌉` this is `≤ 2^{-k}` — no Chernoff
  bound and no independence formalism: the product structure is supplied
  exactly by the bank-swap compiler, and the tail is one count over
  patterns.
* `sum_prod_tail_le` — **the exponential-moment tail** (moved here from `Plurality.lean`, so
  that circuit utilities can use it without the lower-bound development): the weight of the
  records with at least `t` wrong coordinates is at most `(1 + ε)^k / 2^t`.  Unlike the
  majority tail it decays at base error `1/3`: `(4/3)^k / 2^{k/2} = (8/9)^{k/2}`.
-/

namespace QuantumQueryComplexity

/-- **The union bound over coordinates**: every pattern different from `b` is
wrong somewhere, so its weight is charged to some coordinate. -/
lemma sum_filter_ne_le_sum_coord {k : ℕ} (w : (Fin k → Bool) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (b : Fin k → Bool) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b), w y)
      ≤ ∑ j : Fin k, ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => y j ≠ b j), w y := by
  have hite : ∀ (y : Fin k → Bool) (j : Fin k),
      (0 : ℝ) ≤ if y j ≠ b j then w y else 0 := by
    intro y j
    by_cases h : y j ≠ b j <;> simp [h, hw y]
  have hle : ∀ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b),
      w y ≤ ∑ j : Fin k, (if y j ≠ b j then w y else 0) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ b j := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hy (funext fun j => not_not.mp (hcon j))
    calc w y = ∑ l ∈ ({j} : Finset (Fin k)),
          (if y l ≠ b l then w y else 0) := by simp [hj]
      _ ≤ ∑ l : Fin k, (if y l ≠ b l then w y else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun l _ _ => hite y l
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b), w y)
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b),
          ∑ j : Fin k, (if y j ≠ b j then w y else 0) :=
        Finset.sum_le_sum hle
    _ ≤ ∑ y : Fin k → Bool, ∑ j : Fin k, (if y j ≠ b j then w y else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun y _ _ => Finset.sum_nonneg fun j _ => hite y j
    _ = ∑ j : Fin k, ∑ y : Fin k → Bool, (if y j ≠ b j then w y else 0) :=
        Finset.sum_comm
    _ = ∑ j : Fin k, ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => y j ≠ b j), w y := by
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm

/-- **The majority tail**: patterns with at least `t` wrong coordinates carry
product weight at most `2^k·εᵗ`. -/
lemma sum_prod_majority_le {k t : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : Fin k → Bool → ℝ) (b : Fin k → Bool)
    (hp0 : ∀ j y, 0 ≤ p j y) (hp1 : ∀ j y, p j y ≤ 1)
    (hpe : ∀ j, p j (!(b j)) ≤ ε) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
        t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card),
      ∏ j, p j (y j))
      ≤ 2 ^ k * ε ^ t := by
  have hterm : ∀ y : Fin k → Bool,
      t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card →
      (∏ j, p j (y j)) ≤ ε ^ t := by
    intro y hy
    set S := Finset.univ.filter (fun j : Fin k => y j ≠ b j) with hS
    have hsplit : (∏ j, p j (y j))
        = (∏ j ∈ S, p j (y j)) * ∏ j ∈ Sᶜ, p j (y j) :=
      (Finset.prod_mul_prod_compl S _).symm
    have h1 : (∏ j ∈ S, p j (y j)) ≤ ε ^ S.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun j _ => hp0 j _) fun j hj => ?_
      have hne : y j ≠ b j := by
        simpa [hS] using (Finset.mem_filter.mp hj).2
      have hval : y j = !(b j) := by
        cases hb : b j <;> cases hyj : y j <;> simp_all
      rw [hval]
      exact hpe j
    have h2 : (∏ j ∈ Sᶜ, p j (y j)) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => hp0 j _) (fun j _ => hp1 j _)
    have h3 : ε ^ S.card ≤ ε ^ t := pow_le_pow_of_le_one hε0 hε1 hy
    have hS0 : (0 : ℝ) ≤ ε ^ S.card := pow_nonneg hε0 _
    calc (∏ j, p j (y j))
        = (∏ j ∈ S, p j (y j)) * ∏ j ∈ Sᶜ, p j (y j) := hsplit
      _ ≤ ε ^ S.card * 1 := by
          refine mul_le_mul h1 h2 ?_ hS0
          exact Finset.prod_nonneg fun j _ => hp0 j _
      _ ≤ ε ^ t := by rw [mul_one]; exact h3
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
          t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card),
        ∏ j, p j (y j))
      ≤ ∑ _y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
          t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card), ε ^ t := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact hterm y (by simpa using (Finset.mem_filter.mp hy).2)
    _ ≤ ∑ _y : Fin k → Bool, ε ^ t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => pow_nonneg hε0 t
    _ = 2 ^ k * ε ^ t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

section ExpMoment

variable {O : Type} [Fintype O] [DecidableEq O]

/-! ## The exponential-moment tail -/

/-- The number of coordinates at which the record `y` differs from `b`. -/
def wrongCount {k : ℕ} (y b : Fin k → O) : ℕ :=
  (Finset.univ.filter (fun j => y j ≠ b j)).card

lemma prod_ite_eq_two_pow_wrongCount {k : ℕ} (y b : Fin k → O) :
    (∏ j, (if y j ≠ b j then (2 : ℝ) else 1)) = 2 ^ wrongCount y b := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl

/-- **The exponential-moment tail.**  If each coordinate's wrong values carry
probability at most `ε`, the product weight of the records with at least `t`
wrong coordinates, times `2^t`, is at most `(1 + ε)^k`: the weight of
`2^{wrong}` factorizes coordinatewise as `∏ (1 + Pr[wrong]) ≤ (1 + ε)^k`,
and `2^t ≤ 2^{wrong}` on the tail. -/
theorem sum_prod_tail_le {k t : ℕ} {ε : ℝ}
    (p : Fin k → O → ℝ) (b : Fin k → O)
    (hp0 : ∀ j o, 0 ≤ p j o) (hp1 : ∀ j, ∑ o, p j o ≤ 1)
    (hpe : ∀ j, ∑ o ∈ Finset.univ.filter (fun o => o ≠ b j), p j o ≤ ε) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
        ∏ j, p j (y j)) * 2 ^ t
      ≤ (1 + ε) ^ k := by
  have hm0 : ∀ (j : Fin k) (o : O), (0 : ℝ) ≤ if o ≠ b j then 2 else 1 := by
    intro j o
    split_ifs <;> norm_num
  have hfactor : ∀ j : Fin k,
      (∑ o, p j o * (if o ≠ b j then (2 : ℝ) else 1)) ≤ 1 + ε := by
    intro j
    have hsplit : ∀ o, p j o * (if o ≠ b j then (2 : ℝ) else 1)
        = p j o + (if o ≠ b j then p j o else 0) := by
      intro o
      split_ifs <;> ring
    simp only [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    exact add_le_add (hp1 j) (hpe j)
  have hstep : ∀ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
      (∏ j, p j (y j)) * 2 ^ t
        ≤ ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) := by
    intro y hy
    have hy' : t ≤ wrongCount y b := (Finset.mem_filter.mp hy).2
    rw [Finset.prod_mul_distrib, prod_ite_eq_two_pow_wrongCount]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hy')
      (Finset.prod_nonneg fun j _ => hp0 j _)
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          ∏ j, p j (y j)) * 2 ^ t
      = ∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          (∏ j, p j (y j)) * 2 ^ t := Finset.sum_mul _ _ _
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ y : Fin k → O, ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun y _ _ => Finset.prod_nonneg fun j _ => mul_nonneg (hp0 j _) (hm0 j _)
    _ = ∏ j, ∑ o, p j o * (if o ≠ b j then (2 : ℝ) else 1) :=
        (Fintype.prod_sum fun j o => p j o * (if o ≠ b j then (2 : ℝ) else 1)).symm
    _ ≤ ∏ _j : Fin k, (1 + ε) :=
        Finset.prod_le_prod₀
          (fun j _ => Finset.sum_nonneg fun o _ => mul_nonneg (hp0 j o) (hm0 j o))
          (fun j _ => hfactor j)
    _ = (1 + ε) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ExpMoment

end QuantumQueryComplexity
