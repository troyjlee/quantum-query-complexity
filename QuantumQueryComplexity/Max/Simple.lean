import QuantumQueryComplexity.Max.Staircase
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The one-coordinate-per-value staircase

The simplest staircase takes one coordinate per alphabet value: the coordinate
`c` carries the cut `c ≤ ·`, the row `a j` is the indicator of `{c | j < c}`, and
the column `G k` is the indicator of `{k}`.  The factorization identity is then
just `∑ c, [j < c] * [c = k] = [j < k]`.

Its row mass is `m = |A|` and its column mass is `1`, so it gives

  `advPM maxFun ≤ 2 √(n m)`.

This already beats the trivial `n` bound whenever `m < n`, and — more to the
point — it exercises the whole pipeline of `QuantumQueryComplexity/Max/Staircase.lean` on a
staircase whose combinatorics are a one-liner.  `QuantumQueryComplexity/Max/Dyadic.lean`
replaces `m` by `⌈log₂ m⌉²` in the same slot.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]

/-- One coordinate per alphabet value: coordinate `c` cuts at `c`. -/
def simpleStaircase : Staircase A A where
  up c v := decide (c ≤ v)
  up_mono := fun _c _v _w hvw hv => by
    simp only [decide_eq_true_eq] at hv ⊢
    exact hv.trans hvw
  a j c := if j < c then 1 else 0
  G k c := if c = k then 1 else 0
  a_supp j c h := by
    have hjc : j < c := by
      by_contra hc
      rw [if_neg hc] at h
      exact h rfl
    exact decide_eq_false_iff_not.mpr (not_le.mpr hjc)
  G_supp k c h := by
    have hck : c = k := by
      by_contra hc
      rw [if_neg hc] at h
      exact h rfl
    subst hck
    simp
  pairing j k hjk := by
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one, if_pos hjk]
    · intro c _ hc
      rw [if_neg hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h

@[simp] lemma simpleStaircase_a (j c : A) :
    (simpleStaircase : Staircase A A).a j c = if j < c then 1 else 0 := rfl

@[simp] lemma simpleStaircase_G (k c : A) :
    (simpleStaircase : Staircase A A).G k c = if c = k then 1 else 0 := rfl

/-- The row mass is the number of values above `j`, hence at most `|A|`. -/
lemma simpleStaircase_a_sq_le (j : A) :
    (∑ c, (simpleStaircase : Staircase A A).a j c
        * (simpleStaircase : Staircase A A).a j c)
      ≤ (Fintype.card A : ℝ) := by
  have hsq : ∀ c : A, (simpleStaircase : Staircase A A).a j c
      * (simpleStaircase : Staircase A A).a j c = if j < c then (1 : ℝ) else 0 := by
    intro c
    simp only [simpleStaircase_a]
    by_cases h : j < c <;> simp [h]
  simp only [hsq]
  calc (∑ c : A, if j < c then (1 : ℝ) else 0) ≤ ∑ _c : A, (1 : ℝ) :=
      Finset.sum_le_sum fun c _ => by by_cases h : j < c <;> simp [h]
    _ = (Fintype.card A : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ]

/-- The column mass is exactly `1`: `G k` is a single indicator. -/
lemma simpleStaircase_G_sq_le (k : A) :
    (∑ c, (simpleStaircase : Staircase A A).G k c
        * (simpleStaircase : Staircase A A).G k c) ≤ (1 : ℝ) := by
  have hsq : ∀ c : A, (simpleStaircase : Staircase A A).G k c
      * (simpleStaircase : Staircase A A).G k c = if c = k then (1 : ℝ) else 0 := by
    intro c
    simp only [simpleStaircase_G]
    by_cases h : c = k <;> simp [h]
  simp only [hsq]
  rw [Finset.sum_ite_eq' Finset.univ k (fun _ => (1 : ℝ))]
  simp

/-- **`ADV±(MAX) ≤ 2√(n m)`** for an `n`-tuple over an `m`-element alphabet. -/
theorem advPM_maxFun_le_two_sqrt_card_mul [Nonempty A] :
    advPM (maxFun : (ι → A) → A)
      ≤ 2 * Real.sqrt ((Fintype.card ι : ℝ) * (Fintype.card A : ℝ)) := by
  have hA : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := advPM_maxFun_le (ι := ι) (simpleStaircase : Staircase A A)
    simpleStaircase_a_sq_le simpleStaircase_G_sq_le hA one_pos
  rwa [mul_one] at h

end QuantumQueryComplexity
