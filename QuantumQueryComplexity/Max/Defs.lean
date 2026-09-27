import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Maximum finding: the function and its level counts

`maxFun x = ⊔ᵢ x i` for `x : ι → A` with `A` a linear order and `ι` a nonempty
finite index type.  This is the non-Boolean function whose adversary bound we
study; at `A = Bool` it is exactly `orN`.

We use `Finset.sup'` over `univ` rather than `Finset.max'`: `max'` takes a
`Finset A`, so stating it would force `(Finset.univ.image x).max'`, dragging in
`[DecidableEq A]` and an `image`-nonemptiness proof.  `sup'` ranges over `ι`
directly and needs neither.

Alongside it we define `cnt p x`, the number of coordinates of `x` on which a
`Bool`-valued predicate `p` holds, and the normalised indicator `wt p x`.
Predicates are `Bool`-valued rather than `Prop`-valued throughout this
development so that no `Decidable` instance ever has to be carried, matched, or
unified.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] {A : Type*} [LinearOrder A]

/-- The maximum of a tuple: `maxFun x = ⊔ᵢ x i`. -/
noncomputable def maxFun [Nonempty ι] (x : ι → A) : A :=
  Finset.univ.sup' Finset.univ_nonempty x

variable [Nonempty ι]

lemma le_maxFun (x : ι → A) (i : ι) : x i ≤ maxFun x :=
  Finset.le_sup' x (Finset.mem_univ i)

lemma exists_eq_maxFun (x : ι → A) : ∃ i, x i = maxFun x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  exact ⟨i, hi.symm⟩

lemma maxFun_le {x : ι → A} {b : A} (h : ∀ i, x i ≤ b) : maxFun x ≤ b :=
  Finset.sup'_le _ _ fun i _ => h i

/-- `maxFun` is characterised by the two conditions defining a maximum. -/
lemma maxFun_eq_iff {x : ι → A} {b : A} :
    maxFun x = b ↔ (∃ i, x i = b) ∧ ∀ i, x i ≤ b := by
  constructor
  · rintro rfl
    exact ⟨exists_eq_maxFun x, le_maxFun x⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (maxFun_le h) (le_maxFun x i)

/-! ## Level counts -/

/-- The number of coordinates of `x` on which the predicate `p` holds. -/
def cnt (p : A → Bool) (x : ι → A) : ℕ :=
  (Finset.univ.filter fun i => p (x i)).card

variable {p : A → Bool}

lemma cnt_eq_sum (x : ι → A) :
    (cnt p x : ℝ) = ∑ i, if p (x i) then 1 else 0 := by
  simp only [cnt]
  rw [Finset.card_filter]
  push_cast
  rfl

/-- If the cut holds at the maximum then some coordinate realises it, so the
count is positive.  This is what makes the division by `cnt` in the dual
solution harmless. -/
lemma cnt_pos_of_maxFun (x : ι → A) (h : p (maxFun x)) : 0 < cnt p x := by
  obtain ⟨i, hi⟩ := exists_eq_maxFun x
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
  exact h

lemma cnt_ne_zero_of_maxFun (x : ι → A) (h : p (maxFun x)) :
    (cnt p x : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (cnt_pos_of_maxFun x h).ne'

lemma one_le_cnt_of_maxFun (x : ι → A) (h : p (maxFun x)) :
    (1 : ℝ) ≤ (cnt p x : ℝ) := by
  exact_mod_cast cnt_pos_of_maxFun x h

/-! ## The normalised indicator of a cut -/

/-- The indicator of `{i | p (x i)}`, normalised to sum to `1`. -/
noncomputable def wt (p : A → Bool) (x : ι → A) (i : ι) : ℝ :=
  (if p (x i) then 1 else 0) / (cnt p x : ℝ)

lemma wt_eq_zero (x : ι → A) {i : ι} (h : p (x i) = false) : wt p x i = 0 := by
  simp [wt, h]

/-- The normalised indicator sums to `1` whenever the cut holds at the
maximum. -/
lemma sum_wt (x : ι → A) (h : p (maxFun x)) : (∑ i, wt p x i) = 1 := by
  simp only [wt]
  rw [← Finset.sum_div, ← cnt_eq_sum]
  exact div_self (cnt_ne_zero_of_maxFun x h)

/-- The squared `ℓ²` mass of the normalised indicator is `1 / cnt ≤ 1`. -/
lemma sum_wt_sq_le_one (x : ι → A) (h : p (maxFun x)) :
    (∑ i, wt p x i * wt p x i) ≤ 1 := by
  have hne := cnt_ne_zero_of_maxFun (p := p) x h
  have key : (∑ i, wt p x i * wt p x i) = 1 / (cnt p x : ℝ) := by
    have hsq : ∀ i : ι, wt p x i * wt p x i
        = (if p (x i) then (1 : ℝ) else 0) / ((cnt p x : ℝ) * (cnt p x : ℝ)) := by
      intro i
      simp only [wt, div_mul_div_comm]
      by_cases hi : p (x i) <;> simp [hi]
    simp only [hsq]
    rw [← Finset.sum_div, ← cnt_eq_sum]
    field_simp
  rw [key, div_le_one (lt_of_lt_of_le zero_lt_one (one_le_cnt_of_maxFun x h))]
  exact one_le_cnt_of_maxFun x h

end QuantumQueryComplexity
