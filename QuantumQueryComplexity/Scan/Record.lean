import QuantumQueryComplexity.Scan.Max
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The record lemma

Over a uniformly random scan order, the probability that step `t` sets a strict
record is at most `1 / (t + 1)`.

No bijection onto a quotient is needed.  For each position `s ≤ t` let
`domSet x t s` be the orders whose position-`s` coordinate *strictly dominates*
all the others at positions `≤ t`.  Then

* the `domSet x t s` for `s ≤ t` are **pairwise disjoint** — a strict dominator
  is unique;
* they are **equinumerous**, by composing an order with the transposition of
  positions `s` and `t`;
* `domSet x t t` is exactly the event "step `t` is a strict record".

So `(t + 1)` disjoint sets of equal size fit inside all the orders, giving
`(t + 1) * |record event| ≤ n!`.  Ties are handled for free: if the maximum
over the first `t + 1` positions is attained twice, *no* order is counted, which
only helps.

This is the one place where randomising the scan order earns its keep.  For a
fixed order an increasing input sets a record at every step.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [LinearOrder A]

/-- A scan order: a bijection of the coordinates onto positions. -/
abbrev Order (ι : Type*) [Fintype ι] := ι ≃ Fin (Fintype.card ι)

/-- The orders whose position-`s` coordinate strictly dominates every other
coordinate at a position `≤ t`. -/
def domSet (x : ι → A) (t s : Fin (Fintype.card ι)) : Finset (Order ι) :=
  Finset.univ.filter fun e =>
    ∀ s' : Fin (Fintype.card ι), s' ≤ t → s' ≠ s → x (e.symm s') < x (e.symm s)

lemma mem_domSet {x : ι → A} {t s : Fin (Fintype.card ι)} {e : Order ι} :
    e ∈ domSet x t s ↔ ∀ s' : Fin (Fintype.card ι), s' ≤ t → s' ≠ s →
      x (e.symm s') < x (e.symm s) := by
  simp [domSet]

/-- A strict dominator is unique, so the sets are pairwise disjoint. -/
lemma domSet_disjoint (x : ι → A) (t : Fin (Fintype.card ι))
    {s₁ s₂ : Fin (Fintype.card ι)} (hne : s₁ ≠ s₂) (h1 : s₁ ≤ t) (h2 : s₂ ≤ t) :
    Disjoint (domSet x t s₁) (domSet x t s₂) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  have k1 := (mem_domSet.1 he₁) s₂ h2 (Ne.symm hne)
  have k2 := (mem_domSet.1 he₂) s₁ h1 hne
  exact absurd k1 (not_lt.2 k2.le)

/-- Swapping positions `s` and `t` matches the two dominance events. -/
lemma card_domSet_eq (x : ι → A) {t s : Fin (Fintype.card ι)} (hs : s ≤ t) :
    (domSet x t s).card = (domSet x t t).card := by
  classical
  refine Finset.card_nbij' (fun e => e.trans (Equiv.swap s t))
    (fun e => e.trans (Equiv.swap s t)) ?_ ?_ ?_ ?_
  · -- forward: dominance at `s` becomes dominance at `t`
    intro e he
    simp only [Finset.mem_coe] at he ⊢
    rw [mem_domSet] at he ⊢
    intro s' hs' hne
    have hswt : (Equiv.swap s t) t = s := Equiv.swap_apply_right s t
    have hkey : ∀ u : Fin (Fintype.card ι), u ≤ t → u ≠ t →
        (Equiv.swap s t) u ≤ t ∧ (Equiv.swap s t) u ≠ s := by
      intro u hu hut
      by_cases hus : u = s
      · rw [hus, Equiv.swap_apply_left]
        exact ⟨le_rfl, fun h => hut (hus.trans h.symm)⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hus hut]
        exact ⟨hu, hus⟩
    obtain ⟨hle, hnes⟩ := hkey s' hs' hne
    have := he ((Equiv.swap s t) s') hle hnes
    simpa [Equiv.symm_trans_apply, Equiv.symm_swap, hswt] using this
  · -- backward: the same map, since the transposition is an involution
    intro e he
    simp only [Finset.mem_coe] at he ⊢
    rw [mem_domSet] at he ⊢
    intro s' hs' hne
    have hsws : (Equiv.swap s t) s = t := Equiv.swap_apply_left s t
    have hkey : ∀ u : Fin (Fintype.card ι), u ≤ t → u ≠ s →
        (Equiv.swap s t) u ≤ t ∧ (Equiv.swap s t) u ≠ t := by
      intro u hu hus
      by_cases hut : u = t
      · rw [hut, Equiv.swap_apply_right]
        exact ⟨hs, fun h => hus (hut.trans h.symm)⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hus hut]
        exact ⟨hu, hut⟩
    obtain ⟨hle, hnet⟩ := hkey s' hs' hne
    have := he ((Equiv.swap s t) s') hle hnet
    simpa [Equiv.symm_trans_apply, Equiv.symm_swap, hsws] using this
  · intro e _
    simp [Equiv.trans_assoc]
  · intro e _
    simp [Equiv.trans_assoc]

/-- **The record bound in counting form.** -/
lemma card_domSet_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (domSet x t t).card ≤ Fintype.card (Order ι) := by
  classical
  have hdisj : ((Finset.Iic t : Finset (Fin (Fintype.card ι))) : Set _).PairwiseDisjoint
      (fun s => domSet x t s) := by
    intro s₁ h1 s₂ h2 hne
    exact domSet_disjoint x t hne (Finset.mem_Iic.1 h1) (Finset.mem_Iic.1 h2)
  have hcard : ((Finset.Iic t).biUnion fun s => domSet x t s).card
      = ∑ s ∈ Finset.Iic t, (domSet x t s).card :=
    Finset.card_biUnion fun s₁ h1 s₂ h2 hne =>
      domSet_disjoint x t hne (Finset.mem_Iic.1 h1) (Finset.mem_Iic.1 h2)
  have hconst : ∑ s ∈ Finset.Iic t, (domSet x t s).card
      = ∑ _s ∈ Finset.Iic t, (domSet x t t).card :=
    Finset.sum_congr rfl fun s hs => card_domSet_eq x (Finset.mem_Iic.1 hs)
  calc ((t : ℕ) + 1) * (domSet x t t).card
      = ∑ _s ∈ Finset.Iic t, (domSet x t t).card := by
        rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
    _ = ((Finset.Iic t).biUnion fun s => domSet x t s).card := by
        rw [hcard, hconst]
    _ ≤ Fintype.card (Order ι) := Finset.card_le_univ _

/-! ## Identifying the record event -/

lemma isRecord_eq_true_iff (x : ι → A) (e : Order ι) (i : ι) :
    isRecord (⇑e) x i = true ↔ ∀ j : ι, e j < e i → x j < x i := by
  rw [isRecord, decide_eq_true_iff, runBefore, Finset.sup_lt_iff (by simp)]
  constructor
  · intro h j hj
    exact_mod_cast h j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  · intro h j hj
    exact_mod_cast h j (by simpa [beforeSet] using hj)

/-- **The record event is exactly the top dominance set.** -/
lemma isRecord_iff_mem_domSet (x : ι → A) (e : Order ι)
    (t : Fin (Fintype.card ι)) :
    isRecord (⇑e) x (e.symm t) = true ↔ e ∈ domSet x t t := by
  rw [isRecord_eq_true_iff, mem_domSet]
  constructor
  · intro h s' hs' hne
    refine h (e.symm s') ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact lt_of_le_of_ne hs' hne
  · intro h j hj
    rw [Equiv.apply_symm_apply] at hj
    have := h (e j) (le_of_lt hj) (ne_of_lt hj)
    rwa [Equiv.symm_apply_apply] at this

/-- **The record lemma.**  At most a `1/(t+1)` fraction of scan orders make
step `t` a strict record. -/
theorem card_record_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) *
        (Finset.univ.filter fun e : Order ι =>
          isRecord (⇑e) x (e.symm t) = true).card
      ≤ Fintype.card (Order ι) := by
  classical
  have : (Finset.univ.filter fun e : Order ι =>
      isRecord (⇑e) x (e.symm t) = true) = domSet x t t := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRecord_iff_mem_domSet x e t
  rw [this]
  exact card_domSet_mul_le x t

end QuantumQueryComplexity
