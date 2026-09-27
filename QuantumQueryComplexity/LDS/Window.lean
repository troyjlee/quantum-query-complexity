import QuantumQueryComplexity.LDS.Defs
import QuantumQueryComplexity.ED.Main
import QuantumQueryComplexity.Promise.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Windowed distinctness duals

The only expensive leaves of the whole longest-distinct-substring
construction are the tests "is the window `[i, j]` distinct?".  Such a test
*is* element distinctness on the window: a dual solution for `edFun` on the
index type `Win i j` pulls back along the inclusion `Win i j ↪ Fin n` at no
cost (`HasDual.pullback` — freezing the coordinates outside the window is
free), and the output recoding `[distinct] = ¬ edFun` is free as well
(`HasDual.ofKer` sees only the level sets).  So

  **`hasDual_isDistinct`** — the test costs `8 · (j - i + 1)^{2/3}`,

uniformly in `n` and in the alphabet. Binary search uses `⌈log₂ s⌉` of
these anchors, one per level.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The positions of the window `[i, j]`, as an index type. -/
abbrev Win (i j : Fin n) : Type := {p : Fin n // p ∈ Finset.Icc i j}

lemma card_win (i j : Fin n) : Fintype.card (Win i j) = winLen i j := by
  rw [Fintype.card_coe, Fin.card_Icc]
  rfl

/-- A window is distinct exactly when it has no repeated letter — that is,
exactly when element distinctness on the window is negative. -/
lemma isDistinct_iff_edFun (α : Fin n → σ) (i j : Fin n) :
    IsDistinct α i j ↔ edFun (fun p : Win i j => α p.val) = false := by
  rw [edFun_eq_false_iff]
  constructor
  · intro h p q hpq
    exact Subtype.ext (h p.val p.2 q.val q.2 hpq)
  · intro h a ha b hb hab
    exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩ hab)

lemma decide_isDistinct (α : Fin n → σ) (i j : Fin n) :
    decide (IsDistinct α i j) = !(edFun (fun p : Win i j => α p.val)) := by
  by_cases h : IsDistinct α i j
  · rw [decide_eq_true h, (isDistinct_iff_edFun α i j).mp h]
    rfl
  · have htrue : edFun (fun p : Win i j => α p.val) = true := by
      rcases Bool.eq_false_or_eq_true (edFun (fun p : Win i j => α p.val)) with h' | h'
      · exact h'
      · exact absurd ((isDistinct_iff_edFun α i j).mpr h') h
    rw [decide_eq_false h, htrue]
    rfl

/-- **The windowed distinctness dual**: deciding whether `[i, j]` is distinct
has a feasible dual solution of cost `8 · (j - i + 1)^{2/3}`, for every `n`
and every alphabet. -/
theorem hasDual_isDistinct (i j : Fin n) :
    HasDual (fun α : Fin n → σ => decide (IsDistinct α i j))
      (8 * (winLen i j : ℝ) ^ ((2 : ℝ) / 3)) := by
  have hpull : HasDual
      (pullbackFun (fun p : Win i j => p.val) (edFun (ι := Win i j) (σ := σ)))
      (8 * (Fintype.card (Win i j) : ℝ) ^ ((2 : ℝ) / 3)) :=
    (hasDual_edFun (Win i j) σ).pullback Subtype.val_injective
  rw [card_win] at hpull
  refine hpull.ofKer fun α β => ?_
  rw [pullbackFun_apply, pullbackFun_apply, decide_isDistinct, decide_isDistinct]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Bool.not_inj h

end QuantumQueryComplexity
