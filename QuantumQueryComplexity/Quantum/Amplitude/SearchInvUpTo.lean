import QuantumQueryComplexity.Quantum.Amplitude.ApproxSearch
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The contract, restricted to the levels a search uses

`approxSearch … K` runs the stages `0, …, K`, hence uses the reflections `refl 1, …, refl (K+1)`
and the flags `clean 0, …, clean K` only.  `SearchInvUpTo L` is the contract of
`SearchInv.lean` with every clause restricted to those levels: reflections `1, …, L`, flags
`0, …, L−1`, supports `F 0 ⊆ ⋯ ⊆ F L`, precisions `β 1, …, β L`.  A caller with finitely many
ancillas proves exactly this.

`SearchInvUpTo.extend` is the extension lemma: above level `L` put the *exact* reflection about
the start state (any routine `E` with `E.run a = 2|s⟩⟨s| − 1`, e.g. `prepReflR`), trivial
flags, the top support and precision `0`; the result satisfies the unrestricted contract.
The compiled search does not see the difference (`approxSearch_congr`), so

* `approxSearch_pr_unmarked_upTo`, `two_thirds_le_approxSearch_upTo`,
  `approxSearch_pr_none_of_empty_upTo`

hold for the caller's own routines whenever `K + 1 ≤ L`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-! ## The exact reflection preserves supports containing the state -/

section Exact

variable {H : Type} [Fintype H] [DecidableEq H]

lemma preserves_stateRefl {s : H → ℂ} {F : Set H} (hs : SuppIn F s) :
    Preserves (stateRefl s) F := fun w hw x hx => by
  by_contra hF
  have h1 : s x = 0 := by by_contra h; exact hF (hs x h)
  have h2 : w x = 0 := by by_contra h; exact hF (hw x h)
  exact hx (by rw [stateRefl_mulVec, Pi.sub_apply, Pi.smul_apply, h1, h2, smul_zero, sub_zero])

lemma stateRefl_conjTranspose {s : H → ℂ} (hs : IsQState s) : (stateRefl s)ᴴ = stateRefl s :=
  qRefl_conjTranspose (isQProjector_ketbra hs)

end Exact

/-- The exact reflection about the prepared state, as a routine (`2·prep.len` queries). -/
noncomputable def prepReflR (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) : QRoutine ι σ W :=
  prep.inv.conjFixed (stateRefl init) (stateRefl_mem_unitaryGroup hinit)

lemma prepReflR_run (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
    (a : ι → σ) : (prepReflR prep init hinit).run a = stateRefl (prep.run a *ᵥ init) := by
  rw [prepReflR, QRoutine.conjFixed_run, QRoutine.inv_run, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, mul_stateRefl_mul_conjTranspose (prep.run_mem_unitaryGroup a)]

variable (vtx : QBasis ι σ W → V) (Marked : V → Prop) [DecidablePred Marked]

/-- **The contract up to level `L`.** -/
structure SearchInvUpTo (L : ℕ) (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W)
    (clean : ℕ → QBasis ι σ W → Bool) (a : ι → σ) (s : QBasis ι σ W → ℂ) (β : ℕ → ℝ)
    (F : ℕ → Set (QBasis ι σ W)) : Prop where
  unit : IsQState s
  mono : ∀ j, j < L → F j ⊆ F (j + 1)
  s_supp : SuppIn (F 0) s
  s_clean : ∀ j, j < L → goodPart (clean j) (· = true) s = s
  mark_flip : ∀ j, j ≤ L → ∀ w, SuppIn (F j) w → mark.run a *ᵥ w = phaseFlip vtx Marked w
  refl_comm : ∀ j, j < L → (refl (j + 1)).run a * flagProj (clean j)
    = flagProj (clean j) * (refl (j + 1)).run a
  refl_pres : ∀ j l, j + 1 ≤ l → l ≤ L → Preserves ((refl (j + 1)).run a) (F l)
  refl_pres_adj : ∀ j l, j + 1 ≤ l → l ≤ L → Preserves ((refl (j + 1)).run a)ᴴ (F l)
  β_nonneg : ∀ j, j ≤ L → 0 ≤ β j
  β_le : ∀ j, j ≤ L → β j ≤ (1 / 2) ^ (j + 8)
  refl_approx : ∀ j, j < L → IsApproxRefl ((refl (j + 1)).run a) s
    {w | SuppIn (F j) w ∧ badPart (clean j) (· = true) w = 0} (β (j + 1))

variable {vtx Marked} {L : ℕ} {mark : QRoutine ι σ W} {refl : ℕ → QRoutine ι σ W}
  {clean : ℕ → QBasis ι σ W → Bool} {a : ι → σ} {s : QBasis ι σ W → ℂ} {β : ℕ → ℝ}
  {F : ℕ → Set (QBasis ι σ W)}

/-- The unrestricted contract restricts. -/
theorem SearchInv.upTo (h : SearchInv vtx Marked mark refl clean a s β F) (L : ℕ) :
    SearchInvUpTo vtx Marked L mark refl clean a s β F :=
  ⟨h.unit, fun j _ => h.mono j, h.s_supp, fun j _ => h.s_clean j, fun j _ => h.mark_flip j,
   fun j _ => h.refl_comm j, fun j l hl _ => h.refl_pres j l hl,
   fun j l hl _ => h.refl_pres_adj j l hl, fun j _ => h.β_nonneg j, fun j _ => h.β_le j,
   fun j _ => h.refl_approx j⟩

/-! ## The extension -/

/-- Reflections above `L` replaced by `E`. -/
noncomputable def extRefl (L : ℕ) (refl : ℕ → QRoutine ι σ W) (E : QRoutine ι σ W) :
    ℕ → QRoutine ι σ W := fun j => if j ≤ L then refl j else E

/-- Flags from `L` on replaced by the trivial flag. -/
def extClean (L : ℕ) (clean : ℕ → QBasis ι σ W → Bool) : ℕ → QBasis ι σ W → Bool :=
  fun j => if j < L then clean j else fun _ => true

lemma flagProj_true {H : Type} [Fintype H] [DecidableEq H] :
    flagProj (fun _ : H => true) = 1 := by
  rw [flagProj, ← Matrix.diagonal_one]; congr 1

/-- **The extension lemma.** -/
theorem SearchInvUpTo.extend (h : SearchInvUpTo vtx Marked L mark refl clean a s β F)
    {E : QRoutine ι σ W} (hE : E.run a = stateRefl s) :
    SearchInv vtx Marked mark (extRefl L refl E) (extClean L clean) a s
      (fun j => if j ≤ L then β j else 0) (fun l => F (min l L)) where
  unit := h.unit
  mono := fun j => by
    by_cases hj : j < L
    · rw [min_eq_left hj.le, min_eq_left (Nat.succ_le_of_lt hj)]; exact h.mono j hj
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
  s_supp := by rw [Nat.zero_min]; exact h.s_supp
  s_clean := fun j => by
    by_cases hj : j < L
    · simp only [extClean, if_pos hj]; exact h.s_clean j hj
    · simp only [extClean, if_neg hj]
      funext q; rw [goodPart_apply, if_pos rfl]
  mark_flip := fun j w hw => h.mark_flip (min j L) (min_le_right _ _) w hw
  refl_comm := fun j => by
    by_cases hj : j < L
    · simp only [extRefl, extClean, if_pos hj, if_pos (Nat.succ_le_of_lt hj)]
      exact h.refl_comm j hj
    · simp only [extClean, if_neg hj]
      rw [flagProj_true, Matrix.mul_one, Matrix.one_mul]
  refl_pres := fun j l hl => by
    by_cases hj : j + 1 ≤ L
    · simp only [extRefl, if_pos hj]
      exact h.refl_pres j (min l L) (le_min hl hj) (min_le_right _ _)
    · simp only [extRefl, if_neg hj]
      rw [hE]
      exact preserves_stateRefl (h.s_supp.mono (by
        intro x hx
        have hmono : ∀ n, n ≤ L → F 0 ⊆ F n := by
          intro n hn
          induction n with
          | zero => exact le_rfl
          | succ n ih => exact (ih (by omega)).trans (h.mono n (by omega))
        exact hmono _ (min_le_right _ _) hx))
  refl_pres_adj := fun j l hl => by
    by_cases hj : j + 1 ≤ L
    · simp only [extRefl, if_pos hj]
      exact h.refl_pres_adj j (min l L) (le_min hl hj) (min_le_right _ _)
    · simp only [extRefl, if_neg hj]
      rw [hE, stateRefl_conjTranspose h.unit]
      exact preserves_stateRefl (h.s_supp.mono (by
        intro x hx
        have hmono : ∀ n, n ≤ L → F 0 ⊆ F n := by
          intro n hn
          induction n with
          | zero => exact le_rfl
          | succ n ih => exact (ih (by omega)).trans (h.mono n (by omega))
        exact hmono _ (min_le_right _ _) hx))
  β_nonneg := fun j => by
    by_cases hj : j ≤ L
    · simp only [if_pos hj]; exact h.β_nonneg j hj
    · simp only [if_neg hj]; exact le_rfl
  β_le := fun j => by
    by_cases hj : j ≤ L
    · simp only [if_pos hj]; exact h.β_le j hj
    · simp only [if_neg hj]; positivity
  refl_approx := fun j => by
    by_cases hj : j < L
    · simp only [extRefl, extClean, if_pos hj, if_pos (Nat.succ_le_of_lt hj),
        min_eq_left hj.le]
      exact h.refl_approx j hj
    · have hj' : ¬ j + 1 ≤ L := by omega
      simp only [extRefl, if_neg hj']
      rw [hE]
      exact ⟨(isApproxRefl_stateRefl h.unit).fix, fun w _ => by
        rw [sub_self, qNorm_zero]; simp⟩

/-! ## The compiled search does not see the extension -/

section Congr

variable (prep mark' : QRoutine ι σ W) {refl₁ refl₂ : ℕ → QRoutine ι σ W}
  {clean₁ clean₂ : ℕ → QBasis ι σ W → Bool} (vtx' : QBasis ι σ W → V)

lemma chainR_congr (j : ℕ) (hr : ∀ l, l ≤ j → refl₁ l = refl₂ l)
    (hc : ∀ l, l < j → clean₁ l = clean₂ l) :
    chainR mark' refl₁ clean₁ j = chainR mark' refl₂ clean₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [chainR, chainR, ih (fun l hl => hr l (by omega)) (fun l hl => hc l (by omega)),
        hr (j + 1) le_rfl, hc j (Nat.lt_succ_self j)]

lemma stageR_congr (j : ℕ) (hr : ∀ l, l ≤ j + 1 → refl₁ l = refl₂ l)
    (hc : ∀ l, l ≤ j → clean₁ l = clean₂ l) :
    stageR mark' refl₁ clean₁ j = stageR mark' refl₂ clean₂ j := by
  rw [stageR, stageR, chainR_congr mark' j (fun l hl => hr l (by omega))
    (fun l hl => hc l (by omega)), hr (j + 1) le_rfl, hc j le_rfl]

lemma passUpTo_congr {N : ℕ} (j : ℕ) (hj : j < N) (hr : ∀ l, l ≤ j → refl₁ l = refl₂ l)
    (hc : ∀ l, l < j → clean₁ l = clean₂ l) :
    passUpTo (N := N) prep mark' refl₁ clean₁ vtx' j hj
      = passUpTo (N := N) prep mark' refl₂ clean₂ vtx' j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [passUpTo, passUpTo, ih (Nat.lt_of_succ_lt hj) (fun l hl => hr l (by omega))
        (fun l hl => hc l (by omega)),
        stageR_congr mark' j hr (fun l hl => hc l (by omega))]

end Congr

/-- **The search is the same algorithm** when the routines agree on the levels it uses. -/
theorem approxSearch_congr (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (mark : QRoutine ι σ W) {refl₁ refl₂ : ℕ → QRoutine ι σ W}
    {clean₁ clean₂ : ℕ → QBasis ι σ W → Bool} (vtx : QBasis ι σ W → V) (K : ℕ)
    (hr : ∀ l, l ≤ K + 1 → refl₁ l = refl₂ l) (hc : ∀ l, l ≤ K → clean₁ l = clean₂ l) :
    approxSearch prep init hinit mark refl₁ clean₁ vtx K
      = approxSearch prep init hinit mark refl₂ clean₂ vtx K := by
  have hR : passR prep mark refl₁ clean₁ vtx K = passR prep mark refl₂ clean₂ vtx K :=
    passUpTo_congr prep mark vtx (K + 1) _ hr (fun l hl => hc l (by omega))
  have hT : passTrial prep init hinit mark refl₁ clean₁ vtx K
      = passTrial prep init hinit mark refl₂ clean₂ vtx K := by
    unfold passTrial
    rw [← passR_len prep mark refl₁ clean₁ vtx K, ← passR_len prep mark refl₂ clean₂ vtx K, hR]
  rw [approxSearch, approxSearch, hT]

/-! ## The theorems, for the caller's own routines -/

section Public

variable {prep : QRoutine ι σ W} {init : QBasis ι σ W → ℂ} {hinit : IsQState init} {K : ℕ}
  (h : SearchInvUpTo vtx Marked L mark refl clean a (prep.run a *ᵥ init) β F)
  (hKL : K + 1 ≤ L)

include h hKL

lemma approxSearch_eq_ext :
    approxSearch prep init hinit mark refl clean vtx K
      = approxSearch prep init hinit mark (extRefl L refl (prepReflR prep init hinit))
          (extClean L clean) vtx K :=
  approxSearch_congr prep init hinit mark vtx K
    (fun l hl => by simp only [extRefl, if_pos (show l ≤ L by omega)])
    (fun l hl => by simp only [extClean, if_pos (show l < L by omega)])

theorem approxSearch_pr_unmarked_upTo {v : V} (hv : ¬ Marked v) :
    (approxSearch prep init hinit mark refl clean vtx K).pr a (some v) = 0 := by
  rw [approxSearch_eq_ext (hinit := hinit) h hKL]
  exact approxSearch_pr_unmarked (h.extend (prepReflR_run prep init hinit a)) K hv

theorem two_thirds_le_approxSearch_upTo {ε : ℝ} (hε : 0 < ε)
    (hm0 : ε ≤ goodProb vtx Marked (prep.run a *ᵥ init)) (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) :
    2 / 3 ≤ (approxSearch prep init hinit mark refl clean vtx K).good Marked a := by
  rw [approxSearch_eq_ext (hinit := hinit) h hKL]
  exact two_thirds_le_approxSearch (h.extend (prepReflR_run prep init hinit a)) hε hm0 hK

theorem approxSearch_pr_none_of_empty_upTo (hno : ∀ v, ¬ Marked v) :
    (approxSearch prep init hinit mark refl clean vtx K).pr a none = 1 := by
  rw [approxSearch_eq_ext (hinit := hinit) h hKL]
  exact approxSearch_pr_none_of_empty (h.extend (prepReflR_run prep init hinit a)) hno K

end Public

end QuantumQueryComplexity
