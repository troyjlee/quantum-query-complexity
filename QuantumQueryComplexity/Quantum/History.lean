import QuantumQueryComplexity.Quantum.Amplitude.ChainRoutine
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Finite coherent measurement histories

A finite deferred-measurement compiler for "check; if found, remember what was found; else
continue".  It is a fixed schedule of unitaries, not a model with stopping times.

The history is a register of `N` **slots** `Fin N → Option V`, placed outside the control
workspace: the full workspace is `Slots N V × CtrlWork ι W`.  Every query routine is lifted past
the slots (`liftReg`), so it cannot touch them.  After a check has written the success flag
into the shared control bit, `recordMat vtx j` — two free involutions —

1. `histSwap`: on a set flag, exchanges `none ↔ some (vtx q)` in slot `j`;
2. `flagClear`: flips the flag when slot `j` holds `some (vtx q)`,

so the found value is copied into slot `j`, the flag is returned **clean** for the next use,
and the continuing branch (flag unset, slot empty) is untouched.  Later operations act on the
successful branches too — they are charged, there is no early stopping — but they never touch
the slots, and the readout `firstSlot` takes the *first* recorded value.

* `recordMat_embed_false` — the continuing branch is fixed;
* `suppIn_record_embed_true` — a flagged branch is recorded in slot `j`: every basis state of
  the result has slots `0 … j−1` empty and slot `j` holding `vtx q` for a `q` in the support;
* `preserves_liftReg_slots`, `preserves_record` — slot-only supports survive lifted routines,
  and recording in slot `j` does not change which earlier slot comes first;
* `firstSlot_empty`, `firstSlot_of_mem` — the readout.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-- The history register. -/
abbrev Slots (N : ℕ) (V : Type) : Type := Fin N → Option V

/-- The empty history. -/
def emptySlots (N : ℕ) (V : Type) : Slots N V := fun _ => none

/-! ## Lifted routines never touch the extra register -/

section Lift

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The sector of the extra register value `u`. -/
def sectorOf (u : U) (ψ : QBasis ι σ (U × W) → ℂ) : QBasis ι σ W → ℂ :=
  fun q => ψ (q.1, q.2.1, (u, q.2.2))

lemma eq_sum_embedReg_sectorOf (ψ : QBasis ι σ (U × W) → ℂ) :
    ψ = ∑ u, embedReg u (sectorOf u ψ) := by
  funext p
  obtain ⟨k, t, u, w⟩ := p
  rw [Finset.sum_apply, Finset.sum_eq_single u]
  · rw [embedReg_apply, if_pos rfl]; rfl
  · intro u' _ hu'
    rw [embedReg_apply, if_neg (Ne.symm hu')]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **A lifted routine preserves every support defined by the extra register alone.** -/
theorem preserves_liftReg (X : QRoutine ι σ W) (a : ι → σ) (P : U → Prop) :
    Preserves ((X.liftReg U).run a) {p : QBasis ι σ (U × W) | P p.2.2.1} := by
  intro ψ hψ p hp
  by_contra hP
  apply hp
  rw [eq_sum_embedReg_sectorOf ψ, Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [QRoutine.liftReg_run_embed, embedReg_apply]
  by_cases hu : p.2.2.1 = u
  · have hz : sectorOf u ψ = 0 := by
      funext q
      by_contra hq
      have hmem : P u := hψ (q.1, q.2.1, (u, q.2.2)) hq
      exact hP (show P p.2.2.1 by rw [hu]; exact hmem)
    rw [if_pos hu, hz, Matrix.mulVec_zero]; rfl
  · rw [if_neg hu]

end Lift

/-! ## Recording -/

section Record

variable {N : ℕ} (vtx : QBasis ι σ W → V) (j : Fin N)

/-- On a set flag, exchange `none ↔ some (vtx q)` in slot `j`. -/
def histSwapMap : QBasis ι σ (Slots N V × CtrlWork ι W) → QBasis ι σ (Slots N V × CtrlWork ι W)
  | (k, t, (sl, (b, pk, w))) =>
      (k, t, ((if b then Function.update sl j (Equiv.swap none (some (vtx (k, t, w))) (sl j))
        else sl), (b, pk, w)))

lemma histSwapMap_involutive : Function.Involutive (histSwapMap (N := N) vtx j) := by
  rintro ⟨k, t, sl, b, pk, w⟩
  cases b
  · rfl
  · simp only [histSwapMap, if_true, Function.update_self, Equiv.swap_apply_self,
      Function.update_idem, Function.update_eq_self]

/-- Flip the flag when slot `j` holds `some (vtx q)`. -/
def flagClearMap : QBasis ι σ (Slots N V × CtrlWork ι W) → QBasis ι σ (Slots N V × CtrlWork ι W)
  | (k, t, (sl, (b, pk, w))) =>
      (k, t, (sl, (xor b (decide (sl j = some (vtx (k, t, w)))), pk, w)))

lemma flagClearMap_involutive : Function.Involutive (flagClearMap (N := N) vtx j) := by
  rintro ⟨k, t, sl, b, pk, w⟩
  show (k, t, (sl, (xor (xor b (decide (sl j = some (vtx (k, t, w)))))
    (decide (sl j = some (vtx (k, t, w)))), pk, w))) = _
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- **Record the found value in slot `j` and return the flag clean.** -/
def recordMat : Matrix (QBasis ι σ (Slots N V × CtrlWork ι W))
    (QBasis ι σ (Slots N V × CtrlWork ι W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ (flagClearMap_involutive vtx j))
    * qPerm (Function.Involutive.toPerm _ (histSwapMap_involutive vtx j))

lemma recordMat_mem_unitaryGroup : recordMat (N := N) (ι := ι) (σ := σ) vtx j
    ∈ Matrix.unitaryGroup _ ℂ :=
  mul_mem_qUnitary (qPerm_mem_unitaryGroup _) (qPerm_mem_unitaryGroup _)

lemma recordMat_mulVec_apply (ψ : QBasis ι σ (Slots N V × CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (Slots N V × CtrlWork ι W)) :
    (recordMat vtx j *ᵥ ψ) p = ψ (histSwapMap vtx j (flagClearMap vtx j p)) := by
  rw [recordMat, ← Matrix.mulVec_mulVec, qPerm_mulVec_apply, qPerm_mulVec_apply]
  rfl

/-- **The continuing branch is untouched**: flag unset, slot empty. -/
theorem recordMat_embed_false (φ : QBasis ι σ W → ℂ) :
    recordMat vtx j *ᵥ embedReg (emptySlots N V) (embedCtrl false φ)
      = embedReg (emptySlots N V) (embedCtrl false φ) := by
  funext p
  obtain ⟨k, t, sl, b, pk, w⟩ := p
  rw [recordMat_mulVec_apply]
  simp only [flagClearMap, histSwapMap, embedReg_apply, embedCtrl_apply]
  by_cases hs : sl j = some (vtx (k, t, w))
  · have hne : sl ≠ emptySlots N V := fun h => by rw [h] at hs; simp [emptySlots] at hs
    cases b <;> simp [hs, hne]
  · cases b <;> simp [hs]

variable (Marked : V → Prop)

/-- Some slot below `l` is the first non-empty one, and holds a marked value. -/
def foundBelow (ι σ W : Type) (N : ℕ) (Marked : V → Prop) (l : ℕ) :
    Set (QBasis ι σ (Slots N V × CtrlWork ι W)) :=
  {p | ∃ i : Fin N, i.val < l ∧ (∀ i' < i, p.2.2.1 i' = none) ∧ ∃ v, p.2.2.1 i = some v ∧ Marked v}

lemma foundBelow_mono {l l' : ℕ} (h : l ≤ l') :
    foundBelow ι σ W N Marked l ⊆ foundBelow ι σ W N Marked l' :=
  fun _ ⟨i, hi, hrest⟩ => ⟨i, by omega, hrest⟩

/-- **A flagged branch is recorded in slot `j`.** -/
theorem suppIn_record_embed_true (g : QBasis ι σ W → ℂ) (hg : ∀ q, g q ≠ 0 → Marked (vtx q)) :
    SuppIn (foundBelow ι σ W N Marked (j.val + 1))
      (recordMat vtx j *ᵥ embedReg (emptySlots N V) (embedCtrl true g)) := by
  intro p hp
  obtain ⟨k, t, sl, b, pk, w⟩ := p
  rw [recordMat_mulVec_apply] at hp
  simp only [flagClearMap, histSwapMap, embedReg_apply, embedCtrl_apply] at hp
  -- the flag after clearing must be set, and the swapped slots must be empty
  by_cases hB : xor b (decide (sl j = some (vtx (k, t, w)))) = true
  swap
  · exact absurd (by simp [hB]) hp
  simp only [hB, if_true, true_and] at hp
  have hslots : Function.update sl j (Equiv.swap none (some (vtx (k, t, w))) (sl j))
      = emptySlots N V := by
    by_contra h; simp [h] at hp
  have hgne : g (k, t, w) ≠ 0 := by
    intro h0; simp [hslots, h0] at hp
  have hj : sl j = some (vtx (k, t, w)) := by
    have h1 := congrFun hslots j
    rw [Function.update_self] at h1
    have h2 : Equiv.swap none (some (vtx (k, t, w))) (sl j) = none := h1
    calc sl j = Equiv.swap none (some (vtx (k, t, w)))
          (Equiv.swap none (some (vtx (k, t, w))) (sl j)) := (Equiv.swap_apply_self _ _ _).symm
      _ = Equiv.swap none (some (vtx (k, t, w))) none := by rw [h2]
      _ = some (vtx (k, t, w)) := Equiv.swap_apply_left _ _
  refine ⟨j, Nat.lt_succ_self _, fun i' hi' => ?_, vtx (k, t, w), hj, hg _ hgne⟩
  have h1 := congrFun hslots i'
  rwa [Function.update_of_ne (ne_of_lt hi')] at h1

/-- **Recording in slot `j` keeps the earlier findings.** -/
theorem preserves_record {l : ℕ} (hl : l ≤ j.val) :
    Preserves (recordMat (ι := ι) (σ := σ) (W := W) vtx j) (foundBelow ι σ W N Marked l) := by
  intro ψ hψ p hp
  obtain ⟨k, t, sl, b, pk, w⟩ := p
  rw [recordMat_mulVec_apply] at hp
  obtain ⟨i, hi, hfirst, v, hv, hM⟩ := hψ _ hp
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  have key : ∀ i'' : Fin N, i'' ≠ j →
      (histSwapMap vtx j (flagClearMap vtx j (k, t, sl, b, pk, w))).2.2.1 i'' = sl i'' := by
    intro i'' hne
    show (if xor b (decide (sl j = some (vtx (k, t, w)))) = true
      then Function.update sl j (Equiv.swap none (some (vtx (k, t, w))) (sl j)) else sl) i''
      = sl i''
    by_cases hB : xor b (decide (sl j = some (vtx (k, t, w)))) = true
    · rw [if_pos hB]; exact Function.update_of_ne hne _ _
    · rw [if_neg hB]
  refine ⟨i, hi, fun i' hi' => ?_, v, ?_, hM⟩
  · have hne : i' ≠ j := fun h => by
      have : i'.val < i.val := hi'
      rw [h] at this; omega
    have := hfirst i' hi'
    rw [key i' hne] at this
    exact this
  · have := hv
    rw [key i hij] at this
    exact this

end Record

/-! ## The readout -/

section Readout

variable {N : ℕ}

/-- **The first recorded value.** -/
def firstSlot (sl : Slots N V) : Option V :=
  if h : ∃ i, (sl i).isSome = true then sl (Fin.find _ h) else none

lemma firstSlot_empty : firstSlot (emptySlots N V) = none := by
  rw [firstSlot, dif_neg]
  rintro ⟨i, hi⟩
  simp [emptySlots] at hi

lemma firstSlot_of_first {sl : Slots N V} {i : Fin N} {v : V} (hfirst : ∀ i' < i, sl i' = none)
    (hv : sl i = some v) : firstSlot sl = some v := by
  have h : ∃ i, (sl i).isSome = true := ⟨i, by rw [hv]; rfl⟩
  have hfind : Fin.find _ h = i := by
    rw [Fin.find_eq_iff]
    exact ⟨by rw [hv]; rfl, fun i' hi' => by rw [hfirst i' hi']; simp⟩
  rw [firstSlot, dif_pos h, hfind, hv]

/-- The output of a history: the first recorded value. -/
def slotReadout (ι σ W : Type) (N : ℕ) (V : Type) :
    QBasis ι σ (Slots N V × CtrlWork ι W) → Option V := fun p => firstSlot p.2.2.1

lemma slotReadout_of_found {Marked : V → Prop} {l : ℕ}
    {p : QBasis ι σ (Slots N V × CtrlWork ι W)} (hp : p ∈ foundBelow ι σ W N Marked l) :
    ∃ v, slotReadout ι σ W N V p = some v ∧ Marked v := by
  obtain ⟨i, _, hfirst, v, hv, hM⟩ := hp
  exact ⟨v, firstSlot_of_first hfirst hv, hM⟩

end Readout

end QuantumQueryComplexity
