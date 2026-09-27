import QuantumQueryComplexity.Quantum.Amplitude.SearchInv
import QuantumQueryComplexity.Quantum.History
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One compiled pass of the tolerant protocol

    prepare ; check₀ ; record₀ ; stage₀ ; check₁ ; record₁ ; stage₁ ; … ; check_{K+1} ; record_{K+1}

on the workspace `Slots (K+2) V × CtrlWork ι W`.  The start state is prepared **once**.
A check is the Hadamard test of the exact marker (`flagRoutine`, cost `C`); a stage is
`stageR j` (cost `2q_j + r_{j+1}`); recording is free.  Nothing stops early: successful
branches keep being acted on (and charged), but the slots are out of reach of every lifted
routine, and the readout takes the first recorded value.

* `passLen`, `passR_len` — the exact cost, `S + C + ∑_{j ≤ K} (2q_j + r_{j+1} + C)`:
  **no level-dependent multiple of the setup cost `S`**.
* `passR_run` — the state after the pass is
  `(empty history) ⊗ (continuing vector ν (K+1))  +  Ξ`, with `Ξ` supported on histories
  whose first recorded value is a marked vertex.  The continuing vector is the one of
  `Tolerant.lean`: products of projectors and routines, unnormalized.
* `pass_prob_none`, `pass_prob_unmarked` — `Pr[none] = ‖ν (K+1)‖²`, and an unmarked vertex is
  returned with probability `0`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

section Supp

variable {H : Type} [Fintype H] [DecidableEq H]

lemma SuppIn.add {F : Set H} {v w : H → ℂ} (hv : SuppIn F v) (hw : SuppIn F w) :
    SuppIn F (v + w) := fun x hx => by
  by_contra hF
  have h1 : v x = 0 := by by_contra h; exact hF (hv x h)
  have h2 : w x = 0 := by by_contra h; exact hF (hw x h)
  exact hx (by rw [Pi.add_apply, h1, h2, add_zero])

lemma suppIn_zero (F : Set H) : SuppIn F (0 : H → ℂ) := fun _ hx => absurd rfl hx

end Supp

lemma embedReg_add' {U : Type} [Fintype U] [DecidableEq U] (u : U) (φ χ : QBasis ι σ W → ℂ) :
    embedReg u (φ + χ) = embedReg u φ + embedReg u χ := by
  funext p
  simp only [Pi.add_apply, embedReg_apply]
  split_ifs <;> simp

variable (prep mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W)
  (clean : ℕ → QBasis ι σ W → Bool) (vtx : QBasis ι σ W → V)

/-- Check the marker and record the result in slot `j`. -/
noncomputable def chkRec {N : ℕ} (j : Fin N) :
    QRoutine ι σ (Slots N V × CtrlWork ι W) :=
  ((flagRoutine mark).liftReg (Slots N V)).comp
    (QRoutine.ofUnitary (recordMat vtx j) (recordMat_mem_unitaryGroup vtx j))

/-- The pass, up to and including the check of stage `j`. -/
noncomputable def passUpTo {N : ℕ} : (j : ℕ) → j < N → QRoutine ι σ (Slots N V × CtrlWork ι W)
  | 0, h => ((liftCtrl prep).liftReg (Slots N V)).comp (chkRec mark vtx ⟨0, h⟩)
  | j + 1, h => (passUpTo j (Nat.lt_of_succ_lt h)).comp
      (((stageR mark refl clean j).liftReg (Slots N V)).comp (chkRec mark vtx ⟨j + 1, h⟩))

/-- **One pass**: `K + 1` stages, `K + 2` checks. -/
noncomputable def passR (K : ℕ) : QRoutine ι σ (Slots (K + 2) V × CtrlWork ι W) :=
  passUpTo prep mark refl clean vtx (K + 1) (Nat.lt_succ_self _)

/-- The cost of a pass through the check of stage `j`. -/
def passLen (S C : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => S + C
  | j + 1 => passLen S C r j + (2 * chainLen C r j + r (j + 1)) + C

lemma chkRec_len {N : ℕ} (j : Fin N) : (chkRec (ι := ι) (σ := σ) mark vtx j).len = mark.len := by
  simp only [chkRec, QRoutine.comp_len, QRoutine.liftReg_len, flagRoutine_len,
    QRoutine.ofUnitary_len, add_zero]

theorem passUpTo_len {N : ℕ} (j : ℕ) (hj : j < N) :
    (passUpTo (N := N) prep mark refl clean vtx j hj).len
      = passLen prep.len mark.len (fun l => (refl l).len) j := by
  induction j with
  | zero =>
      simp only [passUpTo, QRoutine.comp_len, QRoutine.liftReg_len, liftCtrl_len, chkRec_len,
        passLen]
  | succ j ih =>
      simp only [passUpTo, QRoutine.comp_len, QRoutine.liftReg_len, chkRec_len, stageR_len,
        ih (Nat.lt_of_succ_lt hj), passLen]
      ring

theorem passR_len (K : ℕ) :
    (passR prep mark refl clean vtx K).len
      = passLen prep.len mark.len (fun l => (refl l).len) (K + 1) :=
  passUpTo_len prep mark refl clean vtx (K + 1) _

variable {prep mark refl clean vtx}

/-! ## The state of a pass -/

variable {Marked : V → Prop} [DecidablePred Marked]

/-- The check-and-record step on "continuing + found". -/
theorem chkRec_run {N : ℕ} (j : Fin N) (a : ι → σ) {χ : QBasis ι σ W → ℂ}
    (hg : mark.run a *ᵥ goodPart vtx Marked χ = -goodPart vtx Marked χ)
    (hb : mark.run a *ᵥ badPart vtx Marked χ = badPart vtx Marked χ)
    {Ξ : QBasis ι σ (Slots N V × CtrlWork ι W) → ℂ} {l : ℕ} (hl : l ≤ j.val)
    (hΞ : SuppIn (foundBelow ι σ W N Marked l) Ξ) :
    ∃ Ξ', SuppIn (foundBelow ι σ W N Marked (j.val + 1)) Ξ'
      ∧ (chkRec mark vtx j).run a *ᵥ (embedReg (emptySlots N V) (embedCtrl false χ) + Ξ)
        = embedReg (emptySlots N V) (embedCtrl false (badPart vtx Marked χ)) + Ξ' := by
  have hflag := flagRoutine_run mark a hg hb
  rw [goodPart_add_badPart] at hflag
  have hpresL : Preserves (((flagRoutine mark).liftReg (Slots N V)).run a)
      (foundBelow ι σ W N Marked l) :=
    preserves_liftReg (flagRoutine mark) a
      (fun sl : Slots N V => ∃ i : Fin N, i.val < l ∧ (∀ i' < i, sl i' = none)
        ∧ ∃ v, sl i = some v ∧ Marked v)
  refine ⟨recordMat vtx j *ᵥ embedReg (emptySlots N V)
        (embedCtrl true (goodPart vtx Marked χ))
      + recordMat vtx j *ᵥ (((flagRoutine mark).liftReg (Slots N V)).run a *ᵥ Ξ), ?_, ?_⟩
  · refine SuppIn.add ?_ ?_
    · refine suppIn_record_embed_true vtx j Marked _ fun q hq => ?_
      by_contra hM
      exact hq (by rw [goodPart_apply, if_neg hM])
    · exact (preserves_record vtx j Marked hl _ (hpresL _ hΞ)).mono
        (foundBelow_mono Marked (by omega))
  · rw [chkRec, QRoutine.comp_run, QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_add, QRoutine.liftReg_run_embed, hflag, embedReg_add', Matrix.mulVec_add,
      Matrix.mulVec_add, recordMat_embed_false]
    abel

/-- A lifted routine on "continuing + found". -/
theorem liftReg_run_found {N : ℕ} (X : QRoutine ι σ (CtrlWork ι W)) (a : ι → σ)
    {χ χ' : QBasis ι σ W → ℂ} (hX : X.run a *ᵥ embedCtrl false χ = embedCtrl false χ')
    {Ξ : QBasis ι σ (Slots N V × CtrlWork ι W) → ℂ} {l : ℕ}
    (hΞ : SuppIn (foundBelow ι σ W N Marked l) Ξ) :
    ∃ Ξ', SuppIn (foundBelow ι σ W N Marked l) Ξ'
      ∧ (X.liftReg (Slots N V)).run a *ᵥ (embedReg (emptySlots N V) (embedCtrl false χ) + Ξ)
        = embedReg (emptySlots N V) (embedCtrl false χ') + Ξ' := by
  have hpresL : Preserves ((X.liftReg (Slots N V)).run a) (foundBelow ι σ W N Marked l) :=
    preserves_liftReg X a
      (fun sl : Slots N V => ∃ i : Fin N, i.val < l ∧ (∀ i' < i, sl i' = none)
        ∧ ∃ v, sl i = some v ∧ Marked v)
  exact ⟨_, hpresL _ hΞ, by rw [Matrix.mulVec_add, QRoutine.liftReg_run_embed, hX]⟩

/-! ## The pass under the contract -/

namespace SearchInv

variable {a : ι → σ} {s : QBasis ι σ W → ℂ} {β : ℕ → ℝ} {F : ℕ → Set (QBasis ι σ W)}
  (h : SearchInv vtx Marked mark refl clean a s β F)

include h

lemma mark_parts {l : ℕ} {χ : QBasis ι σ W → ℂ} (hχ : SuppIn (F l) χ) :
    mark.run a *ᵥ goodPart vtx Marked χ = -goodPart vtx Marked χ
    ∧ mark.run a *ᵥ badPart vtx Marked χ = badPart vtx Marked χ :=
  ⟨by rw [h.mark_flip l _ (hχ.goodPart vtx Marked), phaseFlip_goodPart],
   by rw [h.mark_flip l _ (hχ.badPart vtx Marked), phaseFlip_badPart]⟩

lemma supp_stage (j : ℕ) :
    SuppIn (F (j + 1)) (chainM (mark.run a) (cleanOps refl clean a) j
      *ᵥ contV vtx Marked s (mark.run a) (cleanOps refl clean a) j) := by
  have hA := h.pres_chainA j (j + 1) (by omega)
  have hM : Preserves (chainM (mark.run a) (cleanOps refl clean a) j) (F (j + 1)) :=
    (hA.1.mul (h.pres_cleanOps j (j + 1) le_rfl)).mul hA.2
  exact hM _ ((h.supp_contV j).mono (h.mono j))

/-- **The state of the pass**: the continuing vector under the empty history, plus branches
whose first recorded value is a marked vertex. -/
theorem passUpTo_run {N : ℕ} {init : QBasis ι σ W → ℂ} (hs : prep.run a *ᵥ init = s) (j : ℕ)
    (hj : j < N) :
    ∃ Ξ, SuppIn (foundBelow ι σ W N Marked (j + 1)) Ξ
      ∧ (passUpTo (N := N) prep mark refl clean vtx j hj).run a
          *ᵥ embedReg (emptySlots N V) (embedCtrl false init)
        = embedReg (emptySlots N V)
            (embedCtrl false (contV vtx Marked s (mark.run a) (cleanOps refl clean a) j)) + Ξ := by
  induction j with
  | zero =>
      obtain ⟨hg, hb⟩ := h.mark_parts h.s_supp
      obtain ⟨Ξ', hΞ', hrun⟩ := chkRec_run (N := N) ⟨0, hj⟩ a hg hb (le_refl 0)
        (suppIn_zero (foundBelow ι σ W N Marked 0))
      refine ⟨Ξ', hΞ', ?_⟩
      rw [passUpTo, QRoutine.comp_run, ← Matrix.mulVec_mulVec, QRoutine.liftReg_run_embed,
        liftCtrl_run, hs]
      rw [add_zero] at hrun
      exact hrun
  | succ j ih =>
      obtain ⟨Ξ, hΞ, hrun⟩ := ih (Nat.lt_of_succ_lt hj)
      obtain ⟨Ξ₁, hΞ₁, hrun₁⟩ := liftReg_run_found (N := N) (stageR mark refl clean j) a
        (stageR_run h.refl_comm j _) hΞ
      obtain ⟨hg, hb⟩ := h.mark_parts (h.supp_stage j)
      obtain ⟨Ξ₂, hΞ₂, hrun₂⟩ := chkRec_run (N := N) ⟨j + 1, hj⟩ a hg hb (le_refl (j + 1)) hΞ₁
      refine ⟨Ξ₂, hΞ₂, ?_⟩
      rw [passUpTo, QRoutine.comp_run, QRoutine.comp_run, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hrun, hrun₁, hrun₂]
      rfl

end SearchInv

/-! ## Reading a history -/

section Read

variable {N : ℕ} {ν : QBasis ι σ W → ℂ} {Ξ : QBasis ι σ (Slots N V × CtrlWork ι W) → ℂ} {l : ℕ}

omit [DecidablePred Marked] in
lemma main_apply_eq_zero {p : QBasis ι σ (Slots N V × CtrlWork ι W)}
    (hp : slotReadout ι σ W N V p ≠ none) :
    embedReg (emptySlots N V) (embedCtrl false ν) p = 0 := by
  rw [embedReg_apply, if_neg]
  intro hsl
  exact hp (by rw [slotReadout, hsl, firstSlot_empty])

omit [DecidablePred Marked] in
/-- **`Pr[none]` is the remaining mass.** -/
theorem qProb_slotReadout_none (hΞ : SuppIn (foundBelow ι σ W N Marked l) Ξ) :
    qProb (slotReadout ι σ W N V) (embedReg (emptySlots N V) (embedCtrl false ν) + Ξ) none
      = qNormSq ν := by
  rw [← qNormSq_embedCtrl false ν, ← qNormSq_embedReg (emptySlots N V), qProb, qNormSq_def]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : slotReadout ι σ W N V p = none
  · have hΞp : Ξ p = 0 := by
      by_contra hne
      obtain ⟨v, hv, _⟩ := slotReadout_of_found (hΞ p hne)
      rw [hp] at hv; exact absurd hv (by simp)
    rw [if_pos hp, Pi.add_apply, hΞp, add_zero]
  · rw [if_neg hp, main_apply_eq_zero hp, map_zero]

omit [DecidablePred Marked] in
/-- **An unmarked value is never read.** -/
theorem qProb_slotReadout_unmarked (hΞ : SuppIn (foundBelow ι σ W N Marked l) Ξ) {v : V}
    (hv : ¬ Marked v) :
    qProb (slotReadout ι σ W N V) (embedReg (emptySlots N V) (embedCtrl false ν) + Ξ) (some v)
      = 0 := by
  rw [qProb]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : slotReadout ι σ W N V p = some v
  · have hΞp : Ξ p = 0 := by
      by_contra hne
      obtain ⟨v', hv', hM⟩ := slotReadout_of_found (hΞ p hne)
      rw [hp] at hv'
      exact hv (by rw [Option.some.inj hv']; exact hM)
    rw [if_pos hp, Pi.add_apply, hΞp, add_zero,
      main_apply_eq_zero (by rw [hp]; simp), map_zero]
  · rw [if_neg hp]

end Read

end QuantumQueryComplexity
