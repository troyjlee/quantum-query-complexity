import QuantumQueryComplexity.Quantum.Amplitude.ChainRoutine
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The caller's contract for approximate-reflection search

`SearchInv` states, for one input `a`, what a caller must prove about the supplied routines,
in terms of **supports** `F j` of basis states ("encoded logical content; the ancillas of the
reflections above level `j` are blank"):

* the prepared state `s` is a unit vector supported on `F 0`, clean for every flag;
* the marker acts as the exact phase flip on every vector supported on some `F j` — throughout
  the encoded space, whatever spectator ancillas hold, not merely on two special vectors;
* `refl (j+1)` commutes with the flag `clean j` (it does not touch the earlier ancillas),
  it and its adjoint preserve the supports `F l`, `l ≥ j+1`, and it is a `β (j+1)`-approximate
  reflection about `s` on the clean vectors supported on `F j`.

`SearchInv.chainOK` and `SearchInv.contV_dom` are then the hypotheses of `Recursive.lean` and
`Tolerant.lean`, so `SearchInv.pass_fail_le` is the bound `≤ 99/100` for one tolerant pass of
the *compiled* operators.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

section PhaseFlip

variable {H O : Type} [Fintype H] [DecidableEq H] (rd : H → O) (G : O → Prop) [DecidablePred G]

lemma phaseFlip_phaseFlip (w : H → ℂ) : phaseFlip rd G (phaseFlip rd G w) = w := by
  rw [phaseFlip, phaseFlip, badPart_sub, goodPart_sub, badPart_badPart, badPart_goodPart,
    goodPart_badPart, goodPart_goodPart, sub_zero, zero_sub, sub_neg_eq_add, add_comm]
  exact goodPart_add_badPart rd G w

end PhaseFlip

variable (vtx : QBasis ι σ W → V) (Marked : V → Prop) [DecidablePred Marked]

/-- **The contract**, for one input. -/
structure SearchInv (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W)
    (clean : ℕ → QBasis ι σ W → Bool) (a : ι → σ) (s : QBasis ι σ W → ℂ) (β : ℕ → ℝ)
    (F : ℕ → Set (QBasis ι σ W)) : Prop where
  unit : IsQState s
  mono : ∀ j, F j ⊆ F (j + 1)
  s_supp : SuppIn (F 0) s
  s_clean : ∀ j, goodPart (clean j) (· = true) s = s
  mark_flip : ∀ j w, SuppIn (F j) w → mark.run a *ᵥ w = phaseFlip vtx Marked w
  refl_comm : ∀ j, (refl (j + 1)).run a * flagProj (clean j)
    = flagProj (clean j) * (refl (j + 1)).run a
  refl_pres : ∀ j l, j + 1 ≤ l → Preserves ((refl (j + 1)).run a) (F l)
  refl_pres_adj : ∀ j l, j + 1 ≤ l → Preserves ((refl (j + 1)).run a)ᴴ (F l)
  β_nonneg : ∀ j, 0 ≤ β j
  β_le : ∀ j, β j ≤ (1 / 2) ^ (j + 8)
  refl_approx : ∀ j, IsApproxRefl ((refl (j + 1)).run a) s
    {w | SuppIn (F j) w ∧ badPart (clean j) (· = true) w = 0} (β (j + 1))

variable {vtx Marked} {mark : QRoutine ι σ W} {refl : ℕ → QRoutine ι σ W}
  {clean : ℕ → QBasis ι σ W → Bool} {a : ι → σ} {s : QBasis ι σ W → ℂ} {β : ℕ → ℝ}
  {F : ℕ → Set (QBasis ι σ W)}

namespace SearchInv

variable (h : SearchInv vtx Marked mark refl clean a s β F)

include h

local notation "Sm" => mark.run a
local notation "Rm" => cleanOps refl clean a

lemma mono_le {j l : ℕ} (hjl : j ≤ l) : F j ⊆ F l := by
  induction l, hjl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact ih.trans (h.mono l)

lemma pres_mark (l : ℕ) : Preserves Sm (F l) := fun w hw => by
  rw [h.mark_flip l w hw]; exact hw.phaseFlip vtx Marked

lemma pres_mark_adj (l : ℕ) : Preserves (Sm)ᴴ (F l) := fun w hw => by
  have h1 := h.mark_flip l _ (hw.phaseFlip vtx Marked)
  rw [phaseFlip_phaseFlip] at h1
  have h2 : (Sm)ᴴ *ᵥ w = phaseFlip vtx Marked w := by
    calc (Sm)ᴴ *ᵥ w = (Sm)ᴴ *ᵥ (Sm *ᵥ phaseFlip vtx Marked w) := by rw [h1]
      _ = phaseFlip vtx Marked w := by
          rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
            (mark.run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [h2]; exact hw.phaseFlip vtx Marked

lemma cleanOps_conjTranspose (j : ℕ) :
    (Rm (j + 1))ᴴ = cleanMat (clean j) ((refl (j + 1)).run a)ᴴ := by
  have hcomm := h.refl_comm j
  have hPH := flagProj_conjTranspose (clean j)
  have hcomm' : ((refl (j + 1)).run a)ᴴ * flagProj (clean j)
      = flagProj (clean j) * ((refl (j + 1)).run a)ᴴ := by
    have := congrArg Matrix.conjTranspose hcomm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH] at this
    exact this.symm
  rw [cleanOps, cleanMat, cleanMat, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH, hcomm']

lemma pres_cleanOps (j l : ℕ) (hl : j + 1 ≤ l) : Preserves (Rm (j + 1)) (F l) :=
  (h.refl_pres j l hl).cleanMat _

lemma pres_cleanOps_adj (j l : ℕ) (hl : j + 1 ≤ l) : Preserves (Rm (j + 1))ᴴ (F l) := by
  rw [h.cleanOps_conjTranspose]
  exact (h.refl_pres_adj j l hl).cleanMat _

/-- The level operators and their adjoints preserve the supports above their level. -/
theorem pres_chainA (j : ℕ) :
    ∀ l, j ≤ l → Preserves (chainA Sm Rm j) (F l) ∧ Preserves (chainA Sm Rm j)ᴴ (F l) := by
  induction j with
  | zero =>
      intro l _
      refine ⟨preserves_one _, ?_⟩
      rw [chainA, Matrix.conjTranspose_one]; exact preserves_one _
  | succ j ih =>
      intro l hl
      obtain ⟨hA, hAH⟩ := ih l (by omega)
      have hR := h.pres_cleanOps j l hl
      have hRH := h.pres_cleanOps_adj j l hl
      have hS := h.pres_mark l
      have hSH := h.pres_mark_adj l
      constructor
      · rw [chainA]; exact ((hA.mul hR).mul hAH).mul (hS.mul hA)
      · rw [chainA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        exact (hAH.mul hSH).mul (hA.mul (hRH.mul hAH))

lemma supp_ψ (j : ℕ) : SuppIn (F j) (chainA Sm Rm j *ᵥ s) :=
  (h.pres_chainA j j le_rfl).1 _ (h.s_supp.mono (h.mono_le (Nat.zero_le j)))

/-- The allowed sets of the abstract recursion. -/
def Dom (_ : SearchInv vtx Marked mark refl clean a s β F) (j : ℕ) :
    Set (QBasis ι σ W → ℂ) :=
  {w | goodPart (clean j) (· = true) w
    ∈ {w | SuppIn (F j) w ∧ badPart (clean j) (· = true) w = 0}}

lemma mem_Dom {j : ℕ} {w : QBasis ι σ W → ℂ} (hw : SuppIn (F j) w) : w ∈ h.Dom j :=
  ⟨hw.goodPart _ _, badPart_goodPart _ _ _⟩

/-- **The hypotheses of the abstract recursion hold.** -/
theorem chainOK : ChainOK vtx Marked s Sm Rm β h.Dom where
  unit := h.unit
  S_unitary := mark.run_mem_unitaryGroup a
  R_unitary := cleanOps_mem_unitaryGroup h.refl_comm
  β_nonneg := h.β_nonneg
  β_le := h.β_le
  refl := fun j => (h.refl_approx j).clean (h.β_nonneg _) h.unit (h.s_clean j)
  flip := fun j => h.mark_flip j _ (h.supp_ψ j)
  dom := fun j => h.mem_Dom
    ((h.pres_chainA j j le_rfl).2 _ ((h.supp_ψ j).phaseFlip vtx Marked))

lemma supp_contV (j : ℕ) : SuppIn (F j) (contV vtx Marked s Sm Rm j) := by
  induction j with
  | zero => exact h.s_supp.badPart vtx Marked
  | succ j ih =>
      have hA := h.pres_chainA j (j + 1) (by omega)
      have hM : Preserves (chainM Sm Rm j) (F (j + 1)) :=
        (hA.1.mul (h.pres_cleanOps j (j + 1) le_rfl)).mul hA.2
      exact (hM _ (ih.mono (h.mono j))).badPart vtx Marked

/-- The continuing vectors are allowed. -/
theorem contV_dom (j : ℕ) :
    (chainA Sm Rm j)ᴴ *ᵥ contV vtx Marked s Sm Rm j ∈ h.Dom j :=
  h.mem_Dom ((h.pres_chainA j j le_rfl).2 _ (h.supp_contV j))

/-- **One tolerant pass of the compiled operators fails with probability `≤ 99/100`.** -/
theorem pass_fail_le {ε : ℝ} (hε : 0 < ε) (hm0 : ε ≤ goodProb vtx Marked s) {K : ℕ}
    (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) :
    qNormSq (contV vtx Marked s Sm Rm (K + 1)) ≤ 99 / 100 :=
  h.chainOK.qNormSq_contV_le h.contV_dom hε (by rw [h.chainOK.m_zero]; exact hm0) hK

end SearchInv

end QuantumQueryComplexity
