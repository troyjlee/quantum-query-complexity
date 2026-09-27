import QuantumQueryComplexity.Quantum.Amplify
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Named coherent repetition and majority

`amplify` (`Amplify.lean`) packages repetition existentially.  Here the same construction is
*named*, so that a caller can run it inside a larger routine, invert it, and keep every
outcome register:

* `PowWork ι σ V k` — `k` banks, each a complete copy `QBasis ι σ V` of the machine;
* `powRoutine R k` — run `R` on each bank in turn, `k · R.len` queries (`powRoutine_len`);
* `powInit η k`, `powReadout rd k` — the product initial vector and the record of the `k`
  outcomes; nothing is erased: the bank contents (the garbage) stay in place;
* `qProb_powReadout` — **the exact product law** of the record, from the bank-swap compiler;
* `majReadout rd k` — the majority bit of the record, a function of the computational basis
  of the banks, hence readable, reflectable and copyable by input-independent operations at
  no query cost;
* `qProb_majReadout_not_le` — the majority is wrong with probability at most
  `(1+ε)^k / 2^⌈k/2⌉` (exponential moment, `Tail.lean`);
* `maj_twelve_le` — **from error `1/3`, `12·n` copies give error at most `2^{-n}`**:
  `(4/3)^12 ≤ 32`.  The cruder bound `2^k·ε^{⌈k/2⌉}` does not decay at `ε = 1/3` and is not
  used.

Statements are about an arbitrary initial vector `η` of the bank: when the bank is one
factor of a product with a spectator (`prodState`, `pairRoutine`), they apply to the factor.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V] [DecidableEq O]

/-- A function of the readout is read with the summed probabilities. -/
lemma qProb_comp {H O' : Type} [Fintype H] [Fintype O] [DecidableEq O'] (rd : H → O)
    (f : O → O') (ψ : H → ℂ) (o' : O') :
    qProb (f ∘ rd) ψ o' = ∑ o ∈ Finset.univ.filter (fun o => f o = o'), qProb rd ψ o := by
  simp only [qProb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-! ## The banks -/

/-- `k` complete copies of the machine with workspace `V`. -/
def PowWork (ι σ V : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => QBasis ι σ V × QBasis ι σ (PowWork ι σ V k)

noncomputable instance PowWork.fintype (ι σ V : Type) [Fintype ι] [Fintype σ] [Fintype V] :
    ∀ k, Fintype (PowWork ι σ V k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
      letI := PowWork.fintype ι σ V k
      inferInstanceAs (Fintype (QBasis ι σ V × QBasis ι σ (PowWork ι σ V k)))

instance PowWork.decEq (ι σ V : Type) [DecidableEq ι] [DecidableEq σ] [DecidableEq V] :
    ∀ k, DecidableEq (PowWork ι σ V k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 =>
      letI := PowWork.decEq ι σ V k
      inferInstanceAs (DecidableEq (QBasis ι σ V × QBasis ι σ (PowWork ι σ V k)))

/-- **Run `R` on each of the `k` banks.** -/
noncomputable def powRoutine (R : QRoutine ι σ V) : ∀ k, QRoutine ι σ (PowWork ι σ V k)
  | 0 => QRoutine.identity
  | k + 1 => pairRoutine R (powRoutine R k)

@[simp] theorem powRoutine_len (R : QRoutine ι σ V) (k : ℕ) :
    (powRoutine R k).len = k * R.len := by
  induction k with
  | zero => simp [powRoutine]
  | succ k ih =>
      rw [powRoutine, pairRoutine_len, ih]; ring

/-- The product initial vector. -/
noncomputable def powInit (η : QBasis ι σ V → ℂ) : ∀ k, QBasis ι σ (PowWork ι σ V k) → ℂ
  | 0 => qBasis ((none, none, ()) : QBasis ι σ Unit)
  | k + 1 => prodState blankReg η (powInit η k)

lemma isQState_powInit {η : QBasis ι σ V → ℂ} (hη : IsQState η) (k : ℕ) :
    IsQState (powInit η k) := by
  induction k with
  | zero => exact isQState_qBasis _
  | succ k ih => exact isQState_prodState hη ih

/-- The record of the `k` outcomes. -/
def powReadout (rd : QBasis ι σ V → O) : ∀ k, QBasis ι σ (PowWork ι σ V k) → (Fin k → O)
  | 0 => fun _ => Fin.elim0
  | k + 1 => fun p => Fin.cons (rd p.2.2.1) (powReadout rd k p.2.2.2)

/-- The state of the banks: the product of the `k` final states. -/
theorem powRoutine_run (R : QRoutine ι σ V) (a : ι → σ) (η : QBasis ι σ V → ℂ) (k : ℕ) :
    (powRoutine R k).run a *ᵥ powInit η k = powInit (R.run a *ᵥ η) k := by
  induction k with
  | zero => rw [powRoutine, QRoutine.identity_run, Matrix.one_mulVec]; rfl
  | succ k ih =>
      have h := pairRoutine_run_prodState R (powRoutine R k) a blankReg η (powInit η k)
      rw [ih] at h
      exact h

/-- **The exact product law of the record.** -/
theorem qProb_powReadout (rd : QBasis ι σ V → O) {ψ : QBasis ι σ V → ℂ} (k : ℕ)
    (y : Fin k → O) :
    qProb (powReadout rd k) (powInit ψ k) y = ∏ j, qProb rd ψ (y j) := by
  induction k with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.prod_empty]
      have h : qProb (powReadout rd 0) (powInit ψ 0) y = qNormSq (powInit ψ 0) := by
        rw [qProb, qNormSq_def]
        refine Finset.sum_congr rfl fun h _ => if_pos (Subsingleton.elim _ _)
      rw [h]
      exact isQState_qBasis _
  | succ k ih =>
      have h : qProb (powReadout rd (k + 1)) (powInit ψ (k + 1)) y
          = qProb (pairReadout rd (powReadout rd k)) (prodState blankReg ψ (powInit ψ k))
              (y 0, Fin.tail y) := by
        rw [qProb, qProb]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hiff : powReadout rd (k + 1) p = y
            ↔ pairReadout rd (powReadout rd k) p = (y 0, Fin.tail y) := by
          show Fin.cons (rd p.2.2.1) (powReadout rd k p.2.2.2) = y
            ↔ (rd p.2.2.1, powReadout rd k p.2.2.2) = (y 0, Fin.tail y)
          rw [Prod.mk.injEq]
          constructor
          · rintro rfl
            exact ⟨rfl, rfl⟩
          · rintro ⟨h1, h2⟩
            rw [h1, h2, Fin.cons_self_tail]
        by_cases hp : powReadout rd (k + 1) p = y
        · rw [if_pos hp, if_pos (hiff.mp hp)]; rfl
        · rw [if_neg hp, if_neg (fun h' => hp (hiff.mpr h'))]
      rw [h, qProb_pairReadout, sum_normSq_blankReg, one_mul, ih, Fin.prod_univ_succ]
      rfl

/-! ## The majority bit -/

/-- **The majority bit of the record.** -/
def majReadout (rd : QBasis ι σ V → Bool) (k : ℕ) : QBasis ι σ (PowWork ι σ V k) → Bool :=
  majVote k ∘ powReadout rd k

/-- **The majority is wrong with exponentially small probability.** -/
theorem qProb_majReadout_not_le (rd : QBasis ι σ V → Bool) {ψ : QBasis ι σ V → ℂ}
    (hψ : IsQState ψ) (b : Bool) {ε : ℝ} (hε : qProb rd ψ (!b) ≤ ε) (k : ℕ) :
    qProb (majReadout rd k) (powInit ψ k) (!b) ≤ (1 + ε) ^ k / 2 ^ ((k + 1) / 2) := by
  rw [majReadout, qProb_comp, le_div_iff₀ (by positivity)]
  have hsub : Finset.univ.filter (fun y : Fin k → Bool => majVote k y = !b)
      ⊆ Finset.univ.filter (fun y : Fin k → Bool =>
          (k + 1) / 2 ≤ wrongCount y (fun _ => b)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact le_card_wrong_of_majVote_ne (by rw [hy]; cases b <;> simp)
  have hsum : ∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => majVote k y = !b),
        qProb (powReadout rd k) (powInit ψ k) y
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
          (k + 1) / 2 ≤ wrongCount y (fun _ => b)), ∏ j, qProb rd ψ (y j) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun y _ _ => qProb_nonneg _ _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun y _ => qProb_powReadout rd k y
  refine le_trans (mul_le_mul_of_nonneg_right hsum (by positivity)) ?_
  refine sum_prod_tail_le (fun _ o => qProb rd ψ o) (fun _ => b)
    (fun _ o => qProb_nonneg _ _ _) (fun _ => le_of_eq (sum_qProb_eq_one hψ rd)) fun _ => ?_
  have : Finset.univ.filter (fun o : Bool => o ≠ b) = {!b} := by
    ext o; cases o <;> cases b <;> simp
  rw [this, Finset.sum_singleton]
  exact hε

/-- **From error `1/3`, `12·n` copies give error at most `2^{-n}`.** -/
theorem maj_twelve_le (rd : QBasis ι σ V → Bool) {ψ : QBasis ι σ V → ℂ} (hψ : IsQState ψ)
    (b : Bool) (hε : qProb rd ψ (!b) ≤ 1 / 3) (n : ℕ) :
    qProb (majReadout rd (12 * n)) (powInit ψ (12 * n)) (!b) ≤ (1 / 2) ^ n := by
  refine (qProb_majReadout_not_le rd hψ b hε (12 * n)).trans ?_
  have hk : (12 * n + 1) / 2 = 6 * n := by omega
  rw [hk, pow_mul, pow_mul, ← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  norm_num

/-- The right answer therefore has probability at least `1 − 2^{-n}`. -/
theorem one_sub_le_maj_twelve (rd : QBasis ι σ V → Bool) {ψ : QBasis ι σ V → ℂ}
    (hψ : IsQState ψ) (b : Bool) (hε : qProb rd ψ (!b) ≤ 1 / 3) (n : ℕ) :
    1 - (1 / 2) ^ n ≤ qProb (majReadout rd (12 * n)) (powInit ψ (12 * n)) b := by
  have h := maj_twelve_le rd hψ b hε n
  have hsum := sum_qProb_eq_one (isQState_powInit hψ (12 * n)) (majReadout rd (12 * n))
  rw [Fintype.sum_bool] at hsum
  cases b
  · simp only [Bool.not_false] at h; linarith
  · simp only [Bool.not_true] at h; linarith

end QuantumQueryComplexity
