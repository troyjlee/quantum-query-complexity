import QuantumQueryComplexity.Quantum.Control
import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Padding an algorithm, and monotonicity of the achievable query counts

`QueryCounts` should be upward closed — an algorithm that succeeds with `q`
queries should succeed with `q'` for any `q' ≥ q` — but that is not free in this
model: every query is a real query unless the index register happens to be idle
when it fires.  Making it idle is exactly what `Control.lean` built.

The padded algorithm runs the original under `QRoutine.control` with the control
bit **`true`**, flips the bit to `false` (a basis permutation, no queries), and
then spends the remaining `q' - q` queries parked, where each is the identity.
The readout drops the two added registers.

  `padAlg_state` : the padded state after `q + n` queries is
                   `embedCtrl false (A.state a q)`
  `padAlg_prob`  : hence every outcome probability is unchanged
  `queryCounts_upward` : `q ∈ QueryCounts → q ≤ q' → q' ∈ QueryCounts`

The embedding lemmas at the top say why the readout can ignore the extra
registers: `embedReg` preserves squared norms and outcome probabilities, being
an isometry onto a sector.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O V W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## The embedding is an isometry onto its sector -/

-- `sum_reg`, `embedReg_regEquiv_symm` and `qNormSq_embedReg` live in `Blocks.lean`,
-- next to `embedReg` itself: the orthogonality of the sectors is a fact about the
-- embedding, not about padding.

lemma qProb_embedReg (p : QBasis ι σ W → O) (v : V) (ψ : QBasis ι σ W → ℂ) (o : O) :
    qProb (fun r => p (r.1, r.2.1, r.2.2.2)) (embedReg v ψ) o = qProb p ψ o := by
  rw [qProb, sum_reg, qProb]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single v]
  · rw [embedReg_regEquiv_symm, if_pos rfl]
    rfl
  · intro u _ hu
    rw [embedReg_regEquiv_symm, if_neg hu, Complex.normSq_zero]
    simp
  · simp

lemma qNormSq_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedCtrl b ψ) = qNormSq ψ := by
  rw [embedCtrl, qNormSq_embedReg, qNormSq_embedReg]

lemma isQState_embedCtrl (b : Bool) {ψ : QBasis ι σ W → ℂ} (h : IsQState ψ) :
    IsQState (embedCtrl b ψ) := by
  rw [IsQState, qNormSq_embedCtrl]
  exact h

/-- The readout of a padded algorithm: ignore the control bit and the slot. -/
def dropCtrl (p : QBasis ι σ W → O) : QBasis ι σ (CtrlWork ι W) → O :=
  fun r => p (r.1, r.2.1, r.2.2.2.2)

lemma qProb_embedCtrl (p : QBasis ι σ W → O) (b : Bool) (ψ : QBasis ι σ W → ℂ)
    (o : O) : qProb (dropCtrl p) (embedCtrl b ψ) o = qProb p ψ o := by
  have h1 : qProb (fun r : QBasis ι σ (Option ι × W) => p (r.1, r.2.1, r.2.2.2))
      (embedReg none ψ) o = qProb p ψ o := qProb_embedReg p none ψ o
  have h2 := qProb_embedReg
    (fun r : QBasis ι σ (Option ι × W) => p (r.1, r.2.1, r.2.2.2)) b
    (embedReg none ψ) o
  rw [h1] at h2
  exact h2

/-! ## Flipping the control bit -/

def flipMap : QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W)
  | (k, t, (b, s, w)) => (k, t, (!b, s, w))

lemma flipMap_involutive :
    Function.Involutive (flipMap (ι := ι) (σ := σ) (W := W)) := by
  rintro ⟨k, t, b, s, w⟩
  cases b <;> rfl

def flipPerm : Equiv.Perm (QBasis ι σ (CtrlWork ι W)) :=
  Function.Involutive.toPerm _ flipMap_involutive

def flipMat : Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm flipPerm

lemma flipMat_mem_unitaryGroup :
    flipMat (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma flipMat_mulVec_apply (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) : (flipMat *ᵥ ψ) p = ψ (flipMap p) := by
  rw [flipMat, qPerm_mulVec_apply]
  rfl

lemma flipMat_mulVec_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    flipMat *ᵥ embedCtrl b ψ = embedCtrl (!b) ψ := by
  funext p
  rw [flipMat_mulVec_apply, embedCtrl_apply, embedCtrl_apply]
  obtain ⟨k, t, b', s, w⟩ := p
  cases b <;> cases b' <;> simp [flipMap]

/-! ## Idling -/

/-- `n` parked queries. -/
def idleRoutine : ℕ → QRoutine ι σ (CtrlWork ι W)
  | 0 => QRoutine.identity
  | n + 1 => (idleRoutine n).comp ctrlQueryRoutine

lemma idleRoutine_len (n : ℕ) :
    (idleRoutine (ι := ι) (σ := σ) (W := W) n).len = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (idleRoutine n).len + 1 = n + 1
      rw [ih]

lemma idleRoutine_run_of_parked (a : ι → σ) (n : ℕ)
    {ψ : QBasis ι σ (CtrlWork ι W) → ℂ} (h : IsParked ψ) :
    (idleRoutine n).run a *ᵥ ψ = ψ := by
  induction n with
  | zero =>
      show (1 : Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ) *ᵥ ψ = ψ
      rw [Matrix.one_mulVec]
  | succ n ih =>
      show ((idleRoutine n).comp ctrlQueryRoutine).run a *ᵥ ψ = ψ
      rw [QRoutine.comp_run, ctrlQueryRoutine_run, ← Matrix.mulVec_mulVec, ih,
        ctrlQuery_mulVec_of_parked a h]

/-! ## The padded algorithm -/

/-- An algorithm's state is its schedule, read as a routine. -/
lemma QAlg.state_eq_runUpto (A : QAlg ι σ O W) (R : QRoutine ι σ W)
    (hR : R.step = A.step) (a : ι → σ) (t : ℕ) :
    A.state a t = R.runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rw [QAlg.state_zero, QRoutine.runUpto_zero, hR]
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, hR]

/-- The routine of a padded algorithm: run controlled, flip the bit, then idle. -/
def padRoutine (A : QAlg ι σ O W) (q n : ℕ) : QRoutine ι σ (CtrlWork ι W) :=
  (((⟨q, A.step, A.step_unitary⟩ : QRoutine ι σ W).control).comp
      (QRoutine.ofUnitary flipMat flipMat_mem_unitaryGroup)).comp (idleRoutine n)

lemma padRoutine_len (A : QAlg ι σ O W) (q n : ℕ) :
    (padRoutine A q n).len = q + n := by
  show ((⟨q, A.step, A.step_unitary⟩ : QRoutine ι σ W).control.len + 0)
    + (idleRoutine (ι := ι) (σ := σ) (W := W) n).len = q + n
  rw [control_len, idleRoutine_len]
  rfl

/-- **The padded algorithm.** -/
def padAlg (A : QAlg ι σ O W) (q n : ℕ) : QAlg ι σ O (CtrlWork ι W) :=
  (padRoutine A q n).toAlg (embedCtrl true A.init)
    (isQState_embedCtrl true A.init_isQState) (dropCtrl A.readout)

lemma padRoutine_run (A : QAlg ι σ O W) (q n : ℕ) (a : ι → σ) :
    (padRoutine A q n).run a *ᵥ embedCtrl true A.init
      = embedCtrl false (A.state a q) := by
  rw [padRoutine, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, control_run_true,
    flipMat_mulVec_embedCtrl, Bool.not_true,
    idleRoutine_run_of_parked a n (isParked_embedCtrl_false _)]
  congr 1
  exact (A.state_eq_runUpto ⟨q, A.step, A.step_unitary⟩ rfl a q).symm

/-- **The padded state**: the original computation, embedded in the idle
sector. -/
theorem padAlg_state (A : QAlg ι σ O W) (q n : ℕ) (a : ι → σ) :
    (padAlg A q n).state a (q + n) = embedCtrl false (A.state a q) := by
  rw [← padRoutine_len A q n, padAlg, QRoutine.toAlg_state_len, padRoutine_run]

/-- **Padding changes no outcome probability.** -/
theorem padAlg_prob (A : QAlg ι σ O W) (q n : ℕ) (a : ι → σ) (o : O) :
    (padAlg A q n).prob a (q + n) o = A.prob a q o := by
  rw [QAlg.prob, padAlg_state]
  show qProb (dropCtrl A.readout) (embedCtrl false (A.state a q)) o = _
  rw [qProb_embedCtrl]
  rfl

/-! ## Monotonicity -/

variable {X : Type} [Fintype X]

theorem computesWithErrorOn_padAlg {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ}
    {f : X → O} {ε : ℝ} (h : ComputesWithErrorOn A q read f ε) (n : ℕ) :
    ComputesWithErrorOn (padAlg A q n) (q + n) read f ε := by
  intro x
  rw [padAlg_prob]
  exact h x

/-- **The achievable query counts are upward closed.** -/
theorem queryCounts_upward {read : X → ι → σ} {f : X → O} {ε : ℝ} {q q' : ℕ}
    (hq : q ∈ QueryCounts read f ε) (hle : q ≤ q') :
    q' ∈ QueryCounts read f ε := by
  obtain ⟨W', hW', hW'', A, hA⟩ := hq
  letI := hW'
  letI := hW''
  have hsplit : q' = q + (q' - q) := by omega
  rw [hsplit]
  exact mem_queryCounts (computesWithErrorOn_padAlg hA (q' - q))

end QuantumQueryComplexity
