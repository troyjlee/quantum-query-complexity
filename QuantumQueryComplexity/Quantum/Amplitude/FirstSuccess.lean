import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Amplify
set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Named output combinators: pairing, reshaping, and "first success"

`ProductRun.lean` packages the pair compiler and the free reshaping of outcomes as
*existential* statements (`Realizes.pair`, `Realizes.map`).  Amplitude amplification must
hand its caller an actual algorithm, so the same constructions are named here:

* `QAlg.pairAlg A₁ q₁ A₂ q₂`: run both, `q₁ + q₂` queries, exact product law;
* `QAlg.mapOut g A`: relabel the outcome through the (input-independent) readout, free;
* `QAlg.orElse A₁ q₁ A₂ q₂`: two `Option`-valued trials, return the first `some`.  Choosing
  the first flagged output is a readout of stored outputs, hence free.  Its law:

      Pr[some y] = P₁(some y) + P₁(none)·P₂(some y),      Pr[none] = P₁(none)·P₂(none).

The Boolean `Realizes.fold` of `Amplify.lean` is untouched.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W W₁ W₂ : Type} [Fintype W] [DecidableEq W] [Fintype W₁] [DecidableEq W₁]
  [Fintype W₂] [DecidableEq W₂]
variable {O O' O₁ O₂ : Type} [DecidableEq O] [DecidableEq O'] [DecidableEq O₁] [DecidableEq O₂]

namespace QAlg

/-- **Run two algorithms side by side**, for `q₁` and `q₂` queries. -/
def pairAlg (A₁ : QAlg ι σ O₁ W₁) (q₁ : ℕ) (A₂ : QAlg ι σ O₂ W₂) (q₂ : ℕ) :
    QAlg ι σ (O₁ × O₂) (QBasis ι σ W₁ × QBasis ι σ W₂) :=
  (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
      (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
    (prodState blankReg A₁.init A₂.init)
    (isQState_prodState A₁.init_isQState A₂.init_isQState)
    (pairReadout A₁.readout A₂.readout)

/-- **The exact product law**, at `q₁ + q₂` queries. -/
theorem pairAlg_prob (A₁ : QAlg ι σ O₁ W₁) (q₁ : ℕ) (A₂ : QAlg ι σ O₂ W₂) (q₂ : ℕ)
    (a : ι → σ) (o₁ : O₁) (o₂ : O₂) :
    (pairAlg A₁ q₁ A₂ q₂).prob a (q₁ + q₂) (o₁, o₂) = A₁.prob a q₁ o₁ * A₂.prob a q₂ o₂ := by
  have hlen : (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
      (QRoutine.mk q₂ A₂.step A₂.step_unitary)).len = q₁ + q₂ := by
    rw [pairRoutine_len]
  have hstate : (pairAlg A₁ q₁ A₂ q₂).state a (q₁ + q₂)
      = prodState blankReg (A₁.state a q₁) (A₂.state a q₂) := by
    rw [pairAlg, ← hlen, QRoutine.toAlg_state_len, pairRoutine_run_prodState]
    rw [show (QRoutine.mk q₁ A₁.step A₁.step_unitary).run a
        = (QRoutine.mk q₁ A₁.step A₁.step_unitary).runUpto a q₁ from rfl,
      ← state_eq_runUpto2 A₁ q₁]
    rw [show (QRoutine.mk q₂ A₂.step A₂.step_unitary).run a
        = (QRoutine.mk q₂ A₂.step A₂.step_unitary).runUpto a q₂ from rfl,
      ← state_eq_runUpto2 A₂ q₂]
  rw [QAlg.prob, hstate]
  show qProb (pairReadout A₁.readout A₂.readout) _ (o₁, o₂) = _
  rw [qProb_pairReadout, sum_normSq_blankReg, one_mul]
  rfl

/-- **Relabel the outcome through the readout** — free. -/
def mapOut (g : O → O') (A : QAlg ι σ O W) : QAlg ι σ O' W where
  init := A.init
  init_isQState := A.init_isQState
  step := A.step
  step_unitary := A.step_unitary
  readout := fun p => g (A.readout p)

lemma mapOut_state (g : O → O') (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    (mapOut g A).state a t = A.state a t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [QAlg.state_succ, ih]; rfl

/-- The relabelled law: the preimage's total probability. -/
theorem mapOut_prob [Fintype O] (g : O → O') (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ)
    (o' : O') :
    (mapOut g A).prob a t o' = ∑ o, if g o = o' then A.prob a t o else 0 := by
  rw [QAlg.prob, mapOut_state]
  show qProb (fun p => g (A.readout p)) _ o' = _
  simp only [QAlg.prob, qProb]
  rw [show (∑ o, if g o = o' then
        ∑ h, (if A.readout h = o then Complex.normSq (A.state a t h) else 0) else 0)
      = ∑ o, ∑ h, if A.readout h = o then
          (if g o = o' then Complex.normSq (A.state a t h) else 0) else 0 from
    Finset.sum_congr rfl fun o _ => by
      split_ifs
      · exact Finset.sum_congr rfl fun h _ => by split_ifs <;> rfl
      · exact (Finset.sum_eq_zero fun h _ => by split_ifs <;> rfl).symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (A.readout h), if_pos (Finset.mem_univ _)]

end QAlg

/-- The first `some` of two optional outputs. -/
def firstSome : Option O × Option O → Option O
  | (some y, _) => some y
  | (none, o) => o

namespace QAlg

/-- **Two verified trials, first success**: `q₁ + q₂` queries. -/
def orElse (A₁ : QAlg ι σ (Option O) W₁) (q₁ : ℕ) (A₂ : QAlg ι σ (Option O) W₂) (q₂ : ℕ) :
    QAlg ι σ (Option O) (QBasis ι σ W₁ × QBasis ι σ W₂) :=
  mapOut firstSome (pairAlg A₁ q₁ A₂ q₂)

variable [Fintype O]

theorem orElse_prob_some (A₁ : QAlg ι σ (Option O) W₁) (q₁ : ℕ)
    (A₂ : QAlg ι σ (Option O) W₂) (q₂ : ℕ) (a : ι → σ) (y : O) :
    (orElse A₁ q₁ A₂ q₂).prob a (q₁ + q₂) (some y)
      = A₁.prob a q₁ (some y) + A₁.prob a q₁ none * A₂.prob a q₂ (some y) := by
  rw [orElse, mapOut_prob, Fintype.sum_prod_type, Fintype.sum_option]
  have hnone : (∑ o₂ : Option O, if firstSome ((none : Option O), o₂) = some y
      then (pairAlg A₁ q₁ A₂ q₂).prob a (q₁ + q₂) (none, o₂) else 0)
      = A₁.prob a q₁ none * A₂.prob a q₂ (some y) := by
    rw [Finset.sum_eq_single (some y)]
    · rw [if_pos (by rfl), pairAlg_prob]
    · intro o₂ _ ho
      rw [if_neg (by simpa [firstSome] using ho)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsome : (∑ z : O, ∑ o₂ : Option O, if firstSome (some z, o₂) = some y
      then (pairAlg A₁ q₁ A₂ q₂).prob a (q₁ + q₂) (some z, o₂) else 0)
      = A₁.prob a q₁ (some y) := by
    rw [Finset.sum_eq_single y]
    · simp only [firstSome, if_true]
      simp_rw [pairAlg_prob]
      rw [← Finset.mul_sum, QAlg.sum_prob, mul_one]
    · intro z _ hz
      refine Finset.sum_eq_zero fun o₂ _ => ?_
      rw [if_neg (by simpa [firstSome] using hz)]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hnone, hsome, add_comm]

theorem orElse_prob_none (A₁ : QAlg ι σ (Option O) W₁) (q₁ : ℕ)
    (A₂ : QAlg ι σ (Option O) W₂) (q₂ : ℕ) (a : ι → σ) :
    (orElse A₁ q₁ A₂ q₂).prob a (q₁ + q₂) none
      = A₁.prob a q₁ none * A₂.prob a q₂ none := by
  rw [orElse, mapOut_prob, Fintype.sum_prod_type, Fintype.sum_option]
  have hsome : (∑ z : O, ∑ o₂ : Option O, if firstSome (some z, o₂) = (none : Option O)
      then (pairAlg A₁ q₁ A₂ q₂).prob a (q₁ + q₂) (some z, o₂) else 0) = 0 :=
    Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun o₂ _ => by simp [firstSome]
  rw [hsome, add_zero, Finset.sum_eq_single none]
  · rw [if_pos (by rfl), pairAlg_prob]
  · intro o₂ _ ho
    rw [if_neg (by simpa [firstSome] using ho)]
  · intro h; exact absurd (Finset.mem_univ _) h

end QAlg

end QuantumQueryComplexity
