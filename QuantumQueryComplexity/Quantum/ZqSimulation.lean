import QuantumQueryComplexity.Quantum.ZqOracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Simulating the value oracle in the phase-oracle model over `Z_q`

A value-oracle algorithm is simulated in the phase model over `Z_q` at **two phase queries per
value query**, with exactly the same success on every input and for every relation
(`zqSuccessProbOn_simStdToZq`). This is the direction lower bounds need: a lower bound in the
phase model is a lower bound for value-oracle algorithms at half the query count.

The simulated value query uses one ancillary answer register `Option (ZMod q)`. It moves the
ancilla, holding `0`, into the answer position, adds `aᵢ` with one additive query (a Fourier-
conjugated phase query, `addOracleMat_eq_fourier_phase`), applies the value oracle's swap
`none ↔ some aᵢ` to the original answer register controlled on the ancilla and on a non-idle
index, and removes `aᵢ` with a second additive query after negating the ancilla.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι O W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
variable {q : ℕ} [NeZero q]
variable {X : Type} [Fintype X]

/-! ## The run in the phase model, packaged -/

namespace QRoutine

/-- The operator implemented by `R` against the phase oracle over `Z_q`. -/
noncomputable def zqRun (R : QRoutine ι (ZMod q) W) (a : ι → ZMod q) :
    Matrix (QBasis ι (ZMod q) W) (QBasis ι (ZMod q) W) ℂ :=
  R.runWith (phaseZqOracleMat a) R.len

theorem comp_zqRun (R S : QRoutine ι (ZMod q) W) (a : ι → ZMod q) :
    (R.comp S).zqRun a = S.zqRun a * R.zqRun a :=
  comp_runWith_full (phaseZqOracleMat a) R S

@[simp] lemma ofUnitary_zqRun (U : Matrix (QBasis ι (ZMod q) W) (QBasis ι (ZMod q) W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) W) ℂ) (a : ι → ZMod q) :
    (ofUnitary U hU).zqRun a = U := rfl

end QRoutine

/-! ## The gadget permutations

All on `QBasis ι (ZMod q) (Option (ZMod q) × W)`: index, answer, ancilla, workspace. -/

/-- Swap the answer register with the ancilla. -/
def zqSwapAncMap :
    QBasis ι (ZMod q) (Option (ZMod q) × W) → QBasis ι (ZMod q) (Option (ZMod q) × W)
  | (idx, t, (s, w)) => (idx, s, (t, w))

lemma zqSwapAncMap_involutive :
    Function.Involutive (zqSwapAncMap (ι := ι) (q := q) (W := W)) := by
  rintro ⟨idx, t, s, w⟩
  rfl

/-- On an active index with answer `some v`: swap `none ↔ some v` in the ancilla. -/
def zqCtrlSwapMap :
    QBasis ι (ZMod q) (Option (ZMod q) × W) → QBasis ι (ZMod q) (Option (ZMod q) × W)
  | (some i, some v, (t, w)) => (some i, some v, (Equiv.swap none (some v) t, w))
  | p => p

@[simp] lemma zqCtrlSwapMap_active (i : ι) (v : ZMod q) (t : Option (ZMod q)) (w : W) :
    zqCtrlSwapMap ((some i, some v, (t, w)) : QBasis ι (ZMod q) (Option (ZMod q) × W))
      = (some i, some v, (Equiv.swap none (some v) t, w)) := rfl

@[simp] lemma zqCtrlSwapMap_idle (s t : Option (ZMod q)) (w : W) :
    zqCtrlSwapMap ((none, s, (t, w)) : QBasis ι (ZMod q) (Option (ZMod q) × W))
      = (none, s, (t, w)) := by
  cases s <;> rfl

@[simp] lemma zqCtrlSwapMap_blank (i : ι) (t : Option (ZMod q)) (w : W) :
    zqCtrlSwapMap ((some i, none, (t, w)) : QBasis ι (ZMod q) (Option (ZMod q) × W))
      = (some i, none, (t, w)) := rfl

lemma zqCtrlSwapMap_involutive :
    Function.Involutive (zqCtrlSwapMap (ι := ι) (q := q) (W := W)) := by
  rintro ⟨(_ | i), (_ | v), t, w⟩ <;> simp

/-- Negate the `some`-part of the answer register. -/
def zqNegMap :
    QBasis ι (ZMod q) (Option (ZMod q) × W) → QBasis ι (ZMod q) (Option (ZMod q) × W)
  | (idx, t, x) => (idx, t.map Neg.neg, x)

lemma zqNegMap_involutive :
    Function.Involutive (zqNegMap (ι := ι) (q := q) (W := W)) := by
  rintro ⟨idx, (_ | c), x⟩ <;> simp [zqNegMap]

/-! ## The gadget unitaries -/

/-- The answer–ancilla swap. -/
def zqSwapAncMat : Matrix (QBasis ι (ZMod q) (Option (ZMod q) × W))
    (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ zqSwapAncMap_involutive)

lemma zqSwapAncMat_mem_unitaryGroup :
    zqSwapAncMat (ι := ι) (q := q) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma zqSwapAncMat_mulVec_apply (ψ : QBasis ι (ZMod q) (Option (ZMod q) × W) → ℂ)
    (p : QBasis ι (ZMod q) (Option (ZMod q) × W)) :
    (zqSwapAncMat *ᵥ ψ) p = ψ (zqSwapAncMap p) := by
  rw [zqSwapAncMat, qPerm_mulVec_apply]
  rfl

/-- The controlled-swap unitary. -/
def zqCtrlSwapMat : Matrix (QBasis ι (ZMod q) (Option (ZMod q) × W))
    (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ zqCtrlSwapMap_involutive)

lemma zqCtrlSwapMat_mem_unitaryGroup :
    zqCtrlSwapMat (ι := ι) (q := q) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma zqCtrlSwapMat_mulVec_apply (ψ : QBasis ι (ZMod q) (Option (ZMod q) × W) → ℂ)
    (p : QBasis ι (ZMod q) (Option (ZMod q) × W)) :
    (zqCtrlSwapMat *ᵥ ψ) p = ψ (zqCtrlSwapMap p) := by
  rw [zqCtrlSwapMat, qPerm_mulVec_apply]
  rfl

/-- The negation unitary on the answer register. -/
def zqNegMat : Matrix (QBasis ι (ZMod q) (Option (ZMod q) × W))
    (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ zqNegMap_involutive)

lemma zqNegMat_mem_unitaryGroup :
    zqNegMat (ι := ι) (q := q) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) (Option (ZMod q) × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma zqNegMat_mulVec_apply (ψ : QBasis ι (ZMod q) (Option (ZMod q) × W) → ℂ)
    (p : QBasis ι (ZMod q) (Option (ZMod q) × W)) :
    (zqNegMat *ᵥ ψ) p = ψ (zqNegMap p) := by
  rw [zqNegMat, qPerm_mulVec_apply]
  rfl

lemma addOracleMat_mulVec_apply (a : ι → ZMod q) (ψ : QBasis ι (ZMod q) W → ℂ)
    (p : QBasis ι (ZMod q) W) :
    (addOracleMat a *ᵥ ψ) p = ψ (addOracleMap (-a) p) := by
  rw [addOracleMat, qPerm_mulVec_apply]
  rfl

/-! ## The gadget -/

/-- **The phase model simulates one value query**: two phase queries. Before the first, swap
the ancilla into the answer position and open an additive query (`F†`); between them, close it
(`F`), apply the controlled swap, negate, and open the second additive query; after the second,
close it and swap back. -/
noncomputable def zqGadget : QRoutine ι (ZMod q) (Option (ZMod q) × W) where
  len := 2
  step := fun
    | 0 => ansFourierZqᴴ * zqSwapAncMat
    | 1 => ansFourierZqᴴ * (zqNegMat * zqCtrlSwapMat) * ansFourierZq
    | _ + 2 => zqSwapAncMat * ansFourierZq
  step_unitary := by
    have hF := ansFourierZq_mem_unitaryGroup (ι := ι) (q := q) (W := Option (ZMod q) × W)
    rintro (_ | _ | _)
    · exact mul_mem (conjTranspose_mem_qUnitary hF) zqSwapAncMat_mem_unitaryGroup
    · exact mul_mem (mul_mem (conjTranspose_mem_qUnitary hF)
        (mul_mem zqNegMat_mem_unitaryGroup zqCtrlSwapMat_mem_unitaryGroup)) hF
    · exact mul_mem zqSwapAncMat_mem_unitaryGroup hF

@[simp] lemma zqGadget_len : (zqGadget (ι := ι) (q := q) (W := W)).len = 2 := rfl

/-- The gadget's phase-model run is two additive queries around the free permutations. -/
lemma zqGadget_zqRun (a : ι → ZMod q) :
    (zqGadget (ι := ι) (W := W)).zqRun a
      = zqSwapAncMat * (addOracleMat a * ((zqNegMat * zqCtrlSwapMat)
          * (addOracleMat a * zqSwapAncMat))) := by
  rw [addOracleMat_eq_fourier_phase]
  change (zqSwapAncMat * ansFourierZq) * (phaseZqOracleMat a
      * ((ansFourierZqᴴ * (zqNegMat * zqCtrlSwapMat) * ansFourierZq)
        * (phaseZqOracleMat a * (ansFourierZqᴴ * zqSwapAncMat)))) = _
  simp only [Matrix.mul_assoc]

/-- **The gadget's action on the clean-ancilla sector** is exactly one value query. -/
theorem zqGadget_zqRun_embedReg (a : ι → ZMod q) (ψ : QBasis ι (ZMod q) W → ℂ) :
    (zqGadget (ι := ι) (W := W)).zqRun a *ᵥ embedReg (some 0) ψ
      = embedReg (some 0) (oracleMat a *ᵥ ψ) := by
  funext p
  rw [zqGadget_zqRun]
  simp only [← Matrix.mulVec_mulVec]
  rw [zqSwapAncMat_mulVec_apply, addOracleMat_mulVec_apply, zqNegMat_mulVec_apply,
    zqCtrlSwapMat_mulVec_apply, addOracleMat_mulVec_apply, zqSwapAncMat_mulVec_apply]
  obtain ⟨idx, t, s, w⟩ := p
  rcases idx with _ | i
  · rcases s with _ | c <;> simp [embedReg_apply, zqSwapAncMap, zqNegMap, addOracleMap]
  · rcases s with _ | c
    · simp [embedReg_apply, zqSwapAncMap, zqNegMap, addOracleMap]
    · by_cases hc : c = 0
      · subst hc
        simp [embedReg_apply, zqSwapAncMap, zqNegMap, addOracleMap]
      · simp [embedReg_apply, zqSwapAncMap, zqNegMap, addOracleMap, hc]

/-! ## The compiler -/

/-- Compile the first `t` value queries of a schedule into the phase model: lifted steps, one
`zqGadget` per query. -/
noncomputable def simZqUpto (R : QRoutine ι (ZMod q) W) :
    ℕ → QRoutine ι (ZMod q) (Option (ZMod q) × W)
  | 0 => QRoutine.ofUnitary (liftReg (Option (ZMod q)) (R.step 0))
      (liftReg_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simZqUpto R t).comp (zqGadget.comp
      (QRoutine.ofUnitary (liftReg (Option (ZMod q)) (R.step (t + 1)))
        (liftReg_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simZqUpto_len (R : QRoutine ι (ZMod q) W) (t : ℕ) :
    (simZqUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simZqUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, zqGadget_len, QRoutine.ofUnitary_len]
      omega

theorem simZqUpto_zqRun (R : QRoutine ι (ZMod q) W) (a : ι → ZMod q) (t : ℕ)
    (ψ : QBasis ι (ZMod q) W → ℂ) :
    (simZqUpto R t).zqRun a *ᵥ embedReg (some 0) ψ
      = embedReg (some 0) (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).zqRun a *ᵥ _ = _
      rw [QRoutine.ofUnitary_zqRun, liftReg_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simZqUpto R (t + 1)).zqRun a
          = liftReg (Option (ZMod q)) (R.step (t + 1))
              * (zqGadget.zqRun a * (simZqUpto R t).zqRun a) := by
        change ((simZqUpto R t).comp _).zqRun a = _
        rw [QRoutine.comp_zqRun, QRoutine.comp_zqRun, QRoutine.ofUnitary_zqRun,
          Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        zqGadget_zqRun_embedReg, liftReg_mulVec_embed, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-! ## The state bridges -/

/-- The value-oracle state is the run of the algorithm's own schedule. -/
lemma zq_state_eq_runUpto (A : QAlg ι (ZMod q) O W) (n : ℕ) (a : ι → ZMod q) (t : ℕ) :
    A.state a t = (QRoutine.mk n A.step A.step_unitary).runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The phase-model state of a packaged routine is its parametric run. -/
lemma zqState_toAlg (R : QRoutine ι (ZMod q) W) (init : QBasis ι (ZMod q) W → ℂ)
    (hinit : IsQState init) (r : QBasis ι (ZMod q) W → O) (a : ι → ZMod q) (t : ℕ) :
    zqState (R.toAlg init hinit r) a t = R.runWith (phaseZqOracleMat a) t *ᵥ init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [zqState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

/-! ## Simulating the value oracle in the phase model -/

/-- **The phase-model simulation of a value-oracle algorithm**, at two phase queries per value
query, with one ancillary answer register. Its construction is fixed by the exact identity
`zqSuccessProbOn_simStdToZq`. -/
noncomputable def QAlg.simStdToZq (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    QAlg ι (ZMod q) O (Option (ZMod q) × W) :=
  (simZqUpto (QRoutine.mk t A.step A.step_unitary) t).toAlg (embedReg (some 0) A.init)
    (isQState_embedReg (some 0) A.init_isQState) (stripReadout A.readout)

/-- The phase-model state of `A.simStdToZq t` after `2t` queries is `A`'s state after `t`
value queries, embedded with a clean ancilla. -/
lemma zqState_simStdToZq (A : QAlg ι (ZMod q) O W) (t : ℕ) (a : ι → ZMod q) :
    zqState (A.simStdToZq t) a (2 * t) = embedReg (some 0) (A.state a t) := by
  rw [QAlg.simStdToZq, zqState_toAlg, ← simZqUpto_len (QRoutine.mk t A.step A.step_unitary) t]
  change (simZqUpto (QRoutine.mk t A.step A.step_unitary) t).zqRun a *ᵥ _ = _
  rw [simZqUpto_zqRun, ← zq_state_eq_runUpto A t]

/-- **The value oracle in the phase model**: after `2t` phase queries the simulation succeeds
with exactly the probability that `A` succeeds after `t` value queries, on every input and for
every relation. -/
theorem zqSuccessProbOn_simStdToZq (A : QAlg ι (ZMod q) O W) (t : ℕ) (read : X → ι → ZMod q)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    zqSuccessProbOn (A.simStdToZq t) (2 * t) read Good x = successProbOn A t read Good x := by
  rw [zqSuccessProbOn, zqState_simStdToZq, successProbOn]
  exact qProb_stripReadout_embedReg (V := Option (ZMod q))
    (fun h => decide (Good x (A.readout h))) (some 0) true (A.state (read x) t)

end QuantumQueryComplexity
