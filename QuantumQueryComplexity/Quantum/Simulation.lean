import QuantumQueryComplexity.Quantum.XorOracle
import QuantumQueryComplexity.Quantum.Blocks
import QuantumQueryComplexity.Quantum.ReadAll
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Oracle simulation: transposition ↔ XOR, at two queries per query

The model-equivalence theorem of Milestone B step 7, for Boolean input
alphabets.  Each direction is one **two-query gadget** on a clean-ancilla
encoded subspace (`embedReg` with an `Option Bool` ancilla register), compiled
over whole routines at exactly `2·R.len` queries, and exported as a
`QueryCounts` translation:

    q ∈ XorQueryCounts read f ε  →  2q ∈ QueryCounts read f ε
    q ∈ QueryCounts read f ε     →  2q ∈ XorQueryCounts read f ε

with the complexity inequalities

    qQueryOn read f ε ≤ 2 · xorQQueryOn read f ε
    xorQQueryOn read f ε ≤ 2 · qQueryOn read f ε.

**The gadgets.**  With ancilla `v`, answer `t`:

* transposition simulates XOR (`xorGadget`, clean value `⊥`):
  swap `t ↔ v`, query (`⊥ ↦ a i`), XOR the answer into the ancilla, unquery,
  swap back — `swap · O · xorInto · O · swap`;
* XOR simulates transposition (`transGadget`, clean value `some false`):
  swap, query (`some false ↦ some (a i)`), controlled-swap `⊥ ↔ some v` on
  the ancilla where `v` is the answer's value, unquery, swap back —
  `swap · Oˣ · ctrlSwap · Oˣ · swap`.

Both middle unitaries are input-independent basis permutations; the
controlled swap is additionally controlled on the index register being
active, which is what keeps the idle sector exactly fixed.  Off the clean
sector each gadget moves the ancilla away from the clean value, so the
encoded-subspace statements hold with no side condition.

The compilers are compositional (`QRoutine.comp` + `ofUnitary` of lifted
steps, exactly like `selectPowers`), with `comp_run` sequencing the standard
side and `comp_runWith`/`xorRun` (from `RunWith.lean`) the XOR side.

Boolean specifically: for an arbitrary alphabet there is no canonical XOR
directly on `σ` without choosing a group structure on `σ`; the transposition
oracle is the alphabet-free primitive, which is why it is this development's
native model.  Milestone G (`OneHotSimulation.lean`) handles arbitrary finite
alphabets by XORing the letter's one-hot *encoding* into a `Hot σ` register,
with the same two-queries-per-query gadget pattern as here.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-! ## The run in the XOR model, packaged -/

namespace QRoutine

/-- The operator implemented by `R` against the XOR oracle. -/
def xorRun (R : QRoutine ι Bool W) (a : ι → Bool) :
    Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  R.runWith (xorOracleMat a) R.len

theorem comp_xorRun (R S : QRoutine ι Bool W) (a : ι → Bool) :
    (R.comp S).xorRun a = S.xorRun a * R.xorRun a :=
  comp_runWith_full (xorOracleMat a) R S

@[simp] lemma ofUnitary_xorRun (U : Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ) (a : ι → Bool) :
    (ofUnitary U hU).xorRun a = U := rfl

end QRoutine

/-! ## The gadget permutations

All on `QBasis ι Bool (Option Bool × W)`: index, answer, ancilla,
workspace. -/

/-- Swap the answer register with the ancilla. -/
def swapAncMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (idx, t, (v, w)) => (idx, v, (t, w))

@[simp] lemma swapAncMap_apply (idx : Option ι) (t v : Option Bool) (w : W) :
    swapAncMap ((idx, t, (v, w)) : QBasis ι Bool (Option Bool × W))
      = (idx, v, (t, w)) := rfl

lemma swapAncMap_involutive :
    Function.Involutive (swapAncMap (ι := ι) (W := W)) := by
  rintro ⟨idx, t, v, w⟩
  rfl

/-- XOR the answer register's value into the ancilla. -/
def xorIntoMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (idx, s, (t, w)) => (idx, s, (optXor t s, w))

@[simp] lemma xorIntoMap_apply (idx : Option ι) (s t : Option Bool) (w : W) :
    xorIntoMap ((idx, s, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (idx, s, (optXor t s, w)) := rfl

lemma xorIntoMap_involutive :
    Function.Involutive (xorIntoMap (ι := ι) (W := W)) := by
  rintro ⟨idx, s, t, w⟩
  simp [optXor_optXor]

/-- On an active index with answer `some v`: swap `⊥ ↔ some v` in the
ancilla.  Controlled on the index being active, so the idle sector is exactly
fixed. -/
def ctrlSwapMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (some i, some v, (t, w)) => (some i, some v, (Equiv.swap none (some v) t, w))
  | p => p

@[simp] lemma ctrlSwapMap_active (i : ι) (v : Bool) (t : Option Bool) (w : W) :
    ctrlSwapMap ((some i, some v, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (some i, some v, (Equiv.swap none (some v) t, w)) := rfl

@[simp] lemma ctrlSwapMap_idle (s : Option Bool) (t : Option Bool) (w : W) :
    ctrlSwapMap ((none, s, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (none, s, (t, w)) := by
  cases s <;> rfl

@[simp] lemma ctrlSwapMap_blank (i : ι) (t : Option Bool) (w : W) :
    ctrlSwapMap ((some i, none, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (some i, none, (t, w)) := rfl

lemma ctrlSwapMap_involutive :
    Function.Involutive (ctrlSwapMap (ι := ι) (W := W)) := by
  rintro ⟨(_ | i), (_ | v), t, w⟩ <;> simp

/-! ## The gadget unitaries -/

/-- The answer–ancilla swap. -/
def swapAncMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ swapAncMap_involutive)

lemma swapAncMat_mem_unitaryGroup :
    swapAncMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma swapAncMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (swapAncMat *ᵥ ψ) p = ψ (swapAncMap p) := by
  rw [swapAncMat, qPerm_mulVec_apply]
  rfl

/-- The XOR-into-the-ancilla unitary. -/
def xorIntoMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ xorIntoMap_involutive)

lemma xorIntoMat_mem_unitaryGroup :
    xorIntoMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma xorIntoMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (xorIntoMat *ᵥ ψ) p = ψ (xorIntoMap p) := by
  rw [xorIntoMat, qPerm_mulVec_apply]
  rfl

/-- The controlled-swap unitary. -/
def ctrlSwapMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ ctrlSwapMap_involutive)

lemma ctrlSwapMat_mem_unitaryGroup :
    ctrlSwapMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma ctrlSwapMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (ctrlSwapMat *ᵥ ψ) p = ψ (ctrlSwapMap p) := by
  rw [ctrlSwapMat, qPerm_mulVec_apply]
  rfl

/-! ## The two gadgets -/

/-- **Transposition simulates XOR**: two physical queries. -/
def xorGadget : QRoutine ι Bool (Option Bool × W) where
  len := 2
  step := fun t => if t = 1 then xorIntoMat else swapAncMat
  step_unitary := by
    intro t
    split_ifs
    · exact xorIntoMat_mem_unitaryGroup
    · exact swapAncMat_mem_unitaryGroup

@[simp] lemma xorGadget_len : (xorGadget (ι := ι) (W := W)).len = 2 := rfl

/-- **XOR simulates transposition**: two physical queries. -/
def transGadget : QRoutine ι Bool (Option Bool × W) where
  len := 2
  step := fun t => if t = 1 then ctrlSwapMat else swapAncMat
  step_unitary := by
    intro t
    split_ifs
    · exact ctrlSwapMat_mem_unitaryGroup
    · exact swapAncMat_mem_unitaryGroup

@[simp] lemma transGadget_len : (transGadget (ι := ι) (W := W)).len = 2 := rfl

/-- **The XOR gadget's action on the clean-ancilla sector** is exactly one
XOR query. -/
theorem xorGadget_run (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ) :
    (xorGadget (ι := ι) (W := W)).run a *ᵥ embedReg none ψ
      = embedReg none (xorOracleMat a *ᵥ ψ) := by
  have hrun : (xorGadget (ι := ι) (W := W)).run a
      = swapAncMat * (oracleMat a * (xorIntoMat * (oracleMat a * swapAncMat))) :=
    rfl
  funext p
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapAncMat_mulVec_apply, oracleMat_mulVec_apply, xorIntoMat_mulVec_apply,
    oracleMat_mulVec_apply, swapAncMat_mulVec_apply]
  obtain ⟨idx, t, v, w⟩ := p
  rcases idx with _ | i
  · rcases v with _ | c <;>
      simp [embedReg_apply, xorOracleMat_mulVec_apply]
  · rcases v with _ | c
    · -- clean ancilla, active index: the simulated query
      cases hai : a i <;> rcases t with _ | tb <;>
        simp [hai, embedReg_apply, xorOracleMat_mulVec_apply,
          Equiv.swap_apply_def, optXor]
    · -- dirty ancilla: the ancilla stays dirty, both sides vanish
      cases hai : a i <;> rcases c with _ | _ <;>
        simp [hai, embedReg_apply, Equiv.swap_apply_def, optXor]

/-- **The transposition gadget's action on the clean-ancilla sector** is
exactly one transposition query, under XOR semantics. -/
theorem transGadget_xorRun (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ) :
    (transGadget (ι := ι) (W := W)).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (oracleMat a *ᵥ ψ) := by
  have hrun : (transGadget (ι := ι) (W := W)).xorRun a
      = swapAncMat * (xorOracleMat a
          * (ctrlSwapMat * (xorOracleMat a * swapAncMat))) := rfl
  funext p
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapAncMat_mulVec_apply, xorOracleMat_mulVec_apply,
    ctrlSwapMat_mulVec_apply, xorOracleMat_mulVec_apply,
    swapAncMat_mulVec_apply]
  obtain ⟨idx, t, v, w⟩ := p
  rcases idx with _ | i
  · rcases v with _ | c <;>
      simp [embedReg_apply, oracleMat_mulVec_apply]
  · rcases v with _ | c
    · -- blank ancilla: the XOR oracle fixes it, both sides vanish
      simp [embedReg_apply, optXor]
    · -- clean ancilla `some false`: the simulated transposition;
      -- dirty `some true`: stays dirty, both sides vanish
      cases hai : a i <;> rcases c with _ | _ <;>
        simp [hai, embedReg_apply, oracleMat_mulVec_apply,
          Equiv.swap_apply_def, optXor]

/-! ## The compilers -/

/-- Compile the first `t` XOR queries of a schedule into the transposition
model: lifted steps, one `xorGadget` per query. -/
def simXorUpto (R : QRoutine ι Bool W) : ℕ → QRoutine ι Bool (Option Bool × W)
  | 0 => QRoutine.ofUnitary (liftReg (Option Bool) (R.step 0))
      (liftReg_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simXorUpto R t).comp (xorGadget.comp
      (QRoutine.ofUnitary (liftReg (Option Bool) (R.step (t + 1)))
        (liftReg_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simXorUpto_len (R : QRoutine ι Bool W) (t : ℕ) :
    (simXorUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show ((simXorUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, xorGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simXorUpto_run (R : QRoutine ι Bool W) (a : ι → Bool) (t : ℕ)
    (ψ : QBasis ι Bool W → ℂ) :
    (simXorUpto R t).run a *ᵥ embedReg none ψ
      = embedReg none (R.runWith (xorOracleMat a) t *ᵥ ψ) := by
  induction t with
  | zero =>
      show (QRoutine.ofUnitary _ _).run a *ᵥ _ = _
      rw [QRoutine.ofUnitary_run, liftReg_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simXorUpto R (t + 1)).run a
          = liftReg (Option Bool) (R.step (t + 1))
              * (xorGadget.run a * (simXorUpto R t).run a) := by
        show ((simXorUpto R t).comp _).run a = _
        rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
          Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        xorGadget_run, liftReg_mulVec_embed, QRoutine.runWith_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled XOR schedule**: `2·R.len` transposition queries. -/
def simXor (R : QRoutine ι Bool W) : QRoutine ι Bool (Option Bool × W) :=
  simXorUpto R R.len

@[simp] lemma simXor_len (R : QRoutine ι Bool W) :
    (simXor R).len = 2 * R.len := simXorUpto_len R R.len

theorem simXor_run (R : QRoutine ι Bool W) (a : ι → Bool)
    (ψ : QBasis ι Bool W → ℂ) :
    (simXor R).run a *ᵥ embedReg none ψ
      = embedReg none (R.runWith (xorOracleMat a) R.len *ᵥ ψ) :=
  simXorUpto_run R a R.len ψ

/-- Compile the first `t` transposition queries of a schedule into the XOR
model: lifted steps, one `transGadget` per query. -/
def simTransUpto (R : QRoutine ι Bool W) : ℕ → QRoutine ι Bool (Option Bool × W)
  | 0 => QRoutine.ofUnitary (liftReg (Option Bool) (R.step 0))
      (liftReg_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simTransUpto R t).comp (transGadget.comp
      (QRoutine.ofUnitary (liftReg (Option Bool) (R.step (t + 1)))
        (liftReg_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simTransUpto_len (R : QRoutine ι Bool W) (t : ℕ) :
    (simTransUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show ((simTransUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, transGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simTransUpto_xorRun (R : QRoutine ι Bool W) (a : ι → Bool) (t : ℕ)
    (ψ : QBasis ι Bool W → ℂ) :
    (simTransUpto R t).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      show (QRoutine.ofUnitary _ _).xorRun a *ᵥ _ = _
      rw [QRoutine.ofUnitary_xorRun, liftReg_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simTransUpto R (t + 1)).xorRun a
          = liftReg (Option Bool) (R.step (t + 1))
              * (transGadget.xorRun a * (simTransUpto R t).xorRun a) := by
        show ((simTransUpto R t).comp _).xorRun a = _
        rw [QRoutine.comp_xorRun, QRoutine.comp_xorRun,
          QRoutine.ofUnitary_xorRun, Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        transGadget_xorRun, liftReg_mulVec_embed, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled transposition schedule**: `2·R.len` XOR queries. -/
def simTrans (R : QRoutine ι Bool W) : QRoutine ι Bool (Option Bool × W) :=
  simTransUpto R R.len

@[simp] lemma simTrans_len (R : QRoutine ι Bool W) :
    (simTrans R).len = 2 * R.len := simTransUpto_len R R.len

theorem simTrans_xorRun (R : QRoutine ι Bool W) (a : ι → Bool)
    (ψ : QBasis ι Bool W → ℂ) :
    (simTrans R).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (R.run a *ᵥ ψ) :=
  simTransUpto_xorRun R a R.len ψ

/-! ## Transporting states, readouts, and probabilities -/

section Transport

variable {σ V O : Type} [Fintype σ] [DecidableEq σ] [Fintype V] [DecidableEq V]
  [DecidableEq O]

lemma isQState_embedReg (v : V) {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) :
    IsQState (embedReg v ψ) := by
  rw [IsQState, qNormSq_embedReg]
  exact hψ

/-- Read the underlying registers, ignoring the ancilla. -/
def stripReadout (r : QBasis ι σ W → O) : QBasis ι σ (V × W) → O :=
  fun p => r (p.1, p.2.1, p.2.2.2)

lemma qRestrict_stripReadout_embedReg (r : QBasis ι σ W → O) (v : V) (o : O)
    (χ : QBasis ι σ W → ℂ) :
    qRestrict (stripReadout (V := V) r) o (embedReg v χ)
      = embedReg v (qRestrict r o χ) := by
  funext p
  rw [qRestrict, embedReg_apply, embedReg_apply, qRestrict, stripReadout]
  by_cases hv : p.2.2.1 = v <;>
    by_cases hr : r (p.1, p.2.1, p.2.2.2) = o <;>
    simp [hv, hr]

/-- **Measuring through the ancilla changes nothing.** -/
lemma qProb_stripReadout_embedReg (r : QBasis ι σ W → O) (v : V) (o : O)
    (χ : QBasis ι σ W → ℂ) :
    qProb (stripReadout (V := V) r) (embedReg v χ) o = qProb r χ o := by
  rw [qProb_eq_qNormSq_qRestrict, qProb_eq_qNormSq_qRestrict,
    qRestrict_stripReadout_embedReg, qNormSq_embedReg]

end Transport

/-! ## The state bridges -/

section Bridges

variable {O : Type} [DecidableEq O]

/-- The standard state is the run of the algorithm's own schedule. -/
lemma state_eq_runUpto (A : QAlg ι Bool O W) (n : ℕ) (a : ι → Bool) (t : ℕ) :
    A.state a t
      = (QRoutine.mk n A.step A.step_unitary).runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The XOR state of a packaged routine is its parametric run. -/
lemma xorState_toAlg (R : QRoutine ι Bool W) (init : QBasis ι Bool W → ℂ)
    (hinit : IsQState init) (r : QBasis ι Bool W → O) (a : ι → Bool) (t : ℕ) :
    xorState (R.toAlg init hinit r) a t
      = R.runWith (xorOracleMat a) t *ᵥ init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [xorState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

end Bridges

/-! ## The `QueryCounts` translations -/

section Translations

variable {O : Type} [DecidableEq O] {X : Type} [Fintype X]

/-- **The transposition model simulates the XOR model** at a factor of two:
every achievable XOR query count doubles into the native model. -/
theorem two_mul_mem_queryCounts_of_xor {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ XorQueryCounts read f ε) :
    2 * q ∈ QueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_queryCounts
    (A := (simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
      (embedReg none A.init) (isQState_embedReg none A.init_isQState)
      (stripReadout A.readout)) ?_
  intro x
  have hlen : (simXor (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simXor_len]
  have hstate : ((simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg none A.init) (isQState_embedReg none A.init_isQState)
        (stripReadout A.readout)).state (read x) (2 * q)
      = embedReg none (xorState A (read x) q) := by
    rw [← hlen, QRoutine.toAlg_state_len, simXor_run,
      ← xorState_eq_runWith A q]
  rw [QAlg.prob, hstate,
    show ((simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg none A.init) (isQState_embedReg none A.init_isQState)
        (stripReadout A.readout)).readout = stripReadout A.readout from rfl,
    qProb_stripReadout_embedReg]
  exact hA x

/-- **The XOR model simulates the transposition model** at a factor of two. -/
theorem two_mul_mem_xorQueryCounts_of_std {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ QueryCounts read f ε) :
    2 * q ∈ XorQueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_xorQueryCounts
    (A := (simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
      (embedReg (some false) A.init)
      (isQState_embedReg (some false) A.init_isQState)
      (stripReadout A.readout)) ?_
  intro x
  have hlen : (simTrans (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simTrans_len]
  have hstate : xorState ((simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg (some false) A.init)
        (isQState_embedReg (some false) A.init_isQState)
        (stripReadout A.readout)) (read x) (2 * q)
      = embedReg (some false) (A.state (read x) q) := by
    rw [xorState_toAlg, show (2 * q)
        = (simTrans (QRoutine.mk q A.step A.step_unitary)).len from hlen.symm]
    rw [show (simTrans (QRoutine.mk q A.step A.step_unitary)).runWith
          (xorOracleMat (read x))
          (simTrans (QRoutine.mk q A.step A.step_unitary)).len
        = (simTrans (QRoutine.mk q A.step A.step_unitary)).xorRun (read x)
        from rfl]
    rw [simTrans_xorRun,
      show (QRoutine.mk q A.step A.step_unitary).run (read x)
          = (QRoutine.mk q A.step A.step_unitary).runUpto (read x) q from rfl,
      ← state_eq_runUpto A q]
  rw [hstate,
    show ((simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg (some false) A.init)
        (isQState_embedReg (some false) A.init_isQState)
        (stripReadout A.readout)).readout = stripReadout A.readout from rfl,
    qProb_stripReadout_embedReg]
  exact hA x

/-! ## The complexity comparison -/

variable [Nonempty O]

theorem xorQueryCounts_nonempty {read : X → ι → Bool} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    (XorQueryCounts read f ε).Nonempty := by
  obtain ⟨q, hq⟩ := queryCounts_nonempty hdet hε0
  exact ⟨2 * q, two_mul_mem_xorQueryCounts_of_std hq⟩

/-- **Model equivalence, one direction**: standard complexity is at most
twice the XOR complexity. -/
theorem qQueryOn_le_two_mul_xorQQueryOn {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    qQueryOn read f ε ≤ 2 * xorQQueryOn read f ε := by
  have hne := xorQueryCounts_nonempty hdet hε0
  have hmem : xorQQueryOn read f ε ∈ XorQueryCounts read f ε :=
    Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_queryCounts_of_xor hmem)

/-- **Model equivalence, the other direction**: XOR complexity is at most
twice the standard complexity. -/
theorem xorQQueryOn_le_two_mul_qQueryOn {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    xorQQueryOn read f ε ≤ 2 * qQueryOn read f ε := by
  have hne := queryCounts_nonempty hdet hε0
  have hmem : qQueryOn read f ε ∈ QueryCounts read f ε := Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_xorQueryCounts_of_std hmem)

end Translations

end QuantumQueryComplexity
