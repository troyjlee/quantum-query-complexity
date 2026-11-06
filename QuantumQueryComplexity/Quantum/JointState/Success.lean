import QuantumQueryComplexity.Quantum.JointState.Oracle
import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.Simulation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Relational and average success, and their transport across oracle models

* `xorSuccessProbOn`, `XorSolvesWithErrorOn` — the relational success semantics of
  `Relation.lean` in the XOR query model.
* `FinDist.avgSuccessProb`, `FinDist.avgXorSuccessProb` — average success probability under an
  input distribution, possibly with hidden labels.  It is the squared norm of the joint state
  masked to the basis states whose readout is valid for the input
  (`FinDist.avgSuccessProb_eq_jNormSq_goodMask`, Belovs's Claim 3.7).  Pointwise success
  implies average success (`FinDist.avgSuccessProb_ge_of_solves`).
* `QAlg.simToXor`, `QAlg.simToStd` — the two-queries-per-query simulations of `Simulation.lean`,
  packaged as algorithms, with **relational** success transported exactly
  (`xorSuccessProbOn_simToXor`, `successProbOn_simToStd`).  The library's existing exports
  transport only function computation (`ComputesWithErrorOn`); lower bounds for relational
  problems such as triangle finding need these forms.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O W X Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X] [Fintype Ω] [DecidableEq Ω]

/-! ## Relational success in the XOR model -/

/-- **The probability that `A`, after `q` XOR queries on the promise input `x`, outputs a value
valid for `x`.** -/
def xorSuccessProbOn (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : ℝ :=
  goodProb A.readout (Good x) (xorState A (read x) q)

/-- **`A` solves the relation `Good` on the promise with error at most `ε` in `q` XOR
queries.** -/
def XorSolvesWithErrorOn (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤ xorSuccessProbOn A q read Good x

lemma xorSuccessProbOn_nonneg (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    0 ≤ xorSuccessProbOn A q read Good x :=
  goodProb_nonneg _ _ _

lemma xorSuccessProbOn_le_one (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    xorSuccessProbOn A q read Good x ≤ 1 := by
  classical
  exact goodProb_le_one _ _ (xorState_isQState _ _ _)

/-! ## Average success -/

namespace FinDist

variable (ρ : FinDist Ω)

/-- A mass-weighted sum over `Ω` is the same sum over the support. -/
lemma sum_mass_mul_eq_sum_supp (g : Ω → ℝ) :
    ∑ ω, ρ.mass ω * g ω = ∑ x : ρ.Supp, ρ.mass x * g x := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun ω => 0 < ρ.mass ω)
    (p := fun ω => 0 < ρ.mass ω) (fun ω => by simp) (fun ω => ρ.mass ω * g ω)]
  refine (Finset.sum_filter_of_ne fun ω _ hω => ?_).symm
  exact lt_of_le_of_ne (ρ.mass_nonneg ω) (Ne.symm (left_ne_zero_of_mul hω))

/-- A lower bound on every input of positive mass bounds the mass-weighted average. -/
private lemma le_sum_mass_mul_of_forall {g : Ω → ℝ} {s : ℝ} (h : ∀ ω, 0 < ρ.mass ω → s ≤ g ω) :
    s ≤ ∑ ω, ρ.mass ω * g ω := by
  calc s = ∑ ω, ρ.mass ω * s := by rw [← Finset.sum_mul, ρ.sum_mass, one_mul]
    _ ≤ ∑ ω, ρ.mass ω * g ω := Finset.sum_le_sum fun ω _ => by
        rcases (ρ.mass_nonneg ω).eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h ω hpos) hpos.le

/-- **Average success probability** under `ρ` (value-oracle model). -/
noncomputable def avgSuccessProb (A : QAlg ι σ O W) (q : ℕ) (read : Ω → ι → σ)
    (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] : ℝ :=
  ∑ ω, ρ.mass ω * successProbOn A q read Good ω

/-- **Average success probability** under `ρ` (XOR model). -/
noncomputable def avgXorSuccessProb (A : QAlg ι Bool O W) (q : ℕ) (read : Ω → ι → Bool)
    (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] : ℝ :=
  ∑ ω, ρ.mass ω * xorSuccessProbOn A q read Good ω

/-- If every input of positive probability is solved with probability at least `s`, the average
success is at least `s`. -/
theorem le_avgSuccessProb_of_forall {A : QAlg ι σ O W} {q : ℕ} {read : Ω → ι → σ}
    {Good : Ω → O → Prop} [∀ ω, DecidablePred (Good ω)] {s : ℝ}
    (h : ∀ ω, 0 < ρ.mass ω → s ≤ successProbOn A q read Good ω) :
    s ≤ ρ.avgSuccessProb A q read Good :=
  ρ.le_sum_mass_mul_of_forall h

theorem le_avgXorSuccessProb_of_forall {A : QAlg ι Bool O W} {q : ℕ} {read : Ω → ι → Bool}
    {Good : Ω → O → Prop} [∀ ω, DecidablePred (Good ω)] {s : ℝ}
    (h : ∀ ω, 0 < ρ.mass ω → s ≤ xorSuccessProbOn A q read Good ω) :
    s ≤ ρ.avgXorSuccessProb A q read Good :=
  ρ.le_sum_mass_mul_of_forall h

/-- **Pointwise success implies average success.** -/
theorem avgSuccessProb_ge_of_solves {A : QAlg ι σ O W} {q : ℕ} {read : Ω → ι → σ}
    {Good : Ω → O → Prop} [∀ ω, DecidablePred (Good ω)] {ε : ℝ}
    (h : SolvesWithErrorOn A q read Good ε) : 1 - ε ≤ ρ.avgSuccessProb A q read Good :=
  ρ.le_avgSuccessProb_of_forall fun ω _ => h ω

theorem avgXorSuccessProb_ge_of_solves {A : QAlg ι Bool O W} {q : ℕ} {read : Ω → ι → Bool}
    {Good : Ω → O → Prop} [∀ ω, DecidablePred (Good ω)] {ε : ℝ}
    (h : XorSolvesWithErrorOn A q read Good ε) : 1 - ε ≤ ρ.avgXorSuccessProb A q read Good :=
  ρ.le_avgXorSuccessProb_of_forall fun ω _ => h ω

/-- Mask a joint vector to the basis states whose readout is valid for the input `x`. -/
def goodMask {B : Type} (rd : B → O) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)]
    (f : JVec ρ.Supp B) : JVec ρ.Supp B :=
  fun x b => if Good x (rd b) then f x b else 0

/-- The squared norm of a masked workspace vector is the valid mass of the unmasked one. -/
lemma qNormSq_wvec_goodMask {B : Type} [Fintype B] [DecidableEq B] (rd : B → O)
    (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] (f : JVec ρ.Supp B) (x : ρ.Supp) :
    qNormSq (ρ.wvec (ρ.goodMask rd Good f) x) = goodProb rd (Good x) (ρ.wvec f x) := by
  rw [qNormSq_def, goodProb_eq_sum_ite]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [wvec, goodMask, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **Average success is the squared norm of the masked joint state** (value-oracle model). -/
theorem avgSuccessProb_eq_jNormSq_goodMask (A : QAlg ι σ O W) (q : ℕ) (read : Ω → ι → σ)
    (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] :
    ρ.avgSuccessProb A q read Good
      = jNormSq (ρ.goodMask A.readout Good (ρ.jointState read A q)) := by
  rw [avgSuccessProb, jNormSq_eq_sum_wvec, sum_mass_mul_eq_sum_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [qNormSq_wvec_goodMask, wvec_jointState, successProbOn]

/-- **Average success is the squared norm of the masked joint state** (XOR model). -/
theorem avgXorSuccessProb_eq_jNormSq_goodMask (A : QAlg ι Bool O W) (q : ℕ)
    (read : Ω → ι → Bool) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] :
    ρ.avgXorSuccessProb A q read Good
      = jNormSq (ρ.goodMask A.readout Good (ρ.jointXorState read A q)) := by
  rw [avgXorSuccessProb, jNormSq_eq_sum_wvec, sum_mass_mul_eq_sum_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [qNormSq_wvec_goodMask, wvec_jointXorState, xorSuccessProbOn]

end FinDist

/-! ## Transport across oracle models -/

section Transport

variable [DecidableEq O]

/-- Measuring a relation through an ancilla changes nothing. -/
theorem goodProb_stripReadout_embedReg {V : Type} [Fintype V] [DecidableEq V]
    (r : QBasis ι σ W → O) (v : V) (G : O → Prop) [DecidablePred G] (ψ : QBasis ι σ W → ℂ) :
    goodProb (stripReadout (V := V) r) G (embedReg v ψ) = goodProb r G ψ :=
  qProb_stripReadout_embedReg (V := V) (fun h => decide (G (r h))) v true ψ

/-- The XOR-model algorithm simulating the first `q` value-oracle queries of `A`, at two XOR
queries per query (`simTrans`), with a clean `Option Bool` ancilla. -/
noncomputable def QAlg.simToXor (A : QAlg ι Bool O W) (q : ℕ) :
    QAlg ι Bool O (Option Bool × W) :=
  (simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg (embedReg (some false) A.init)
    (isQState_embedReg (some false) A.init_isQState) (stripReadout A.readout)

/-- The value-oracle algorithm simulating the first `q` XOR queries of `A`, at two value queries
per query (`simXor`), with a clean `Option Bool` ancilla. -/
noncomputable def QAlg.simToStd (A : QAlg ι Bool O W) (q : ℕ) :
    QAlg ι Bool O (Option Bool × W) :=
  (simXor (QRoutine.mk q A.step A.step_unitary)).toAlg (embedReg none A.init)
    (isQState_embedReg none A.init_isQState) (stripReadout A.readout)

/-- The XOR state of `A.simToXor q` after `2q` queries is `A`'s state after `q` value
queries, embedded with a clean ancilla. -/
private lemma xorState_simToXor (A : QAlg ι Bool O W) (q : ℕ) (a : ι → Bool) :
    xorState (A.simToXor q) a (2 * q) = embedReg (some false) (A.state a q) := by
  rw [QAlg.simToXor, xorState_toAlg, show (2 * q)
      = (simTrans (QRoutine.mk q A.step A.step_unitary)).len by rw [simTrans_len]]
  rw [show (simTrans (QRoutine.mk q A.step A.step_unitary)).runWith
        (xorOracleMat a) (simTrans (QRoutine.mk q A.step A.step_unitary)).len
      = (simTrans (QRoutine.mk q A.step A.step_unitary)).xorRun a from rfl]
  rw [simTrans_xorRun,
    show (QRoutine.mk q A.step A.step_unitary).run a
        = (QRoutine.mk q A.step A.step_unitary).runUpto a q from rfl,
    ← state_eq_runUpto A q]

/-- The state of `A.simToStd q` after `2q` value queries is `A`'s XOR state after `q` queries,
embedded with a clean ancilla. -/
private lemma state_simToStd (A : QAlg ι Bool O W) (q : ℕ) (a : ι → Bool) :
    (A.simToStd q).state a (2 * q) = embedReg none (xorState A a q) := by
  rw [QAlg.simToStd, show (2 * q)
      = (simXor (QRoutine.mk q A.step A.step_unitary)).len by rw [simXor_len],
    QRoutine.toAlg_state_len, simXor_run, ← xorState_eq_runWith A q]

/-- **Value oracle → XOR, relationally**: the simulation's success after `2q` XOR queries
equals `A`'s success after `q` value queries, on every input and for every relation. -/
theorem xorSuccessProbOn_simToXor (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    xorSuccessProbOn (A.simToXor q) (2 * q) read Good x = successProbOn A q read Good x := by
  rw [xorSuccessProbOn, xorState_simToXor,
    show (A.simToXor q).readout = stripReadout A.readout from rfl,
    goodProb_stripReadout_embedReg, successProbOn]

/-- **XOR → value oracle, relationally.** -/
theorem successProbOn_simToStd (A : QAlg ι Bool O W) (q : ℕ) (read : X → ι → Bool)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    successProbOn (A.simToStd q) (2 * q) read Good x = xorSuccessProbOn A q read Good x := by
  rw [successProbOn, state_simToStd,
    show (A.simToStd q).readout = stripReadout A.readout from rfl,
    goodProb_stripReadout_embedReg, xorSuccessProbOn]

theorem xorSolvesWithErrorOn_simToXor {A : QAlg ι Bool O W} {q : ℕ} {read : X → ι → Bool}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {ε : ℝ}
    (h : SolvesWithErrorOn A q read Good ε) :
    XorSolvesWithErrorOn (A.simToXor q) (2 * q) read Good ε := fun x => by
  rw [xorSuccessProbOn_simToXor]
  exact h x

theorem solvesWithErrorOn_simToStd {A : QAlg ι Bool O W} {q : ℕ} {read : X → ι → Bool}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {ε : ℝ}
    (h : XorSolvesWithErrorOn A q read Good ε) :
    SolvesWithErrorOn (A.simToStd q) (2 * q) read Good ε := fun x => by
  rw [successProbOn_simToStd]
  exact h x

/-- Average success is transported by the simulation as well. -/
theorem avgXorSuccessProb_simToXor (ρ : FinDist Ω) (A : QAlg ι Bool O W) (q : ℕ)
    (read : Ω → ι → Bool) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] :
    ρ.avgXorSuccessProb (A.simToXor q) (2 * q) read Good = ρ.avgSuccessProb A q read Good := by
  rw [FinDist.avgXorSuccessProb, FinDist.avgSuccessProb]
  exact Finset.sum_congr rfl fun ω _ => by rw [xorSuccessProbOn_simToXor]

end Transport

end QuantumQueryComplexity
