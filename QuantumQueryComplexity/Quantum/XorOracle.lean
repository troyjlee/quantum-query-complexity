import QuantumQueryComplexity.Quantum.RunWith
import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The standard Boolean XOR oracle, and its query model

The conventional oracle for Boolean inputs: on the answer register,

  `|i⟩|b⟩|w⟩ ↦ |i⟩|b ⊕ a i⟩|w⟩`,

with an **idle index** (`none`, no query) and a fixed blank answer — on this
model's basis `QBasis ι Bool W` the answer register is `Option Bool`, the XOR
acts on the `some`-part, and both `none` sectors are fixed.  Boolean
specifically: for an arbitrary alphabet there is no canonical XOR directly
on `σ` without choosing a group structure, so the simulation theorems start
here.  Milestone G (`OneHot.lean`) instead XORs an *encoding* of the letter
— its one-hot code in `Hot σ := σ → Bool` — which needs no structure on `σ`.

Like the transposition oracle it is a basis permutation and an involution, so
unitarity and query = unquery are free.

The model: `QAlg` is oracle-agnostic data (initial state, steps, readout);
only the *state semantics* names the oracle.  `xorState` is `QAlg.state` with
`xorOracleMat` in place of `oracleMat`, and `XorComputesWithErrorOn`,
`XorQueryCounts`, `xorQQueryOn` mirror the standard model's definitions
verbatim.  `Simulation.lean` proves the two models equivalent within a factor
of two in the query count.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## The XOR on an optional Boolean -/

/-- XOR the `some`-part of `s` into the `some`-part of `t`; blank on either
side leaves `t` alone. -/
def optXor : Option Bool → Option Bool → Option Bool
  | some b, some c => some (xor b c)
  | t, _ => t

@[simp] lemma optXor_some_some (b c : Bool) :
    optXor (some b) (some c) = some (xor b c) := rfl

@[simp] lemma optXor_none (s : Option Bool) : optXor none s = none := by
  cases s <;> rfl

@[simp] lemma optXor_blank (t : Option Bool) : optXor t none = t := by
  cases t <;> rfl

lemma optXor_optXor (t s : Option Bool) : optXor (optXor t s) s = t := by
  cases t <;> cases s <;> simp [optXor]

/-! ## The oracle -/

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- The XOR oracle's action on the computational basis. -/
def xorOracleMap (a : ι → Bool) : QBasis ι Bool W → QBasis ι Bool W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, optXor t (some (a i)), w)

@[simp] lemma xorOracleMap_none (a : ι → Bool) (t : Option Bool) (w : W) :
    xorOracleMap a ((none, t, w) : QBasis ι Bool W) = (none, t, w) := rfl

/-- **The XOR oracle reads the input only at the queried index.** -/
@[simp] lemma xorOracleMap_some (a : ι → Bool) (i : ι) (t : Option Bool)
    (w : W) : xorOracleMap a ((some i, t, w) : QBasis ι Bool W)
      = (some i, optXor t (some (a i)), w) := rfl

/-- The blank answer is fixed: the XOR oracle, too, has an idle answer. -/
lemma xorOracleMap_blank (a : ι → Bool) (i : ι) (w : W) :
    xorOracleMap a ((some i, none, w) : QBasis ι Bool W)
      = (some i, none, w) := rfl

lemma xorOracleMap_involutive (a : ι → Bool) :
    Function.Involutive (xorOracleMap (W := W) a) := by
  rintro ⟨(_ | i), t, w⟩
  · rfl
  · simp [optXor_optXor]

/-- The XOR oracle as a permutation of the basis. -/
def xorOraclePerm (a : ι → Bool) : Equiv.Perm (QBasis ι Bool W) :=
  Function.Involutive.toPerm _ (xorOracleMap_involutive a)

@[simp] lemma xorOraclePerm_apply (a : ι → Bool) (p : QBasis ι Bool W) :
    xorOraclePerm a p = xorOracleMap a p := rfl

/-- **The XOR oracle unitary.** -/
def xorOracleMat (a : ι → Bool) :
    Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  qPerm (xorOraclePerm a)

theorem xorOracleMat_mem_unitaryGroup (a : ι → Bool) :
    xorOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **Query = unquery**, here too. -/
theorem xorOracleMat_mul_self (a : ι → Bool) :
    xorOracleMat (W := W) a * xorOracleMat a = 1 :=
  qPerm_mul_self_of_involutive (xorOracleMap_involutive a)

lemma xorOracleMat_mulVec_apply (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ)
    (p : QBasis ι Bool W) :
    (xorOracleMat a *ᵥ ψ) p = ψ (xorOracleMap a p) := by
  rw [xorOracleMat, qPerm_mulVec_apply]
  rfl

/-! ## The XOR query model

`QAlg` carries no oracle; the state semantics does.  These definitions mirror
`QAlg.state`, `ComputesWithErrorOn`, `QueryCounts`, and `qQueryOn` with the
XOR oracle substituted. -/

variable {O : Type} [DecidableEq O]
variable {X : Type} [Fintype X]

/-- **The state of `A` on input `a` after `t` XOR queries.** -/
def xorState (A : QAlg ι Bool O W) (a : ι → Bool) :
    ℕ → (QBasis ι Bool W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (xorOracleMat a *ᵥ xorState A a t)

@[simp] lemma xorState_zero (A : QAlg ι Bool O W) (a : ι → Bool) :
    xorState A a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma xorState_succ (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    xorState A a (t + 1)
      = A.step (t + 1) *ᵥ (xorOracleMat a *ᵥ xorState A a t) := rfl

theorem xorState_isQState (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    IsQState (xorState A a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [xorState_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (xorOracleMat_mem_unitaryGroup a) ih)

/-- **The bridge to the parametric run**: the XOR state is `runWith` of the
algorithm's step schedule, packaged with any length. -/
lemma xorState_eq_runWith (A : QAlg ι Bool O W) (n : ℕ) (a : ι → Bool)
    (t : ℕ) : xorState A a t
      = (QRoutine.mk n A.step A.step_unitary).runWith (xorOracleMat a) t
          *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [xorState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- `A` computes `f` on the promise `read` with error at most `ε` in `q`
**XOR queries**. -/
def XorComputesWithErrorOn (A : QAlg ι Bool O W) (q : ℕ)
    (read : X → ι → Bool) (f : X → O) (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ qProb A.readout (xorState A (read x) q) (f x)

/-- The achievable XOR-query counts. -/
def XorQueryCounts (read : X → ι → Bool) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QAlg ι Bool O W), XorComputesWithErrorOn A q read f ε}

/-- Quantum query complexity in the **XOR-oracle model**. -/
noncomputable def xorQQueryOn (read : X → ι → Bool) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (XorQueryCounts read f ε)

theorem mem_xorQueryCounts {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι Bool O W}
    (h : XorComputesWithErrorOn A q read f ε) :
    q ∈ XorQueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

end QuantumQueryComplexity
