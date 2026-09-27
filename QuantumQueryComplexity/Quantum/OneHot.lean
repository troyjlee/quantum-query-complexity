import QuantumQueryComplexity.Quantum.RunWith
import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The canonical one-hot XOR oracle model

The conventional oracle for a finite alphabet `σ` is a *phase* or *XOR*
oracle, and for a non-group alphabet the XOR needs a choice of encoding.  The
**canonical one-hot XOR oracle model** fixes the simplest one: the physical
answer register holds a Boolean vector indexed by the alphabet,

    Hot σ := σ → Bool,     hotCode a := indicator of {a},

and a query at index `i` XORs `hotCode (x i)` into the active answer
register:

    |i⟩ |h⟩ |w⟩ ↦ |i⟩ |h ⊕ hotCode (x i)⟩ |w⟩.

On this file's basis `QBasis ι (Hot σ) W` the answer register is
`Option (Hot σ)`: the XOR acts on the `some`-part, and both the idle index
`none` and the blank answer `none` are fixed.  The **clean answer** is
`some hotZero`, the zero vector; a query on a clean register reads
`some (hotCode (x i))`.  The logical alphabet `σ` and the physical answer
type `Hot σ` are kept distinct throughout — the one-hot model's basis has a
*different* answer type from the native model's `QBasis ι σ W`, and the
comparison in `OneHotSimulation.lean` moves one register into the workspace.

This is one specific convention, not a claim about every finite-alphabet
oracle. A whole-element value query returns the entire letter `x i`;
the one-hot XOR oracle is a concrete
unitary realization of that whole-element value-oracle convention, and
`OneHotSimulation.lean` proves it equivalent to the native transposition
model at a factor of two in the query count, directly and without passing
through the Boolean XOR model.

Like the transposition and Boolean XOR oracles it is a basis permutation and
an involution, so unitarity and query = unquery are free.  The query model
mirrors `XorOracle.lean` verbatim: `oneHotState` is `QAlg.state` with
`oneHotOracleMat` in place of `oracleMat`, and `OneHotComputesWithErrorOn`,
`OneHotXorQueryCounts`, `oneHotQQueryOn` mirror the native definitions.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## The physical answer type -/

/-- **The physical answer type of the one-hot model**: one Boolean per
letter. -/
abbrev Hot (σ : Type) : Type := σ → Bool

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **The one-hot code of a letter**: the indicator of `{a}`. -/
def hotCode (a : σ) : Hot σ := fun b => decide (b = a)

@[simp] lemma hotCode_apply (a b : σ) : hotCode a b = decide (b = a) := rfl

lemma hotCode_injective : Function.Injective (hotCode (σ := σ)) := by
  intro a b h
  have hab := congrFun h a
  by_contra hne
  simp [hotCode, hne] at hab

/-- **The clean answer**: the zero vector `0`. -/
def hotZero : Hot σ := fun _ => false

@[simp] lemma hotZero_apply (b : σ) : hotZero (σ := σ) b = false := rfl

/-- Bitwise XOR of two one-hot registers. -/
def hotXor (h g : Hot σ) : Hot σ := fun b => xor (h b) (g b)

@[simp] lemma hotXor_apply (h g : Hot σ) (b : σ) :
    hotXor h g b = xor (h b) (g b) := rfl

lemma hotXor_hotXor (h g : Hot σ) : hotXor (hotXor h g) g = h := by
  funext b
  simp only [hotXor_apply]
  cases h b <;> cases g b <;> rfl

@[simp] lemma hotZero_hotXor (g : Hot σ) : hotXor hotZero g = g := by
  funext b
  simp [hotXor, hotZero]

lemma hotXor_self (h : Hot σ) : hotXor h h = hotZero := by
  funext b
  simp [hotXor, hotZero]

/-- A one-hot code is never the clean answer. -/
lemma hotCode_ne_hotZero (a : σ) : hotCode a ≠ hotZero := by
  intro h
  have := congrFun h a
  simp at this

/-! ## The XOR on an optional one-hot register -/

/-- XOR `s` into the `some`-part of `t`; a blank `t` is fixed. -/
def optHotXor (t : Option (Hot σ)) (s : Hot σ) : Option (Hot σ) :=
  t.map fun h => hotXor h s

@[simp] lemma optHotXor_some (h s : Hot σ) :
    optHotXor (some h) s = some (hotXor h s) := rfl

@[simp] lemma optHotXor_none (s : Hot σ) :
    optHotXor (σ := σ) none s = none := rfl

lemma optHotXor_optHotXor (t : Option (Hot σ)) (s : Hot σ) :
    optHotXor (optHotXor t s) s = t := by
  cases t <;> simp [hotXor_hotXor]

/-! ## The oracle -/

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- The one-hot XOR oracle's action on the computational basis. -/
def oneHotOracleMap (a : ι → σ) : QBasis ι (Hot σ) W → QBasis ι (Hot σ) W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, optHotXor t (hotCode (a i)), w)

@[simp] lemma oneHotOracleMap_none (a : ι → σ) (t : Option (Hot σ)) (w : W) :
    oneHotOracleMap a ((none, t, w) : QBasis ι (Hot σ) W) = (none, t, w) := rfl

/-- **The one-hot oracle reads the input only at the queried index.** -/
@[simp] lemma oneHotOracleMap_some (a : ι → σ) (i : ι) (t : Option (Hot σ))
    (w : W) : oneHotOracleMap a ((some i, t, w) : QBasis ι (Hot σ) W)
      = (some i, optHotXor t (hotCode (a i)), w) := rfl

/-- The blank answer is fixed: the one-hot oracle has an idle answer. -/
lemma oneHotOracleMap_blank (a : ι → σ) (i : ι) (w : W) :
    oneHotOracleMap a ((some i, none, w) : QBasis ι (Hot σ) W)
      = (some i, none, w) := rfl

/-- **A query on a clean register reads the one-hot code of the letter.** -/
lemma oneHotOracleMap_clean (a : ι → σ) (i : ι) (w : W) :
    oneHotOracleMap a ((some i, some hotZero, w) : QBasis ι (Hot σ) W)
      = (some i, some (hotCode (a i)), w) := by
  simp

lemma oneHotOracleMap_involutive (a : ι → σ) :
    Function.Involutive (oneHotOracleMap (W := W) a) := by
  rintro ⟨(_ | i), t, w⟩
  · rfl
  · simp [optHotXor_optHotXor]

/-- The one-hot oracle as a permutation of the basis. -/
def oneHotOraclePerm (a : ι → σ) : Equiv.Perm (QBasis ι (Hot σ) W) :=
  Function.Involutive.toPerm _ (oneHotOracleMap_involutive a)

@[simp] lemma oneHotOraclePerm_apply (a : ι → σ) (p : QBasis ι (Hot σ) W) :
    oneHotOraclePerm a p = oneHotOracleMap a p := rfl

/-- **The one-hot XOR oracle unitary.** -/
def oneHotOracleMat (a : ι → σ) :
    Matrix (QBasis ι (Hot σ) W) (QBasis ι (Hot σ) W) ℂ :=
  qPerm (oneHotOraclePerm a)

theorem oneHotOracleMat_mem_unitaryGroup (a : ι → σ) :
    oneHotOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι (Hot σ) W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **Query = unquery**, here too. -/
theorem oneHotOracleMat_mul_self (a : ι → σ) :
    oneHotOracleMat (W := W) a * oneHotOracleMat a = 1 :=
  qPerm_mul_self_of_involutive (oneHotOracleMap_involutive a)

lemma oneHotOracleMat_mulVec_apply (a : ι → σ) (ψ : QBasis ι (Hot σ) W → ℂ)
    (p : QBasis ι (Hot σ) W) :
    (oneHotOracleMat a *ᵥ ψ) p = ψ (oneHotOracleMap a p) := by
  rw [oneHotOracleMat, qPerm_mulVec_apply]
  rfl

lemma oneHotOracleMat_mulVec_qBasis (a : ι → σ) (p : QBasis ι (Hot σ) W) :
    oneHotOracleMat a *ᵥ qBasis p = qBasis (oneHotOracleMap a p) := by
  rw [oneHotOracleMat, qPerm_mulVec_qBasis]
  rfl

/-! ## The one-hot query model

`QAlg` carries no oracle; the state semantics does.  These definitions mirror
`QAlg.state`, `ComputesWithErrorOn`, `QueryCounts`, and `qQueryOn` with the
one-hot XOR oracle substituted.  An algorithm of this model is a
`QAlg ι (Hot σ) O W`: its *basis* carries the physical answer type. -/

variable {O : Type}

/-- **The state of `A` on input `a` after `t` one-hot queries.** -/
def oneHotState (A : QAlg ι (Hot σ) O W) (a : ι → σ) :
    ℕ → (QBasis ι (Hot σ) W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (oneHotOracleMat a *ᵥ oneHotState A a t)

@[simp] lemma oneHotState_zero (A : QAlg ι (Hot σ) O W) (a : ι → σ) :
    oneHotState A a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma oneHotState_succ (A : QAlg ι (Hot σ) O W) (a : ι → σ) (t : ℕ) :
    oneHotState A a (t + 1)
      = A.step (t + 1) *ᵥ (oneHotOracleMat a *ᵥ oneHotState A a t) := rfl

theorem oneHotState_isQState (A : QAlg ι (Hot σ) O W) (a : ι → σ) (t : ℕ) :
    IsQState (oneHotState A a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [oneHotState_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (oneHotOracleMat_mem_unitaryGroup a) ih)

/-- **The bridge to the parametric run**: the one-hot state is `runWith` of
the algorithm's step schedule, packaged with any length. -/
lemma oneHotState_eq_runWith (A : QAlg ι (Hot σ) O W) (n : ℕ) (a : ι → σ)
    (t : ℕ) : oneHotState A a t
      = (QRoutine.mk n A.step A.step_unitary).runWith (oneHotOracleMat a) t
          *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [oneHotState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

variable [DecidableEq O] {X : Type} [Fintype X]

/-- `A` computes `f` on the promise `read` with error at most `ε` in `q`
**one-hot XOR queries**. -/
def OneHotComputesWithErrorOn (A : QAlg ι (Hot σ) O W) (q : ℕ)
    (read : X → ι → σ) (f : X → O) (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ qProb A.readout (oneHotState A (read x) q) (f x)

/-- The achievable one-hot query counts. -/
def OneHotXorQueryCounts (read : X → ι → σ) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QAlg ι (Hot σ) O W), OneHotComputesWithErrorOn A q read f ε}

/-- Quantum query complexity in the **canonical one-hot XOR oracle model**. -/
noncomputable def oneHotQQueryOn (read : X → ι → σ) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (OneHotXorQueryCounts read f ε)

/-- The one-hot complexity of a total function. -/
noncomputable abbrev oneHotQQuery (f : (ι → σ) → O) (ε : ℝ) : ℕ :=
  oneHotQQueryOn (X := ι → σ) id f ε

theorem mem_oneHotXorQueryCounts {read : X → ι → σ} {f : X → O} {ε : ℝ}
    {q : ℕ} {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι (Hot σ) O W}
    (h : OneHotComputesWithErrorOn A q read f ε) :
    q ∈ OneHotXorQueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

/-- **One algorithm bounds the one-hot complexity.** -/
theorem oneHotQQueryOn_le {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι (Hot σ) O W}
    (h : OneHotComputesWithErrorOn A q read f ε) :
    oneHotQQueryOn read f ε ≤ q :=
  Nat.sInf_le (mem_oneHotXorQueryCounts h)

end QuantumQueryComplexity
