import QuantumQueryComplexity.Quantum.Measurement
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The standard XOR oracle, on the literal basis `ι × Bool × W`

The library's oracle models (`Oracle.lean`, `XorOracle.lean`, `AddOracle.lean`) run algorithms
on the basis `QBasis ι σ W = Option ι × Option σ × W`: besides the indices `some i` and the
answers `some s`, the query register has an *idle* value `none` and the answer register a
*blank* value `none`. Every oracle acts as the identity on an idle query; the XOR and additive
oracles also leave a blank answer unchanged, while the value oracle writes the answer into it. The
textbook model has neither value. Its basis is

  `PBasis ι W = ι × Bool × W`,

a query index, an answer bit and a workspace, and on input `a : ι → Bool` the oracle is

  `|i, b, w⟩ ↦ |i, b ⊕ a i, w⟩`   (`plainOracleMat`).

This file defines that model: algorithms (`PAlg`), their states (`PAlg.state`), bounded-error
correctness (`PlainComputesWithErrorOn`), the achievable query counts (`PlainQueryCounts`) and the
query complexity (`plainQQueryOn`). The definitions mirror `XorComputesWithErrorOn`,
`XorQueryCounts` and `xorQQueryOn` verbatim, with the literal basis in place of `QBasis`.
`PlainSimulation.lean` proves that the two XOR models have the same query counts, with no
overhead in either direction, for every nonempty index type.

Note that the literal basis is empty when `ι` is: an index type with no element admits no
algorithm in this model, so `PlainQueryCounts` is then empty and `plainQQueryOn` takes the junk
value `sInf ∅ = 0`.
-/

namespace QuantumQueryComplexity

namespace Plain

open scoped Matrix
open Matrix

variable {ι W O X : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-! ## The oracle -/

/-- **The basis of the standard model**: a query index, an answer bit and a workspace. -/
abbrev PBasis (ι W : Type) : Type := ι × Bool × W

/-- The standard XOR oracle's action on the basis: `|i, b, w⟩ ↦ |i, b ⊕ a i, w⟩`. It reads the
input only at the queried index. -/
def plainOracleMap (a : ι → Bool) (p : PBasis ι W) : PBasis ι W :=
  (p.1, xor p.2.1 (a p.1), p.2.2)

@[simp] lemma plainOracleMap_apply (a : ι → Bool) (i : ι) (b : Bool) (w : W) :
    plainOracleMap a ((i, b, w) : PBasis ι W) = (i, xor b (a i), w) := rfl

lemma plainOracleMap_involutive (a : ι → Bool) :
    Function.Involutive (plainOracleMap (W := W) a) := by
  rintro ⟨i, b, w⟩
  simp

/-- The standard XOR oracle as a permutation of the basis. -/
def plainOraclePerm (a : ι → Bool) : Equiv.Perm (PBasis ι W) :=
  Function.Involutive.toPerm _ (plainOracleMap_involutive a)

/-- **The standard XOR oracle unitary.** It is a permutation matrix, hence unitary, and an
involution, so query and unquery are the same matrix. -/
def plainOracleMat (a : ι → Bool) : Matrix (PBasis ι W) (PBasis ι W) ℂ :=
  qPerm (plainOraclePerm a)

theorem plainOracleMat_mem_unitaryGroup (a : ι → Bool) :
    plainOracleMat (W := W) a ∈ Matrix.unitaryGroup (PBasis ι W) ℂ :=
  qPerm_mem_unitaryGroup _

lemma plainOracleMat_mulVec_apply (a : ι → Bool) (ψ : PBasis ι W → ℂ) (p : PBasis ι W) :
    (plainOracleMat a *ᵥ ψ) p = ψ (plainOracleMap a p) := by
  rw [plainOracleMat, qPerm_mulVec_apply]
  rfl

/-! ## The query model -/

/-- **A quantum query algorithm in the standard model**, with output type `O` and workspace `W`:
an initial unit state on `ι × Bool × W`, input-independent unitaries, and the readout of the
final computational-basis measurement. As in `QAlg`, the unitaries are indexed by all of `ℕ`, and
the query count is the time at which the answer is read off. -/
structure PAlg (ι O W : Type) [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] where
  /-- The initial state. -/
  init : PBasis ι W → ℂ
  /-- The initial state is a unit vector. -/
  init_isQState : IsQState init
  /-- The unitaries; `step t` is applied after the `t`-th query (`step 0` before the first). -/
  step : ℕ → Matrix (PBasis ι W) (PBasis ι W) ℂ
  /-- Each step is unitary. -/
  step_unitary : ∀ t, step t ∈ Matrix.unitaryGroup (PBasis ι W) ℂ
  /-- The readout of the final measurement. -/
  readout : PBasis ι W → O

namespace PAlg

/-- **The state of a standard-model algorithm on input `a` after `t` queries**:
`ψ₀ = U₀ |init⟩` and `ψ_{t+1} = U_{t+1} O_a ψ_t`, with `O_a = plainOracleMat a`. -/
def state (A : PAlg ι O W) (a : ι → Bool) : ℕ → (PBasis ι W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (plainOracleMat a *ᵥ A.state a t)

@[simp] lemma state_zero (A : PAlg ι O W) (a : ι → Bool) : A.state a 0 = A.step 0 *ᵥ A.init :=
  rfl

@[simp] lemma state_succ (A : PAlg ι O W) (a : ι → Bool) (t : ℕ) :
    A.state a (t + 1) = A.step (t + 1) *ᵥ (plainOracleMat a *ᵥ A.state a t) := rfl

/-- The state stays a unit vector. -/
theorem state_isQState (A : PAlg ι O W) (a : ι → Bool) (t : ℕ) : IsQState (A.state a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [state_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (plainOracleMat_mem_unitaryGroup a) ih)

end PAlg

variable [DecidableEq O]

/-- `A` computes `f` on the promise `read` with error at most `ε` in `q` **standard XOR
queries**: on every input `x` the readout announces `f x` with probability at least `1 - ε`
after `q` queries. -/
def PlainComputesWithErrorOn (A : PAlg ι O W) (q : ℕ) (read : X → ι → Bool) (f : X → O)
    (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ qProb A.readout (A.state (read x) q) (f x)

/-- The query counts achievable in the standard model with error at most `ε`, by a single
algorithm on some finite workspace chosen before the input. -/
def PlainQueryCounts (read : X → ι → Bool) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : PAlg ι O W),
    PlainComputesWithErrorOn A q read f ε}

/-- **Quantum query complexity in the standard XOR model**: the infimum of the achievable query
counts, which is the least of them when some count is achievable and `0` (`sInf ∅`) when none is. -/
noncomputable def plainQQueryOn (read : X → ι → Bool) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (PlainQueryCounts read f ε)

theorem mem_plainQueryCounts {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ}
    {A : PAlg ι O W} (h : PlainComputesWithErrorOn A q read f ε) :
    q ∈ PlainQueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

end Plain

end QuantumQueryComplexity
