import QuantumQueryComplexity.Quantum.Measurement
import QuantumQueryComplexity.Quantum.Oracle
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Quantum query algorithms

A **quantum query algorithm** is an initial unit state on `QBasis ι σ Work`, a
sequence of input-independent unitaries, and a readout map for the final
computational-basis measurement.  On input `a : ι → σ` it evolves as

  `ψ₀ = U₀ |init⟩`,   `ψ_{t+1} = U_{t+1} O_a ψ_t`,

so `A.state a t` is the state after **`t` queries**; `A.prob a t o` is the
probability that measuring it announces `o`.  This is the standard
deferred-measurement form of the model.

## Design notes

* The unitaries are indexed by all of `ℕ`.  An algorithm is not tied to a query
  count: the query count is the time `t` at which one reads off the answer.
  This removes every `Fin (q+1)` cast from the development, and makes "the same
  algorithm run longer" a statement about `t`, not a new structure.
* The workspace `W` is a **parameter**, not a field.  Bundling it inside the
  structure makes `A.Work` appear in the index type of every matrix, and then
  `rw` and instance search fail on goals that are true by `rfl` (the type
  `QBasis ι σ A.Work` is only *definitionally* the concrete workspace a
  construction used).  Quantifying over `W` is deferred to `QueryCounts` in
  `Complexity.lean`, which is the one place it costs anything.  Everything lives
  in `Type` (universe 0): every index type, alphabet and workspace in this
  project is concrete.
* Correctness is stated **promise-natively**, through `read : X → ι → σ`.  The
  total case is `X = (ι → σ)` with `read = id`.

## Main results

* `QAlg.state_isQState` — the algorithm's state is a unit vector at all times.
* `computesWithErrorOn_const` — a constant function needs no queries.
* `computesWithErrorOn_proj` — one query reads one coordinate exactly.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {X : Type} [Fintype X]

/-- **A quantum query algorithm** with output type `O` and workspace `W`. -/
structure QAlg (ι σ O W : Type) [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] where
  /-- The initial state. -/
  init : QBasis ι σ W → ℂ
  /-- The initial state is a unit vector. -/
  init_isQState : IsQState init
  /-- The input-independent unitaries; `step t` is applied after the `t`-th
  query (and `step 0` before the first). -/
  step : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  /-- Each step is unitary. -/
  step_unitary : ∀ t, step t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ
  /-- The final measurement's readout map. -/
  readout : QBasis ι σ W → O

namespace QAlg

/-- **The state of `A` on input `a` after `t` queries.** -/
def state (A : QAlg ι σ O W) (a : ι → σ) : ℕ → (QBasis ι σ W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (oracleMat a *ᵥ A.state a t)

@[simp] lemma state_zero (A : QAlg ι σ O W) (a : ι → σ) :
    A.state a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma state_succ (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    A.state a (t + 1) = A.step (t + 1) *ᵥ (oracleMat a *ᵥ A.state a t) := rfl

/-- **The state stays a unit vector.** -/
theorem state_isQState (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    IsQState (A.state a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [state_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (oracleMat_mem_unitaryGroup a) ih)

variable [DecidableEq O]

/-- The probability that `A`, run for `t` queries on input `a`, announces `o`. -/
def prob (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) : ℝ :=
  qProb A.readout (A.state a t) o

lemma prob_nonneg (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) :
    0 ≤ A.prob a t o := qProb_nonneg _ _ _

lemma prob_le_one [Fintype O] (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) :
    A.prob a t o ≤ 1 :=
  qProb_le_one (A.state_isQState a t) _ _

end QAlg

/-! ## Bounded-error correctness -/

variable [DecidableEq O]

/-- **`A` computes `f` on the promise `read` with error at most `ε` in `q`
queries.** -/
def ComputesWithErrorOn (A : QAlg ι σ O W) (q : ℕ) (read : X → ι → σ) (f : X → O)
    (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ A.prob (read x) q (f x)

lemma ComputesWithErrorOn.mono {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ}
    {f : X → O} {ε ε' : ℝ} (h : ComputesWithErrorOn A q read f ε) (hε : ε ≤ ε') :
    ComputesWithErrorOn A q read f ε' :=
  fun x => le_trans (by linarith) (h x)

/-! ## Two sanity constructions

These are the smallest end-to-end uses of the model: they exercise the oracle's
action on a basis state and the measurement rule, and they are the base cases of
every later construction. -/

/-- The zero-query algorithm that always announces `c`. -/
def constAlg (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (c : O) : QAlg ι σ O Unit where
  init := qBasis (none, none, ())
  init_isQState := isQState_qBasis _
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary
  readout := fun _ => c

/-- **A constant function needs no queries.** -/
theorem computesWithErrorOn_const (read : X → ι → σ) (c : O) {f : X → O}
    (hf : ∀ x, f x = c) {ε : ℝ} (hε : 0 ≤ ε) :
    ComputesWithErrorOn (constAlg ι σ c) 0 read f ε := by
  intro x
  have h : (constAlg ι σ c).prob (read x) 0 (f x) = 1 := by
    simp [QAlg.prob, constAlg, hf x]
  rw [h]
  linarith

/-- The one-query algorithm that queries the coordinate `i` and announces the
answer register. -/
def projAlg (σ : Type) [Fintype σ] [DecidableEq σ] {ι : Type} [Fintype ι]
    [DecidableEq ι] (i : ι) : QAlg ι σ (Option σ) Unit where
  init := qBasis (some i, none, ())
  init_isQState := isQState_qBasis _
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary
  readout := fun p => p.2.1

/-- **One query reads one coordinate, exactly.** -/
theorem computesWithErrorOn_proj (read : X → ι → σ) (i : ι) {ε : ℝ} (hε : 0 ≤ ε) :
    ComputesWithErrorOn (projAlg σ i) 1 read (fun x => some (read x i)) ε := by
  intro x
  have h : (projAlg σ i).prob (read x) 1 (some (read x i)) = 1 := by
    simp [QAlg.prob, projAlg, oracleMat_mulVec_qBasis]
  rw [h]
  linarith

end QuantumQueryComplexity
