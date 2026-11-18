import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.RunWith
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Additive oracles over a finite abelian group, and their query model

For a finite additive commutative group `G` and an input `a : ι → G`, the **additive oracle**
acts on the library's basis `QBasis ι G W` (index register `Option ι`, answer register
`Option G`, workspace `W`) by

  `|i, c, w⟩ ↦ |i, c + aᵢ, w⟩`,

and fixes the idle index and the blank answer (`addOracleMat`). It is a basis permutation whose
inverse is the oracle of `−a`. Instances:

* `G = ZMod q`: the additive oracle over `Z_q` of `ZqOracle.lean`, which is conjugate to the
  phase oracle;
* `G = Fin m → ZMod 2`: XOR of an `m`-bit string into the answer register, the standard oracle
  for inputs given in binary (e.g. the adjacency-matrix oracle of Apers and Lee, *Quantum
  complexity of minimum cut*, Section 2.3, with `m`-bit weights);
* `G = ZMod n × (Fin m → ZMod 2)`: add a vertex name modulo `n` and XOR an `m`-bit weight, the
  adjacency-array oracle of the same paper.

**The additive query model** runs a `QAlg ι G O W` with the additive oracle in place of the
value oracle (`addState`). `AddComputesWithErrorOn`, `addSuccessProbOn`, `AddSolvesWithErrorOn`,
`AddQueryCounts` and `addQQueryOn` copy the value-oracle definitions exactly. A promise problem is
read by `read : X → ι → G`; an input over another alphabet `σ` enters through an encoding
`enc : σ → G` composed into the reading.

`AddSimulation.lean` proves the additive and value-oracle models equivalent within a factor of two
in the query count, in both directions and for every relation.

## Main definitions

* `addOracleMap`, `addOraclePerm`, `addOracleMat`: the additive oracle.
* `addState`: the state of an algorithm against the additive oracle.
* `AddComputesWithErrorOn`, `addSuccessProbOn`, `AddSolvesWithErrorOn`, `AddQueryCounts`,
  `addQQueryOn`, `addQQuery`: the additive query model.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W G : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The additive oracle -/

/-- The additive oracle on a basis state: add `aᵢ` to the `some`-part of the answer register of a
query to `i`. -/
def addOracleMap (a : ι → G) : QBasis ι G W → QBasis ι G W
  | (some i, t, w) => (some i, t.map (· + a i), w)
  | p => p

/-- The additive oracle as a permutation (its inverse adds `−aᵢ`). -/
def addOraclePerm (a : ι → G) : Equiv.Perm (QBasis ι G W) where
  toFun := addOracleMap a
  invFun := addOracleMap (-a)
  left_inv := by
    rintro ⟨_ | i, _ | c, w⟩ <;> simp [addOracleMap]
  right_inv := by
    rintro ⟨_ | i, _ | c, w⟩ <;> simp [addOracleMap]

/-- **The additive oracle** `|i, c⟩ ↦ |i, c + aᵢ⟩` over a finite abelian group. -/
def addOracleMat (a : ι → G) : Matrix (QBasis ι G W) (QBasis ι G W) ℂ :=
  qPerm (addOraclePerm a)

theorem addOracleMat_mem_unitaryGroup (a : ι → G) :
    addOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι G W) ℂ := by
  exact qPerm_mem_unitaryGroup _

lemma addOracleMat_mulVec_apply (a : ι → G) (ψ : QBasis ι G W → ℂ) (p : QBasis ι G W) :
    (addOracleMat a *ᵥ ψ) p = ψ (addOracleMap (-a) p) := by
  rw [addOracleMat, qPerm_mulVec_apply]
  rfl

/-! ## The additive query model

`QAlg` carries no oracle; the state semantics does. These definitions copy `QAlg.state`,
`ComputesWithErrorOn`, `successProbOn`, `SolvesWithErrorOn`, `QueryCounts` and `qQueryOn` with
the additive oracle substituted. An algorithm of this model is a `QAlg ι G O W`: its basis
carries the group `G` as the answer type. -/

variable {O : Type}

/-- **The state of `A` on input `a` after `t` additive queries.** -/
def addState (A : QAlg ι G O W) (a : ι → G) : ℕ → (QBasis ι G W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (addOracleMat a *ᵥ addState A a t)

@[simp] lemma addState_zero (A : QAlg ι G O W) (a : ι → G) :
    addState A a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma addState_succ (A : QAlg ι G O W) (a : ι → G) (t : ℕ) :
    addState A a (t + 1) = A.step (t + 1) *ᵥ (addOracleMat a *ᵥ addState A a t) := rfl

theorem addState_isQState (A : QAlg ι G O W) (a : ι → G) (t : ℕ) :
    IsQState (addState A a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [addState_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (addOracleMat_mem_unitaryGroup a) ih)

/-- **The bridge to the parametric run**: the additive state is `runWith` of the algorithm's step
schedule, packaged with any length. -/
lemma addState_eq_runWith (A : QAlg ι G O W) (n : ℕ) (a : ι → G) (t : ℕ) :
    addState A a t
      = (QRoutine.mk n A.step A.step_unitary).runWith (addOracleMat a) t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [addState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

section Relations

variable {X : Type}

/-- **The probability that `A`, after `q` additive queries on the promise input `x`, outputs a
value valid for `x`.** -/
def addSuccessProbOn (A : QAlg ι G O W) (q : ℕ) (read : X → ι → G) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : ℝ :=
  goodProb A.readout (Good x) (addState A (read x) q)

/-- **`A` solves the relation `Good` on the promise with error at most `ε` in `q` additive
queries.** -/
def AddSolvesWithErrorOn (A : QAlg ι G O W) (q : ℕ) (read : X → ι → G) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤ addSuccessProbOn A q read Good x

end Relations

variable [DecidableEq O] {X : Type}

/-- `A` computes `f` on the promise `read` with error at most `ε` in `q` **additive queries**. -/
def AddComputesWithErrorOn (A : QAlg ι G O W) (q : ℕ) (read : X → ι → G) (f : X → O)
    (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ qProb A.readout (addState A (read x) q) (f x)

/-- The achievable additive query counts. -/
def AddQueryCounts (read : X → ι → G) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QAlg ι G O W), AddComputesWithErrorOn A q read f ε}

/-- Quantum query complexity in the **additive oracle model** over `G`. -/
noncomputable def addQQueryOn (read : X → ι → G) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (AddQueryCounts read f ε)

/-- The additive complexity of a total function. -/
noncomputable abbrev addQQuery (f : (ι → G) → O) (ε : ℝ) : ℕ :=
  addQQueryOn (X := ι → G) id f ε

theorem mem_addQueryCounts {read : X → ι → G} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι G O W}
    (h : AddComputesWithErrorOn A q read f ε) : q ∈ AddQueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

/-- **One algorithm bounds the additive complexity.** -/
theorem addQQueryOn_le {read : X → ι → G} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι G O W}
    (h : AddComputesWithErrorOn A q read f ε) : addQQueryOn read f ε ≤ q :=
  Nat.sInf_le (mem_addQueryCounts h)

/-- **Functions are relations** in the additive model: for `Good x y ↔ y = f x`, solving is
computing. -/
theorem addSolvesWithErrorOn_eq_iff {A : QAlg ι G O W} {q : ℕ} {read : X → ι → G} {f : X → O}
    {ε : ℝ} :
    AddSolvesWithErrorOn A q read (fun x y => y = f x) ε ↔
      AddComputesWithErrorOn A q read f ε := by
  refine forall_congr' fun x => ?_
  rw [addSuccessProbOn, goodProb_eq]

end QuantumQueryComplexity
