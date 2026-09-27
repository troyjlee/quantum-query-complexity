import QuantumQueryComplexity.Quantum.SelectRoutine
import QuantumQueryComplexity.Quantum.CoherentMajority
import QuantumQueryComplexity.Quantum.Amplitude.Routine
import QuantumQueryComplexity.Quantum.Simulation
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Robust search: the recursive levels

Høyer–Mosca–de Wolf search with bounded-error tests, as compiled routines.

A **level** `RSLevel ι σ I` is a routine `A` on its own workspace, an input-independent unit
initial vector, and two *physical* readouts of the computational basis: the acceptance flag
`acc` and the candidate index `idx : … → I`.  The true predicate never appears here.

A **test bank** `TestBank ι σ I` is a routine `F` on a fresh workspace together with, for every
candidate `i`, a unit initial vector `β i` and a Boolean readout `t`: the test of candidate
`i` is "start the bank in `β i`, run `F`, read `t`".  (For supplied algorithms with different
workspaces this is `selectPadded`, repeated and read by majority: `Main.lean`.)

`RSLevel.next L K i₀` is one recursion step:

1. **amplify the recorded flag once**: `G = −A S₀ A⁻¹ S_acc` applied to `A·init`, i.e.
   `(L.setup).ampRoutine 1` with the zero-query marker `signMarker L.acc` — three
   invocations of `A` (two forwards, one inverse);
2. **initialize a fresh bank coherently by the index**: the bank starts in the blank vector
   `embedReg true (K.β i₀)` and the free unitary `bankCtrl L.idx (swapRefl blank (β i))`
   carries it, on the component of index `i`, to `embedReg false (K.β i)`;
3. **run the fresh test** `K.F` on the bank;
4. the new flag is `old flag ∧ test bit`; the old flag, the old bank and all garbage stay.

`next_len : (L.next K i₀).A.len = 3 · L.A.len + K.F.len` is the exact query recurrence: no
preparation, inverse or controlled invocation is missing from it, and the free steps are
input-independent unitaries.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-! ## The zero-query marker of a physical flag -/

section Sign

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The diagonal sign of a flag. -/
def signMat (f : QBasis ι σ W → Bool) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  Matrix.diagonal fun h => if f h then -1 else 1

lemma signMat_mem_unitaryGroup (f : QBasis ι σ W → Bool) :
    signMat f ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, signMat,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext h
  by_cases hf : f h <;> simp [hf]

lemma signMat_mulVec (f : QBasis ι σ W → Bool) (φ : QBasis ι σ W → ℂ) :
    signMat f *ᵥ φ = phaseFlip f (· = true) φ := by
  funext h
  rw [signMat, Matrix.mulVec_diagonal, phaseFlip, Pi.sub_apply, goodPart_apply, badPart_apply]
  by_cases hf : f h = true <;> simp [hf]

/-- **Reflecting a physical flag is free and exact.** -/
def signMarker (f : QBasis ι σ W → Bool) : QRoutine ι σ W :=
  QRoutine.ofUnitary (signMat f) (signMat_mem_unitaryGroup f)

@[simp] lemma signMarker_len (f : QBasis ι σ W → Bool) :
    (signMarker (ι := ι) (σ := σ) f).len = 0 := rfl

lemma signMarker_run (f : QBasis ι σ W → Bool) (a : ι → σ) (φ : QBasis ι σ W → ℂ) :
    (signMarker f).run a *ᵥ φ = phaseFlip f (· = true) φ := by
  rw [signMarker, QRoutine.ofUnitary_run, signMat_mulVec]

end Sign

/-! ## Levels and test banks -/

/-- A level of the recursion. -/
structure RSLevel (ι σ I : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] where
  /-- The workspace. -/
  Y : Type
  [fY : Fintype Y]
  [dY : DecidableEq Y]
  /-- The routine. -/
  A : QRoutine ι σ Y
  /-- The input-independent initial vector. -/
  init : QBasis ι σ Y → ℂ
  init_unit : IsQState init
  /-- The physical acceptance flag. -/
  acc : QBasis ι σ Y → Bool
  /-- The physical candidate index. -/
  idx : QBasis ι σ Y → I

attribute [instance] RSLevel.fY RSLevel.dY

/-- A bank of tests. -/
structure TestBank (ι σ I : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] where
  /-- The workspace of the bank. -/
  B : Type
  [fB : Fintype B]
  [dB : DecidableEq B]
  /-- The test routine. -/
  F : QRoutine ι σ B
  /-- The initial vector of the test of candidate `i`. -/
  β : I → QBasis ι σ B → ℂ
  β_unit : ∀ i, IsQState (β i)
  /-- The test bit. -/
  t : QBasis ι σ B → Bool

attribute [instance] TestBank.fB TestBank.dB

variable {I : Type} [Fintype I] [DecidableEq I]

namespace TestBank

variable (K : TestBank ι σ I)

/-- The blank vector of the bank, orthogonal to every test's initial vector. -/
noncomputable def blank (i₀ : I) : QBasis ι σ (Bool × K.B) → ℂ := embedReg true (K.β i₀)

/-- The embedded initial vector of the test of candidate `i`. -/
noncomputable def start (i : I) : QBasis ι σ (Bool × K.B) → ℂ := embedReg false (K.β i)

lemma isQState_blank (i₀ : I) : IsQState (K.blank i₀) := isQState_embedReg true (K.β_unit i₀)

lemma isQState_start (i : I) : IsQState (K.start i) := isQState_embedReg false (K.β_unit i)

lemma qInner_blank_start (i₀ i : I) : qInner (K.blank i₀) (K.start i) = 0 := by
  rw [blank, start, qInner_embedReg, if_neg (by simp)]

/-- The free index-controlled initialization of the bank. -/
noncomputable def prepMat (i₀ : I) (i : I) :
    Matrix (QBasis ι σ (Bool × K.B)) (QBasis ι σ (Bool × K.B)) ℂ :=
  swapRefl (K.blank i₀) (K.start i)

lemma prepMat_mem_unitaryGroup (i₀ i : I) : K.prepMat i₀ i ∈ Matrix.unitaryGroup _ ℂ :=
  swapRefl_mem_unitaryGroup (K.isQState_blank i₀) (K.isQState_start i)
    (K.qInner_blank_start i₀ i)

lemma prepMat_mulVec_blank (i₀ i : I) : K.prepMat i₀ i *ᵥ K.blank i₀ = K.start i :=
  swapRefl_mulVec (K.isQState_blank i₀) (K.qInner_blank_start i₀ i)

/-- The acceptance probability of the test of candidate `i` on the input `a`. -/
noncomputable def accProb (a : ι → σ) (i : I) : ℝ := qProb K.t (K.F.run a *ᵥ K.β i) true

lemma accProb_nonneg (a : ι → σ) (i : I) : 0 ≤ K.accProb a i := qProb_nonneg _ _ _

end TestBank

namespace RSLevel

variable (L : RSLevel ι σ I)

/-- The amplification setup of the recorded flag. -/
noncomputable def setup : AmpSetup ι σ L.Y Bool where
  prep := L.A
  init := L.init
  init_isQState := L.init_unit
  mark := signMarker L.acc
  readout := L.acc

/-- The state of the level on the input `a`. -/
noncomputable def state (a : ι → σ) : QBasis ι σ L.Y → ℂ := L.A.run a *ᵥ L.init

lemma isQState_state (a : ι → σ) : IsQState (L.state a) := L.setup.isQState_prepared a

/-- The joint readout: flag and index. -/
def flagIdx : QBasis ι σ L.Y → Bool × I := fun y => (L.acc y, L.idx y)

/-- **`Pr[flag ∧ index = i]`.** -/
noncomputable def u (a : ι → σ) (i : I) : ℝ := qProb L.flagIdx (L.state a) (true, i)

/-- **`Pr[flag]`.** -/
noncomputable def p (a : ι → σ) : ℝ := qProb L.acc (L.state a) true

lemma u_nonneg (a : ι → σ) (i : I) : 0 ≤ L.u a i := qProb_nonneg _ _ _

/-- The output of a level: the index if the flag is set. -/
def out : QBasis ι σ L.Y → Option I := fun y => if L.acc y then some (L.idx y) else none

/-- The level as an algorithm. -/
noncomputable def alg : QAlg ι σ (Option I) L.Y := L.A.toAlg L.init L.init_unit L.out

/-- The routine of one recursion step. -/
noncomputable def nextA (K : TestBank ι σ I) (i₀ : I) :
    QRoutine ι σ (QBasis ι σ L.Y × QBasis ι σ (Bool × K.B)) :=
  (pairRoutine (L.setup.ampRoutine 1) QRoutine.identity).comp
    ((QRoutine.ofUnitary (bankCtrl L.idx (K.prepMat i₀))
        (bankCtrl_mem_unitaryGroup L.idx (K.prepMat_mem_unitaryGroup i₀))).comp
      (pairRoutine QRoutine.identity (K.F.liftReg Bool)))

/-- **One recursion step.** -/
noncomputable def next (K : TestBank ι σ I) (i₀ : I) : RSLevel ι σ I where
  Y := QBasis ι σ L.Y × QBasis ι σ (Bool × K.B)
  A := L.nextA K i₀
  init := prodState blankReg L.init (K.blank i₀)
  init_unit := isQState_prodState L.init_unit (K.isQState_blank i₀)
  acc := fun p => L.acc p.2.2.1 && stripReadout K.t p.2.2.2
  idx := fun p => L.idx p.2.2.1

/-- **The exact query recurrence.** -/
theorem next_len (K : TestBank ι σ I) (i₀ : I) :
    (L.next K i₀).A.len = 3 * L.A.len + K.F.len := by
  have h1 : L.setup.prep.len = L.A.len := rfl
  have h2 : L.setup.mark.len = 0 := rfl
  simp only [next, nextA, QRoutine.comp_len, pairRoutine_len, QRoutine.ofUnitary_len,
    QRoutine.identity_len, QRoutine.liftReg_len, AmpSetup.ampRoutine_len, h1, h2]
  ring

end RSLevel

end QuantumQueryComplexity
