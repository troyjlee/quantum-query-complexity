import QuantumQueryComplexity.Quantum.Amplitude.Marker
import QuantumQueryComplexity.Quantum.Mixture
set_option synthInstance.maxSize 800
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The compiled Grover iterate

An `AmpSetup` is the supplied data of amplitude amplification: a preparation routine (`S`
queries), an input-independent unit initial vector, a marker routine (`C` queries) and a
readout.  From it this file compiles, in execution order *marker, then the reflection about
the prepared state*,

    grover      = mark ; prep⁻¹ ; (2|η⟩⟨η| − I) ; prep          grover.len = 2·S + C
    ampRoutine j = prep ; grover^j                               len = S + j·(2·S + C)

with `grover.run a = (2|ψ_a⟩⟨ψ_a| − I) · mark.run a`, `ψ_a = prep.run a · η` (this sign
convention exactly).  For a marker correct on the good and bad parts of the prepared state,

* `ampRoutine_run_mulVec`: the state after `j` iterations is `α_j·good + β_j·bad`;
* `successProbOn_ampAlg`: its success probability is `sin²((2j+1)θ)`, `sin² θ = p`, for every
  `0 ≤ p ≤ 1` including the endpoints;
* `prob_ampAlg_of_good`, `successProb_mul_prob_ampAlg`: the successful component is a scalar
  multiple of the original one, so for every output `y`

      p · Pr_amp[y ∧ valid] = Pr_amp[valid] · Pr_orig[y ∧ valid].

  The product form needs no positivity: an iterate may overshoot to success `0`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- The supplied data of amplitude amplification. -/
structure AmpSetup (ι σ W O : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype W] [DecidableEq W] where
  /-- The preparation routine. -/
  prep : QRoutine ι σ W
  /-- The input-independent initial vector. -/
  init : QBasis ι σ W → ℂ
  /-- It is a unit vector. -/
  init_isQState : IsQState init
  /-- The marker routine. -/
  mark : QRoutine ι σ W
  /-- The readout of a candidate output. -/
  readout : QBasis ι σ W → O

namespace AmpSetup

variable (P : AmpSetup ι σ W O)

/-- The prepared state on input `a`. -/
noncomputable def prepared (a : ι → σ) : QBasis ι σ W → ℂ := P.prep.run a *ᵥ P.init

lemma isQState_prepared (a : ι → σ) : IsQState (P.prepared a) :=
  IsQState.mulVec (P.prep.run_mem_unitaryGroup a) P.init_isQState

/-- The original algorithm: prepare and read out. -/
def origAlg : QAlg ι σ O W := P.prep.toAlg P.init P.init_isQState P.readout

lemma origAlg_state (a : ι → σ) : P.origAlg.state a P.prep.len = P.prepared a :=
  QRoutine.toAlg_state_len _ _ _ _ _

/-- The reflection about the prepared state: `prep · (2|η⟩⟨η| − I) · prep⁻¹`. -/
noncomputable def prepRefl : QRoutine ι σ W :=
  P.prep.inv.conjFixed (stateRefl P.init) (stateRefl_mem_unitaryGroup P.init_isQState)

@[simp] lemma prepRefl_len : P.prepRefl.len = 2 * P.prep.len := by
  rw [prepRefl, QRoutine.conjFixed_len, QRoutine.inv_len]

lemma prepRefl_run (a : ι → σ) : P.prepRefl.run a = stateRefl (P.prepared a) := by
  rw [prepRefl, QRoutine.conjFixed_run, QRoutine.inv_run, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, mul_stateRefl_mul_conjTranspose (P.prep.run_mem_unitaryGroup a)]
  rfl

/-- **The Grover iterate**: the marker, then the reflection about the prepared state. -/
noncomputable def grover : QRoutine ι σ W := P.mark.comp P.prepRefl

/-- **`grover.len = 2·S + C`.** -/
@[simp] lemma grover_len : P.grover.len = 2 * P.prep.len + P.mark.len := by
  rw [grover, QRoutine.comp_len, prepRefl_len]; omega

lemma grover_run (a : ι → σ) :
    P.grover.run a = stateRefl (P.prepared a) * P.mark.run a := by
  rw [grover, QRoutine.comp_run, prepRefl_run]

/-- Prepare, then iterate `j` times. -/
noncomputable def ampRoutine (j : ℕ) : QRoutine ι σ W := P.prep.comp (P.grover.iterate j)

/-- **`len = S + j·(2·S + C)`.** -/
@[simp] lemma ampRoutine_len (j : ℕ) :
    (P.ampRoutine j).len = P.prep.len + j * (2 * P.prep.len + P.mark.len) := by
  rw [ampRoutine, QRoutine.comp_len, QRoutine.iterate_len, grover_len]

/-- **The state equation, abstractly**: for any orthogonal split of the prepared state on
which the marker acts correctly. -/
theorem ampRoutine_run_mulVec_of_split (a : ι → σ) {g b : QBasis ι σ W → ℂ}
    (hsplit : GroverSplit (P.prepared a) g b) (hg : P.mark.run a *ᵥ g = -g)
    (hb : P.mark.run a *ᵥ b = b) (j : ℕ) :
    (P.ampRoutine j).run a *ᵥ P.init
      = ((ampA (qNormSq g) j : ℝ) : ℂ) • g + ((ampB (qNormSq g) j : ℝ) : ℂ) • b := by
  rw [ampRoutine, QRoutine.comp_run, QRoutine.iterate_run, ← Matrix.mulVec_mulVec, grover_run]
  exact hsplit.grover_pow_mulVec hg hb j

/-- The amplified algorithm. -/
noncomputable def ampAlg (j : ℕ) : QAlg ι σ O W :=
  (P.ampRoutine j).toAlg P.init P.init_isQState P.readout

lemma ampAlg_state (a : ι → σ) (j : ℕ) :
    (P.ampAlg j).state a (P.ampRoutine j).len = (P.ampRoutine j).run a *ᵥ P.init :=
  QRoutine.toAlg_state_len _ _ _ _ _

/-! ## With a relation -/

variable {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- The marker contract of a setup: it marks the prepared states. -/
def Marks (P : AmpSetup ι σ W O) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] : Prop :=
  MarksState P.mark read Good P.readout (fun x => P.prepared (read x))

/-- The original success probability `pₓ`. -/
noncomputable def succProb (P : AmpSetup ι σ W O) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : ℝ :=
  goodProb P.readout (Good x) (P.prepared (read x))

lemma succProb_eq_successProbOn (x : X) :
    P.succProb read Good x = successProbOn P.origAlg P.prep.len read Good x := by
  rw [succProb, successProbOn, origAlg_state]
  rfl

lemma succProb_nonneg (x : X) : 0 ≤ P.succProb read Good x := goodProb_nonneg _ _ _

lemma succProb_le_one (x : X) : P.succProb read Good x ≤ 1 :=
  goodProb_le_one _ _ (P.isQState_prepared _)

/-- **The state after `j` iterations**: `α_j · good + β_j · bad`. -/
theorem ampRoutine_run_mulVec (hP : P.Marks read Good) (x : X) (j : ℕ) :
    (P.ampRoutine j).run (read x) *ᵥ P.init
      = ((ampA (P.succProb read Good x) j : ℝ) : ℂ)
          • goodPart P.readout (Good x) (P.prepared (read x))
        + ((ampB (P.succProb read Good x) j : ℝ) : ℂ)
          • badPart P.readout (Good x) (P.prepared (read x)) := by
  have h := P.ampRoutine_run_mulVec_of_split (read x)
    (groverSplit_parts P.readout (Good x) (P.isQState_prepared (read x))) (hP x).1 (hP x).2 j
  rwa [qNormSq_goodPart] at h

/-- **Collinearity**: the successful component of the amplified state is `α_j` times the
successful component of the prepared state. -/
theorem goodPart_ampRoutine_run (hP : P.Marks read Good) (x : X) (j : ℕ) :
    goodPart P.readout (Good x) ((P.ampRoutine j).run (read x) *ᵥ P.init)
      = ((ampA (P.succProb read Good x) j : ℝ) : ℂ)
          • goodPart P.readout (Good x) (P.prepared (read x)) := by
  rw [P.ampRoutine_run_mulVec hP, goodPart_add, goodPart_smul, goodPart_smul,
    goodPart_goodPart, goodPart_badPart, smul_zero, add_zero]

/-- **The amplified success probability is `sin²((2j+1)θ)`**, endpoints included. -/
theorem successProbOn_ampAlg (hP : P.Marks read Good) (x : X) (j : ℕ) :
    successProbOn (P.ampAlg j) (P.ampRoutine j).len read Good x
      = Real.sin ((2 * j + 1) * groverAngle (P.succProb read Good x)) ^ 2 := by
  rw [successProbOn, ampAlg_state, ← mul_ampA_sq (P.succProb_nonneg x) (P.succProb_le_one x)]
  show goodProb P.readout (Good x) _ = _
  rw [← qNormSq_goodPart, P.goodPart_ampRoutine_run hP, qNormSq_smul, Complex.normSq_ofReal,
    qNormSq_goodPart]
  rw [succProb]
  ring

variable [DecidableEq O]

/-- **The law of a valid output**: `α_j²` times its original probability. -/
theorem prob_ampAlg_of_good (hP : P.Marks read Good) (x : X) (j : ℕ) {y : O}
    (hy : Good x y) :
    (P.ampAlg j).prob (read x) (P.ampRoutine j).len y
      = ampA (P.succProb read Good x) j ^ 2 * P.origAlg.prob (read x) P.prep.len y := by
  have h1 := qProb_goodPart P.readout (Good x) ((P.ampRoutine j).run (read x) *ᵥ P.init) y
  have h2 := qProb_goodPart P.readout (Good x) (P.prepared (read x)) y
  rw [if_pos hy] at h1 h2
  rw [QAlg.prob, ampAlg_state, QAlg.prob, origAlg_state]
  show qProb P.readout _ y = _ * qProb P.readout _ y
  rw [← h1, ← h2, P.goodPart_ampRoutine_run hP, qProb_smul, Complex.normSq_ofReal]
  ring

/-- **The conditional law is preserved, in product form**:
`p · Pr_amp[y] = Pr_amp[valid] · Pr_orig[y]` for every valid `y`. -/
theorem successProb_mul_prob_ampAlg (hP : P.Marks read Good) (x : X) (j : ℕ) {y : O}
    (hy : Good x y) :
    P.succProb read Good x * (P.ampAlg j).prob (read x) (P.ampRoutine j).len y
      = successProbOn (P.ampAlg j) (P.ampRoutine j).len read Good x
          * P.origAlg.prob (read x) P.prep.len y := by
  rw [P.prob_ampAlg_of_good hP x j hy, P.successProbOn_ampAlg hP,
    ← mul_ampA_sq (P.succProb_nonneg x) (P.succProb_le_one x)]
  ring

end AmpSetup

end QuantumQueryComplexity
