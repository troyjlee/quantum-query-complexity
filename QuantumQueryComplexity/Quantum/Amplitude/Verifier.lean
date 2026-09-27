import QuantumQueryComplexity.Quantum.Amplitude.Routine
import QuantumQueryComplexity.Quantum.Simulation
set_option synthInstance.maxSize 800
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# An amplification setup from an exact coherent verifier

A caller who has a preparation routine (`S` queries), an input-independent initial vector, a
readout, and an **exact coherent verifier** (`V` queries, `IsCoherentVerifier`: on a clean
flag it writes the validity of the candidate and preserves the logical state, for every
logical vector) gets an `AmpSetup` with no ancilla bookkeeping:

    AmpSetup.ofVerifier prep init hinit rd verifier : AmpSetup ι σ (Bool × W) O
      prep    := prep.liftReg Bool                       (S queries)
      init    := embedReg false init
      mark    := markerOfVerifier verifier               (2·V queries: verify, phase, unverify)
      readout := flagBlind rd                            (= stripReadout rd, flag ignored)

The constructor takes no hidden input, no `read`, no `Good`.  Those enter only in

* `ofVerifier_marks`:
  `IsCoherentVerifier verifier read Good rd → (ofVerifier …).Marks read Good`,
  with every embedding / readout-commutation obligation discharged here;
* `ofVerifier_origAlg_prob`, `ofVerifier_succProb`: the original output law and success mass
  are those of the logical algorithm `prep.toAlg init hinit rd`;
* `ofVerifier_ampRoutine_run`: the ordinary Grover iterates stay in the clean subspace, as
  the embedded combination `α_j·good + β_j·bad` of the logical parts (no division; `p = 0`,
  `p = 1` and overshooting included).  Nothing of the sort is claimed for the four-trial
  algorithm with its seeds and stored registers.

`(ofVerifier …).amplified` and `.aeAlg` are the public algorithms; their budgets are the
existing ones at `C = 2·V` — a marker built by verifying and unverifying is never charged
`V`.  The marker is only a *clean* phase marker: nothing is assumed, or true in general,
on dirty flag states.  A bounded-error Boolean verifier does not satisfy the contract.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- The flag-blind extension of a logical readout (`stripReadout`, without any decidability
assumption on the outputs). -/
def flagBlind (rd : QBasis ι σ W → O) : QBasis ι σ (Bool × W) → O :=
  fun p => rd (p.1, p.2.1, p.2.2.2)

lemma flagBlind_eq_stripReadout [DecidableEq O] (rd : QBasis ι σ W → O) :
    flagBlind rd = stripReadout (V := Bool) rd := rfl

/-- **The setup of a preparation routine and an exact coherent verifier.** -/
noncomputable def AmpSetup.ofVerifier (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (rd : QBasis ι σ W → O) (verifier : QRoutine ι σ (Bool × W)) :
    AmpSetup ι σ (Bool × W) O where
  prep := prep.liftReg Bool
  init := embedReg false init
  init_isQState := isQState_embedReg false hinit
  mark := markerOfVerifier verifier
  readout := flagBlind rd

section

variable (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
  (rd : QBasis ι σ W → O) (verifier : QRoutine ι σ (Bool × W))

/-! ## Costs -/

@[simp] lemma ofVerifier_prep_len :
    (AmpSetup.ofVerifier prep init hinit rd verifier).prep.len = prep.len := rfl

/-- **The marker costs `2·V`**: verify and unverify. -/
@[simp] lemma ofVerifier_mark_len :
    (AmpSetup.ofVerifier prep init hinit rd verifier).mark.len = 2 * verifier.len :=
  markerOfVerifier_len verifier

/-! ## Transport -/

/-- **The prepared state is the embedded logical prepared state.** -/
theorem ofVerifier_prepared (a : ι → σ) :
    (AmpSetup.ofVerifier prep init hinit rd verifier).prepared a
      = embedReg false (prep.run a *ᵥ init) := by
  rw [AmpSetup.prepared]
  exact QRoutine.liftReg_run_embed prep a false init

lemma embedReg_neg (v : Bool) (φ : QBasis ι σ W → ℂ) :
    embedReg v (-φ) = -embedReg v φ := by
  rw [← neg_one_smul ℂ φ, embedReg_smul, neg_one_smul]

/-- Taking the good part commutes with the clean embedding. -/
theorem goodPart_flagBlind_embedReg (G : O → Prop) [DecidablePred G] (v : Bool)
    (χ : QBasis ι σ W → ℂ) :
    goodPart (flagBlind rd) G (embedReg v χ) = embedReg v (goodPart rd G χ) :=
  qRestrict_stripReadout_embedReg (fun h => decide (G (rd h))) v true χ

/-- Taking the bad part commutes with the clean embedding. -/
theorem badPart_flagBlind_embedReg (G : O → Prop) [DecidablePred G] (v : Bool)
    (χ : QBasis ι σ W → ℂ) :
    badPart (flagBlind rd) G (embedReg v χ) = embedReg v (badPart rd G χ) :=
  qRestrict_stripReadout_embedReg (fun h => decide (G (rd h))) v false χ

/-- **The original output law is the logical one**, at the same query count. -/
theorem ofVerifier_origAlg_prob [DecidableEq O] (a : ι → σ) (y : O) :
    (AmpSetup.ofVerifier prep init hinit rd verifier).origAlg.prob a
        (AmpSetup.ofVerifier prep init hinit rd verifier).prep.len y
      = (prep.toAlg init hinit rd).prob a prep.len y := by
  rw [QAlg.prob, AmpSetup.origAlg_state, ofVerifier_prepared, QAlg.prob,
    QRoutine.toAlg_state_len]
  exact qProb_stripReadout_embedReg rd false y _

variable {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- **The original success mass is the logical one.** -/
theorem ofVerifier_succProb (x : X) :
    (AmpSetup.ofVerifier prep init hinit rd verifier).succProb read Good x
      = goodProb rd (Good x) (prep.run (read x) *ᵥ init) := by
  rw [AmpSetup.succProb, ofVerifier_prepared]
  exact qProb_stripReadout_embedReg (fun h => decide (Good x (rd h))) false true _

/-- **The correctness bridge**: an exact coherent verifier makes the constructed setup
mark its prepared states.  No embedding or readout hypothesis is left to the caller. -/
theorem ofVerifier_marks (h : IsCoherentVerifier verifier read Good rd) :
    (AmpSetup.ofVerifier prep init hinit rd verifier).Marks read Good := by
  have hm := (isCleanPhaseMarker_markerOfVerifier h).marksState (flagBlind rd)
    (fun φ => embedReg_neg false φ)
    (fun x φ => goodPart_flagBlind_embedReg rd (Good x) false φ)
    (fun x φ => badPart_flagBlind_embedReg rd (Good x) false φ)
    (fun x => prep.run (read x) *ᵥ init)
  intro x
  have hx := hm x
  beta_reduce at hx ⊢
  rw [ofVerifier_prepared]
  exact hx

/-- **The ordinary Grover iterates stay clean**: the state of `ampRoutine j` is the embedded
combination `α_j·good + β_j·bad` of the logical good and bad parts. -/
theorem ofVerifier_ampRoutine_run (h : IsCoherentVerifier verifier read Good rd) (x : X)
    (j : ℕ) :
    ((AmpSetup.ofVerifier prep init hinit rd verifier).ampRoutine j).run (read x)
        *ᵥ (AmpSetup.ofVerifier prep init hinit rd verifier).init
      = embedReg false
          (((ampA (goodProb rd (Good x) (prep.run (read x) *ᵥ init)) j : ℝ) : ℂ)
              • goodPart rd (Good x) (prep.run (read x) *ᵥ init)
            + ((ampB (goodProb rd (Good x) (prep.run (read x) *ᵥ init)) j : ℝ) : ℂ)
              • badPart rd (Good x) (prep.run (read x) *ᵥ init)) := by
  rw [AmpSetup.ampRoutine_run_mulVec _ (ofVerifier_marks prep init hinit rd verifier h) x j,
    ofVerifier_succProb, ofVerifier_prepared]
  show _ • goodPart (flagBlind rd) _ _ + _ • badPart (flagBlind rd) _ _ = _
  rw [goodPart_flagBlind_embedReg, badPart_flagBlind_embedReg, embedReg_add, embedReg_smul,
    embedReg_smul]

end

end QuantumQueryComplexity
