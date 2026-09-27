import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.Amplitude.Geometry
import QuantumQueryComplexity.Quantum.HadamardTest
import QuantumQueryComplexity.Quantum.Clock
set_option synthInstance.maxSize 800
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Exact phase markers, clean ancillas, and coherent success flags

The validity of an output is input-dependent, so an algorithm can learn it only through a
query routine. This file fixes the contracts and provides adapters between
the logical output predicate and its coherent marker.

* `goodPart rd G ψ`, `badPart rd G ψ`: the components of `ψ` on the basis states whose
  readout is valid / invalid.  They split a unit vector as a `GroverSplit`, and
  `qProb rd (goodPart rd G ψ) y = if G y then qProb rd ψ y else 0`.
* `IsPhaseMarker mark read Good rd`: the **full-operator** contract
  `mark.run (read x) = I − 2Πₓ` (stated on vectors: `φ ↦ badPart φ − goodPart φ`).
* `IsCleanPhaseMarker mark E read Good rd`: the **clean-ancilla** contract
  `mark.run (read x) (E φ) = E (Sₓ φ)` for every logical `φ`; nothing is required on dirty
  ancillas.
* `MarksState mark read Good rd ψ`: what the rotation actually uses — the marker negates
  the good part and fixes the bad part of the prepared states `ψ x`.  Both contracts above
  imply it.  (An identity on `ψ x` alone would not do: the iterate visits both parts.)
* `markerOfVerifier`: an exact coherent verifier of cost `V`, run forwards, a phase on its
  success bit, run backwards: a clean phase marker of cost `2V`.  A bounded-error Boolean
  algorithm is **not** such a verifier.
* `flagRoutine mark`: Hadamard, controlled marker, Hadamard — writes the validity bit of
  the *candidate* coherently at the marker's cost `C`, preserving the candidate and
  restoring the parking register.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## Good and bad parts -/

section Parts

variable {H : Type} [Fintype H] [DecidableEq H] {O : Type}

/-- The component of `ψ` on basis states with a valid readout. -/
def goodPart (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) : H → ℂ :=
  qRestrict (fun h => decide (G (rd h))) true ψ

/-- The component of `ψ` on basis states with an invalid readout. -/
def badPart (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) : H → ℂ :=
  qRestrict (fun h => decide (G (rd h))) false ψ

variable (rd : H → O) (G : O → Prop) [DecidablePred G]

lemma goodPart_apply (ψ : H → ℂ) (h : H) :
    goodPart rd G ψ h = if G (rd h) then ψ h else 0 := by
  simp [goodPart, qRestrict]

lemma badPart_apply (ψ : H → ℂ) (h : H) :
    badPart rd G ψ h = if G (rd h) then 0 else ψ h := by
  by_cases hg : G (rd h) <;> simp [badPart, qRestrict, hg]

lemma goodPart_add_badPart (ψ : H → ℂ) : goodPart rd G ψ + badPart rd G ψ = ψ := by
  funext h
  rw [Pi.add_apply, goodPart_apply, badPart_apply]
  split_ifs <;> simp

lemma qInner_goodPart_badPart (ψ φ : H → ℂ) :
    qInner (goodPart rd G ψ) (badPart rd G φ) = 0 :=
  qInner_qRestrict_of_ne _ (by decide) ψ φ

lemma qNormSq_goodPart (ψ : H → ℂ) : qNormSq (goodPart rd G ψ) = goodProb rd G ψ :=
  (qProb_eq_qNormSq_qRestrict _ _ _).symm

lemma goodPart_goodPart (ψ : H → ℂ) : goodPart rd G (goodPart rd G ψ) = goodPart rd G ψ := by
  funext h; simp only [goodPart_apply]; split_ifs <;> rfl

lemma badPart_goodPart (ψ : H → ℂ) : badPart rd G (goodPart rd G ψ) = 0 := by
  funext h; simp only [goodPart_apply, badPart_apply, Pi.zero_apply]; split_ifs <;> rfl

lemma goodPart_badPart (ψ : H → ℂ) : goodPart rd G (badPart rd G ψ) = 0 := by
  funext h; simp only [goodPart_apply, badPart_apply, Pi.zero_apply]; split_ifs <;> rfl

lemma badPart_badPart (ψ : H → ℂ) : badPart rd G (badPart rd G ψ) = badPart rd G ψ := by
  funext h; simp only [badPart_apply]; split_ifs <;> rfl

lemma goodPart_sub (ψ φ : H → ℂ) :
    goodPart rd G (ψ - φ) = goodPart rd G ψ - goodPart rd G φ := by
  funext h; simp only [goodPart_apply, Pi.sub_apply]; split_ifs <;> simp

lemma badPart_sub (ψ φ : H → ℂ) :
    badPart rd G (ψ - φ) = badPart rd G ψ - badPart rd G φ := by
  funext h; simp only [badPart_apply, Pi.sub_apply]; split_ifs <;> simp

lemma goodPart_add (ψ φ : H → ℂ) :
    goodPart rd G (ψ + φ) = goodPart rd G ψ + goodPart rd G φ := by
  funext h; simp only [goodPart_apply, Pi.add_apply]; split_ifs <;> simp

lemma badPart_add (ψ φ : H → ℂ) :
    badPart rd G (ψ + φ) = badPart rd G ψ + badPart rd G φ := by
  funext h; simp only [badPart_apply, Pi.add_apply]; split_ifs <;> simp

lemma goodPart_smul (c : ℂ) (ψ : H → ℂ) : goodPart rd G (c • ψ) = c • goodPart rd G ψ := by
  funext h; simp only [goodPart_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

lemma badPart_smul (c : ℂ) (ψ : H → ℂ) : badPart rd G (c • ψ) = c • badPart rd G ψ := by
  funext h; simp only [badPart_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- The unit vector `ψ` splits into its good and bad parts. -/
theorem groverSplit_parts {ψ : H → ℂ} (hψ : IsQState ψ) :
    GroverSplit ψ (goodPart rd G ψ) (badPart rd G ψ) :=
  ⟨hψ, (goodPart_add_badPart rd G ψ).symm, qInner_goodPart_badPart rd G ψ ψ⟩

/-- The phase flip `I − 2Π`, on vectors. -/
def phaseFlip (ψ : H → ℂ) : H → ℂ := badPart rd G ψ - goodPart rd G ψ

lemma phaseFlip_goodPart (ψ : H → ℂ) :
    phaseFlip rd G (goodPart rd G ψ) = -goodPart rd G ψ := by
  rw [phaseFlip, badPart_goodPart, goodPart_goodPart, zero_sub]

lemma phaseFlip_badPart (ψ : H → ℂ) :
    phaseFlip rd G (badPart rd G ψ) = badPart rd G ψ := by
  rw [phaseFlip, badPart_badPart, goodPart_badPart, sub_zero]

/-- The outcome law of the good part: the valid outcomes keep their probabilities. -/
lemma qProb_goodPart [DecidableEq O] (ψ : H → ℂ) (y : O) :
    qProb rd (goodPart rd G ψ) y = if G y then qProb rd ψ y else 0 := by
  simp only [qProb, goodPart_apply]
  by_cases hy : G y
  · rw [if_pos hy]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : rd h = y
    · rw [if_pos hh, if_pos hh, if_pos (hh ▸ hy)]
    · rw [if_neg hh, if_neg hh]
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun h _ => ?_
    by_cases hh : rd h = y
    · rw [if_pos hh, if_neg (hh ▸ hy)]; simp
    · rw [if_neg hh]

end Parts

/-! ## Marker contracts -/

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- **The full-operator phase marker**: `mark.run (read x) = I − 2Πₓ`. -/
def IsPhaseMarker (mark : QRoutine ι σ W) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (rd : QBasis ι σ W → O) : Prop :=
  ∀ x φ, mark.run (read x) *ᵥ φ = phaseFlip rd (Good x) φ

/-- **What the rotation uses**: the marker negates the good part and fixes the bad part of
the prepared states. -/
def MarksState (mark : QRoutine ι σ W) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (rd : QBasis ι σ W → O)
    (ψ : X → (QBasis ι σ W → ℂ)) : Prop :=
  ∀ x, mark.run (read x) *ᵥ goodPart rd (Good x) (ψ x) = -goodPart rd (Good x) (ψ x) ∧
    mark.run (read x) *ᵥ badPart rd (Good x) (ψ x) = badPart rd (Good x) (ψ x)

theorem IsPhaseMarker.marksState {mark : QRoutine ι σ W} {read : X → ι → σ}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {rd : QBasis ι σ W → O}
    (h : IsPhaseMarker mark read Good rd) (ψ : X → (QBasis ι σ W → ℂ)) :
    MarksState mark read Good rd ψ := fun x =>
  ⟨by rw [h, phaseFlip_goodPart], by rw [h, phaseFlip_badPart]⟩

/-- **The clean-ancilla phase marker**: on the image of the embedding `E` it acts as the
logical `I − 2Πₓ`; dirty ancillas are unconstrained. -/
def IsCleanPhaseMarker {W' : Type} [Fintype W'] [DecidableEq W'] (mark : QRoutine ι σ W')
    (E : (QBasis ι σ W → ℂ) → (QBasis ι σ W' → ℂ)) (read : X → ι → σ)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (rd : QBasis ι σ W → O) : Prop :=
  ∀ x φ, mark.run (read x) *ᵥ E φ = E (phaseFlip rd (Good x) φ)

/-- A clean marker marks every embedded prepared state, for a physical readout `rd'` whose
good and bad parts commute with the embedding. -/
theorem IsCleanPhaseMarker.marksState {W' : Type} [Fintype W'] [DecidableEq W']
    {mark : QRoutine ι σ W'} {E : (QBasis ι σ W → ℂ) → (QBasis ι σ W' → ℂ)}
    {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]
    {rd : QBasis ι σ W → O} (h : IsCleanPhaseMarker mark E read Good rd)
    (rd' : QBasis ι σ W' → O) (hneg : ∀ φ, E (-φ) = -E φ)
    (hg : ∀ x φ, goodPart rd' (Good x) (E φ) = E (goodPart rd (Good x) φ))
    (hb : ∀ x φ, badPart rd' (Good x) (E φ) = E (badPart rd (Good x) φ))
    (ψ : X → (QBasis ι σ W → ℂ)) :
    MarksState mark read Good rd' (fun x => E (ψ x)) := fun x =>
  ⟨by rw [hg, h, phaseFlip_goodPart, hneg], by rw [hb, h, phaseFlip_badPart]⟩

/-! ## Adapter 1: a coherent verifier gives a clean phase marker at twice the cost -/

/-- The phase gate `diag(1, −1)` on a flag bit. -/
noncomputable def zMat : Matrix Bool Bool ℂ :=
  Matrix.of fun b b' => if b = b' then (if b then -1 else 1) else 0

lemma zMat_mem_unitaryGroup : zMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext b b'
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases b <;> cases b' <;> simp [zMat, Matrix.conjTranspose_apply, Matrix.one_apply]

/-- **An exact coherent verifier**: on a clean flag it writes the validity of the data,
preserving the data. -/
def IsCoherentVerifier (Vr : QRoutine ι σ (Bool × W)) (read : X → ι → σ)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (rd : QBasis ι σ W → O) : Prop :=
  ∀ x φ, Vr.run (read x) *ᵥ embedReg false φ
    = embedReg false (badPart rd (Good x) φ) + embedReg true (goodPart rd (Good x) φ)

/-- Verify, phase the success bit, unverify. -/
noncomputable def markerOfVerifier (Vr : QRoutine ι σ (Bool × W)) : QRoutine ι σ (Bool × W) :=
  (Vr.comp (QRoutine.ofUnitary (regOp zMat) (regOp_mem_unitaryGroup zMat_mem_unitaryGroup))).comp
    Vr.inv

@[simp] lemma markerOfVerifier_len (Vr : QRoutine ι σ (Bool × W)) :
    (markerOfVerifier Vr).len = 2 * Vr.len := by
  change Vr.len + 0 + Vr.inv.len = 2 * Vr.len
  rw [QRoutine.inv_len]; omega

/-- **Adapter 1**: the verifier's marker is a clean phase marker, at cost `2V`. -/
theorem isCleanPhaseMarker_markerOfVerifier {Vr : QRoutine ι σ (Bool × W)}
    {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]
    {rd : QBasis ι σ W → O} (h : IsCoherentVerifier Vr read Good rd) :
    IsCleanPhaseMarker (markerOfVerifier Vr) (embedReg false) read Good rd := by
  intro x φ
  have hV := Vr.run_mem_unitaryGroup (read x)
  have hZ : ∀ (b : Bool) (χ : QBasis ι σ W → ℂ),
      regOp zMat *ᵥ embedReg b χ = (if b then (-1 : ℂ) else 1) • embedReg b χ := by
    intro b χ
    rw [regOp_mulVec_embedReg, Fintype.sum_bool]
    cases b <;> simp [zMat]
  -- the forward verifier applied to the target state gives the phased state
  have hfwd : Vr.run (read x) *ᵥ embedReg false (phaseFlip rd (Good x) φ)
      = embedReg false (badPart rd (Good x) φ) - embedReg true (goodPart rd (Good x) φ) := by
    rw [h, phaseFlip, badPart_sub, goodPart_sub, badPart_badPart, badPart_goodPart,
      goodPart_badPart, goodPart_goodPart, sub_zero, zero_sub]
    rw [← neg_one_smul ℂ (goodPart rd (Good x) φ), embedReg_smul]
    module
  rw [markerOfVerifier, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
    QRoutine.inv_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_add,
    hZ, hZ]
  simp only [Bool.false_eq_true, if_false, if_true, one_smul, neg_smul]
  rw [← sub_eq_add_neg, ← hfwd, Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary hV,
    Matrix.one_mulVec]

/-! ## Adapter 2: the coherent success flag -/

/-- Hadamard, controlled marker, Hadamard. -/
noncomputable def flagRoutine (mark : QRoutine ι σ W) : QRoutine ι σ (CtrlWork ι W) :=
  (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup).comp
    (mark.control.comp (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup))

@[simp] lemma flagRoutine_len (mark : QRoutine ι σ W) : (flagRoutine mark).len = mark.len := by
  change 0 + (mark.control.len + 0) = mark.len
  rw [control_len]; omega

/-- **Adapter 2**: on a clean control bit, the validity of the candidate is written into
the bit; the candidate itself is preserved and the parking register is restored. -/
theorem flagRoutine_run (mark : QRoutine ι σ W) (a : ι → σ) {φg φb : QBasis ι σ W → ℂ}
    (hg : mark.run a *ᵥ φg = -φg) (hb : mark.run a *ᵥ φb = φb) :
    (flagRoutine mark).run a *ᵥ embedCtrl false (φg + φb)
      = embedCtrl false φb + embedCtrl true φg := by
  have hM : mark.run a *ᵥ (φg + φb) = φb - φg := by
    rw [Matrix.mulVec_add, hg, hb]; abel
  rw [flagRoutine, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ctrlHad_mulVec_embedCtrl,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, control_run_true,
    control_run_false, hM, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    ctrlHad_mulVec_embedCtrl, ctrlHad_mulVec_embedCtrl]
  simp only [hadMat_apply, Bool.and_false, Bool.and_true, Bool.and_self, if_false, if_true,
    Bool.false_eq_true]
  have h2 := hadS_mul_hadS
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, embedCtrl_apply, Pi.sub_apply]
  by_cases h1 : p.2.2.1 = true <;> by_cases h3 : p.2.2.2.1 = none
  · simp only [h1, h3, and_self, if_true, Bool.true_eq_false, false_and, if_false]
    linear_combination (2 * φg (p.1, p.2.1, p.2.2.2.2)) * h2
  · simp [h1, h3]
  · have h1' : p.2.2.1 = false := by simpa using h1
    simp only [h1', h3, and_self, if_true, Bool.false_eq_true, false_and, if_false]
    linear_combination (2 * φb (p.1, p.2.1, p.2.2.2.2)) * h2
  · simp [h3]

end QuantumQueryComplexity
