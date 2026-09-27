import QuantumQueryComplexity.Quantum.Amplitude.Routine
import QuantumQueryComplexity.Quantum.Amplitude.TrigSum
set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One verified, fixed-budget, randomized amplification trial

The iteration count cannot be chosen from the unknown success probability `pₓ`, so
:

1. **Dilution.**  A fair ancillary bit is added and only *(bit ∧ valid)* is marked, by the
   controlled marker (`mark.control`, still `C` queries).  The diluted success probability is
   `a = pₓ/2 ≤ 1/2`.  The diluted setup is `AmpSetup.dilute`.
2. **Verification.**  After `j` diluted iterations the *original* validity of the candidate
   is written coherently into a fresh flag by `flagRoutine` (`C` more queries), and the
   readout returns `some y` only when the flag is set.  Verifying the original predicate
   rather than the diluted one only increases the acceptance probability and keeps the
   guarantee that no invalid output is ever returned.
3. **Randomization.**  `j` is uniform in `{0,…,m−1}`; the branches are padded to the common
   budget `Q = S + (m−1)(2S+C) + C` and mixed (`Padding.lean`, `Mixture.lean`).

The exact law of one trial (`randTrial_prob_some`): for every output `y`,

    Pr[some y] = c · (if Good x y then Pr_orig[y] else 0),

with one constant `c = (1/m)·∑_j (α_j² + β_j²)/2` independent of `y`; and
`c · pₓ ≥ 1/4` whenever `pₓ ≥ p₀` and `m·√p₀ ≥ 1` (`quarter_le_randTrial_weight_mul`).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-! ## Lifting a routine to a controlled workspace, acting on both sectors -/

/-- Run `R` on the data of a `CtrlWork`, whatever the control bit and parking slot. -/
def QRoutine.liftCtrl (R : QRoutine ι σ W) : QRoutine ι σ (CtrlWork ι W) :=
  (R.liftReg (Option ι)).liftReg Bool

@[simp] lemma QRoutine.liftCtrl_len (R : QRoutine ι σ W) : R.liftCtrl.len = R.len := rfl

lemma QRoutine.liftCtrl_run_embedCtrl (R : QRoutine ι σ W) (a : ι → σ) (b : Bool)
    (φ : QBasis ι σ W → ℂ) :
    R.liftCtrl.run a *ᵥ embedCtrl b φ = embedCtrl b (R.run a *ᵥ φ) := by
  rw [QRoutine.liftCtrl, embedCtrl, QRoutine.liftReg_run_embed, QRoutine.liftReg_run_embed]
  rfl

lemma embedCtrl_smul (b : Bool) (c : ℂ) (φ : QBasis ι σ W → ℂ) :
    embedCtrl b (c • φ) = c • embedCtrl b φ := by
  rw [embedCtrl, embedReg_smul, embedReg_smul]
  rfl

lemma embedCtrl_neg (b : Bool) (φ : QBasis ι σ W → ℂ) :
    embedCtrl b (-φ) = -embedCtrl b φ := by
  rw [← neg_one_smul ℂ φ, embedCtrl_smul, neg_one_smul]

/-! ## Reading a candidate through a flag -/

/-- Return the candidate only when the flag (the control bit) is set. -/
def flagReadout (r : QBasis ι σ W → O) : QBasis ι σ (CtrlWork ι W) → Option O :=
  fun q => if q.2.2.1 = true then some (dropCtrl r q) else none

/-- The flagged law: only the flag-true sector can return a candidate. -/
lemma qProb_flagReadout_some [DecidableEq O] (r : QBasis ι σ W → O)
    (χ₀ χ₁ : QBasis ι σ W → ℂ) (y : O) :
    qProb (flagReadout r) (embedCtrl false χ₀ + embedCtrl true χ₁) (some y) = qProb r χ₁ y := by
  rw [← qProb_embedCtrl r true χ₁ y, qProb, qProb]
  refine Finset.sum_congr rfl fun q => fun _ => ?_
  obtain ⟨k, t, b, s, w⟩ := q
  cases b
  · simp [flagReadout, embedCtrl_apply]
  · simp [flagReadout, embedCtrl_apply]

/-- The law of a two-sector state under a sector-blind readout. -/
lemma qProb_dropCtrl_two_sectors [DecidableEq O] (r : QBasis ι σ W → O) (c₀ c₁ : ℂ)
    (χ₀ χ₁ : QBasis ι σ W → ℂ) (y : O) :
    qProb (dropCtrl r) (c₁ • embedCtrl true χ₁ + c₀ • embedCtrl false χ₀) y
      = Complex.normSq c₁ * qProb r χ₁ y + Complex.normSq c₀ * qProb r χ₀ y := by
  rw [← qProb_embedCtrl r true χ₁ y, ← qProb_embedCtrl r false χ₀ y, ← qProb_smul,
    ← qProb_smul, qProb, qProb, qProb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q => fun _ => ?_
  obtain ⟨k, t, b, s, w⟩ := q
  cases b
  · simp [embedCtrl_apply]
  · simp [embedCtrl_apply]

namespace AmpSetup

variable (P : AmpSetup ι σ W O)

/-! ## Dilution -/

/-- **The diluted setup**: a fair control bit, the data prepared in both sectors, and the
marker controlled on the bit.  Same costs `S` and `C`. -/
noncomputable def dilute : AmpSetup ι σ (CtrlWork ι W) O where
  prep := (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup).comp P.prep.liftCtrl
  init := embedCtrl false P.init
  init_isQState := isQState_embedCtrl false P.init_isQState
  mark := P.mark.control
  readout := dropCtrl P.readout

@[simp] lemma dilute_prep_len : P.dilute.prep.len = P.prep.len := by
  show 0 + P.prep.liftCtrl.len = P.prep.len
  rw [QRoutine.liftCtrl_len]; omega

@[simp] lemma dilute_mark_len : P.dilute.mark.len = P.mark.len := control_len _

lemma dilute_prepared (a : ι → σ) :
    P.dilute.prepared a
      = hadS • embedCtrl true (P.prepared a) + hadS • embedCtrl false (P.prepared a) := by
  rw [prepared, dilute, QRoutine.comp_run, QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec,
    ctrlHad_mulVec_embedCtrl, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    QRoutine.liftCtrl_run_embedCtrl, QRoutine.liftCtrl_run_embedCtrl]
  simp only [hadMat_apply, Bool.and_false, if_false, Bool.false_eq_true]
  rfl

variable {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- The diluted good part: control bit set and the candidate valid. -/
noncomputable def dilGood (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  hadS • embedCtrl true (goodPart P.readout (Good x) (P.prepared (read x)))

/-- The diluted bad part. -/
noncomputable def dilBad (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  hadS • embedCtrl false (P.prepared (read x))
    + hadS • embedCtrl true (badPart P.readout (Good x) (P.prepared (read x)))

lemma qNormSq_dilGood (x : X) :
    qNormSq (P.dilGood read Good x) = P.succProb read Good x / 2 := by
  rw [dilGood, qNormSq_smul, normSq_hadS, qNormSq_embedCtrl, qNormSq_goodPart, succProb]
  ring

theorem groverSplit_dilute (x : X) :
    GroverSplit (P.dilute.prepared (read x)) (P.dilGood read Good x) (P.dilBad read Good x) := by
  refine ⟨P.dilute.isQState_prepared _, ?_, ?_⟩
  · have hsplit : embedCtrl true (P.prepared (read x))
        = embedCtrl true (goodPart P.readout (Good x) (P.prepared (read x)))
          + embedCtrl true (badPart P.readout (Good x) (P.prepared (read x))) := by
      rw [← embedCtrl_add, goodPart_add_badPart]
    rw [dilute_prepared, dilGood, dilBad, hsplit]
    module
  · simp only [dilGood, dilBad, qInner_add_right, qInner_smul_left, qInner_smul_right,
      qInner_embedCtrl, qInner_goodPart_badPart]
    simp

lemma dilute_mark_good (hP : P.Marks read Good) (x : X) :
    P.dilute.mark.run (read x) *ᵥ P.dilGood read Good x = -P.dilGood read Good x := by
  show P.mark.control.run (read x) *ᵥ _ = _
  rw [dilGood, Matrix.mulVec_smul, control_run_true, (hP x).1, embedCtrl_neg, smul_neg]

lemma dilute_mark_bad (hP : P.Marks read Good) (x : X) :
    P.dilute.mark.run (read x) *ᵥ P.dilBad read Good x = P.dilBad read Good x := by
  show P.mark.control.run (read x) *ᵥ _ = _
  rw [dilBad, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, control_run_false,
    control_run_true, (hP x).2]

/-- **The diluted state after `j` iterations.** -/
theorem dilute_ampRoutine_run (hP : P.Marks read Good) (x : X) (j : ℕ) :
    (P.dilute.ampRoutine j).run (read x) *ᵥ P.dilute.init
      = ((ampA (P.succProb read Good x / 2) j : ℝ) : ℂ) • P.dilGood read Good x
        + ((ampB (P.succProb read Good x / 2) j : ℝ) : ℂ) • P.dilBad read Good x := by
  have h := P.dilute.ampRoutine_run_mulVec_of_split (read x) (P.groverSplit_dilute x)
    (P.dilute_mark_good hP x) (P.dilute_mark_bad hP x) j
  rwa [qNormSq_dilGood] at h

/-! ## The verified trial -/

/-- The valid and invalid components of the diluted iterate, by the *original* predicate. -/
noncomputable def trialGood (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (j : ℕ) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  (((ampA (P.succProb read Good x / 2) j : ℝ) : ℂ) * hadS)
      • embedCtrl true (goodPart P.readout (Good x) (P.prepared (read x)))
    + (((ampB (P.succProb read Good x / 2) j : ℝ) : ℂ) * hadS)
      • embedCtrl false (goodPart P.readout (Good x) (P.prepared (read x)))

noncomputable def trialBad (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (j : ℕ) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  (((ampB (P.succProb read Good x / 2) j : ℝ) : ℂ) * hadS)
      • (embedCtrl false (badPart P.readout (Good x) (P.prepared (read x)))
        + embedCtrl true (badPart P.readout (Good x) (P.prepared (read x))))

lemma trialGood_add_trialBad (x : X) (j : ℕ) :
    P.trialGood read Good x j + P.trialBad read Good x j
      = ((ampA (P.succProb read Good x / 2) j : ℝ) : ℂ) • P.dilGood read Good x
        + ((ampB (P.succProb read Good x / 2) j : ℝ) : ℂ) • P.dilBad read Good x := by
  have hsplit : embedCtrl false (P.prepared (read x))
      = embedCtrl false (goodPart P.readout (Good x) (P.prepared (read x)))
        + embedCtrl false (badPart P.readout (Good x) (P.prepared (read x))) := by
    rw [← embedCtrl_add, goodPart_add_badPart]
  rw [trialGood, trialBad, dilGood, dilBad, hsplit]
  module

/-- **One verified trial** with `j` diluted iterations: prepare, iterate, write the flag. -/
noncomputable def trialRoutine (j : ℕ) : QRoutine ι σ (CtrlWork ι (CtrlWork ι W)) :=
  (P.dilute.ampRoutine j).liftCtrl.comp (flagRoutine P.mark.liftCtrl)

/-- **`len = S + j·(2S+C) + C`**: the flag extraction is charged. -/
@[simp] lemma trialRoutine_len (j : ℕ) :
    (P.trialRoutine j).len
      = P.prep.len + j * (2 * P.prep.len + P.mark.len) + P.mark.len := by
  rw [trialRoutine, QRoutine.comp_len, QRoutine.liftCtrl_len, ampRoutine_len, flagRoutine_len,
    QRoutine.liftCtrl_len, dilute_prep_len, dilute_mark_len]

lemma liftCtrl_mark_trialGood (hP : P.Marks read Good) (x : X) (j : ℕ) :
    P.mark.liftCtrl.run (read x) *ᵥ P.trialGood read Good x j = -P.trialGood read Good x j := by
  rw [trialGood, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    QRoutine.liftCtrl_run_embedCtrl, QRoutine.liftCtrl_run_embedCtrl, (hP x).1,
    embedCtrl_neg, embedCtrl_neg]
  module

lemma liftCtrl_mark_trialBad (hP : P.Marks read Good) (x : X) (j : ℕ) :
    P.mark.liftCtrl.run (read x) *ᵥ P.trialBad read Good x j = P.trialBad read Good x j := by
  rw [trialBad, Matrix.mulVec_smul, Matrix.mulVec_add, QRoutine.liftCtrl_run_embedCtrl,
    QRoutine.liftCtrl_run_embedCtrl, (hP x).2]

/-- **The final state of a trial**: the valid component sits in the flag-true sector. -/
theorem trialRoutine_run (hP : P.Marks read Good) (x : X) (j : ℕ) :
    (P.trialRoutine j).run (read x) *ᵥ embedCtrl false P.dilute.init
      = embedCtrl false (P.trialBad read Good x j) + embedCtrl true (P.trialGood read Good x j) := by
  rw [trialRoutine, QRoutine.comp_run, ← Matrix.mulVec_mulVec, QRoutine.liftCtrl_run_embedCtrl,
    P.dilute_ampRoutine_run hP, ← trialGood_add_trialBad]
  exact flagRoutine_run _ _ (P.liftCtrl_mark_trialGood hP x j) (P.liftCtrl_mark_trialBad hP x j)

/-- The trial as an algorithm with output `Option O`. -/
noncomputable def trialAlg (j : ℕ) : QAlg ι σ (Option O) (CtrlWork ι (CtrlWork ι W)) :=
  (P.trialRoutine j).toAlg (embedCtrl false P.dilute.init)
    (isQState_embedCtrl false P.dilute.init_isQState) (flagReadout (dropCtrl P.readout))

variable [DecidableEq O]

/-- The weight of one trial: `(α_j² + β_j²)/2` at the diluted probability `pₓ/2`. -/
noncomputable def trialWeight (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (j : ℕ) : ℝ :=
  (ampA (P.succProb read Good x / 2) j ^ 2 + ampB (P.succProb read Good x / 2) j ^ 2) / 2

/-- **The exact law of one trial**: a candidate is returned with a probability proportional
to its original probability if it is valid, and never if it is not. -/
theorem trialAlg_prob_some (hP : P.Marks read Good) (x : X) (j : ℕ) (y : O) :
    (P.trialAlg j).prob (read x) (P.trialRoutine j).len (some y)
      = P.trialWeight read Good x j
          * (if Good x y then P.origAlg.prob (read x) P.prep.len y else 0) := by
  rw [QAlg.prob, trialAlg, QRoutine.toAlg_state_len, P.trialRoutine_run hP]
  show qProb (flagReadout (dropCtrl P.readout)) _ (some y) = _
  rw [qProb_flagReadout_some, trialGood, qProb_dropCtrl_two_sectors, qProb_goodPart,
    QAlg.prob, origAlg_state, trialWeight]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, normSq_hadS]
  show _ = _ * (if Good x y then qProb P.readout _ y else 0)
  ring

/-- The diluted success of a trial is at least `sin²((2j+1)θ)`, `sin² θ = pₓ/2`. -/
theorem sin_sq_le_trialWeight_mul (x : X) (j : ℕ) :
    Real.sin ((2 * j + 1) * groverAngle (P.succProb read Good x / 2)) ^ 2
      ≤ P.trialWeight read Good x j * P.succProb read Good x := by
  have h0 := P.succProb_nonneg (read := read) (Good := Good) x
  have h1 := P.succProb_le_one (read := read) (Good := Good) x
  rw [← mul_ampA_sq (by linarith) (by linarith), trialWeight]
  nlinarith [sq_nonneg (ampB (P.succProb read Good x / 2) j)]

/-! ## Randomizing the iteration count -/

/-- The common budget of a randomized trial: `S + (m−1)(2S+C) + C`. -/
def trialBudget (m : ℕ) : ℕ :=
  P.prep.len + (m - 1) * (2 * P.prep.len + P.mark.len) + P.mark.len

lemma trialRoutine_len_le (m : ℕ) (j : Fin m) : (P.trialRoutine j).len ≤ P.trialBudget m := by
  rw [trialRoutine_len, trialBudget]
  have : (j : ℕ) ≤ m - 1 := by have := j.2; omega
  have := Nat.mul_le_mul_right (2 * P.prep.len + P.mark.len) this
  omega

/-- **`Q ≤ m·(2S+C)`.** -/
lemma trialBudget_le (m : ℕ) (hm : 0 < m) :
    P.trialBudget m ≤ m * (2 * P.prep.len + P.mark.len) := by
  rw [trialBudget]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  omega

/-- **The randomized trial**: `j` uniform in `Fin m`, branches padded to the budget. -/
noncomputable def randTrial (m : ℕ) (hm : 0 < m) :
    QAlg ι σ (Option O) (Σ _ : Fin m, CtrlWork ι (CtrlWork ι (CtrlWork ι W))) :=
  mixAlg (fun _ : Fin m => (1 : ℝ) / m) (fun _ => by positivity)
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
    (fun j => padAlg (P.trialAlg j) (P.trialRoutine j).len
      (P.trialBudget m - (P.trialRoutine j).len))

/-- The weight of the randomized trial: the average of the trial weights. -/
noncomputable def randWeight (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) (m : ℕ) : ℝ :=
  (∑ j : Fin m, P.trialWeight read Good x j) / m

/-- **The exact law of the randomized trial.** -/
theorem randTrial_prob_some (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) (y : O) :
    (P.randTrial m hm).prob (read x) (P.trialBudget m) (some y)
      = P.randWeight read Good x m
          * (if Good x y then P.origAlg.prob (read x) P.prep.len y else 0) := by
  rw [randTrial, mixAlg_prob, randWeight, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlen := P.trialRoutine_len_le m j
  have hpad := padAlg_prob (P.trialAlg j) (P.trialRoutine j).len
    (P.trialBudget m - (P.trialRoutine j).len) (read x) (some y)
  rw [show (P.trialRoutine j).len + (P.trialBudget m - (P.trialRoutine j).len)
      = P.trialBudget m by omega] at hpad
  rw [hpad, P.trialAlg_prob_some hP]
  ring

lemma randWeight_nonneg (x : X) (m : ℕ) : 0 ≤ P.randWeight read Good x m :=
  div_nonneg (Finset.sum_nonneg fun j _ => by rw [trialWeight]; positivity) (Nat.cast_nonneg m)

/-- **One randomized trial succeeds with probability at least `1/4`** when `pₓ ≥ p₀` and
`m·√p₀ ≥ 1`. -/
theorem quarter_le_randWeight_mul (x : X) {m : ℕ} (hm : 0 < m) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hpp : p₀ ≤ P.succProb read Good x) (hmp : 1 ≤ (m : ℝ) * Real.sqrt p₀) :
    1 / 4 ≤ P.randWeight read Good x m * P.succProb read Good x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum := quarter_le_sum_sin_sq hp₀ hpp (P.succProb_le_one x) hmp
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Real.sin ((2 * (j : ℝ) + 1) * groverAngle (P.succProb read Good x / 2)) ^ 2) m]
    at hsum
  have hle : (∑ j : Fin m,
      Real.sin ((2 * ((j : ℕ) : ℝ) + 1) * groverAngle (P.succProb read Good x / 2)) ^ 2)
      ≤ (∑ j : Fin m, P.trialWeight read Good x j) * P.succProb read Good x := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => P.sin_sq_le_trialWeight_mul x j
  rw [randWeight, div_mul_eq_mul_div, le_div_iff₀ hm']
  linarith

end AmpSetup

end QuantumQueryComplexity
