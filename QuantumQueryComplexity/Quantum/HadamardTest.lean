import QuantumQueryComplexity.Quantum.Control
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The Hadamard test, compiled

The generic measurement layer of the algorithm extraction: given a routine `R`
and a unit vector `u`, the **Hadamard test** prepares
`(|0⟩ + |1⟩)/√2 ⊗ u`, runs `R` controlled on the first qubit, applies a
Hadamard to it, and measures it.  The whole point:

    P(announce true)  = (1 + Re⟪u, R.run a · u⟫)/2
    P(announce false) = (1 − Re⟪u, R.run a · u⟫)/2

(`hadTest_prob_true` / `hadTest_prob_false`) — the test turns the real part of
the expectation `⟪u, R_a u⟫`, which the fidelity bounds of `Fidelity.lean`
control, into an outcome probability, at **exactly `R.len` queries**
(`QRoutine.control` costs `R.len`, the Hadamards are free).

The compilation reuses the existing plumbing wholesale: `QRoutine.control`
for the controlled run, `regOp` for the Hadamard on the control register,
`comp`/`ofUnitary` for the final gate, and `toAlg` for the bridge to `QAlg`.
The announcement convention is `true` on control `0`: the detector this test
will be applied to is `≈ +1` on the accepting side, so acceptance is
constructive interference back onto `|0⟩`.

`hadMat` is real symmetric, and everything about it is decided entrywise over
`Bool` — no `2 × 2` matrix theory is imported.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## The Hadamard gate, on the control register -/

/-- `1/√2`, as a complex scalar. -/
noncomputable def hadS : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

lemma star_hadS : star hadS = hadS := by
  rw [hadS, RCLike.star_def, Complex.conj_ofReal]

lemma hadS_mul_hadS : hadS * hadS = (2 : ℂ)⁻¹ := by
  rw [hadS, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma normSq_hadS : Complex.normSq hadS = 2⁻¹ := by
  rw [hadS, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Hadamard gate on one qubit: `(1/√2)·(−1)^{b·b'}`. -/
noncomputable def hadMat : Matrix Bool Bool ℂ :=
  Matrix.of fun b b' => if b && b' then -hadS else hadS

@[simp] lemma hadMat_apply (b b' : Bool) :
    hadMat b b' = if b && b' then -hadS else hadS := rfl

lemma hadMat_mem_unitaryGroup : hadMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext b b'
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases b <;> cases b' <;>
    simp only [Matrix.conjTranspose_apply, hadMat_apply, Bool.and_self,
      Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true,
      if_true, if_false, Bool.false_eq_true, star_neg, star_hadS,
      Matrix.one_apply, mul_neg, neg_mul, neg_neg, hadS_mul_hadS] <;>
    norm_num

/-- The Hadamard on the control register of `CtrlWork`. -/
noncomputable def ctrlHad :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  regOp hadMat

lemma regOp_mem_unitaryGroup {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A ∈ Matrix.unitaryGroup V ℂ) :
    regOp (ι := ι) (σ := σ) (W := W) A
      ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    regOp_conjTranspose, regOp_mul, conjTranspose_mul_self_of_unitary hA,
    regOp_one]

lemma ctrlHad_mem_unitaryGroup :
    ctrlHad (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  regOp_mem_unitaryGroup hadMat_mem_unitaryGroup

/-- **The Hadamard acts on the control sectors** as its column says. -/
lemma ctrlHad_mulVec_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    ctrlHad *ᵥ embedCtrl b ψ
      = hadMat true b • embedCtrl true ψ + hadMat false b • embedCtrl false ψ := by
  rw [ctrlHad, embedCtrl, regOp_mulVec_embedReg, Fintype.sum_bool]
  rfl

/-! ## Sector algebra -/

lemma embedCtrl_add (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedCtrl b (ψ + φ) = embedCtrl b ψ + embedCtrl b φ := by
  funext p
  by_cases h : p.2.2.1 = b ∧ p.2.2.2.1 = none <;>
    simp [embedCtrl_apply, h]

lemma embedCtrl_sub (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedCtrl b (ψ - φ) = embedCtrl b ψ - embedCtrl b φ := by
  funext p
  by_cases h : p.2.2.1 = b ∧ p.2.2.2.1 = none <;>
    simp [embedCtrl_apply, h]

lemma qNormSq_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedCtrl b ψ) = qNormSq ψ := by
  rw [embedCtrl, qNormSq_embedReg, qNormSq_embedReg]

lemma qInner_embedCtrl (b b' : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedCtrl b ψ) (embedCtrl b' φ)
      = if b = b' then qInner ψ φ else 0 := by
  rw [embedCtrl, embedCtrl, qInner_embedReg]
  by_cases h : b = b'
  · rw [if_pos h, if_pos h, qInner_embedReg, if_pos rfl]
  · rw [if_neg h, if_neg h]

/-! ## The test -/

/-- The Hadamard-test initial state: `(|0⟩ + |1⟩)/√2 ⊗ u`. -/
noncomputable def hadInit (u : QBasis ι σ W → ℂ) :
    QBasis ι σ (CtrlWork ι W) → ℂ :=
  hadS • (embedCtrl false u + embedCtrl true u)

lemma isQState_hadInit {u : QBasis ι σ W → ℂ} (hu : IsQState u) :
    IsQState (hadInit u) := by
  rw [IsQState, hadInit, qNormSq_smul, normSq_hadS, qNormSq_add,
    qNormSq_embedCtrl, qNormSq_embedCtrl, qInner_embedCtrl,
    if_neg (by simp : ¬(false = true)), hu]
  norm_num

/-- **The Hadamard test of `R` on `u`**: controlled-`R` between two Hadamards
on a control qubit, measuring the control.  Announces `true` on control `0`.
Costs exactly `R.len` queries. -/
noncomputable def hadTest (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) : QAlg ι σ Bool (CtrlWork ι W) :=
  (R.control.comp (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup)).toAlg
    (hadInit u) (isQState_hadInit hu) (fun p => !p.2.2.1)

lemma hadTest_readout (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) :
    (hadTest R u hu).readout = fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1 :=
  rfl

/-- **The final state of the test**, exactly: interference between `u` and
`R_a u`, sorted by the control bit. -/
theorem hadTest_state (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).state a R.len
      = (hadS * hadS) • (embedCtrl false (u + R.run a *ᵥ u)
          + embedCtrl true (u - R.run a *ᵥ u)) := by
  have hlen : (R.control.comp
      (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup)).len = R.len := by
    rw [QRoutine.comp_len, QRoutine.ofUnitary_len, control_len,
      Nat.add_zero]
  rw [hadTest, ← hlen, QRoutine.toAlg_state_len, QRoutine.comp_run,
    QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec, hadInit,
    Matrix.mulVec_smul, Matrix.mulVec_add, control_run_false,
    control_run_true, Matrix.mulVec_smul, Matrix.mulVec_add,
    ctrlHad_mulVec_embedCtrl, ctrlHad_mulVec_embedCtrl]
  simp only [hadMat_apply, Bool.and_false, Bool.and_true, Bool.and_self,
    if_false, if_true, Bool.false_eq_true]
  rw [embedCtrl_add, embedCtrl_sub]
  module

/-- The measurement rule of the sorted state. -/
lemma qProb_hadReadout_true (a : ℂ) (χ₁ χ₂ : QBasis ι σ W → ℂ) :
    qProb (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1)
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂)) true
      = Complex.normSq a * qNormSq χ₁ := by
  rw [qProb_eq_qNormSq_qRestrict]
  have hres : qRestrict (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1) true
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂))
      = a • embedCtrl false χ₁ := by
    funext p
    rw [qRestrict]
    cases hb : p.2.2.1 with
    | false => simp [hb, embedCtrl_apply]
    | true => simp [hb, embedCtrl_apply]
  rw [hres, qNormSq_smul, qNormSq_embedCtrl]

lemma qProb_hadReadout_false (a : ℂ) (χ₁ χ₂ : QBasis ι σ W → ℂ) :
    qProb (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1)
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂)) false
      = Complex.normSq a * qNormSq χ₂ := by
  rw [qProb_eq_qNormSq_qRestrict]
  have hres : qRestrict (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1) false
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂))
      = a • embedCtrl true χ₂ := by
    funext p
    rw [qRestrict]
    cases hb : p.2.2.1 with
    | false => simp [hb, embedCtrl_apply]
    | true => simp [hb, embedCtrl_apply]
  rw [hres, qNormSq_smul, qNormSq_embedCtrl]

private lemma normSq_hadS_sq : Complex.normSq (hadS * hadS) = 4⁻¹ := by
  rw [Complex.normSq_mul, normSq_hadS]
  norm_num

/-- **The acceptance probability of the Hadamard test.** -/
theorem hadTest_prob_true (R : QRoutine ι σ W) {u : QBasis ι σ W → ℂ}
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).prob a R.len true
      = (1 + (qInner u (R.run a *ᵥ u)).re) / 2 := by
  rw [QAlg.prob, hadTest_readout, hadTest_state R u hu a,
    qProb_hadReadout_true, normSq_hadS_sq, qNormSq_add, hu,
    qNormSq_mulVec (R.run_mem_unitaryGroup a), hu]
  ring

/-- **The rejection probability of the Hadamard test.** -/
theorem hadTest_prob_false (R : QRoutine ι σ W) {u : QBasis ι σ W → ℂ}
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).prob a R.len false
      = (1 - (qInner u (R.run a *ᵥ u)).re) / 2 := by
  have hsub : qNormSq (u - R.run a *ᵥ u)
      = 2 - 2 * (qInner u (R.run a *ᵥ u)).re := by
    have h : u - R.run a *ᵥ u = u + (-1 : ℂ) • (R.run a *ᵥ u) := by module
    rw [h, qNormSq_add, qNormSq_smul, qInner_smul_right, hu,
      qNormSq_mulVec (R.run_mem_unitaryGroup a), hu]
    simp only [Complex.normSq_neg, Complex.normSq_one, neg_one_mul,
      Complex.neg_re]
    ring
  rw [QAlg.prob, hadTest_readout, hadTest_state R u hu a,
    qProb_hadReadout_false, normSq_hadS_sq, hsub]
  ring

end QuantumQueryComplexity
