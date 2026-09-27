import QuantumQueryComplexity.Quantum.Amplitude.Recursive
import QuantumQueryComplexity.Quantum.Amplitude.Randomized
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The clean-history reflection

A reflection routine `R` of a later level is guaranteed only when the ancillas of the earlier
reflections are clean.  `cleanRefl c R` is the compiled operation

    apply `R` on the branch where the physical flag `c` holds, and `−1` on the other branch,

built with one shared control bit and the parking construction: compute `c` into the control
bit (free permutation), run `R.control`, uncompute, and put the sign `−1` on `¬c` (free
diagonal).  The schedule is fixed: **it costs `R.len` queries on both branches**.

* `cleanMat c U = U·P_c − (1 − P_c)`, the operator on the base space;
* `cleanRefl_run` — on a clean control bit, `cleanRefl c R` acts as `cleanMat c (R.run a)`,
  provided `R` preserves the flag (`U P_c = P_c U`);
* `cleanMat_mem_unitaryGroup`;
* `IsApproxRefl.clean` — if `R` is a `β`-approximate reflection about a clean `s` on `D`, then
  `cleanMat c R` is one on `{w | P_c w ∈ D}`: on the dirty branch it is *exactly* the
  reflection, which is `−1` there.
* `liftCtrl X` — a routine run regardless of the control bit; `liftCtrl_run`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## The operator -/

section Mat

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The diagonal projector of a flag. -/
def flagProj (c : H → Bool) : Matrix H H ℂ := Matrix.diagonal fun h => if c h then 1 else 0

lemma flagProj_mulVec (c : H → Bool) (φ : H → ℂ) :
    flagProj c *ᵥ φ = goodPart c (· = true) φ := by
  funext h
  rw [flagProj, Matrix.mulVec_diagonal, goodPart_apply]
  by_cases hc : c h = true <;> simp [hc]

lemma one_sub_flagProj_mulVec (c : H → Bool) (φ : H → ℂ) :
    (1 - flagProj c) *ᵥ φ = badPart c (· = true) φ := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, flagProj_mulVec]
  exact sub_eq_of_eq_add' (goodPart_add_badPart c (· = true) φ).symm

lemma flagProj_mul_self (c : H → Bool) : flagProj c * flagProj c = flagProj c := by
  rw [flagProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext h; split_ifs <;> simp

lemma flagProj_conjTranspose (c : H → Bool) : (flagProj c)ᴴ = flagProj c := by
  rw [flagProj, Matrix.diagonal_conjTranspose]
  congr 1; funext h; simp only [Pi.star_apply]; split_ifs <;> simp

/-- **`U` on the clean branch, `−1` on the dirty branch.** -/
def cleanMat (c : H → Bool) (U : Matrix H H ℂ) : Matrix H H ℂ :=
  U * flagProj c - (1 - flagProj c)

lemma cleanMat_mulVec (c : H → Bool) (U : Matrix H H ℂ) (φ : H → ℂ) :
    cleanMat c U *ᵥ φ = U *ᵥ goodPart c (· = true) φ - badPart c (· = true) φ := by
  rw [cleanMat, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, flagProj_mulVec,
    one_sub_flagProj_mulVec]

theorem cleanMat_mem_unitaryGroup {c : H → Bool} {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hcomm : U * flagProj c = flagProj c * U) :
    cleanMat c U ∈ Matrix.unitaryGroup H ℂ := by
  have hUU := conjTranspose_mul_self_of_unitary hU
  have hP := flagProj_mul_self c
  have hPH := flagProj_conjTranspose c
  have hcomm' : Uᴴ * flagProj c = flagProj c * Uᴴ := by
    have := congrArg Matrix.conjTranspose hcomm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH] at this
    exact this.symm
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, cleanMat,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hPH]
  have e1 : flagProj c * Uᴴ * (U * flagProj c) = flagProj c := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hUU, Matrix.one_mul, hP]
  have e2 : flagProj c * Uᴴ * (1 - flagProj c) = 0 := by
    rw [← hcomm', Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hP, sub_self,
      Matrix.mul_zero]
  have e3 : (1 - flagProj c) * (U * flagProj c) = 0 := by
    rw [hcomm, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hP, sub_self,
      Matrix.zero_mul]
  have e4 : (1 - flagProj c) * (1 - flagProj c) = 1 - flagProj c := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP]; abel
  have expand : (flagProj c * Uᴴ - (1 - flagProj c)) * (U * flagProj c - (1 - flagProj c))
      = flagProj c * Uᴴ * (U * flagProj c) - flagProj c * Uᴴ * (1 - flagProj c)
        - (1 - flagProj c) * (U * flagProj c) + (1 - flagProj c) * (1 - flagProj c) := by
    noncomm_ring
  rw [expand, e1, e2, e3, e4]
  abel

/-- **The contract survives the dirty-branch convention.** -/
theorem IsApproxRefl.clean {R : Matrix H H ℂ} {s : H → ℂ} {D : Set (H → ℂ)} {β : ℝ}
    (h : IsApproxRefl R s D β) (hβ : 0 ≤ β) (hs : IsQState s) {c : H → Bool}
    (hsc : goodPart c (· = true) s = s) :
    IsApproxRefl (cleanMat c R) s {w | goodPart c (· = true) w ∈ D} β where
  fix := by
    have hb : badPart c (· = true) s = 0 := by rw [← hsc, badPart_goodPart]
    rw [cleanMat_mulVec, hsc, hb, sub_zero, h.fix]
  near := fun w hw => by
    set g := goodPart c (· = true) w with hg
    set b := badPart c (· = true) w with hb
    have hwsplit : w = g + b := (goodPart_add_badPart c (· = true) w).symm
    have hsb : qInner s b = 0 := by
      rw [← hsc, hb]; exact qInner_goodPart_badPart c (· = true) s w
    have hin : qInner s w = qInner s g := by rw [hwsplit, qInner_add_right, hsb, add_zero]
    have hrefl : stateRefl s *ᵥ w = stateRefl s *ᵥ g - b := by
      rw [stateRefl_mulVec, stateRefl_mulVec, hin]
      have : (2 * qInner s g) • s - w = (2 * qInner s g) • s - (g + b) := by rw [← hwsplit]
      rw [this]
      abel
    have hL : cleanMat c R *ᵥ w - stateRefl s *ᵥ w = R *ᵥ g - stateRefl s *ᵥ g := by
      rw [cleanMat_mulVec, hrefl]; abel
    rw [hL]
    refine (h.near g hw).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    -- the clean part of the orthogonal component is no longer than the whole
    have hgoodpart : g - qInner s g • s = goodPart c (· = true) (w - qInner s w • s) := by
      rw [goodPart_sub, goodPart_smul, hsc, hin]
    rw [hgoodpart]
    exact qNorm_goodPart_le c (· = true) _

end Mat

/-! ## The compiled routine -/

/-- XOR the flag into the control bit. -/
def flagXorMap (c : QBasis ι σ W → Bool) :
    QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W)
  | (k, t, (b, pk, w)) => (k, t, (xor b (c (k, t, w)), pk, w))

lemma flagXorMap_involutive (c : QBasis ι σ W → Bool) : Function.Involutive (flagXorMap c) := by
  rintro ⟨k, t, b, pk, w⟩
  simp [flagXorMap]

/-- The free permutation computing the flag. -/
def flagXorMat (c : QBasis ι σ W → Bool) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ (flagXorMap_involutive c))

lemma flagXorMat_mem_unitaryGroup (c : QBasis ι σ W → Bool) :
    flagXorMat c ∈ Matrix.unitaryGroup _ ℂ := qPerm_mem_unitaryGroup _

lemma flagXorMat_mulVec_apply (c : QBasis ι σ W → Bool) (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) : (flagXorMat c *ᵥ ψ) p = ψ (flagXorMap c p) := by
  rw [flagXorMat, qPerm_mulVec_apply]
  rfl

/-- On a clean control bit, the flag is written. -/
lemma flagXorMat_mulVec_embedCtrl_false (c : QBasis ι σ W → Bool) (φ : QBasis ι σ W → ℂ) :
    flagXorMat c *ᵥ embedCtrl false φ
      = embedCtrl true (goodPart c (· = true) φ) + embedCtrl false (badPart c (· = true) φ) := by
  funext p
  obtain ⟨k, t, b, pk, w⟩ := p
  rw [flagXorMat_mulVec_apply, flagXorMap]
  simp only [Pi.add_apply, embedCtrl_apply, goodPart_apply, badPart_apply]
  by_cases hc : c (k, t, w) = true <;> cases b <;> simp [hc]

/-- A flagged vector under a set control bit is unflagged. -/
lemma flagXorMat_mulVec_embedCtrl_true (c : QBasis ι σ W → Bool) (φ : QBasis ι σ W → ℂ)
    (hφ : badPart c (· = true) φ = 0) :
    flagXorMat c *ᵥ embedCtrl true φ = embedCtrl false φ := by
  have hφ' : ∀ q, c q ≠ true → φ q = 0 := fun q hq => by
    have := congrFun hφ q
    rwa [badPart_apply, if_neg hq] at this
  funext p
  obtain ⟨k, t, b, pk, w⟩ := p
  rw [flagXorMat_mulVec_apply, flagXorMap]
  simp only [embedCtrl_apply]
  by_cases hc : c (k, t, w) = true
  · cases b <;> simp [hc]
  · have h0 := hφ' (k, t, w) hc
    cases b <;> simp [hc, h0]

lemma flagXorMat_mulVec_embedCtrl_false_of_bad (c : QBasis ι σ W → Bool)
    (φ : QBasis ι σ W → ℂ) (hφ : goodPart c (· = true) φ = 0) :
    flagXorMat c *ᵥ embedCtrl false φ = embedCtrl false φ := by
  rw [flagXorMat_mulVec_embedCtrl_false, hφ]
  have : badPart c (· = true) φ = φ := by
    have := goodPart_add_badPart c (· = true) φ
    rwa [hφ, zero_add] at this
  rw [this]
  funext p
  simp [embedCtrl_apply]

/-- The sign `−1` on the dirty branch. -/
def dirtySignMat (c : QBasis ι σ W → Bool) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  Matrix.diagonal fun p => if c (p.1, p.2.1, p.2.2.2.2) then 1 else -1

lemma dirtySignMat_mem_unitaryGroup (c : QBasis ι σ W → Bool) :
    dirtySignMat c ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dirtySignMat,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  by_cases hc : c (p.1, p.2.1, p.2.2.2.2) <;> simp [hc]

lemma dirtySignMat_mulVec_embedCtrl (c : QBasis ι σ W → Bool) (b : Bool)
    (φ : QBasis ι σ W → ℂ) :
    dirtySignMat c *ᵥ embedCtrl b φ
      = embedCtrl b (goodPart c (· = true) φ - badPart c (· = true) φ) := by
  funext p
  rw [dirtySignMat, Matrix.mulVec_diagonal]
  simp only [embedCtrl_apply, Pi.sub_apply, goodPart_apply, badPart_apply]
  by_cases hc : c (p.1, p.2.1, p.2.2.2.2) = true <;>
    by_cases hp : p.2.2.1 = b ∧ p.2.2.2.1 = none <;> simp [hc, hp]

/-- **The clean-history reflection.** -/
noncomputable def cleanRefl (c : QBasis ι σ W → Bool) (R : QRoutine ι σ W) :
    QRoutine ι σ (CtrlWork ι W) :=
  (QRoutine.ofUnitary (flagXorMat c) (flagXorMat_mem_unitaryGroup c)).comp
    (R.control.comp
      ((QRoutine.ofUnitary (flagXorMat c) (flagXorMat_mem_unitaryGroup c)).comp
        (QRoutine.ofUnitary (dirtySignMat c) (dirtySignMat_mem_unitaryGroup c))))

/-- **The dirty branch is charged too**: the schedule is fixed. -/
@[simp] theorem cleanRefl_len (c : QBasis ι σ W → Bool) (R : QRoutine ι σ W) :
    (cleanRefl c R).len = R.len := by
  simp only [cleanRefl, QRoutine.comp_len, QRoutine.ofUnitary_len, control_len]
  omega

/-- **On a clean control bit it is `cleanMat`.** -/
theorem cleanRefl_run (c : QBasis ι σ W → Bool) (R : QRoutine ι σ W) (a : ι → σ)
    (hcomm : R.run a * flagProj c = flagProj c * R.run a) (φ : QBasis ι σ W → ℂ) :
    (cleanRefl c R).run a *ᵥ embedCtrl false φ
      = embedCtrl false (cleanMat c (R.run a) *ᵥ φ) := by
  have hpres : badPart c (· = true) (R.run a *ᵥ goodPart c (· = true) φ) = 0 := by
    rw [← flagProj_mulVec, ← one_sub_flagProj_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, flagProj_mul_self, sub_self, Matrix.zero_mul, Matrix.zero_mulVec]
  have hrun : (cleanRefl c R).run a
      = dirtySignMat c * (flagXorMat c * (R.control.run a * flagXorMat c)) := by
    rw [cleanRefl, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run,
      QRoutine.ofUnitary_run, QRoutine.ofUnitary_run]
    simp only [Matrix.mul_assoc]
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    flagXorMat_mulVec_embedCtrl_false, Matrix.mulVec_add, control_run_true, control_run_false,
    Matrix.mulVec_add, flagXorMat_mulVec_embedCtrl_true c _ hpres,
    flagXorMat_mulVec_embedCtrl_false_of_bad c _ (goodPart_badPart c (· = true) φ),
    Matrix.mulVec_add, dirtySignMat_mulVec_embedCtrl, dirtySignMat_mulVec_embedCtrl,
    cleanMat_mulVec, ← embedCtrl_add]
  congr 1
  have h1 : goodPart c (· = true) (R.run a *ᵥ goodPart c (· = true) φ)
      = R.run a *ᵥ goodPart c (· = true) φ := by
    have := goodPart_add_badPart c (· = true) (R.run a *ᵥ goodPart c (· = true) φ)
    rwa [hpres, add_zero] at this
  rw [h1, hpres, goodPart_badPart, badPart_badPart]
  abel

/-! ## Routines run regardless of the control bit -/

/-- Lift a routine past the control bit and the parking register. -/
def liftCtrl (X : QRoutine ι σ W) : QRoutine ι σ (CtrlWork ι W) :=
  (X.liftReg (Option ι)).liftReg Bool

@[simp] lemma liftCtrl_len (X : QRoutine ι σ W) : (liftCtrl X).len = X.len := rfl

theorem liftCtrl_run (X : QRoutine ι σ W) (a : ι → σ) (b : Bool) (φ : QBasis ι σ W → ℂ) :
    (liftCtrl X).run a *ᵥ embedCtrl b φ = embedCtrl b (X.run a *ᵥ φ) := by
  rw [liftCtrl, embedCtrl, QRoutine.liftReg_run_embed, QRoutine.liftReg_run_embed]
  rfl

end QuantumQueryComplexity
