import QuantumQueryComplexity.Quantum.RobustSearch.Defs
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Robust search: the exact recurrence of one step

For a level `L` and the input `a` write `u i = Pr[flag ∧ index = i]` and `p = Pr[flag] = ∑ u i`.
One recursion step with the test bank `K` gives, **exactly**,

    (L.next K i₀).u a i = (3 − 4·p)² · u i · Pr[test of i accepts].

The three factors are: the single amplification step (`ampA p 1 = 3 − 4p`, from the
division-free geometry, valid at `p = 0` and `p = 1` alike); the old accepted component of
index `i`; and the fresh test, which sees only the index — it is started by an
index-controlled free unitary on a blank bank, whatever the old registers are entangled with.

The marked / unmarked classification of the analysis is obtained by summing this identity over
the marked, respectively unmarked, indices (`Progress.lean`): the true predicate occurs in no
gate and no readout.

`alg_prob_some`, `alg_prob_none` read the level as an algorithm with output `Option I`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {I : Type} [Fintype I] [DecidableEq I]

lemma ampA_one (p : ℝ) : ampA p 1 = 3 - 4 * p := by
  rw [ampA_succ, ampA_zero, ampB_zero]; ring

/-! ## A sum of index-restricted product states, read jointly -/

section Joint

variable {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]

lemma qRestrict_sum_prodState (c : QBasis ι σ W₁ → I) (r₁ : QBasis ι σ W₁ → Bool)
    (r₂ : QBasis ι σ W₂ → Bool) (χ : Option ι × Option σ → ℂ) (θ : QBasis ι σ W₁ → ℂ)
    (w : I → QBasis ι σ W₂ → ℂ) (i : I) :
    qRestrict (fun p : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) =>
        (r₁ p.2.2.1 && r₂ p.2.2.2, c p.2.2.1)) (true, i)
        (∑ i', prodState χ (qRestrict c i' θ) (w i'))
      = prodState χ (qRestrict (fun y => (r₁ y, c y)) (true, i) θ) (qRestrict r₂ true (w i)) := by
  funext q
  obtain ⟨k, t, y, b⟩ := q
  have hsum : (∑ i', prodState χ (qRestrict c i' θ) (w i')) (k, t, y, b)
      = χ (k, t) * θ y * w (c y) b := by
    rw [Finset.sum_apply, Finset.sum_eq_single (c y)]
    · show χ (k, t) * qRestrict c (c y) θ y * w (c y) b = _
      rw [qRestrict, if_pos rfl]
    · intro i' _ hi'
      show χ (k, t) * qRestrict c i' θ y * w i' b = 0
      rw [qRestrict, if_neg (Ne.symm hi'), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  show (if (r₁ y && r₂ b, c y) = (true, i) then _ else 0)
    = χ (k, t) * qRestrict (fun y => (r₁ y, c y)) (true, i) θ y * qRestrict r₂ true (w i) b
  rw [hsum]
  simp only [qRestrict, Prod.mk.injEq, Bool.and_eq_true]
  by_cases h1 : r₁ y = true <;> by_cases h2 : r₂ b = true <;> by_cases h3 : c y = i <;>
    simp [h1, h2, h3]

end Joint

namespace RSLevel

variable (L : RSLevel ι σ I)

lemma goodProb_acc (a : ι → σ) : goodProb L.acc (· = true) (L.state a) = L.p a := by
  rw [goodProb, p]
  congr 1

/-- **The amplified state**: `(3 − 4p)·accepted + (1 − 4p)·rejected`. -/
theorem ampRoutine_state (a : ι → σ) :
    (L.setup.ampRoutine 1).run a *ᵥ L.init
      = ((ampA (L.p a) 1 : ℝ) : ℂ) • goodPart L.acc (· = true) (L.state a)
        + ((ampB (L.p a) 1 : ℝ) : ℂ) • badPart L.acc (· = true) (L.state a) := by
  have h := L.setup.ampRoutine_run_mulVec_of_split a
    (groverSplit_parts L.acc (· = true) (L.isQState_state a))
    (by rw [show L.setup.mark = signMarker L.acc from rfl, signMarker_run, phaseFlip_goodPart])
    (by rw [show L.setup.mark = signMarker L.acc from rfl, signMarker_run, phaseFlip_badPart]) 1
  rw [qNormSq_goodPart, show L.setup.prepared a = L.state a from rfl, L.goodProb_acc] at h
  exact h

/-- On the accepted component of index `i` the amplified state is `3 − 4p` times the old. -/
lemma qRestrict_flagIdx_amp (a : ι → σ) (i : I) :
    qRestrict L.flagIdx (true, i) ((L.setup.ampRoutine 1).run a *ᵥ L.init)
      = ((3 - 4 * L.p a : ℝ) : ℂ) • qRestrict L.flagIdx (true, i) (L.state a) := by
  rw [L.ampRoutine_state, ampA_one]
  funext y
  simp only [qRestrict, flagIdx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, goodPart_apply,
    badPart_apply, Prod.mk.injEq]
  by_cases h1 : L.acc y = true <;> by_cases h2 : L.idx y = i <;> simp [h1, h2]

/-- **The state of the next level.** -/
theorem nextA_run (K : TestBank ι σ I) (i₀ : I) (a : ι → σ) :
    (L.nextA K i₀).run a *ᵥ prodState blankReg L.init (K.blank i₀)
      = ∑ i, prodState blankReg
          (qRestrict L.idx i ((L.setup.ampRoutine 1).run a *ᵥ L.init))
          (embedReg false (K.F.run a *ᵥ K.β i)) := by
  have hA : (L.nextA K i₀).run a
      = (pairRoutine (ι := ι) (σ := σ) (QRoutine.identity (W := L.Y)) (K.F.liftReg Bool)).run a
        * (bankCtrl L.idx (K.prepMat i₀)
          * (pairRoutine (L.setup.ampRoutine 1) (QRoutine.identity (W := Bool × K.B))).run a) := by
    rw [nextA, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run, Matrix.mul_assoc]
  rw [hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pairRoutine_run_prodState,
    QRoutine.identity_run, Matrix.one_mulVec, bankCtrl_mulVec_prodState, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairRoutine_run_prodState, QRoutine.identity_run, Matrix.one_mulVec,
    K.prepMat_mulVec_blank, TestBank.start, QRoutine.liftReg_run_embed]

/-- **The exact recurrence.** -/
theorem next_u (K : TestBank ι σ I) (i₀ : I) (a : ι → σ) (i : I) :
    (L.next K i₀).u a i = (3 - 4 * L.p a) ^ 2 * L.u a i * K.accProb a i := by
  show qProb (fun p : QBasis ι σ (QBasis ι σ L.Y × QBasis ι σ (Bool × K.B)) =>
      (L.acc p.2.2.1 && stripReadout (V := Bool) K.t p.2.2.2, L.idx p.2.2.1))
      ((L.nextA K i₀).run a *ᵥ prodState blankReg L.init (K.blank i₀)) (true, i) = _
  rw [qProb_eq_qNormSq_qRestrict, L.nextA_run, qRestrict_sum_prodState,
    qNormSq_prodState, sum_normSq_blankReg, one_mul,
    show (fun y => (L.acc y, L.idx y)) = L.flagIdx from rfl, L.qRestrict_flagIdx_amp,
    qNormSq_smul, qRestrict_stripReadout_embedReg, qNormSq_embedReg,
    ← qProb_eq_qNormSq_qRestrict, ← qProb_eq_qNormSq_qRestrict, Complex.normSq_ofReal]
  rw [u, TestBank.accProb]
  ring

/-- **`Pr[flag] = ∑ᵢ Pr[flag ∧ index = i]`.** -/
theorem p_eq_sum (a : ι → σ) : L.p a = ∑ i, L.u a i := by
  have h := qProb_comp L.flagIdx Prod.fst (L.state a) true
  rw [show (Prod.fst ∘ L.flagIdx) = L.acc from rfl] at h
  rw [p, h, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [u]

lemma p_nonneg (a : ι → σ) : 0 ≤ L.p a := qProb_nonneg _ _ _

lemma p_le_one (a : ι → σ) : L.p a ≤ 1 := qProb_le_one (L.isQState_state a) _ _

/-! ## The level as an algorithm -/

theorem alg_prob_some (a : ι → σ) (i : I) : L.alg.prob a L.A.len (some i) = L.u a i := by
  rw [QAlg.prob, alg, QRoutine.toAlg_state_len]
  show qProb L.out (L.state a) (some i) = qProb L.flagIdx (L.state a) (true, i)
  rw [qProb, qProb]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : L.out y = some i ↔ L.flagIdx y = (true, i) := by
    rw [out, flagIdx, Prod.mk.injEq]
    by_cases h : L.acc y = true <;> simp [h]
  by_cases h : L.out y = some i
  · rw [if_pos h, if_pos (this.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

theorem alg_prob_none (a : ι → σ) : L.alg.prob a L.A.len none = 1 - L.p a := by
  rw [QAlg.prob, alg, QRoutine.toAlg_state_len]
  have hsum := sum_qProb_eq_one (L.isQState_state a) L.acc
  rw [Fintype.sum_bool] at hsum
  have : qProb L.out (L.state a) none = qProb L.acc (L.state a) false := by
    rw [qProb, qProb]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : L.out y = none ↔ L.acc y = false := by
      rw [out]; by_cases h : L.acc y = true <;> simp [h]
    by_cases h : L.out y = none
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  show qProb L.out (L.state a) none = 1 - L.p a
  rw [this, p]
  linarith

end RSLevel

end QuantumQueryComplexity
