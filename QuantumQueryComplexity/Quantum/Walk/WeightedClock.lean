import QuantumQueryComplexity.Quantum.ClockDetector
import QuantumQueryComplexity.Quantum.Amplitude.Geometry
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# A detector with a weighted clock

`clockPhaseRefl` reflects about the *uniform* clock; its deviation from `−1` is twice the
uniform average of the powers, of size `2/(TΔ)`.  For a reflection of precision `2^{-k}` one
wants `k` clocks and the joint "all clocks read zero" test, whose deviation is the `k`-th
power of that average.  Since the controlled powers of the `k` clocks commute and compose to
`U^{c₁+⋯+c_k}`, the same operator is obtained from **one** clock register holding the sum,
prepared in the *non-uniform* state `α` whose weights `|α_m|²` are the distribution of
`c₁+⋯+c_k`: no nested workspaces, and the cost is that of `selectPowers` on the larger clock.

This file is the clock half, for an arbitrary unit clock state `α : Fin T → ℂ`:

* `wClock α ψ` — the clock in state `α`, the system in `ψ`; `qNormSq_wClock`;
* `wDetector R T α = SELECT† · (2|α⟩⟨α| − 1) · SELECT`, `wDetector_len = 2(T−1)·R.len`;
* `wDetector_run_mulVec_wClock_add` — **the deviation identity**:
  `D (α ⊗ ψ) + α ⊗ ψ = 2·SELECT† (α ⊗ ∑_c |α_c|²·U^c ψ)`;
* `qNormSq_wDetector_add` — hence `‖D(α⊗ψ) + α⊗ψ‖² = 4·‖∑_c |α_c|² U^c ψ‖²`;
* `wDetector_run_mulVec_wClock_of_fixed` — on a fixed vector of `U` it is exactly the identity.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- The clock in the state `α`, the system in `ψ`. -/
noncomputable def wClock (α : Fin T → ℂ) (ψ : QBasis ι σ W → ℂ) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  clockPack fun c => α c • ψ

theorem qNormSq_wClock (α : Fin T → ℂ) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (wClock α ψ) = qNormSq α * qNormSq ψ := by
  rw [wClock, qNormSq_clockPack, qNormSq_def, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => qNormSq_smul _ _

/-- The projector of the clock register onto `α`. -/
noncomputable def clockStateProj (α : Fin T → ℂ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  liftReg Bool (liftReg (Option ι) (regOp (ketbra α)))

theorem isQProjector_clockStateProj {α : Fin T → ℂ} (hα : IsQState α) :
    IsQProjector (clockStateProj (ι := ι) (σ := σ) (W := W) α) :=
  isQProjector_liftReg (isQProjector_liftReg (isQProjector_regOp (isQProjector_ketbra hα)))

lemma ketbra_apply (α : Fin T → ℂ) (c' c : Fin T) : ketbra α c' c = α c' * star (α c) := by
  rw [ketbra, Matrix.vecMulVec_apply]
  rfl

theorem clockStateProj_mulVec_embedClock (α : Fin T → ℂ) (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    clockStateProj α *ᵥ embedClock c false ψ
      = ∑ c' : Fin T, (α c' * star (α c)) • embedClock c' false ψ := by
  rw [clockStateProj, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    regOp_mulVec_embedReg, embedReg_sum, embedReg_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedReg_smul, embedReg_smul, ketbra_apply]
  rfl

/-- **The projector returns the `α`-weighted combination, in the clock state `α`.** -/
theorem clockStateProj_mulVec_clockPack (α : Fin T → ℂ) (f : Fin T → (QBasis ι σ W → ℂ)) :
    clockStateProj α *ᵥ clockPack f = wClock α (∑ c : Fin T, star (α c) • f c) := by
  rw [clockPack, Matrix.mulVec_sum,
    Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
      clockStateProj_mulVec_embedClock α c (f c),
    Finset.sum_comm, wClock, clockPack]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.smul_sum, embedClock_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul, embedClock_smul]

/-- The reflection about the clock state `α`. -/
noncomputable def clockStateRefl (α : Fin T → ℂ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl (clockStateProj α)

theorem clockStateRefl_mem_unitaryGroup {α : Fin T → ℂ} (hα : IsQState α) :
    clockStateRefl (ι := ι) (σ := σ) (W := W) α
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_clockStateProj hα)

/-- **The weighted detector**: `SELECT† · (2|α⟩⟨α| − 1) · SELECT`. -/
noncomputable def wDetector (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ} (hα : IsQState α) :
    QRoutine ι σ (ClockWork ι T W) :=
  (selectPowers R T).conjFixed (clockStateRefl α) (clockStateRefl_mem_unitaryGroup hα)

@[simp] theorem wDetector_len (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ} (hα : IsQState α) :
    (wDetector R T hα).len = 2 * ((T - 1) * R.len) := by
  rw [wDetector, QRoutine.conjFixed_len, selectPowers_len]

theorem wDetector_run (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ} (hα : IsQState α)
    (a : ι → σ) :
    (wDetector R T hα).run a
      = ((selectPowers R T).run a)ᴴ * (clockStateRefl α * (selectPowers R T).run a) :=
  QRoutine.conjFixed_run _ _ _ _

/-- The deviation from `−1` is twice `SELECT† P SELECT`. -/
theorem wDetector_run_mulVec_add (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ}
    (hα : IsQState α) (a : ι → σ) (u : QBasis ι σ (ClockWork ι T W) → ℂ) :
    (wDetector R T hα).run a *ᵥ u + u
      = (2 : ℂ) • (((selectPowers R T).run a)ᴴ
          *ᵥ (clockStateProj α *ᵥ ((selectPowers R T).run a *ᵥ u))) := by
  have hSS : ((selectPowers R T).run a)ᴴ *ᵥ ((selectPowers R T).run a *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [wDetector_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, clockStateRefl,
    qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, hSS]
  module

/-- The `|α|²`-weighted average of the powers. -/
noncomputable def wAvg (α : Fin T → ℂ) (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) : QBasis ι σ W → ℂ :=
  ∑ c : Fin T, ((Complex.normSq (α c) : ℝ) : ℂ) • ((U ^ (c : ℕ)) *ᵥ ψ)

/-- **The deviation identity.** -/
theorem wDetector_run_mulVec_wClock_add (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ}
    (hα : IsQState α) (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    (wDetector R T hα).run a *ᵥ wClock α ψ + wClock α ψ
      = (2 : ℂ) • (((selectPowers R T).run a)ᴴ *ᵥ wClock α (wAvg α (R.run a) ψ)) := by
  rw [wDetector_run_mulVec_add, wClock, selectPowers_run_clockPack,
    clockStateProj_mulVec_clockPack]
  congr 3
  rw [wAvg]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, smul_smul, Complex.normSq_eq_conj_mul_self]
  rfl

/-- **The size of the deviation is twice the weighted average.** -/
theorem qNormSq_wDetector_add (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ} (hα : IsQState α)
    (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    qNormSq ((wDetector R T hα).run a *ᵥ wClock α ψ + wClock α ψ)
      = 4 * qNormSq (wAvg α (R.run a) ψ) := by
  rw [wDetector_run_mulVec_wClock_add, qNormSq_smul,
    qNormSq_mulVec (conjTranspose_mem_unitaryGroup ((selectPowers R T).run_mem_unitaryGroup a)),
    qNormSq_wClock, hα, one_mul]
  norm_num [Complex.normSq_apply]

/-- **Completeness**: on a fixed vector of `U` the detector is exactly the identity. -/
theorem wDetector_run_mulVec_wClock_of_fixed (R : QRoutine ι σ W) (T : ℕ) {α : Fin T → ℂ}
    (hα : IsQState α) (a : ι → σ) {ψ : QBasis ι σ W → ℂ} (hfix : R.run a *ᵥ ψ = ψ) :
    (wDetector R T hα).run a *ᵥ wClock α ψ = wClock α ψ := by
  have hpow : ∀ n : ℕ, (R.run a) ^ n *ᵥ ψ = ψ := fun n => pow_mulVec_eq_self hfix n
  have havg : wAvg α (R.run a) ψ = ψ := by
    rw [wAvg]
    simp only [hpow]
    rw [← Finset.sum_smul]
    have : (∑ c : Fin T, ((Complex.normSq (α c) : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum]
      have h := hα
      rw [IsQState, qNormSq_def] at h
      rw [h, Complex.ofReal_one]
    rw [this, one_smul]
  have hS : (selectPowers R T).run a *ᵥ wClock α ψ = wClock α ψ := by
    rw [wClock, selectPowers_run_clockPack]
    congr 1
    funext c
    rw [Matrix.mulVec_smul, hpow]
  have hSH : ((selectPowers R T).run a)ᴴ *ᵥ wClock α ψ = wClock α ψ := by
    nth_rewrite 1 [← hS]
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  have h := wDetector_run_mulVec_wClock_add R T hα a ψ
  rw [havg, hSH] at h
  have h2 : (wDetector R T hα).run a *ᵥ wClock α ψ = (2 : ℂ) • wClock α ψ - wClock α ψ :=
    eq_sub_of_add_eq h
  rw [h2, two_smul, add_sub_cancel_right]

end QuantumQueryComplexity
