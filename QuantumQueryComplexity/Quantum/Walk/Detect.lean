import QuantumQueryComplexity.Quantum.Walk.TwoReflections
import QuantumQueryComplexity.Quantum.Walk.ClockWeights
import QuantumQueryComplexity.Quantum.Approximation
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The `k`-clock detector on the walk: a `2^{1−k}`-approximate reflection

For a two-reflection walk (`TwoReflections.lean`) with gap `δ`, a clock length `T` with
`4 ≤ T²δ`, and the clock state of `k` summed uniform clocks (`ClockWeights.lean`):

* `WalkFam.avg_pow_K` — the `k`-th power of the uniform average has norm `≤ 2^{-k}` on `K`
  and stays in `K` (iterating `qNormSq_avg_le_of_gap`);
* `WalkFam.isApproxRefl_wDetector` — the weighted detector is a **`2^{1−k}`-approximate
  reflection about `α ⊗ s`** on `{α ⊗ (c s + v) | v ∈ K}`;
* `prepState α` — a free unitary of the clock register carrying `|0⟩` to `α` (Householder), and
  `clockPrep α` on the clocked workspace: `clockPrep α (|0⟩ ⊗ ψ) = α ⊗ ψ`;
* `WalkFam.isApproxRefl_level` — conjugating by `clockPrep` and by a lifted unitary `U` with
  `U (e u) = a u`: **the level operator `U'† P† D P U'` is a `2^{1−k}`-approximate reflection
  about `|0⟩ ⊗ e-combination of r`, on the vectors `|0⟩ ⊗ (e-combination)`** — a subspace
  described by the basis states `e u` with a blank clock, i.e. a support condition.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## Householder: a free unitary carrying `|0⟩` to `α` -/

section Householder

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The reflection about the bisector of `u` and `v`, for `⟨u, v⟩` real and nonnegative. -/
noncomputable def bisectRefl (u v : H → ℂ) (t : ℝ) : Matrix H H ℂ :=
  stateRefl ((((Real.sqrt (2 + 2 * t))⁻¹ : ℝ) : ℂ) • (u + v))

lemma isQState_bisect {u v : H → ℂ} (hu : IsQState u) (hv : IsQState v) {t : ℝ} (ht : 0 ≤ t)
    (huv : qInner u v = (t : ℂ)) :
    IsQState ((((Real.sqrt (2 + 2 * t))⁻¹ : ℝ) : ℂ) • (u + v)) := by
  rw [IsQState, qNormSq_smul, qNormSq_add, hu, hv, huv, Complex.ofReal_re, Complex.normSq_ofReal]
  have hpos : 0 < 2 + 2 * t := by linarith
  rw [← mul_inv, Real.mul_self_sqrt hpos.le, show (1 : ℝ) + 1 + 2 * t = 2 + 2 * t by ring]
  exact inv_mul_cancel₀ hpos.ne'

lemma bisectRefl_mem_unitaryGroup {u v : H → ℂ} (hu : IsQState u) (hv : IsQState v) {t : ℝ}
    (ht : 0 ≤ t) (huv : qInner u v = (t : ℂ)) : bisectRefl u v t ∈ Matrix.unitaryGroup H ℂ :=
  stateRefl_mem_unitaryGroup (isQState_bisect hu hv ht huv)

/-- **It carries `u` to `v`.** -/
theorem bisectRefl_mulVec {u v : H → ℂ} (hu : IsQState u) {t : ℝ} (ht : 0 ≤ t)
    (huv : qInner u v = (t : ℂ)) : bisectRefl u v t *ᵥ u = v := by
  have hvu : qInner v u = (t : ℂ) := by rw [← qInner_conj, huv, Complex.star_def, Complex.conj_ofReal]
  rw [bisectRefl, stateRefl_mulVec, qInner_smul_left, qInner_add_left, qInner_self, hu, hvu,
    smul_smul]
  have hpos : 0 < 2 + 2 * t := by linarith
  have h := Real.mul_self_sqrt hpos.le
  have hne : Real.sqrt (2 + 2 * t) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hc : (2 * (star (((Real.sqrt (2 + 2 * t))⁻¹ : ℝ) : ℂ) * (((1 : ℝ) : ℂ) + (t : ℂ))))
      * (((Real.sqrt (2 + 2 * t))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_ofReal]
    have e : (Real.sqrt (2 + 2 * t))⁻¹ * (Real.sqrt (2 + 2 * t))⁻¹ = (2 + 2 * t)⁻¹ := by
      rw [← mul_inv, h]
    have hr : (2 * ((Real.sqrt (2 + 2 * t))⁻¹ * (1 + t)) * (Real.sqrt (2 + 2 * t))⁻¹ : ℝ) = 1 := by
      calc (2 * ((Real.sqrt (2 + 2 * t))⁻¹ * (1 + t)) * (Real.sqrt (2 + 2 * t))⁻¹ : ℝ)
          = (2 + 2 * t) * ((Real.sqrt (2 + 2 * t))⁻¹ * (Real.sqrt (2 + 2 * t))⁻¹) := by ring
        _ = 1 := by rw [e]; exact mul_inv_cancel₀ hpos.ne'
    exact_mod_cast hr
  rw [hc, one_smul, add_sub_cancel_left]

end Householder

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- The clock state `α` prepared from `|0⟩`, on the clock register alone. -/
noncomputable def prepState {T : ℕ} (α : Fin (T + 1) → ℂ) (t : ℝ) : Matrix (Fin (T + 1)) (Fin (T + 1)) ℂ :=
  bisectRefl (qBasis 0) α t

/-- The clock-register preparation on the clocked workspace. -/
noncomputable def clockPrep {T : ℕ} (α : Fin (T + 1) → ℂ) (t : ℝ) :
    Matrix (QBasis ι σ (ClockWork ι (T + 1) W)) (QBasis ι σ (ClockWork ι (T + 1) W)) ℂ :=
  liftReg Bool (liftReg (Option ι) (regOp (prepState α t)))

lemma clockPrep_mem_unitaryGroup {α : Fin (T + 1) → ℂ} (hα : IsQState α) {t : ℝ} (ht : 0 ≤ t)
    (h0 : qInner (qBasis 0) α = (t : ℂ)) :
    clockPrep (ι := ι) (σ := σ) (W := W) α t ∈ Matrix.unitaryGroup _ ℂ :=
  liftReg_mem_unitaryGroup (liftReg_mem_unitaryGroup (regOp_mem_unitaryGroup
    (bisectRefl_mem_unitaryGroup (isQState_qBasis 0) hα ht h0)))

lemma regOp_mulVec_embedReg_col {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℂ)
    (v : V) (ψ : QBasis ι σ W → ℂ) :
    regOp A *ᵥ embedReg v ψ = ∑ v' : V, (A *ᵥ qBasis v) v' • embedReg v' ψ := by
  rw [regOp_mulVec_embedReg]
  refine Finset.sum_congr rfl fun v' _ => ?_
  congr 1
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single v]
  · rw [qBasis, Pi.single_eq_same, mul_one]
  · intro b _ hb; rw [qBasis, Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`clockPrep α (|0⟩ ⊗ ψ) = α ⊗ ψ`.** -/
theorem clockPrep_mulVec_embedClock_zero {α : Fin (T + 1) → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (h0 : qInner (qBasis 0) α = (t : ℂ)) (ψ : QBasis ι σ W → ℂ) :
    clockPrep α t *ᵥ embedClock 0 false ψ = wClock α ψ := by
  rw [clockPrep, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    regOp_mulVec_embedReg_col, prepState, bisectRefl_mulVec (isQState_qBasis 0) ht h0,
    embedReg_sum, embedReg_sum, wClock, clockPack]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [embedReg_smul, embedReg_smul, embedClock_smul]
  rfl

/-! ## `wClock` is linear and isometric -/

lemma wClock_add (α : Fin T → ℂ) (ψ φ : QBasis ι σ W → ℂ) :
    wClock α (ψ + φ) = wClock α ψ + wClock α φ := by
  simp only [wClock, clockPack, smul_add, embedClock_add, Finset.sum_add_distrib]

lemma wClock_smul (α : Fin T → ℂ) (c : ℂ) (ψ : QBasis ι σ W → ℂ) :
    wClock α (c • ψ) = c • wClock α ψ := by
  simp only [wClock, clockPack, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_comm, embedClock_smul]

lemma wClock_sub (α : Fin T → ℂ) (ψ φ : QBasis ι σ W → ℂ) :
    wClock α (ψ - φ) = wClock α ψ - wClock α φ := by
  rw [sub_eq_add_neg, wClock_add, ← neg_one_smul ℂ φ, wClock_smul, neg_one_smul, sub_eq_add_neg]

lemma qInner_wClock (α : Fin T → ℂ) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (wClock α ψ) (wClock α φ) = ((qNormSq α : ℝ) : ℂ) * qInner ψ φ := by
  rw [wClock, wClock, qInner_clockPack, qNormSq_def]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [qInner_smul_left, qInner_smul_right, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

lemma qNorm_wClock {α : Fin T → ℂ} (hα : IsQState α) (ψ : QBasis ι σ W → ℂ) :
    qNorm (wClock α ψ) = qNorm ψ := by
  rw [qNorm, qNormSq_wClock, hα, one_mul, qNorm]

/-! ## The average on `K` -/

namespace WalkFam

variable {V : Type} [Fintype V] [DecidableEq V] {a b : V → (QBasis ι σ W → ℂ)}
  {D : Matrix V V ℂ} {r : V → ℂ} {δ : ℝ} (h : WalkFam a b D r δ)

include h

lemma avgOp_mulVec (T : ℕ) (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (v : QBasis ι σ W → ℂ) :
    avgOp T U *ᵥ v = (T : ℂ)⁻¹ • ∑ c : Fin T, (U ^ (c : ℕ)) *ᵥ v := by
  rw [avgOp, Matrix.smul_mulVec, Matrix.sum_mulVec,
    ← Fin.sum_univ_eq_sum_range (fun c => (U ^ c) *ᵥ v) T]

/-- One average: norm down by `1/(T²δ)`, staying in `K`. -/
lemma avg_K {T : ℕ} (hT : 4 ≤ (T : ℝ) ^ 2 * δ) {v : QBasis ι σ W → ℂ} (hv : v ∈ h.K) :
    avgOp T (walkOp a b) *ᵥ v ∈ h.K
    ∧ qNormSq (avgOp T (walkOp a b) *ᵥ v) ≤ (1 / 4) * qNormSq v := by
  have hg := qNormSq_avg_le_of_gap h.walkOp_mem_unitaryGroup h.K (fun y hy => h.walkOp_mem_K hy)
    (γ := 2 * Real.sqrt δ) (fun y hy => by
      have := h.gap hy
      rw [mul_pow, Real.sq_sqrt h.δ_pos.le]; linarith) T hv
  rw [← h.avgOp_mulVec] at hg
  refine ⟨hg.2, ?_⟩
  have h1 := hg.1
  rw [mul_pow, Real.sq_sqrt h.δ_pos.le] at h1
  have hnn := qNormSq_nonneg (avgOp T (walkOp a b) *ᵥ v)
  have : 4 * ((T : ℝ) ^ 2 * δ) * qNormSq (avgOp T (walkOp a b) *ᵥ v)
      = (T : ℝ) ^ 2 * (2 ^ 2 * δ) * qNormSq (avgOp T (walkOp a b) *ᵥ v) := by ring
  nlinarith

/-- **The `k`-th power of the average on `K`.** -/
theorem avg_pow_K {T : ℕ} (hT : 4 ≤ (T : ℝ) ^ 2 * δ) (k : ℕ) {v : QBasis ι σ W → ℂ}
    (hv : v ∈ h.K) :
    (avgOp T (walkOp a b)) ^ k *ᵥ v ∈ h.K
    ∧ qNormSq ((avgOp T (walkOp a b)) ^ k *ᵥ v) ≤ (1 / 4) ^ k * qNormSq v := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_mul]; exact ⟨hv, le_rfl⟩
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      obtain ⟨h1, h2⟩ := h.avg_K hT ih.1
      refine ⟨h1, h2.trans ?_⟩
      rw [pow_succ]
      nlinarith [ih.2]

/-! ## The detector is an approximate reflection on `span s ⊕ K` -/

variable {walkR : QRoutine ι σ W} {x : ι → σ} (hW : walkR.run x = walkOp a b)

include hW

/-- The deviation on `α ⊗ v`, `v ∈ K`. -/
theorem qNorm_wDetector_add_K {T : ℕ} (hT0 : 0 < T) (hT : 4 ≤ (T : ℝ) ^ 2 * δ) (k : ℕ)
    {v : QBasis ι σ W → ℂ} (hv : v ∈ h.K) :
    qNorm ((wDetector walkR (k * (T - 1) + 1) (isQState_kClock hT0 k)).run x
        *ᵥ wClock (kClock T k) v + wClock (kClock T k) v)
      ≤ 2 * (1 / 2) ^ k * qNorm v := by
  refine qNorm_le_of_qNormSq_le (by have := qNorm_nonneg v; positivity) ?_
  rw [qNormSq_wDetector_add, hW, wAvg_kClock hT0]
  have := (h.avg_pow_K hT k hv).2
  rw [mul_pow, mul_pow, qNorm_sq, ← pow_mul, show (1 / 2 : ℝ) ^ (k * 2) = (1 / 4) ^ k by
    rw [mul_comm, pow_mul]; norm_num]
  nlinarith

/-- **The detector is a `2^{1−k}`-approximate reflection about `α ⊗ s`.** -/
theorem isApproxRefl_wDetector {T : ℕ} (hT0 : 0 < T) (hT : 4 ≤ (T : ℝ) ^ 2 * δ) (k : ℕ) :
    IsApproxRefl ((wDetector walkR (k * (T - 1) + 1) (isQState_kClock hT0 k)).run x)
      (wClock (kClock T k) h.s)
      {w | ∃ (c : ℂ) (v : QBasis ι σ W → ℂ), v ∈ h.K ∧ w = wClock (kClock T k) (c • h.s + v)}
      (2 * (1 / 2) ^ k) where
  fix := wDetector_run_mulVec_wClock_of_fixed _ _ _ x (by rw [hW]; exact h.walkOp_s)
  near := by
    rintro w ⟨c, v, hv, rfl⟩
    have hα := isQState_kClock hT0 k
    have hfix := wDetector_run_mulVec_wClock_of_fixed walkR (k * (T - 1) + 1) hα x
      (ψ := h.s) (by rw [hW]; exact h.walkOp_s)
    have hsv : qInner (wClock (kClock T k) h.s) (wClock (kClock T k) v) = 0 := by
      rw [qInner_wClock, h.qInner_s_K hv, mul_zero]
    have hss : qInner (wClock (kClock T k) h.s) (wClock (kClock T k) h.s) = 1 := by
      rw [qInner_wClock, hα, qInner_self, h.s_unit]; simp
    rw [wClock_add, wClock_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hfix, stateRefl_mulVec,
      qInner_add_right, qInner_smul_right, hss, hsv]
    have e1 : c • wClock (kClock T k) h.s
          + (wDetector walkR (k * (T - 1) + 1) hα).run x *ᵥ wClock (kClock T k) v
          - ((2 * (c * 1 + 0)) • wClock (kClock T k) h.s
            - (c • wClock (kClock T k) h.s + wClock (kClock T k) v))
        = (wDetector walkR (k * (T - 1) + 1) hα).run x *ᵥ wClock (kClock T k) v
            + wClock (kClock T k) v := by
      module
    have e2 : c • wClock (kClock T k) h.s + wClock (kClock T k) v
          - (c * 1 + 0) • wClock (kClock T k) h.s = wClock (kClock T k) v := by module
    rw [e1, e2, qNorm_wClock hα]
    exact h.qNorm_wDetector_add_K hW hT0 hT k hv

end WalkFam

end QuantumQueryComplexity
