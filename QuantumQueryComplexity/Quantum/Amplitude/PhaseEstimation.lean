import QuantumQueryComplexity.Quantum.Amplitude.Fourier
import QuantumQueryComplexity.Quantum.Amplitude.Randomized
set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Operational phase estimation

For a routine `R` and a clock size `M ≥ 1`:

    peRoutine R M = selectPowers R M ; (inverse Fourier transform on the clock register),

`peRoutine_len : (M − 1)·R.len` — the Fourier transform is an input-independent unitary and
costs nothing.  Started on the uniform clock over a vector `ψ`
(`peRoutine_run_uniformClock`), branch `y` of the clock ends with the vector

    ∑_c (F†)_{y c} · (1/√M) · R_a^c ψ,

so the clock outcome `y` has probability `‖·‖²` (`qProb_clockReadout_clockPack`).

For an **eigenvector** `R_a ψ = e(φ)·ψ` (a semantic statement about a supplied vector — the
phase-estimation routine has no input-dependent initial state; an operational algorithm must
prepare `ψ` itself and pay for it):

* `peRoutine_prob_eigen`: `Pr[y] = |peKernel M (φ − y/M)|² · ‖ψ‖²`;
* `peRoutine_prob_eigen_grid`: on a grid phase `φ = y₀/M` the answer `y₀` is deterministic;
* `five_sixths_le_pe_close`: `Pr[circDist(φ − y/M) ≤ 4/M] ≥ 5/6` for a unit eigenvector
  (`three_quarters_le_pe_close` is the compatibility weakening).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix Finset

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-! ## Operators on the clock register -/

/-- An operator on the clock register alone. -/
noncomputable def clockOp (T : ℕ) (A : Matrix (Fin T) (Fin T) ℂ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  liftReg Bool (liftReg (Option ι) (regOp A))

lemma clockOp_mem_unitaryGroup {A : Matrix (Fin T) (Fin T) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin T) ℂ) :
    clockOp (ι := ι) (σ := σ) (W := W) T A
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  liftReg_mem_unitaryGroup (liftReg_mem_unitaryGroup (regOp_mem_unitaryGroup hA))

theorem clockOp_mulVec_embedClock (A : Matrix (Fin T) (Fin T) ℂ) (c : Fin T)
    (ψ : QBasis ι σ W → ℂ) :
    clockOp T A *ᵥ embedClock c false ψ = ∑ c' : Fin T, A c' c • embedClock c' false ψ := by
  rw [clockOp, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    regOp_mulVec_embedReg, embedReg_sum, embedReg_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedReg_smul, embedReg_smul]
  rfl

theorem clockOp_mulVec_clockPack (A : Matrix (Fin T) (Fin T) ℂ)
    (f : Fin T → (QBasis ι σ W → ℂ)) :
    clockOp T A *ᵥ clockPack f = clockPack (fun c' => ∑ c : Fin T, A c' c • f c) := by
  rw [clockPack, Matrix.mulVec_sum,
    Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => clockOp_mulVec_embedClock A c (f c),
    Finset.sum_comm, clockPack]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedClock_sum]
  exact Finset.sum_congr rfl fun c _ => (embedClock_smul c' false _ _).symm

/-- Read the clock register. -/
def clockReadout : QBasis ι σ (ClockWork ι T W) → Fin T := fun p => p.2.2.2.2.1

lemma embedClock_apply (c : Fin T) (b : Bool) (ψ : QBasis ι σ W → ℂ)
    (p : QBasis ι σ (ClockWork ι T W)) :
    embedClock c b ψ p
      = if p.2.2.1 = b ∧ p.2.2.2.1 = none ∧ p.2.2.2.2.1 = c
        then ψ (p.1, p.2.1, p.2.2.2.2.2) else 0 := by
  rw [embedClock, embedCtrl_apply, embedReg_apply]
  by_cases h1 : p.2.2.1 = b ∧ p.2.2.2.1 = none <;> by_cases h2 : p.2.2.2.2.1 = c <;>
    simp [h1, h2]

lemma qNormSq_embedClock (c : Fin T) (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedClock c b ψ) = qNormSq ψ := by
  rw [embedClock, qNormSq_embedCtrl, qNormSq_embedReg]

/-- **The clock outcome law of a packed history**: branch `y` is measured with the squared
norm of its vector. -/
theorem qProb_clockReadout_clockPack (f : Fin T → (QBasis ι σ W → ℂ)) (y : Fin T) :
    qProb clockReadout (clockPack f) y = qNormSq (f y) := by
  rw [qProb_eq_qNormSq_qRestrict, ← qNormSq_embedClock y false (f y)]
  congr 1
  funext p
  rw [qRestrict, clockPack, Finset.sum_apply]
  by_cases hp : clockReadout p = y
  · rw [if_pos hp, Finset.sum_eq_single y]
    · intro c _ hc
      rw [embedClock_apply, if_neg]
      rintro ⟨-, -, h⟩
      exact hc (h.symm.trans hp)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hp, embedClock_apply, if_neg]
    rintro ⟨-, -, h⟩
    exact hp h

/-! ## The phase-estimation routine -/

/-- **Phase estimation**: coherent powers, then the inverse Fourier transform of the clock. -/
noncomputable def peRoutine (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) :
    QRoutine ι σ (ClockWork ι M W) :=
  (selectPowers R M).comp (QRoutine.ofUnitary (clockOp M (fourierMat M)ᴴ)
    (clockOp_mem_unitaryGroup (conjTranspose_mem_qUnitary (fourierMat_mem_unitaryGroup hM))))

/-- **The exact query count: `(M − 1)·R.len`.** -/
@[simp] theorem peRoutine_len (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) :
    (peRoutine R hM).len = (M - 1) * R.len := by
  rw [peRoutine, QRoutine.comp_len, selectPowers_len, QRoutine.ofUnitary_len, Nat.add_zero]

/-- The state of phase estimation on the uniform clock over `ψ`. -/
theorem peRoutine_run_uniformClock (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    (ψ : QBasis ι σ W → ℂ) :
    (peRoutine R hM).run a *ᵥ uniformClock M ψ
      = clockPack (fun y => ∑ c : Fin M, (fourierMat M)ᴴ y c
          • ((((Real.sqrt M : ℝ) : ℂ)⁻¹) • ((R.run a) ^ (c : ℕ) *ᵥ ψ))) := by
  rw [peRoutine, QRoutine.comp_run, QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec,
    selectPowers_run_uniformClock, Matrix.mulVec_smul, clockOp_mulVec_clockPack]
  rw [clockPack, clockPack, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← embedClock_smul, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [smul_comm]

/-! ## Eigenvectors -/

lemma pow_mulVec_eigen {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} {ψ : QBasis ι σ W → ℂ}
    {z : ℂ} (h : U *ᵥ ψ = z • ψ) (c : ℕ) : (U ^ c) *ᵥ ψ = z ^ c • ψ := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

/-- **An eigenvector's clock branches are multiples of it by the kernel.** -/
theorem peRoutine_run_eigen (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} {φ : ℝ} (h : R.run a *ᵥ ψ = cexp1 φ • ψ) :
    (peRoutine R hM).run a *ᵥ uniformClock M ψ
      = clockPack (fun y : Fin M => peKernel M (φ - (y : ℕ) / M) • ψ) := by
  rw [peRoutine_run_uniformClock]
  congr 1
  funext y
  rw [← fourierMat_conjTranspose_mulVec_ramp hM φ y, Matrix.mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_mulVec_eigen h, ← cexp1_nat_mul, smul_smul, smul_smul]
  congr 1
  have : (((Real.sqrt M : ℝ) : ℂ)⁻¹) = (((Real.sqrt M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  ring

/-- **The outcome law on an eigenvector**: `|k(φ − y/M)|²·‖ψ‖²`. -/
theorem peRoutine_prob_eigen (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} {φ : ℝ} (h : R.run a *ᵥ ψ = cexp1 φ • ψ) (y : Fin M) :
    qProb clockReadout ((peRoutine R hM).run a *ᵥ uniformClock M ψ) y
      = Complex.normSq (peKernel M (φ - (y : ℕ) / M)) * qNormSq ψ := by
  rw [peRoutine_run_eigen R hM a h, qProb_clockReadout_clockPack, qNormSq_smul]

/-- **A grid phase is read exactly**: for `φ = y₀/M` the outcome `y₀` has probability
`‖ψ‖²` (no geometric-sum quotient is involved). -/
theorem peRoutine_prob_eigen_grid (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (y₀ : Fin M)
    (h : R.run a *ᵥ ψ = cexp1 (((y₀ : ℕ) : ℝ) / M) • ψ) :
    qProb clockReadout ((peRoutine R hM).run a *ᵥ uniformClock M ψ) y₀ = qNormSq ψ := by
  rw [peRoutine_prob_eigen R hM a h, sub_self]
  have := peKernel_int hM 0
  rw [Int.cast_zero] at this
  rw [this]
  simp

/-- **Concentration**: for a unit eigenvector, the clock outcome is within circular
distance `4/M` of the phase with probability at least `5/6`. -/
theorem five_sixths_le_pe_close (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) {φ : ℝ} (h : R.run a *ᵥ ψ = cexp1 φ • ψ) :
    5 / 6 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then qProb clockReadout ((peRoutine R hM).run a *ᵥ uniformClock M ψ) y else 0 := by
  refine (five_sixths_le_good_mass hM φ).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [peRoutine_prob_eigen R hM a h, hψ, mul_one]

/-- The `3/4` form, kept for compatibility. -/
theorem three_quarters_le_pe_close (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) {φ : ℝ} (h : R.run a *ᵥ ψ = cexp1 φ • ψ) :
    3 / 4 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then qProb clockReadout ((peRoutine R hM).run a *ᵥ uniformClock M ψ) y else 0 :=
  le_trans (by norm_num) (five_sixths_le_pe_close R hM a hψ h)

end QuantumQueryComplexity
