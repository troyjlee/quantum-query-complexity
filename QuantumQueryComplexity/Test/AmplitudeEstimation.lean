import QuantumQueryComplexity.Quantum.Amplitude.Counting
import QuantumQueryComplexity.Quantum.Amplitude.Verifier

set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: amplitude estimation and counting

1. Exact lengths: phase estimation `(M−1)·R.len`; amplitude estimation `S + (M−1)(2S+C)`;
   counting `2(M−1)` native queries.
2. Phase estimation on a supplied eigenvector: the outcome law, exact grid phases, the
   concentration `≥ 3/4` within circular distance `4/M`; the Fourier matrix is unitary with
   the stated signs.
3. **Wraparound**: circular distance is `1`-periodic; the grid point `(M−1)/M` is at
   circular distance `1/M` from the phase `0`.
4. Amplitude estimation: the mixture law for every `0 ≤ p ≤ 1`; accuracy
   `8π√(p(1−p))/M + 16π²/M²` with probability `≥ 3/4`; additive `η` for `M ≥ 8π/η` and the
   budget `≤ 18π(S+C)/η`; the decoder is a finite label with values in `[0,1]`.
5. Endpoints: `p = 0` gives estimate `0` surely; `p = 1` gives estimate `1` surely **for an
   even clock**.
6. **The phase convention**: at `p = 1/4`, `M = 6`, the clock reads `1` or `5`, each with
   probability `1/2`, and both decode to exactly `1/4`.  With `−G` in place of `G` the
   eigenphases would move by `1/2` and the labels `4`, `2` would decode to `3/4`.
7. Counting: the substitution `p = t/n`, the error `8π√(t(n−t))/M + 16π²n/M²`, the additive
   `η·n` corollary.  The undiluted predicate of `searchSetup` is used.
8. **Success `5/6`**: the same six statements — kernel mass, phase
   estimation, amplitude estimation (fine and additive), counting (fine and additive) — with
   `5/6` in place of `3/4`, on the actual `QAlg` probabilities and at unchanged cost.  The
   `3/4` pins above are retained; they are now weakenings.
9. **Estimation through the verifier constructor**: from `IsCoherentVerifier` alone, the
   logical success probability is estimated with probability `≥ 5/6` at cost
   `S + (M−1)(2S+2V) ≤ 18π(S+2V)/η`.
-/

namespace QuantumQueryComplexity
namespace AmplitudeEstimationAcceptance

open Finset

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-! ## 1–2. Phase estimation -/

theorem acceptance_pe_len (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) :
    (peRoutine R hM).len = (M - 1) * R.len := peRoutine_len R hM

theorem acceptance_fourier {M : ℕ} (hM : 0 < M) :
    fourierMat M ∈ Matrix.unitaryGroup (Fin M) ℂ
    ∧ (∀ y c : Fin M, fourierMat M y c
        = (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 ((y : ℕ) * (c : ℕ) / M))
    ∧ ∀ y c : Fin M, (fourierMat M).conjTranspose y c
        = (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * cexp1 (-((c : ℕ) * (y : ℕ) / M)) :=
  ⟨fourierMat_mem_unitaryGroup hM, fourierMat_apply M, fourierMat_conjTranspose_apply M⟩

theorem acceptance_pe_eigen (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) {φ : ℝ}
    (h : Matrix.mulVec (R.run a) ψ = cexp1 φ • ψ) :
    (∀ y : Fin M, qProb clockReadout (Matrix.mulVec ((peRoutine R hM).run a) (uniformClock M ψ)) y
        = Complex.normSq (peKernel M (φ - (y : ℕ) / M)))
    ∧ 3 / 4 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
        then qProb clockReadout (Matrix.mulVec ((peRoutine R hM).run a) (uniformClock M ψ)) y
        else 0 :=
  ⟨fun y => by rw [peRoutine_prob_eigen R hM a h, hψ, mul_one],
   three_quarters_le_pe_close R hM a hψ h⟩

/-- An exact grid phase is read deterministically. -/
theorem acceptance_pe_grid (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) (y₀ : Fin M)
    (h : Matrix.mulVec (R.run a) ψ = cexp1 (((y₀ : ℕ) : ℝ) / M) • ψ) :
    qProb clockReadout (Matrix.mulVec ((peRoutine R hM).run a) (uniformClock M ψ)) y₀ = 1 := by
  rw [peRoutine_prob_eigen_grid R hM a y₀ h, hψ]

/-! ## 3. Wraparound -/

/-- Circular distance is `1`-periodic. -/
example (δ : ℝ) (n : ℤ) : circDist (δ + n) = circDist δ := by
  rw [circDist, circDist, round_add_intCast]
  push_cast
  ring_nf

/-- The last grid point is at circular distance `1/M` from the phase `0`. -/
example {M : ℕ} (hM : 3 ≤ M) : circDist (0 - ((M - 1 : ℕ) : ℝ) / M) = 1 / (M : ℝ) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hrw : 0 - ((M - 1 : ℕ) : ℝ) / M = 1 / (M : ℝ) + ((-1 : ℤ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  have hsmall : (1 : ℝ) / M ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
  have hr : round ((1 : ℝ) / M) = 0 := by
    rw [round_eq_zero_iff]
    constructor
    · have : (0 : ℝ) ≤ 1 / M := by positivity
      linarith
    · linarith
  rw [hrw, circDist, round_add_intCast, hr]
  push_cast
  rw [show (1 : ℝ) / M + -1 - -1 = 1 / M by ring, abs_of_nonneg (by positivity)]

/-! ## 4. Amplitude estimation -/

section AE

variable (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

theorem acceptance_ae_len {M : ℕ} (hM : 0 < M) :
    (P.aeRoutine hM).len = P.prep.len + (M - 1) * (2 * P.prep.len + P.mark.len) :=
  P.aeRoutine_len hM

theorem acceptance_ae_law (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) (y : Fin M) :
    (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y
      = (Complex.normSq (peKernel M
            (groverAngle (P.succProb read Good x) / Real.pi - (y : ℕ) / M))
          + Complex.normSq (peKernel M
            (-(groverAngle (P.succProb read Good x) / Real.pi) - (y : ℕ) / M))) / 2 :=
  P.aeAlg_prob hP x hM y

theorem acceptance_ae_accuracy (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) :
    3 / 4 ≤ ∑ y : Fin M,
      if |aeEstimate M y - P.succProb read Good x|
          ≤ 8 * Real.pi * Real.sqrt (P.succProb read Good x * (1 - P.succProb read Good x)) / M
            + 16 * Real.pi ^ 2 / (M : ℝ) ^ 2
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 :=
  P.three_quarters_le_ae_accurate hP x hM

theorem acceptance_ae_additive (hP : P.Marks read Good) (x : X) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) :
    (3 / 4 ≤ ∑ y : Fin (AmpSetup.aeClock η),
        if |aeEstimate (AmpSetup.aeClock η) y - P.succProb read Good x| ≤ η
        then (P.aeAlg (AmpSetup.aeClock_pos hη)).prob (read x)
          (P.aeRoutine (AmpSetup.aeClock_pos hη)).len y else 0)
    ∧ ((P.aeRoutine (AmpSetup.aeClock_pos hη)).len : ℝ)
        ≤ 18 * Real.pi * ((P.prep.len : ℝ) + P.mark.len) / η :=
  ⟨P.ae_additive hP x (AmpSetup.aeClock_pos hη) hη hη1 (AmpSetup.le_aeClock η),
   P.aeRoutine_len_le_real hη hη1⟩

/-- The decoder takes values in `[0, 1]`; the output type is the finite label `Fin M`. -/
theorem acceptance_decoder (M : ℕ) (y : Fin M) : 0 ≤ aeEstimate M y ∧ aeEstimate M y ≤ 1 :=
  ⟨aeEstimate_nonneg M y, aeEstimate_le_one M y⟩

/-! ## 5. Endpoints -/

theorem acceptance_ae_zero (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M)
    (h0 : P.succProb read Good x = 0) :
    (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len ⟨0, hM⟩ = 1
      ∧ aeEstimate M ⟨0, hM⟩ = 0 :=
  ⟨P.aeAlg_prob_zero_of_succProb_eq_zero hP x hM h0, AmpSetup.aeEstimate_zero hM⟩

/-- Only for an even clock `M = 2h`. -/
theorem acceptance_ae_one (hP : P.Marks read Good) (x : X) {h : ℕ} (hh : 0 < h)
    (h1 : P.succProb read Good x = 1) :
    (P.aeAlg (by omega : 0 < 2 * h)).prob (read x) (P.aeRoutine (by omega : 0 < 2 * h)).len
        ⟨h, by omega⟩ = 1
      ∧ aeEstimate (2 * h) ⟨h, by omega⟩ = 1 :=
  ⟨P.aeAlg_prob_half_of_succProb_eq_one hP x hh h1, AmpSetup.aeEstimate_half hh⟩

/-! ## 6. The phase convention: `p = 1/4`, `M = 6` -/

lemma groverAngle_quarter : groverAngle (1 / 4) = Real.pi / 6 := by
  rw [groverAngle, show Real.sqrt (1 / 4) = 1 / 2 by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  refine Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six ⟨?_, ?_⟩ <;>
    nlinarith [Real.pi_pos]

/-- A grid point that is not an integer multiple of the period carries no kernel mass. -/
lemma peKernel_grid_zero {M : ℕ} {d : ℤ} (hd : d ≠ 0) (hdM : |d| < M) :
    peKernel M ((d : ℝ) / M) = 0 := by
  rw [peKernel, sum_cexp1_eq_zero hd hdM, mul_zero]

/-- **At `p = 1/4` with `M = 6`, the clock reads `1` or `5`, each with probability `1/2`,
and both labels decode to exactly `1/4`.** -/
example (hP : P.Marks read Good) (x : X) (h : P.succProb read Good x = 1 / 4) :
    (P.aeAlg (by norm_num : 0 < 6)).prob (read x) (P.aeRoutine (by norm_num : 0 < 6)).len 1
        = 1 / 2
    ∧ (P.aeAlg (by norm_num : 0 < 6)).prob (read x) (P.aeRoutine (by norm_num : 0 < 6)).len 5
        = 1 / 2
    ∧ aeEstimate 6 1 = 1 / 4 ∧ aeEstimate 6 5 = 1 / 4 := by
  have hpi := Real.pi_ne_zero
  have k0 : peKernel 6 ((0 : ℤ) : ℝ) = 1 := peKernel_int (by norm_num) 0
  have km1 : peKernel 6 ((-1 : ℤ) : ℝ) = 1 := peKernel_int (by norm_num) (-1)
  have k2 : peKernel 6 (((-2 : ℤ) : ℝ) / (6 : ℕ)) = 0 :=
    peKernel_grid_zero (by norm_num) (by norm_num)
  have k4 : peKernel 6 (((-4 : ℤ) : ℝ) / (6 : ℕ)) = 0 :=
    peKernel_grid_zero (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P.aeAlg_prob hP x _ 1, h, groverAngle_quarter]
    have e1 : Real.pi / 6 / Real.pi - (((1 : Fin 6) : ℕ) : ℝ) / (6 : ℕ) = ((0 : ℤ) : ℝ) := by
      simp; field_simp; ring
    have e2 : -(Real.pi / 6 / Real.pi) - (((1 : Fin 6) : ℕ) : ℝ) / (6 : ℕ)
        = ((-2 : ℤ) : ℝ) / (6 : ℕ) := by
      simp; field_simp; ring
    rw [e1, e2, k0, k2]; norm_num
  · rw [P.aeAlg_prob hP x _ 5, h, groverAngle_quarter]
    have e1 : Real.pi / 6 / Real.pi - (((5 : Fin 6) : ℕ) : ℝ) / (6 : ℕ)
        = ((-4 : ℤ) : ℝ) / (6 : ℕ) := by
      simp; field_simp; ring
    have e2 : -(Real.pi / 6 / Real.pi) - (((5 : Fin 6) : ℕ) : ℝ) / (6 : ℕ) = ((-1 : ℤ) : ℝ) := by
      simp; field_simp; ring
    rw [e1, e2, k4, km1]; norm_num
  · rw [aeEstimate, show Real.pi * (((1 : Fin 6) : ℕ) : ℝ) / (6 : ℕ) = Real.pi / 6 by simp,
      Real.sin_pi_div_six]
    norm_num
  · rw [aeEstimate, show Real.pi * (((5 : Fin 6) : ℕ) : ℝ) / (6 : ℕ) = Real.pi - Real.pi / 6 by
        simp; ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
    norm_num

end AE

/-! ## 7. Counting -/

theorem acceptance_count {n : ℕ} (hn : 0 < n) {M : ℕ} (hM : 0 < M) (x : Fin n → Bool) :
    countBudget M = 2 * (M - 1)
    ∧ (3 / 4 ≤ ∑ y : Fin M,
        if |(n : ℝ) * aeEstimate M y - markedCount x|
            ≤ 8 * Real.pi * Real.sqrt ((markedCount x : ℝ) * ((n : ℝ) - markedCount x)) / M
              + 16 * Real.pi ^ 2 * n / (M : ℝ) ^ 2
        then (countAlg hn hM).prob x (countBudget M) y else 0)
    ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → 8 * Real.pi / η ≤ M →
        3 / 4 ≤ ∑ y : Fin M, if |(n : ℝ) * aeEstimate M y - markedCount x| ≤ η * n
          then (countAlg hn hM).prob x (countBudget M) y else 0 :=
  ⟨rfl, three_quarters_le_count_accurate hn hM x,
   fun _ hη hη1 hMη => count_additive hn hM x hη hη1 hMη⟩

/-- The counting setup uses the original (undiluted) two-query marker and no preparation. -/
example {n : ℕ} (hn : 0 < n) {M : ℕ} (hM : 0 < M) :
    ((searchSetup hn).aeRoutine hM).len = 2 * (M - 1) := searchSetup_aeRoutine_len hn hM

example (x : Fin 0 → Bool) : markedCount x = 0 := markedCount_fin_zero x

/-! ## 8. Success probability `5/6` -/

theorem acceptance_kernel_five_sixths {M : ℕ} (hM : 0 < M) (φ : ℝ) :
    5 / 6 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then Complex.normSq (peKernel M (φ - (y : ℕ) / M)) else 0 :=
  five_sixths_le_good_mass hM φ

theorem acceptance_pe_five_sixths (R : QRoutine ι σ W) {M : ℕ} (hM : 0 < M) (a : ι → σ)
    {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) {φ : ℝ}
    (h : Matrix.mulVec (R.run a) ψ = cexp1 φ • ψ) :
    5 / 6 ≤ ∑ y : Fin M, if circDist (φ - (y : ℕ) / M) ≤ 4 / (M : ℝ)
      then qProb clockReadout (Matrix.mulVec ((peRoutine R hM).run a) (uniformClock M ψ)) y
      else 0 :=
  five_sixths_le_pe_close R hM a hψ h

section AE56

variable (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

theorem acceptance_ae_five_sixths (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) :
    5 / 6 ≤ ∑ y : Fin M,
      if |aeEstimate M y - P.succProb read Good x|
          ≤ 8 * Real.pi * Real.sqrt (P.succProb read Good x * (1 - P.succProb read Good x)) / M
            + 16 * Real.pi ^ 2 / (M : ℝ) ^ 2
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 :=
  P.five_sixths_le_ae_accurate hP x hM

/-- Additive accuracy `η` with probability `≥ 5/6` at the clock `aeClock η`; the query
bound is unchanged. -/
theorem acceptance_ae_additive_five_sixths (hP : P.Marks read Good) (x : X) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    (5 / 6 ≤ ∑ y : Fin (AmpSetup.aeClock η),
        if |aeEstimate (AmpSetup.aeClock η) y - P.succProb read Good x| ≤ η
        then (P.aeAlg (AmpSetup.aeClock_pos hη)).prob (read x)
          (P.aeRoutine (AmpSetup.aeClock_pos hη)).len y else 0)
    ∧ ((P.aeRoutine (AmpSetup.aeClock_pos hη)).len : ℝ)
        ≤ 18 * Real.pi * ((P.prep.len : ℝ) + P.mark.len) / η :=
  ⟨P.ae_additive_five_sixths hP x (AmpSetup.aeClock_pos hη) hη hη1 (AmpSetup.le_aeClock η),
   P.aeRoutine_len_le_real hη hη1⟩

end AE56

theorem acceptance_count_five_sixths {n : ℕ} (hn : 0 < n) {M : ℕ} (hM : 0 < M)
    (x : Fin n → Bool) :
    (5 / 6 ≤ ∑ y : Fin M,
        if |(n : ℝ) * aeEstimate M y - markedCount x|
            ≤ 8 * Real.pi * Real.sqrt ((markedCount x : ℝ) * ((n : ℝ) - markedCount x)) / M
              + 16 * Real.pi ^ 2 * n / (M : ℝ) ^ 2
        then (countAlg hn hM).prob x (countBudget M) y else 0)
    ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → 8 * Real.pi / η ≤ M →
        5 / 6 ≤ ∑ y : Fin M, if |(n : ℝ) * aeEstimate M y - markedCount x| ≤ η * n
          then (countAlg hn hM).prob x (countBudget M) y else 0 :=
  ⟨five_sixths_le_count_accurate hn hM x,
   fun _ hη hη1 hMη => count_additive_five_sixths hn hM x hη hη1 hMη⟩

/-! ## 9. Estimation through the verifier constructor -/

section Verifier

variable (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
  (rd : QBasis ι σ W → O) (verifier : QRoutine ι σ (Bool × W)) {read : X → ι → σ}
  {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- From the verifier contract alone: the *logical* success probability is estimated to
additive `η` with probability `≥ 5/6`, at cost `S + (M−1)(2S+2V) ≤ 18π(S+2V)/η`. -/
theorem acceptance_verifier_estimation (hV : IsCoherentVerifier verifier read Good rd) (x : X)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    let P := AmpSetup.ofVerifier prep init hinit rd verifier
    let M := AmpSetup.aeClock η
    (5 / 6 ≤ ∑ y : Fin M,
        if |aeEstimate M y - goodProb rd (Good x) (Matrix.mulVec (prep.run (read x)) init)| ≤ η
        then (P.aeAlg (AmpSetup.aeClock_pos hη)).prob (read x)
          (P.aeRoutine (AmpSetup.aeClock_pos hη)).len y else 0)
    ∧ (P.aeRoutine (AmpSetup.aeClock_pos hη)).len
        = prep.len + (M - 1) * (2 * prep.len + 2 * verifier.len)
    ∧ ((P.aeRoutine (AmpSetup.aeClock_pos hη)).len : ℝ)
        ≤ 18 * Real.pi * ((prep.len : ℝ) + 2 * verifier.len) / η := by
  intro P M
  have hP := ofVerifier_marks prep init hinit rd verifier hV
  refine ⟨?_, ?_, ?_⟩
  · have h := P.ae_additive_five_sixths hP x (AmpSetup.aeClock_pos hη) hη hη1
      (AmpSetup.le_aeClock η)
    rwa [ofVerifier_succProb] at h
  · rw [AmpSetup.aeRoutine_len, ofVerifier_mark_len, ofVerifier_prep_len]
  · have h := P.aeRoutine_len_le_real hη hη1
    rw [ofVerifier_mark_len, ofVerifier_prep_len] at h
    push_cast at h
    exact h

end Verifier

end AmplitudeEstimationAcceptance
end QuantumQueryComplexity
