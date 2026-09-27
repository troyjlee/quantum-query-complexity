import QuantumQueryComplexity.Quantum.Clock
import QuantumQueryComplexity.Quantum.ClockGap
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The uniform-clock detector

The **suppression bridge**: the operational clock of `Clock.lean` meets the
spectral estimate of `ClockGap.lean`.  It needs those two and nothing else — in
particular not `OperationalGap.lean`, which is for *specializing* this to the
input reflection product, not for stating it.

The detector is `clockPhaseRefl R T = SELECTᴴ · clockRefl · SELECT`, and the two
facts about it are exactly the two extremes:

* **Completeness** (`Clock.lean`): on a fixed vector it is the identity, exactly.
* **Soundness** (here): on the far window it is `-1` up to an error that shrinks
  like `1/T`:

      `‖D·u + u‖² ≤ 16/(T²Δ²)·‖x‖²`,   `u = uniformClock T (F x)`.

Both come from one algebraic identity, `D·u + u = 2·SELECTᴴ P SELECT u`: the
detector's deviation from `-1` **is** twice the averaging projector's output, so
soundness is precisely the statement that the vector average is small.  The `16`
is `4 · 4`: one factor from that `2`, squared, and one from `‖1 - Uᵀ‖ ≤ 2` inside
the suppression bound.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- **The detector's deviation from `-1` is twice the averaged state.**  This is
the identity behind everything below: `D·u + u = 2·SELECTᴴ P SELECT u`. -/
theorem clockPhaseRefl_run_mulVec_add (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (u : QBasis ι σ (ClockWork ι T W) → ℂ) :
    (clockPhaseRefl R T).run a *ᵥ u + u
      = (2 : ℂ) • (((selectPowers R T).run a)ᴴ
          *ᵥ (clockAvgProj T *ᵥ ((selectPowers R T).run a *ᵥ u))) := by
  have hSS : ((selectPowers R T).run a)ᴴ *ᵥ ((selectPowers R T).run a *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [clockPhaseRefl_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, clockRefl,
    qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, hSS]
  module

lemma conjTranspose_mem_unitaryGroup {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact conjTranspose_mul_self_of_unitary hU

/-- **Soundness of the detector**, multiplied out.  On the far window the
detector is `-1` up to an error controlled by `1/(TΔ)`.  As with the suppression
bound it rests on, this form needs **no positivity hypothesis**: at `T = 0` the
factor `T²` kills the left side. -/
theorem qNormSq_clockPhaseRefl_add_le (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (Δ : ℝ) (x : QBasis ι σ W → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((clockPhaseRefl R T).run a
              *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x)
            + uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      ≤ 16 * qNormSq x := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · -- an empty clock: the left side carries the factor `T² = 0`
    subst hT
    have hq := qNormSq_nonneg x
    have h0 : ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul, zero_mul]
    linarith
  have hU := R.run_mem_unitaryGroup a
  have hSu := (selectPowers R T).run_mem_unitaryGroup a
  -- the deviation is twice the averaged state, whose norm is the vector average
  have hdev := clockPhaseRefl_run_mulVec_add R T a
    (uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
  have havg : clockAvgProj T *ᵥ ((selectPowers R T).run a
        *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      = uniformClock T ((T : ℂ)⁻¹
          • ∑ c : Fin T, (R.run a) ^ (c : ℕ) *ᵥ (chordFarProj (R.run a) Δ *ᵥ x)) :=
    clockAvgProj_mulVec_selectPowers_uniformClock R T a _
  rw [hdev, havg, qNormSq_smul, qNormSq_mulVec (conjTranspose_mem_unitaryGroup hSu),
    qNormSq_uniformClock hT]
  have hsupp := qNormSq_avg_pow_chordFar hU Δ T x
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]
  nlinarith [hsupp]

/-- **Soundness of the detector**, in divided form:
`‖D·u + u‖² ≤ 16/(T²Δ²)·‖x‖²`. -/
theorem qNormSq_clockPhaseRefl_add_le_div (R : QRoutine ι σ W) {T : ℕ} (hT : 0 < T)
    (a : ι → σ) {Δ : ℝ} (hΔ : 0 < Δ) (x : QBasis ι σ W → ℂ) :
    qNormSq ((clockPhaseRefl R T).run a
          *ᵥ uniformClock T (chordFarProj (R.run a) Δ *ᵥ x)
        + uniformClock T (chordFarProj (R.run a) Δ *ᵥ x))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq x := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < (T : ℝ) ^ 2 * Δ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm]
  exact qNormSq_clockPhaseRefl_add_le R T a Δ x

end QuantumQueryComplexity
