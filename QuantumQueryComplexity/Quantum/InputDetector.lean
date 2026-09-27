import QuantumQueryComplexity.Quantum.ClockDetector
import QuantumQueryComplexity.Quantum.OperationalGap
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The detector for the input reflection product

The specialization, and the only file that needs both the suppression bridge
(`ClockDetector.lean`) and the effective gap for the operational product
(`OperationalGap.lean`).  Everything upstream stays generic: `ClockDetector`
knows nothing about input reflections, `OperationalGap` nothing about clocks.

Three facts, which together are the detector's guarantee on `P w`:

* **Cost.**  `4(T-1)` queries, exactly.  `inputReflProduct` costs `2` because
  the `L`-side reflection is a fixed, zero-query `ofUnitary`, and conjugating
  `SELECT` doubles `(T-1)·2`.  If both sides were input-dependent this would be
  `8(T-1)`.
* **The far part is large.**  The effective gap bounds the *near* part of `P w`
  by `(Δ²/4)‖w‖²`, so by the Pythagorean decomposition the far part carries at
  least `‖P w‖² - (Δ²/4)‖w‖²`.
* **The detector reads `-1` there**, up to `16/(T²Δ²)·‖P w‖²`.

Completeness is `clockPhaseRefl_run_mulVec_uniformClock_of_fixed`: on a vector
fixed by the reflection product the detector is *exactly* the identity, so the
two verdicts are separated with no error on one side.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- **The exact cost of the input detector**: `4(T-1)` queries. -/
@[simp] theorem clockPhaseRefl_len_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (T : ℕ) :
    (clockPhaseRefl (inputReflProduct v L hL) T).len = 4 * (T - 1) := by
  rw [clockPhaseRefl_len, inputReflProduct_len]
  ring

/-- **The far window carries what the effective gap leaves.**  The near part of
`P w` is at most `(Δ²/4)‖w‖²`, so the far part — the part the detector sees — is
at least `‖P w‖²` minus that. -/
theorem le_qNormSq_chordFar_inputProj (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ)
    {w : QBasis ι σ W → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (inputProj v a *ᵥ w) - (Δ ^ 2 / 4) * qNormSq w
      ≤ qNormSq (chordFarProj ((inputReflProduct v L hL).run a) Δ
          *ᵥ (inputProj v a *ᵥ w)) := by
  have hdec := qNormSq_chord_decomp ((inputReflProduct v L hL).run a) Δ
    (inputProj v a *ᵥ w)
  have hnear := effective_chord_gap_sq_inputReflProduct v L hL a hw Δ
  linarith

/-- **The input detector reads `-1` on the far window**, multiplied out — and,
like the bound it specializes, with no positivity hypothesis. -/
theorem qNormSq_clockPhaseRefl_add_le_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (T : ℕ)
    (a : ι → σ) (Δ : ℝ) (w : QBasis ι σ W → ℂ) :
    (T : ℝ) ^ 2 * Δ ^ 2
        * qNormSq ((clockPhaseRefl (inputReflProduct v L hL) T).run a
              *ᵥ uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
                  *ᵥ (inputProj v a *ᵥ w))
            + uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
                *ᵥ (inputProj v a *ᵥ w)))
      ≤ 16 * qNormSq (inputProj v a *ᵥ w) :=
  qNormSq_clockPhaseRefl_add_le (inputReflProduct v L hL) T a Δ (inputProj v a *ᵥ w)

/-- **The input detector reads `-1` on the far window**, in divided form. -/
theorem qNormSq_clockPhaseRefl_add_le_div_inputReflProduct
    (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) {T : ℕ}
    (hT : 0 < T) (a : ι → σ) {Δ : ℝ} (hΔ : 0 < Δ) (w : QBasis ι σ W → ℂ) :
    qNormSq ((clockPhaseRefl (inputReflProduct v L hL) T).run a
          *ᵥ uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
              *ᵥ (inputProj v a *ᵥ w))
        + uniformClock T (chordFarProj ((inputReflProduct v L hL).run a) Δ
            *ᵥ (inputProj v a *ᵥ w)))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) * qNormSq (inputProj v a *ᵥ w) :=
  qNormSq_clockPhaseRefl_add_le_div (inputReflProduct v L hL) hT a hΔ
    (inputProj v a *ᵥ w)

end QuantumQueryComplexity
