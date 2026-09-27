import QuantumQueryComplexity.Quantum.ChordWindow
import QuantumQueryComplexity.Quantum.Reflection
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The effective gap, for the operational reflection product

The **effective-gap specialization bridge**, where the *operational* layer
(routines, queries, oracles) and the *spectral* layer (functional calculus,
chord windows) meet for the reflection product.  It is not the only such
crossing — `ClockDetector.lean` is the *suppression* bridge, joining the same
two layers for the uniform clock — so the two are kept apart, and
`InputDetector.lean` is the single file that needs both.

`ChordWindow.lean` states the effective gap for an arbitrary pair of projectors,
which is how it should be stated — it is a fact about reflections, not about
queries.  `Reflection.lean` builds the operational product `R_P · R_L` as a
two-query routine.  This file is the one line that joins them, and it is a file
of its own so that neither side has to import the other: a client that only
wants reflections does not pay for the functional calculus, and the spectral
layer stays free of the query model.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The effective gap, for the operational product.**  The abstract theorem of
`ChordWindow.lean`, instantiated by the two-query routine of
`Reflection.lean`. -/
theorem effective_chord_gap_sq_inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ)
    {w : QBasis ι σ W → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (chordNearProj ((inputReflProduct v L hL).run a) Δ *ᵥ (inputProj v a *ᵥ w))
      ≤ (Δ ^ 2 / 4) * qNormSq w := by
  rw [inputReflProduct_run]
  exact effective_chord_gap_sq (isQProjector_inputProj v a) hL hw Δ

end QuantumQueryComplexity
