import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.FiniteOutput
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.OneHotSimulation
import QuantumQueryComplexity.Quantum.OneHotReadAll
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Transport between the native and the one-hot oracle models

The generic half of the one-hot endpoints: a native lower bound halves and a
native upper bound doubles under the direct factor-two simulation of
`OneHotSimulation.lean`, and the exact read-all cap `|ι|` comes from
`OneHotReadAll.lean`. These statements apply to arbitrary observation maps
and output functions, so applications can reuse the model comparison.
-/

namespace QuantumQueryComplexity

section Transfer

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O] [Nonempty O] {X : Type} [Fintype X]

/-- **A native lower bound halves** into the one-hot model. -/
theorem half_le_oneHotQQueryOn_of_le_qQueryOn {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) {c : ℝ}
    (h : c ≤ (qQueryOn read f ε : ℝ)) :
    c / 2 ≤ (oneHotQQueryOn read f ε : ℝ) := by
  have h2 : (qQueryOn read f ε : ℝ) ≤ 2 * (oneHotQQueryOn read f ε : ℝ) := by
    exact_mod_cast qQueryOn_le_two_mul_oneHotQQueryOn hdet hε0
  linarith

/-- **A native upper bound doubles** into the one-hot model. -/
theorem oneHotQQueryOn_le_two_mul_of_qQueryOn_le {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) {c : ℝ}
    (h : (qQueryOn read f ε : ℝ) ≤ c) :
    (oneHotQQueryOn read f ε : ℝ) ≤ 2 * c := by
  have h2 : (oneHotQQueryOn read f ε : ℝ) ≤ 2 * (qQueryOn read f ε : ℝ) := by
    exact_mod_cast oneHotQQueryOn_le_two_mul_qQueryOn hdet hε0
  linarith

/-- A total function is observationally determined. -/
lemma id_det (f : (ι → σ) → O) :
    ∀ x y : ι → σ, id x = id y → f x = f y :=
  fun x y h => by rw [show x = y from h]

/-- **Reading every letter, exactly**: `oneHotQQuery f ε ≤ |ι|`. -/
theorem oneHotQQuery_le_card (f : (ι → σ) → O) {ε : ℝ} (hε : 0 ≤ ε) :
    oneHotQQuery f ε ≤ Fintype.card ι :=
  oneHotQQueryOn_le_card (id_det f) hε

end Transfer

end QuantumQueryComplexity
