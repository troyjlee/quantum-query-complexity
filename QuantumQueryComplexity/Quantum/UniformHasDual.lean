import QuantumQueryComplexity.Quantum.UniformExtraction
import QuantumQueryComplexity.Promise.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Uniform extraction: the `HasDualOn` wrappers

The bundled form of the cardinality-free extraction.  `HasDualOn` hides the
dual dimension type, and it lives in `QuantumQueryComplexity/Promise/HasDual.lean` —
**not** one of the five shared foundation modules — so this file sits
**outside** the `QuantumQueryComplexity.Quantum` aggregate. The full
`QuantumQueryComplexity` library imports it, and the default build checks it.

Both wrappers are one destructuring away from
`exists_algorithm_of_dualPairOn_uniform`: any bundled dual solution of cost
`c` gives `Q_{1/16}(f) ≤ 8192(1 + c)`, and `Q_{1/3}` by error
monotonicity — for **any decidable output type**, with no `|σ|`, `|O|` or
`|range f|` anywhere.
-/

namespace QuantumQueryComplexity

variable {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **Cardinality-free extraction from a bundled dual**:
`Q_{1/16}(f) ≤ 8192(1 + c)` for any decidable output type. -/
theorem qQueryOn_le_of_hasDualOn_uniform [Nonempty O] {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) := by
  obtain ⟨K, hK, P, hP⟩ := h
  let _ := hK
  let _ := Classical.decEq K
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn_uniform P hP hc
  have h1 : qQueryOn read f (1 / 16) ≤ q := Nat.sInf_le hq
  have h2 : (qQueryOn read f (1 / 16) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith

/-- The bounded-error form, by error monotonicity. -/
theorem qQueryOn_third_le_of_hasDualOn_uniform [Nonempty O] {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) := by
  obtain ⟨K, hK, P, hP⟩ := h
  let _ := hK
  let _ := Classical.decEq K
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn_uniform P hP hc
  have h1 : qQueryOn read f (1 / 3) ≤ q :=
    Nat.sInf_le (queryCounts_mono (by norm_num) hq)
  have h2 : (qQueryOn read f (1 / 3) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith

end QuantumQueryComplexity
