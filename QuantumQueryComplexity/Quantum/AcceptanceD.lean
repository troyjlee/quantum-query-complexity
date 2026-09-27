import QuantumQueryComplexity.Quantum.UniformHasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Uniform extraction: statement tests

These pins cover cardinality-free non-Boolean extraction. They import the
`HasDualOn` wrappers from the classical layer, so they belong to the full
`QuantumQueryComplexity` library. The library root imports this file,
and the default build checks it.

Pinned:

1. **The constant** — `uniformExtractionConstant = 8192`, one fixed
   absolute numeral, not a free variable.
2. **The acceptance theorem** — a promise dual solution of cost `c` is an
   algorithm at error `1/16` within `8192(1 + c)` queries.
3. **The bundled wrappers** — `Q_{1/16}` and `Q_{1/3}` against
   `HasDualOn`.

Scope, on the record, every clause load-bearing: arbitrary **decidable**
output type `O` — *no* `[Fintype O]` anywhere; the constant is independent
of `|σ|`, of `|O|`, and of `|range f|`; `[Nonempty O]` and `0 ≤ c` are
genuine hypotheses (the readout needs a junk label, and a negative `c`
would make the bound negative); promise-native; no appeal to
general-output strong duality.

    #print axioms QuantumQueryComplexity.exists_algorithm_of_dualPairOn_uniform
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneD

/-! ## 1. The constant -/

/-- **The extraction constant, pinned**: the absolute numeral `8192`. -/
theorem uniform_constant_pinned : uniformExtractionConstant = (8192 : ℝ) :=
  rfl

/-! ## 2. The acceptance theorem -/

/-- **Cardinality-free extraction, pinned**: any promise dual solution of
cost `c`, over any decidable output type, yields an algorithm at error
`1/16` within `uniformExtractionConstant·(1 + c)` queries. -/
theorem acceptance_uniform {ι σ K X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X]
    [DecidableEq O] [Nonempty O] {read : X → ι → σ} {f : X → O}
    (P : DualPairOn read K f) {c : ℝ} (hP : P.IsCostLe c) (hc : 0 ≤ c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ uniformExtractionConstant * (1 + c) :=
  exists_algorithm_of_dualPairOn_uniform P hP hc

/-! ## 3. The bundled wrappers -/

/-- **The `HasDualOn` wrapper at `1/16`, pinned.** -/
theorem acceptance_uniform_hasDual {ι σ X O : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq O]
    [Nonempty O] {read : X → ι → σ} {f : X → O} {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) :=
  qQueryOn_le_of_hasDualOn_uniform h hc

/-- **The `HasDualOn` wrapper at bounded error `1/3`, pinned.** -/
theorem acceptance_uniform_hasDual_third {ι σ X O : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq O]
    [Nonempty O] {read : X → ι → σ} {f : X → O} {c : ℝ}
    (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + c) :=
  qQueryOn_third_le_of_hasDualOn_uniform h hc

end MilestoneD
end QuantumQueryComplexity
