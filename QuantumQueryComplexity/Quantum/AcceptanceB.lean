import QuantumQueryComplexity.Quantum.Characterization
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Boolean characterization: statement tests

This file restates the headline results in full to catch weakened statements.
It imports the strong-duality development through `Characterization`, so it
belongs to the full `QuantumQueryComplexity` library. The library root imports
it, and the default build checks it.

The pins:

1. **The characterizations** — both halves at `ε = 1/16` and at the
   conventional `ε = 1/3`, written through `qQueryOn id` rather than the
   `qQuery` abbreviation, plus the sharp promise-native Boolean lower bound
   they rest on.
2. **Oracle simulation** — the two membership translations, the two
   factor-of-two complexity inequalities, and the characterization
   transported into the conventional XOR-oracle model.
3. **The extraction is promise-native** — `exists_algorithm_of_dualPairOn`
   in full, `QueryCounts` membership and the explicit
   `8192(1 + 4√|σ|·c)` bound, for any alphabet and promise.
4. **The measurement law and the exact cost** — the Hadamard test reads
   `(1 + Re⟪u, R_a u⟫)/2` at exactly `R.len` queries, and the detector costs
   exactly `4(T−1)`.  These are what an algorithm-layer refactor is most
   likely to disturb.

Scope, on the record: total Boolean functions, at fixed error `1/16` and at
the conventional `1/3` (via the sharp Boolean output condition, not
amplification), in the transposition-oracle model AND — through the
two-queries-per-query simulation — in the standard XOR-oracle model.
`Test/AdversaryAxioms.lean` checks the characterization module's axiom
dependencies on every CI run.
-/

namespace QuantumQueryComplexity
namespace MilestoneB

open scoped Matrix
open Matrix

/-! ## 1. The characterization -/

/-- **The Boolean characterization, pinned**:
`(7/32)·ADV±(f) ≤ Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. -/
theorem acceptance {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    (7 / 32 : ℝ) * advPM f
        ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 16) : ℝ) ∧
      (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 16) : ℝ)
        ≤ 2 ^ 14 * advPM f :=
  qQuery_characterized_by_advPM f

/-- The conventional-error upper half, already free. -/
theorem acceptance_third_upper {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 ^ 14 * advPM f :=
  boundedErrorQQuery_le_advPM f

/-- **The conventional-error characterization, pinned**:
`(1/36)·ADV±(f) ≤ Q_{1/3}(f) ≤ 2¹⁴·ADV±(f)`, the lower half via the sharp
Boolean output condition — no amplification. -/
theorem acceptance_third {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * advPM f
        ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) ∧
      (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
        ≤ 2 ^ 14 * advPM f :=
  boundedErrorQQuery_characterized_by_advPM f

/-- The sharp Boolean lower bound behind it, pinned in its promise-native
parametric form: any `ε ≤ 1/2` with `2√(ε(1−ε)) < 1`. -/
theorem sharp_lower_pinned {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]
    {read : X → ι → σ} {f : X → Bool} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hlt : 2 * Real.sqrt (ε * (1 - ε)) < 1) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) / 2 * advPMOn read f
      ≤ (qQueryOn read f ε : ℝ) :=
  mul_advPMOn_le_qQueryOn_bool hdet hε0 hε2 hlt

/-! ## 2. Oracle simulation -/

/-- **Model equivalence, pinned**: the native transposition model is at most
twice the XOR model, for Boolean inputs, any promise, any output. -/
theorem simulation_std_le_pinned {ι X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq O] [Nonempty O]
    {read : X → ι → Bool} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    qQueryOn read f ε ≤ 2 * xorQQueryOn read f ε :=
  qQueryOn_le_two_mul_xorQQueryOn hdet hε0

/-- **Model equivalence, pinned**: the XOR model is at most twice the native
transposition model. -/
theorem simulation_xor_le_pinned {ι X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq O] [Nonempty O]
    {read : X → ι → Bool} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    xorQQueryOn read f ε ≤ 2 * qQueryOn read f ε :=
  xorQQueryOn_le_two_mul_qQueryOn hdet hε0

/-- The membership translations behind them: each achievable count doubles
into the other model. -/
theorem simulation_members_pinned {ι X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq O]
    {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ} :
    (q ∈ XorQueryCounts read f ε → 2 * q ∈ QueryCounts read f ε) ∧
      (q ∈ QueryCounts read f ε → 2 * q ∈ XorQueryCounts read f ε) :=
  ⟨two_mul_mem_queryCounts_of_xor, two_mul_mem_xorQueryCounts_of_std⟩

/-- **The conventional-model characterization, pinned**: total Boolean `f`,
the standard XOR oracle, error `1/3` —
`(1/72)·ADV±(f) ≤ Qˣ_{1/3}(f) ≤ 2¹⁵·ADV±(f)`. -/
theorem acceptance_xor {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    (1 / 72 : ℝ) * advPM f
        ≤ (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) ∧
      (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
        ≤ 2 ^ 15 * advPM f :=
  xorQQuery_characterized_by_advPM f

/-! ## 3. The extraction is promise-native -/

/-- **The extraction, pinned**: any `DualPairOn` of cost `c > 0` for a
Boolean function on any promise and alphabet is an algorithm at error
`1/16`, in `QueryCounts` form with the explicit bound. -/
theorem extraction_pinned {ι σ X K : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype K]
    [DecidableEq K] [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool) {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) :=
  exists_algorithm_of_dualPairOn read f P hP hc

/-- Its `qQueryOn` form. -/
theorem extraction_qQueryOn_pinned {ι σ X K : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K] [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool) {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) :=
  qQueryOn_le_of_dualPairOn read f P hP hc

/-! ## 4. The measurement law and the exact cost -/

/-- **The Hadamard test's acceptance law, pinned**: probability
`(1 + Re⟪u, R_a u⟫)/2`, measured after exactly `R.len` queries. -/
theorem hadamard_test_pinned {ι σ W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]
    (R : QRoutine ι σ W) {u : QBasis ι σ W → ℂ} (hu : IsQState u)
    (a : ι → σ) :
    (hadTest R u hu).prob a R.len true
      = (1 + (qInner u (R.run a *ᵥ u)).re) / 2 :=
  hadTest_prob_true R hu a

/-- **The detector's exact cost, pinned**: `4(T−1)` queries. -/
theorem detector_cost_pinned {ι σ X O K : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [DecidableEq O]
    [Fintype K] [DecidableEq K]
    (read : X → ι → σ) (f : X → O) (P : DualPairOn read K f) (o : O)
    (T : ℕ) :
    (scDetector read f P o T).len = 4 * (T - 1) :=
  scDetector_len read f P o T

end MilestoneB
end QuantumQueryComplexity
