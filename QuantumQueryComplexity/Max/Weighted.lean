import QuantumQueryComplexity.Max.Staircase
import QuantumQueryComplexity.WeightedDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The weighted cost of the staircase dual

`QuantumQueryComplexity/Max/Staircase.lean` gives the staircase dual per-coordinate weights
`w`, which cancel in every product and so leave feasibility untouched.  Their
purpose is entirely quantitative, and it is realised here: with `w = √c` the
`c`-weighted cost becomes proportional to `∑ i, (c i)²` rather than `∑ i, c i`.

That distinction is the whole reason divide and conquer wins.  Across the levels
of a recursion the subproblem costs `c p` vary over many orders of magnitude —
level `t` has `2^t` subproblems of cost about `√(n/2^t)` — and

  `∑ p, (c p)² = ∑ t, 2^t · n/2^t = n log n`,   whereas   `∑ p, c p ≈ n`.

Paired with `DualPair.composeShared_isCostLe`, this is what turns "solve each
subproblem, then maximise over subproblems" into a `√(n log n)` bound instead of
a linear one.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {C : Type*} [Fintype C]

namespace Staircase

variable (S : Staircase A C)

/-- **The `c`-weighted cost of the staircase dual.**  With balancing weights
`w = √c`, the outer solution costs `(lam²α)·∑ (c i)² + lam⁻²β`, which optimises
to `2√(αβ · ∑ (c i)²)`.

This is the form a divide-and-conquer composition consumes: paired with
`DualPair.composeShared_isCostLe`, an outer maximum over subproblems of costs
`c p` composes to `√(∑ (c p)²)` up to the staircase's `√(αβ)`. -/
lemma dual_isWeightedCostLe {lam : ℝ} (hlam : lam ≠ 0) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {α β : ℝ}
    (hα : ∀ j, (∑ d, S.a j d * S.a j d) ≤ α)
    (hβ : ∀ k, (∑ d, S.G k d * S.G k d) ≤ β) :
    (S.dual (ι := ι) hlam (w := fun i => Real.sqrt (c i))
        (fun i => (Real.sqrt_pos.mpr (hc i)).ne')).IsWeightedCostLe c
      ((lam * lam) * α * (∑ i, c i * c i) + lam⁻¹ * lam⁻¹ * β) := by
  refine ⟨fun x => S.sum_dualU_sq_weighted_le hlam hc x hα hβ, fun y => ?_⟩
  have h : ∀ i : ι,
      (∑ k : C ⊕ C, S.dualV lam (fun i => Real.sqrt (c i)) y i k
          * S.dualV lam (fun i => Real.sqrt (c i)) y i k)
      = ∑ k : C ⊕ C, S.dualU lam (fun i => Real.sqrt (c i)) y i k
          * S.dualU lam (fun i => Real.sqrt (c i)) y i k := fun i =>
    Fintype.sum_equiv (Equiv.sumComm C C) _ _ fun k => by
      rw [S.dualV_eq_dualU_swap]
      rfl
  show (∑ i, c i * ∑ k : C ⊕ C, S.dualV lam (fun i => Real.sqrt (c i)) y i k
      * S.dualV lam (fun i => Real.sqrt (c i)) y i k) ≤ _
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [h i]]
  exact S.sum_dualU_sq_weighted_le hlam hc y hα hβ

end Staircase

end QuantumQueryComplexity
