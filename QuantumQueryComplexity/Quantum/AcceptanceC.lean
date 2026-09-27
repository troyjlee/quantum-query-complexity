import QuantumQueryComplexity.Quantum.Characterization
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Promise and finite-output characterization: statement tests

These pins complement the total Boolean statements in `AcceptanceB.lean`.
Their imports include the strong-duality development, so they belong to the
full `QuantumQueryComplexity` library. The library root imports this file,
and the default build checks it.

Pinned:

1. **Promise strong duality** — above the promise adversary bound of a
   read-determined Boolean promise problem, every value is achieved by a
   feasible `DualPairOn`.
2. **The promise-Boolean characterization**, at fixed error `1/16` and at
   bounded error `1/3`, plus the multiplicative form for problems
   nonconstant on the promise.
3. **Finite outputs** — the bit-encoding upper bound at both errors, the
   same-error characterization under the unsuffixed name, and the pure
   multiplicative `2¹⁸·log m·loglog m·√|σ|·ADV±ₚ` form.

Scope, on the record: any finite **nonempty** output type, any promise
domain, any finite **nonempty** input alphabet, read-determinacy as a
hypothesis, the native transposition model.  The general-output theorem is
proved by bit-encoded outputs, the bank-swap independent-run compiler, and
majority amplification; the characterization is **same-error**, both halves
at fixed `1/16`, with the `1/3` upper bound by monotonicity (a
general-output `1/3` LOWER bound would need plurality amplification, not
yet formalized).

    #print axioms QuantumQueryComplexity.qQueryOn_characterized_by_advPMOn_bool_third
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneC

open scoped Matrix
open Matrix

/-! ## 1. Promise strong duality -/

/-- **Promise strong duality, pinned**: above the promise adversary bound of
a read-determined Boolean promise problem, every value is achieved by a
feasible promise dual solution. -/
theorem promise_duality_pinned {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]
    {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y) {c : ℝ}
    (hc : advPMOn read f < c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c :=
  exists_dualPairOn_of_advPMOn_lt hdet hc

/-! ## 2. The promise-Boolean characterization -/

/-- **The promise-Boolean characterization at `1/16`, pinned**: any promise,
any finite nonempty alphabet, Boolean outputs. -/
theorem acceptance_promise {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) :=
  qQueryOn_characterized_by_advPMOn_bool_sixteenth read f hdet

/-- **The promise-Boolean characterization at bounded error `1/3`,
pinned.** -/
theorem acceptance_promise_third {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (1 / 36 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) :=
  qQueryOn_characterized_by_advPMOn_bool_third read f hdet

/-- Its multiplicative form, for problems nonconstant on the promise. -/
theorem acceptance_promise_mul {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y)
    {x y : X} (hxy : f x ≠ f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 17 * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  qQueryOn_le_mul_advPMOn_bool_sixteenth read f hdet hxy

/-! ## 3. Finite outputs -/

/-- **The general-output upper bound, pinned**: the bit-encoding route at
`O(log m · loglog m · √|σ| · ADV±ₚ)`. -/
theorem finite_output_pinned {ι σ X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ]
    (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
            * advPMOn read f)) :=
  qQueryOn_le_advPMOn_finiteOutput read f hdet

/-- **The finite-output characterization, pinned** (the unsuffixed name):
**same-error**, both halves at fixed `1/16`, for any finite nonempty output
type. -/
theorem acceptance_finite_output {ι σ X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ]
    (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  qQueryOn_characterized_by_advPMOn read f hdet

/-- **The multiplicative asymptotic, pinned, at the characterization's own
error**: `Q_{1/16}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f)`,
`B = Nat.clog 2 m` (with `Nat.clog 2 0 = 0`, so singleton outputs are
included). -/
theorem finite_output_mul_sixteenth_pinned {ι σ X O : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]
    [Fintype O] [DecidableEq O] [Nonempty O] [Nonempty σ]
    (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  qQueryOn_le_mul_advPMOn_finiteOutput_sixteenth read f hdet

/-- Its conventional-error form, by monotonicity. -/
theorem finite_output_mul_pinned {ι σ X O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ]
    (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  qQueryOn_le_mul_advPMOn_finiteOutput read f hdet

end MilestoneC
end QuantumQueryComplexity
