import QuantumQueryComplexity.Max.Dyadic
import QuantumQueryComplexity.Max.Lower
import QuantumQueryComplexity.FirstDiff
import QuantumQueryComplexity.Scan.Final
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# `ADV±(MAX) = Θ(√n)`

For `maxFun` on `n` coordinates over a finite linearly ordered alphabet of size
`m`, the adversary bound is `√n` up to a constant, with **no dependence on the
alphabet**:

  `√n ≤ ADV±(MAX) ≤ 24 √n`.

The lower bound is the star witness on a two-valued sub-cube, where `maxFun`
degenerates to `OR` (`QuantumQueryComplexity/Max/Lower.lean`).  The upper bound is the
weighted random scan of `QuantumQueryComplexity/Scan/Final.lean`.

## Two weaker bounds, and why they are still here

* `2⌈log₂ m⌉ √n` from the dyadic staircase (`QuantumQueryComplexity/Max/Dyadic.lean`);
* `2n` from the first-difference dual (`QuantumQueryComplexity/FirstDiff.lean`).

Both are superseded by `24 √n`, but neither is dead weight: the staircase is the
general "cut" machinery used elsewhere, and the `2n` bound holds for *every*
function, not just `maxFun`.

## Why the staircase could not reach `√n`

Worth recording, because the obstruction is real but narrower than it looks.
Any witness of "staircase" shape must supply vectors with
`⟨a_j, G_k⟩ = [j < k]` over the alphabet — a γ₂ factorization of the
greater-than matrix.  Since γ₂ is the Schur-multiplier norm and
`γ₂(GT_m) = Θ(log m)` (Kwapień–Pełczyński triangular truncation), the cost
within that ansatz is *exactly* `Θ(√n log m)`.  The logarithm is the price of
comparing two alphabet symbols through an inner product.

That argument bounds the ansatz, not the problem.  The scan witness never
compares two alphabet symbols through an inner product at all: the comparison
happens inside the branch structure, and the dual only ever tests branch labels
for **equality**, which costs `O(1)`.  So the greater-than matrix is never
materialised, and the logarithm never appears.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]

/-- **The sandwich.**  `ADV±(MAX)` is `√n` up to a constant, for every
alphabet. -/
theorem advPM_maxFun_sandwich {lo hi : A} (h : lo < hi) :
    Real.sqrt (Fintype.card ι : ℝ) ≤ advPM (maxFun : (ι → A) → A) ∧
      advPM (maxFun : (ι → A) → A) ≤ 24 * Real.sqrt (Fintype.card ι : ℝ) :=
  ⟨sqrt_card_le_advPM_maxFun h, advPM_maxFun_le_sqrt⟩

/-! ## The superseded bounds -/

/-- `ADV±(MAX) ≤ 2n` with no alphabet dependence, from the trivial decision tree
that reads every coordinate.  Superseded by `advPM_maxFun_le_sqrt`, but the
underlying `advPM_le_two_mul_card` holds for every function. -/
theorem advPM_maxFun_le_two_mul_card :
    advPM (maxFun : (ι → A) → A) ≤ 2 * (Fintype.card ι : ℝ) :=
  advPM_le_two_mul_card _

/-- The best bound obtainable from the staircase machinery alone: the better of
the dyadic staircase and the decision-tree dual.  Superseded by
`advPM_maxFun_le_sqrt`. -/
theorem advPM_maxFun_le_min (hA : 0 < alphaBits A) :
    advPM (maxFun : (ι → A) → A)
      ≤ min (2 * (Fintype.card ι : ℝ))
          (2 * (alphaBits A : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) :=
  le_min (advPM_le_two_mul_card _) (advPM_maxFun_le_bits hA)

end QuantumQueryComplexity
