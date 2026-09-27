import QuantumQueryComplexity.Quantum.ReadAll
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# When is `qQueryOn` meaningful?

`qQueryOn read f ε = sInf (QueryCounts read f ε)` and `Nat.sInf ∅ = 0`, so an
**impossible** problem is reported as costing zero queries.  That is a hazard of
the public API rather than of the theorems — every result about `qQueryOn`
either carries the nonemptiness hypothesis or derives it from observational
determinacy — but a hazard that is documented and not *characterized* is a trap.

This file closes it by pinning down exactly when the junk value occurs:

  `(QueryCounts read f ε).Nonempty ↔ ∀ x y, read x = read y → f x = f y`

for `0 ≤ ε < 1/2`.  The `←` direction is the exact algorithm of `ReadAll.lean`.
The `→` direction is the operational statement that **the model computes only
observationally determined functions**: the algorithm's states depend on the
input only through `read`, so two promise inputs with the same observations have
the same output distribution, and a single distribution cannot give two distinct
outcomes probability `> 1/2` each.

Consequences, in the two directions a caller cares about:

* `qQueryOn_eq_zero_of_not_det` — the value `0` on an impossible problem is
  *provably* the junk value, not a claim that the problem is free.
* `exists_computes_qQueryOn_of_det`, `qQueryOn_le_card` — on a determined
  problem the infimum is attained and bounded by `|ι|`, so `qQueryOn` is a
  genuine minimum.

The threshold `ε < 1/2` cannot be weakened to `≤`, and the reason is specific to
**Boolean** output: there a zero-query uniform guess already achieves error
exactly `1/2`, so at `ε = 1/2` every problem — determined or not — is
"solvable" and the equivalence fails.  That witness is necessarily Boolean.  With
three or more indistinguishable answers a uniform guess errs with probability
`1 - 1/|O| > 1/2`, so `ε = 1/2` is *not* automatically achievable for a general
finite output type, and this file makes no claim that it is.  One counterexample
is all sharpness needs; the theorems below are proved for every finite `O`.
-/

namespace QuantumQueryComplexity

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype O] [DecidableEq O]
variable {X : Type} [Fintype X]
variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The model computes only observationally determined functions.**  If an
algorithm answers correctly with probability more than `1/2`, then inputs it
cannot distinguish must have the same value. -/
theorem det_of_computesWithErrorOn {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ}
    {f : X → O} {ε : ℝ} (hε : ε < 1 / 2) (h : ComputesWithErrorOn A q read f ε) :
    ∀ x y, read x = read y → f x = f y := by
  intro x y hxy
  by_contra hne
  have h1 := h x
  have h2 := h y
  rw [← hxy] at h2
  have hsum : A.prob (read x) q (f x) + A.prob (read x) q (f y) ≤ 1 :=
    qProb_add_qProb_le_one (A.state_isQState (read x) q) A.readout hne
  linarith

/-- **The achievable set is nonempty exactly on the determined problems.** -/
theorem queryCounts_nonempty_iff [Nonempty O] {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    (QueryCounts read f ε).Nonempty ↔ ∀ x y, read x = read y → f x = f y := by
  constructor
  · rintro ⟨q, W', _, _, A, hA⟩
    exact det_of_computesWithErrorOn hε hA
  · intro hdet
    exact queryCounts_nonempty hdet hε0

/-- **The junk value, characterized.**  On a problem that is not observationally
determined `qQueryOn` is `0` — because nothing computes it, not because it is
cheap. -/
theorem qQueryOn_eq_zero_of_not_det [Nonempty O] {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hε : ε < 1 / 2)
    (hnd : ¬ ∀ x y, read x = read y → f x = f y) :
    qQueryOn read f ε = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro q ⟨W', _, _, A, hA⟩
  exact hnd (det_of_computesWithErrorOn hε hA)

/-- Contrapositive, in the form a caller wants: a nonzero query count certifies
that the problem is determined. -/
theorem det_of_qQueryOn_ne_zero [Nonempty O] {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hε : ε < 1 / 2) (h : qQueryOn read f ε ≠ 0) :
    ∀ x y, read x = read y → f x = f y := by
  by_contra hnd
  exact h (qQueryOn_eq_zero_of_not_det hε hnd)

/-- **On a determined problem the infimum is attained.**  This is
`exists_computes_qQueryOn` with its hypothesis discharged. -/
theorem exists_computes_qQueryOn_of_det [Nonempty O] {read : X → ι → σ}
    {f : X → O} {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A (qQueryOn read f ε) read f ε :=
  exists_computes_qQueryOn (queryCounts_nonempty hdet hε0)

/-- The safe two-sided reading of `qQueryOn` on a determined problem: it is
attained, and at most `|ι|`. -/
theorem qQueryOn_isMin_of_det [Nonempty O] {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A (qQueryOn read f ε) read f ε)
    ∧ qQueryOn read f ε ≤ Fintype.card ι :=
  ⟨exists_computes_qQueryOn_of_det hdet hε0, qQueryOn_le_card hdet hε0⟩

end QuantumQueryComplexity
