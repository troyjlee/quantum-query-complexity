import QuantumQueryComplexity.Quantum.XorPolynomialMethod
import QuantumQueryComplexity.Quantum.Simulation
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Query lower bounds from polynomial obstructions

The two lower-bound interfaces of the polynomial method, for the native and the XOR
oracle, on promise problems and total functions:

* **algorithm level**: if no polynomial of total degree `≤ d` approximates `f` within `ε`
  on the observations `read x`, then every `t`-query algorithm with error `ε` has `d < 2·t`
  (`lt_two_mul_of_computes`, `lt_two_mul_of_xorComputes`);
* **complexity level**: the same conclusion for the optimal query count, once the
  achievable set is known to be nonempty (`lt_two_mul_qQueryOn`, `lt_two_mul_xorQQueryOn`),
  with the natural-number rounding `d / 2 + 1 ≤ Q`.

`qQueryOn` is an infimum in `ℕ` and `sInf ∅ = 0`, so an obstruction alone is not a lower
bound on the infimum: the complexity-level theorems take the nonemptiness hypothesis
explicitly, or discharge it from read-determinacy and `0 ≤ ε` through
`queryCounts_nonempty`/`xorQueryCounts_nonempty`.  No injectivity of `read` and no
`ε < 1/2` is assumed; `ε = 0` gives the exact polynomial method.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X : Type} [Fintype X]

/-- A degree-`d` polynomial obstruction to approximating `f` on the promise within `ε`. -/
def PolyObstructionOn (read : X → ι → Bool) (f : X → Bool) (ε : ℝ) (d : ℕ) : Prop :=
  ∀ p : MvPolynomial ι ℝ, p.totalDegree ≤ d → ¬ ApproximatesOn p read f ε

variable {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} {d : ℕ}

/-! ## The native oracle -/

section Native

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Algorithm-level obstruction.** -/
theorem lt_two_mul_of_computes (hobs : PolyObstructionOn read f ε d) {A : QAlg ι Bool Bool W}
    {t : ℕ} (hA : ComputesWithErrorOn A t read f ε) : d < 2 * t := by
  obtain ⟨p, hdeg, happ, -⟩ := hA.exists_approx_polynomial
  by_contra hle
  push Not at hle
  exact hobs p (hdeg.trans hle) happ

end Native

/-- **Complexity-level obstruction**, with the achievable set assumed nonempty. -/
theorem lt_two_mul_qQueryOn (hne : (QueryCounts read f ε).Nonempty)
    (hobs : PolyObstructionOn read f ε d) : d < 2 * qQueryOn read f ε := by
  obtain ⟨W, hW, hWd, A, hA⟩ := exists_computes_qQueryOn hne
  exact lt_two_mul_of_computes hobs hA

theorem div_two_succ_le_qQueryOn (hne : (QueryCounts read f ε).Nonempty)
    (hobs : PolyObstructionOn read f ε d) : d / 2 + 1 ≤ qQueryOn read f ε := by
  have := lt_two_mul_qQueryOn hne hobs
  omega

/-- The convenient form: read-determinacy and `0 ≤ ε` supply nonemptiness. -/
theorem lt_two_mul_qQueryOn_of_det (hdet : ∀ x y, read x = read y → f x = f y) (hε : 0 ≤ ε)
    (hobs : PolyObstructionOn read f ε d) : d < 2 * qQueryOn read f ε :=
  lt_two_mul_qQueryOn (queryCounts_nonempty hdet hε) hobs

theorem div_two_succ_le_qQueryOn_of_det (hdet : ∀ x y, read x = read y → f x = f y)
    (hε : 0 ≤ ε) (hobs : PolyObstructionOn read f ε d) : d / 2 + 1 ≤ qQueryOn read f ε :=
  div_two_succ_le_qQueryOn (queryCounts_nonempty hdet hε) hobs

/-- Total functions: `read = id`. -/
theorem lt_two_mul_qQuery {g : (ι → Bool) → Bool} (hε : 0 ≤ ε)
    (hobs : PolyObstructionOn id g ε d) : d < 2 * qQuery g ε :=
  lt_two_mul_qQueryOn_of_det (fun _ _ h => congrArg g h) hε hobs

theorem div_two_succ_le_qQuery {g : (ι → Bool) → Bool} (hε : 0 ≤ ε)
    (hobs : PolyObstructionOn id g ε d) : d / 2 + 1 ≤ qQuery g ε :=
  div_two_succ_le_qQueryOn_of_det (fun _ _ h => congrArg g h) hε hobs

/-! ## The XOR oracle -/

section Xor

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Algorithm-level obstruction, XOR oracle.** -/
theorem lt_two_mul_of_xorComputes (hobs : PolyObstructionOn read f ε d)
    {A : QAlg ι Bool Bool W} {t : ℕ} (hA : XorComputesWithErrorOn A t read f ε) :
    d < 2 * t := by
  obtain ⟨p, hdeg, happ, -⟩ := hA.exists_approx_polynomial
  by_contra hle
  push Not at hle
  exact hobs p (hdeg.trans hle) happ

end Xor

/-- The optimal XOR algorithm exists as soon as any does. -/
theorem exists_xorComputes_xorQQueryOn {O : Type} [DecidableEq O] {g : X → O}
    (hne : (XorQueryCounts read g ε).Nonempty) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι Bool O W),
      XorComputesWithErrorOn A (xorQQueryOn read g ε) read g ε :=
  Nat.sInf_mem hne

/-- **Complexity-level obstruction, XOR oracle.** -/
theorem lt_two_mul_xorQQueryOn (hne : (XorQueryCounts read f ε).Nonempty)
    (hobs : PolyObstructionOn read f ε d) : d < 2 * xorQQueryOn read f ε := by
  obtain ⟨W, hW, hWd, A, hA⟩ := exists_xorComputes_xorQQueryOn hne
  exact lt_two_mul_of_xorComputes hobs hA

theorem div_two_succ_le_xorQQueryOn (hne : (XorQueryCounts read f ε).Nonempty)
    (hobs : PolyObstructionOn read f ε d) : d / 2 + 1 ≤ xorQQueryOn read f ε := by
  have := lt_two_mul_xorQQueryOn hne hobs
  omega

theorem lt_two_mul_xorQQueryOn_of_det (hdet : ∀ x y, read x = read y → f x = f y)
    (hε : 0 ≤ ε) (hobs : PolyObstructionOn read f ε d) : d < 2 * xorQQueryOn read f ε :=
  lt_two_mul_xorQQueryOn (xorQueryCounts_nonempty hdet hε) hobs

theorem div_two_succ_le_xorQQueryOn_of_det (hdet : ∀ x y, read x = read y → f x = f y)
    (hε : 0 ≤ ε) (hobs : PolyObstructionOn read f ε d) :
    d / 2 + 1 ≤ xorQQueryOn read f ε :=
  div_two_succ_le_xorQQueryOn (xorQueryCounts_nonempty hdet hε) hobs

/-- Total functions, XOR oracle. -/
theorem lt_two_mul_xorQQuery {g : (ι → Bool) → Bool} (hε : 0 ≤ ε)
    (hobs : PolyObstructionOn id g ε d) : d < 2 * xorQQueryOn id g ε :=
  lt_two_mul_xorQQueryOn_of_det (fun _ _ h => congrArg g h) hε hobs

theorem div_two_succ_le_xorQQuery {g : (ι → Bool) → Bool} (hε : 0 ≤ ε)
    (hobs : PolyObstructionOn id g ε d) : d / 2 + 1 ≤ xorQQueryOn id g ε :=
  div_two_succ_le_xorQQueryOn_of_det (fun _ _ h => congrArg g h) hε hobs

end QuantumQueryComplexity
