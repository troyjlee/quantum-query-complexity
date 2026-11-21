import QuantumQueryComplexity.Quantum.Records.CondBern
import QuantumQueryComplexity.Quantum.JointState.Oracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The input phase in workspace coordinates

On a distribution `ρ` over Boolean strings, the input phase `Q_e = readPhase (·.1) e` multiplies
the workspace vector of every input `x` by `(−1)^{x_e}`: on the support
(`FinDist.wvec_readPhase_mul`) and at every input (`FinDist.wvecAt_readPhase_mul`). Used by the
local comparison maps of the downstream problems repository.
-/

namespace QuantumQueryComplexity

open scoped Matrix

variable {A : Type} [Fintype A]

/-- The input phase `Q_e` multiplies `wvec` at `x` by `(−1)^{x_e}`. -/
theorem FinDist.wvec_readPhase_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : FinDist (ι → Bool)) (e : ι) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (readPhase (fun x : ρ.Supp => x.1) e * f) x
      = (if x.1 e then (-1 : ℂ) else 1) • ρ.wvec f x := by
  rw [readPhase, FinDist.wvec_diagonal_mul]

/-- The input phase `Q_e` multiplies `wvecAt` at any input `z` by `(−1)^{z_e}`. -/
theorem FinDist.wvecAt_readPhase_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : FinDist (ι → Bool)) (e : ι) (f : JVec ρ.Supp A) (z : ι → Bool) :
    ρ.wvecAt (readPhase (fun x : ρ.Supp => x.1) e * f) z
      = (if z e then (-1 : ℂ) else 1) • ρ.wvecAt f z := by
  by_cases h : 0 < ρ.mass z
  · rw [FinDist.wvecAt, FinDist.wvecAt, dite_eq_left h, dite_eq_left h, FinDist.wvec_readPhase_mul]
  · rw [FinDist.wvecAt, FinDist.wvecAt, dite_eq_right h, dite_eq_right h, smul_zero]

end QuantumQueryComplexity
