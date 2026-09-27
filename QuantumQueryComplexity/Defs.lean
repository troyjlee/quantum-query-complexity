import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The negative-weight adversary bound: definitions

We define the negative-weight adversary bound `ADV±` of Høyer–Lee–Špalek
(quant-ph/0611054, Definition 2) for a total function `f : (ι → σ) → O`, in the
division-free primal form of Belovs–Lee (arXiv:2004.06439, Definition 6):

  `advPM f = sup { ‖Γ‖ | Γ symmetric, Γ x y = 0 whenever f x = f y,
                          and ‖Γ ⊙ D i‖ ≤ 1 for every input index i }`

where `D i = advD i` is the difference matrix with `(D i) x y = 1` iff
`x i ≠ y i`, `⊙` is the Hadamard (entrywise) product, and `‖·‖` is the spectral
(L2 operator) norm.  Since `Γ = 0` is feasible, the value set is nonempty and
`advPM f ≥ 0`; no division or `Γ ≠ 0` side condition is needed.

Nothing here uses two-valuedness of the input alphabet `σ` or of the output type
`O`: `advD` needs only `DecidableEq σ` for its `if`, and `IsAdvMatrix` uses
`f x = f y` as a proposition, never as a decidable test.  The Boolean theory is
recovered at `σ = O = Bool`, which is how every downstream file uses it; the
general alphabet is what makes non-Boolean problems such as maximum finding
expressible.

We also define the classical nonnegative-weight bound `adv` (HLŠ Definition 1)
by adding the entrywise nonnegativity constraint.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*}

/-- The difference matrix `D_i` (HLŠ §2, BL Definition 6): `(advD i) x y = 1`
if `x i ≠ y i` and `0` otherwise. -/
def advD (i : ι) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y => if x i = y i then 0 else 1

@[simp] lemma advD_apply (i : ι) (x y : ι → σ) :
    advD i x y = if x i = y i then 0 else 1 := rfl

lemma advD_isHermitian (i : ι) : (advD (σ := σ) i).IsHermitian := by
  show (advD i)ᴴ = advD i
  ext x y
  simp [Matrix.conjTranspose_apply, advD, eq_comm]

lemma hadamard_advD_apply (Γ : Matrix (ι → σ) (ι → σ) ℝ) (i : ι)
    (x y : ι → σ) : (Γ ⊙ advD i) x y = if x i = y i then 0 else Γ x y := by
  rw [Matrix.hadamard_apply, advD_apply]
  by_cases h : x i = y i <;> simp [h]

/-- An adversary matrix for `f` (HLŠ §2): a real symmetric matrix supported on
pairs of inputs with different `f`-values.  Taking `x = y` shows the diagonal
vanishes. -/
def IsAdvMatrix (f : (ι → σ) → O)
    (Γ : Matrix (ι → σ) (ι → σ) ℝ) : Prop :=
  Γ.IsHermitian ∧ ∀ x y, f x = f y → Γ x y = 0

namespace IsAdvMatrix

variable {f : (ι → σ) → O} {Γ : Matrix (ι → σ) (ι → σ) ℝ}

lemma isHermitian (h : IsAdvMatrix f Γ) : Γ.IsHermitian := h.1

lemma apply_eq_zero (h : IsAdvMatrix f Γ) {x y : ι → σ} (hxy : f x = f y) :
    Γ x y = 0 := h.2 x y hxy

lemma diag_eq_zero (h : IsAdvMatrix f Γ) (x : ι → σ) : Γ x x = 0 :=
  h.2 x x rfl

lemma smul (h : IsAdvMatrix f Γ) (c : ℝ) : IsAdvMatrix f (c • Γ) :=
  ⟨h.1.smul (star_trivial c), fun x y hxy => by
    simp [Matrix.smul_apply, h.2 x y hxy]⟩

end IsAdvMatrix

lemma isAdvMatrix_zero (f : (ι → σ) → O) : IsAdvMatrix f 0 :=
  ⟨Matrix.isHermitian_zero, fun _ _ _ => rfl⟩

/-- The negative-weight adversary bound `ADV±(f)` (HLŠ Definition 2, in the
division-free form of BL Definition 6). -/
noncomputable def advPM (f : (ι → σ) → O) : ℝ :=
  sSup {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧ r = ‖Γ‖}

/-- The classical (nonnegative-weight) adversary bound `ADV(f)`
(HLŠ Definition 1). -/
noncomputable def adv (f : (ι → σ) → O) : ℝ :=
  sSup {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
    (∀ x y, 0 ≤ Γ x y) ∧ r = ‖Γ‖}

end QuantumQueryComplexity
