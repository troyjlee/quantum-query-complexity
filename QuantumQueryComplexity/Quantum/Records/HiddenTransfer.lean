import QuantumQueryComplexity.Quantum.Records.RecordCount

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Hidden problems and the exact transfer operator

Belovs's framework [Bel26, Sections 3.3–3.4] runs the algorithm on a **reference** distribution
`ρ` on strings — there the uniform distribution on `Z_qⁿ`, here any product distribution with
full-support marginals — and moves the result to the distribution of the problem being solved by
an exact **transfer operator**.

A **hidden computational problem** is a distribution `ν` on a finite type `Ω` of labelled inputs,
each observed through `read : Ω → ι → σ` [Bel26, Definition 3.3]. The label may carry a hidden
type (`Knowledge.lean`) and the relation `Good` may depend on it; several labels may share a string.
The transfer operator (`xferOp`) is, in the square-root weighted coordinates,

    Υ |x⟩ = ∑_{ω : read ω = x} √(ν(ω)/ρ(x)) |ω⟩    [Bel26, (3.25)].

It maps `|ρ⟩` to `|ν⟩` (`xferOp_mulVec_ket`), commutes with every query (`xferOp_mul_jOracle`,
[Bel26, Fact 3.5]), and therefore carries the joint state of any algorithm under `ρ` to its joint
state under `ν` (`xferOp_mul_jointState`, `xferOp_mul_jointXorState`, [Bel26, Proposition 3.6]).
The type-restricted operators `Υ_μ` of [Bel26, (3.26)] are rows of `Υ` and need no separate
definition.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace FinDist

/-- **The exact transfer operator** from the reference distribution `ρ` to the hidden problem
`ν` observed through `read` [Bel26, (3.25)]: the entry at `(ω, x)` is `√(ν(ω)/ρ(x))` if
`read ω = x` and `0` otherwise. -/
noncomputable def xferOp (ρ : FinDist (ι → σ)) (ν : FinDist Ω) (read : Ω → ι → σ) :
    Matrix ν.Supp ρ.Supp ℂ :=
  fun ω x => if read ω = x.1 then ((Real.sqrt (ν.mass ω / ρ.mass x) : ℝ) : ℂ) else 0

variable {ρ : FinDist (ι → σ)} {ν : FinDist Ω} {read : Ω → ι → σ}

/-- `√(ν(ω)/ρ(x)) · √ρ(x) = √ν(ω)` when `ρ(x) > 0`. -/
private lemma sqrt_div_mul_sqrt {a b : ℝ} (hb : 0 < b) :
    ((Real.sqrt (a / b) : ℝ) : ℂ) * ((Real.sqrt b : ℝ) : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul' _ hb.le, div_mul_cancel₀ _ hb.ne']

/-- Under full support, row `ω` of `Υ` has the single nonzero entry at `read ω`. -/
private lemma xferOp_sum_mul (h : ρ.IsFullProduct) (ω : ν.Supp) (g : ρ.Supp → ℂ) :
    ∑ x, xferOp ρ ν read ω x * g x
      = ((Real.sqrt (ν.mass ω / ρ.mass (read ω)) : ℝ) : ℂ)
          * g ⟨read ω, mass_pos_of_isFullProduct h _⟩ := by
  rw [Finset.sum_eq_single ⟨read ω, mass_pos_of_isFullProduct h _⟩]
  · simp [xferOp]
  · intro x _ hx
    have : read ω ≠ x.1 := fun e => hx (Subtype.ext e.symm)
    simp [xferOp, this]
  · simp

/-- `Υ` carries the joint vector with workspace vectors `g ∘ val` under `ρ` to the one with
workspace vectors `g ∘ read` under `ν`. -/
private lemma xferOp_mul_ofWvec (h : ρ.IsFullProduct) {A : Type} [Fintype A]
    (g : (ι → σ) → A → ℂ) :
    xferOp ρ ν read * ρ.ofWvec (fun x => g x.1) = ν.ofWvec (fun ω => g (read ω)) := by
  ext ω b
  rw [Matrix.mul_apply]
  simp only [ofWvec, Pi.smul_apply, smul_eq_mul]
  rw [xferOp_sum_mul (g := fun x => ((Real.sqrt (ρ.mass x) : ℝ) : ℂ) * g x.1 b) h, ← mul_assoc,
    sqrt_div_mul_sqrt (mass_pos_of_isFullProduct h _)]

/-- `Υ|ρ⟩ = |ν⟩`. -/
theorem xferOp_mulVec_ket (h : ρ.IsFullProduct) : xferOp ρ ν read *ᵥ ρ.ket = ν.ket := by
  funext ω
  rw [Matrix.mulVec, dotProduct]
  simp only [ket]
  rw [xferOp_sum_mul (g := fun x => ((Real.sqrt (ρ.mass x) : ℝ) : ℂ)) h,
    sqrt_div_mul_sqrt (mass_pos_of_isFullProduct h _)]

/-- **The transfer operator commutes with queries** [Bel26, Fact 3.5], for every oracle family
and workspace. -/
theorem xferOp_mul_jOracle {A : Type} [Fintype A] (O : (ι → σ) → Matrix A A ℂ)
    (f : JVec ρ.Supp A) :
    xferOp ρ ν read * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
      = jOracle O (fun ω : ν.Supp => read ω) (xferOp ρ ν read * f) := by
  ext ω b
  have key : ∀ x : ρ.Supp, xferOp ρ ν read ω x * (O x.1 *ᵥ f x) b
      = xferOp ρ ν read ω x * (O (read ω) *ᵥ f x) b := by
    intro x
    by_cases hx : read ω = x.1
    · rw [hx]
    · simp [xferOp, hx]
  simp only [Matrix.mul_apply, jOracle]
  rw [Finset.sum_congr rfl fun x _ => key x]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **The transferred joint state** [Bel26, Proposition 3.6], value oracle: `Υ` carries the joint
state under `ρ` after `t` queries to the joint state under `ν`. -/
theorem xferOp_mul_jointState (h : ρ.IsFullProduct) {O W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (t : ℕ) :
    xferOp ρ ν read * ρ.jointState id A t = ν.jointState read A t := by
  exact xferOp_mul_ofWvec h (fun x => A.state x t)

/-- **The transferred joint state**, XOR oracle. -/
theorem xferOp_mul_jointXorState {ρ : FinDist (ι → Bool)} (h : ρ.IsFullProduct)
    {read : Ω → ι → Bool} {O W : Type} [Fintype W] [DecidableEq W] (A : QAlg ι Bool O W)
    (t : ℕ) :
    xferOp ρ ν read * ρ.jointXorState id A t = ν.jointXorState read A t := by
  exact xferOp_mul_ofWvec h (fun x => xorState A x t)

end FinDist

end QuantumQueryComplexity
