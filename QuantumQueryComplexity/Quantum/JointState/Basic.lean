import QuantumQueryComplexity.Quantum.Algorithm
import Mathlib.Analysis.Matrix.Order

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Probability-weighted joint states

An input distribution `ρ` on a finite set `Ω` gives an **input register** whose basis is
the positive support `ρ.Supp`, with initial state `|ρ⟩ = ∑ₓ √ρ(x) |x⟩` (`FinDist.ket`).
Running an algorithm with this register in superposition gives the **joint state**

  `Ψₜ = ∑ₓ √ρ(x) |x⟩ ⊗ ψₓ,ₜ`,

in which the input register is reached only through queries.  `Ω` may carry hidden labels:
the algorithm sees an input only through an observation map `read : Ω → ι → σ`.

## Representation

A **joint vector** with input basis `X` and workspace basis `A` is a matrix `f : Matrix X A ℂ`
(`JVec X A`): row `x` is the component on input `x`.  Operators on the input register act by
left multiplication, `B * f`, and operators on the workspace act on the right, so the two
commute by associativity.  Under a distribution, row `x` is `√ρ(x)` times the **workspace
vector** `ρ.wvec f x`; the squared norm is the `ρ`-average of the squared workspace norms,
and `ρ.infNormSq f` is the largest squared workspace norm.

The positive-semidefinite (Loewner) order on input operators is Mathlib's, scoped to
`MatrixOrder`.  `jInner_le_of_le` lifts it to joint vectors on **every** finite workspace, which
is how all Hilbert-norm estimates on the input register become uniform in the workspace.

## Main definitions

* `FinDist`, `FinDist.Supp`, `FinDist.ket`, `FinDist.prob`.
* `JVec`, `jInner`, `jNormSq`.
* `FinDist.wvec`, `FinDist.ofWvec`, `FinDist.infNormSq`.
* `FinDist.jointState` — the joint state of a `QAlg` under `ρ`.

## Main results

* `jInner_le_of_le`, `jNormSq_mul_le`, `jNormSq_mul_le_smul` — the order lifting.
* `FinDist.jNormSq_eq_sum_wvec` — `‖f‖² = E_ρ ‖fˣ‖²`.
* `FinDist.sum_qNormSq_le_prob_mul_infNormSq` — rare inputs contribute at most
  `ρ(S) ‖f‖∞²`.
* `FinDist.jNormSq_jointState`, `FinDist.infNormSq_jointState` — an actual computation has
  `‖Ψₜ‖ = ‖Ψₜ‖∞ = 1`.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

/-! ## Finite distributions -/

/-- A probability distribution on a finite type, given by its point masses. -/
structure FinDist (Ω : Type) [Fintype Ω] where
  /-- The mass of each point. -/
  mass : Ω → ℝ
  /-- Masses are nonnegative. -/
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  /-- Masses sum to one. -/
  sum_mass : ∑ ω, mass ω = 1

namespace FinDist

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)

/-- The positive support of `ρ`: the basis of its input register. -/
abbrev Supp : Type := {ω : Ω // 0 < ρ.mass ω}

lemma mass_pos (x : ρ.Supp) : 0 < ρ.mass x := x.2

/-- The support of a distribution is nonempty. -/
instance : Nonempty ρ.Supp := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hle : ∀ ω, ρ.mass ω ≤ 0 := fun ω => not_lt.mp fun hω => h.false ⟨ω, hω⟩
  have := Finset.sum_nonpos (s := Finset.univ) fun ω _ => hle ω
  linarith [ρ.sum_mass]

/-- The masses on the support sum to one. -/
lemma sum_mass_supp : ∑ x : ρ.Supp, ρ.mass x = 1 := by
  classical
  rw [← ρ.sum_mass, ← Finset.sum_subtype (Finset.univ.filter fun ω => 0 < ρ.mass ω)
    (p := fun ω => 0 < ρ.mass ω) (fun ω => by simp)]
  refine Finset.sum_filter_of_ne fun ω _ hω => ?_
  exact lt_of_le_of_ne (ρ.mass_nonneg ω) (Ne.symm hω)

/-- The probability of a set of support points. -/
def prob (s : Finset ρ.Supp) : ℝ := ∑ x ∈ s, ρ.mass x

/-- The initial state of the input register, `|ρ⟩ = ∑ₓ √ρ(x) |x⟩`. -/
noncomputable def ket : ρ.Supp → ℂ := fun x => (Real.sqrt (ρ.mass x) : ℂ)

/-- `|ρ⟩` is a unit vector. -/
theorem qNormSq_ket : qNormSq ρ.ket = 1 := by
  rw [qNormSq_def, ← ρ.sum_mass_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ket, Complex.normSq_ofReal, Real.mul_self_sqrt (ρ.mass_nonneg x)]

end FinDist

/-! ## Joint vectors -/

/-- A **joint vector** with input basis `X` and workspace basis `A`: row `x` is the workspace
component on input `x`.  Input-register operators act by left multiplication. -/
abbrev JVec (X A : Type) := Matrix X A ℂ

variable {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype A]

/-- The inner product of joint vectors, conjugate-linear in the first argument. -/
def jInner (f g : JVec X A) : ℂ := ∑ x, qInner (f x) (g x)

/-- The squared norm of a joint vector. -/
def jNormSq (f : JVec X A) : ℝ := ∑ x, qNormSq (f x)

lemma jNormSq_nonneg (f : JVec X A) : 0 ≤ jNormSq f := by
  classical
  exact Finset.sum_nonneg fun x _ => qNormSq_nonneg (f x)

/-- The squared norm of a joint vector is the sum of the squared norms of its columns. -/
theorem jNormSq_eq_sum_qNormSq_col (f : JVec X A) :
    jNormSq f = ∑ a, qNormSq (fun x => f x a) := by
  simp only [jNormSq, qNormSq]
  exact Finset.sum_comm

lemma jInner_self (f : JVec X A) : jInner f f = (jNormSq f : ℂ) := by
  classical
  simp only [jInner, jNormSq, qInner_self]
  push_cast
  rfl

/-- The inner product is the trace pairing. -/
lemma jInner_eq_trace (f g : JVec X A) : jInner f g = (fᴴ * g).trace := by
  simp only [jInner, qInner_def, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- Moving an input-register operator across the inner product. -/
lemma jInner_mul_right (B : Matrix Y X ℂ) (g : JVec Y A) (f : JVec X A) :
    jInner g (B * f) = jInner (Bᴴ * g) f := by
  rw [jInner_eq_trace, jInner_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **Order lifting.** The positive-semidefinite order on input-register operators holds for
joint vectors on every finite workspace. -/
theorem jInner_le_of_le {B C : Matrix X X ℂ} (h : B ≤ C) (f : JVec X A) :
    (jInner f (B * f)).re ≤ (jInner f (C * f)).re := by
  have hpsd : (fᴴ * (C - B) * f).PosSemidef :=
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same f
  have hnn := (Complex.nonneg_iff.mp hpsd.trace_nonneg).1
  have heq : jInner f (C * f) - jInner f (B * f) = (fᴴ * (C - B) * f).trace := by
    rw [jInner_eq_trace, jInner_eq_trace, ← Matrix.trace_sub, ← Matrix.mul_sub,
      ← Matrix.sub_mul, Matrix.mul_assoc]
  have := congrArg Complex.re heq
  rw [Complex.sub_re] at this
  linarith

/-- A positive-semidefinite input-register operator has nonnegative quadratic form on every
finite workspace. -/
theorem jInner_nonneg_of_nonneg {B : Matrix X X ℂ} (h : 0 ≤ B) (f : JVec X A) :
    0 ≤ (jInner f (B * f)).re := by
  have := jInner_le_of_le h f
  simpa [jInner_eq_trace] using this

/-- A norm bound `‖Bf‖² ≤ ⟨f, Cf⟩` from the operator inequality `B†B ≤ C`, uniformly in the
workspace. -/
theorem jNormSq_mul_le {B : Matrix Y X ℂ} {C : Matrix X X ℂ} (h : Bᴴ * B ≤ C) (f : JVec X A) :
    jNormSq (B * f) ≤ (jInner f (C * f)).re := by
  have heq : jInner (B * f) (B * f) = jInner f ((Bᴴ * B) * f) := by
    rw [jInner_eq_trace, jInner_eq_trace, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h1 : jNormSq (B * f) = (jInner (B * f) (B * f)).re := by
    rw [jInner_self, Complex.ofReal_re]
  rw [h1, heq]
  exact jInner_le_of_le h f

/-- An operator-norm bound `‖Bf‖² ≤ c ‖f‖²` from `B†B ≤ c I`, uniformly in the workspace. -/
theorem jNormSq_mul_le_smul {B : Matrix Y X ℂ} {c : ℝ} (h : Bᴴ * B ≤ (c : ℂ) • (1 : Matrix X X ℂ))
    (f : JVec X A) : jNormSq (B * f) ≤ c * jNormSq f := by
  refine (jNormSq_mul_le h f).trans_eq ?_
  rw [Matrix.smul_mul, Matrix.one_mul, jInner_eq_trace, Matrix.mul_smul, Matrix.trace_smul,
    ← jInner_eq_trace, jInner_self, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ## Workspace vectors under a distribution -/

namespace FinDist

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)

/-- The **workspace vector** of `f` at input `x`: row `x` divided by `√ρ(x)`. -/
noncomputable def wvec (f : JVec ρ.Supp A) (x : ρ.Supp) : A → ℂ :=
  ((Real.sqrt (ρ.mass x))⁻¹ : ℂ) • f x

/-- The joint vector whose workspace vectors are `g`. -/
noncomputable def ofWvec (g : ρ.Supp → A → ℂ) : JVec ρ.Supp A :=
  fun x => (Real.sqrt (ρ.mass x) : ℂ) • g x

private lemma sqrt_mass_ne_zero (x : ρ.Supp) : (Real.sqrt (ρ.mass x) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr x.2).ne'

@[simp] lemma wvec_ofWvec (g : ρ.Supp → A → ℂ) (x : ρ.Supp) : ρ.wvec (ρ.ofWvec g) x = g x := by
  rw [wvec, ofWvec, smul_smul, inv_mul_cancel₀ (ρ.sqrt_mass_ne_zero x), one_smul]

@[simp] lemma ofWvec_wvec (f : JVec ρ.Supp A) : ρ.ofWvec (ρ.wvec f) = f := by
  funext x
  rw [ofWvec, wvec, smul_smul, mul_inv_cancel₀ (ρ.sqrt_mass_ne_zero x), one_smul]

private lemma qNormSq_eq_mass_mul (f : JVec ρ.Supp A) (x : ρ.Supp) :
    qNormSq (f x) = ρ.mass x * qNormSq (ρ.wvec f x) := by
  classical
  conv_lhs => rw [← ρ.ofWvec_wvec f]
  rw [ofWvec, qNormSq_smul, Complex.normSq_ofReal, Real.mul_self_sqrt (ρ.mass_nonneg x)]

/-- `‖f‖² = E_{x∼ρ} ‖fˣ‖²`. -/
theorem jNormSq_eq_sum_wvec (f : JVec ρ.Supp A) :
    jNormSq f = ∑ x : ρ.Supp, ρ.mass x * qNormSq (ρ.wvec f x) := by
  exact Finset.sum_congr rfl fun x _ => ρ.qNormSq_eq_mass_mul f x

/-- `⟨f, g⟩ = E_{x∼ρ} ⟨fˣ, gˣ⟩`. -/
theorem jInner_eq_sum_wvec (f g : JVec ρ.Supp A) :
    jInner f g = ∑ x : ρ.Supp, (ρ.mass x : ℂ) * qInner (ρ.wvec f x) (ρ.wvec g x) := by
  classical
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [← ρ.ofWvec_wvec f, ← ρ.ofWvec_wvec g]
  rw [ofWvec, ofWvec, qInner_smul_left, qInner_smul_right, Complex.star_def,
    Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (ρ.mass_nonneg x)]

/-- The squared **infinity norm**, the largest squared workspace norm. -/
noncomputable def infNormSq (f : JVec ρ.Supp A) : ℝ := ⨆ x, qNormSq (ρ.wvec f x)

theorem qNormSq_wvec_le_infNormSq (f : JVec ρ.Supp A) (x : ρ.Supp) :
    qNormSq (ρ.wvec f x) ≤ ρ.infNormSq f := by
  exact le_ciSup (Set.finite_range fun y => qNormSq (ρ.wvec f y)).bddAbove x

theorem infNormSq_le {f : JVec ρ.Supp A} {c : ℝ} (h : ∀ x, qNormSq (ρ.wvec f x) ≤ c) :
    ρ.infNormSq f ≤ c := by
  exact ciSup_le h

lemma infNormSq_nonneg (f : JVec ρ.Supp A) : 0 ≤ ρ.infNormSq f := by
  classical
  exact (qNormSq_nonneg _).trans (ρ.qNormSq_wvec_le_infNormSq f (Classical.arbitrary ρ.Supp))

/-- The Hilbert norm is at most the infinity norm. -/
theorem jNormSq_le_infNormSq (f : JVec ρ.Supp A) : jNormSq f ≤ ρ.infNormSq f := by
  calc jNormSq f = ∑ x : ρ.Supp, ρ.mass x * qNormSq (ρ.wvec f x) := ρ.jNormSq_eq_sum_wvec f
    _ ≤ ∑ x : ρ.Supp, ρ.mass x * ρ.infNormSq f :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (ρ.qNormSq_wvec_le_infNormSq f x) (ρ.mass_nonneg x)
    _ = ρ.infNormSq f := by rw [← Finset.sum_mul, ρ.sum_mass_supp, one_mul]

/-- **Rare inputs.** The inputs in a set `s` contribute at most `ρ(s) ‖f‖∞²`. -/
theorem sum_qNormSq_le_prob_mul_infNormSq (s : Finset ρ.Supp) (f : JVec ρ.Supp A) :
    ∑ x ∈ s, qNormSq (f x) ≤ ρ.prob s * ρ.infNormSq f := by
  rw [prob, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [ρ.qNormSq_eq_mass_mul f x]
  exact mul_le_mul_of_nonneg_left (ρ.qNormSq_wvec_le_infNormSq f x) (ρ.mass_nonneg x)

/-! ## The joint state of an algorithm -/

section Algorithm

variable {ι σ O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The joint state** `Ψₜ = ∑ₓ √ρ(x) |x⟩ ⊗ ψₓ,ₜ` of `A` after `t` queries, for inputs drawn
from `ρ` and observed through `read`. -/
noncomputable def jointState (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) :
    JVec ρ.Supp (QBasis ι σ W) :=
  ρ.ofWvec fun x => A.state (read x) t

@[simp] lemma wvec_jointState (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) (x : ρ.Supp) :
    ρ.wvec (ρ.jointState read A t) x = A.state (read x) t := by
  rw [jointState, wvec_ofWvec]

/-- An actual joint state is a unit vector. -/
theorem jNormSq_jointState (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) :
    jNormSq (ρ.jointState read A t) = 1 := by
  rw [jNormSq_eq_sum_wvec, ← ρ.sum_mass_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [wvec_jointState, (A.state_isQState _ _ : qNormSq _ = 1), mul_one]

/-- Every workspace vector of an actual joint state is a unit vector, so `‖Ψₜ‖∞ = 1`. -/
theorem infNormSq_jointState (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) :
    ρ.infNormSq (ρ.jointState read A t) = 1 := by
  refine le_antisymm (ρ.infNormSq_le fun x => ?_) ?_
  · rw [wvec_jointState, (A.state_isQState _ _ : qNormSq _ = 1)]
  · have := ρ.qNormSq_wvec_le_infNormSq (ρ.jointState read A t)
      (Classical.arbitrary ρ.Supp)
    rwa [wvec_jointState, (A.state_isQState _ _ : qNormSq _ = 1)] at this

end Algorithm

end FinDist

end QuantumQueryComplexity
