import QuantumQueryComplexity.Basic
import QuantumQueryComplexity.SchurMultiplier
import QuantumQueryComplexity.Bipartite
set_option linter.style.header false

/-!
# The composed adversary matrix (hat formulation)

Following Belovs–Lee (arXiv:2004.06439, Definitions 17 and 19), the composed
adversary matrix for `h = f ∘ gᵏ` is built from an outer matrix `Γf` and inner
matrices `M i` via `hat N = N + ‖N‖ • 1`:

  `compose g Γf M x y = Γf (tilde g x) (tilde g y) * ∏ i, hat (M i) (x·ᵢ) (y·ᵢ)`

For a g-shaped `N` (symmetric, vanishing on pairs with `g u = g v`), `hat N`
agrees entrywise with the color-block convention of HLŠ Definition 6:
same-color blocks are `‖N‖·I`, different-color blocks are `N`.

## The block decomposition is abstract

The inner inputs are **not** assumed to form a Boolean cube.  Everything below
is stated for a composed input type `Z` equipped with an equivalence
`e : Z ≃ (α → Y)` onto tuples of inner inputs drawn from an arbitrary finite
type `Y`, with a colouring `g : α → Y → Bool`.

This permits composition of *promise* problems whose inner inputs range over a
subtype rather than a cube. The spectral content never sees the cube: the two
places two-valuedness is used are the colouring's **output** and the outer cube
`α → Bool`, and both survive.

The original cube statements are recovered verbatim as the instance
`e := cubeBlocks α β`, so no downstream file changes.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma isHermitian_apply_symm {n : Type*} {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (a b : n) : A a b = A b a := by
  conv_lhs => rw [← hA.eq]
  simp [Matrix.conjTranspose_apply]

/-! ## The hat matrix -/

/-- BL Definition 17 in additive form: `hat N = N + ‖N‖ • 1`. -/
noncomputable def hat {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) : Matrix n n ℝ :=
  N + ‖N‖ • (1 : Matrix n n ℝ)

lemma hat_apply {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℝ)
    (u v : n) : hat N u v = N u v + ‖N‖ * (if u = v then 1 else 0) := by
  simp [hat, Matrix.one_apply]

lemma hat_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {N : Matrix n n ℝ} (hN : N.IsHermitian) : (hat N).IsHermitian :=
  hN.add (Matrix.isHermitian_one.smul (star_trivial _))

/-! ## Composition over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The `i`-th block of a composed input. -/
def sliceE (e : Z ≃ (α → Y)) (z : Z) (i : α) : Y := e z i

/-- The vector of inner-function values of a composed input. -/
def tildeE (e : Z ≃ (α → Y)) (g : α → Y → Bool) (z : Z) : α → Bool :=
  fun i => g i (sliceE e z i)

@[simp] lemma sliceE_apply (e : Z ≃ (α → Y)) (z : Z) (i : α) :
    sliceE e z i = e z i := rfl

@[simp] lemma tildeE_apply (e : Z ≃ (α → Y)) (g : α → Y → Bool) (z : Z)
    (i : α) : tildeE e g z i = g i (sliceE e z i) := rfl

/-- BL Definition 19 over an abstract block decomposition. -/
noncomputable def composeE (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) :
    Matrix Z Z ℝ :=
  Matrix.of fun x y =>
    Γf (tildeE e g x) (tildeE e g y) * ∏ i, hat (M i) (sliceE e x i) (sliceE e y i)

@[simp] lemma composeE_apply (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) (x y : Z) :
    composeE e g Γf M x y
      = Γf (tildeE e g x) (tildeE e g y)
        * ∏ i, hat (M i) (sliceE e x i) (sliceE e y i) := rfl

lemma composeE_isHermitian (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    {Γf : Matrix (α → Bool) (α → Bool) ℝ} {M : α → Matrix Y Y ℝ}
    (hΓf : Γf.IsHermitian) (hM : ∀ i, (M i).IsHermitian) :
    (composeE e g Γf M).IsHermitian := by
  show (composeE e g Γf M)ᴴ = composeE e g Γf M
  ext x y
  simp only [Matrix.conjTranspose_apply, composeE_apply, star_trivial]
  rw [isHermitian_apply_symm hΓf (tildeE e g y) (tildeE e g x)]
  congr 1
  exact Finset.prod_congr rfl fun i _ =>
    isHermitian_apply_symm (hat_isHermitian (hM i)) _ _

end General

/-! ## The cube instance

The original statements, recovered by taking the block decomposition to be the
currying equivalence. -/

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The block decomposition of a Boolean cube into `α` blocks of shape `β`. -/
def cubeBlocks (α β : Type*) : ((α × β) → Bool) ≃ (α → (β → Bool)) :=
  Equiv.curry α β Bool

/-- The `i`-th block of a composed input. -/
def slice (x : (α × β) → Bool) (i : α) : β → Bool := sliceE (cubeBlocks α β) x i

/-- The vector of inner-function values of a composed input. -/
def tilde (g : α → (β → Bool) → Bool) (x : (α × β) → Bool) : α → Bool :=
  tildeE (cubeBlocks α β) g x

/-- The constant family of inner functions (the uniform case). -/
abbrev constFam (g : (β → Bool) → Bool) : α → (β → Bool) → Bool := fun _ => g

@[simp] lemma slice_apply (x : (α × β) → Bool) (i : α) (j : β) :
    slice x i j = x (i, j) := rfl

@[simp] lemma tilde_apply (g : α → (β → Bool) → Bool) (x : (α × β) → Bool)
    (i : α) : tilde g x i = g i (slice x i) := rfl

/-- BL Definition 19, uniform-alphabet form: the composed matrix. -/
noncomputable def compose (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) :
    Matrix ((α × β) → Bool) ((α × β) → Bool) ℝ :=
  composeE (cubeBlocks α β) g Γf M

@[simp] lemma compose_apply (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) (x y : (α × β) → Bool) :
    compose g Γf M x y
      = Γf (tilde g x) (tilde g y) * ∏ i, hat (M i) (slice x i) (slice y i) :=
  rfl

lemma compose_isHermitian (g : α → (β → Bool) → Bool)
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hΓf : Γf.IsHermitian) (hM : ∀ i, (M i).IsHermitian) :
    (compose g Γf M).IsHermitian :=
  composeE_isHermitian _ g hΓf hM

end QuantumQueryComplexity
