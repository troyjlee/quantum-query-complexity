import QuantumQueryComplexity.Composition.Hat
set_option linter.style.header false

/-!
# The b-sum form of the composed matrix

The first rewriting lemma (`composeE_apply_sum`): the entry
`composeE e g Γf M x y` can be written as a sum over all outer inputs
`b : α → Bool`, with guards `if g i (sliceE e y i) = b i` making the
`b = tildeE e g y` fiber automatic.  This eliminates the non-factoring
occurrence `Γf x̃ ỹ` before any sum/product interchange.

As in `Hat.lean` the block decomposition is abstract; the cube statement is the
instance at `cubeBlocks`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma composeE_apply_sum (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) (x y : Z) :
    composeE e g Γf M x y
      = ∑ b : α → Bool, Γf (tildeE e g x) b *
          ∏ i, (if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0) := by
  symm
  calc ∑ b : α → Bool, Γf (tildeE e g x) b *
        ∏ i, (if g i (sliceE e y i) = b i
          then hat (M i) (sliceE e x i) (sliceE e y i) else 0)
      = Γf (tildeE e g x) (tildeE e g y) *
        ∏ i, (if g i (sliceE e y i) = tildeE e g y i
          then hat (M i) (sliceE e x i) (sliceE e y i) else 0) := by
        refine Finset.sum_eq_single (tildeE e g y) ?_ ?_
        · intro b _ hb
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
          have hzero : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) = 0 :=
            if_neg fun h => hi (h.symm.trans (tildeE_apply e g y i).symm)
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = composeE e g Γf M x y := by
        rw [composeE_apply]
        congr 1
        exact Finset.prod_congr rfl fun i _ => if_pos rfl

end General

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma compose_apply_sum (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) (x y : (α × β) → Bool) :
    compose g Γf M x y
      = ∑ b : α → Bool, Γf (tilde g x) b *
          ∏ i, (if g i (slice y i) = b i
            then hat (M i) (slice x i) (slice y i) else 0) :=
  composeE_apply_sum (cubeBlocks α β) g Γf M x y

end QuantumQueryComplexity
