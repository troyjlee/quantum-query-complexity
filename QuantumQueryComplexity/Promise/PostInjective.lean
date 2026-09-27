import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Injective postprocessing preserves the adversary bound

`advPMOn_comp_le` (`Promise/Post.lean`) says classical postprocessing of the
output can only lower the adversary bound.  When the postprocessing is
**injective** nothing is lost: an adversary matrix for `f` vanishes exactly
where `f` agrees, and `g ∘ f` agrees exactly where `f` does.  So
`advPMOn read (g ∘ f) = advPMOn read f`, and for total functions
`advPM (g ∘ f) = advPM f`.  This is the device for moving a lower bound
proved on a convenient encoding of the output (say a one-coordinate power
`Unit → M`) to the output type itself.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O O' : Type*}

lemma isAdvMatrixOn_comp_injective {g : O → O'} (hg : Function.Injective g) (f : X → O)
    (Γ : Matrix X X ℝ) : IsAdvMatrixOn (g ∘ f) Γ ↔ IsAdvMatrixOn f Γ := by
  unfold IsAdvMatrixOn
  simp only [Function.comp, hg.eq_iff]

/-- **Injective postprocessing preserves the promise adversary bound.** -/
theorem advPMOn_postcomp_injective {g : O → O'} (hg : Function.Injective g)
    (read : X → ι → σ) (f : X → O) :
    advPMOn read (g ∘ f) = advPMOn read f := by
  unfold advPMOn
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, isAdvMatrixOn_comp_injective hg]

/-- **Injective postprocessing preserves the adversary bound.** -/
theorem advPM_postcomp_injective [DecidableEq O] [DecidableEq O'] {g : O → O'}
    (hg : Function.Injective g) (f : (ι → σ) → O) : advPM (g ∘ f) = advPM f := by
  rw [← advPMOn_id, ← advPMOn_id]
  exact advPMOn_postcomp_injective hg _ f

end QuantumQueryComplexity
