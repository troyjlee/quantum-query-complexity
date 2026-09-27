import QuantumQueryComplexity.Promise.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Post-composition lowers the promise adversary bound

An adversary matrix for `g ∘ f` is supported on pairs with `g (f x) ≠ g (f y)`,
hence on pairs with `f x ≠ f y` — so it is an adversary matrix for `f`, with
the same feasibility.  The suprema then compare directly:

    advPMOn read (g ∘ f) ≤ advPMOn read f.

This is the promise mirror of the `advPM_comp_le` post-processing lemma, and
it is what makes the **bit encoding** of a finite output type free on the
adversary side: each output bit is a post-composition of `f`, so its promise
adversary bound is at most that of `f`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O O' : Type*} [DecidableEq O] [DecidableEq O']

/-- An adversary matrix for a post-composition is one for the base
function. -/
lemma IsAdvMatrixOn.of_comp {f : X → O} {g : O → O'} {Γ : Matrix X X ℝ}
    (h : IsAdvMatrixOn (fun x => g (f x)) Γ) : IsAdvMatrixOn f Γ :=
  ⟨h.1, fun x y hxy => h.2 x y (by show g (f x) = g (f y); rw [hxy])⟩

/-- Determinacy transfers to any post-composition. -/
lemma det_comp {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (g : O → O') :
    ∀ x y, read x = read y → g (f x) = g (f y) :=
  fun x y hxy => by rw [hdet x y hxy]

/-- **Post-composition lowers the promise adversary bound.** -/
theorem advPMOn_comp_le {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (g : O → O') :
    advPMOn read (fun x => g (f x)) ≤ advPMOn read f := by
  refine csSup_le (advPMOn_set_nonempty read _) ?_
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact le_advPMOn hdet h1.of_comp h2

/-! ## Relabelling the answers

An injective relabelling of the oracle's answers changes nothing: the masks
`advDOn` only ask whether two promise inputs are distinguished at `i`. -/

variable {σ' : Type*} [DecidableEq σ']

lemma advDOn_comp_injective {φ : σ → σ'} (hφ : Function.Injective φ)
    (read : X → ι → σ) (i : ι) :
    advDOn (fun x j => φ (read x j)) i = advDOn read i := by
  ext x y
  rw [advDOn_apply, advDOn_apply]
  refine if_congr ?_ rfl rfl
  exact ⟨fun h => hφ h, fun h => congrArg φ h⟩

/-- **The adversary bound is invariant under injective relabelling of the
answers.** -/
theorem advPMOn_comp_injective {φ : σ → σ'} (hφ : Function.Injective φ)
    (read : X → ι → σ) (f : X → O) :
    advPMOn (fun x j => φ (read x j)) f = advPMOn read f := by
  have hset : {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ
        ∧ (∀ i, ‖Γ ⊙ advDOn (fun x j => φ (read x j)) i‖ ≤ 1) ∧ r = ‖Γ‖}
      = {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ
        ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ r = ‖Γ‖} := by
    ext r
    constructor
    · rintro ⟨Γ, h1, h2, rfl⟩
      exact ⟨Γ, h1, fun i => by rw [← advDOn_comp_injective hφ read i]; exact h2 i,
        rfl⟩
    · rintro ⟨Γ, h1, h2, rfl⟩
      exact ⟨Γ, h1, fun i => by rw [advDOn_comp_injective hφ read i]; exact h2 i,
        rfl⟩
  rw [advPMOn, advPMOn, hset]

end QuantumQueryComplexity
