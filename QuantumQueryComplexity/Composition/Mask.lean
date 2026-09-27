import QuantumQueryComplexity.Composition.NormCompose
import QuantumQueryComplexity.Promise.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The Hadamard-mask identity (HLŠ p. 20 / BL Eq. (8) + Claim 23)

Masking the composed matrix by a difference matrix produces another composed
matrix: the outer matrix is masked by `advD p` and the inner matrix in slot `p`
is masked by the inner difference matrix at `q`:

  `composeE e g Γf M ⊙ advDOn (composeReadE e innerRead) (p, q)
     = composeE e g (Γf ⊙ advD p)
         (Function.update M p (M p ⊙ advDOn innerRead q))`

This is an exact entrywise identity: in every configuration where the
`‖·‖ • 1` part of a hat matrix could differ between the two sides, either the
outer factor `(Γf ⊙ advD p)` or a Kronecker delta vanishes first.

## The mask is a promise mask

The composed inputs form an arbitrary finite type `Z ≃ (α → Y)`, and a query
`(p, q)` reads coordinate `q` of the `p`-th block *through the inner
observation map* `innerRead : Y → β → σ` (`composeReadE`).  So the relevant
difference matrix is `advDOn`, evaluated on the inner observations.

Neither delicate step needs `innerRead` to be injective.  In the "queries
agree" branch the `p`-slot hat entry vanishes because the masked inner entry
vanishes *and* the two blocks have different `g`-values, hence are distinct
blocks; in the "queries differ" branch the blocks are distinct because a single
`congrArg` turns differing reads into differing blocks.

The original cube statement `compose_hadamard_advD` is recovered as the
instance `e := cubeBlocks α β` with `innerRead` the identity, since
`advDOn (fun u => u) q` is `advD q` definitionally.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma IsAdvMatrix.hadamard_advD {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → Bool} {Γ : Matrix (ι → Bool) (ι → Bool) ℝ}
    (h : IsAdvMatrix f Γ) (i : ι) : IsAdvMatrix f (Γ ⊙ advD i) :=
  ⟨h.isHermitian.hadamard (advD_isHermitian i), fun x y hxy => by
    rw [Matrix.hadamard_apply, h.apply_eq_zero hxy, zero_mul]⟩

/-! ## The mask identity over an abstract block decomposition -/

section General

variable {α β σ Y Z : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [DecidableEq σ] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma IsAdvCol.hadamard_advDOn {g : Y → Bool} {N : Matrix Y Y ℝ}
    (h : IsAdvCol g N) (innerRead : Y → β → σ) (q : β) :
    IsAdvCol g (N ⊙ advDOn innerRead q) :=
  ⟨h.isHermitian.hadamard (advDOn_isHermitian innerRead q), fun u v huv => by
    rw [Matrix.hadamard_apply, h.apply_eq_zero huv, zero_mul]⟩

/-- The observation map of a composed input: the query `(p, q)` reads
coordinate `q` of the `p`-th block, through the inner observation map. -/
def composeReadE (e : Z ≃ (α → Y)) (innerRead : Y → β → σ) :
    Z → (α × β) → σ :=
  fun z pq => innerRead (sliceE e z pq.1) pq.2

@[simp] lemma composeReadE_apply (e : Z ≃ (α → Y)) (innerRead : Y → β → σ)
    (z : Z) (pq : α × β) :
    composeReadE e innerRead z pq = innerRead (sliceE e z pq.1) pq.2 := rfl

/-- The mask identity. -/
theorem composeE_hadamard_advDOn (e : Z ≃ (α → Y)) (innerRead : Y → β → σ)
    (g : α → Y → Bool) (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix Y Y ℝ) (hM : ∀ i, IsAdvCol (g i) (M i)) (p : α) (q : β) :
    composeE e g Γf M ⊙ advDOn (composeReadE e innerRead) (p, q)
      = composeE e g (Γf ⊙ advD p)
          (Function.update M p (M p ⊙ advDOn innerRead q)) := by
  ext x y
  rw [Matrix.hadamard_apply, composeE_apply, composeE_apply, advDOn_apply,
    composeReadE_apply, composeReadE_apply]
  by_cases hpq : innerRead (sliceE e x p) q = innerRead (sliceE e y p) q
  · rw [if_pos hpq, mul_zero]
    by_cases hcol : g p (sliceE e x p) = g p (sliceE e y p)
    · rw [hadamard_advD_apply,
        if_pos (show tildeE e g x p = tildeE e g y p from hcol), zero_mul]
    · have hhat : hat (Function.update M p (M p ⊙ advDOn innerRead q) p)
          (sliceE e x p) (sliceE e y p) = 0 := by
        rw [Function.update_self, hat_apply, hadamard_advDOn_apply,
          if_pos hpq,
          if_neg (show ¬sliceE e x p = sliceE e y p from fun hc =>
            hcol (by rw [hc]))]
        ring
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hhat, zero_mul,
        mul_zero]
  · rw [if_neg hpq, mul_one]
    have hslice_ne : sliceE e x p ≠ sliceE e y p := fun hc => hpq (by rw [hc])
    by_cases hcol : g p (sliceE e x p) = g p (sliceE e y p)
    · rw [hadamard_advD_apply,
        if_pos (show tildeE e g x p = tildeE e g y p from hcol), zero_mul]
      have hhat : hat (M p) (sliceE e x p) (sliceE e y p) = 0 := by
        rw [hat_apply, (hM p).apply_eq_zero hcol, if_neg hslice_ne]
        ring
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hhat, zero_mul,
        mul_zero]
    · rw [hadamard_advD_apply,
        if_neg (show ¬tildeE e g x p = tildeE e g y p from hcol),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ p),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
      have hp_eq : hat (Function.update M p (M p ⊙ advDOn innerRead q) p)
          (sliceE e x p) (sliceE e y p)
          = hat (M p) (sliceE e x p) (sliceE e y p) := by
        rw [Function.update_self, hat_apply, hat_apply, hadamard_advDOn_apply,
          if_neg hpq, if_neg hslice_ne]
        ring
      have hP : ∏ i ∈ Finset.univ.erase p,
          hat (Function.update M p (M p ⊙ advDOn innerRead q) i)
            (sliceE e x i) (sliceE e y i)
          = ∏ i ∈ Finset.univ.erase p,
              hat (M i) (sliceE e x i) (sliceE e y i) :=
        Finset.prod_congr rfl fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hp_eq, hP]

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The mask identity, cube form. -/
theorem compose_hadamard_advD (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) (p : α) (q : β) :
    compose g Γf M ⊙ advD (p, q)
      = compose g (Γf ⊙ advD p) (Function.update M p (M p ⊙ advD q)) :=
  composeE_hadamard_advDOn (cubeBlocks α β) (fun u => u) g Γf M
    (fun i => (hM i).isAdvCol) p q

end Cube

end QuantumQueryComplexity
