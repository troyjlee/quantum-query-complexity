import QuantumQueryComplexity.Composition.Main
set_option linter.style.header false

/-!
# The weighted composition lower bound

The composition machinery now allows a *different* inner function in each
block (`compose g Γf M` with `g : α → (β → Bool) → Bool`), which is what the
cost/weighted version of the adversary composition theorem needs.

`advPM_composeFunFam_ge` is the general weighted statement: if the outer
witness `Γf` satisfies

  `‖Γf ⊙ D_p‖ · V ≤ ‖Γf‖ · ‖M p‖`  for every outer coordinate `p`,

— i.e. `Γf` certifies the value `V` for `f` *with costs* `‖M p‖` — and each
inner witness `M i` is feasible, then `ADV±(f ∘ (g_1, …, g_k)) ≥ V`.

This is HLŠ Theorem 13 (`ADV±_α(h) ≥ ADV±_β(f)` with `β_i = ADV±(g_i)`) in
witness form: the cost vector enters as the norms `‖M p‖` of the inner
witnesses, so no separate `ADV±_α` definition is needed.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **The weighted composition lower bound.** -/
theorem advPM_composeFunFam_ge {f : (α → Bool) → Bool}
    {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hf : IsAdvMatrix f Γf) (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    {V : ℝ} (hVpos : 0 < V) (hΓfpos : 0 < ‖Γf‖)
    (hV : ∀ p, ‖Γf ⊙ advD p‖ * V ≤ ‖Γf‖ * ‖M p‖) :
    V ≤ advPM (composeFunFam f g) := by
  classical
  have hCpos : 0 < ∏ i, ‖M i‖ := Finset.prod_pos fun i _ => hMpos i
  have hcpos : 0 < ‖Γf‖ * (∏ i, ‖M i‖) / V := by positivity
  have hΓh : IsAdvMatrix (composeFunFam f g) (compose g Γf M) :=
    isAdvMatrix_compose hf hM
  have hmask : ∀ ℓ : α × β,
      ‖compose g Γf M ⊙ advD ℓ‖ ≤ ‖Γf‖ * (∏ i, ‖M i‖) / V := by
    rintro ⟨p, q⟩
    rw [compose_hadamard_advD g Γf M hM p q]
    have hshape : ∀ i, IsAdvMatrix (g i)
        (Function.update M p (M p ⊙ advD q) i) := by
      intro i
      by_cases hip : i = p
      · subst hip
        rw [Function.update_self]
        exact (hM i).hadamard_advD q
      · rw [Function.update_of_ne hip]
        exact hM i
    refine (norm_compose_le
      (hf.isHermitian.hadamard (advD_isHermitian p)) hshape).trans ?_
    -- split the product at `p`
    have hprod : ∏ i, ‖Function.update M p (M p ⊙ advD q) i‖
        = ‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have herase : (∏ i ∈ Finset.univ.erase p, ‖M i‖) * ‖M p‖
        = ∏ i, ‖M i‖ := by
      rw [mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun i => ‖M i‖)
        (Finset.mem_univ p)
    have hepos : 0 < ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
      Finset.prod_pos fun i _ => hMpos i
    rw [hprod]
    -- `‖Γf ⊙ D_p‖ * (‖M p ⊙ D_q‖ * ∏_{i≠p}) ≤ ‖Γf‖ * ∏ / V`
    rw [le_div_iff₀ hVpos]
    calc ‖Γf ⊙ advD p‖ * (‖M p ⊙ advD q‖ *
          ∏ i ∈ Finset.univ.erase p, ‖M i‖) * V
        ≤ ‖Γf ⊙ advD p‖ * (1 * ∏ i ∈ Finset.univ.erase p, ‖M i‖) * V := by
          have h1 : ‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖
              ≤ 1 * ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
            mul_le_mul_of_nonneg_right (hMfeas p q) hepos.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) hVpos.le
      _ = (‖Γf ⊙ advD p‖ * V) * ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by ring
      _ ≤ (‖Γf‖ * ‖M p‖) * ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
          mul_le_mul_of_nonneg_right (hV p) hepos.le
      _ = ‖Γf‖ * ∏ i, ‖M i‖ := by rw [← herase]; ring
  have hnorm : ‖compose g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
    norm_compose hf.isHermitian hM
  have h := norm_div_le_advPM hΓh hmask hcpos
  rw [hnorm] at h
  have hsimp : ‖Γf‖ * (∏ i, ‖M i‖) / (‖Γf‖ * (∏ i, ‖M i‖) / V) = V := by
    field_simp
  rwa [hsimp] at h

end QuantumQueryComplexity
