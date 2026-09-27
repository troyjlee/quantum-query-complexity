import QuantumQueryComplexity.Composition.Mask
set_option linter.style.header false

/-!
# The composition theorem for the negative-weight adversary bound

**Main result** (`advPM_mul_le_advPM_composeFun`): for total Boolean functions
`f : (α → Bool) → Bool` and `g : (β → Bool) → Bool`,

  `ADV±(f) * ADV±(g) ≤ ADV±(f ∘ gᵏ)`

— the composition lower bound of Høyer–Lee–Špalek (quant-ph/0611054,
Theorem 13, uniform unit-cost case) in the formulation of Belovs–Lee
(arXiv:2004.06439, Theorem 1, `≥` direction).  The iterated corollary
`advPM_pow_le_advPM_iterFun` gives `ADV±(f)^(d+1) ≤ ADV±(f^{∘(d+1)})`.

Proof: for feasible witnesses `Γf, Γg`, the composed matrix
`Γh = compose (constFam g) Γf (fun _ => Γg)` is an adversary matrix for `f ∘ gᵏ` with
`‖Γh‖ ≥ ‖Γf‖ ‖Γg‖^k` (Lemma 16, `≥`) and
`‖Γh ⊙ advD (p,q)‖ ≤ ‖Γg‖^(k-1)` (mask identity + Lemma 16, `≤`), so the
un-normalized witness lemma yields `advPM (f ∘ gᵏ) ≥ ‖Γf‖ ‖Γg‖`; two
supremum passes finish the proof.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The composed function `f ∘ gᵏ` on inputs indexed by `α × β`. -/
def composeFunFam (f : (α → Bool) → Bool) (g : α → (β → Bool) → Bool) :
    ((α × β) → Bool) → Bool :=
  fun x => f (tilde g x)

/-- The composed function `f ∘ gᵏ` on inputs indexed by `α × β`. -/
def composeFun (f : (α → Bool) → Bool) (g : (β → Bool) → Bool) :
    ((α × β) → Bool) → Bool :=
  composeFunFam f (constFam g)

lemma isAdvMatrix_compose {f : (α → Bool) → Bool}
    {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hf : IsAdvMatrix f Γf) (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    IsAdvMatrix (composeFunFam f g) (compose g Γf M) := by
  refine ⟨compose_isHermitian g hf.isHermitian fun i => (hM i).isHermitian, ?_⟩
  intro x y hxy
  rw [compose_apply, hf.apply_eq_zero hxy, zero_mul]

/-- The masked norm bound for the composed witness (T1). -/
lemma norm_compose_mask {g : (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {Γg : Matrix (β → Bool) (β → Bool) ℝ}
    (hf : Γf.IsHermitian) (hg : IsAdvMatrix g Γg) (p : α) (q : β) :
    ‖compose (constFam g) Γf (fun _ => Γg) ⊙ advD (p, q)‖
      ≤ ‖Γf ⊙ advD p‖ *
        (‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1)) := by
  rw [compose_hadamard_advD (constFam g) Γf (fun _ => Γg) (fun _ => hg) p q]
  have hshape : ∀ i, IsAdvMatrix (constFam g i)
      (Function.update (fun _ : α => Γg) p (Γg ⊙ advD q) i) := by
    intro i
    by_cases hip : i = p
    · rw [hip, Function.update_self]
      exact hg.hadamard_advD q
    · rw [Function.update_of_ne hip]
      exact hg
  refine (norm_compose_le (hf.hadamard (advD_isHermitian p)) hshape).trans ?_
  have hprod : ∏ i, ‖Function.update (fun _ : α => Γg) p (Γg ⊙ advD q) i‖
      = ‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
    congr 1
    rw [Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)],
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
  rw [hprod]

/-- **The composition theorem** (HLŠ Theorem 13, uniform unit-cost case;
BL Theorem 1, `≥` direction): `ADV±(f) * ADV±(g) ≤ ADV±(f ∘ gᵏ)`. -/
theorem advPM_mul_le_advPM_composeFun (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM f * advPM g ≤ advPM (composeFun f g) := by
  classical
  have hkey : ∀ Γf, IsAdvMatrix f Γf → (∀ i, ‖Γf ⊙ advD i‖ ≤ 1) →
      ∀ Γg, IsAdvMatrix g Γg → (∀ j, ‖Γg ⊙ advD j‖ ≤ 1) →
      ‖Γf‖ * ‖Γg‖ ≤ advPM (composeFun f g) := by
    intro Γf hf1 hf2 Γg hg1 hg2
    rcases eq_or_lt_of_le (norm_nonneg Γf) with hf0 | hΓfpos
    · rw [← hf0, zero_mul]
      exact advPM_nonneg _
    rcases eq_or_lt_of_le (norm_nonneg Γg) with hg0 | hΓgpos
    · rw [← hg0, mul_zero]
      exact advPM_nonneg _
    -- a nonzero adversary matrix for f forces α to be inhabited
    have hα : Nonempty α := by
      have hΓf0 : Γf ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hΓfpos
        exact lt_irrefl 0 hΓfpos
      have hentry : ∃ x y, Γf x y ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hΓf0 (Matrix.ext fun x y => by
          rw [hc x y, Matrix.zero_apply])
      obtain ⟨x, y, hxy⟩ := hentry
      have hfxy : f x ≠ f y := fun h => hxy (hf1.apply_eq_zero h)
      have hxyne : x ≠ y := fun h => hfxy (by rw [h])
      obtain ⟨i, -⟩ := Function.ne_iff.mp hxyne
      exact ⟨i⟩
    haveI := hα
    have hk : Fintype.card α - 1 + 1 = Fintype.card α :=
      Nat.succ_pred_eq_of_pos Fintype.card_pos
    -- the composed witness
    have hΓh_adv : IsAdvMatrix (composeFun f g)
        (compose (constFam g) Γf fun _ => Γg) :=
      isAdvMatrix_compose hf1 fun _ => hg1
    have hmask : ∀ ℓ : α × β,
        ‖compose (constFam g) Γf (fun _ => Γg) ⊙ advD ℓ‖
          ≤ ‖Γg‖ ^ (Fintype.card α - 1) := by
      rintro ⟨p, q⟩
      refine (norm_compose_mask hf1.isHermitian hg1 p q).trans ?_
      calc ‖Γf ⊙ advD p‖ * (‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1))
          ≤ 1 * (1 * ‖Γg‖ ^ (Fintype.card α - 1)) :=
            mul_le_mul (hf2 p)
              (mul_le_mul (hg2 q) le_rfl (by positivity) zero_le_one)
              (by positivity) zero_le_one
        _ = ‖Γg‖ ^ (Fintype.card α - 1) := by ring
    have hfinal := norm_div_le_advPM hΓh_adv hmask (pow_pos hΓgpos _)
    have hlow : ‖Γf‖ * ‖Γg‖
        ≤ ‖compose (constFam g) Γf (fun _ => Γg)‖ / ‖Γg‖ ^ (Fintype.card α - 1) := by
      rw [le_div_iff₀ (pow_pos hΓgpos _)]
      calc ‖Γf‖ * ‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)
          = ‖Γf‖ * (‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)) := mul_assoc _ _ _
        _ = ‖Γf‖ * ‖Γg‖ ^ (Fintype.card α - 1 + 1) := by rw [← pow_succ']
        _ = ‖Γf‖ * ‖Γg‖ ^ (Fintype.card α) := by rw [hk]
        _ ≤ ‖compose (constFam g) Γf (fun _ => Γg)‖ := by
            have h := le_norm_compose (g := constFam g) hf1.isHermitian fun _ : α => hg1
            rw [Finset.prod_const, Finset.card_univ] at h
            exact h
    exact hlow.trans hfinal
  -- two supremum passes
  rcases eq_or_lt_of_le (advPM_nonneg g) with hg0 | hg0
  · rw [← hg0, mul_zero]
    exact advPM_nonneg _
  rw [← le_div_iff₀ hg0]
  refine advPM_le fun Γf hf1 hf2 => ?_
  rw [le_div_iff₀ hg0]
  rcases eq_or_lt_of_le (norm_nonneg Γf) with hf0 | hf0
  · rw [← hf0, zero_mul]
    exact advPM_nonneg _
  rw [mul_comm, ← le_div_iff₀ hf0]
  refine advPM_le fun Γg hg1 hg2 => ?_
  rw [le_div_iff₀ hf0, mul_comm]
  exact hkey Γf hf1 hf2 Γg hg1 hg2

/-! ## The iterated corollary -/

/-- Index types for iterated composition: `α`, `α × α`, `α × (α × α)`, … -/
def iterIdx (α : Type*) : ℕ → Type _
  | 0 => α
  | d + 1 => α × iterIdx α d

instance iterIdx.fintype (α : Type*) [Fintype α] :
    (d : ℕ) → Fintype (iterIdx α d)
  | 0 => ‹Fintype α›
  | d + 1 =>
      letI := iterIdx.fintype α d
      inferInstanceAs (Fintype (α × iterIdx α d))

instance iterIdx.decEq (α : Type*) [DecidableEq α] :
    (d : ℕ) → DecidableEq (iterIdx α d)
  | 0 => ‹DecidableEq α›
  | d + 1 =>
      letI := iterIdx.decEq α d
      inferInstanceAs (DecidableEq (α × iterIdx α d))

/-- Iterated composition `f^{∘(d+1)}`. -/
def iterFun (f : (α → Bool) → Bool) : (d : ℕ) → ((iterIdx α d → Bool) → Bool)
  | 0 => f
  | d + 1 => composeFun f (iterFun f d)

/-- Iterated composition corollary: `ADV±(f)^(d+1) ≤ ADV±(f^{∘(d+1)})`. -/
theorem advPM_pow_le_advPM_iterFun (f : (α → Bool) → Bool) (d : ℕ) :
    advPM f ^ (d + 1) ≤ advPM (iterFun f d) := by
  induction d with
  | zero =>
      show advPM f ^ 1 ≤ advPM f
      rw [pow_one]
  | succ d ih =>
      calc advPM f ^ (d + 2) = advPM f * advPM f ^ (d + 1) := by ring
        _ ≤ advPM f * advPM (iterFun f d) :=
            mul_le_mul_of_nonneg_left ih (advPM_nonneg f)
        _ ≤ advPM (iterFun f (d + 1)) :=
            advPM_mul_le_advPM_composeFun f (iterFun f d)

end QuantumQueryComplexity
