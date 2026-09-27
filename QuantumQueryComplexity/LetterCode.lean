import QuantumQueryComplexity.HasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.haveILetI false

/-!
# Duals pull back along letter codes

A **letter code** `E : σ → (κ → σ')` replaces every letter of a word by a block
of `|κ|` letters (a virtual query costs one original query).  A dual for `F` on
the coded words gives a dual for `F ∘ code` on the original words at cost
`√|σ'|` times larger (`hasDual_letterCode`): concatenate the block's vectors,
tensored with the letter-inequality gadget `⟨e_a, ∑_{c ≠ b} e_c⟩ = [a ≠ b]`, which
removes exactly the block terms where the coded letters agree, so the original
constraint is reproduced.  The code need not be injective: a non-injective
letter map is the case `κ = Unit`.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {σ' : Type} [Fintype σ'] [DecidableEq σ']
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {O : Type} [DecidableEq O]

/-- The coded word. -/
def codeWord (E : σ → κ → σ') (x : ι → σ) : ι × κ → σ' := fun p => E (x p.1) p.2

/-- **A dual pulls back along a letter code**, at cost `√|σ'|·c`. -/
theorem hasDual_letterCode [Nonempty σ'] (E : σ → κ → σ') {F : (ι × κ → σ') → O} {c : ℝ}
    (_hc : 0 ≤ c) (h : HasDual F c) :
    HasDual (fun x : ι → σ => F (codeWord E x)) (Real.sqrt (Fintype.card σ') * c) := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  letI := hK
  -- the balancing scale `s` with `s² = √|σ'|`
  set t : ℝ := Real.sqrt (Fintype.card σ') with ht
  set s : ℝ := Real.sqrt t with hs
  have hcard : (0 : ℝ) < Fintype.card σ' := by exact_mod_cast Fintype.card_pos
  have ht0 : 0 < t := Real.sqrt_pos.2 hcard
  have htt : t * t = Fintype.card σ' := Real.mul_self_sqrt hcard.le
  have hs0 : 0 < s := Real.sqrt_pos.2 ht0
  have hss : s * s = t := Real.mul_self_sqrt ht0.le
  -- `U x i (k, j, a) = s · u_{code x,(i,k),j} · [a = coded letter]`,
  -- `V y i (k, j, a) = s⁻¹ · v_{code y,(i,k),j} · [a ≠ coded letter]`
  let U : (ι → σ) → ι → κ × K × σ' → ℝ := fun x i q =>
    if q.2.2 = E (x i) q.1 then s * P.u (codeWord E x) (i, q.1) q.2.1 else 0
  let V : (ι → σ) → ι → κ × K × σ' → ℝ := fun y i q =>
    if q.2.2 = E (y i) q.1 then 0 else P.v (codeWord E y) (i, q.1) q.2.1 / s
  have hinner : ∀ x y i, ∑ q : κ × K × σ', U x i q * V y i q
      = ∑ k : κ, if E (x i) k = E (y i) k then 0
          else ∑ j : K, P.u (codeWord E x) (i, k) j * P.v (codeWord E y) (i, k) j := by
    intro x y i
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type]
    by_cases hk : E (x i) k = E (y i) k
    · rw [if_pos hk]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => ?_
      simp only [U, V]
      by_cases ha : a = E (x i) k
      · rw [if_pos ha, if_pos (ha.trans hk), mul_zero]
      · rw [if_neg ha, zero_mul]
    · rw [if_neg hk]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (E (x i) k)]
      · simp only [U, V, if_true, if_neg hk]
        field_simp
      · intro a _ ha
        simp only [U, V]
        rw [if_neg ha, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hconstr : ∀ x y : ι → σ,
      (∑ i, if x i = y i then 0 else ∑ q, U x i q * V y i q)
        = if F (codeWord E x) = F (codeWord E y) then 0 else 1 := by
    intro x y
    have hP := P.constraint (codeWord E x) (codeWord E y)
    rw [Fintype.sum_prod_type] at hP
    rw [← hP]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hxy : x i = y i
    · rw [if_pos hxy]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [if_pos]
      simp only [codeWord, hxy]
    · rw [if_neg hxy, hinner]
      rfl
  let D : DualPair (κ × K × σ') (fun x : ι → σ => F (codeWord E x)) :=
    { u := U, v := V, constraint := hconstr }
  refine hasDual_of_dualPair D ⟨fun x => ?_, fun x => ?_⟩
  · -- the `U`-load is `s²·(load of u) ≤ t·c`
    change ∑ i, ∑ q, U x i q * U x i q ≤ _
    have hU : ∀ i, ∑ q : κ × K × σ', U x i q * U x i q
        = (s * s) * ∑ k : κ, ∑ j : K,
            P.u (codeWord E x) (i, k) j * P.u (codeWord E x) (i, k) j := by
      intro i
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (E (x i) k)]
      · simp only [U, if_true]; ring
      · intro a _ ha; simp only [U]; rw [if_neg ha, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hU]
    rw [← Finset.mul_sum, hss]
    have hload := hP.1 (codeWord E x)
    rw [Fintype.sum_prod_type] at hload
    exact mul_le_mul_of_nonneg_left hload ht0.le
  · -- the `V`-load is at most `|σ'|·(load of v)/s² = t·c`
    change ∑ i, ∑ q, V x i q * V x i q ≤ _
    have hV : ∀ i, ∑ q : κ × K × σ', V x i q * V x i q
        ≤ (Fintype.card σ' : ℝ) / (s * s)
          * ∑ k : κ, ∑ j : K, P.v (codeWord E x) (i, k) j * P.v (codeWord E x) (i, k) j := by
      intro i
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hterm : ∀ a : σ', V x i (k, j, a) * V x i (k, j, a)
          ≤ (P.v (codeWord E x) (i, k) j * P.v (codeWord E x) (i, k) j) / (s * s) := by
        intro a
        simp only [V]
        split_ifs
        · rw [mul_zero]; exact div_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
        · rw [div_mul_div_comm]
      refine (Finset.sum_le_sum fun a _ => hterm a).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    refine (Finset.sum_le_sum fun i _ => hV i).trans ?_
    rw [← Finset.mul_sum, hss]
    have hload := hP.2 (codeWord E x)
    rw [Fintype.sum_prod_type] at hload
    have hcoef : (Fintype.card σ' : ℝ) / t = t := by
      rw [← htt]; field_simp
    rw [hcoef]
    exact mul_le_mul_of_nonneg_left hload ht0.le

end QuantumQueryComplexity
