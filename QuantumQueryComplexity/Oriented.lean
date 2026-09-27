import QuantumQueryComplexity.HasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Oriented adversary solutions

For a Boolean function it suffices to give vectors `u` on the positive inputs
and `v` on the negative inputs with
`∑_{i : x i ≠ y i} ⟨u x i, v y i⟩ = 1` for every positive `x` and negative `y`.
If their loads are at most `P` and `N`, then `f` has a dual of cost `√(PN)`
(`hasDual_of_oriented`): scale the positive vectors by `(N/P)^{1/4}` and the
negative ones by its reciprocal, put the positive `u` and negative `v` in one
orthogonal copy of the space and the negative `u` and positive `v` in a second
copy.  Opposite outputs give one in both orders; equal outputs give zero.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The filtered inner product of two vector families at a pair of inputs. -/
def filteredSum {K : Type} [Fintype K] (u v : (ι → σ) → ι → K → ℝ) (x y : ι → σ) : ℝ :=
  ∑ i, if x i = y i then 0 else ∑ k, u x i k * v y i k

lemma filteredSum_zero_of_zero {K : Type} [Fintype K] {u v : (ι → σ) → ι → K → ℝ}
    {x y : ι → σ} (hu : ∀ i k, u x i k = 0) : filteredSum u v x y = 0 := by
  unfold filteredSum
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs
  · rfl
  · exact Finset.sum_eq_zero fun k _ => by rw [hu i k, zero_mul]

/-- **The oriented adversary lemma.** -/
theorem hasDual_of_oriented {K : Type} [Fintype K] (f : (ι → σ) → Bool)
    (u v : (ι → σ) → ι → K → ℝ)
    (hcon : ∀ x y, f x = true → f y = false → filteredSum u v x y = 1)
    {P N : ℝ} (hP : 0 ≤ P) (hN : 0 ≤ N)
    (hu : ∀ x, f x = true → ∑ i, ∑ k, u x i k * u x i k ≤ P)
    (hv : ∀ y, f y = false → ∑ i, ∑ k, v y i k * v y i k ≤ N) :
    HasDual f (Real.sqrt (P * N)) := by
  classical
  -- a constant function costs nothing
  by_cases hconst : ∀ x y, f x = f y
  · exact (hasDual_const hconst).mono (Real.sqrt_nonneg _)
  push Not at hconst
  obtain ⟨x₀, y₀, hxy⟩ := hconst
  -- there is a positive and a negative input, so `P, N > 0`
  have hpos : ∃ x, f x = true := by
    cases hx : f x₀
    · cases hy : f y₀
      · exact absurd (hx.trans hy.symm) hxy
      · exact ⟨y₀, hy⟩
    · exact ⟨x₀, hx⟩
  have hneg : ∃ y, f y = false := by
    cases hx : f x₀
    · exact ⟨x₀, hx⟩
    · cases hy : f y₀
      · exact ⟨y₀, hy⟩
      · exact absurd (hx.trans hy.symm) hxy
  obtain ⟨xp, hxp⟩ := hpos
  obtain ⟨yn, hyn⟩ := hneg
  have hP0 : 0 < P := by
    rcases lt_or_eq_of_le hP with h | h
    · exact h
    · exfalso
      have hz : ∀ i k, u xp i k = 0 := by
        intro i k
        have hle := hu xp hxp
        rw [← h] at hle
        have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ k, u xp i k * u xp i k :=
          fun i _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle
          (Finset.sum_nonneg hnn)) i (Finset.mem_univ _)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => mul_self_nonneg (u xp i k))).1 h1 k (Finset.mem_univ _)
        exact mul_self_eq_zero.1 h2
      have := hcon xp yn hxp hyn
      rw [filteredSum_zero_of_zero hz] at this
      exact zero_ne_one this
  have hN0 : 0 < N := by
    rcases lt_or_eq_of_le hN with h | h
    · exact h
    · exfalso
      have hz : ∀ i k, v yn i k = 0 := by
        intro i k
        have hle := hv yn hyn
        rw [← h] at hle
        have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ k, v yn i k * v yn i k :=
          fun i _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle
          (Finset.sum_nonneg hnn)) i (Finset.mem_univ _)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => mul_self_nonneg (v yn i k))).1 h1 k (Finset.mem_univ _)
        exact mul_self_eq_zero.1 h2
      have := hcon xp yn hxp hyn
      unfold filteredSum at this
      rw [Finset.sum_eq_zero fun i _ => by
        split_ifs
        · rfl
        · exact Finset.sum_eq_zero fun k _ => by rw [hz i k, mul_zero]] at this
      exact zero_ne_one this
  -- the scaling
  set s : ℝ := Real.sqrt (Real.sqrt N / Real.sqrt P) with hs
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hP0
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hsN hsP)
  have hss : s * s = Real.sqrt N / Real.sqrt P := Real.mul_self_sqrt (div_pos hsN hsP).le
  have hsq : Real.sqrt (P * N) = Real.sqrt P * Real.sqrt N := Real.sqrt_mul hP N
  have hload1 : s * s * P ≤ Real.sqrt (P * N) := by
    rw [hss, hsq, div_mul_eq_mul_div, ← Real.sqrt_mul_self hP, Real.sqrt_mul_self hP]
    rw [show Real.sqrt N * P / Real.sqrt P = Real.sqrt N * (P / Real.sqrt P) by ring]
    rw [Real.div_sqrt, mul_comm]
  have hload2 : N / (s * s) ≤ Real.sqrt (P * N) := by
    rw [hss, hsq, div_div_eq_mul_div, mul_comm N, mul_div_assoc, Real.div_sqrt]
  -- the two-copy solution, with `0/1` indicators of the output
  let p : (ι → σ) → ℝ := fun x => if f x = true then 1 else 0
  let q : (ι → σ) → ℝ := fun x => if f x = true then 0 else 1
  have hpt : ∀ x, f x = true → p x = 1 ∧ q x = 0 := fun x hx => by simp [p, q, hx]
  have hpf : ∀ x, f x = false → p x = 0 ∧ q x = 1 := fun x hx => by simp [p, q, hx]
  have hpp : ∀ x, p x * p x = p x := fun x => by cases hx : f x <;> simp [p, hx]
  have hqq : ∀ x, q x * q x = q x := fun x => by cases hx : f x <;> simp [q, hx]
  have hpq : ∀ x, p x * q x = 0 := fun x => by cases hx : f x <;> simp [p, q, hx]
  have hpq1 : ∀ x, p x + q x = 1 := fun x => by cases hx : f x <;> simp [p, q, hx]
  let U : (ι → σ) → ι → K ⊕ K → ℝ := fun x i k =>
    match k with
    | Sum.inl k => p x * (s * u x i k)
    | Sum.inr k => q x * (v x i k / s)
  let V : (ι → σ) → ι → K ⊕ K → ℝ := fun x i k =>
    match k with
    | Sum.inl k => q x * (v x i k / s)
    | Sum.inr k => p x * (s * u x i k)
  have hUV : ∀ x y i, ∑ k, U x i k * V y i k
      = p x * q y * ∑ k, u x i k * v y i k + q x * p y * ∑ k, v x i k * u y i k := by
    intro x y i
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> simp only [U, V] <;> field_simp
  have hUU : ∀ x i, ∑ k, U x i k * U x i k
      = p x * (s * s * ∑ k, u x i k * u x i k) + q x * ((∑ k, v x i k * v x i k) / (s * s)) := by
    intro x i
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [U]
      linear_combination (s * u x i k) ^ 2 * hpp x
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [U]
      linear_combination (v x i k / s) ^ 2 * hqq x
  have hVV : ∀ x i, ∑ k, V x i k * V x i k
      = q x * ((∑ k, v x i k * v x i k) / (s * s)) + p x * (s * s * ∑ k, u x i k * u x i k) := by
    intro x i
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [V]
      linear_combination (v x i k / s) ^ 2 * hqq x
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [V]
      linear_combination (s * u x i k) ^ 2 * hpp x
  have hi : ∀ x y i, (if x i = y i then 0 else ∑ k, U x i k * V y i k)
      = p x * q y * (if x i = y i then 0 else ∑ k, u x i k * v y i k)
        + q x * p y * (if x i = y i then 0 else ∑ k, v x i k * u y i k) := by
    intro x y i
    split_ifs
    · ring
    · exact hUV x y i
  have hsum : ∀ x y, (∑ i, if x i = y i then 0 else ∑ k, U x i k * V y i k)
      = p x * q y * filteredSum u v x y + q x * p y * filteredSum v u x y := by
    intro x y
    simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hswap : ∀ x y, filteredSum v u x y = filteredSum u v y x := by
    intro x y
    unfold filteredSum
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i = y i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  let D : DualPair (K ⊕ K) f :=
    { u := U
      v := V
      constraint := fun x y => by
        rw [hsum, hswap]
        cases hx : f x <;> cases hy : f y
        · obtain ⟨hp, hq⟩ := hpf x hx
          obtain ⟨hp', hq'⟩ := hpf y hy
          simp [hp, hq, hp', hq']
        · obtain ⟨hp, hq⟩ := hpf x hx
          obtain ⟨hp', hq'⟩ := hpt y hy
          rw [hcon y x hy hx]
          simp [hp, hq, hp', hq']
        · obtain ⟨hp, hq⟩ := hpt x hx
          obtain ⟨hp', hq'⟩ := hpf y hy
          rw [hcon x y hx hy]
          simp [hp, hq, hp', hq']
        · obtain ⟨hp, hq⟩ := hpt x hx
          obtain ⟨hp', hq'⟩ := hpt y hy
          simp [hp, hq, hp', hq'] }
  refine hasDual_of_dualPair D ⟨fun x => ?_, fun x => ?_⟩
  · change ∑ i, ∑ k, U x i k * U x i k ≤ _
    simp only [hUU, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    cases hx : f x
    · obtain ⟨hp, hq⟩ := hpf x hx
      rw [hp, hq, zero_mul, zero_add, one_mul]
      exact (div_le_div_of_nonneg_right (hv x hx) (mul_self_nonneg s)).trans hload2
    · obtain ⟨hp, hq⟩ := hpt x hx
      rw [hp, hq, zero_mul, add_zero, one_mul]
      exact (mul_le_mul_of_nonneg_left (hu x hx) (mul_self_nonneg s)).trans hload1
  · change ∑ i, ∑ k, V x i k * V x i k ≤ _
    simp only [hVV, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    cases hx : f x
    · obtain ⟨hp, hq⟩ := hpf x hx
      rw [hp, hq, zero_mul, add_zero, one_mul]
      exact (div_le_div_of_nonneg_right (hv x hx) (mul_self_nonneg s)).trans hload2
    · obtain ⟨hp, hq⟩ := hpt x hx
      rw [hp, hq, zero_mul, zero_add, one_mul]
      exact (mul_le_mul_of_nonneg_left (hu x hx) (mul_self_nonneg s)).trans hload1

end QuantumQueryComplexity
